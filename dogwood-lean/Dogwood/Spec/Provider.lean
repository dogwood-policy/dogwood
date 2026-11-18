import Dogwood.Spec.Event
import Cedar.Validation.Types

/-!
# Information providers

An information-provider invocation is a namespace-qualified call in an
ordinary Cedar condition, `Ns::Fn(args).m₁(args)….mₖ(args)`, optionally
followed by a field projection (guide chapter 5). The projection is plain
Cedar (`getAttr`) over the invocation's value; what is specific to providers
is the invocation and its eager output-method chain, a `Call` here.

Providers are not specified by this document: their implementations are
sandboxed scripts or caller-supplied resolvers. The language fixes only the
contract (guide chapter 5, "The provider contract"), which the model below
reflects:

* a provider is a **pure** function of its resolved arguments, so its meaning
  is a function `Providers` from resolved invocations to outputs;
* any argument may be **absent** on a given event (`ArgValue.absent`, `Null`
  to a script);
* an invocation either produces a value or **fails** (`Output.error`). It fails
  when its script throws, when a caller-supplied resolver reports an error, when
  an output method of its chain fails, when its provider is not declared and no
  resolver supplies its value, and when its output does not have its declared
  type in a way the reference implementation checks: a value outside a declared
  enum, or a value of the wrong shape where the declared type contains an enum
  (`coerce_to_declared`). An output of the wrong shape whose declared type
  contains no enum is not a failure: it is a value, and the decision fails
  closed on it before Cedar reads it (`FailClosed.nonconformingProviderOutput`);
* evaluation is **unconditional**: every invocation in a policy set is
  evaluated for every decision event, whatever the rule it belongs to. So a
  failing invocation fails every decision at that event, not only the
  decisions its rule could make. The decision fails closed
  (`FailClosed.providerError`, `Dogwood.Spec.Decision`).

The guide calls an erroring script or resolver undefined behavior, and says
that the reference interpreter's denial is its implementation choice. The
specification fixes that choice, as the crate's front end does (`api.rs`,
`decide_at`): the decision fails closed. An output outside its declared enum
must deny on every implementation (guide chapter 10, "Fail closed at runtime").
-/

namespace Dogwood.Spec.Provider

open Cedar.Spec (Value Name)

/-- A provider argument, as written: an attribute path rooted at `context`,
`principal` or `resource`, a literal, or a set of arguments. -/
inductive Arg where
  /-- `context.<path>` (`path` excludes the leading `context`). -/
  | context (path : Path)
  /-- `principal` / `resource`, optionally followed by an attribute path. -/
  | scope (root : ScopeRoot) (path : Path)
  | string (s : String)
  | long (i : Int64)
  /-- `decimal("…")`, with its payload as written. -/
  | decimal (text : String)
  | bool (b : Bool)
  | set (items : List Arg)
deriving Repr, Inhabited

/-- One output method of an invocation's eager chain, `.name(args)`. -/
structure MethodCall where
  name : String
  args : List Arg
deriving Repr, Inhabited

/-- A provider invocation `Ns::Fn(args)` and its output-method chain. -/
structure Call where
  function : Name
  args : List Arg
  methods : List MethodCall
deriving Repr, Inhabited

/-- An argument's value on a particular event. -/
inductive ArgValue where
  /-- The argument does not resolve on this event. -/
  | absent
  | value (v : Value)
  | list (items : List ArgValue)

/-- An invocation with its arguments, and those of its output methods,
resolved against the decision event. -/
structure ResolvedCall where
  function : Name
  args : List ArgValue
  methods : List (String × List ArgValue)

/-- What one invocation, after its output-method chain, produced on a decision
event: a value, or a failure. -/
inductive Output where
  /-- The invocation produced this value. -/
  | value (v : Value)
  /-- The invocation failed. -/
  | error
deriving Inhabited

/-- Whether the invocation failed. -/
def Output.isError : Output → Bool
  | .value _ => false
  | .error => true

/-- The value a provider leaf takes: the output's value, or `false` for a
failed output. No decision reads the value of a failed output, because the
decision fails closed first (`PolicySet.authorize`). -/
def Output.leafValue : Output → Value
  | .value v => v
  | .error => .prim (.bool false)

/-- The meaning of the information providers: the output of each resolved
invocation, after its output-method chain. -/
abbrev Providers := ResolvedCall → Output

/-- Providers that never fail, given by the value of each resolved
invocation. -/
def total (f : ResolvedCall → Value) : Providers := fun c => .value (f c)

mutual

/-- Resolve an argument against the request event `e`: a `context` path
reads the request context, a scope path reads the scope entity and its
supplied attributes, and anything that does not resolve is absent. -/
def Arg.resolve (e : Event) : Arg → ArgValue
  | .context p => ((e.contextPath? p).map .value).getD .absent
  | .scope r p => ((e.scopePath? r p).map .value).getD .absent
  | .string s => .value (.prim (.string s))
  | .long i => .value (.prim (.int i))
  | .decimal s =>
    ((Cedar.Spec.Ext.Decimal.parse s).map fun d => .value (.ext (.decimal d))).getD .absent
  | .bool b => .value (.prim (.bool b))
  | .set items => .list (Arg.resolveList e items)

def Arg.resolveList (e : Event) : List Arg → List ArgValue
  | [] => []
  | a :: as => a.resolve e :: Arg.resolveList e as

end

def Call.resolve (e : Event) (c : Call) : ResolvedCall where
  function := c.function
  args := Arg.resolveList e c.args
  methods := c.methods.map fun m => (m.name, Arg.resolveList e m.args)

/-! ## Declarations

A provider's declaration (`providers.json`, guide chapter 10) gives the types of its arguments
and of its output, and the methods callable on its output, each with argument types and an
output type that re-types the pipeline. Types are Cedar types: the crate converts each declared
`paramType` to the Cedar type of the hoisted field, an enum entity type to an entity type the
action schema declares. -/

open Cedar.Validation (CedarType)

/-- A declared output method: its argument types, the type of the value it takes when it
declares one (`inputType`), and its output type. -/
structure MethodSig where
  name : String
  args : List CedarType
  input : Option CedarType := none
  output : CedarType

/-- A declared information provider. -/
structure Signature where
  function : Name
  args : List CedarType
  output : CedarType
  methods : List MethodSig

/-- The declarations of a policy set's providers. -/
abbrev Declarations := List Signature

/-- The declaration of the provider `f`, if any. -/
def Declarations.find? (D : Declarations) (f : Name) : Option Signature :=
  List.find? (·.function == f) D

/-- The declared type of a literal argument; `none` for an argument read off the request,
which may be absent on an event and so is not checked. -/
def Arg.literalType? : Arg → Option CedarType
  | .string _ => some .string
  | .long _ => some .int
  | .decimal _ => some (.ext .decimal)
  | .bool _ => some (.bool .anyBool)
  | _ => none

/-- Literal arguments have their declared types, and there are as many arguments as declared
types. -/
def argsMatchDecl (args : List Arg) (tys : List CedarType) : Prop :=
  args.length = tys.length ∧
    ∀ p ∈ args.zip tys, p.1.literalType? = none ∨ p.1.literalType? = some p.2

/-- Each method of the chain is declared, and takes the type the stage before it produces, when
it declares the type it takes. The first stage is the provider's output, of type `s`. -/
def Signature.Chains (sig : Signature) : CedarType → List MethodCall → Prop
  | _, [] => True
  | s, m :: ms =>
    match sig.methods.find? (·.name == m.name) with
    | some msig => (msig.input = none ∨ msig.input = some s) ∧ sig.Chains msig.output ms
    | none => False

/-- The invocation names a declared provider and declared output methods, with arguments that
match their declarations, and each method takes the value the stage before it produces. -/
def Call.Declared (D : Declarations) (c : Call) : Prop :=
  ∃ sig, D.find? c.function = some sig ∧ argsMatchDecl c.args sig.args ∧
    (∀ m ∈ c.methods, ∃ ms ∈ sig.methods, ms.name = m.name ∧ argsMatchDecl m.args ms.args) ∧
    sig.Chains sig.output c.methods

/-- The declared type of an invocation's value: its provider's output type, or the output type
of the last method of its chain. -/
def Call.outputType? (D : Declarations) (c : Call) : Option CedarType :=
  match D.find? c.function with
  | none => none
  | some sig =>
    match c.methods.getLast? with
    | none => some sig.output
    | some m => (sig.methods.find? (·.name == m.name)).map (·.output)

end Dogwood.Spec.Provider
