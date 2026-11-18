import Dogwood.Frontend.Validate.Events

/-!
# The temporal dialect's checks

The crate's validator checks each hoisted temporal leaf (`TemporalDialect::validate`,
`extension/temporal/validate.rs` and `validity.rs`, and the event-schema names check
`event_schema/validate.rs`), in this order:

1. **event names** (`validate_condition`): every predicate names a derived event, and every field
   it mentions is a declared leaf field of it; only the first problem is reported;
2. **windows** (`check_windows`): every window is positive, its length in seconds fits a `Long`,
   and it is at most `max_window`;
3. **wildcard operands** (`check_wildcard_operands`);
4. **entity literals** (`check_entity_types`): an action literal names a declared action, any
   other entity literal a declared entity type, and an enum's id one of its ids;
5. **decimal literals** (`check_decimal_literals`);
6. **request paths** (`check_context_fields`): in every target action that admits a request
   environment, every `context.<path>` resolves, and every `principal.<path>` /
   `resource.<path>` resolves, with one type, on every admitted entity type;
7. **time dependence** (`check_tp_dependence`);
8. **types** (`check_types`), in every request environment: `tp` binds a `Timepoint`, an
   ordering compares two `Long`s, an equality two compatible types, a compound's atoms are
   `Long`s, and a predicate argument has a type its field can hold;
9. **summands** (`check_sum_summands`);
10. **validity rules** (`validity::check_leaf`): the `for` variables of an aggregation are
    distinct; every binder's type is declared; every optional attribute a request path reads is
    guarded by a `has` fact; every pin's request-side path is declared and required, of a type
    the field can hold; and a variable bound by a field the event schema names has a type every
    value of the field has.

The checks run on the leaf's specification form (`Condition.toFormula`): the same tree, without
spans and without the transient forms that never reach validation. A check that walks the leaf
visits the aggregation bodies of comparison operands, as the crate's `walk` does, and a check
that binds variables skips the body of an ill-formed binder list, as the crate's `walk_typed`
and `visit` do. Each finding is a message; its category is read off it as the conformance
harness reads the crate's (`Conformance.crateCategory`).
-/

namespace Dogwood.Frontend.Validate

open Cedar.Spec (EntityType EntityUID Attr)
open Cedar.Validation (CedarType RecordType QualifiedType Schema ActionSchemaEntry)
open Dogwood.Spec (Path ScopeRoot)
open Dogwood.Spec.Temporal

/-- What the checks of one temporal leaf read: the augmented schema, the derived event schema,
the `max_window` cap, the actions the leaf's rule resolves to that the schema declares, the
rule's principal and resource narrowing, and the facts the leaf's position establishes. -/
structure LeafCtx where
  schema : Schema
  events : DerivedEventSchema
  cap : Int
  capText : String
  /-- The `max_horizon` cap, in seconds, if the event schema declares one, and its unit and text
  (diagnostics). -/
  horizonCap : Option Int := none
  horizonUnit : TimeUnit := .hours
  horizonCapText : String := ""
  targets : List (EntityUID × ActionSchemaEntry)
  principal : ScopeConstraint
  resource : ScopeConstraint
  facts : List Guard
  /-- The ids of an enum entity type in the order the schema declares them (diagnostics only). -/
  declaredEnum : EntityType → Option (List String) := fun _ => none

namespace LeafCtx

variable (C : LeafCtx)

/-- The narrowing of a scope root. -/
def narrow : Root → ScopeConstraint
  | .principal => C.principal
  | .resource => C.resource

/-- The target actions that admit a request environment under the rule's narrowing. -/
def actions : List (EntityUID × ActionSchemaEntry) :=
  C.targets.filter fun (_, entry) => admitsAnyEnv C.schema entry C.principal C.resource

end LeafCtx

/-- A field path's text. -/
def pathText (p : Path) : String := fieldPathJoin p

/-- `root.<path>`'s text. -/
def pathUnder (root : String) (p : Path) : String := fieldPathJoin (root :: p)

/-- A window as written, `<amount><unit>`. -/
def renderWindow (w : Window) : String :=
  toString w.amount ++ match w.unit with
    | .seconds => "s" | .minutes => "m" | .hours => "h" | .days => "d"

/-- A predicate's head, as a diagnostic shows it. -/
def predHead (a : EntityUID) (k : String) : String := actionText a ++ "::" ++ k

/-! ## 1. Event names -/

/-- The first problem with a predicate's event and fields (crate `validate_predicate`). -/
def predEventProblem (d : DerivedEventSchema) (a : EntityUID) (k : String)
    (args : List (Path × Term)) : Option String :=
  match eventOf? d a k with
  | none => some s!"predicate `{predHead a k}` does not name a declared event (no event kind `{k}` derived for action `{escapedId a.eid}`)"
  | some ev =>
    args.findSome? fun (p, _) =>
      match lookupPath ev p with
      | .leaf => none
      | .group => some s!"predicate `{predHead a k}` mentions `{pathText p}`, which is a field group, not a field; address a field inside it (e.g. `{pathText p}.<field>`)"
      | .absent => some s!"predicate `{predHead a k}` mentions field `{pathText p}`, which is not declared on that event (declared fields: {", ".intercalate (declaredPaths ev)})"

mutual

/-- The first event-name problem in a condition (crate `validate_condition`). -/
def eventNamesF (d : DerivedEventSchema) : Formula → Option String
  | .and φ ψ | .since φ _ ψ => (eventNamesF d φ).or (eventNamesF d ψ)
  | .not φ | .formerly _ φ | .previous _ φ | .exist _ φ => eventNamesF d φ
  | .pred a k args => predEventProblem d a k args
  | .cmp _ l r => (eventNamesT d l).or (eventNamesT d r)
  | .tp _ => none

/-- The first event-name problem in an operand's aggregation bodies (crate `validate_term`). -/
def eventNamesT (d : DerivedEventSchema) : Term → Option String
  | .agg a => eventNamesA d a
  | .arith _ l r => (eventNamesT d l).or (eventNamesT d r)
  | _ => none

def eventNamesA (d : DerivedEventSchema) : Aggregate → Option String
  | .count _ body | .sum _ _ body => eventNamesF d body

end

/-! ## A walk over the nodes

The crate's `walk` visits every node of a condition, and the aggregation bodies of comparison
operands (an aggregate that is the operand, or an atom of a compound one). At each node a check
looks at the node itself, and `for_each_term` at the terms the node carries: the comparison
operands, with the atoms of a compound, and the predicate arguments. -/

/-- The terms a node carries, with the atoms of a compound (crate `for_each_term`). -/
def termAtoms : Term → List Term
  | .arith op l r => .arith op l r :: (termAtoms l ++ termAtoms r)
  | t => [t]

/-- The predicate arguments' terms, with the atoms of compounds. -/
def argsAtoms : List (Path × Term) → List Term
  | [] => []
  | (_, t) :: args => termAtoms t ++ argsAtoms args

mutual

/-- Every finding `f` reports at a node, over the walk of a condition (crate `walk`). -/
def walkF (f : Formula → List String) : Formula → List String
  | .and φ ψ => f (.and φ ψ) ++ walkF f φ ++ walkF f ψ
  | .since φ w ψ => f (.since φ w ψ) ++ walkF f φ ++ walkF f ψ
  | .not φ => f (.not φ) ++ walkF f φ
  | .formerly w φ => f (.formerly w φ) ++ walkF f φ
  | .previous w φ => f (.previous w φ) ++ walkF f φ
  | .exist x φ => f (.exist x φ) ++ walkF f φ
  | .pred a k args => f (.pred a k args)
  | .cmp op l r => f (.cmp op l r) ++ walkT f l ++ walkT f r
  | .tp x => f (.tp x)

/-- The walk of an operand's aggregation bodies. -/
def walkT (f : Formula → List String) : Term → List String
  | .agg a => walkA f a
  | .arith _ l r => walkT f l ++ walkT f r
  | _ => []

def walkA (f : Formula → List String) : Aggregate → List String
  | .count _ body | .sum _ _ body => walkF f body

end

/-- The terms a node carries (crate `for_each_term`). -/
def nodeTerms : Formula → List Term
  | .pred _ _ args => argsAtoms args
  | .cmp _ l r => termAtoms l ++ termAtoms r
  | _ => []

/-- Every finding `g` reports at a term a node carries, over the walk. -/
def walkTerms (g : Term → List String) (φ : Formula) : List String :=
  walkF (fun n => (nodeTerms n).flatMap g) φ

/-! ## 2. Windows -/

/-- The finding for a window longer than the `max_window` cap (crate `check_windows`). A
`max_window` may not exceed a declared `max_horizon`, so for a window longer than
`max_horizon` the finding says to raise `max_horizon`. -/
def windowCapMessage (C : LeafCtx) (w : Window) : String :=
  if C.horizonCap.any (fun h => decide (h < w.seconds)) then
    s!"temporal window `{renderWindow w}` exceeds the maximum allowed window `{C.capText}`; shorten this window to at most `{C.capText}`, or raise the event schema's `max_horizon` of `{C.horizonCapText}` (and its `max_window`, if it declares one)"
  else
    s!"temporal window `{renderWindow w}` exceeds the maximum allowed window `{C.capText}` set by the event schema's `max_window`; shorten this window to at most `{C.capText}`, or raise `max_window` in the event schema"

/-- The problem with a window, if any (crate `check_windows`). -/
def windowProblem (C : LeafCtx) (w : Window) : Option String :=
  if w.amount ≤ 0 then
    some s!"temporal window `{renderWindow w}` must be positive; a zero or negative window matches no events, silently disabling this guard"
  else if w.seconds > Int64.MAX then
    some s!"temporal window `{renderWindow w}` is too large; its length in seconds overflows a 64-bit integer. Use a smaller window."
  else if w.seconds > C.cap then
    some (windowCapMessage C w)
  else none

/-- A number of seconds as an interval, in `unit` when it divides evenly and in seconds
otherwise (crate `render_seconds`). -/
def renderSeconds (secs : Int) (unit : TimeUnit) : String :=
  if secs % unit.toSeconds == 0 then renderWindow ⟨secs / unit.toSeconds, unit⟩
  else toString secs ++ "s"

/-- The problem with a leaf's horizon, if it exceeds `max_horizon` (crate `check_horizon`, which
sums exactly, in 128 bits). -/
def horizonProblem (C : LeafCtx) (φ : Formula) : Option String :=
  let h := φ.horizon .seconds
  match C.horizonCap with
  | none => none
  | some cap =>
  if h > cap then
    some s!"temporal condition looks back up to `{renderSeconds h C.horizonUnit}` (the largest sum of the `within` windows along one chain of nested `formerly`, `previous` and `since` operators), which exceeds the event schema's `max_horizon` of `{C.horizonCapText}`; shorten or un-nest its windows, or raise `max_horizon` in the event schema (events older than `max_horizon` are never consulted)"
  else none

/-- The window problems at a node. -/
def windowsAt (C : LeafCtx) : Formula → List String
  | .formerly w _ | .previous w _ | .since _ w _ => (windowProblem C w).toList
  | _ => []

/-! ## 3. Wildcard operands -/

def wildcardAt : Formula → List String
  | .cmp _ .wildcard _ | .cmp _ _ .wildcard =>
    ["a wildcard (`*` / `_`) cannot be a comparison operand; it resolves to no value, so the comparison is always false, and its negation always true"]
  | _ => []

/-! ## 4, 5. Literals -/

/-- The ids of an enum entity type, quoted and escaped, in the order the schema declares them,
or `(none)` (crate `enum_choices`). `declared` gives the declaration order (the schema's sets
are sorted). -/
def enumChoices (ids : List String) : String :=
  if ids.isEmpty then "(none)" else ", ".intercalate (ids.map fun e => "\"" ++ escapedId e ++ "\"")

/-- The entity types the schema declares, by name, sorted (crate `known_entities_help`). -/
def knownEntitiesHelp (S : Schema) : String :=
  match (S.ets.toList.map fun (ety, _) => nameText ety).mergeSort (fun a b => decide (a ≤ b)) with
  | [] => "the schema declares no entity types"
  | known => "known entity types: " ++ ", ".intercalate known

/-- The problem with an entity literal (crate `check_entity_types`); `declared` gives an enum's
ids in the order the schema declares them. -/
def entityProblem (S : Schema) (declared : EntityType → Option (List String)) (uid : EntityUID) :
    Option String :=
  if uid.ty.id == "Action" then
    if S.acts.contains uid then none
    else some s!"`{nameText uid.ty}::\"{escapedId uid.eid}\"` is not a declared action; an action literal names an action the schema declares"
  else
    match S.ets.find? uid.ty with
    | some (.enum eids) =>
      if eids.contains uid.eid then none
      else some s!"`{nameText uid.ty}` is an enum entity type; `\"{escapedId uid.eid}\"` is not one of its permitted ids ({enumChoices ((declared uid.ty).getD eids.toList)})"
    | some (.standard _) => none
    | none => some s!"unknown entity type `{nameText uid.ty}`; {knownEntitiesHelp S}"

def entityAt (S : Schema) (declared : EntityType → Option (List String)) : Term → List String
  | .entity uid => (entityProblem S declared uid).toList
  | _ => []

def decimalAt : Term → List String
  | .decimal text =>
    if (Cedar.Spec.Ext.Decimal.parse text).isSome then []
    else [s!"`decimal({Escape.strDebug text})` does not parse as a `decimal`: Cedar's decimals have digits on both sides of a point, at most four after it, and fit a 64-bit integer at that scale"]
  | _ => []

/-! ## 6. Request paths -/

/-- The problem with `context.<path>` in an action's context (crate `check_one_context_path`). -/
def contextPathProblem (uid : EntityUID) (entry : ActionSchemaEntry) (p : Path) : Option String :=
  match p with
  | [] => none
  | head :: _ =>
    match resolveContextPath entry.context p with
    | .resolved _ => none
    | .headMissing => some s!"action `{predicateRef uid}` has no context field `{head}` for `context.{head}`"
    | .nestedMissing seg => some s!"record has no field `{seg}` in `{pathUnder "context" p}` path"
    | .nonRecord seg => some s!"`{seg}` accesses a field of a non-record type"

/-- The problem with `root.<path>` on the entity types the action admits (crate
`check_one_scope_path`). -/
def scopePathProblem (S : Schema) (entry : ActionSchemaEntry) (r : Root) (narrow : ScopeConstraint)
    (p : Path) : Option String :=
  match p with
  | [] => none
  | _ :: _ =>
    let rendered := pathUnder r.name p
    match resolveScopePath S entry r narrow p with
    -- A path of a different type on each admitted entity type is typed in each request
    -- environment (crate `check_one_scope_path`).
    | .resolved | .unknown | .ambiguous _ => none
    | .missing entities seg => some s!"`{rendered}` does not resolve for every entity the rule's `{r.name}` may be: `{"`, `".intercalate entities}` declares no attribute `{seg}`, so for those requests the comparison can never match and the condition is permanently false. Narrow the rule's scope (`{r.name} is <type>`) if only some types are meant."
    | .nonRecord seg => some s!"`{seg}` accesses a field of a non-record type in `{rendered}`"

def pathsAt (C : LeafCtx) (uid : EntityUID) (entry : ActionSchemaEntry) : Term → List String
  | .context p => (contextPathProblem uid entry p).toList
  | .scope r p => (scopePathProblem C.schema entry (Root.ofSpec r) (C.narrow (Root.ofSpec r)) p).toList
  | _ => []

/-! ## 7. Time dependence -/

def degenerate (what : String) : String :=
  s!"{what} does not vary with the current timepoint; it monitors nothing"

mutual

/-- Whether a condition varies with the timepoint, and the degenerate monitoring scopes inside
it (crate `is_tp_dep`). `E` holds the variables that vary. -/
def tpDep (E : List VarName) : Formula → Bool × List String
  | .pred _ _ _ | .tp _ => (true, [])
  | .cmp _ l r => (l.variesB E || r.variesB E, tpDepT E l ++ tpDepT E r)
  | .not φ => tpDep E φ
  | .and φ ψ => ((tpDep E φ).1 || (tpDep E ψ).1, (tpDep E φ).2 ++ (tpDep E ψ).2)
  | .formerly _ φ | .previous _ φ =>
    (true, (tpDep E φ).2 ++ if (tpDep E φ).1 then [] else [degenerate "this temporal operator's body"])
  | .since φ _ ψ =>
    (true, (tpDep E φ).2 ++ (if (tpDep E φ).1 then [] else [degenerate "the left side of `since`"]) ++
      (tpDep E ψ).2 ++ (if (tpDep E ψ).1 then [] else [degenerate "the right side of `since`"]))
  | .exist x φ =>
    (true, (tpDep (x.name :: E) φ).2 ++
      if (tpDep (x.name :: E) φ).1 then [] else [degenerate "the body of the `exists`"])

/-- The degenerate aggregation bodies of an operand (crate `check_agg_tp_dependence`, on each
aggregate of the operand). -/
def tpDepT (E : List VarName) : Term → List String
  | .agg a => tpDepA E a
  | .arith _ l r => tpDepT E l ++ tpDepT E r
  | _ => []

def tpDepA (E : List VarName) : Aggregate → List String
  | .sum s _ body =>
    (tpDep (s :: E) body).2 ++
      if (tpDep (s :: E) body).1 then [] else [degenerate "the `where` body of the aggregation"]
  | .count _ body =>
    (tpDep E body).2 ++ if (tpDep E body).1 then [] else [degenerate "the `where` body of the aggregation"]

end

/-- The time-dependence findings of a leaf (crate `check_tp_dependence`). -/
def checkTpDependence (φ : Formula) : List String :=
  φ.conjuncts.flatMap fun c =>
    (tpDep φ.ruleWideBinders c).2 ++
      if (tpDep φ.ruleWideBinders c).1 then []
      else ["this `when`/`unless` conjunct does not vary with the current timepoint; it monitors nothing"]

/-! ## 8. Types, in each request environment -/

/-- A request environment of a leaf's rule: a target action, and a principal type and a resource
type the action admits and the rule's narrowing admits. -/
structure ReqEnv where
  uid : EntityUID
  entry : ActionSchemaEntry
  principal : EntityType
  resource : EntityType

/-- `xs` without one occurrence of each element of `ys` (a multiset difference). -/
def eraseEach (xs ys : List String) : List String := ys.foldl List.erase xs

/-- The findings of each request environment, merged as the crate reports them (crate
`check_types`, its `seen` set): the environments in order, and of each one's findings those the
earlier ones did not already report as many times. (The crate tells two findings apart by their
message and the position of their node; the specification form of a leaf has no positions, so a
finding is told apart by its message, and the number of times one environment reports it.) -/
def mergeEnvFindings {α : Type} (envs : List α) (f : α → List String) : List String :=
  envs.foldl (fun acc e => acc ++ eraseEach (f e) acc) []

/-- The request environments of a leaf's rule (crate `check_types`). -/
def LeafCtx.envs (C : LeafCtx) : List ReqEnv :=
  C.targets.flatMap fun (uid, entry) =>
    (admittedTypes C.schema entry .principal C.principal).flatMap fun p =>
      (admittedTypes C.schema entry .resource C.resource).map fun r => ⟨uid, entry, p, r⟩

def ReqEnv.scopeType (e : ReqEnv) : ScopeRoot → EntityType
  | .principal => e.principal
  | .resource => e.resource

/-- Whether a binder's declared type means something (crate `binder_type_declared`): a scalar
(`Long`, `String`, `Bool`, `decimal`), `Timepoint`, or an entity type the schema declares, by its
qualified name as written. -/
def binderTypeDeclared (S : Schema) : BinderType → Bool
  | .timepoint => true
  | .named path =>
    match path.getLast? with
    | some "Long" | some "String" | some "Bool" | some "Boolean" | some "decimal" | some "Decimal" => true
    | some id => S.ets.contains ⟨id, path.dropLast⟩
    | none => false

/-- What a finding says of a binder or a term of one of Cedar's extension types other than
`decimal` (crate `UNSUPPORTED_EXTENSION`). -/
def unsupportedExtension : String :=
  "temporal conditions do not support Cedar's `datetime`, `duration`, and `ipaddr` types"

/-- Whether a binder is declared with one of Cedar's extension types other than `decimal`, by its
last segment (crate `unsupported_extension_binder`). -/
def unsupportedExtensionBinder : BinderType → Bool
  | .timepoint => false
  | .named path =>
    match path.getLast? with
    | some "datetime" | some "duration" | some "ipaddr" => true
    | _ => false

/-- Whether a binder list is well-formed: every type declared, the names distinct (crate
`binders_typed`). -/
def bindersTyped (S : Schema) (bs : List Binder) : Bool :=
  bs.all (binderTypeDeclared S ·.ty) && decide (bs.map (·.name)).Nodup

/-- The sort a binder's annotation gives its variable (crate `rich_type_of_annotation`): any name
other than a scalar's is an entity type, by its qualified name as written. -/
def annotationSort : BinderType → TType
  | .timepoint => .timepoint
  | .named path =>
    match path.getLast? with
    | some "Long" => .cedar .int
    | some "String" => .cedar .string
    | some "Bool" | some "Boolean" => .cedar (.bool .anyBool)
    | some "decimal" | some "Decimal" => .cedar (.ext .decimal)
    | some id => .cedar (.entity ⟨id, path.dropLast⟩)
    | none => .cedar (.entity ⟨"", []⟩)

/-- The bindings a binder list makes. -/
def binderBindings (bs : List Binder) : Bindings :=
  bs.map fun b => (b.name, annotationSort b.ty)

/-- The input fields of an action, with their types: the variables the crate's type environment
starts from (crate `build_type_env`). -/
def inputBindings (entry : ActionSchemaEntry) : Bindings :=
  match entry.context.find? "input" with
  | some q => match q.getType with
    | .record rty => rty.toList.map fun (a, q) => (a, .cedar q.getType)
    | _ => []
  | none => []

/-- The sort of a term in a request environment, when it has one (crate `term_type`). -/
def termSort (S : Schema) (e : ReqEnv) (Γ : Bindings) : Term → Option TType
  | .var x => Γ.lookup x
  | .long _ => some (.cedar .int)
  | .decimal _ => some (.cedar (.ext .decimal))
  | .string _ => some (.cedar .string)
  | .bool _ => some (.cedar (.bool .anyBool))
  | .entity uid => some (.cedar (.entity uid.ty))
  | .context p => (contextPathType? e.entry.context p).map .cedar
  | .scope r [] => some (.cedar (.entity (e.scopeType r)))
  | .scope r p => (scopeAttrTypeOf? S (e.scopeType r) p).map .cedar
  | .agg _ | .arith _ _ _ => some (.cedar .int)
  | .wildcard => none

/-- The finding for a request-side path whose type is, or holds, one of Cedar's extension types
other than `decimal` (crate `check_unsupported_operand`): temporal conditions do not support
them. -/
def unsupportedOperand (S : Schema) (e : ReqEnv) : Term → Option String
  | .context p =>
    match contextPathType? e.entry.context p with
    | some ty =>
      if ty.temporalSupported then none
      else some s!"`{pathUnder "context" p}` has the type `{renderType ty}`; {unsupportedExtension}"
    | none => none
  | .scope r (a :: p) =>
    match scopeAttrTypeOf? S (e.scopeType r) (a :: p) with
    | some ty =>
      if ty.temporalSupported then none
      else some s!"`{pathUnder (Root.ofSpec r).name (a :: p)}` has the type `{renderType ty}`; {unsupportedExtension}"
    | none => none
  | _ => none

/-- The unsupported-type finding of a predicate argument other than a variable or a wildcard
(crate `check_predicate_args`). -/
def argUnsupported (S : Schema) (e : ReqEnv) : Term → Option String
  | .var _ | .wildcard => none
  | t => unsupportedOperand S e t

/-- The problems with the atoms of a compound operand (crate `check_arith_atoms`). -/
def arithAtoms (S : Schema) (e : ReqEnv) (Γ : Bindings) : Term → List String
  | .arith _ l r => arithAtoms S e Γ l ++ arithAtoms S e Γ r
  | .wildcard => ["a wildcard (`*` / `_`) cannot appear inside an arithmetic expression; it resolves to no value, so the whole guard would be silently false"]
  | t =>
    match termSort S e Γ t with
    | some (.cedar .int) | none => []
    | some τ =>
      match unsupportedOperand S e t with
      | some m => [m]
      | none => [s!"arithmetic operates only on `Long` values, but this operand has type `{renderSort τ}`"]

/-- The compound-operand problems of a comparison operand. -/
def operandArith (S : Schema) (e : ReqEnv) (Γ : Bindings) : Term → List String
  | .arith op l r => arithAtoms S e Γ (.arith op l r)
  | _ => []

/-- The problem with a comparison's operand types (crate `check_types_in_env`). -/
def comparisonProblem (S : Schema) (e : ReqEnv) (Γ : Bindings) (op : CmpOp) (l r : Term) :
    Option String :=
  match termSort S e Γ l, termSort S e Γ r with
  | some τ₁, some τ₂ =>
    if op.isOrder then
      if τ₁ == .cedar .int && τ₂ == .cedar .int then none
      else some s!"comparison requires numeric operands on both sides, got `{renderSort τ₁}` and `{renderSort τ₂}`"
    else if τ₁ == τ₂ || (eqRestricted? l r == none &&
        match τ₁, τ₂ with
        | .cedar (.entity _), .cedar (.entity _) => true
        | _, _ => false) then none
    else some s!"equality requires both sides to have the same type, got `{renderSort τ₁}` and `{renderSort τ₂}`"
  | _, _ => none

/-- The problems with a comparison's operands' types: an unsupported operand's, which stands for
the comparison, or else the comparison's (crate `check_types_in_env`). -/
def comparisonProblems (S : Schema) (e : ReqEnv) (Γ : Bindings) (op : CmpOp) (l r : Term) :
    List String :=
  match (unsupportedOperand S e l).toList ++ (unsupportedOperand S e r).toList with
  | [] => (comparisonProblem S e Γ op l r).toList
  | us => us

/-- The type of a spliced field in the predicate action's context (crate
`predicate_field_type`). -/
def splicedFieldType? (S : Schema) (a : EntityUID) (p : Path) : Option CedarType :=
  match S.acts.find? a with
  | some entry => contextPathType? entry.context p
  | none => none

/-- The problems with a predicate's arguments in a request environment (crate
`check_predicate_args`). -/
def predArgsProblems (S : Schema) (d : DerivedEventSchema) (e : ReqEnv) (Γ : Bindings)
    (a : EntityUID) (k : String) (args : List (Path × Term)) : List String :=
  let ev := eventOf? d a k
  args.flatMap fun (p, t) =>
    match argUnsupported S e t with
    | some m => [m]
    | none =>
    match (if isSpliced p then splicedFieldType? S a p else none) with
    | some expected =>
      match termSort S e Γ t with
      | some got =>
        if got == .cedar expected then []
        else [s!"argument `{pathText p}` of `{escapedId a.eid}` expects `{renderType expected}` but got `{renderSort got}`"]
      | none => []
    | none =>
      match t with
      | .var _ | .wildcard => []
      | _ =>
        match ev.bind (fieldType? S · p), termSort S e Γ t with
        | some fty, some got =>
          if fieldAccepts fty got then []
          else [s!"argument `{pathText p}` of `{escapedId a.eid}` expects `{renderFieldTy fty}` but got `{renderSort got}`"]
        | _, _ => []

@[simp] theorem eraseDups_eq_nil_iff {α : Type} [BEq α] [LawfulBEq α] (l : List α) :
    l.eraseDups = [] ↔ l = [] := by
  cases l with
  | nil => simp
  | cons a l => simp [List.eraseDups_cons]

mutual

/-- The type problems of a condition in one request environment, with the variables `Γ` in
scope (crate `check_types_in_env`, over `walk_typed`). A node's own findings carry its position
in the crate, which reports one finding once per position (`check_types`, its `seen` set), so a
message a node gives twice (`context.input.at == context.input.at`, both operands unsupported) is
reported once (`eraseDups`). -/
def typesF (S : Schema) (d : DerivedEventSchema) (e : ReqEnv) (Γ : Bindings) :
    Formula → List String
  | .and φ ψ | .since φ _ ψ => typesF S d e Γ φ ++ typesF S d e Γ ψ
  | .not φ | .formerly _ φ | .previous _ φ => typesF S d e Γ φ
  | .exist x φ =>
    if bindersTyped S [x] then typesF S d e ((x.name, annotationSort x.ty) :: Γ) φ else []
  | .pred a k args => (predArgsProblems S d e Γ a k args).eraseDups
  | .tp x =>
    match Γ.lookup x with
    | some τ =>
      if τ == .timepoint then []
      else [s!"`tp({x})` binds `{x}` to the current timepoint, but `{x}` is declared `{renderSort τ}`; a `tp` variable must be declared `Timepoint`"]
    | none => []
  | .cmp op l r =>
    (operandArith S e Γ l ++ operandArith S e Γ r ++ comparisonProblems S e Γ op l r).eraseDups ++
      typesT S d e Γ l ++ typesT S d e Γ r

/-- The type problems of an operand's aggregation bodies. -/
def typesT (S : Schema) (d : DerivedEventSchema) (e : ReqEnv) (Γ : Bindings) :
    Term → List String
  | .agg a => typesA S d e Γ a
  | .arith _ l r => typesT S d e Γ l ++ typesT S d e Γ r
  | _ => []

def typesA (S : Schema) (d : DerivedEventSchema) (e : ReqEnv) (Γ : Bindings) :
    Aggregate → List String
  | .count dom body | .sum _ dom body =>
    if bindersTyped S dom then typesF S d e (binderBindings dom ++ Γ) body else []

end

/-! ## 9. Summands -/

/-- The declared type of a summand, and why it is not summable (crate `sum_summand_type_error`). -/
def summandProblem (s : VarName) : BinderType → Option String
  | .timepoint => some s!"cannot sum `{s}`: sum requires a `Long` summand, but `{s}` is `Timepoint`. Timepoints are ordinal positions, not quantities — use a Timepoint in the `for (…)` binders to keep per-timepoint rows, not as the value being summed."
  | .named path =>
    match path.getLast? with
    | some "Long" => none
    | some "decimal" | some "Decimal" =>
      some s!"cannot sum `{s}`: sum requires a `Long` summand, but `{s}` is `Decimal`. Dogwood arithmetic operates only on `Long` values, not decimals."
    | _ => some s!"cannot sum `{s}`: sum requires a `Long` summand, but `{s}` is `{"::".intercalate path}`."

mutual

/-- Every binder a condition declares, in the order the crate's walk meets them (crate
`collect_declared_binder_types`). -/
def declaredBindersF : Formula → List Binder
  | .and φ ψ | .since φ _ ψ => declaredBindersF φ ++ declaredBindersF ψ
  | .not φ | .formerly _ φ | .previous _ φ => declaredBindersF φ
  | .exist x φ => x :: declaredBindersF φ
  | .pred _ _ _ | .tp _ => []
  | .cmp _ l r => declaredDomT l ++ declaredDomT r ++ declaredBindersT l ++ declaredBindersT r

/-- The `for` lists of an operand's aggregates. -/
def declaredDomT : Term → List Binder
  | .agg (.count dom _) | .agg (.sum _ dom _) => dom
  | .arith _ l r => declaredDomT l ++ declaredDomT r
  | _ => []

/-- The binders the aggregation bodies of an operand declare. -/
def declaredBindersT : Term → List Binder
  | .agg a => declaredBindersA a
  | .arith _ l r => declaredBindersT l ++ declaredBindersT r
  | _ => []

def declaredBindersA : Aggregate → List Binder
  | .count _ body | .sum _ _ body => declaredBindersF body

end

/-- The summand problems at a term a node carries (crate `check_sum_summands`). -/
def summandAt (declared : List Binder) : Term → List String
  | .agg (.sum s dom _) =>
    match (dom.find? (·.name == s)).map (·.ty) |>.or ((declared.reverse.find? (·.name == s)).map (·.ty)) with
    | some ty => (summandProblem s ty).toList
    | none => []
  | _ => []

/-! ## 10. The validity rules -/

/-- The `for`-list problems of the aggregates of an operand (crate `check_for_lists`). -/
def forListAt : Term → List String
  | .agg (.count dom _) | .agg (.sum _ dom _) =>
    ((dom.map (·.name)).zipIdx.filterMap fun (n, i) =>
      if ((dom.map (·.name)).take i).contains n then
        some s!"the `for` list of this aggregation binds `{n}` more than once; give each `for` variable a name of its own, since the rows are projected onto one column per name"
      else none).eraseDups
  | .arith _ l r => forListAt l ++ forListAt r
  | _ => []

/-- A binder's type as written (crate `Type::render`). -/
def binderTypeText : BinderType → String
  | .timepoint => "Timepoint"
  | .named p => "::".intercalate p

/-- The problem with a binder's type (crate `check_binder_types`). -/
def binderTypeProblem (S : Schema) (b : Binder) : Option String :=
  if binderTypeDeclared S b.ty then none
  else if unsupportedExtensionBinder b.ty then
    some s!"the binder `{b.name}` is declared `{binderTypeText b.ty}`; {unsupportedExtension}"
  else some s!"the binder `{b.name}` is declared `{binderTypeText b.ty}`, which names no declared entity type; a binder's type is `Long`, `String`, `Bool`, `decimal`, `Timepoint`, or an entity type the schema declares, written with its namespace"

/-- The binder-type problems of the aggregates of an operand. -/
def binderTypesAt (S : Schema) : Term → List String
  | .agg (.count dom _) | .agg (.sum _ dom _) => (dom.filterMap (binderTypeProblem S)).eraseDups
  | .arith _ l r => binderTypesAt S l ++ binderTypesAt S r
  | _ => []

/-- The first optional attribute along `path` that no fact guards: the full prefix that ends at
it (crate `unguarded_optional`). A path that does not resolve has none. -/
def unguardedOptional (guarded : Path → Bool) : RecordType → Path → Path → Option Path
  | _, _, [] => none
  | attrs, pre, seg :: rest =>
    match attrs.find? seg with
    | none => none
    | some q =>
      if !q.isRequired && !guarded (pre ++ [seg]) then some (pre ++ [seg])
      else match rest, q.getType with
        | [], _ => none
        | _ :: _, .record rty => unguardedOptional guarded rty (pre ++ [seg]) rest
        | _ :: _, _ => none

/-- The unguarded optional reads of a term (crate `check_optional_read`). -/
def optionalAt (C : LeafCtx) : Term → List String
  | .context p =>
    C.actions.filterMap fun (uid, entry) =>
      (unguardedOptional (fun q => decide (Guard.context q ∈ C.facts)) entry.context [] p).map
        fun pre => s!"`context.{pathText p}` reads the optional attribute `{pathText pre}` of the context of `{actionText uid}` with no `has` test guarding it, so a request without it makes the comparison false, and true under `!`; test it first, as in `{pathUnder "context" pre.dropLast} has {pre.getLast?.getD ""} && temporal \{ … }`"
  | .scope r p =>
    if p.isEmpty then []
    else C.actions.flatMap fun (_, entry) =>
      (admittedTypes C.schema entry (Root.ofSpec r) (C.narrow (Root.ofSpec r))).filterMap fun ety =>
        match entityAttrs? C.schema ety with
        | some attrs =>
          (unguardedOptional (fun q => decide (Guard.scope r q ∈ C.facts)) attrs [] p).map
            fun pre => s!"`{pathUnder (Root.ofSpec r).name p}` reads the optional attribute `{pathText pre}` of `{nameText ety}` with no `has` test guarding it, so a request without it makes the comparison false, and true under `!`; test it first, as in `{pathUnder (Root.ofSpec r).name pre.dropLast} has {pre.getLast?.getD ""} && temporal \{ … }`"
        | none => none
  | _ => []

/-- The type at `path` in a record type, when every attribute along it is declared and required
(crate `required_path_type`). -/
def requiredPathType? : RecordType → Path → Option CedarType
  | _, [] => none
  | attrs, [last] =>
    match attrs.find? last with
    | some (.required t) => some t
    | _ => none
  | attrs, seg :: rest@(_ :: _) =>
    match attrs.find? seg with
    | some (.required (.record rty)) => requiredPathType? rty rest
    | _ => none

/-- The sorts a pin's request-side reference has in the environments of an action the rule
decides, when it is a declared, required path there (crate `pin_ref_types`). -/
def pinRefSorts? (C : LeafCtx) (entry : ActionSchemaEntry) (pin : Pin) : Option (List TType) :=
  match pin.root with
  | .context =>
    match pin.contextPath with
    | head :: _ =>
      if isHoistedName head then none
      else (requiredPathType? entry.context pin.contextPath).map fun t => [.cedar t]
    | [] => none
  | .scope =>
    match pin.contextPath with
    | root :: tail =>
      let r? : Option Root := if root == "principal" then some .principal
        else if root == "resource" then some .resource else none
      match r? with
      | none => none
      | some r =>
        let types := admittedTypes C.schema entry r (C.narrow r)
        if tail.isEmpty then some (types.map fun ety => .cedar (.entity ety))
        else types.mapM fun ety =>
          (entityAttrs? C.schema ety).bind fun attrs => (requiredPathType? attrs tail).map .cedar
    | [] => none

/-- A pin's request-side reference as the crate's diagnostics print it: `context.<path>`, or the
scope path as written. -/
def pinReference (pin : Pin) : String :=
  match pin.root with
  | .context => pathUnder "context" pin.contextPath
  | .scope => pathText pin.contextPath

/-- The pin problems of a predicate (crate `check_pins`). -/
def pinsAt (C : LeafCtx) (a : EntityUID) (k : String) : List String :=
  match eventOf? C.events a k with
  | none => []
  | some ev =>
    ev.pins.flatMap fun pin =>
      match fieldType? C.schema ev pin.fieldPath with
      | none => []
      | some fty =>
        C.actions.filterMap fun (uid, entry) =>
          match pinRefSorts? C entry pin with
          | some sorts =>
            match sorts.find? (!TType.temporalSupported ·) with
            | some τ => some s!"pin `{pathText pin.fieldPath}` of `{predHead a k}` correlates the field with `{pinReference pin}`, of type `{renderCSort τ}`; {unsupportedExtension}"
            | none =>
              (sorts.find? (!fieldAccepts fty ·)).map fun τ =>
                s!"pin `{pathText pin.fieldPath}` of `{predHead a k}` correlates the field, of type `{renderFieldTy fty}`, with `{pinReference pin}`, which is a `{renderCSort τ}` in the requests of `{actionText uid}` the rule decides; the field cannot hold it"
          | none => some s!"pin `{pathText pin.fieldPath}` of `{predHead a k}` correlates the field with `{pinReference pin}`, which is not a declared, required attribute in the requests of `{actionText uid}` the rule decides; a pin's request-side path must be, so that every conforming request has its value"

/-- The value sort a binder's declared type means, when it is a value type the schema declares
(crate `binder_value_type`): none for a `Timepoint` and for an undeclared entity type. -/
def binderValueSort? (S : Schema) : BinderType → Option TType
  | .timepoint => none
  | .named path =>
    match path.getLast? with
    | some "Long" => some (.cedar .int)
    | some "String" => some (.cedar .string)
    | some "Bool" | some "Boolean" => some (.cedar (.bool .anyBool))
    | some "decimal" | some "Decimal" => some (.cedar (.ext .decimal))
    | some id => if S.ets.contains ⟨id, path.dropLast⟩ then some (.cedar (.entity ⟨id, path.dropLast⟩)) else none
    | none => none

/-- The binding-field problems of a predicate, with the binders `scope` in scope, innermost first
(crate `check_binding_fields`). -/
def bindingFieldsAt (C : LeafCtx) (scope : List Binder) (a : EntityUID) (k : String)
    (args : List (Path × Term)) : List String :=
  match eventOf? C.events a k with
  | none => []
  | some ev =>
    args.filterMap fun (p, t) =>
      match t with
      | .var x =>
        if isSpliced p then none
        else match fieldType? C.schema ev p, scope.find? (·.name == x) with
          | some fty, some b =>
            let ok := match binderValueSort? C.schema b.ty with
              | some τ => fieldWithin fty τ
              | none => false
            if ok then none
            else some s!"argument `{pathText p}` of `{escapedId a.eid}` expects `{renderFieldTy fty}`, but binds the variable `{x}`, declared `{binderTypeText b.ty}`: a variable bound by a field must have a type every value of the field has"
          | _, _ => none
      | _ => none

/-- The terms a node carries for the optional-read rule (crate `validity::node_terms`). -/
def validityNodeTerms : Formula → List Term
  | .cmp _ l r => termAtoms l ++ termAtoms r
  | .pred _ _ args => argsAtoms args
  | _ => []

/-- What the validity rules report at a node, with the binders in scope. A finding carries the
position the crate reports it at, and the crate keeps the first of a repeated `(message,
position)` (`check_leaf`, its `seen` set): the optional reads of a node share the node's position,
so a message its operands repeat is reported once, while an aggregation's `for`-list and binder
findings carry the aggregation's position (`check_for_lists`, `check_binder_types`), so two
aggregations of one comparison report theirs apart (`forListAt`, `binderTypesAt`). -/
def validityAt (C : LeafCtx) (scope : List Binder) : Formula → List String
  | .pred a k args =>
    ((argsAtoms args).flatMap (optionalAt C) ++ pinsAt C a k ++
      bindingFieldsAt C scope a k args).eraseDups
  | .cmp _ l r =>
    ((termAtoms l ++ termAtoms r).flatMap (optionalAt C)).eraseDups ++
      forListAt l ++ forListAt r ++ binderTypesAt C.schema l ++ binderTypesAt C.schema r
  | .exist x _ => (binderTypeProblem C.schema x).toList
  | _ => []

mutual

/-- The validity rules over a condition, with the binders `scope` in scope (crate `visit`): the
body of an ill-formed binder list is not visited. -/
def validityF (C : LeafCtx) (scope : List Binder) : Formula → List String
  | .and φ ψ => validityAt C scope (.and φ ψ) ++ validityF C scope φ ++ validityF C scope ψ
  | .since φ w ψ => validityAt C scope (.since φ w ψ) ++ validityF C scope φ ++ validityF C scope ψ
  | .not φ => validityAt C scope (.not φ) ++ validityF C scope φ
  | .formerly w φ => validityAt C scope (.formerly w φ) ++ validityF C scope φ
  | .previous w φ => validityAt C scope (.previous w φ) ++ validityF C scope φ
  | .exist x φ =>
    validityAt C scope (.exist x φ) ++
      if bindersTyped C.schema [x] then validityF C (x :: scope) φ else []
  | .pred a k args => validityAt C scope (.pred a k args) ++ validityArgs C scope args
  | .cmp op l r => validityAt C scope (.cmp op l r) ++ validityT C scope l ++ validityT C scope r
  | .tp x => validityAt C scope (.tp x)

/-- The validity rules over the aggregation bodies of a term (crate `visit_term`). -/
def validityT (C : LeafCtx) (scope : List Binder) : Term → List String
  | .agg a => validityA C scope a
  | .arith _ l r => validityT C scope l ++ validityT C scope r
  | _ => []

def validityA (C : LeafCtx) (scope : List Binder) : Aggregate → List String
  | .count dom body | .sum _ dom body =>
    if bindersTyped C.schema dom then validityF C (dom.reverse ++ scope) body else []

def validityArgs (C : LeafCtx) (scope : List Binder) : List (Path × Term) → List String
  | [] => []
  | (_, t) :: args => validityT C scope t ++ validityArgs C scope args

end

/-! ## The leaf -/

/-- Every finding of the temporal dialect on one leaf, in the crate's order. -/
def leafFindings (C : LeafCtx) (φ : Formula) : List String :=
  (eventNamesF C.events φ).toList ++
  walkF (windowsAt C) φ ++
  (horizonProblem C φ).toList ++
  walkF wildcardAt φ ++
  walkTerms (entityAt C.schema C.declaredEnum) φ ++
  walkTerms decimalAt φ ++
  C.actions.flatMap (fun (uid, entry) => walkTerms (pathsAt C uid entry) φ) ++
  checkTpDependence φ ++
  mergeEnvFindings C.envs (fun e => typesF C.schema C.events e (inputBindings e.entry) φ) ++
  walkTerms (summandAt (declaredBindersF φ)) φ ++
  validityF C [] φ

end Dogwood.Frontend.Validate
