import Dogwood.Frontend.Validate.Cedar
import Dogwood.Eval.Validity

/-!
# What the frontend's earlier stages guarantee, as checks on the lowered set

The soundness theorem of the validator (`Dogwood.Thm.Frontend.validate_sound`) takes the earlier
stages' acceptance as hypotheses, each stated as a property of the lowered set that the stage
guarantees, and each decided here, so that it can be checked on any lowered set (and is, on the
corpus):

* **parse-time checks** (`parseChecked`, `extension/temporal/check.rs`, run on every leaf at
  parsing and after macro expansion): each leaf is closed, binds no reserved name, places
  aggregates and compounds only in comparison operands, sums a binder of its own `for` list, and
  is safe. Pin injection keeps each property (`Formula.isSafe_injectPins` for safety). No leaf
  has a bare `context` term (`leavesNoEmptyContext`);
* **names** (`namesOnce`, `cedarify`): the lowered rules read each hoisted leaf once, in its own
  rule, as `context.<id>` (temporal) or `context.providers.<id>` (provider), and a temporal leaf's
  id is a name lowering reserves;
* **scopes** (`scopesCovered`, `scope_target_actions`, `scope_constraint`): each leaf's target
  actions and principal and resource narrowing admit every request environment its rule's scope
  admits;
* **provider types** (`providerTypesAgree`): the projection's signature of each declared
  provider is the crate's declaration, its types as the crate converts them
  (`ParamType::to_cedar_type_with`), and the augmented schema's `providers` record types each
  provider field so, with a type well-formed in it (`providerTypesWellFormed`);
* **temporal attributes** (`temporalAttrsBool`): the augmented schema types each temporal leaf's
  attribute `Bool`;
* **derivation** (`derivedFacts`, `event_schema/derive.rs`): every spliced field of an event
  resolves in its action's context, and every pin's field is a declared field of its event;
* **lowered rules** (`policiesLeafless`): the lowered rules are Cedar's, without leaves;
* **the schema's shape** (`appliesToDeclared`, `providersNotEntity`): every entity type an action
  admits is declared, and with a provider leaf no action's `providers` attribute is an entity;
* **the specification's names** (`specNamesAbsent`): no action's context declares, and no rule
  reads off the context, an attribute named like the specification's leaf attributes
  (`__dogwood_leaf_<k>`).
-/

namespace Dogwood.Frontend.Validate

open Dogwood.Spec (Expr Policy Path)
open Dogwood.Spec.Temporal
open Cedar.Validation (CedarType Schema)

/-! ## Parse-time checks -/

mutual

/-- No binder is named after a Cedar request variable (crate `reject_reserved_binder`). -/
def noReservedF : Formula → Bool
  | .and φ ψ | .since φ _ ψ => noReservedF φ && noReservedF ψ
  | .not φ | .formerly _ φ | .previous _ φ => noReservedF φ
  | .exist x φ => !reservedBinderNames.contains x.name && noReservedF φ
  | .pred _ _ args => noReservedArgs args
  | .cmp _ l r => noReservedT l && noReservedT r
  | .tp _ => true

def noReservedT : Term → Bool
  | .agg (.count dom body) | .agg (.sum _ dom body) =>
    dom.all (fun b => !reservedBinderNames.contains b.name) && noReservedF body
  | .arith _ l r => noReservedT l && noReservedT r
  | _ => true

def noReservedArgs : List (Path × Term) → Bool
  | [] => true
  | (_, t) :: args => noReservedT t && noReservedArgs args

end

mutual

/-- Aggregates and compounds are only comparison operands, or atoms of compound operands (crate
`check_operand`, `reject_nested_agg`). -/
def wellPlacedF : Formula → Bool
  | .and φ ψ | .since φ _ ψ => wellPlacedF φ && wellPlacedF ψ
  | .not φ | .formerly _ φ | .previous _ φ | .exist _ φ => wellPlacedF φ
  | .pred _ _ args => args.all (·.2.simple)
  | .cmp _ l r => wellPlacedT l && wellPlacedT r
  | .tp _ => true

def wellPlacedT : Term → Bool
  | .agg (.count _ body) | .agg (.sum _ _ body) => wellPlacedF body
  | .arith _ l r => wellPlacedT l && wellPlacedT r
  | _ => true

end

mutual

/-- Every `sum` adds a binder of its own `for` list (crate `check_aggregation`). -/
def summandsOwnF : Formula → Bool
  | .and φ ψ | .since φ _ ψ => summandsOwnF φ && summandsOwnF ψ
  | .not φ | .formerly _ φ | .previous _ φ | .exist _ φ => summandsOwnF φ
  | .pred _ _ args => summandsOwnArgs args
  | .cmp _ l r => summandsOwnT l && summandsOwnT r
  | .tp _ => true

def summandsOwnT : Term → Bool
  | .agg (.sum s dom body) => (dom.map (·.name)).contains s && summandsOwnF body
  | .agg (.count _ body) => summandsOwnF body
  | .arith _ l r => summandsOwnT l && summandsOwnT r
  | _ => true

def summandsOwnArgs : List (Path × Term) → Bool
  | [] => true
  | (_, t) :: args => summandsOwnT t && summandsOwnArgs args

end

mutual

/-- No term of the condition is `context` with an empty path: the crate's temporal grammar has
no bare `context` term (a `context.<path>` has a segment), and the projection keeps the path. -/
def noEmptyContextF : Formula → Bool
  | .and φ ψ | .since φ _ ψ => noEmptyContextF φ && noEmptyContextF ψ
  | .not φ | .formerly _ φ | .previous _ φ | .exist _ φ => noEmptyContextF φ
  | .pred _ _ args => noEmptyContextArgs args
  | .cmp _ l r => noEmptyContextT l && noEmptyContextT r
  | .tp _ => true

def noEmptyContextT : Term → Bool
  | .context [] => false
  | .agg (.count _ body) | .agg (.sum _ _ body) => noEmptyContextF body
  | .arith _ l r => noEmptyContextT l && noEmptyContextT r
  | _ => true

def noEmptyContextArgs : List (Path × Term) → Bool
  | [] => true
  | (_, t) :: args => noEmptyContextT t && noEmptyContextArgs args

end

/-- What the crate's parse-time checks guarantee of a temporal leaf: it is closed
(`check_leaf_closed`), binds no reserved name, places its aggregates and compounds in comparison
operands, sums its own binders, and is safe (`check_condition`, `check_demands`, which are
stricter than `Formula.IsSafe`). -/
def parseChecked (φ : Formula) : Bool :=
  φ.fv.isEmpty && noReservedF φ && wellPlacedF φ && summandsOwnF φ && Dogwood.Eval.isSafeB φ

/-- Every temporal leaf of the lowered set passed the parse-time checks. -/
def leavesParseChecked (l : Lowered) : Bool :=
  l.temporal.all fun f => match f.condition.condition.toFormula with
    | .ok φ => parseChecked φ
    | .error _ => true

/-- No temporal leaf of the lowered set has a bare `context` term. -/
def leavesNoEmptyContext (l : Lowered) : Bool :=
  l.temporal.all fun f => match f.condition.condition.toFormula with
    | .ok φ => noEmptyContextF φ
    | .error _ => true

/-! ## Names -/

mutual

/-- The hoisted leaves an expression reads, in evaluation order, as the conformance projection
puts them back (`putBack`): `(true, id)` for `context.<id>` of a temporal leaf, `(false, id)`
for `context.providers.<id>` of a provider leaf. -/
def hoistedReads (tids pids : List String) : Expr → List (Bool × String)
  | .getAttr e a =>
    if isContext e && tids.contains a then [(true, a)]
    else if isContextProviders e && pids.contains a then [(false, a)]
    else hoistedReads tids pids e
  | .lit _ | .var _ | .temporal _ | .provider _ => []
  | .ite c t e => hoistedReads tids pids c ++ hoistedReads tids pids t ++ hoistedReads tids pids e
  | .and a b | .or a b | .binaryApp _ a b => hoistedReads tids pids a ++ hoistedReads tids pids b
  | .unaryApp _ e | .hasAttr e _ | .extHasAttr e _ _ => hoistedReads tids pids e
  | .set xs | .call _ xs => hoistedReadsList tids pids xs
  | .record axs => hoistedReadsRecord tids pids axs

def hoistedReadsList (tids pids : List String) : List Expr → List (Bool × String)
  | [] => []
  | x :: xs => hoistedReads tids pids x ++ hoistedReadsList tids pids xs

def hoistedReadsRecord (tids pids : List String) : List (String × Expr) → List (Bool × String)
  | [] => []
  | (_, x) :: axs => hoistedReads tids pids x ++ hoistedReadsRecord tids pids axs

end

/-- The hoisted reads of each lowered rule. -/
def ruleReads (l : Lowered) : List (List (Bool × String)) :=
  l.policies.map fun q => hoistedReads (l.temporal.map (·.id)) (l.providers.map (·.id)) q.toExpr

/-- Lowering's names: each leaf is read once, in its own rule; a temporal leaf's id is a reserved
name other than `providers` (`<rule>__temporal_<n>`). -/
def namesOnce (l : Lowered) : Bool :=
  let reads := ruleReads l
  l.temporalRules.length == l.temporal.length && l.providerRules.length == l.providers.length &&
    decide reads.flatten.Nodup &&
    (l.temporal.zip l.temporalRules).all (fun (f, k) => ((reads[k]?).getD []).contains (true, f.id)) &&
    (l.providers.zip l.providerRules).all (fun (g, k) => ((reads[k]?).getD []).contains (false, g.id)) &&
    l.temporal.all (fun f => isHoistedName f.id && f.id != "providers")

/-! ## Scopes -/

/-- The action schema the conformance projection reads off the augmented schema. -/
def specActionSchema (l : Lowered) : Schema :=
  (actionSchemaJson l.schema l.hoistedNames).toSchema

/-- A leaf's target actions and narrowing admit every request environment of the action schema
that its rule's scope admits. -/
def coversScope (l : Lowered) (q : Policy) (targets : List (String × String))
    (p r : ScopeConstraint) : Bool :=
  let A := specActionSchema l
  A.environments.all fun env => !(q.admits A env) ||
    (targets.any (fun (ns, id) => actionUidOf ns id == env.reqty.action) &&
      constraintAdmits l.schema p env.reqty.principal &&
      constraintAdmits l.schema r env.reqty.resource)

/-- Every leaf's metadata covers its rule's scope. -/
def scopesCovered (l : Lowered) : Bool :=
  (l.temporal.zip l.temporalRules).all (fun (f, k) => match l.policies[k]? with
    | some q => coversScope l q f.targetActions f.principal f.resource
    | none => false) &&
  (l.providers.zip l.providerRules).all (fun (g, k) => match l.policies[k]? with
    | some q => coversScope l q g.targetActions g.principal g.resource
    | none => false)

/-! ## Provider types -/

/-- A declared provider, as the crate types its declaration. -/
def crateSignature (names : List (String × String)) (fn : Cedar.Spec.Name)
    (d : ProviderDecls.ProviderDecl) : Dogwood.Spec.Provider.Signature where
  function := fn
  args := d.argumentTypes.map (paramCType names)
  output := paramCType names d.outputType
  methods := d.methods.map fun (m, md) =>
    { name := m, args := md.argumentTypes.map (paramCType names),
      input := md.inputType.map (paramCType names), output := paramCType names md.outputType }

/-- Two provider signatures are the same. -/
def sigEq (a b : Dogwood.Spec.Provider.Signature) : Bool :=
  a.function == b.function && a.args == b.args && a.output == b.output &&
    a.methods.length == b.methods.length &&
    (a.methods.zip b.methods).all fun (x, y) =>
      x.name == y.name && x.args == y.args && x.input == y.input && x.output == y.output

/-- The type the crate gives a provider leaf's value: its last method's output type, or its
provider's. -/
def crateOutputType (g : LoweredProviderField) (d : ProviderDecls.ProviderDecl) : Option CedarType :=
  match g.methods.getLast? with
  | none => some (paramCType g.entityTypeNames d.outputType)
  | some m => (d.methods.lookup m.name).map fun md => paramCType g.entityTypeNames md.outputType

/-- The projection's provider declarations are the crate's, and the augmented schema's `providers`
record types each provider field as the crate types its value. -/
def providerTypesAgree (l : Lowered) : Bool :=
  let D := (providerDeclsToSpec l.declarations l.schema).1
  l.providers.all fun g =>
    match g.declaration, g.toCall with
    | some d, .ok c =>
      (match D.find? c.function with
        | some sig => sigEq sig (crateSignature g.entityTypeNames c.function d)
        | none => false) &&
      l.schema.acts.toList.all fun (_, e) =>
        match e.context.find? "providers" with
        | some q => match q.getType with
          | .record R => (R.find? g.id).all fun q' => some q'.getType == crateOutputType g d
          | _ => true
        | none => true
    | _, _ => true

/-- A request-less environment of a schema: what the well-formedness of a type reads. -/
def schemaEnv (S : Schema) : Cedar.Validation.TypeEnv := { ets := S.ets, acts := S.acts, reqty := default }

/-- The type the crate gives each provider leaf's value is well-formed in the augmented schema:
the entity types it names are declared, and its booleans are Cedar's `Bool`. (Cedar's schema
constructor resolves the shared provider type the crate synthesizes, so every entity type it
names is declared.) -/
def providerTypesWellFormed (l : Lowered) : Bool :=
  l.providers.all fun g => match g.declaration with
    | some d => (crateOutputType g d).all fun ty =>
        (match ty.validateWellFormed (schemaEnv l.schema) with
          | .ok () => true
          | .error _ => false) &&
        (match ty.validateLifted with
          | .ok () => true
          | .error _ => false)
    | none => true

/-- Every entity type an action admits for its principal or resource is a declared entity type
(Cedar's schema constructor requires it; cedar-lean's well-formedness check also admits an
action's type). -/
def appliesToDeclared (l : Lowered) : Bool :=
  l.schema.acts.toList.all fun (_, e) =>
    e.appliesToPrincipal.toList.all l.schema.ets.contains &&
      e.appliesToResource.toList.all l.schema.ets.contains

/-- When the set has a provider leaf, no action declares its `providers` context attribute as an
entity (the crate grafts a record onto the actions it targets; an entity's attributes would be read
through it elsewhere). -/
def providersNotEntity (l : Lowered) : Bool :=
  l.providers.isEmpty || l.schema.acts.toList.all fun (_, e) =>
    match e.context.find? "providers" with
    | some q => match q.getType with
      | .entity _ => false
      | _ => true
    | none => true

/-! ## Temporal attributes, derivation, lowered rules -/

/-- The augmented schema types each temporal leaf's attribute `Bool`. -/
def temporalAttrsBool (l : Lowered) : Bool :=
  l.schema.acts.toList.all fun (_, e) =>
    l.temporal.all fun f => (e.context.find? f.id).all (·.getType == .bool .anyBool)

/-- Every spliced field of a derived event resolves in its action's context, and every pin's
field is a declared field of its event. -/
def derivedFacts (l : Lowered) : Bool :=
  l.eventSchema.events.all fun ev =>
    let ctx := (l.schema.acts.find? (actionUid ev.namespace ev.action)).map (·.context)
    ev.leafFields.all (fun (p, _) => !isSpliced p || (ctx.bind (pathType · p)).isSome) &&
      ev.pins.all fun pin => ev.leafFields.any (·.1 == pin.fieldPath)

/-- The lowered rules have no leaves. -/
def policiesLeafless (l : Lowered) : Bool :=
  l.policies.all fun q => q.toExpr.leaves.isEmpty

mutual

/-- The attributes an expression reads or tests off `context`. -/
def contextAttrs : Expr → List String
  | .getAttr e a | .hasAttr e a | .extHasAttr e a _ =>
    match e with
    | .var .context => [a]
    | _ => contextAttrs e
  | .lit _ | .var _ | .temporal _ | .provider _ => []
  | .ite c t e => contextAttrs c ++ contextAttrs t ++ contextAttrs e
  | .and a b | .or a b | .binaryApp _ a b => contextAttrs a ++ contextAttrs b
  | .unaryApp _ e => contextAttrs e
  | .set xs | .call _ xs => contextAttrsList xs
  | .record axs => contextAttrsRecord axs

def contextAttrsList : List Expr → List String
  | [] => []
  | x :: xs => contextAttrs x ++ contextAttrsList xs

def contextAttrsRecord : List (String × Expr) → List String
  | [] => []
  | (_, x) :: axs => contextAttrs x ++ contextAttrsRecord axs

end

/-- A name of the specification's leaf attributes' shape: `__dogwood_leaf_` and anything. -/
def isSpecLeafName (a : String) : Bool := "__dogwood_leaf_".toList.isPrefixOf a.toList

/-- No action's context declares, and no lowered rule reads off the context, an attribute named
like the specification's leaf attributes. -/
def specNamesAbsent (l : Lowered) : Bool :=
  l.schema.acts.toList.all (fun (_, e) => e.context.toList.all fun (a, _) => !isSpecLeafName a) &&
    l.policies.all fun q => (contextAttrs q.toExpr).all (!isSpecLeafName ·)

/-- Every assumption, decided. -/
def assumptions (l : Lowered) : List (String × Bool) :=
  [("leavesParseChecked", leavesParseChecked l), ("leavesNoEmptyContext", leavesNoEmptyContext l),
   ("namesOnce", namesOnce l),
   ("scopesCovered", scopesCovered l), ("providerTypesAgree", providerTypesAgree l),
   ("temporalAttrsBool", temporalAttrsBool l), ("derivedFacts", derivedFacts l),
   ("policiesLeafless", policiesLeafless l), ("specNamesAbsent", specNamesAbsent l),
   ("providerTypesWellFormed", providerTypesWellFormed l), ("appliesToDeclared", appliesToDeclared l),
   ("providersNotEntity", providersNotEntity l),
   ("schemaWellFormed", match l.schema.validateWellFormed with | .ok () => true | .error _ => false)]

end Dogwood.Frontend.Validate
