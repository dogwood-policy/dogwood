import Dogwood.Spec.EventSchema
import Dogwood.Spec.Temporal.Safety
import Cedar.Validation.Types

/-!
# Temporal conditions: typing

`Formula.WellTyped C Γ φ` states that the temporal condition `φ` is well-typed in the typing
context `C`, with the binders of `Γ` in scope. Validation requires every temporal leaf of a rule
to be well-typed in every request environment of the action schema that the rule's scope admits
(`Dogwood.Spec.PolicySet.Valid`). Together with safety (`Formula.IsSafe`) and runtime conformance,
typing makes every term of every atom an evaluation reaches resolve to a value of its type, and
every aggregate have a total (`Dogwood.Thm.soundness`).

## The typing context

`C : TypingCtx` holds:

* `env`: a request environment of Cedar's validator (`Cedar.Validation.TypeEnv`): the entity
  types and actions of the action schema, and one request type — a principal type, an action, a
  resource type, and the action's context record type;
* `events`: the derived event schema, whose signatures declare the type of every field;
* `maxWindow`: the event schema's `max_window` cap, in seconds;
* `facts`: the attribute paths the Cedar part of the rule has tested present at the leaf's
  position (`Guard`, `Dogwood.Spec.Expr.leafFacts`).

## Sorts

A term has a Cedar type, or is a **timepoint** (`TType.timepoint`). Only a variable declared
`Timepoint`, by `exists` or a `for` list, is a timepoint. A timepoint may be the argument of
`tp`, may be compared for equality with a timepoint, may be a `for` variable of an aggregation,
which keeps the aggregation's rows distinct, and nothing else: no ordering, no arithmetic, no
constant, no predicate argument, and no comparison with a value of another sort. The reference
validator applies the same rules (`extension/temporal/validate.rs`, `check_types`,
`check_arith_atoms`).

## The rules

* **Binders.** Every `exists` binder and `for` variable has a meaningful declared type —
  `Long`, `String`, `Bool`, `decimal`, `Timepoint`, or an entity type the schema declares —
  and is not named after a Cedar request variable. The `for` variables of one aggregation have
  distinct names. A variable is used only where it is bound, so the condition is closed.
* **Comparisons.** Ordering (`<`, `<=`, `>`, `>=`) applies only to two `Long`s. Equality
  (`==`, `!=`) applies to two terms of the same type, which includes two `decimal`s and two
  timepoints; two entities of different types may be compared, unless the equality can bind a
  variable, in which case the types must be equal. A wildcard is not a comparison operand.
* **Arithmetic.** Every atom of a compound operand is a `Long`, and so is an aggregate.
* **Aggregates.** A `sum`'s summand is a `Long` binder of its own `for` list.
* **Predicates.** A predicate names a declared event signature, and each argument a declared
  field of it. A variable argument has a type that every value of the field has; any other
  argument a type the field can hold; a wildcard matches anything. No argument is an aggregate
  or a compound. Every pin of the signature correlates its field with a request-side path that
  is *required* in the environment, of a type the field can hold: so a conforming request always
  has the pin's value.
* **Extension types.** Temporal conditions do not support Cedar's extension types other than
  `decimal`: no request-side path a term reads, and no pin's, has a type that is or holds a
  `datetime`, a `duration`, or an `ipaddr` (`CedarType.temporalSupported`). A schema may
  declare such attributes and fields; a predicate matches such a field only by a wildcard, or
  not at all. No binder has such a type either.
* **Request-side paths.** A `context.<path>` resolves in the environment's context record type,
  and `principal.<path>` / `resource.<path>` in the attributes of the environment's principal or
  resource type. `id` and `type` are attributes like any other, as in Cedar. Every **optional**
  attribute along a path is guarded: the Cedar part of the rule tests it with `has` at the
  leaf's position, as in `context.input has amount && temporal { … context.input.amount … }`.
  An attribute that is required needs no guard.
* **Literals.** An entity literal is of a declared entity type, with one of the type's ids when
  the type is enumerated, or is a declared action; a `decimal` literal parses.
* **Windows.** Every window is positive and at most `max_window`. The cap bounds a window's
  authored length, in seconds, whatever the tick rate the decisions compare in.

`Formula.check` decides typing, reporting what it finds by category
(`Dogwood.Thm.Formula.check_eq_nil_iff`).
-/

namespace Dogwood.Spec.Temporal

open Cedar.Spec (EntityType EntityUID)
open Cedar.Validation (CedarType TypeEnv RecordType Qualified)

/-! ## Reserved names and windows -/

/-- Cedar's request variables, which cannot name a binder. -/
def reservedBinderNames : List VarName := ["principal", "action", "resource", "context"]

/-- The window is positive, its length in seconds fits a `Long`, and it is at most `cap`
seconds. The cap and the bound are on the authored length, as the crate's validator checks them;
the semantics compares the length in ticks (`Window.ticks`). -/
def Window.withinCap (cap : Int) (w : Window) : Bool :=
  0 < w.amount && w.seconds ≤ Int64.MAX && w.seconds ≤ cap

/-- The default `max_window` cap: 24 hours, in seconds. -/
def defaultMaxWindow : Int := 86400

/-! ## Supported types -/

/-- Temporal conditions support the type: it is not, and holds no set element or record
attribute of, one of Cedar's extension types other than `decimal` (`datetime`, `duration`,
`ipaddr`). The reference validator rejects a temporal term of such a type
(`extension/temporal/validate.rs`, `check_unsupported_operand`). -/
def _root_.Cedar.Validation.CedarType.temporalSupported : CedarType → Bool
  | .ext .decimal => true
  | .ext _ => false
  | .set ty => ty.temporalSupported
  | .record rty =>
    rty.toList.attach.all fun ⟨(_, qty), _⟩ =>
      match qty with
      | .optional ty => ty.temporalSupported
      | .required ty => ty.temporalSupported
  | .bool _ | .int | .string | .entity _ => true
termination_by ty => sizeOf ty
decreasing_by
  any_goals simp
  any_goals
    rename_i hmem
    have h := List.sizeOf_lt_of_mem hmem
    cases rty
    simp only [Prod.mk.sizeOf_spec, Qualified.optional.sizeOf_spec, Qualified.required.sizeOf_spec,
      Cedar.Data.Map.toList_mk_id, Cedar.Data.Map.mk.sizeOf_spec, gt_iff_lt] at h ⊢
    omega

/-! ## Sorts and guards -/

/-- The sort of a temporal term: a Cedar type, or a timepoint. -/
inductive TType where
  | cedar (ty : CedarType)
  | timepoint
deriving DecidableEq, Repr, Inhabited

/-- Temporal conditions support the sort: a timepoint, or a Cedar type they support. -/
def TType.temporalSupported : TType → Bool
  | .cedar ty => ty.temporalSupported
  | .timepoint => true

/-- An attribute path that the Cedar part of a rule has tested present, with `has`: a path of
the request context, or of the principal's or resource's attributes. -/
inductive Guard where
  | context (path : Path)
  | scope (root : ScopeRoot) (path : Path)
deriving DecidableEq, Repr, Inhabited

/-- What the typing of a temporal leaf needs. -/
structure TypingCtx where
  env : TypeEnv
  events : EventSchema
  maxWindow : Int
  facts : List Guard

/-- Binders in scope, innermost first. -/
abbrev Bindings := List (VarName × TType)

/-- The type of the innermost binder named `x`. -/
def Bindings.lookup (Γ : Bindings) (x : VarName) : Option TType :=
  (Γ.find? (·.1 == x)).map (·.2)

/-! ## Binder types -/

/-- The sort a binder's declared type means, in an environment whose entity types are `ets`.
As in the reference validator, a scalar type is named by its last segment. Cedar's extension
types other than `decimal` name none (`CedarType.temporalSupported`), unless an entity type is
so named. -/
def BinderType.sort? (ets : Cedar.Validation.EntitySchema) : BinderType → Option TType
  | .timepoint => some .timepoint
  | .named path =>
    match path.getLast? with
    | some "Long" => some (.cedar .int)
    | some "String" => some (.cedar .string)
    | some "Bool" | some "Boolean" => some (.cedar (.bool .anyBool))
    | some "decimal" | some "Decimal" => some (.cedar (.ext .decimal))
    | some id =>
      let ety : EntityType := ⟨id, path.dropLast⟩
      if ets.contains ety then some (.cedar (.entity ety)) else none
    | none => none

/-- A binder's name and sort, when its type is meaningful and its name is not reserved. -/
def Binder.sort? (ets : Cedar.Validation.EntitySchema) (b : Binder) : Option (VarName × TType) :=
  if reservedBinderNames.contains b.name then none else (b.ty.sort? ets).map (b.name, ·)

/-- A `for` list's binders, as bindings, when every binder is meaningful and their names are
distinct. -/
def domainSorts? (ets : Cedar.Validation.EntitySchema) (dom : List Binder) : Option Bindings :=
  if (dom.map (·.name)).Nodup then dom.mapM (Binder.sort? ets) else none

/-! ## Request-side paths -/

/-- The type of the attribute path `p` (after the prefix `pre`) in the record type `rty`, when
every attribute along it is declared, and each optional one is present by `present`: `present q`
holds of the full prefix `q` that ends at the attribute. -/
def pathType? (present : Path → Bool) (rty : RecordType) (pre : Path) : Path → Option CedarType
  | [] => none
  | a :: p =>
    match rty.find? a with
    | some qty =>
      if qty.isRequired || present (pre ++ [a]) then
        match p, qty.getType with
        | [], ty => some ty
        | _ :: _, .record rty' => pathType? present rty' (pre ++ [a]) p
        | _ :: _, _ => none
      else none
    | none => none

/-- The entity type of a request-scope root in the environment. -/
def TypingCtx.scopeType (C : TypingCtx) : ScopeRoot → EntityType
  | .principal => C.env.reqty.principal
  | .resource => C.env.reqty.resource

/-- The type of a `context.<p>` term: its type in the context record, every optional attribute
along it guarded. -/
def TypingCtx.contextType? (C : TypingCtx) (p : Path) : Option CedarType :=
  pathType? (fun q => decide (Guard.context q ∈ C.facts)) C.env.reqty.context [] p

/-- The type of a `principal.<p>` / `resource.<p>` attribute term: its type in the attributes of
the root's entity type, every optional attribute along it guarded. -/
def TypingCtx.scopeAttrType? (C : TypingCtx) (r : ScopeRoot) (p : Path) : Option CedarType :=
  match C.env.ets.attrs? (C.scopeType r) with
  | some rty => pathType? (fun q => decide (Guard.scope r q ∈ C.facts)) rty [] p
  | none => none

/-! ## Fields -/

/-- A term of sort `τ` can match a value of the field type: the field can hold a value of
sort `τ`. -/
def _root_.Dogwood.Spec.FieldTy.Accepts : FieldTy → TType → Prop
  | .cedar ty, τ => τ = .cedar ty
  | .entities etys, τ => ∃ ety ∈ etys, τ = .cedar (.entity ety)

/-- Every value of the field type has sort `τ`: a variable of sort `τ` can be bound by the
field. -/
def _root_.Dogwood.Spec.FieldTy.Within : FieldTy → TType → Prop
  | .cedar ty, τ => τ = .cedar ty
  | .entities etys, τ => etys ≠ [] ∧ ∀ ety ∈ etys, τ = .cedar (.entity ety)

/-! ## Pins -/

/-- The sort of a pin's request-side reference, in the context `C`. -/
def _root_.Dogwood.Spec.PinRef.sort? (C : TypingCtx) : PinRef → Option TType
  | .context p => ((C.contextType? p).filter (·.temporalSupported)).map .cedar
  | .scope r [] => some (.cedar (.entity (C.scopeType r)))
  | .scope r p => ((C.scopeAttrType? r p).filter (·.temporalSupported)).map .cedar

/-- Every pin of the signature correlates a declared field with a request-side path that is
required in the environment (it needs no guard), of a type the field can hold. -/
def _root_.Dogwood.Spec.EventSignature.PinsTyped (C : TypingCtx) (sig : EventSignature) : Prop :=
  ∀ pin ∈ sig.pins, ∃ fd τ, sig.field? pin.field = some fd ∧
    pin.ref.sort? { C with facts := [] } = some τ ∧ fd.ty.Accepts τ

/-! ## Typing -/

/-- A term in a predicate-argument position is neither an aggregate nor a compound. -/
def Term.Simple : Term → Prop
  | .agg _ | .arith _ _ _ => False
  | _ => True

/-- The ordering operators, which apply only to `Long`s. -/
def CmpOp.IsOrder : CmpOp → Prop
  | .lt | .le | .gt | .ge => True
  | .eq | .ne => False

/-- Two terms of these sorts may be compared for equality: the same sort, or two entity types
when the equality cannot bind a variable. -/
def EqCompatible (l r : Term) (τ₁ τ₂ : TType) : Prop :=
  τ₁ = τ₂ ∨ (eqRestricted? l r = none ∧ ∃ e₁ e₂, τ₁ = .cedar (.entity e₁) ∧ τ₂ = .cedar (.entity e₂))

mutual

/-- `Γ ⊢ t : τ` in the context `C`. -/
inductive Term.Typed (C : TypingCtx) : Bindings → Term → TType → Prop
  | entity {Γ uid} :
      (C.env.ets.isValidEntityUID uid || C.env.acts.contains uid) = true →
      Term.Typed C Γ (.entity uid) (.cedar (.entity uid.ty))
  | long {Γ i} : Term.Typed C Γ (.long i) (.cedar .int)
  | decimal {Γ s} : (Cedar.Spec.Ext.Decimal.parse s).isSome = true →
      Term.Typed C Γ (.decimal s) (.cedar (.ext .decimal))
  | string {Γ s} : Term.Typed C Γ (.string s) (.cedar .string)
  | bool {Γ b} : Term.Typed C Γ (.bool b) (.cedar (.bool .anyBool))
  | context {Γ p ty} : C.contextType? p = some ty → ty.temporalSupported = true →
      Term.Typed C Γ (.context p) (.cedar ty)
  | scopeRoot {Γ r} : Term.Typed C Γ (.scope r []) (.cedar (.entity (C.scopeType r)))
  | scopeAttr {Γ r p ty} : p ≠ [] → C.scopeAttrType? r p = some ty → ty.temporalSupported = true →
      Term.Typed C Γ (.scope r p) (.cedar ty)
  | var {Γ x τ} : Γ.lookup x = some τ → Term.Typed C Γ (.var x) τ
  | agg {Γ a} : Aggregate.Typed C Γ a → Term.Typed C Γ (.agg a) (.cedar .int)
  | arith {Γ op l r} : Term.Typed C Γ l (.cedar .int) → Term.Typed C Γ r (.cedar .int) →
      Term.Typed C Γ (.arith op l r) (.cedar .int)

/-- An aggregation is well-typed. -/
inductive Aggregate.Typed (C : TypingCtx) : Bindings → Aggregate → Prop
  | count {Γ dom body Δ} : domainSorts? C.env.ets dom = some Δ →
      Formula.WellTyped C (Δ ++ Γ) body → Aggregate.Typed C Γ (.count dom body)
  | sum {Γ s dom body Δ} : domainSorts? C.env.ets dom = some Δ → (s, .cedar .int) ∈ Δ →
      Formula.WellTyped C (Δ ++ Γ) body → Aggregate.Typed C Γ (.sum s dom body)

/-- `Γ ⊢ φ` in the context `C`. -/
inductive Formula.WellTyped (C : TypingCtx) : Bindings → Formula → Prop
  | and {Γ φ ψ} : Formula.WellTyped C Γ φ → Formula.WellTyped C Γ ψ →
      Formula.WellTyped C Γ (.and φ ψ)
  | not {Γ φ} : Formula.WellTyped C Γ φ → Formula.WellTyped C Γ (.not φ)
  | formerly {Γ w φ} : w.withinCap C.maxWindow = true → Formula.WellTyped C Γ φ →
      Formula.WellTyped C Γ (.formerly w φ)
  | previous {Γ w φ} : w.withinCap C.maxWindow = true → Formula.WellTyped C Γ φ →
      Formula.WellTyped C Γ (.previous w φ)
  | since {Γ φ w ψ} : w.withinCap C.maxWindow = true → Formula.WellTyped C Γ φ →
      Formula.WellTyped C Γ ψ → Formula.WellTyped C Γ (.since φ w ψ)
  | pred {Γ a k args sig} : C.events.signature? a k = some sig →
      (∀ arg ∈ args, Formula.ArgTyped C Γ sig arg) → sig.PinsTyped C →
      Formula.WellTyped C Γ (.pred a k args)
  | eq {Γ op l r τ₁ τ₂} : ¬ op.IsOrder → Term.Typed C Γ l τ₁ → Term.Typed C Γ r τ₂ →
      EqCompatible l r τ₁ τ₂ → Formula.WellTyped C Γ (.cmp op l r)
  | ord {Γ op l r} : op.IsOrder → Term.Typed C Γ l (.cedar .int) →
      Term.Typed C Γ r (.cedar .int) → Formula.WellTyped C Γ (.cmp op l r)
  | exist {Γ x φ b} : Binder.sort? C.env.ets x = some b → Formula.WellTyped C (b :: Γ) φ →
      Formula.WellTyped C Γ (.exist x φ)
  | tp {Γ x} : Γ.lookup x = some .timepoint → Formula.WellTyped C Γ (.tp x)

/-- A predicate argument is well-typed against the signature. -/
inductive Formula.ArgTyped (C : TypingCtx) : Bindings → EventSignature → Path × Term → Prop
  | wildcard {Γ sig p fd} : sig.field? p = some fd → Formula.ArgTyped C Γ sig (p, .wildcard)
  | var {Γ sig p fd x τ} : sig.field? p = some fd → Γ.lookup x = some τ → fd.ty.Within τ →
      Formula.ArgTyped C Γ sig (p, .var x)
  | term {Γ sig p fd t τ} : sig.field? p = some fd → t.Simple → (∀ x, t ≠ .var x) →
      t ≠ .wildcard → Term.Typed C Γ t τ → fd.ty.Accepts τ → Formula.ArgTyped C Γ sig (p, t)

end

end Dogwood.Spec.Temporal
