import Dogwood.Spec.Temporal.Typing

/-!
# Deciding typing

`Term.check? C Γ t` computes the sort of a well-typed term, or the category of the first
problem it finds. `Formula.check C Γ φ` lists the categories of the problems it finds in a
condition: none exactly when the condition is well-typed
(`Dogwood.Thm.Formula.check_eq_nil_iff`). They are not part of the specification: the
conformance harness runs them, and compares the categories with the crate's findings.
-/

namespace Dogwood.Eval

open Dogwood.Spec Dogwood.Spec.Temporal
open Cedar.Validation (CedarType)

/-- A category of validation finding. -/
inductive Finding where
  /-- A predicate names an undeclared event, or an undeclared field of it. -/
  | eventName
  /-- A window is not positive, or exceeds `max_window`. -/
  | window
  /-- A temporal leaf looks back further than `max_horizon` in total (`Formula.horizon`). -/
  | horizon
  /-- A binder's type is meaningless, its name is reserved, or two `for` variables share a
  name. -/
  | binder
  /-- A variable is used where it is not bound: the condition is not closed. -/
  | unbound
  /-- `tp(x)` reads a variable that is not a `Timepoint`, or a timepoint is ordered, is an
  arithmetic operand, or is compared with a value of another type. -/
  | timepoint
  /-- A comparison's operands have types it does not apply to. -/
  | operand
  /-- A predicate argument has a type its field cannot hold. -/
  | argument
  /-- A request-side path, an entity literal, or a `decimal` literal does not resolve. -/
  | path
  /-- A request-side path reads an optional attribute that no `has` test guards. -/
  | optional
  /-- A request-side path has a type temporal conditions do not support: it is or holds one of
  Cedar's extension types other than `decimal` (`CedarType.temporalSupported`). -/
  | extension
  /-- A pin correlates a field with a request-side path that is not required, or of the wrong
  type. -/
  | pin
  /-- A `sum` adds a variable that is not a `Long` binder of its own `for` list. -/
  | summand
  /-- An aggregate or a compound is a predicate argument, or a wildcard a comparison operand. -/
  | placement
  /-- A quantified variable is not range-restricted, or an atom reads a variable that is not. -/
  | safety
  /-- A monitoring scope does not vary with the timepoint. -/
  | timeDependence
  /-- Cedar's validator rejects the lowered rules. -/
  | cedar
  /-- The Cedar part reads `context` other than through an attribute, or reads a leaf's
  attribute; or a leaf's attribute collides with a declared one. -/
  | contextRead
  /-- A provider invocation names an undeclared provider or method, or has the wrong
  arguments. -/
  | provider
  /-- The augmented schema is not well-formed (`Cedar.Validation.Schema.validateWellFormed`). -/
  | schema
deriving DecidableEq, Repr

/-- `FieldTy.Accepts`, decided. -/
def acceptsB : FieldTy → TType → Bool
  | .cedar ty, τ => τ == .cedar ty
  | .entities etys, τ => etys.any fun ety => τ == .cedar (.entity ety)

/-- `FieldTy.Within`, decided. -/
def withinB : FieldTy → TType → Bool
  | .cedar ty, τ => τ == .cedar ty
  | .entities etys, τ => !etys.isEmpty && etys.all fun ety => τ == .cedar (.entity ety)

/-- `EqCompatible`, decided. -/
def eqCompatibleB (l r : Term) (τ₁ τ₂ : TType) : Bool :=
  τ₁ == τ₂ || (eqRestricted? l r == none &&
    match τ₁, τ₂ with
    | .cedar (.entity _), .cedar (.entity _) => true
    | _, _ => false)

/-- `CmpOp.IsOrder`, decided. -/
def _root_.Dogwood.Spec.Temporal.CmpOp.isOrder : CmpOp → Bool
  | .lt | .le | .gt | .ge => true
  | .eq | .ne => false

/-- `Term.Simple`, decided. -/
def _root_.Dogwood.Spec.Temporal.Term.simple : Term → Bool
  | .agg _ | .arith _ _ _ => false
  | _ => true

/-- Whether a path is declared, guarded or not: tells an unguarded optional attribute from an
undeclared one. -/
def pathDeclared (rty : Cedar.Validation.RecordType) (p : Path) : Bool :=
  (pathType? (fun _ => true) rty [] p).isSome

/-- The finding for a request-side path that does not type. -/
def pathFinding (declared : Bool) : Finding := if declared then .optional else .path

/-- `EventSignature.PinsTyped`, decided. -/
def pinsTypedB (C : TypingCtx) (sig : EventSignature) : Bool :=
  sig.pins.all fun pin =>
    match sig.field? pin.field, pin.ref.sort? { C with facts := [] } with
    | some fd, some τ => acceptsB fd.ty τ
    | _, _ => false

end Dogwood.Eval

namespace Dogwood.Spec.Temporal

open Dogwood.Eval

/-- The sort of a term that is neither an aggregate nor a compound, or the first problem found.
An aggregate or a compound is reported as misplaced. -/
def Term.checkSimple? (C : TypingCtx) (Γ : Bindings) : Term → Except Finding TType
  | .entity uid =>
    if (C.env.ets.isValidEntityUID uid || C.env.acts.contains uid) then .ok (.cedar (.entity uid.ty))
    else .error .path
  | .long _ => .ok (.cedar .int)
  | .decimal s =>
    if (Cedar.Spec.Ext.Decimal.parse s).isSome then .ok (.cedar (.ext .decimal)) else .error .path
  | .string _ => .ok (.cedar .string)
  | .bool _ => .ok (.cedar (.bool .anyBool))
  | .context p =>
    match C.contextType? p with
    | some ty => if ty.temporalSupported then .ok (.cedar ty) else .error .extension
    | none => .error (pathFinding (pathDeclared C.env.reqty.context p))
  | .scope r [] => .ok (.cedar (.entity (C.scopeType r)))
  | .scope r (a :: p) =>
    match C.scopeAttrType? r (a :: p) with
    | some ty => if ty.temporalSupported then .ok (.cedar ty) else .error .extension
    | none =>
      .error (pathFinding (match C.env.ets.attrs? (C.scopeType r) with
        | some rty => pathDeclared rty (a :: p)
        | none => false))
  | .var x =>
    match Γ.lookup x with
    | some τ => .ok τ
    | none => .error .unbound
  | .wildcard | .agg _ | .arith _ _ _ => .error .placement

/-- The problems a predicate argument's term has of its own, whatever field it is for. -/
def Formula.argTermProblems (C : TypingCtx) (Γ : Bindings) : Term → List Finding
  | .wildcard => []
  | .var x => if (Γ.lookup x).isSome then [] else [.unbound]
  | t => match Term.checkSimple? C Γ t with
    | .error f => [f]
    | .ok _ => []

/-- The problems found in one predicate argument. An argument for a field the event does not
declare is an event-name problem, and its term is checked too. -/
def Formula.argCheck (C : TypingCtx) (Γ : Bindings) (sig : EventSignature) :
    Path × Term → List Finding
  | (p, t) =>
    match sig.field? p with
    | none => .eventName :: Formula.argTermProblems C Γ t
    | some fd =>
      match t with
      | .wildcard => []
      | .var x =>
        match Γ.lookup x with
        | none => [.unbound]
        | some τ => if withinB fd.ty τ then [] else [.argument]
      | t =>
        match Term.checkSimple? C Γ t with
        | .error f => [f]
        | .ok τ => if acceptsB fd.ty τ then [] else [.argument]

/-- The problems found in a predicate's arguments. -/
def Formula.argsCheck (C : TypingCtx) (Γ : Bindings) (sig : EventSignature) :
    List (Path × Term) → List Finding
  | [] => []
  | a :: args => Formula.argCheck C Γ sig a ++ Formula.argsCheck C Γ sig args

mutual

/-- The sort of a term, or the first problem found. -/
def Term.check? (C : TypingCtx) (Γ : Bindings) : Term → Except Finding TType
  | .agg a =>
    match Aggregate.check C Γ a with
    | [] => .ok (.cedar .int)
    | f :: _ => .error f
  | .arith _ l r =>
    match Term.check? C Γ l, Term.check? C Γ r with
    | .error f, _ => .error f
    | _, .error f => .error f
    | .ok τ₁, .ok τ₂ =>
      if τ₁ == .cedar .int && τ₂ == .cedar .int then .ok (.cedar .int)
      else if τ₁ == .timepoint || τ₂ == .timepoint then .error .timepoint
      else .error .operand
  | .wildcard => .error .placement
  | t => t.checkSimple? C Γ

/-- Every problem found in a comparison operand: those of each aggregate in it, and of each of
its atoms; none exactly when it has a sort (`Dogwood.Thm.Term.problems_eq_nil_iff`). -/
def Term.problems (C : TypingCtx) (Γ : Bindings) : Term → List Finding
  | .agg a => Aggregate.check C Γ a
  | .arith _ l r =>
    match Term.check? C Γ l, Term.check? C Γ r with
    | .ok τ₁, .ok τ₂ =>
      if τ₁ == .cedar .int && τ₂ == .cedar .int then []
      else if τ₁ == .timepoint || τ₂ == .timepoint then [.timepoint]
      else [.operand]
    | _, _ => Term.problems C Γ l ++ Term.problems C Γ r
  | .wildcard => [.placement]
  | t => match t.checkSimple? C Γ with
    | .error f => [f]
    | .ok _ => []

/-- The problems found in an aggregation. -/
def Aggregate.check (C : TypingCtx) (Γ : Bindings) : Aggregate → List Finding
  | .count dom body =>
    match domainSorts? C.env.ets dom with
    | none => [.binder]
    | some Δ => Formula.check C (Δ ++ Γ) body
  | .sum s dom body =>
    match domainSorts? C.env.ets dom with
    | none => [.binder]
    | some Δ =>
      (if Δ.contains (s, .cedar .int) then [] else [.summand]) ++ Formula.check C (Δ ++ Γ) body

/-- The problems found in a condition. -/
def Formula.check (C : TypingCtx) (Γ : Bindings) : Formula → List Finding
  | .and φ ψ => Formula.check C Γ φ ++ Formula.check C Γ ψ
  | .not φ => Formula.check C Γ φ
  | .formerly w φ =>
    (if w.withinCap C.maxWindow then [] else [.window]) ++ Formula.check C Γ φ
  | .previous w φ =>
    (if w.withinCap C.maxWindow then [] else [.window]) ++ Formula.check C Γ φ
  | .since φ w ψ =>
    (if w.withinCap C.maxWindow then [] else [.window]) ++ Formula.check C Γ φ ++
      Formula.check C Γ ψ
  | .pred a k args =>
    match C.events.signature? a k with
    | none => [.eventName]
    | some sig => Formula.argsCheck C Γ sig args ++ (if pinsTypedB C sig then [] else [.pin])
  | .cmp op l r =>
    match Term.check? C Γ l, Term.check? C Γ r with
    | .ok τ₁, .ok τ₂ =>
      if op.isOrder then
        if τ₁ == .cedar .int && τ₂ == .cedar .int then []
        else if τ₁ == .timepoint || τ₂ == .timepoint then [.timepoint]
        else [.operand]
      else if eqCompatibleB l r τ₁ τ₂ then []
      else if τ₁ == .timepoint || τ₂ == .timepoint then [.timepoint]
      else [.operand]
    -- Every problem of both operands, not only the first.
    | _, _ => Term.problems C Γ l ++ Term.problems C Γ r
  | .exist x φ =>
    match Binder.sort? C.env.ets x with
    | none => [.binder]
    | some b => Formula.check C (b :: Γ) φ
  | .tp x =>
    match Γ.lookup x with
    | some .timepoint => []
    | some _ => [.timepoint]
    | none => [.unbound]

end

end Dogwood.Spec.Temporal
