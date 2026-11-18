import Dogwood.Spec.Validity
import Cedar.Validation

/-!
# How Cedar types an action scope

Cedar types an action scope constraint, after action substitution, as `False` when the
environment's action cannot satisfy it. So a constraint that types otherwise admits the action
(`actionScopeAdmits_of_typeOf`), and one that does not admit the action either types as `False` or
fails to type (`actionScope_ff_or_error`). Moved here from `Dogwood.Thm.TemporalEmbeddingTyping`
so that the action-selective augmentation (`Dogwood.Thm.SelectiveAugment`) can use it.
-/

namespace Dogwood.Thm

open Dogwood.Spec
open Cedar.Spec (Var Attr EntityUID Prim)
open Cedar.Validation (TypeEnv CedarType Capabilities typeOf TypedExpr)

section

open Cedar.Validation (mapOnVars substituteAction)

/-- The substitution `substituteAction` applies. -/
def actionSubst (uid : EntityUID) : Var → Cedar.Spec.Expr
  | .action => .lit (.entityUID uid)
  | v => .var v

theorem substituteAction_eq (uid : EntityUID) (x : Cedar.Spec.Expr) :
    substituteAction uid x = mapOnVars (actionSubst uid) x := by
  unfold substituteAction
  dsimp only
  congr 1
  funext v
  cases v <;> rfl

end

section

open Cedar.Validation (mapOnVars typeOfLit typeOfBinaryApp typeOfEq typeOfUnaryApp typeOfInₑ
  typeOfInₛ ActionSchema Schema typeOfSet justType)
open Cedar.Spec (EntityType)

variable {A : Schema} {env : TypeEnv}

theorem typeOf_lit_action {c : Capabilities} (hact : env.acts.contains env.reqty.action = true) :
    typeOf (.lit (.entityUID env.reqty.action)) c env =
      .ok (.lit (.entityUID env.reqty.action) (.entity env.reqty.action.ty), ∅) := by
  simp [typeOf, typeOfLit, hact, Cedar.Validation.ok]

theorem typeOf_mem_action {c : Capabilities} (hact : env.acts.contains env.reqty.action = true)
    {uid : EntityUID} {tx : TypedExpr} {cx : Capabilities}
    (h : typeOf (.binaryApp .mem (.lit (.entityUID env.reqty.action)) (.lit (.entityUID uid))) c
      env =
      .ok (tx, cx)) :
    tx.typeOf = .bool (if env.acts.descendentOf env.reqty.action uid then .tt else .ff) := by
  rw [typeOf, typeOf_lit_action hact] at h
  simp only [Except.bind_ok] at h
  rw [typeOf] at h
  simp only [typeOfLit] at h
  split at h
  · simp [Cedar.Validation.ok, typeOfBinaryApp, TypedExpr.typeOf, typeOfInₑ,
      Cedar.Validation.actionUID?, Cedar.Validation.entityUID?, hact] at h
    obtain ⟨rfl, -⟩ := h
    rfl
  · simp [Cedar.Validation.err] at h

theorem entityUIDs?_lits (ls : List EntityUID) :
    Cedar.Validation.entityUIDs? (.set (ls.map fun e => .lit (.entityUID e))) = some ls := by
  simp only [Cedar.Validation.entityUIDs?]
  induction ls with
  | nil => rfl
  | cons e es ih => simp_all [List.mapM_cons, Cedar.Validation.entityUID?]

theorem typeOf_set_type {xs : List Cedar.Spec.Expr} {c : Capabilities} {tx : TypedExpr}
    {cx : Capabilities} (h : typeOf (.set xs) c env = .ok (tx, cx)) :
    ∃ ty, tx.typeOf = .set ty := by
  rw [typeOf] at h
  cases hm : xs.mapM₁ (fun ⟨x₁, _⟩ => justType (typeOf x₁ c env)) with
  | error e => rw [hm] at h; cases h
  | ok tys =>
    rw [hm] at h
    simp only [Except.bind_ok] at h
    unfold typeOfSet at h
    split at h
    · cases h
    · split at h
      · simp only [Cedar.Validation.ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        exact ⟨_, rfl⟩
      · cases h

theorem and_second_nonff {x y : Cedar.Spec.Expr} {c : Capabilities} {env : TypeEnv}
    {t : TypedExpr} {ct : Capabilities} (h : typeOf (.and x y) c env = .ok (t, ct))
    (hne : t.typeOf ≠ .bool .ff) {tx : TypedExpr} {cx : Capabilities}
    (hx : typeOf x c env = .ok (tx, cx)) (hbx : tx.typeOf ≠ .bool .ff) :
    ∃ ty cy, typeOf y (c ∪ cx) env = .ok (ty, cy) ∧ ty.typeOf ≠ .bool .ff := by
  rw [typeOf, hx] at h
  simp only [Except.bind_ok] at h
  unfold Cedar.Validation.typeOfAnd at h
  cases htx : tx.typeOf with
  | bool b =>
    rw [htx] at h
    cases b with
    | ff => exact absurd htx hbx
    | tt | anyBool =>
      simp only at h
      cases hy : typeOf y (c ∪ cx) env with
      | error e => rw [hy] at h; cases h
      | ok r =>
        obtain ⟨ty, cy⟩ := r
        rw [hy] at h
        simp only [Except.bind_ok] at h
        refine ⟨ty, cy, rfl, fun hff => ?_⟩
        rw [hff] at h
        simp only [Cedar.Validation.ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        exact hne rfl
  | _ => rw [htx] at h; cases h

/-- **An action scope constraint Cedar does not type as `False`, after action substitution,
admits the environment's action.** -/
theorem actionScopeAdmits_of_typeOf
    (hdesc : ∀ a b, env.acts.descendentOf a b = A.acts.descendentOf a b)
    (hact : env.acts.contains env.reqty.action = true) {s : Cedar.Spec.ActionScope}
    {c : Capabilities} {tx : TypedExpr} {cx : Capabilities}
    (h : typeOf (mapOnVars (actionSubst env.reqty.action) s.toExpr) c env = .ok (tx, cx))
    (hne : tx.typeOf ≠ .bool .ff) :
    actionScopeAdmits A env.reqty.action s = true := by
  have hlit := typeOf_lit_action (c := c) hact
  cases s with
  | actionScope s =>
    cases s with
    | any => rfl
    | eq uid =>
      simp only [Cedar.Spec.ActionScope.toExpr, Cedar.Spec.Scope.toExpr,
        Cedar.Spec.Var.eqEntityUID, mapOnVars, actionSubst] at h
      rw [typeOf, hlit] at h
      simp only [Except.bind_ok] at h
      rw [typeOf] at h
      simp only [typeOfLit] at h
      split at h
      · simp only [Cedar.Validation.ok, Except.bind_ok, typeOfBinaryApp, typeOfEq] at h
        by_cases he : env.reqty.action = uid
        · simp [actionScopeAdmits, he]
        · exfalso
          have : (Prim.entityUID env.reqty.action == Prim.entityUID uid) = false := by
            simp [he]
          simp [this, Cedar.Validation.ok] at h
          obtain ⟨rfl, -⟩ := h
          exact hne rfl
      · simp [Cedar.Validation.err] at h
    | mem uid =>
      simp only [Cedar.Spec.ActionScope.toExpr, Cedar.Spec.Scope.toExpr,
        Cedar.Spec.Var.inEntityUID, mapOnVars, actionSubst] at h
      have ht := typeOf_mem_action hact h
      simp only [actionScopeAdmits, ← hdesc]
      by_cases hd : env.acts.descendentOf env.reqty.action uid = true
      · exact hd
      · simp [hd] at ht
        exact absurd ht hne
    | is ety =>
      simp only [Cedar.Spec.ActionScope.toExpr, Cedar.Spec.Scope.toExpr,
        Cedar.Spec.Var.isEntityType, mapOnVars, actionSubst] at h
      rw [typeOf, hlit] at h
      simp only [Except.bind_ok, typeOfUnaryApp, TypedExpr.typeOf, Cedar.Validation.ok,
        Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      simp only [TypedExpr.typeOf] at hne
      split at hne
      · simp_all [actionScopeAdmits]
      · exact absurd rfl hne
    | isMem ety uid =>
      simp only [Cedar.Spec.ActionScope.toExpr, Cedar.Spec.Scope.toExpr,
        Cedar.Spec.Var.isEntityType, Cedar.Spec.Var.inEntityUID, mapOnVars, actionSubst] at h
      by_cases hE : ety = env.reqty.action.ty
      · have hx : typeOf (.unaryApp (.is ety) (.lit (.entityUID env.reqty.action))) c env =
            .ok (.unaryApp (.is ety) (.lit (.entityUID env.reqty.action)
              (.entity env.reqty.action.ty)) (.bool .tt), ∅) := by
          rw [typeOf, hlit]
          simp [typeOfUnaryApp, TypedExpr.typeOf, hE, Cedar.Validation.ok]
        obtain ⟨tm, cm, hm, hnm⟩ := and_second_nonff h hne hx (by simp [TypedExpr.typeOf])
        have htm := typeOf_mem_action hact hm
        by_cases hd : env.acts.descendentOf env.reqty.action uid = true
        · simp [actionScopeAdmits, hE, ← hdesc, hd]
        · exfalso
          simp [hd] at htm
          exact hnm htm
      · exfalso
        have hx : typeOf (.unaryApp (.is ety) (.lit (.entityUID env.reqty.action))) c env =
            .ok (.unaryApp (.is ety) (.lit (.entityUID env.reqty.action)
              (.entity env.reqty.action.ty)) (.bool .ff), ∅) := by
          rw [typeOf, hlit]
          simp [typeOfUnaryApp, TypedExpr.typeOf, hE, Cedar.Validation.ok]
        rw [typeOf, hx] at h
        simp only [Except.bind_ok, Cedar.Validation.typeOfAnd, TypedExpr.typeOf,
          Cedar.Validation.ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        exact hne rfl
  | actionInAny ls =>
    simp only [Cedar.Spec.ActionScope.toExpr, mapOnVars, actionSubst] at h
    have hset : (ls.map fun e => Cedar.Spec.Expr.lit (.entityUID e)).map₁
        (fun ⟨x, _⟩ => mapOnVars (actionSubst env.reqty.action) x) =
        ls.map fun e => .lit (.entityUID e) := by
      rw [List.map₁_eq_map (fun x => mapOnVars (actionSubst env.reqty.action) x)]
      simp [mapOnVars]
    rw [hset, typeOf, hlit] at h
    simp only [Except.bind_ok] at h
    cases hs : typeOf (.set (ls.map fun e => .lit (.entityUID e))) c env with
    | error e => rw [hs] at h; cases h
    | ok r =>
      obtain ⟨ts, cs⟩ := r
      rw [hs] at h
      simp only [Except.bind_ok] at h
      obtain ⟨ty, hty⟩ := typeOf_set_type hs
      simp only [typeOfBinaryApp, hty, show (TypedExpr.lit (.entityUID env.reqty.action)
        (.entity env.reqty.action.ty)).typeOf = .entity env.reqty.action.ty from rfl] at h
      cases ty with
      | entity ety₂ =>
        simp only [Cedar.Validation.ok, typeOfInₛ, Cedar.Validation.actionUID?,
          Cedar.Validation.entityUID?, hact, ↓reduceIte, Option.bind_some, entityUIDs?_lits,
          Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        simp only [actionScopeAdmits, ← hdesc]
        by_cases hany : (ls.any fun x => env.acts.descendentOf env.reqty.action x) = true
        · exact hany
        · exfalso
          apply hne
          simp only [TypedExpr.typeOf]
          simp only [Bool.not_eq_true] at hany
          simp [hact, hany]
      | _ => simp [Cedar.Validation.err] at h

end

/-- **An action scope constraint that does not admit the environment's action types as `False`,
or fails to type**, whatever the capabilities. -/
theorem actionScope_ff_or_error {A : Cedar.Validation.Schema} {env : TypeEnv}
    (hdesc : ∀ a b, env.acts.descendentOf a b = A.acts.descendentOf a b)
    (hact : env.acts.contains env.reqty.action = true) {s : Cedar.Spec.ActionScope}
    (hna : actionScopeAdmits A env.reqty.action s = false) (c : Capabilities) :
    (∃ tx c', typeOf (Cedar.Validation.mapOnVars (actionSubst env.reqty.action) s.toExpr) c env =
        .ok (tx, c') ∧ tx.typeOf = .bool .ff) ∨
      ∃ e, typeOf (Cedar.Validation.mapOnVars (actionSubst env.reqty.action) s.toExpr) c env =
        .error e := by
  cases h : typeOf (Cedar.Validation.mapOnVars (actionSubst env.reqty.action) s.toExpr) c env with
  | error e => exact .inr ⟨e, rfl⟩
  | ok r =>
    obtain ⟨tx, c'⟩ := r
    by_cases hff : tx.typeOf = .bool .ff
    · exact .inl ⟨tx, c', rfl, hff⟩
    · have := actionScopeAdmits_of_typeOf hdesc hact h hff
      rw [hna] at this
      cases this

end Dogwood.Thm
