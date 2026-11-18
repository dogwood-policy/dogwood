import Dogwood.Thm.TemporalEmbedding
import Dogwood.Thm.ScopeTyping


/-!
# Dogwood's typing of a temporal leaf is stricter than Cedar's

A Cedar expression of the translated fragment (`Dogwood.Thm.TemporalEmbedding`) whose translation
is a well-typed temporal leaf is well-typed in Cedar too, in the same request environment, as a
`Bool` (`typeOf_toTemporal`), given that every fact the leaf's typing uses is a capability of
Cedar's (`CapsCover`): a `has` test Cedar's typing has seen. So Dogwood's typing accepts only
expressions Cedar's accepts. The two typings agree term by term: Cedar types each translated term
as Dogwood does, but for a `Bool` literal, which Cedar types as `True` or `False` (`CedarFits`).
Only facts about optional attributes are used; Cedar's typing of a `has` test of an optional
attribute records exactly that capability, and a fact about a required attribute is needed by
neither typing.

For a valid policy set, this lifts to a rule (`validate_cedarVersion`): put the Cedar expression
back in place of the leaf's hoisted attribute in the lowered rule, and Cedar's validation of the
result against the augmented schema succeeds, or reports the policy impossible (typed `False` in
every environment), never a type error or an undeclared entity. Along the way: Cedar's typing of
a rule's scope admits each environment it passes (`admits_of_reaches`), its earlier conditions
earn the capabilities of their facts (`caps_of_facts`), and replacing a condition keeps the rule
typed (`typecheckPolicy_replace`).

The inclusion is strict (`literal_eq_cedar`, `literal_eq_not_wellTyped`): Cedar's typing accepts a
comparison of two literals of any types (it is constant), where Dogwood's asks that the two sides
have the same type. Two other cases are known, outside this module's statement: an earlier
condition that is `False` in a request environment makes Cedar skip the rest there, where Dogwood
types a leaf in every environment the rule's scope admits; and Cedar keeps the capabilities of the
left of an `||` whose right is `False`, where Dogwood's facts come only from `&&` and `has`.
-/

namespace Dogwood.Thm

open Dogwood.Spec Dogwood.Spec.Temporal
open Cedar.Spec (Request Entities Value Prim Var BinaryOp UnaryOp Attr EntityUID)
open Cedar.Validation (TypeEnv RecordType CedarType Capabilities Key typeOf TypedExpr
  ResultType)

/-- Cedar types `y`, whatever its capabilities, as a record in which the attribute `a` is
required: its `has` test types as `True`, and earns no capability. -/
def RequiredAt (env : TypeEnv) (y : Cedar.Spec.Expr) (a : Attr) : Prop :=
  ∀ c t ct, typeOf y c env = .ok (t, ct) →
    ∃ rty aty, t.typeOf = .record rty ∧ rty.find? a = some (.required aty)

/-- **Cedar's capabilities cover the leaf's facts**: the `has` test of each fact is a capability,
or tests an attribute required where Cedar types its subject (which earns none, and needs none). -/
def CapsCover (env : TypeEnv) (F : List Guard) (c : Capabilities) : Prop :=
  ∀ g ∈ F, ∀ y a, g.expr = .hasAttr y a → (y, Key.attr a) ∈ c ∨ RequiredAt env y a

theorem CapsCover.mono {env : TypeEnv} {F : List Guard} {c c' : Capabilities}
    (h : CapsCover env F c) (hc : ∀ k ∈ c, k ∈ c') : CapsCover env F c' :=
  fun g hg y a he => (h g hg y a he).imp_left (hc _)

theorem RequiredAt.not_optional {env : TypeEnv} {y : Cedar.Spec.Expr} {a : Attr}
    (h : RequiredAt env y a) {c : Capabilities} {t : TypedExpr} {ct : Capabilities}
    (hy : typeOf y c env = .ok (t, ct)) {rty : RecordType} (ht : t.typeOf = .record rty)
    {qty : Cedar.Validation.QualifiedType} (hf : rty.find? a = some qty)
    (hq : qty.isRequired = false) : False := by
  obtain ⟨rty', aty, ht', hf'⟩ := h c t ct hy
  rw [ht] at ht'
  cases ht'
  rw [hf] at hf'
  cases hf'
  cases hq

theorem RequiredAt.not_entity {env : TypeEnv} {y : Cedar.Spec.Expr} {a : Attr}
    (h : RequiredAt env y a) {c : Capabilities} {t : TypedExpr} {ct : Capabilities}
    (hy : typeOf y c env = .ok (t, ct)) {e : Cedar.Spec.EntityType}
    (ht : t.typeOf = .entity e) : False := by
  obtain ⟨rty', aty, ht', -⟩ := h c t ct hy
  rw [ht] at ht'
  cases ht'

/-! ## Paths -/

/-- A path typed through records, by its last attribute. -/
theorem pathType_snoc {present : Path → Bool} :
    (q : Path) → (pre : Path) → (rty : RecordType) → (a : Attr) → {T : CedarType} →
    pathType? present rty pre (q ++ [a]) = some T →
    (q = [] ∧ ∃ qty, rty.find? a = some qty ∧ (qty.isRequired || present (pre ++ [a])) = true ∧
        qty.getType = T) ∨
      (∃ rty', pathType? present rty pre q = some (.record rty') ∧ ∃ qty,
        rty'.find? a = some qty ∧ (qty.isRequired || present (pre ++ q ++ [a])) = true ∧
        qty.getType = T)
  | [], pre, rty, a, T, h => by
    left
    refine ⟨rfl, ?_⟩
    simp only [List.nil_append] at h
    unfold pathType? at h
    cases hf : rty.find? a with
    | none => rw [hf] at h; cases h
    | some qty =>
      rw [hf] at h
      simp only at h
      split at h
      · rename_i hc
        simp only [Option.some.injEq] at h
        exact ⟨qty, rfl, hc, h⟩
      · cases h
  | b :: q, pre, rty, a, T, h => by
    right
    simp only [List.cons_append] at h
    unfold pathType? at h
    cases hf : rty.find? b with
    | none => rw [hf] at h; cases h
    | some qty =>
      rw [hf] at h
      simp only at h
      split at h
      · rename_i hc
        cases hg : qty.getType with
        | record rty₁ =>
          rw [hg] at h
          obtain ⟨d, rest, hdr⟩ := List.exists_cons_of_ne_nil (by simp : q ++ [a] ≠ [])
          rw [hdr] at h
          simp only at h
          rw [← hdr] at h
          rcases pathType_snoc q (pre ++ [b]) rty₁ a h with ⟨rfl, qty', hf', hc', ht'⟩ |
            ⟨rty', hq, qty', hf', hc', ht'⟩
          · refine ⟨rty₁, ?_, qty', hf', by simpa using hc', ht'⟩
            unfold pathType?
            simp [hf, hc, hg]
          · refine ⟨rty', ?_, qty', hf', by simpa using hc', ht'⟩
            cases q with
            | nil => simp [pathType?] at hq
            | cons d q =>
              unfold pathType?
              simp only [hf, hc, ↓reduceIte, hg]
              exact hq
        | _ =>
          rw [hg] at h
          obtain ⟨d, rest, hdr⟩ := List.exists_cons_of_ne_nil (by simp : q ++ [a] ≠ [])
          rw [hdr] at h
          simp at h
      · cases h

theorem ctxPath_attrChain : (x : Cedar.Spec.Expr) → (p : Path) → ctxPath x = some p →
    x = attrChainExpr .context p
  | .var .context, p, h => by
    simp only [ctxPath, Option.some.injEq] at h
    subst h
    rfl
  | .getAttr x a, p, h => by
    simp only [ctxPath, Option.map_eq_some_iff] at h
    obtain ⟨p', hp', rfl⟩ := h
    rw [attrChainExpr_snoc, ← ctxPath_attrChain x p' hp']
  | .lit _, _, h | .var .principal, _, h | .var .action, _, h | .var .resource, _, h
  | .ite .., _, h | .and .., _, h | .or .., _, h | .unaryApp .., _, h | .binaryApp .., _, h
  | .hasAttr .., _, h | .extHasAttr .., _, h | .set .., _, h | .record .., _, h
  | .call .., _, h => by cases h

theorem scopePath_attrChain : (x : Cedar.Spec.Expr) → (r : ScopeRoot) → (p : Path) →
    scopePath x = some (r, p) → x = attrChainExpr (scopeVar r) p
  | .var .principal, r, p, h => by
    simp only [scopePath, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | .var .resource, r, p, h => by
    simp only [scopePath, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | .getAttr x a, r, p, h => by
    simp only [scopePath, Option.map_eq_some_iff, Prod.exists] at h
    obtain ⟨r', p', hp', hrp⟩ := h
    simp only [Prod.mk.injEq] at hrp
    obtain ⟨rfl, rfl⟩ := hrp
    rw [attrChainExpr_snoc, ← scopePath_attrChain x r' p' hp']
  | .lit _, _, _, h | .var .action, _, _, h | .var .context, _, _, h
  | .ite .., _, _, h | .and .., _, _, h | .or .., _, _, h | .unaryApp .., _, _, h
  | .binaryApp .., _, _, h | .hasAttr .., _, _, h | .extHasAttr .., _, _, h | .set .., _, _, h
  | .record .., _, _, h | .call .., _, _, h => by cases h

theorem guard_context_expr (q : Path) (a : Attr) :
    (Guard.context (q ++ [a])).expr = .hasAttr (attrChainExpr .context q) a := by
  simp [Guard.expr, Guard.expr.test]

theorem guard_scope_expr (r : ScopeRoot) (q : Path) (a : Attr) :
    (Guard.scope r (q ++ [a])).expr = .hasAttr (attrChainExpr (scopeVar r) q) a := by
  cases r <;> simp [Guard.expr, Guard.expr.test, scopeVar]

/-- Cedar types an attribute of a record type that the path's typing reaches. -/
theorem getAttrInRecord_ok {ty : CedarType} {rty : RecordType} {x : Cedar.Spec.Expr}
    {a : Attr} {c : Capabilities} {qty : Cedar.Validation.QualifiedType}
    (hf : rty.find? a = some qty) (hcap : qty.isRequired = false → (x, Key.attr a) ∈ c) :
    Cedar.Validation.getAttrInRecord ty rty x a c = .ok (qty.getType, ∅) := by
  unfold Cedar.Validation.getAttrInRecord
  cases qty with
  | required aty => simp [hf, Cedar.Validation.ok, Cedar.Validation.Qualified.getType]
  | optional aty =>
    have := hcap rfl
    simp [hf, this, Cedar.Validation.ok, Cedar.Validation.Qualified.getType]

/-! ## Attribute chains -/

section

variable {C : TypingCtx} {c : Capabilities}

theorem pathType_ne_nil {present : Path → Bool} {rty : RecordType} {pre q : Path}
    {T : CedarType} (h : pathType? present rty pre q = some T) : q ≠ [] := by
  rintro rfl
  simp [pathType?] at h

/-- **Cedar types a context path Dogwood types**, to the same type, when its capabilities cover
the facts. -/
theorem typeOf_ctxPath (hcap : CapsCover C.env C.facts c) :
    (x : Cedar.Spec.Expr) → (p : Path) → ctxPath x = some p → {T : CedarType} →
      C.contextType? p = some T → ∃ tx c', typeOf x c C.env = .ok (tx, c') ∧ tx.typeOf = T
  | .getAttr x a, p, hp, T, hT => by
    simp only [ctxPath, Option.map_eq_some_iff] at hp
    obtain ⟨p', hp', rfl⟩ := hp
    unfold TypingCtx.contextType? at hT
    have hxe := ctxPath_attrChain x p' hp'
    rcases pathType_snoc p' [] _ a hT with ⟨rfl, qty, hf, hc, ht⟩ | ⟨rty', hq, qty, hf, hc, ht⟩
    · have hx : x = .var .context := by simpa [attrChainExpr] using hxe
      subst hx
      have hcap' : qty.isRequired = false → (Cedar.Spec.Expr.var .context, Key.attr a) ∈ c := by
        intro hreq
        rw [hreq, Bool.false_or] at hc
        rcases hcap _ (of_decide_eq_true hc) _ _
          (by simpa [attrChainExpr] using guard_context_expr [] a) with h | h
        · exact h
        · exact (h.not_optional (c := c) (t := .var .context (.record C.env.reqty.context))
            (ct := ∅) (by simp [typeOf, Cedar.Validation.typeOfVar, Cedar.Validation.ok]) rfl hf
            hreq).elim
      refine ⟨.getAttr (.var .context (.record C.env.reqty.context)) a qty.getType, ∅, ?_, ht⟩
      rw [typeOf]
      simp [typeOf, Cedar.Validation.typeOfVar, Cedar.Validation.typeOfGetAttr,
        TypedExpr.typeOf, getAttrInRecord_ok hf hcap', Cedar.Validation.ok]
    · obtain ⟨tx, c₁, hx, htx⟩ := typeOf_ctxPath hcap x p' hp' hq
      have hcap' : qty.isRequired = false → (x, Key.attr a) ∈ c := by
        intro hreq
        rw [hreq, Bool.false_or] at hc
        rcases hcap _ (of_decide_eq_true (by simpa using hc)) _ _ (guard_context_expr p' a)
          with h | h
        · rwa [← hxe] at h
        · rw [← hxe] at h
          exact (h.not_optional hx htx hf hreq).elim
      refine ⟨.getAttr tx a qty.getType, ∅, ?_, ht⟩
      rw [typeOf]
      simp only [hx, Except.bind_ok]
      simp [Cedar.Validation.typeOfGetAttr, htx, getAttrInRecord_ok hf hcap',
        Cedar.Validation.ok]
  | .var .context, p, hp, T, hT => by
    simp only [ctxPath, Option.some.injEq] at hp
    subst hp
    exact absurd rfl (pathType_ne_nil hT)
  | .lit _, _, hp, _, _ | .var .principal, _, hp, _, _ | .var .action, _, hp, _, _
  | .var .resource, _, hp, _, _ | .ite .., _, hp, _, _ | .and .., _, hp, _, _
  | .or .., _, hp, _, _ | .unaryApp .., _, hp, _, _ | .binaryApp .., _, hp, _, _
  | .hasAttr .., _, hp, _, _ | .extHasAttr .., _, hp, _, _ | .set .., _, hp, _, _
  | .record .., _, hp, _, _ | .call .., _, hp, _, _ => by cases hp

theorem typeOf_scopeVar (r : ScopeRoot) :
    ∃ tx, typeOf (.var (scopeVar r)) c C.env = .ok (tx, ∅) ∧
      tx.typeOf = .entity (C.scopeType r) := by
  cases r
  · exact ⟨.var .principal (.entity C.env.reqty.principal),
      by simp [scopeVar, typeOf, Cedar.Validation.typeOfVar, Cedar.Validation.ok], rfl⟩
  · exact ⟨.var .resource (.entity C.env.reqty.resource),
      by simp [scopeVar, typeOf, Cedar.Validation.typeOfVar, Cedar.Validation.ok], rfl⟩

/-- **Cedar types a scope path Dogwood types**, to the same type, when its capabilities cover the
facts. -/
theorem typeOf_scopePath (hcap : CapsCover C.env C.facts c) :
    (x : Cedar.Spec.Expr) → (r : ScopeRoot) → (p : Path) → scopePath x = some (r, p) →
      {T : CedarType} → C.scopeAttrType? r p = some T →
      ∃ tx c', typeOf x c C.env = .ok (tx, c') ∧ tx.typeOf = T
  | .getAttr x a, r, p, hp, T, hT => by
    simp only [scopePath, Option.map_eq_some_iff, Prod.exists] at hp
    obtain ⟨r', p', hp', hrp⟩ := hp
    simp only [Prod.mk.injEq] at hrp
    obtain ⟨rfl, rfl⟩ := hrp
    have hxe := scopePath_attrChain x r' p' hp'
    unfold TypingCtx.scopeAttrType? at hT
    split at hT
    · rename_i rty hrty
      rcases pathType_snoc p' [] rty a hT with ⟨rfl, qty, hf, hc, ht⟩ |
        ⟨rty', hq, qty, hf, hc, ht⟩
      · have hx : x = .var (scopeVar r') := by simpa [attrChainExpr] using hxe
        subst hx
        have hcap' : qty.isRequired = false →
            (Cedar.Spec.Expr.var (scopeVar r'), Key.attr a) ∈ c := by
          intro hreq
          rw [hreq, Bool.false_or] at hc
          obtain ⟨tv, hv, htv⟩ := typeOf_scopeVar (C := C) (c := c) r'
          rcases hcap _ (of_decide_eq_true hc) _ _
            (by simpa [attrChainExpr] using guard_scope_expr r' [] a) with h | h
          · exact h
          · exact (h.not_entity hv htv).elim
        obtain ⟨tv, hv, htv⟩ := typeOf_scopeVar (C := C) (c := c) r'
        refine ⟨.getAttr tv a qty.getType, ∅, ?_, ht⟩
        rw [typeOf, hv]
        simp only [Except.bind_ok]
        simp [Cedar.Validation.typeOfGetAttr, htv, hrty, getAttrInRecord_ok hf hcap',
          Cedar.Validation.ok]
      · have hsc : C.scopeAttrType? r' p' = some (.record rty') := by
          unfold TypingCtx.scopeAttrType?
          rw [hrty]
          exact hq
        obtain ⟨tx, c₁, hx, htx⟩ := typeOf_scopePath hcap x r' p' hp' hsc
        have hcap' : qty.isRequired = false → (x, Key.attr a) ∈ c := by
          intro hreq
          rw [hreq, Bool.false_or] at hc
          rcases hcap _ (of_decide_eq_true (by simpa using hc)) _ _ (guard_scope_expr r' p' a)
            with h | h
          · rwa [← hxe] at h
          · rw [← hxe] at h
            exact (h.not_optional hx htx hf hreq).elim
        refine ⟨.getAttr tx a qty.getType, ∅, ?_, ht⟩
        rw [typeOf]
        simp only [hx, Except.bind_ok]
        simp [Cedar.Validation.typeOfGetAttr, htx, getAttrInRecord_ok hf hcap',
          Cedar.Validation.ok]
    · cases hT
  | .var .principal, r, p, hp, T, hT | .var .resource, r, p, hp, T, hT => by
    simp only [scopePath, Option.some.injEq, Prod.mk.injEq] at hp
    obtain ⟨rfl, rfl⟩ := hp
    unfold TypingCtx.scopeAttrType? at hT
    split at hT
    · exact absurd rfl (pathType_ne_nil hT)
    · cases hT
  | .lit _, _, _, hp, _, _ | .var .action, _, _, hp, _, _ | .var .context, _, _, hp, _, _
  | .ite .., _, _, hp, _, _ | .and .., _, _, hp, _, _ | .or .., _, _, hp, _, _
  | .unaryApp .., _, _, hp, _, _ | .binaryApp .., _, _, hp, _, _ | .hasAttr .., _, _, hp, _, _
  | .extHasAttr .., _, _, hp, _, _ | .set .., _, _, hp, _, _ | .record .., _, _, hp, _, _
  | .call .., _, _, hp, _, _ => by cases hp

end

/-! ## Terms and conditions -/

/-- Cedar's type of a term is the leaf's, but for a `Bool` literal, which Cedar types as `True`
or `False` and the leaf as `Bool`. -/
def CedarFits (ty : CedarType) (τ : TType) : Prop :=
  τ = .cedar ty ∨ ∃ b, ty = .bool b ∧ τ = .cedar (.bool .anyBool)

section

variable {C : TypingCtx} {c : Capabilities}

/-- **Cedar types a term Dogwood types**, to its type (a `Bool` literal, to `True` or `False`). -/
theorem typeOf_toTerm (hcap : CapsCover C.env C.facts c) :
    (x : Cedar.Spec.Expr) → (t : Term) → toTerm x = some t → {τ : TType} →
      Term.Typed C [] t τ → ∃ tx c', typeOf x c C.env = .ok (tx, c') ∧ CedarFits tx.typeOf τ
  | .lit p, t, ht, τ, hty => by
    cases p with
    | bool b =>
      simp only [toTerm, Option.some.injEq] at ht
      subst ht
      cases hty
      cases b
      · exact ⟨.lit (.bool false) (.bool .ff), ∅, by simp [typeOf, Cedar.Validation.typeOfLit,
          Cedar.Validation.ok], .inr ⟨_, rfl, rfl⟩⟩
      · exact ⟨.lit (.bool true) (.bool .tt), ∅, by simp [typeOf, Cedar.Validation.typeOfLit,
          Cedar.Validation.ok], .inr ⟨_, rfl, rfl⟩⟩
    | int i =>
      simp only [toTerm, Option.some.injEq] at ht
      subst ht
      cases hty
      exact ⟨.lit (.int i) .int, ∅, by simp [typeOf, Cedar.Validation.typeOfLit,
        Cedar.Validation.ok], .inl rfl⟩
    | string s =>
      simp only [toTerm, Option.some.injEq] at ht
      subst ht
      cases hty
      exact ⟨.lit (.string s) .string, ∅, by simp [typeOf, Cedar.Validation.typeOfLit,
        Cedar.Validation.ok], .inl rfl⟩
    | entityUID u =>
      simp only [toTerm, Option.some.injEq] at ht
      subst ht
      cases hty with
      | entity h =>
        exact ⟨.lit (.entityUID u) (.entity u.ty), ∅, by
          simp only [typeOf, Cedar.Validation.typeOfLit, h, ↓reduceIte]
          rfl, .inl rfl⟩
  | .var .principal, t, ht, τ, hty | .var .resource, t, ht, τ, hty => by
    simp only [toTerm, Option.some.injEq] at ht
    subst ht
    cases hty with
    | scopeRoot =>
      first
      | exact ⟨.var .principal (.entity C.env.reqty.principal), ∅,
          by simp [typeOf, Cedar.Validation.typeOfVar, Cedar.Validation.ok], .inl rfl⟩
      | exact ⟨.var .resource (.entity C.env.reqty.resource), ∅,
          by simp [typeOf, Cedar.Validation.typeOfVar, Cedar.Validation.ok], .inl rfl⟩
    | scopeAttr hne _ _ => exact absurd rfl hne
  | .call xfn xs, t, ht, τ, hty => by
    obtain ⟨s, rfl, rfl, rfl⟩ := toTerm_call ht
    cases hty with
    | decimal h =>
      obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp h
      refine ⟨.call .decimal [.lit (.string s) .string] (.ext .decimal), ∅, ?_, .inl rfl⟩
      simp [typeOf, List.mapM₁, Cedar.Validation.justType, Cedar.Validation.typeOfLit,
        Cedar.Validation.typeOfCall, Cedar.Validation.typeOfConstructor, Cedar.Validation.ok,
        Cedar.Spec.Ext.Decimal.decimal, hd]
      rfl
  | .getAttr x a, t, ht, τ, hty => by
    cases hcx : ctxPath x with
    | some p =>
      simp only [toTerm, attrTerm, hcx, Option.some.injEq] at ht
      subst ht
      cases hty with
      | context hT =>
        obtain ⟨tx, c', h, htx⟩ := typeOf_ctxPath hcap (.getAttr x a) (p ++ [a])
          (by simp [ctxPath, hcx]) hT
        exact ⟨tx, c', h, .inl (by rw [htx])⟩
    | none =>
      cases hsx : scopePath x with
      | none => simp [toTerm, attrTerm, hcx, hsx] at ht
      | some rp =>
        obtain ⟨r, p⟩ := rp
        simp only [toTerm, attrTerm, hcx, hsx, Option.some.injEq] at ht
        subst ht
        generalize hq : p ++ [a] = q at hty
        cases hty with
        | scopeRoot => simp at hq
        | scopeAttr _ hT =>
          rw [← hq] at hT
          obtain ⟨tx, c', h, htx⟩ := typeOf_scopePath hcap (.getAttr x a) r (p ++ [a])
            (by simp [scopePath, hsx]) hT
          exact ⟨tx, c', h, .inl (by rw [htx])⟩
  | .binaryApp .add x y, t, ht, τ, hty | .binaryApp .sub x y, t, ht, τ, hty
  | .binaryApp .mul x y, t, ht, τ, hty => by
    simp only [toTerm, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at ht
    obtain ⟨tx', htx', ty', hty', rfl⟩ := ht
    cases hty with
    | arith hl hr =>
      obtain ⟨t₁, c₁, h₁, hf₁⟩ := typeOf_toTerm hcap x tx' htx' hl
      obtain ⟨t₂, c₂, h₂, hf₂⟩ := typeOf_toTerm hcap y ty' hty' hr
      have hi₁ : t₁.typeOf = .int := by
        rcases hf₁ with h | ⟨_, _, h⟩ <;> simp_all
      have hi₂ : t₂.typeOf = .int := by
        rcases hf₂ with h | ⟨_, _, h⟩ <;> simp_all
      exact ⟨_, ∅, by
        rw [typeOf]
        simp only [h₁, h₂, Except.bind_ok]
        simp [Cedar.Validation.typeOfBinaryApp, hi₁, hi₂, Cedar.Validation.ok]
        rfl, by exact .inl rfl⟩
  | .var .action, _, ht, _, _ | .var .context, _, ht, _, _
  | .ite .., _, ht, _, _ | .and .., _, ht, _, _ | .or .., _, ht, _, _
  | .unaryApp .., _, ht, _, _ | .binaryApp .eq .., _, ht, _, _
  | .binaryApp .mem .., _, ht, _, _ | .binaryApp .hasTag .., _, ht, _, _
  | .binaryApp .getTag .., _, ht, _, _ | .binaryApp .less .., _, ht, _, _
  | .binaryApp .lessEq .., _, ht, _, _ | .binaryApp .contains .., _, ht, _, _
  | .binaryApp .containsAll .., _, ht, _, _ | .binaryApp .containsAny .., _, ht, _, _
  | .hasAttr .., _, ht, _, _ | .extHasAttr .., _, ht, _, _ | .set .., _, ht, _, _
  | .record .., _, ht, _, _ => by simp [toTerm] at ht

end

section

variable {C : TypingCtx} {c : Capabilities}

/-- Two Cedar types fitting the sides of a Dogwood equality have a least upper bound, or are both
entity types. -/
theorem lub_or_entities {ty₁ ty₂ : CedarType} {τ₁ τ₂ : TType} (h₁ : CedarFits ty₁ τ₁)
    (h₂ : CedarFits ty₂ τ₂)
    (hc : τ₁ = τ₂ ∨ ∃ e₁ e₂, τ₁ = .cedar (.entity e₁) ∧ τ₂ = .cedar (.entity e₂)) :
    (∃ T, (ty₁ ⊔ ty₂) = some T) ∨ ∃ e₁ e₂, ty₁ = .entity e₁ ∧ ty₂ = .entity e₂ := by
  have hbools : ∀ b₁ b₂, ∃ T, (CedarType.bool b₁ ⊔ CedarType.bool b₂) = some T :=
    fun b₁ b₂ => ⟨.bool (Cedar.Validation.lubBool b₁ b₂), by cases b₁ <;> cases b₂ <;> rfl⟩
  rcases hc with rfl | ⟨e₁, e₂, rfl, rfl⟩
  · rcases h₁ with h₁ | ⟨b₁, rfl, h₁⟩ <;> rcases h₂ with h₂ | ⟨b₂, rfl, h₂⟩
    · have h := h₁.symm.trans h₂
      simp only [TType.cedar.injEq] at h
      subst h
      exact .inl ⟨ty₁, Cedar.Thm.lub_refl _⟩
    · have h := h₁.symm.trans h₂
      simp only [TType.cedar.injEq] at h
      subst h
      exact .inl (hbools _ _)
    · have h := h₁.symm.trans h₂
      simp only [TType.cedar.injEq] at h
      subst h
      exact .inl (hbools _ _)
    · exact .inl (hbools _ _)
  · rcases h₁ with h₁ | ⟨_, _, h₁⟩ <;> rcases h₂ with h₂ | ⟨_, _, h₂⟩ <;>
      simp only [TType.cedar.injEq, reduceCtorEq] at h₁ h₂
    exact .inr ⟨e₁, e₂, h₁.symm, h₂.symm⟩

theorem typeOfEq_bool {t₁ t₂ : TypedExpr} {x y : Cedar.Spec.Expr} {τ₁ τ₂ : TType}
    (h₁ : CedarFits t₁.typeOf τ₁) (h₂ : CedarFits t₂.typeOf τ₂)
    (hc : τ₁ = τ₂ ∨ ∃ e₁ e₂, τ₁ = .cedar (.entity e₁) ∧ τ₂ = .cedar (.entity e₂)) :
    ∃ tx, Cedar.Validation.typeOfEq t₁ t₂ x y = .ok (tx, ∅) ∧ ∃ b, tx.typeOf = .bool b := by
  unfold Cedar.Validation.typeOfEq
  split
  · split <;> exact ⟨_, rfl, _, rfl⟩
  · rcases lub_or_entities h₁ h₂ hc with ⟨T, hT⟩ | ⟨e₁, e₂, he₁, he₂⟩
    · simp only [hT]
      exact ⟨_, rfl, _, rfl⟩
    · cases hT : t₁.typeOf ⊔ t₂.typeOf with
      | some T => exact ⟨_, rfl, _, rfl⟩
      | none => simp only [he₁, he₂]; exact ⟨_, rfl, _, rfl⟩

theorem fits_int {ty : CedarType} (h : CedarFits ty (.cedar .int)) : ty = .int := by
  rcases h with h | ⟨_, _, h⟩ <;> simp_all

/-- **Dogwood's typing is stricter than Cedar's.** A Cedar expression whose translation is a
well-typed temporal leaf is well-typed in Cedar, in the same request environment, as a `Bool`,
with capabilities that cover the leaf's facts. -/
theorem typeOf_toTemporal :
    (e : Cedar.Spec.Expr) → (φ : Formula) → toTemporal e = some φ → φ.WellTyped C [] →
      (c : Capabilities) → CapsCover C.env C.facts c →
      ∃ tx, typeOf e c C.env = .ok (tx, ∅) ∧ ∃ b, tx.typeOf = .bool b
  | .binaryApp .eq x y, φ, hφ, hwt, c, hcap => by
    simp only [toTemporal, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hφ
    obtain ⟨tx, htx, ty, hty, rfl⟩ := hφ
    cases hwt with
    | eq _ hx hy hc =>
      obtain ⟨t₁, c₁, h₁, hf₁⟩ := typeOf_toTerm hcap x tx htx hx
      obtain ⟨t₂, c₂, h₂, hf₂⟩ := typeOf_toTerm hcap y ty hty hy
      have hc' := hc
      unfold EqCompatible at hc'
      obtain ⟨te, he, hb⟩ := typeOfEq_bool (x := x) (y := y) hf₁ hf₂
        (hc'.imp id fun h => h.2)
      refine ⟨te, ?_, hb⟩
      rw [typeOf]
      simp only [h₁, h₂, Except.bind_ok]
      simp only [Cedar.Validation.typeOfBinaryApp]
      exact he
    | ord hord _ _ => exact absurd hord (by simp [CmpOp.IsOrder])
  | .binaryApp .less x y, φ, hφ, hwt, c, hcap | .binaryApp .lessEq x y, φ, hφ, hwt, c, hcap => by
    simp only [toTemporal, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hφ
    obtain ⟨tx, htx, ty, hty, rfl⟩ := hφ
    cases hwt with
    | eq hord _ _ _ => exact absurd (by simp [CmpOp.IsOrder]) hord
    | ord _ hx hy =>
      obtain ⟨t₁, c₁, h₁, hf₁⟩ := typeOf_toTerm hcap x tx htx hx
      obtain ⟨t₂, c₂, h₂, hf₂⟩ := typeOf_toTerm hcap y ty hty hy
      exact ⟨_, by
        rw [typeOf]
        simp only [h₁, h₂, Except.bind_ok]
        simp [Cedar.Validation.typeOfBinaryApp, fits_int hf₁, fits_int hf₂, Cedar.Validation.ok]
        rfl, _, rfl⟩
  | .and x y, φ, hφ, hwt, c, hcap => by
    simp only [toTemporal, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hφ
    obtain ⟨φx, hφx, φy, hφy, rfl⟩ := hφ
    cases hwt with
    | and hx hy =>
      obtain ⟨t₁, h₁, b₁, hb₁⟩ := typeOf_toTemporal x φx hφx hx c hcap
      obtain ⟨t₂, h₂, b₂, hb₂⟩ := typeOf_toTemporal y φy hφy hy (c ∪ ∅)
        (hcap.mono fun k hk => by simp [hk])
      rw [typeOf]
      simp only [h₁, Except.bind_ok]
      unfold Cedar.Validation.typeOfAnd
      simp only [hb₁]
      cases b₁ with
      | ff => exact ⟨_, rfl, _, hb₁⟩
      | tt | anyBool =>
        simp only [h₂, Except.bind_ok, hb₂]
        cases b₂ <;> simp only [show (∅ : Capabilities) ∪ ∅ = ∅ from rfl] <;>
          exact ⟨_, rfl, _, rfl⟩
  | .or x y, φ, hφ, hwt, c, hcap => by
    simp only [toTemporal, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hφ
    obtain ⟨φx, hφx, φy, hφy, rfl⟩ := hφ
    cases hwt with
    | not h =>
      cases h with
      | and hx hy =>
        cases hx with
        | not hx =>
          cases hy with
          | not hy =>
            obtain ⟨t₁, h₁, b₁, hb₁⟩ := typeOf_toTemporal x φx hφx hx c hcap
            obtain ⟨t₂, h₂, b₂, hb₂⟩ := typeOf_toTemporal y φy hφy hy c hcap
            rw [typeOf]
            simp only [h₁, Except.bind_ok]
            unfold Cedar.Validation.typeOfOr
            simp only [hb₁]
            cases b₁ with
            | tt => exact ⟨_, rfl, _, hb₁⟩
            | ff =>
              simp only [h₂, Except.bind_ok, hb₂]
              exact ⟨_, rfl, _, rfl⟩
            | anyBool =>
              simp only [h₂, Except.bind_ok, hb₂]
              cases b₂ <;> exact ⟨_, rfl, _, rfl⟩
  | .unaryApp .not x, φ, hφ, hwt, c, hcap => by
    simp only [toTemporal, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hφ
    obtain ⟨φx, hφx, rfl⟩ := hφ
    cases hwt with
    | not hx =>
      obtain ⟨t₁, h₁, b₁, hb₁⟩ := typeOf_toTemporal x φx hφx hx c hcap
      rw [typeOf]
      simp only [h₁, Except.bind_ok]
      unfold Cedar.Validation.typeOfUnaryApp
      simp only [hb₁]
      exact ⟨_, rfl, _, rfl⟩
  | .lit _, _, hφ, _, _, _ | .var _, _, hφ, _, _, _ | .ite .., _, hφ, _, _, _
  | .unaryApp .neg _, _, hφ, _, _, _ | .unaryApp .isEmpty _, _, hφ, _, _, _
  | .unaryApp (.like _) _, _, hφ, _, _, _ | .unaryApp (.is _) _, _, hφ, _, _, _
  | .binaryApp .mem .., _, hφ, _, _, _ | .binaryApp .hasTag .., _, hφ, _, _, _
  | .binaryApp .getTag .., _, hφ, _, _, _ | .binaryApp .add .., _, hφ, _, _, _
  | .binaryApp .sub .., _, hφ, _, _, _ | .binaryApp .mul .., _, hφ, _, _, _
  | .binaryApp .contains .., _, hφ, _, _, _ | .binaryApp .containsAll .., _, hφ, _, _, _
  | .binaryApp .containsAny .., _, hφ, _, _, _ | .getAttr .., _, hφ, _, _, _
  | .hasAttr .., _, hφ, _, _, _ | .extHasAttr .., _, hφ, _, _, _ | .set .., _, hφ, _, _, _
  | .record .., _, hφ, _, _, _ | .call .., _, hφ, _, _, _ => by simp [toTemporal] at hφ

end

/-! ## The inclusion is strict -/

/-- Cedar's typing accepts `1 == "a"`, a comparison of two literals of different types, in every
request environment: it types as `False`. -/
theorem literal_eq_cedar (env : TypeEnv) (c : Capabilities) :
    ∃ tx c', typeOf (.binaryApp .eq (.lit (.int 1)) (.lit (.string "a"))) c env = .ok (tx, c') ∧
      tx.typeOf = .bool .ff :=
  ⟨.binaryApp .eq (.lit (.int 1) .int) (.lit (.string "a") .string) (.bool .ff), ∅, by
    rw [typeOf]
    simp [typeOf, Cedar.Validation.typeOfLit, Cedar.Validation.typeOfBinaryApp,
      Cedar.Validation.typeOfEq, Cedar.Validation.ok], rfl⟩

/-- Dogwood's typing does not: the leaf `1 == "a"` is ill-typed in every typing context. -/
theorem literal_eq_not_wellTyped (C : TypingCtx) :
    ¬ (Formula.cmp .eq (.long 1) (.string "a")).WellTyped C [] := by
  intro h
  cases h with
  | eq _ hl hr hc =>
    cases hl
    cases hr
    unfold EqCompatible at hc
    simp at hc
  | ord hord _ _ => exact absurd hord (by simp [CmpOp.IsOrder])

theorem toTemporal_literal_eq :
    toTemporal (.binaryApp .eq (.lit (.int 1)) (.lit (.string "a"))) =
      some (.cmp .eq (.long 1) (.string "a")) := rfl

/-! ## Action substitution

Cedar's validator types a policy after substituting the environment's action for the variable
`action` (`substituteAction`). A translation reads no `action`, so substitution leaves it as it
is. -/

section

open Cedar.Validation (mapOnVars substituteAction)

variable {f : Var → Cedar.Spec.Expr}

theorem mapOnVars_ctxPath (hf : f .context = .var .context) :
    (x : Cedar.Spec.Expr) → (p : Path) → ctxPath x = some p → mapOnVars f x = x
  | .var .context, _, _ => by simp [mapOnVars, hf]
  | .getAttr x a, p, h => by
    simp only [ctxPath, Option.map_eq_some_iff] at h
    obtain ⟨p', hp', -⟩ := h
    simp [mapOnVars, mapOnVars_ctxPath hf x p' hp']
  | .lit _, _, h | .var .principal, _, h | .var .action, _, h | .var .resource, _, h
  | .ite .., _, h | .and .., _, h | .or .., _, h | .unaryApp .., _, h | .binaryApp .., _, h
  | .hasAttr .., _, h | .extHasAttr .., _, h | .set .., _, h | .record .., _, h
  | .call .., _, h => by cases h

theorem mapOnVars_scopePath (hp : f .principal = .var .principal)
    (hr : f .resource = .var .resource) :
    (x : Cedar.Spec.Expr) → (r : ScopeRoot) → (p : Path) → scopePath x = some (r, p) →
      mapOnVars f x = x
  | .var .principal, _, _, _ => by simp [mapOnVars, hp]
  | .var .resource, _, _, _ => by simp [mapOnVars, hr]
  | .getAttr x a, r, p, h => by
    simp only [scopePath, Option.map_eq_some_iff, Prod.exists] at h
    obtain ⟨r', p', hp', -⟩ := h
    simp [mapOnVars, mapOnVars_scopePath hp hr x r' p' hp']
  | .lit _, _, _, h | .var .action, _, _, h | .var .context, _, _, h
  | .ite .., _, _, h | .and .., _, _, h | .or .., _, _, h | .unaryApp .., _, _, h
  | .binaryApp .., _, _, h | .hasAttr .., _, _, h | .extHasAttr .., _, _, h | .set .., _, _, h
  | .record .., _, _, h | .call .., _, _, h => by cases h

theorem mapOnVars_toTerm (hc : f .context = .var .context) (hp : f .principal = .var .principal)
    (hr : f .resource = .var .resource) :
    (x : Cedar.Spec.Expr) → (t : Term) → toTerm x = some t → mapOnVars f x = x
  | .lit _, _, _ => by simp [mapOnVars]
  | .var .principal, _, _ => by simp [mapOnVars, hp]
  | .var .resource, _, _ => by simp [mapOnVars, hr]
  | .call xfn xs, t, h => by
    obtain ⟨s, rfl, rfl, -⟩ := toTerm_call h
    simp [mapOnVars, List.map₁]
  | .getAttr x a, t, h => by
    cases hcx : ctxPath x with
    | some p => simp [mapOnVars, mapOnVars_ctxPath hc x p hcx]
    | none =>
      cases hsx : scopePath x with
      | none => simp [toTerm, attrTerm, hcx, hsx] at h
      | some rp => simp [mapOnVars, mapOnVars_scopePath hp hr x rp.1 rp.2 hsx]
  | .binaryApp .add x y, t, h | .binaryApp .sub x y, t, h | .binaryApp .mul x y, t, h => by
    simp only [toTerm, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨tx, htx, ty, hty, -⟩ := h
    simp [mapOnVars, mapOnVars_toTerm hc hp hr x tx htx, mapOnVars_toTerm hc hp hr y ty hty]
  | .var .action, _, h | .var .context, _, h
  | .ite .., _, h | .and .., _, h | .or .., _, h
  | .unaryApp .., _, h | .binaryApp .eq .., _, h
  | .binaryApp .mem .., _, h | .binaryApp .hasTag .., _, h
  | .binaryApp .getTag .., _, h | .binaryApp .less .., _, h
  | .binaryApp .lessEq .., _, h | .binaryApp .contains .., _, h
  | .binaryApp .containsAll .., _, h | .binaryApp .containsAny .., _, h
  | .hasAttr .., _, h | .extHasAttr .., _, h | .set .., _, h
  | .record .., _, h => by simp [toTerm] at h

theorem mapOnVars_toTemporal (hc : f .context = .var .context)
    (hp : f .principal = .var .principal) (hr : f .resource = .var .resource) :
    (e : Cedar.Spec.Expr) → (φ : Formula) → toTemporal e = some φ → mapOnVars f e = e
  | .binaryApp .eq x y, φ, h | .binaryApp .less x y, φ, h | .binaryApp .lessEq x y, φ, h => by
    simp only [toTemporal, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨tx, htx, ty, hty, -⟩ := h
    simp [mapOnVars, mapOnVars_toTerm hc hp hr x tx htx, mapOnVars_toTerm hc hp hr y ty hty]
  | .and x y, φ, h | .or x y, φ, h => by
    simp only [toTemporal, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨φx, hφx, φy, hφy, -⟩ := h
    simp [mapOnVars, mapOnVars_toTemporal hc hp hr x φx hφx,
      mapOnVars_toTemporal hc hp hr y φy hφy]
  | .unaryApp .not x, φ, h => by
    simp only [toTemporal, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨φx, hφx, -⟩ := h
    simp [mapOnVars, mapOnVars_toTemporal hc hp hr x φx hφx]
  | .lit _, _, h | .var _, _, h | .ite .., _, h
  | .unaryApp .neg _, _, h | .unaryApp .isEmpty _, _, h
  | .unaryApp (.like _) _, _, h | .unaryApp (.is _) _, _, h
  | .binaryApp .mem .., _, h | .binaryApp .hasTag .., _, h
  | .binaryApp .getTag .., _, h | .binaryApp .add .., _, h
  | .binaryApp .sub .., _, h | .binaryApp .mul .., _, h
  | .binaryApp .contains .., _, h | .binaryApp .containsAll .., _, h
  | .binaryApp .containsAny .., _, h | .getAttr .., _, h
  | .hasAttr .., _, h | .extHasAttr .., _, h | .set .., _, h
  | .record .., _, h | .call .., _, h => by simp [toTemporal] at h

/-- **Action substitution leaves a translation as it is.** -/
theorem substituteAction_toTemporal {uid : EntityUID} {e : Cedar.Spec.Expr} {φ : Formula}
    (h : toTemporal e = some φ) : substituteAction uid e = e := by
  unfold substituteAction
  exact mapOnVars_toTemporal (f := fun var => match var with
    | .action => .lit (.entityUID uid) | _ => .var var) rfl rfl rfl e φ h

end

/-! ## Replacing a conjunct

A Cedar policy's expression is a chain of conjunctions: its scope constraints, then its conditions
in order. Cedar types a conjunction left to right, passing each conjunct's capabilities to the
next, and stops at a conjunct of type `False`. -/

section

open Cedar.Validation (typeOfAnd)

/-- A chain of conjunctions ending in `z`. -/
def andChain : List Cedar.Spec.Expr → Cedar.Spec.Expr → Cedar.Spec.Expr
  | [], z => z
  | x :: xs, z => .and x (andChain xs z)

/-- The conditions from `c` on, as one expression. -/
def condTail (c : Cedar.Spec.Condition) : Cedar.Spec.Conditions → Cedar.Spec.Expr
  | [] => c.toExpr
  | d :: ds => .and c.toExpr (Cedar.Spec.Conditions.toExpr (d :: ds))

theorem conditions_toExpr_split (c : Cedar.Spec.Condition) (post : Cedar.Spec.Conditions) :
    (pre : Cedar.Spec.Conditions) → Cedar.Spec.Conditions.toExpr (pre ++ c :: post) =
      andChain (pre.map (·.toExpr)) (condTail c post)
  | [] => by
    cases post with
    | nil => simp [andChain, condTail, Cedar.Spec.Conditions.toExpr]
    | cons d ds => simp [andChain, condTail, cedar_conditions_toExpr_cons c (d :: ds) (by simp)]
  | d :: pre => by
    rw [List.cons_append, cedar_conditions_toExpr_cons d _ (by simp),
      conditions_toExpr_split c post pre]
    rfl

theorem policy_toExpr_split (p : Cedar.Spec.Policy) {pre post : Cedar.Spec.Conditions}
    {c : Cedar.Spec.Condition} (h : p.condition = pre ++ c :: post) :
    p.toExpr = andChain ([p.principalScope.toExpr, p.actionScope.toExpr, p.resourceScope.toExpr] ++
      pre.map (·.toExpr)) (condTail c post) := by
  simp only [Cedar.Spec.Policy.toExpr, h, conditions_toExpr_split]
  rfl

theorem andChain_append (xs ys : List Cedar.Spec.Expr) (z : Cedar.Spec.Expr) :
    andChain (xs ++ ys) z = andChain xs (andChain ys z) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [andChain, ih]

/-- **Cedar's typing reaches the end of a chain with the capabilities `ca`**: every conjunct
before it types as a `Bool` other than `False`, each passing its capabilities on. -/
inductive Reaches (env : TypeEnv) : List Cedar.Spec.Expr → Capabilities → Capabilities → Prop
  | nil {c} : Reaches env [] c c
  | cons {x xs c tx cx ca} : typeOf x c env = .ok (tx, cx) → tx.typeOf ≠ .bool .ff →
      Reaches env xs (c ∪ cx) ca → Reaches env (x :: xs) c ca

/-- A Cedar result is a `Bool`. -/
def IsBool (r : ResultType) : Prop := ∃ tx cx b, r = .ok (tx, cx) ∧ tx.typeOf = .bool b

/-- `typeOfAnd` of a `Bool` other than `False`, then a `Bool`, is a `Bool`. -/
theorem typeOfAnd_bool {r₁ : TypedExpr × Capabilities} {r₂ : ResultType}
    {b₁ : Cedar.Validation.BoolType}
    (h₁ : r₁.1.typeOf = .bool b₁) (h₂ : IsBool r₂) : IsBool (typeOfAnd r₁ r₂) := by
  obtain ⟨t₂, c₂, b₂, rfl, hb₂⟩ := h₂
  obtain ⟨t₁, c₁⟩ := r₁
  simp only at h₁
  unfold typeOfAnd
  cases b₁ with
  | ff => simp only [h₁]; exact ⟨_, _, _, rfl, h₁⟩
  | tt | anyBool =>
    simp only [h₁, Except.bind_ok, hb₂]
    cases b₂ <;> exact ⟨_, _, _, rfl, rfl⟩

/-- `typeOfAnd` of `False` is `False`, whatever follows. -/
theorem typeOfAnd_ff {r₁ : TypedExpr × Capabilities} {r₂ : ResultType}
    (h₁ : r₁.1.typeOf = .bool .ff) : IsBool (typeOfAnd r₁ r₂) := by
  unfold typeOfAnd
  simp only [h₁]
  exact ⟨_, _, _, rfl, h₁⟩

/-- A typed conjunction's first conjunct is a `Bool`; when it is not `False`, so is the rest. -/
theorem typeOf_and_inv {x y : Cedar.Spec.Expr} {c : Capabilities} {env : TypeEnv}
    (h : IsBool (typeOf (.and x y) c env)) :
    ∃ tx cx b, typeOf x c env = .ok (tx, cx) ∧ tx.typeOf = .bool b ∧
      (b ≠ .ff → IsBool (typeOf y (c ∪ cx) env)) := by
  obtain ⟨t, ct, bt, h, -⟩ := h
  rw [typeOf] at h
  cases hx : typeOf x c env with
  | error e => rw [hx] at h; cases h
  | ok r =>
    obtain ⟨tx, cx⟩ := r
    rw [hx] at h
    simp only [Except.bind_ok] at h
    unfold typeOfAnd at h
    cases htx : tx.typeOf with
    | bool b =>
      refine ⟨tx, cx, b, rfl, htx, fun hb => ?_⟩
      rw [htx] at h
      cases b with
      | ff => exact absurd rfl hb
      | tt | anyBool =>
        simp only at h
        cases hy : typeOf y (c ∪ cx) env with
        | error e => rw [hy] at h; cases h
        | ok r =>
          obtain ⟨ty, cy⟩ := r
          rw [hy] at h
          simp only [Except.bind_ok] at h
          cases hty : ty.typeOf with
          | bool b' => exact ⟨ty, cy, b', rfl, hty⟩
          | _ => rw [hty] at h; cases h
    | _ => rw [htx] at h; cases h

/-- **Replacing a conjunct.** In a chain Cedar types as a `Bool`, replace a condition `c` that
Cedar types as a `Bool` other than `False`, with no capabilities, by one `c'` it types as a `Bool`
with no capabilities, wherever its typing reaches the condition: the chain still types as a
`Bool`. -/
theorem andChain_replace {env : TypeEnv} {c c' : Cedar.Spec.Condition}
    {post : Cedar.Spec.Conditions}
    (hc : ∀ ca tx cx, typeOf c.toExpr ca env = .ok (tx, cx) → tx.typeOf ≠ .bool .ff ∧ cx = ∅) :
    (xs : List Cedar.Spec.Expr) → (c₀ : Capabilities) →
      (∀ ca, Reaches env xs c₀ ca → ∃ tx b, typeOf c'.toExpr ca env = .ok (tx, ∅) ∧
        tx.typeOf = .bool b) →
      IsBool (typeOf (andChain xs (condTail c post)) c₀ env) →
      IsBool (typeOf (andChain xs (condTail c' post)) c₀ env)
  | [], c₀, h', h => by
    obtain ⟨tn, bn, hn, hbn⟩ := h' c₀ .nil
    cases post with
    | nil => exact ⟨tn, ∅, bn, hn, hbn⟩
    | cons d ds =>
      obtain ⟨to, co, bo, ho, hbo, hrest⟩ := typeOf_and_inv h
      obtain ⟨hno, hco⟩ := hc c₀ to co ho
      subst hco
      have hR := hrest (by rintro rfl; exact hno hbo)
      simp only [andChain, condTail]
      rw [typeOf, hn]
      simp only [Except.bind_ok]
      cases bn with
      | ff => exact typeOfAnd_ff hbn
      | tt | anyBool => exact typeOfAnd_bool hbn hR
  | x :: xs, c₀, h', h => by
    obtain ⟨tx, cx, bx, hx, hbx, hrest⟩ := typeOf_and_inv h
    simp only [andChain]
    rw [typeOf, hx]
    simp only [Except.bind_ok]
    cases bx with
    | ff => exact typeOfAnd_ff hbx
    | tt | anyBool =>
      refine typeOfAnd_bool hbx (andChain_replace hc xs (c₀ ∪ cx) (fun ca hr => ?_)
        (hrest (by simp)))
      exact h' ca (.cons hx (by rw [hbx]; simp) hr)

end

/-! ## A policy, in one environment -/

section

open Cedar.Validation (mapOnVars substituteAction typecheckPolicy subty)

theorem mapOnVars_andChain (f : Var → Cedar.Spec.Expr) :
    (xs : List Cedar.Spec.Expr) → (z : Cedar.Spec.Expr) →
      mapOnVars f (andChain xs z) = andChain (xs.map (mapOnVars f)) (mapOnVars f z)
  | [], _ => rfl
  | x :: xs, z => by simp [andChain, mapOnVars, mapOnVars_andChain f xs z]

/-- A condition with its body's variables mapped. -/
def mapCond (f : Var → Cedar.Spec.Expr) (c : Cedar.Spec.Condition) : Cedar.Spec.Condition :=
  ⟨c.kind, mapOnVars f c.body⟩

theorem mapOnVars_condition (f : Var → Cedar.Spec.Expr) (c : Cedar.Spec.Condition) :
    mapOnVars f c.toExpr = (mapCond f c).toExpr := by
  obtain ⟨k, b⟩ := c
  cases k <;> simp [Cedar.Spec.Condition.toExpr, mapCond, mapOnVars]

theorem mapOnVars_conditions (f : Var → Cedar.Spec.Expr) :
    (cs : Cedar.Spec.Conditions) →
      mapOnVars f (Cedar.Spec.Conditions.toExpr cs) =
        Cedar.Spec.Conditions.toExpr (cs.map (mapCond f))
  | [] => by simp [Cedar.Spec.Conditions.toExpr, mapOnVars]
  | [c] => by simp [Cedar.Spec.Conditions.toExpr, mapOnVars_condition]
  | c :: d :: ds => by
    have h₁ := cedar_conditions_toExpr_cons c (d :: ds) (by simp)
    have h₂ := cedar_conditions_toExpr_cons (mapCond f c) ((d :: ds).map (mapCond f)) (by simp)
    rw [h₁, show List.map (mapCond f) (c :: d :: ds) =
      mapCond f c :: List.map (mapCond f) (d :: ds) from rfl, h₂]
    simp only [mapOnVars, mapOnVars_condition]
    rw [mapOnVars_conditions f (d :: ds)]

theorem mapOnVars_condTail (f : Var → Cedar.Spec.Expr) (c : Cedar.Spec.Condition) :
    (post : Cedar.Spec.Conditions) →
      mapOnVars f (condTail c post) = condTail (mapCond f c) (post.map (mapCond f))
  | [] => by simp [condTail, mapOnVars_condition]
  | d :: ds => by
    simp only [condTail, mapOnVars, mapOnVars_condition, mapOnVars_conditions, List.map_cons]

theorem bool_of_subty {ty : CedarType} (h : (ty ⊑ .bool .anyBool) = true) :
    ∃ b, ty = .bool b := by
  unfold subty at h
  cases ty <;> simp_all [Cedar.Validation.lub?]

/-- **Replacing a condition of a policy, in one environment.** If Cedar types a policy in an
environment, and one of its conditions, after action substitution, is one that Cedar types as a
`Bool` other than `False` with no capabilities, replacing that condition's body by one that action
substitution leaves alone and that Cedar types as a `Bool` with no capabilities wherever its typing
reaches the condition keeps the policy typed in the environment. -/
theorem typecheckPolicy_replace {L : Cedar.Spec.Policy} {env : TypeEnv}
    {pre post : Cedar.Spec.Conditions} {k : Cedar.Spec.ConditionKind} {x e : Cedar.Spec.Expr}
    (hL : L.condition = pre ++ ⟨k, x⟩ :: post)
    (hx : substituteAction env.reqty.action x = x) (he : substituteAction env.reqty.action e = e)
    (hc : ∀ ca tx cx, typeOf (Cedar.Spec.Condition.toExpr ⟨k, x⟩) ca env = .ok (tx, cx) →
      tx.typeOf ≠ .bool .ff ∧ cx = ∅)
    (hc' : ∀ ca, Reaches env
        ([L.principalScope.toExpr, L.actionScope.toExpr, L.resourceScope.toExpr] ++
          pre.map (·.toExpr) |>.map (mapOnVars (actionSubst env.reqty.action))) ∅ ca →
      ∃ tx b, typeOf (Cedar.Spec.Condition.toExpr ⟨k, e⟩) ca env = .ok (tx, ∅) ∧
        tx.typeOf = .bool b)
    {tL : TypedExpr} (htL : typecheckPolicy L env = .ok tL) :
    ∃ tO, typecheckPolicy { L with condition := pre ++ ⟨k, e⟩ :: post } env = .ok tO := by
  have hsplit := policy_toExpr_split L hL
  have hsplit' := policy_toExpr_split { L with condition := pre ++ ⟨k, e⟩ :: post }
    (pre := pre) (post := post) (c := ⟨k, e⟩) rfl
  dsimp only at hsplit'
  unfold typecheckPolicy at htL ⊢
  rw [hsplit] at htL
  rw [hsplit']
  simp only [substituteAction_eq] at htL ⊢ hx he
  simp only [mapOnVars_andChain, mapOnVars_condTail] at htL ⊢
  have hcx : mapCond (actionSubst env.reqty.action) ⟨k, x⟩ = ⟨k, x⟩ := by simp [mapCond, hx]
  have hce : mapCond (actionSubst env.reqty.action) ⟨k, e⟩ = ⟨k, e⟩ := by simp [mapCond, he]
  rw [hcx] at htL
  rw [hce]
  -- The policy's chain types as a `Bool`.
  have hL' : IsBool (typeOf (andChain (([L.principalScope.toExpr, L.actionScope.toExpr,
      L.resourceScope.toExpr] ++ pre.map (·.toExpr)).map (mapOnVars (actionSubst env.reqty.action)))
      (condTail ⟨k, x⟩ (post.map (mapCond (actionSubst env.reqty.action))))) ∅ env) := by
    split at htL
    · rename_i tx cx hty
      split at htL
      · rename_i hsub
        obtain ⟨b, hb⟩ := bool_of_subty hsub
        exact ⟨tx, cx, b, hty, hb⟩
      · cases htL
    · cases htL
  obtain ⟨tO, cO, bO, hO, hbO⟩ := andChain_replace hc _ ∅ hc' hL'
  rw [hO]
  simp only [hbO]
  exact ⟨tO, by
    have : (CedarType.bool bO ⊑ .bool .anyBool) = true := by
      cases bO <;> simp [subty, Cedar.Validation.lub?, Cedar.Validation.lubBool]
    simp [this]⟩

end

/-! ## The scope a policy's typing passes

Cedar types each scope constraint in each environment, and narrows: a constraint the request
type cannot satisfy types as `False`. So where Cedar's typing passes the three scope constraints,
the rule's scope admits the environment (`Policy.admits`). -/

section

open Cedar.Validation (mapOnVars typeOfLit typeOfVar typeOfBinaryApp typeOfEq typeOfUnaryApp
  typeOfInₑ typeOfInₛ lub? ActionSchema Schema)
open Cedar.Spec (EntityType)

variable {A : Schema} {env : TypeEnv}

theorem lub_entity {e₁ e₂ : EntityType} {T : CedarType}
    (h : (CedarType.entity e₁ ⊔ .entity e₂) = some T) :
    e₁ = e₂ := by
  simp only [lub?] at h
  split at h
  · simp_all
  · cases h

/-- The type of a scope variable. -/
theorem typeOf_var_entity {v : Var} {c : Capabilities} {T : EntityType}
    (hT : (v = .principal ∧ T = env.reqty.principal) ∨ (v = .resource ∧ T = env.reqty.resource)) :
    typeOf (.var v) c env = .ok (.var v (.entity T), ∅) := by
  rcases hT with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [typeOf, typeOfVar, Cedar.Validation.ok]

/-- **A principal or resource scope constraint Cedar does not type as `False` admits the scope
variable's type.** -/
theorem scopeAdmitsType_of_typeOf (hets : env.ets = A.ets)
    (hmaybe : ∀ e e', env.acts.maybeDescendentOf e e' = A.acts.maybeDescendentOf e e')
    {v : Var} {T : EntityType}
    (hT : (v = .principal ∧ T = env.reqty.principal) ∨ (v = .resource ∧ T = env.reqty.resource))
    {s : Cedar.Spec.Scope} {c : Capabilities} {tx : TypedExpr} {cx : Capabilities}
    (h : typeOf (s.toExpr v) c env = .ok (tx, cx)) (hne : tx.typeOf ≠ .bool .ff) :
    scopeAdmitsType A s T = true := by
  have hvar := typeOf_var_entity (c := c) hT
  cases s with
  | any => rfl
  | eq uid =>
    simp only [Cedar.Spec.Scope.toExpr, Cedar.Spec.Var.eqEntityUID] at h
    rw [typeOf] at h
    simp only [hvar, Except.bind_ok] at h
    rw [typeOf] at h
    simp only [typeOfLit] at h
    split at h
    · simp only [Cedar.Validation.ok, Except.bind_ok, typeOfBinaryApp, typeOfEq] at h
      cases hl : (CedarType.entity T ⊔ .entity uid.ty) with
      | some U =>
        have := lub_entity hl
        simp [scopeAdmitsType, this]
      | none =>
        simp [TypedExpr.typeOf, hl, Cedar.Validation.ok] at h
        obtain ⟨rfl, -⟩ := h
        exact absurd rfl hne
    · simp [Cedar.Validation.err] at h
  | mem uid =>
    simp only [Cedar.Spec.Scope.toExpr, Cedar.Spec.Var.inEntityUID] at h
    rw [typeOf] at h
    simp only [hvar, Except.bind_ok] at h
    rw [typeOf] at h
    simp only [typeOfLit] at h
    split at h
    · simp only [Cedar.Validation.ok, Except.bind_ok, typeOfBinaryApp, TypedExpr.typeOf,
        typeOfInₑ, Cedar.Validation.actionUID?, Cedar.Validation.entityUID?] at h
      by_cases hd : env.descendentOf T uid.ty = true
      · simp only [scopeAdmitsType, Schema.memberOfType, ← hmaybe]
        unfold Cedar.Validation.TypeEnv.descendentOf at hd
        rw [hets] at hd
        split at hd
        · simp_all
        · cases hf : A.ets.find? T <;> simp_all
      · exfalso
        rcases hT with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;>
        · simp [hd, Cedar.Validation.actionUID?, Cedar.Validation.entityUID?] at h
          obtain ⟨rfl, -⟩ := h
          simp [TypedExpr.typeOf] at hne
    · simp [Cedar.Validation.err] at h
  | is ety =>
    simp only [Cedar.Spec.Scope.toExpr, Cedar.Spec.Var.isEntityType] at h
    rw [typeOf] at h
    simp only [hvar, Except.bind_ok, typeOfUnaryApp, TypedExpr.typeOf, Cedar.Validation.ok,
      Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    simp only [TypedExpr.typeOf] at hne
    split at hne
    · simp_all [scopeAdmitsType]
    · exact absurd rfl hne
  | isMem ety uid =>
    by_cases hE : ety = T
    · simp [scopeAdmitsType, hE]
    · exfalso
      simp only [Cedar.Spec.Scope.toExpr, Cedar.Spec.Var.isEntityType] at h
      have hx : typeOf (.unaryApp (.is ety) (.var v)) c env =
          .ok (.unaryApp (.is ety) (.var v (.entity T)) (.bool .ff), ∅) := by
        rw [typeOf]
        simp [hvar, typeOfUnaryApp, TypedExpr.typeOf, hE, Cedar.Validation.ok]
      rw [typeOf, hx] at h
      simp only [Except.bind_ok, Cedar.Validation.typeOfAnd, TypedExpr.typeOf,
        Cedar.Validation.ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact hne rfl
end


section

open Cedar.Validation (mapOnVars Schema)

variable {A : Schema} {env : TypeEnv}

theorem reaches_append {env : TypeEnv} :
    (xs ys : List Cedar.Spec.Expr) → (c ca : Capabilities) → Reaches env (xs ++ ys) c ca →
      ∃ cb, Reaches env xs c cb ∧ Reaches env ys cb ca
  | [], _, c, _, h => ⟨c, .nil, h⟩
  | x :: xs, ys, c, ca, .cons hx hne hr => by
    obtain ⟨cb, h₁, h₂⟩ := reaches_append xs ys _ ca hr
    exact ⟨cb, .cons hx hne h₁, h₂⟩

theorem mapOnVars_scope (uid : EntityUID) (s : Cedar.Spec.Scope) {v : Var} (hv : v ≠ .action) :
    mapOnVars (actionSubst uid) (s.toExpr v) = s.toExpr v := by
  have hav : actionSubst uid v = .var v := by cases v <;> simp_all [actionSubst]
  cases s <;> simp [Cedar.Spec.Scope.toExpr, Cedar.Spec.Var.eqEntityUID, Cedar.Spec.Var.inEntityUID,
    Cedar.Spec.Var.isEntityType, mapOnVars, hav]

/-- **Where Cedar's typing passes a rule's scope, the scope admits the environment.** -/
theorem admits_of_reaches (hets : env.ets = A.ets)
    (hmaybe : ∀ e e', env.acts.maybeDescendentOf e e' = A.acts.maybeDescendentOf e e')
    (hdesc : ∀ a b, env.acts.descendentOf a b = A.acts.descendentOf a b)
    (hact : env.acts.contains env.reqty.action = true) {q : Policy} {c ca : Capabilities}
    (h : Reaches env ([q.principalScope.toExpr, q.actionScope.toExpr, q.resourceScope.toExpr].map
      (mapOnVars (actionSubst env.reqty.action))) c ca) :
    q.admits A env = true := by
  cases hps : q.principalScope with
  | principalScope ps =>
    cases hrs : q.resourceScope with
    | resourceScope rs =>
      simp only [List.map_cons, List.map_nil, hps, hrs, Cedar.Spec.PrincipalScope.toExpr,
        Cedar.Spec.ResourceScope.toExpr, mapOnVars_scope _ _ (by simp : Var.principal ≠ .action),
        mapOnVars_scope _ _ (by simp : Var.resource ≠ .action)] at h
      rcases h with _ | ⟨hp, hpn, h⟩
      rcases h with _ | ⟨ha, han, h⟩
      rcases h with _ | ⟨hr, hrn, -⟩
      unfold Policy.admits
      rw [hps, hrs]
      simp only [Bool.and_eq_true]
      exact ⟨⟨scopeAdmitsType_of_typeOf hets hmaybe (.inl ⟨rfl, rfl⟩) hp hpn,
        actionScopeAdmits_of_typeOf hdesc hact ha han⟩,
        scopeAdmitsType_of_typeOf hets hmaybe (.inr ⟨rfl, rfl⟩) hr hrn⟩

end

/-! ## The augmented environments

Cedar validates the lowered rules against the augmented schema, whose environments add the
hoisted attributes to each action's context (`augmentEnv`). Its entity types, action hierarchy, and
declared actions are the action schema's, and Dogwood's typing of a translated leaf in an
environment of the action schema carries over to the augmented one. -/

section

open Cedar.Validation (Schema ActionSchema QualifiedType)
open Cedar.Spec (EntityType)

variable {A : Schema} {H : List (Attr × QualifiedType)} {env : TypeEnv}

theorem augmentEnv_descendentOf (h : env ∈ A.environments) (a b : EntityUID) :
    (augmentEnv A H env).acts.descendentOf a b = A.acts.descendentOf a b := by
  simp only [augmentEnv, augment_acts]
  unfold ActionSchema.descendentOf
  rw [Cedar.Data.Map.find?_mapOnValues]
  cases A.acts.find? a <;> rfl

theorem augmentEnv_maybeDescendentOf (e e' : EntityType) :
    (augmentEnv A H env).acts.maybeDescendentOf e e' = A.acts.maybeDescendentOf e e' := by
  simp only [augmentEnv, augment_acts, ActionSchema.maybeDescendentOf, Cedar.Data.Map.mapOnValues,
    Cedar.Data.Map.toList, List.any_map]
  rfl

theorem environments_ets (h : env ∈ A.environments) : env.ets = A.ets := by
  obtain ⟨_, _, _, _, _, _, _, rfl⟩ := mem_environments.mp h
  rfl

theorem environments_acts (h : env ∈ A.environments) : env.acts = A.acts := by
  obtain ⟨_, _, _, _, _, _, _, rfl⟩ := mem_environments.mp h
  rfl

theorem environments_action (h : env ∈ A.environments) :
    A.acts.contains env.reqty.action = true := by
  obtain ⟨a, entry, p, r, hmem, -, -, rfl⟩ := mem_environments.mp h
  unfold ActionSchema.contains Cedar.Data.Map.find?
  cases hf : (Cedar.Data.Map.toList A.acts).find? (fun x => x.1 == a) with
  | none =>
    have := List.find?_eq_none.mp hf _ hmem
    simp at this
  | some x => simp

theorem augmentEnv_context_find? {a : Attr} {q : QualifiedType}
    (h : env.reqty.context.find? a = some q) :
    (augmentEnv A H env).reqty.context.find? a = some q := by
  simp only [augmentEnv]
  rw [make_append_find?]
  rw [map_find?_eq] at h
  cases hf : env.reqty.context.toList.find? (·.1 == a) with
  | none => rw [hf] at h; cases h
  | some p =>
    rw [hf] at h
    simp only [Option.map_some, Option.some.injEq] at h
    simp [h]

/-- A path typed in a record type is typed alike in one that finds its attributes alike. -/
theorem pathType_mono {present : Path → Bool} {rty rty' : RecordType}
    (h : ∀ a q, rty.find? a = some q → rty'.find? a = some q) {pre : Path} :
    (p : Path) → {T : CedarType} → pathType? present rty pre p = some T →
      pathType? present rty' pre p = some T
  | [], _, hT => by simp [pathType?] at hT
  | a :: p, T, hT => by
    unfold pathType? at hT ⊢
    cases hf : rty.find? a with
    | none => rw [hf] at hT; cases hT
    | some q =>
      rw [hf] at hT
      rw [h a q hf]
      exact hT

end

section

variable {C C' : TypingCtx}

/-- What Dogwood's typing of a translated term reads of the typing context. -/
structure TypingCtxLE (C C' : TypingCtx) : Prop where
  ets : C'.env.ets = C.env.ets
  acts : ∀ uid, C'.env.acts.contains uid = C.env.acts.contains uid
  principal : C'.env.reqty.principal = C.env.reqty.principal
  resource : C'.env.reqty.resource = C.env.reqty.resource
  context : ∀ a q, C.env.reqty.context.find? a = some q → C'.env.reqty.context.find? a = some q
  facts : C'.facts = C.facts

private theorem typed_simple_mono (h : TypingCtxLE C C') {t : Term}
    (ht : (∃ p, t = .context p) ∨ (∃ r p, t = .scope r p) ∨ (∃ i, t = .long i) ∨
      (∃ s, t = .string s) ∨ (∃ b, t = .bool b) ∨ (∃ u, t = .entity u) ∨ (∃ s, t = .decimal s))
    {τ : TType} (hty : Term.Typed C [] t τ) : Term.Typed C' [] t τ := by
  have hs : ∀ r, C'.scopeType r = C.scopeType r := fun r => by
    cases r
    · exact h.principal
    · exact h.resource
  rcases ht with ⟨p, rfl⟩ | ⟨r, p, rfl⟩ | ⟨i, rfl⟩ | ⟨s, rfl⟩ | ⟨b, rfl⟩ | ⟨u, rfl⟩ | ⟨s, rfl⟩
  · cases hty with
    | context hT hsupp =>
      refine .context ?_ hsupp
      unfold TypingCtx.contextType? at hT ⊢
      rw [h.facts]
      exact pathType_mono h.context _ hT
  · cases hty with
    | scopeRoot => rw [← hs]; exact .scopeRoot
    | scopeAttr hne hT hsupp =>
      refine .scopeAttr hne ?_ hsupp
      unfold TypingCtx.scopeAttrType? at hT ⊢
      rw [hs, h.ets, h.facts]
      exact hT
  · cases hty; exact .long
  · cases hty; exact .string
  · cases hty; exact .bool
  · cases hty with
    | entity hv => exact .entity (by rw [h.ets, h.acts]; exact hv)
  · cases hty with
    | decimal hd => exact .decimal hd

theorem typed_toTerm_mono (h : TypingCtxLE C C') :
    (x : Cedar.Spec.Expr) → (t : Term) → toTerm x = some t → {τ : TType} →
      Term.Typed C [] t τ → Term.Typed C' [] t τ
  | .binaryApp .add x y, t, ht, τ, hty | .binaryApp .sub x y, t, ht, τ, hty
  | .binaryApp .mul x y, t, ht, τ, hty => by
    simp only [toTerm, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at ht
    obtain ⟨tx, htx, ty, hty', rfl⟩ := ht
    cases hty with
    | arith hl hr =>
      exact .arith (typed_toTerm_mono h x tx htx hl) (typed_toTerm_mono h y ty hty' hr)
  | .lit p, t, ht, τ, hty => by
    refine typed_simple_mono h ?_ hty
    cases p <;> simp only [toTerm, Option.some.injEq] at ht <;> subst ht <;> simp
  | .var v, t, ht, τ, hty => by
    refine typed_simple_mono h ?_ hty
    cases v <;> simp only [toTerm, Option.some.injEq, reduceCtorEq] at ht <;> subst ht <;> simp
  | .getAttr x a, t, ht, τ, hty => by
    refine typed_simple_mono h ?_ hty
    rcases attrTerm_shape ht with ⟨p, rfl⟩ | ⟨r, p, rfl⟩ <;> simp
  | .call _ _, t, ht, τ, hty => by
    refine typed_simple_mono h ?_ hty
    obtain ⟨s, -, -, rfl⟩ := toTerm_call ht
    simp
  | .ite .., _, ht, _, _ | .and .., _, ht, _, _ | .or .., _, ht, _, _
  | .unaryApp .., _, ht, _, _ | .binaryApp .eq .., _, ht, _, _
  | .binaryApp .mem .., _, ht, _, _ | .binaryApp .hasTag .., _, ht, _, _
  | .binaryApp .getTag .., _, ht, _, _ | .binaryApp .less .., _, ht, _, _
  | .binaryApp .lessEq .., _, ht, _, _ | .binaryApp .contains .., _, ht, _, _
  | .binaryApp .containsAll .., _, ht, _, _ | .binaryApp .containsAny .., _, ht, _, _
  | .hasAttr .., _, ht, _, _ | .extHasAttr .., _, ht, _, _ | .set .., _, ht, _, _
  | .record .., _, ht, _, _ => by simp [toTerm] at ht

/-- **Dogwood's typing of a translation carries over** to a typing context with the same entity
types, declared actions, scope types, and facts, whose context type finds the attributes alike. -/
theorem wellTyped_toTemporal_mono (h : TypingCtxLE C C') :
    (e : Cedar.Spec.Expr) → (φ : Formula) → toTemporal e = some φ → φ.WellTyped C [] →
      φ.WellTyped C' []
  | .binaryApp .eq x y, φ, hφ, hwt | .binaryApp .less x y, φ, hφ, hwt
  | .binaryApp .lessEq x y, φ, hφ, hwt => by
    simp only [toTemporal, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hφ
    obtain ⟨tx, htx, ty, hty, rfl⟩ := hφ
    cases hwt with
    | eq hno hx hy hc =>
      exact .eq hno (typed_toTerm_mono h x tx htx hx) (typed_toTerm_mono h y ty hty hy) hc
    | ord ho hx hy =>
      exact .ord ho (typed_toTerm_mono h x tx htx hx) (typed_toTerm_mono h y ty hty hy)
  | .and x y, φ, hφ, hwt => by
    simp only [toTemporal, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hφ
    obtain ⟨φx, hφx, φy, hφy, rfl⟩ := hφ
    cases hwt with
    | and hx hy =>
      exact .and (wellTyped_toTemporal_mono h x φx hφx hx) (wellTyped_toTemporal_mono h y φy hφy hy)
  | .or x y, φ, hφ, hwt => by
    simp only [toTemporal, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hφ
    obtain ⟨φx, hφx, φy, hφy, rfl⟩ := hφ
    cases hwt with
    | not h' =>
      cases h' with
      | and hx hy =>
        cases hx with
        | not hx =>
          cases hy with
          | not hy =>
            exact .not (.and (.not (wellTyped_toTemporal_mono h x φx hφx hx))
              (.not (wellTyped_toTemporal_mono h y φy hφy hy)))
  | .unaryApp .not x, φ, hφ, hwt => by
    simp only [toTemporal, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hφ
    obtain ⟨φx, hφx, rfl⟩ := hφ
    cases hwt with
    | not hx => exact .not (wellTyped_toTemporal_mono h x φx hφx hx)
  | .lit _, _, hφ, _ | .var _, _, hφ, _ | .ite .., _, hφ, _
  | .unaryApp .neg _, _, hφ, _ | .unaryApp .isEmpty _, _, hφ, _
  | .unaryApp (.like _) _, _, hφ, _ | .unaryApp (.is _) _, _, hφ, _
  | .binaryApp .mem .., _, hφ, _ | .binaryApp .hasTag .., _, hφ, _
  | .binaryApp .getTag .., _, hφ, _ | .binaryApp .add .., _, hφ, _
  | .binaryApp .sub .., _, hφ, _ | .binaryApp .mul .., _, hφ, _
  | .binaryApp .contains .., _, hφ, _ | .binaryApp .containsAll .., _, hφ, _
  | .binaryApp .containsAny .., _, hφ, _ | .getAttr .., _, hφ, _
  | .hasAttr .., _, hφ, _ | .extHasAttr .., _, hφ, _ | .set .., _, hφ, _
  | .record .., _, hφ, _ | .call .., _, hφ, _ => by simp [toTemporal] at hφ
end

/-! ## The capabilities a rule's earlier conditions earn

Cedar's typing of a `has` test that does not type as `False` earns its capability, or tests an
attribute required where it types the subject. So where Cedar's typing of a rule reaches a
condition, the facts of the conditions before it are covered. -/

section

open Cedar.Validation (mapOnVars typeOfHasAttr hasAttrInRecord typeOfGetAttr)

variable {env : TypeEnv}

/-- An attribute chain: a variable, then attribute reads. -/
inductive IsChain : Cedar.Spec.Expr → Prop
  | var (v : Var) : IsChain (.var v)
  | getAttr {x : Cedar.Spec.Expr} (a : Attr) : IsChain x → IsChain (.getAttr x a)

theorem isChain_foldl : (p : Path) → {x : Cedar.Spec.Expr} → IsChain x →
    IsChain (p.foldl (fun x a => Cedar.Spec.Expr.getAttr x a) x)
  | [], _, h => h
  | a :: p, _, h => isChain_foldl p (.getAttr a h)

theorem isChain_attrChainExpr (v : Var) (p : Path) : IsChain (attrChainExpr v p) := by
  rw [attrChainExpr_eq_foldl]
  exact isChain_foldl p (.var v)

/-- **The type `typeOfGetAttr` gives depends only on the subject's type.** -/
theorem typeOfGetAttr_type_det {s₁ s₂ : TypedExpr} (hs : s₁.typeOf = s₂.typeOf)
    {y : Cedar.Spec.Expr} {a : Attr} {c₁ c₂ : Capabilities} {t₁ t₂ : TypedExpr}
    {k₁ k₂ : Capabilities} (h₁ : typeOfGetAttr s₁ y a c₁ env = .ok (t₁, k₁))
    (h₂ : typeOfGetAttr s₂ y a c₂ env = .ok (t₂, k₂)) : t₁.typeOf = t₂.typeOf := by
  have hrec : ∀ {rty : RecordType} {T₁ T₂ u₁ u₂ : CedarType} {e₁ e₂ : Capabilities},
      Cedar.Validation.getAttrInRecord T₁ rty y a c₁ = .ok (u₁, e₁) →
      Cedar.Validation.getAttrInRecord T₂ rty y a c₂ = .ok (u₂, e₂) → u₁ = u₂ := by
    intro rty T₁ T₂ u₁ u₂ e₁ e₂ g₁ g₂
    unfold Cedar.Validation.getAttrInRecord at g₁ g₂
    split at g₁
    · rename_i aty haty
      rw [haty] at g₂
      simp only [Cedar.Validation.ok, Except.ok.injEq, Prod.mk.injEq] at g₁ g₂
      rw [← g₁.1, ← g₂.1]
    · rename_i aty haty
      rw [haty] at g₂
      simp only at g₁ g₂
      split at g₁ <;> split at g₂ <;> simp_all [Cedar.Validation.ok, Cedar.Validation.err]
    · cases g₁
  have hfin : ∀ {T₁ T₂ : CedarType} {rty : RecordType},
      (do let w ← Cedar.Validation.getAttrInRecord T₁ rty y a c₁
          Cedar.Validation.ok (s₁.getAttr a w.1) w.2 : ResultType) = .ok (t₁, k₁) →
      (do let w ← Cedar.Validation.getAttrInRecord T₂ rty y a c₂
          Cedar.Validation.ok (s₂.getAttr a w.1) w.2 : ResultType) = .ok (t₂, k₂) →
      t₁.typeOf = t₂.typeOf := by
    intro T₁ T₂ rty g₁ g₂
    cases w₁ : Cedar.Validation.getAttrInRecord T₁ rty y a c₁ with
    | error e => rw [w₁] at g₁; cases g₁
    | ok w =>
      cases w₂ : Cedar.Validation.getAttrInRecord T₂ rty y a c₂ with
      | error e => rw [w₂] at g₂; cases g₂
      | ok w' =>
        rw [w₁] at g₁
        rw [w₂] at g₂
        simp only [Except.bind_ok, Cedar.Validation.ok, Except.ok.injEq, Prod.mk.injEq] at g₁ g₂
        rw [← g₁.1, ← g₂.1]
        exact hrec w₁ w₂
  unfold typeOfGetAttr at h₁ h₂
  rw [← hs] at h₂
  split at h₁
  · rename_i rty hrty
    rw [hrty] at h₂
    simp only at h₁ h₂
    exact hfin h₁ h₂
  · rename_i ety hety
    rw [hety] at h₂
    simp only at h₁ h₂
    split at h₁
    · rename_i rty hrty
      rw [hrty] at h₂
      simp only at h₁ h₂
      exact hfin h₁ h₂
    · cases h₁
  · cases h₁

/-- **Cedar's type of an attribute chain does not depend on the capabilities.** -/
theorem typeOf_chain_det {x : Cedar.Spec.Expr} (hx : IsChain x) :
    ∀ {c₁ c₂ : Capabilities} {t₁ t₂ : TypedExpr} {k₁ k₂ : Capabilities},
      typeOf x c₁ env = .ok (t₁, k₁) → typeOf x c₂ env = .ok (t₂, k₂) →
      t₁.typeOf = t₂.typeOf := by
  induction hx with
  | var v =>
    intro c₁ c₂ t₁ t₂ k₁ k₂ h₁ h₂
    rw [typeOf] at h₁ h₂
    rw [h₁] at h₂
    cases h₂
    rfl
  | getAttr a hy ih =>
    rename_i y
    intro c₁ c₂ t₁ t₂ k₁ k₂ h₁ h₂
    rw [typeOf] at h₁ h₂
    cases hx₁ : typeOf y c₁ env with
    | error e => rw [hx₁] at h₁; cases h₁
    | ok r₁ =>
      cases hx₂ : typeOf y c₂ env with
      | error e => rw [hx₂] at h₂; cases h₂
      | ok r₂ =>
        rw [hx₁] at h₁
        rw [hx₂] at h₂
        simp only [Except.bind_ok] at h₁ h₂
        exact typeOfGetAttr_type_det (ih hx₁ hx₂) h₁ h₂
end

section

open Cedar.Validation (typeOfHasAttr hasAttrInRecord)

variable {env : TypeEnv}

/-- **A `has` test on an attribute chain that Cedar does not type as `False` earns its
capability**, or tests an attribute required where Cedar types the chain. -/
theorem caps_of_typeOfHasAttr {Y : Cedar.Spec.Expr} {ty₁ : TypedExpr}
    (hty : ∀ c' t' ct', typeOf Y c' env = .ok (t', ct') → t'.typeOf = ty₁.typeOf)
    {a : Attr} {c : Capabilities}
    {t : TypedExpr} {ct : Capabilities} (h : typeOfHasAttr ty₁ Y a c env = .ok (t, ct))
    (hne : t.typeOf ≠ .bool .ff) : (Y, Key.attr a) ∈ c ∪ ct ∨ RequiredAt env Y a := by
  have hrec : ∀ {rty : RecordType} {known : Bool},
      (do let w ← hasAttrInRecord rty Y a c known
          Cedar.Validation.ok (TypedExpr.hasAttr ty₁ a w.1) w.2 : ResultType) = .ok (t, ct) →
      (known = true → ty₁.typeOf = .record rty) →
      (Y, Key.attr a) ∈ c ∪ ct ∨ RequiredAt env Y a := by
    intro rty known g hk
    unfold hasAttrInRecord at g
    split at g
    · rename_i qty hq
      split at g
      · rename_i hcond
        rcases Bool.or_eq_true _ _ |>.mp hcond with hm | hr
        · exact .inl (by simp at hm; simp [hm])
        · right
          simp only [Bool.and_eq_true] at hr
          obtain ⟨hreq, hknown⟩ := hr
          intro c' t' ct' hy'
          refine ⟨rty, ?_, ?_, ?_⟩
          · cases qty with
            | required aty => exact aty
            | optional aty => simp [Cedar.Validation.Qualified.isRequired] at hreq
          · rw [hty c' t' ct' hy', hk hknown]
          · cases qty with
            | required aty => exact hq
            | optional aty => simp [Cedar.Validation.Qualified.isRequired] at hreq
      · simp only [Cedar.Validation.ok, Except.bind_ok, Except.ok.injEq, Prod.mk.injEq] at g
        obtain ⟨-, rfl⟩ := g
        exact .inl (by simp [Cedar.Validation.Capabilities.singleton])
    · simp only [Cedar.Validation.ok, Except.bind_ok, Except.ok.injEq, Prod.mk.injEq] at g
      obtain ⟨rfl, -⟩ := g
      exact absurd rfl hne
  unfold typeOfHasAttr at h
  split at h
  · rename_i rty hrty
    exact hrec h (fun _ => hrty)
  · rename_i ety hety
    split at h
    · rename_i rty hrty
      exact hrec h (fun hk => by simp at hk)
    · split at h
      · simp only [Cedar.Validation.ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        exact absurd rfl hne
      · cases h
  · cases h

theorem caps_of_hasAttr {Y : Cedar.Spec.Expr} (hY : IsChain Y) {a : Attr} {c : Capabilities}
    {t : TypedExpr} {ct : Capabilities} (h : typeOf (.hasAttr Y a) c env = .ok (t, ct))
    (hne : t.typeOf ≠ .bool .ff) : (Y, Key.attr a) ∈ c ∪ ct ∨ RequiredAt env Y a := by
  rw [typeOf] at h
  cases hy : typeOf Y c env with
  | error e => rw [hy] at h; cases h
  | ok r =>
    obtain ⟨ty₁, c₁⟩ := r
    rw [hy] at h
    simp only [Except.bind_ok] at h
    exact caps_of_typeOfHasAttr (fun c' t' ct' h' => typeOf_chain_det hY h' hy) h hne
end

section

open Cedar.Validation (typeOfHasAttr typeOfGetAttr typeOfExtHasAttr)

variable {env : TypeEnv}

/-- The `has` tests `x has a.b.c` makes: `x has a`, `x.a has b`, `x.a.b has c`. -/
def extHasTests (x : Cedar.Spec.Expr) : Attr → List Attr → List (Cedar.Spec.Expr × Attr)
  | a, [] => [(x, a)]
  | a, b :: rest => (x, a) :: extHasTests (.getAttr x a) b rest

/-- **An extended `has` test that Cedar does not type as `False` earns the capability of each of
its tests**, or tests an attribute required where Cedar types its subject. -/
theorem caps_of_extHas : (bs : List Attr) → {Y : Cedar.Spec.Expr} → {a : Attr} →
    {ty₁ : TypedExpr} →
    (∀ c' t' ct', typeOf Y c' env = .ok (t', ct') → t'.typeOf = ty₁.typeOf) →
    {c : Capabilities} → {bty : Cedar.Validation.BoolType} → {c' : Capabilities} →
    typeOfExtHasAttr ty₁ Y (a :: bs) c env = .ok (bty, c') → bty ≠ .ff →
    ∀ p ∈ extHasTests Y a bs, (p.1, Key.attr p.2) ∈ c ∪ c' ∨ RequiredAt env p.1 p.2
  | [], Y, a, ty₁, hty, c, bty, c', h, hne, p, hp => by
    simp only [extHasTests, List.mem_singleton] at hp
    subst hp
    unfold typeOfExtHasAttr at h
    cases hh : typeOfHasAttr ty₁ Y a c env with
    | error e => rw [hh] at h; cases h
    | ok r =>
      obtain ⟨tyHas, ci⟩ := r
      rw [hh] at h
      simp only [Except.bind_ok] at h
      have hne' : tyHas.typeOf ≠ .bool .ff := by
        intro hff
        rw [hff] at h
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        exact hne h.1.symm
      have hci : ci = c' := by
        split at h <;> (simp only [Except.ok.injEq, Prod.mk.injEq] at h; exact h.2)
      subst hci
      exact caps_of_typeOfHasAttr hty hh hne'
  | b :: rest, Y, a, ty₁, hty, c, bty, c', h, hne, p, hp => by
    unfold typeOfExtHasAttr at h
    cases hh : typeOfHasAttr ty₁ Y a c env with
    | error e => rw [hh] at h; cases h
    | ok r =>
      obtain ⟨tyHas, ci⟩ := r
      rw [hh] at h
      simp only [Except.bind_ok] at h
      have hne' : tyHas.typeOf ≠ .bool .ff := by
        intro hff
        rw [hff] at h
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        exact hne h.1.symm
      split at h
      · rename_i hff; exact absurd hff hne'
      · cases hg : typeOfGetAttr ty₁ Y a (c ∪ ci) env with
        | error e => rw [hg] at h; cases h
        | ok r =>
          obtain ⟨tyNext, cn⟩ := r
          rw [hg] at h
          simp only [Except.bind_ok] at h
          cases hr : typeOfExtHasAttr tyNext (.getAttr Y a) (b :: rest) (c ∪ ci) env with
          | error e => rw [hr] at h; cases h
          | ok r =>
            obtain ⟨bty', c''⟩ := r
            rw [hr] at h
            simp only [Except.bind_ok] at h
            -- The result's capabilities are the first test's and the rest's.
            have hres : bty' ≠ .ff ∧ c' = ci ∪ c'' := by
              cases bty' with
              | ff =>
                simp only [Except.ok.injEq, Prod.mk.injEq] at h
                exact absurd h.1.symm hne
              | tt =>
                simp only at h
                refine ⟨by simp, ?_⟩
                split at h <;> (simp only [Except.ok.injEq, Prod.mk.injEq] at h; exact h.2.symm)
              | anyBool =>
                simp only [Except.ok.injEq, Prod.mk.injEq] at h
                exact ⟨by simp, h.2.symm⟩
            obtain ⟨hne'', rfl⟩ := hres
            simp only [extHasTests, List.mem_cons] at hp
            rcases hp with rfl | hp
            · show (Y, Key.attr a) ∈ c ∪ (ci ∪ c'') ∨ RequiredAt env Y a
              rcases caps_of_typeOfHasAttr hty hh hne' with hm | hm
              · left
                simp only [List.mem_union_iff] at hm ⊢
                rcases hm with hm | hm <;> simp [hm]
              · exact .inr hm
            · have htyN : ∀ c₁ t₁ ct₁, typeOf (.getAttr Y a) c₁ env = .ok (t₁, ct₁) →
                  t₁.typeOf = tyNext.typeOf := by
                intro c₁ t₁ ct₁ h₁
                rw [typeOf] at h₁
                cases hy₁ : typeOf Y c₁ env with
                | error e => rw [hy₁] at h₁; cases h₁
                | ok r =>
                  obtain ⟨s₁, d₁⟩ := r
                  rw [hy₁] at h₁
                  simp only [Except.bind_ok] at h₁
                  exact typeOfGetAttr_type_det (hty c₁ s₁ d₁ hy₁) h₁ hg
              rcases caps_of_extHas rest htyN hr hne'' p hp with hm | hm
              · left
                simp only [List.mem_union_iff] at hm ⊢
                rcases hm with (hm | hm) | hm <;> simp [hm]
              · exact .inr hm

end

section

open Cedar.Validation (mapOnVars typeOfAnd)

variable {env : TypeEnv}

theorem lowerFrom_attrChain : (y : Expr) → (k : Nat) → {v : Var} → {p : Path} →
    y.attrChain? = some (v, p) → (y.lowerFrom k).1 = attrChainExpr v p
  | .var v', k, v, p, h => by
    simp only [Expr.attrChain?, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | .getAttr y a, k, v, p, h => by
    simp only [Expr.attrChain?, Option.map_eq_some_iff, Prod.exists] at h
    obtain ⟨v', p', hy, hvp⟩ := h
    simp only [Prod.mk.injEq] at hvp
    obtain ⟨rfl, rfl⟩ := hvp
    simp only [Expr.lowerFrom]
    rw [lowerFrom_attrChain y k hy, attrChainExpr_snoc]
  | .lit _, _, _, _, h | .ite .., _, _, _, h | .and .., _, _, _, h | .or .., _, _, _, h
  | .unaryApp .., _, _, _, h | .binaryApp .., _, _, _, h | .hasAttr .., _, _, _, h
  | .extHasAttr .., _, _, _, h | .set .., _, _, _, h | .record .., _, _, _, h
  | .call .., _, _, _, h | .temporal _, _, _, _, h | .provider _, _, _, _, h => by
    simp [Expr.attrChain?] at h

theorem mapOnVars_attrChainExpr (u : EntityUID) {v : Var} (hv : v ≠ .action) (p : Path) :
    mapOnVars (actionSubst u) (attrChainExpr v p) = attrChainExpr v p := by
  have hfold : ∀ (q : Path) (x : Cedar.Spec.Expr), mapOnVars (actionSubst u) x = x →
      mapOnVars (actionSubst u) (q.foldl (fun x a => Cedar.Spec.Expr.getAttr x a) x) =
        q.foldl (fun x a => Cedar.Spec.Expr.getAttr x a) x := by
    intro q
    induction q with
    | nil => intro x hx; exact hx
    | cons a q ih => intro x hx; exact ih _ (by simp [mapOnVars, hx])
  rw [attrChainExpr_eq_foldl]
  exact hfold p _ (by cases v <;> simp_all [mapOnVars, actionSubst])

theorem hasFact?_spec {y : Expr} {a : Attr} {g : Guard} (h : y.hasFact? a = some g) :
    ∃ v p, y.attrChain? = some (v, p) ∧ v ≠ .action ∧
      g.expr = .hasAttr (attrChainExpr v p) a := by
  unfold Expr.hasFact? at h
  split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h
  · rename_i p hp
    exact ⟨_, _, hp, by simp, guard_context_expr p a⟩
  · rename_i p hp
    exact ⟨_, _, hp, by simp, by simpa [scopeVar] using guard_scope_expr .principal p a⟩
  · rename_i p hp
    exact ⟨_, _, hp, by simp, by simpa [scopeVar] using guard_scope_expr .resource p a⟩

theorem extHasFacts_spec : (bs : List Attr) → {y : Expr} → {a : Attr} → {g : Guard} →
    g ∈ y.extHasFacts a bs → ∃ v p, y.attrChain? = some (v, p) ∧ v ≠ .action ∧
      ∃ q ∈ extHasTests (attrChainExpr v p) a bs, g.expr = .hasAttr q.1 q.2
  | [], y, a, g, h => by
    simp only [Expr.extHasFacts, Option.mem_toList] at h
    obtain ⟨v, p, hy, hv, he⟩ := hasFact?_spec h
    exact ⟨v, p, hy, hv, (attrChainExpr v p, a), by simp [extHasTests], he⟩
  | b :: rest, y, a, g, h => by
    simp only [Expr.extHasFacts, List.mem_append, Option.mem_toList] at h
    rcases h with h | h
    · obtain ⟨v, p, hy, hv, he⟩ := hasFact?_spec h
      exact ⟨v, p, hy, hv, (attrChainExpr v p, a), by simp [extHasTests], he⟩
    · obtain ⟨v, p', hy, hv, q, hq, he⟩ := extHasFacts_spec rest h
      simp only [Expr.attrChain?, Option.map_eq_some_iff, Prod.exists] at hy
      obtain ⟨v₀, p, hy₀, hvp⟩ := hy
      simp only [Prod.mk.injEq] at hvp
      obtain ⟨rfl, rfl⟩ := hvp
      refine ⟨v₀, p, hy₀, hv, q, ?_, he⟩
      simp only [extHasTests, List.mem_cons]
      exact .inr (by rw [← attrChainExpr_snoc]; exact hq)

theorem typeOf_and_caps {x y : Cedar.Spec.Expr} {c : Capabilities} {t : TypedExpr}
    {ct : Capabilities} (h : typeOf (.and x y) c env = .ok (t, ct))
    (hne : t.typeOf ≠ .bool .ff) :
    ∃ tx cx ty cy, typeOf x c env = .ok (tx, cx) ∧ tx.typeOf ≠ .bool .ff ∧
      typeOf y (c ∪ cx) env = .ok (ty, cy) ∧ ty.typeOf ≠ .bool .ff ∧ ct = cx ∪ cy := by
  rw [typeOf] at h
  cases hx : typeOf x c env with
  | error e => rw [hx] at h; cases h
  | ok r =>
    obtain ⟨tx, cx⟩ := r
    rw [hx] at h
    simp only [Except.bind_ok] at h
    unfold typeOfAnd at h
    cases htx : tx.typeOf with
    | bool b =>
      rw [htx] at h
      cases b with
      | ff =>
        simp only [Cedar.Validation.ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        exact absurd htx hne
      | tt | anyBool =>
        simp only at h
        cases hy : typeOf y (c ∪ cx) env with
        | error e => rw [hy] at h; cases h
        | ok r =>
          obtain ⟨ty, cy⟩ := r
          rw [hy] at h
          simp only [Except.bind_ok] at h
          cases hty : ty.typeOf with
          | bool b' =>
            rw [hty] at h
            cases b' with
            | ff =>
              simp only [Cedar.Validation.ok, Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, -⟩ := h
              simp [TypedExpr.typeOf] at hne
            | tt | anyBool =>
              simp only [Cedar.Validation.ok, Except.ok.injEq, Prod.mk.injEq] at h
              exact ⟨tx, cx, ty, cy, by simp [hx], by simp [htx], by simp [hy], by simp [hty],
                h.2.symm⟩
          | _ => rw [hty] at h; cases h
    | _ => rw [htx] at h; cases h

/-- **A lowered condition that Cedar does not type as `False` earns the capabilities of its
facts**, or its facts test attributes required where Cedar types their subjects. -/
theorem caps_of_facts (u : EntityUID) :
    (x : Expr) → (k : Nat) → {c : Capabilities} → {t : TypedExpr} → {ct : Capabilities} →
      typeOf (mapOnVars (actionSubst u) (x.lowerFrom k).1) c env = .ok (t, ct) →
      t.typeOf ≠ .bool .ff → CapsCover env x.facts (c ∪ ct)
  | .hasAttr y a, k, c, t, ct, h, hne => by
    intro g hg y' a' he
    simp only [Expr.facts, Option.mem_toList] at hg
    obtain ⟨v, p, hy, hv, hg'⟩ := hasFact?_spec hg
    rw [hg'] at he
    simp only [Cedar.Spec.Expr.hasAttr.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    simp only [Expr.lowerFrom, mapOnVars] at h
    rw [lowerFrom_attrChain y k hy, mapOnVars_attrChainExpr u hv] at h
    exact caps_of_hasAttr (isChain_attrChainExpr v p) h hne
  | .extHasAttr y a bs, k, c, t, ct, h, hne => by
    intro g hg y' a' he
    simp only [Expr.facts] at hg
    obtain ⟨v, p, hy, hv, q, hq, hg'⟩ := extHasFacts_spec bs hg
    rw [hg'] at he
    simp only [Cedar.Spec.Expr.hasAttr.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    simp only [Expr.lowerFrom, mapOnVars] at h
    rw [lowerFrom_attrChain y k hy, mapOnVars_attrChainExpr u hv] at h
    rw [typeOf] at h
    cases hY : typeOf (attrChainExpr v p) c env with
    | error e => rw [hY] at h; cases h
    | ok r =>
      obtain ⟨ty₁, c₁⟩ := r
      rw [hY] at h
      simp only [Except.bind_ok] at h
      cases he : Cedar.Validation.typeOfExtHasAttr ty₁ (attrChainExpr v p) (a :: bs) c env with
      | error e => rw [he] at h; cases h
      | ok r =>
        obtain ⟨bty, c'⟩ := r
        rw [he] at h
        simp only [Except.bind_ok, Cedar.Validation.ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hbty : bty ≠ .ff := by
          intro hff
          subst hff
          exact hne rfl
        exact caps_of_extHas bs
          (fun c' t' ct' h' => typeOf_chain_det (isChain_attrChainExpr v p) h' hY) he hbty q hq
  | .and a b, k, c, t, ct, h, hne => by
    simp only [Expr.lowerFrom, mapOnVars] at h
    obtain ⟨ta, ca, tb, cb, ha, hna, hb, hnb, rfl⟩ := typeOf_and_caps h hne
    have iha := caps_of_facts u a k ha hna
    have ihb := caps_of_facts u b _ hb hnb
    intro g hg
    simp only [Expr.facts, List.mem_append] at hg
    rcases hg with hg | hg
    · exact (iha.mono fun k hk => by
        simp only [List.mem_union_iff] at hk ⊢; rcases hk with hk | hk <;> simp [hk]) g hg
    · exact (ihb.mono fun k hk => by
        simp only [List.mem_union_iff] at hk ⊢
        rcases hk with (hk | hk) | hk <;> simp [hk]) g hg
  | .lit _, _, _, _, _, _, _ | .var _, _, _, _, _, _, _ | .ite .., _, _, _, _, _, _
  | .or .., _, _, _, _, _, _ | .unaryApp .., _, _, _, _, _, _ | .binaryApp .., _, _, _, _, _, _
  | .getAttr .., _, _, _, _, _, _ | .set .., _, _, _, _, _, _ | .record .., _, _, _, _, _, _
  | .call .., _, _, _, _, _, _ | .temporal _, _, _, _, _, _, _
  | .provider _, _, _, _, _, _, _ => by
    intro g hg
    simp [Expr.facts] at hg

end

/-! ## Assembling: the lowered rule's typing -/

section

open Cedar.Validation (mapOnVars typeOfGetAttr typeOfUnaryApp)

variable {env : TypeEnv}

/-- **Reading a context attribute in a well-formed environment types as a lifted type**, never
`False`, and earns no capability. -/
theorem typeOf_ctxAttr (hwf : env.WellFormed) {n : Attr} {c : Capabilities} {tx : TypedExpr}
    {cx : Capabilities} (h : typeOf (.getAttr (.var .context) n) c env = .ok (tx, cx)) :
    Cedar.Validation.CedarType.IsLifted tx.typeOf ∧ cx = ∅ := by
  obtain ⟨-, ⟨-, hacts, -⟩, entry, hentry, -, -, hctx⟩ := hwf
  have hlift := (hacts _ _ hentry).2.2.2.2.2.2.2
  rw [← hctx] at hlift
  have hv : typeOf (.var .context) c env =
      .ok (.var .context (.record env.reqty.context), ∅) := by
    simp [typeOf, Cedar.Validation.typeOfVar, Cedar.Validation.ok]
  rw [typeOf, hv] at h
  simp only [Except.bind_ok] at h
  unfold typeOfGetAttr at h
  simp only [TypedExpr.typeOf] at h
  cases hg : Cedar.Validation.getAttrInRecord (.record env.reqty.context) env.reqty.context
      (.var .context) n c with
  | error e => rw [hg] at h; cases h
  | ok r =>
    obtain ⟨ty, cg⟩ := r
    rw [hg] at h
    simp only [Except.bind_ok, Cedar.Validation.ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    unfold Cedar.Validation.getAttrInRecord at hg
    split at hg
    · rename_i aty haty
      simp only [Cedar.Validation.ok, Except.ok.injEq, Prod.mk.injEq] at hg
      obtain ⟨rfl, rfl⟩ := hg
      cases hlift with
      | record_lifted h₂ =>
        have := h₂ n _ (Cedar.Data.Map.find?_mem_toList haty)
        cases this with
        | required_lifted h => exact ⟨h, rfl⟩
    · rename_i aty haty
      split at hg
      · simp only [Cedar.Validation.ok, Except.ok.injEq, Prod.mk.injEq] at hg
        obtain ⟨rfl, rfl⟩ := hg
        cases hlift with
        | record_lifted h₂ =>
          have := h₂ n _ (Cedar.Data.Map.find?_mem_toList haty)
          cases this with
          | optional_lifted h => exact ⟨h, rfl⟩
      · cases hg
    · cases hg

theorem lifted_ne_ff {ty : CedarType} (h : Cedar.Validation.CedarType.IsLifted ty) :
    ty ≠ .bool .ff := by
  rintro rfl
  cases h

/-- The condition `context.n`, or `unless { context.n }`, never types as `False` in a well-formed
environment, and earns no capability. -/
theorem typeOf_ctxCond (hwf : env.WellFormed) (k : Cedar.Spec.ConditionKind) (n : Attr) :
    ∀ c tx cx, typeOf (Cedar.Spec.Condition.toExpr ⟨k, .getAttr (.var .context) n⟩) c env =
      .ok (tx, cx) → tx.typeOf ≠ .bool .ff ∧ cx = ∅ := by
  intro c tx cx h
  cases k
  · obtain ⟨hl, hc⟩ := typeOf_ctxAttr hwf h
    exact ⟨lifted_ne_ff hl, hc⟩
  · simp only [Cedar.Spec.Condition.toExpr] at h
    rw [typeOf] at h
    cases ha : typeOf (.getAttr (.var .context) n) c env with
    | error e => rw [ha] at h; cases h
    | ok r =>
      obtain ⟨ta, ca⟩ := r
      rw [ha] at h
      simp only [Except.bind_ok] at h
      obtain ⟨hl, -⟩ := typeOf_ctxAttr hwf ha
      unfold typeOfUnaryApp at h
      split at h
      · rename_i b hb
        simp only [Cedar.Validation.ok, Function.comp, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [hb] at hl
        cases hl
        exact ⟨by simp [TypedExpr.typeOf, Cedar.Validation.BoolType.not], rfl⟩
      all_goals simp_all [Cedar.Validation.err]

/-- A chain Cedar types as other than `False` reaches its end. -/
theorem reaches_of_andChain : (xs : List Cedar.Spec.Expr) → {z : Cedar.Spec.Expr} →
    {c : Capabilities} → {t : TypedExpr} → {ct : Capabilities} →
    typeOf (andChain xs z) c env = .ok (t, ct) → t.typeOf ≠ .bool .ff →
    ∃ ca, Reaches env xs c ca
  | [], _, c, _, _, _, _ => ⟨c, .nil⟩
  | x :: xs, z, c, t, ct, h, hne => by
    obtain ⟨tx, cx, ty, cy, hx, hnx, hy, hny, -⟩ := typeOf_and_caps h hne
    obtain ⟨ca, hr⟩ := reaches_of_andChain xs hy hny
    exact ⟨ca, .cons hx hnx hr⟩

/-- Capabilities only accumulate along a chain. -/
theorem Reaches.sub : {xs : List Cedar.Spec.Expr} → {c ca : Capabilities} →
    Reaches env xs c ca → ∀ k ∈ c, k ∈ ca
  | [], _, _, .nil => fun _ hk => hk
  | _ :: _, _, _, .cons _ _ hr => fun k hk => hr.sub k (by simp [hk])

/-- **Each conjunct before the end of a chain types as a `Bool` other than `False`, with
capabilities the end has.** -/
theorem Reaches.mem : {xs : List Cedar.Spec.Expr} → {c ca : Capabilities} →
    Reaches env xs c ca → ∀ x ∈ xs, ∃ c₁ tx cx, typeOf x c₁ env = .ok (tx, cx) ∧
      tx.typeOf ≠ .bool .ff ∧ ∀ k ∈ c₁ ∪ cx, k ∈ ca
  | [], _, _, .nil => fun _ hx => by cases hx
  | x :: xs, c, ca, .cons (tx := tx) (cx := cx) hx hne hr => fun y hy => by
    rcases List.mem_cons.mp hy with rfl | hy
    · exact ⟨c, tx, cx, hx, hne, hr.sub⟩
    · exact hr.mem y hy

end

section

open Cedar.Validation (typecheckPolicy typecheckPolicyWithEnvironments checkEntities Schema
  ValidationError allFalse)

theorem forall₂_mem_right {α β : Type} {R : α → β → Prop} :
    {xs : List α} → {ys : List β} → List.Forall₂ R xs ys → {y : β} → y ∈ ys → ∃ x ∈ xs, R x y
  | [], [], .nil, _, hy => by cases hy
  | _ :: _, _ :: _, .cons hxy hr, y, hy => by
    rcases List.mem_cons.mp hy with rfl | hy
    · exact ⟨_, List.mem_cons_self .., hxy⟩
    · obtain ⟨x, hx, h⟩ := forall₂_mem_right hr hy
      exact ⟨x, List.mem_cons_of_mem _ hx, h⟩

/-- What Cedar's validation of a policy against a schema gives: its entity literals are declared,
it is typed in every environment of the schema, and in one, as other than `False`. -/
theorem typecheckPolicyWithEnvironments_inv {L : Cedar.Spec.Policy} {S : Schema}
    (h : typecheckPolicyWithEnvironments typecheckPolicy L S = .ok ()) :
    checkEntities S L.toExpr = .ok () ∧
      (∀ env ∈ S.environments, ∃ tx, typecheckPolicy L env = .ok tx) ∧
      ∃ env ∈ S.environments, ∃ tx, typecheckPolicy L env = .ok tx ∧ tx.typeOf ≠ .bool .ff := by
  unfold typecheckPolicyWithEnvironments at h
  cases hc : checkEntities S L.toExpr with
  | error e => simp [hc, Except.mapError] at h
  | ok u =>
    simp only [hc, Except.mapError] at h
    simp only [Except.bind_ok] at h
    cases hm : S.environments.mapM (typecheckPolicy L) with
    | error e => rw [hm] at h; cases h
    | ok tys =>
      rw [hm] at h
      simp only [Except.bind_ok] at h
      have h₂ := List.mapM_ok_iff_forall₂.mp hm
      refine ⟨rfl, fun env henv => ?_, ?_⟩
      · obtain ⟨y, -, hy⟩ := List.mapM_ok_implies_all_ok hm env henv
        exact ⟨y, hy⟩
      · split at h
        · cases h
        · rename_i hnf
          simp only [allFalse, List.all_eq_true] at hnf
          obtain ⟨tx, hne⟩ := Classical.not_forall.mp hnf
          obtain ⟨htx, hne⟩ := Classical.not_imp.mp hne
          obtain ⟨env, henv, hy⟩ := forall₂_mem_right h₂ htx
          exact ⟨env, henv, tx, hy, by simpa using hne⟩

/-- **Cedar's validation of a policy typed in every environment** succeeds, or reports it
impossible. -/
theorem typecheckPolicyWithEnvironments_of {O : Cedar.Spec.Policy} {S : Schema}
    (hc : checkEntities S O.toExpr = .ok ())
    (hall : ∀ env ∈ S.environments, ∃ tx, typecheckPolicy O env = .ok tx) :
    typecheckPolicyWithEnvironments typecheckPolicy O S = .ok () ∨
      typecheckPolicyWithEnvironments typecheckPolicy O S = .error (.impossiblePolicy O.id) := by
  obtain ⟨tys, htys⟩ := List.all_ok_implies_mapM'_ok (f := typecheckPolicy O) hall
  rw [List.mapM'_eq_mapM] at htys
  unfold typecheckPolicyWithEnvironments
  simp only [hc, Except.mapError, Except.bind_ok, htys]
  split
  · exact .inr rfl
  · exact .inl rfl

theorem validate_mem {ps : Cedar.Spec.Policies} {S : Schema}
    (h : Cedar.Validation.validate ps S = .ok ()) {L : Cedar.Spec.Policy} (hL : L ∈ ps) :
    typecheckPolicyWithEnvironments typecheckPolicy L S = .ok () :=
  List.forM_ok_implies_all_ok _ _ h L hL

end

section

open Cedar.Validation (checkEntities Schema)

variable {S : Schema}

theorem checkEntities_and {x y : Cedar.Spec.Expr} :
    checkEntities S (.and x y) = .ok () ↔
      checkEntities S x = .ok () ∧ checkEntities S y = .ok () := by
  rw [checkEntities]
  cases hx : checkEntities S x with
  | error e => simp
  | ok u => cases u; simp

theorem checkEntities_andChain : (xs : List Cedar.Spec.Expr) → (z : Cedar.Spec.Expr) →
    (checkEntities S (andChain xs z) = .ok () ↔
      (∀ x ∈ xs, checkEntities S x = .ok ()) ∧ checkEntities S z = .ok ())
  | [], z => by simp [andChain]
  | x :: xs, z => by
    simp only [andChain, checkEntities_and, checkEntities_andChain xs z, List.mem_cons,
      forall_eq_or_imp]
    exact and_assoc.symm

theorem checkEntities_condTail {c c' : Cedar.Spec.Condition} {post : Cedar.Spec.Conditions}
    (hc : checkEntities S c.toExpr = .ok () → checkEntities S c'.toExpr = .ok ())
    (h : checkEntities S (condTail c post) = .ok ()) :
    checkEntities S (condTail c' post) = .ok () := by
  cases post with
  | nil => exact hc h
  | cons d ds =>
    simp only [condTail, checkEntities_and] at h ⊢
    exact ⟨hc h.1, h.2⟩

/-- **A typed translation's entity literals are declared.** -/
theorem checkEntities_toTerm {C : TypingCtx} (hets : S.ets = C.env.ets)
    (hacts : ∀ uid, S.acts.contains uid = C.env.acts.contains uid) :
    (x : Cedar.Spec.Expr) → (t : Term) → toTerm x = some t → {τ : TType} →
      Term.Typed C [] t τ → checkEntities S x = .ok ()
  | .lit p, t, ht, τ, hty => by
    cases p <;> simp only [toTerm, Option.some.injEq] at ht <;> subst ht <;>
      simp only [checkEntities]
    cases hty with
    | entity hv => simp [hets, hacts, hv]
  | .var _, _, _, _, _ => by simp [checkEntities]
  | .call xfn xs, t, ht, τ, hty => by
    obtain ⟨s, rfl, rfl, rfl⟩ := toTerm_call ht
    simp [checkEntities, List.forM, List.attach]
  | .getAttr x a, t, ht, τ, hty => by
    have hx : ∀ {v : Var} {p : Path}, x = attrChainExpr v p → checkEntities S x = .ok () := by
      intro v p hx
      subst hx
      have : ∀ (q : Path) (y : Cedar.Spec.Expr), checkEntities S y = .ok () →
          checkEntities S (q.foldl (fun x a => Cedar.Spec.Expr.getAttr x a) y) = .ok () := by
        intro q
        induction q with
        | nil => intro y hy; exact hy
        | cons b q ih => intro y hy; exact ih _ (by simp [checkEntities, hy])
      rw [attrChainExpr_eq_foldl]
      exact this p _ (by simp [checkEntities])
    simp only [checkEntities]
    cases hcx : ctxPath x with
    | some p => exact hx (ctxPath_attrChain x p hcx)
    | none =>
      cases hsx : scopePath x with
      | none => simp [toTerm, attrTerm, hcx, hsx] at ht
      | some rp => exact hx (scopePath_attrChain x rp.1 rp.2 hsx)
  | .binaryApp .add x y, t, ht, τ, hty | .binaryApp .sub x y, t, ht, τ, hty
  | .binaryApp .mul x y, t, ht, τ, hty => by
    simp only [toTerm, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at ht
    obtain ⟨tx, htx, ty, hty', rfl⟩ := ht
    cases hty with
    | arith hl hr =>
      simp only [checkEntities, checkEntities_toTerm hets hacts x tx htx hl,
        checkEntities_toTerm hets hacts y ty hty' hr, Except.bind_ok]
  | .ite .., _, ht, _, _ | .and .., _, ht, _, _ | .or .., _, ht, _, _
  | .unaryApp .., _, ht, _, _ | .binaryApp .eq .., _, ht, _, _
  | .binaryApp .mem .., _, ht, _, _ | .binaryApp .hasTag .., _, ht, _, _
  | .binaryApp .getTag .., _, ht, _, _ | .binaryApp .less .., _, ht, _, _
  | .binaryApp .lessEq .., _, ht, _, _ | .binaryApp .contains .., _, ht, _, _
  | .binaryApp .containsAll .., _, ht, _, _ | .binaryApp .containsAny .., _, ht, _, _
  | .hasAttr .., _, ht, _, _ | .extHasAttr .., _, ht, _, _ | .set .., _, ht, _, _
  | .record .., _, ht, _, _ => by simp [toTerm] at ht

theorem checkEntities_toTemporal {C : TypingCtx} (hets : S.ets = C.env.ets)
    (hacts : ∀ uid, S.acts.contains uid = C.env.acts.contains uid) :
    (e : Cedar.Spec.Expr) → (φ : Formula) → toTemporal e = some φ → φ.WellTyped C [] →
      checkEntities S e = .ok ()
  | .binaryApp .eq x y, φ, hφ, hwt | .binaryApp .less x y, φ, hφ, hwt
  | .binaryApp .lessEq x y, φ, hφ, hwt => by
    simp only [toTemporal, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hφ
    obtain ⟨tx, htx, ty, hty, rfl⟩ := hφ
    have h : ∀ {op : BinaryOp} {τ₁ τ₂}, Term.Typed C [] tx τ₁ → Term.Typed C [] ty τ₂ →
        checkEntities S (.binaryApp op x y) = .ok () := fun hx hy => by
      simp only [checkEntities, checkEntities_toTerm hets hacts x tx htx hx,
        checkEntities_toTerm hets hacts y ty hty hy, Except.bind_ok]
    cases hwt with
    | eq _ hx hy _ => exact h hx hy
    | ord _ hx hy => exact h hx hy
  | .and x y, φ, hφ, hwt => by
    simp only [toTemporal, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hφ
    obtain ⟨φx, hφx, φy, hφy, rfl⟩ := hφ
    cases hwt with
    | and hx hy =>
      simp only [checkEntities, checkEntities_toTemporal hets hacts x φx hφx hx,
        checkEntities_toTemporal hets hacts y φy hφy hy, Except.bind_ok]
  | .or x y, φ, hφ, hwt => by
    simp only [toTemporal, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hφ
    obtain ⟨φx, hφx, φy, hφy, rfl⟩ := hφ
    cases hwt with
    | not h' =>
      cases h' with
      | and hx hy =>
        cases hx with
        | not hx =>
          cases hy with
          | not hy =>
            simp only [checkEntities, checkEntities_toTemporal hets hacts x φx hφx hx,
              checkEntities_toTemporal hets hacts y φy hφy hy, Except.bind_ok]
  | .unaryApp .not x, φ, hφ, hwt => by
    simp only [toTemporal, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hφ
    obtain ⟨φx, hφx, rfl⟩ := hφ
    cases hwt with
    | not hx => simp only [checkEntities, checkEntities_toTemporal hets hacts x φx hφx hx]
  | .lit _, _, hφ, _ | .var _, _, hφ, _ | .ite .., _, hφ, _
  | .unaryApp .neg _, _, hφ, _ | .unaryApp .isEmpty _, _, hφ, _
  | .unaryApp (.like _) _, _, hφ, _ | .unaryApp (.is _) _, _, hφ, _
  | .binaryApp .mem .., _, hφ, _ | .binaryApp .hasTag .., _, hφ, _
  | .binaryApp .getTag .., _, hφ, _ | .binaryApp .add .., _, hφ, _
  | .binaryApp .sub .., _, hφ, _ | .binaryApp .mul .., _, hφ, _
  | .binaryApp .contains .., _, hφ, _ | .binaryApp .containsAll .., _, hφ, _
  | .binaryApp .containsAny .., _, hφ, _ | .getAttr .., _, hφ, _
  | .hasAttr .., _, hφ, _ | .extHasAttr .., _, hφ, _ | .set .., _, hφ, _
  | .record .., _, hφ, _ | .call .., _, hφ, _ => by simp [toTemporal] at hφ

end

section

open Cedar.Validation (Schema QualifiedType)

theorem conditions_lowerFrom_append (c : Condition) (post : Conditions) :
    (pre : Conditions) → (k : Nat) →
      (Conditions.lowerFrom k (pre ++ c :: post)).1 =
        (Conditions.lowerFrom k pre).1 ++
          ⟨c.kind, (c.body.lowerFrom (Conditions.lowerFrom k pre).2).1⟩ ::
          (Conditions.lowerFrom (c.body.lowerFrom (Conditions.lowerFrom k pre).2).2 post).1
  | [], k => rfl
  | d :: pre, k => by
    simp only [List.cons_append, Conditions.lowerFrom]
    rw [conditions_lowerFrom_append c post pre]

theorem conditions_lowerFrom_forall₂ : (cs : Conditions) → (k : Nat) →
    List.Forall₂ (fun d (dL : Cedar.Spec.Condition) =>
      dL.kind = d.kind ∧ ∃ j, dL.body = (d.body.lowerFrom j).1) cs (Conditions.lowerFrom k cs).1
  | [], _ => .nil
  | _ :: cs, _ => .cons ⟨rfl, _, rfl⟩ (conditions_lowerFrom_forall₂ cs _)

theorem forall₂_mem_left {α β : Type} {R : α → β → Prop} :
    {xs : List α} → {ys : List β} → List.Forall₂ R xs ys → {x : α} → x ∈ xs → ∃ y ∈ ys, R x y
  | [], [], .nil, _, hx => by cases hx
  | _ :: _, _ :: _, .cons hxy hr, x, hx => by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨_, List.mem_cons_self .., hxy⟩
    · obtain ⟨y, hy, h⟩ := forall₂_mem_left hr hx
      exact ⟨y, List.mem_cons_of_mem _ hy, h⟩

/-- A rule's scope establishes no fact: its constraints test no attribute. -/
theorem scopeFacts_eq_nil (q : Policy) : scopeFacts q = [] := by
  have hs : ∀ (s : Cedar.Spec.Scope) (v : Var), (Expr.ofCedar (s.toExpr v)).facts = [] := by
    intro s v
    cases s <;> simp [Cedar.Spec.Scope.toExpr, Cedar.Spec.Var.eqEntityUID,
      Cedar.Spec.Var.inEntityUID, Cedar.Spec.Var.isEntityType, Expr.ofCedar, Expr.facts]
  obtain ⟨ps⟩ := q.principalScope
  unfold scopeFacts
  cases q.principalScope with
  | principalScope ps =>
    cases q.resourceScope with
    | resourceScope rs =>
      cases q.actionScope with
      | actionScope s =>
        simp [Cedar.Spec.PrincipalScope.toExpr, Cedar.Spec.ResourceScope.toExpr,
          Cedar.Spec.ActionScope.toExpr, hs]
      | actionInAny ls =>
        simp [Cedar.Spec.PrincipalScope.toExpr, Cedar.Spec.ResourceScope.toExpr,
          Cedar.Spec.ActionScope.toExpr, hs, Expr.ofCedar, Expr.facts]

/-- **Every environment of the augmented schema augments one of the schema.** -/
theorem mem_augment_environments {A : Schema} {H : List (Attr × QualifiedType)} {env : TypeEnv}
    (h : env ∈ (Schema.augment A H).environments) :
    ∃ env₀ ∈ A.environments, env = augmentEnv A H env₀ := by
  obtain ⟨a, entry', p, r, hmem, hp, hr, rfl⟩ := mem_environments.mp h
  rw [augment_acts] at hmem
  change (a, entry') ∈ A.acts.toList.map (fun x => (x.1, augmentEntry H x.2)) at hmem
  obtain ⟨⟨a', entry⟩, hmem', heq⟩ := List.mem_map.mp hmem
  simp only [Prod.mk.injEq] at heq
  obtain ⟨rfl, rfl⟩ := heq
  refine ⟨_, mem_environments.mpr ⟨a', entry, p, r, hmem', hp, hr, rfl⟩, rfl⟩

end

/-! ## For a valid policy set -/

section

open Cedar.Validation (typecheckPolicy typecheckPolicyWithEnvironments checkEntities Schema
  mapOnVars substituteAction)

theorem typecheckPolicy_inv {L : Cedar.Spec.Policy} {env : TypeEnv} {tx : TypedExpr}
    (h : typecheckPolicy L env = .ok tx) :
    ∃ c', typeOf (substituteAction env.reqty.action L.toExpr) ∅ env = .ok (tx, c') := by
  unfold typecheckPolicy at h
  dsimp only at h
  split at h
  · rename_i tx' c' hty
    split at h
    · cases h; exact ⟨c', hty⟩
    · cases h
  · cases h

/-- **The Cedar version of a lowered rule with a leaf**: the leaf's condition `context.n` put back
as the Cedar expression `e` it translates. -/
def cedarVersion (q : Policy) (pre post : Conditions) (k : Cedar.Spec.ConditionKind)
    (e : Cedar.Spec.Expr) (j : Nat) : Cedar.Spec.Policy :=
  let L := (Policy.lowerFrom j q).1
  let jp := (Conditions.lowerFrom j pre).2
  { L with condition := (Conditions.lowerFrom j pre).1 ++ ⟨k, e⟩ ::
      (Conditions.lowerFrom (jp + 1) post).1 }

/-- **Dogwood's validity of a rule with a leaf gives Cedar's of its Cedar version, but for the
impossible-policy check.** For a valid policy set, a rule whose condition is a temporal leaf, the
translation of a Cedar expression `e`, and the rule's lowering: with the leaf's hoisted attribute
read replaced by `e`, Cedar's validation of the policy against the schema augmented at every
action (`PolicySet.allAugmentedSchema`) succeeds, or reports the policy impossible (typed `False` in every environment). It never reports a type error
or an undeclared entity. -/
theorem validate_cedarVersion {P : PolicySet} (hv : P.Valid) {qs₁ qs₂ : Policies} {q : Policy}
    {pre post : Conditions} {k : Cedar.Spec.ConditionKind} {e : Cedar.Spec.Expr} {φ : Formula}
    (hφ : toTemporal e = some φ)
    (hps : P.policies = qs₁ ++ q.withCondition pre ⟨k, .temporal φ⟩ post :: qs₂) :
    ∃ j, (Policy.lowerFrom j (q.withCondition pre ⟨k, .temporal φ⟩ post)).1 ∈ P.lowered ∧
      (typecheckPolicyWithEnvironments typecheckPolicy
          (cedarVersion (q.withCondition pre ⟨k, .temporal φ⟩ post) pre post k e j)
          P.allAugmentedSchema = .ok () ∨
        typecheckPolicyWithEnvironments typecheckPolicy
          (cedarVersion (q.withCondition pre ⟨k, .temporal φ⟩ post) pre post k e j)
          P.allAugmentedSchema = .error (.impossiblePolicy
            (cedarVersion (q.withCondition pre ⟨k, .temporal φ⟩ post) pre post k e j).id)) := by
  have hq'mem : q.withCondition pre ⟨k, .temporal φ⟩ post ∈ P.policies := by rw [hps]; simp
  obtain ⟨j, hmem, -⟩ := lowered_of_mem P.policies 0 _ hq'mem
  refine ⟨j, hmem, ?_⟩
  obtain ⟨L, hLdef⟩ : ∃ L, L = (Policy.lowerFrom j (q.withCondition pre ⟨k, .temporal φ⟩ post)).1 :=
    ⟨_, rfl⟩
  obtain ⟨jp, hjp⟩ : ∃ jp, jp = (Conditions.lowerFrom j pre).2 := ⟨_, rfl⟩
  obtain ⟨preL, hpreL⟩ : ∃ preL, preL = (Conditions.lowerFrom j pre).1 := ⟨_, rfl⟩
  obtain ⟨postL, hpostL⟩ : ∃ postL, postL = (Conditions.lowerFrom (jp + 1) post).1 := ⟨_, rfl⟩
  -- The lowered rule's conditions: the leaf's is `context.n`.
  have hLc : L.condition = preL ++ ⟨k, .getAttr (.var .context) (leafAttr jp)⟩ :: postL := by
    rw [hLdef, hpreL, hpostL, hjp]
    simp only [Policy.lowerFrom, Policy.withCondition]
    rw [conditions_lowerFrom_append]
    rfl
  have hO : cedarVersion (q.withCondition pre ⟨k, .temporal φ⟩ post) pre post k e j =
      { L with condition := preL ++ ⟨k, e⟩ :: postL } := by
    rw [hLdef, hpreL, hpostL, hjp]
    rfl
  rw [hO]
  rw [← hLdef] at hmem
  obtain ⟨hce, hall, envW, henvW, txW, htxW, hneW⟩ :=
    typecheckPolicyWithEnvironments_inv (validate_mem hv.toAll.cedar hmem)
  have hA := augmentedSchema_eq hv
  -- In an environment where Cedar's typing passes the scope, the leaf is well-typed.
  have hleaf : ∀ env ∈ P.allAugmentedSchema.environments, ∀ cb,
      Reaches env ([L.principalScope.toExpr, L.actionScope.toExpr, L.resourceScope.toExpr].map
        (mapOnVars (actionSubst env.reqty.action))) ∅ cb →
      ∃ env₀ ∈ P.actionSchema.environments, env = augmentEnv P.actionSchema P.leafTypes env₀ ∧
        env₀ ∈ P.envsOf (q.withCondition pre ⟨k, .temporal φ⟩ post) := by
    intro env henv cb hr
    rw [hA] at henv
    obtain ⟨env₀, henv₀, rfl⟩ := mem_augment_environments henv
    refine ⟨env₀, henv₀, rfl, List.mem_filter.mpr ⟨henv₀, ?_⟩⟩
    have hsc : L.principalScope = q.principalScope ∧ L.actionScope = q.actionScope ∧
        L.resourceScope = q.resourceScope := by
      rw [hLdef]; exact ⟨rfl, rfl, rfl⟩
    rw [hsc.1, hsc.2.1, hsc.2.2] at hr
    have hadm := admits_of_reaches (A := P.actionSchema)
      (q := q.withCondition pre ⟨k, .temporal φ⟩ post)
      (by rw [show (augmentEnv P.actionSchema P.leafTypes env₀).ets = env₀.ets from rfl,
        environments_ets henv₀])
      augmentEnv_maybeDescendentOf (augmentEnv_descendentOf henv₀)
      (by rw [augmentEnv_contains henv₀, environments_acts henv₀]
          exact environments_action (env := env₀) henv₀) hr
    exact hadm
  -- Where Cedar's typing of the lowered rule reaches the leaf's condition, the Cedar version's
  -- condition is a `Bool` with no capabilities.
  have hcond : ∀ env ∈ P.allAugmentedSchema.environments, ∀ ca,
      Reaches env (([L.principalScope.toExpr, L.actionScope.toExpr, L.resourceScope.toExpr] ++
        preL.map (·.toExpr)).map (mapOnVars (actionSubst env.reqty.action))) ∅ ca →
      ∃ tx b, typeOf (Cedar.Spec.Condition.toExpr ⟨k, e⟩) ca env = .ok (tx, ∅) ∧
        tx.typeOf = .bool b := by
    intro env henv ca hr
    rw [List.map_append] at hr
    obtain ⟨cb, hrs, hrp⟩ := reaches_append _ _ _ _ hr
    obtain ⟨env₀, henv₀, rfl, henvq⟩ := hleaf env henv cb hrs
    obtain ⟨F, hmemF, hF⟩ := mem_leafFacts_withCondition (q := q) (pre := pre) (post := post)
      (k := k) (φ := φ)
    have hwt₀ := (hv.temporal _ hq'mem φ F hmemF).wellTyped env₀ henvq
    have hwt := wellTyped_toTemporal_mono (C := P.typingCtx env₀ F)
      (C' := P.typingCtx (augmentEnv P.actionSchema P.leafTypes env₀) F)
      ⟨rfl, augmentEnv_contains henv₀, rfl, rfl, fun _ _ h => augmentEnv_context_find? h, rfl⟩
      e φ hφ hwt₀
    have hcov : CapsCover (augmentEnv P.actionSchema P.leafTypes env₀) F ca := by
      intro g hg y a hge
      rcases hF g hg with hg' | hg'
      · rw [scopeFacts_eq_nil] at hg'; cases hg'
      · simp only [condFacts, List.mem_flatMap] at hg'
        obtain ⟨d, hd, hgd⟩ := hg'
        obtain ⟨dL, hdL, hkind, j', hbody⟩ :=
          forall₂_mem_left (conditions_lowerFrom_forall₂ pre j) hd
        obtain ⟨dk, db⟩ := d
        cases dk
        · simp only [Condition.toExpr] at hgd
          rw [← hpreL] at hdL
          have hmemx : mapOnVars (actionSubst env₀.reqty.action) (db.lowerFrom j').1 ∈
              (preL.map (·.toExpr)).map (mapOnVars (actionSubst env₀.reqty.action)) := by
            refine List.mem_map.mpr ⟨dL.toExpr, List.mem_map.mpr ⟨dL, hdL, rfl⟩, ?_⟩
            obtain ⟨dLk, dLb⟩ := dL
            simp only at hkind hbody
            subst hkind hbody
            rfl
          obtain ⟨c₁, tx, cx, htyp, hne, hsub⟩ := hrp.mem _ hmemx
          exact ((caps_of_facts _ db j' htyp hne).mono hsub) g hgd y a hge
        · simp [Condition.toExpr, Expr.facts] at hgd
    obtain ⟨te, hte, b, hb⟩ := typeOf_toTemporal
      (C := P.typingCtx (augmentEnv P.actionSchema P.leafTypes env₀) F) e φ hφ hwt ca hcov
    cases k
    · exact ⟨te, b, hte, hb⟩
    · refine ⟨.unaryApp .not te (.bool b.not), b.not, ?_, rfl⟩
      simp only [Cedar.Spec.Condition.toExpr]
      have hte' : typeOf e ca (augmentEnv P.actionSchema P.leafTypes env₀) = .ok (te, ∅) := hte
      rw [typeOf, hte']
      simp [Cedar.Validation.typeOfUnaryApp, hb, Cedar.Validation.ok]
  -- The Cedar version is typed in every environment.
  have hallO : ∀ env ∈ P.allAugmentedSchema.environments,
      ∃ tx, typecheckPolicy { L with condition := preL ++ ⟨k, e⟩ :: postL } env = .ok tx := by
    intro env henv
    obtain ⟨tL, htL⟩ := hall env henv
    have henv' := henv
    rw [hA] at henv'
    obtain ⟨env₀, henv₀, rfl⟩ := mem_augment_environments henv'
    exact typecheckPolicy_replace hLc
      (by simp [substituteAction_eq, mapOnVars, actionSubst])
      (substituteAction_toTemporal hφ) (typeOf_ctxCond (augmented_wf hv henv₀) k (leafAttr jp))
      (hcond _ henv) htL
  -- Its entity literals are declared: the leaf is typed in an environment the rule admits.
  have hceO : checkEntities P.allAugmentedSchema
      ({ L with condition := preL ++ ⟨k, e⟩ :: postL } : Cedar.Spec.Policy).toExpr = .ok () := by
    obtain ⟨cW, hW⟩ := typecheckPolicy_inv htxW
    rw [policy_toExpr_split L hLc, substituteAction_eq, mapOnVars_andChain] at hW
    obtain ⟨caW, hrW⟩ := reaches_of_andChain _ hW hneW
    obtain ⟨cbW, hrsW, -⟩ := reaches_append _ _ _ _ (by rw [← List.map_append]; exact hrW)
    obtain ⟨env₀, henv₀, -, henvq⟩ := hleaf envW henvW cbW hrsW
    obtain ⟨F, hmemF, -⟩ := mem_leafFacts_withCondition (q := q) (pre := pre) (post := post)
      (k := k) (φ := φ)
    have hwt₀ := (hv.temporal _ hq'mem φ F hmemF).wellTyped env₀ henvq
    have hcE := checkEntities_toTemporal (S := P.allAugmentedSchema) (C := P.typingCtx env₀ F)
      (by rw [hA]; show _ = env₀.ets; rw [environments_ets henv₀]; rfl)
      (fun uid => by
        rw [hA]
        exact augmentEnv_contains (H := P.leafTypes) henv₀ uid) e φ hφ hwt₀
    rw [policy_toExpr_split L hLc] at hce
    rw [policy_toExpr_split { L with condition := preL ++ ⟨k, e⟩ :: postL } (pre := preL)
      (post := postL) (c := ⟨k, e⟩) rfl]
    rw [checkEntities_andChain] at hce ⊢
    refine ⟨hce.1, checkEntities_condTail (fun _ => ?_) hce.2⟩
    cases k
    · exact hcE
    · simp only [Cedar.Spec.Condition.toExpr, checkEntities]
      exact hcE
  exact typecheckPolicyWithEnvironments_of hceO hallO

end

end Dogwood.Thm
