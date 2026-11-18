import Dogwood.Thm.Frontend.Cedarify.Lowering

/-!
# Hoisting: what lowering an expression does to the state, and what it produces

Lowering an expression changes the hoisting state only by hoisting leaves, one at a time
(`Hoists`). What it produces is the crate's expression, the specification's form, and the
references, related by `LowersTo`: the crate's expression is the specification's form lowered
with the references, and each reference is the crate's reference to a hoisted field of the
leaf's kind, whose leaf is the specification's when every leaf has a form there (`LeafOK`).
-/

namespace Dogwood.Thm.Frontend.Cedarify

open Dogwood.Spec
open Dogwood.Frontend
open Dogwood.Frontend.Cedarify

/-! ## Hoisting steps -/

/-- The state `s'` follows `s` by hoisting leaves under `env`. -/
inductive Hoists (env : Env) : St → St → Prop
  | refl (s : St) : Hoists env s s
  | temporal (t : Surface.Temporal.Block) {s s' : St} :
      Hoists env (hoistTemporal env t s).2 s' → Hoists env s s'
  | provider (inv : Frontend.Provider.Invocation) (ms : List Frontend.Provider.MethodCall) {s s' : St} :
      Hoists env (hoistProvider env inv ms s).2 s' → Hoists env s s'

theorem Hoists.trans {env : Env} {s₁ s₂ s₃ : St} (h₁ : Hoists env s₁ s₂) (h₂ : Hoists env s₂ s₃) :
    Hoists env s₁ s₃ := by
  induction h₁ with
  | refl => exact h₂
  | temporal t _ ih => exact .temporal t (ih h₂)
  | provider inv ms _ ih => exact .provider inv ms (ih h₂)

theorem Hoists.temporal_one (env : Env) (t : Surface.Temporal.Block) (s : St) :
    Hoists env s (hoistTemporal env t s).2 := .temporal t (.refl _)

theorem Hoists.provider_one (env : Env) (inv : Frontend.Provider.Invocation) (ms : List Frontend.Provider.MethodCall)
    (s : St) : Hoists env s (hoistProvider env inv ms s).2 := .provider inv ms (.refl _)

/-- What a step keeps: the key, the fields hoisted so far (as a prefix), and the leaves without
a form in the specification. -/
structure Grows (s s' : St) : Prop where
  key : s'.key = s.key
  context : s.contextFields <+: s'.contextFields
  providers : s.providerFields <+: s'.providerFields
  specErrors : s.specErrors <+: s'.specErrors
  ordinal : s.ordinal ≤ s'.ordinal

theorem hoistTemporal_snd (env : Env) (t : Surface.Temporal.Block) (s : St) :
    ∃ errs, (hoistTemporal env t s).2 =
      { s with ordinal := s.ordinal + 1,
               contextFields := s.contextFields ++ [{
                 action := env.action, fieldName := temporalName s.key s.ordinal, temporal := t,
                 targetActions := [], principal := env.principal, resource := env.resource }],
               specErrors := errs } ∧ s.specErrors <+: errs := by
  simp only [hoistTemporal]
  split <;> exact ⟨_, rfl, by simp⟩

theorem hoistProvider_snd (env : Env) (inv : Frontend.Provider.Invocation) (ms : List Frontend.Provider.MethodCall)
    (s : St) :
    ∃ errs, (hoistProvider env inv ms s).2 =
      { s with ordinal := s.ordinal + 1,
               providerFields := s.providerFields ++ [{
                 action := env.action, targetActions := [], fieldName := providerName s.key s.ordinal,
                 cedarType := ProviderDecls.cedarTypeOf env.decls env.enumNames inv.key
                   (ms.map (·.name)),
                 bodyBase := 0, invocation := inv, methods := ms, principal := env.principal,
                 resource := env.resource }],
               specErrors := errs } ∧ s.specErrors <+: errs := by
  simp only [hoistProvider]
  split <;> exact ⟨_, rfl, by simp⟩

theorem Hoists.grows {env : Env} {s s' : St} (h : Hoists env s s') : Grows s s' := by
  induction h with
  | refl s => exact ⟨rfl, List.prefix_refl _, List.prefix_refl _, List.prefix_refl _, Nat.le_refl _⟩
  | temporal t _ ih =>
    obtain ⟨errs, he, hp⟩ := hoistTemporal_snd env t _
    rw [he] at ih
    exact ⟨ih.key, (List.prefix_append _ _).trans ih.context, ih.providers, hp.trans ih.specErrors,
      Nat.le_trans (Nat.le_succ _) ih.ordinal⟩
  | provider inv ms _ ih =>
    obtain ⟨errs, he, hp⟩ := hoistProvider_snd env inv ms _
    rw [he] at ih
    exact ⟨ih.key, ih.context, (List.prefix_append _ _).trans ih.providers, hp.trans ih.specErrors,
      Nat.le_trans (Nat.le_succ _) ih.ordinal⟩

/-! ## Leaves and their references -/

/-- The reference `ref` stands, in the state `s`, for the leaf `l`: it is the crate's reference
to a field hoisted for a leaf of that kind, and that field's leaf is `l`, unless some leaf has no
form in the specification. -/
def LeafOK (s : St) : Leaf → Cedar.Spec.Expr → Prop
  | .inl φ, ref => ∃ f ∈ s.contextFields, ref = temporalRef f.fieldName ∧
      (f.temporal.condition.toFormula = .ok φ ∨ s.specErrors ≠ [])
  | .inr c, ref => ∃ f ∈ s.providerFields, ref = providerRef f.fieldName ∧
      (callOf f.invocation f.methods = .ok c ∨ s.specErrors ≠ [])

/-- The fields hoisted, and the leaves without a form in the specification, grow (as prefixes). -/
structure FieldsGrow (s s' : St) : Prop where
  context : s.contextFields <+: s'.contextFields
  providers : s.providerFields <+: s'.providerFields
  specErrors : s.specErrors <+: s'.specErrors

theorem FieldsGrow.refl (s : St) : FieldsGrow s s :=
  ⟨List.prefix_refl _, List.prefix_refl _, List.prefix_refl _⟩

theorem FieldsGrow.trans {s₁ s₂ s₃ : St} (h₁ : FieldsGrow s₁ s₂) (h₂ : FieldsGrow s₂ s₃) :
    FieldsGrow s₁ s₃ :=
  ⟨h₁.context.trans h₂.context, h₁.providers.trans h₂.providers, h₁.specErrors.trans h₂.specErrors⟩

theorem Grows.fields {s s' : St} (g : Grows s s') : FieldsGrow s s' :=
  ⟨g.context, g.providers, g.specErrors⟩

theorem Hoists.fieldsGrow {env : Env} {s s' : St} (h : Hoists env s s') : FieldsGrow s s' :=
  h.grows.fields

theorem FieldsGrow.specErrors_ne {s s' : St} (g : FieldsGrow s s') (h : s.specErrors ≠ []) :
    s'.specErrors ≠ [] := by
  intro he
  obtain ⟨t, ht⟩ := g.specErrors
  rw [he] at ht
  exact h (List.append_eq_nil_iff.mp ht).1

theorem LeafOK.grow {s s' : St} (g : FieldsGrow s s') : ∀ l ref, LeafOK s l ref → LeafOK s' l ref
  | .inl _, _, ⟨f, hf, hr, hφ⟩ => ⟨f, g.context.subset hf, hr, hφ.imp_right g.specErrors_ne⟩
  | .inr _, _, ⟨f, hf, hr, hc⟩ => ⟨f, g.providers.subset hf, hr, hc.imp_right g.specErrors_ne⟩

/-- No reference to a hoisted field is a Boolean literal: Cedar's folding of `&&` and `||`
leaves it alone. -/
theorem leafOK_noBoolRef (s : St) : NoBoolRef (LeafOK s)
  | .inl _, _, ⟨_, _, hr, _⟩, _ => by rw [hr]; simp [temporalRef]
  | .inr _, _, ⟨_, _, hr, _⟩, _ => by rw [hr]; simp [providerRef]

theorem hoistTemporal_lowers (env : Env) (t : Surface.Temporal.Block) (s : St) :
    LowersTo (LeafOK (hoistTemporal env t s).2) (hoistTemporal env t s).1.spec
      (hoistTemporal env t s).1.cedar (hoistTemporal env t s).1.refs := by
  simp only [hoistTemporal]
  split
  · next φ hφ =>
    exact lowersTo_temporal ⟨_, List.mem_append_right _ (List.mem_singleton_self _), rfl, .inl hφ⟩
  · next e he =>
    exact lowersTo_temporal ⟨_, List.mem_append_right _ (List.mem_singleton_self _), rfl,
      .inr (by simp)⟩

theorem hoistProvider_lowers (env : Env) (inv : Frontend.Provider.Invocation) (ms : List Frontend.Provider.MethodCall)
    (s : St) :
    LowersTo (LeafOK (hoistProvider env inv ms s).2) (hoistProvider env inv ms s).1.spec
      (hoistProvider env inv ms s).1.cedar (hoistProvider env inv ms s).1.refs := by
  simp only [hoistProvider]
  split
  · next c hc =>
    exact lowersTo_provider ⟨_, List.mem_append_right _ (List.mem_singleton_self _), rfl, .inl hc⟩
  · next e he =>
    exact lowersTo_provider ⟨_, List.mem_append_right _ (List.mem_singleton_self _), rfl,
      .inr (by simp)⟩

/-! ## Lowering an expression -/

/-- What lowering an expression guarantees: the state grows by hoisting, and the result lowers
to the crate's expression with its references. -/
def Lowers (env : Env) (s : St) (o : Out) (s' : St) : Prop :=
  Hoists env s s' ∧ LowersTo (LeafOK s') o.spec o.cedar o.refs

theorem lowers_of_hoists {env : Env} {s₁ s₂ : St} {o : Out} (h : Hoists env s₁ s₂)
    (hl : LowersTo (LeafOK s₂) o.spec o.cedar o.refs) : Lowers env s₁ o s₂ := ⟨h, hl⟩

mutual

theorem lowerExpr_lowers (env : Env) : (e : Surface.Expr) → (s : St) → (o : Out) → (s' : St) →
    lowerExpr env e s = .ok (o, s') → Lowers env s o s'
  | ⟨k, sp⟩, s, o, s', h => lowerKind_lowers env sp k s o s' h

theorem lowerKind_lowers (env : Env) (sp : Span) : (k : Surface.ExprKind) → (s : St) → (o : Out) →
    (s' : St) → lowerKind env sp k s = .ok (o, s') → Lowers env s o s'
  | .lit l, s, o, s', h => by
    simp only [lowerKind, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨.refl _, lowersTo_lit _⟩
  | .var v, s, o, s', h => by
    simp only [lowerKind, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨.refl _, lowersTo_var _⟩
  | .slot _, s, o, s', h => by
    simp only [lowerKind, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨.refl _, lowersTo_lit _⟩
  | .extension t, s, o, s', h => by
    simp only [lowerKind, Except.ok.injEq] at h
    have ho : o = (hoistTemporal env t s).1 := by rw [h]
    have hs : s' = (hoistTemporal env t s).2 := by rw [h]
    subst ho hs
    exact ⟨Hoists.temporal_one env t s, hoistTemporal_lowers env t s⟩
  | .unaryApp op e, s, o, s', h => by
    simp only [lowerKind] at h
    cases he : lowerExpr env e s with
    | error _ => simp [he, bind, Except.bind] at h
    | ok p =>
      obtain ⟨o₁, s₁⟩ := p
      simp [he, bind, Except.bind, pure, Except.pure] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨hs, hl⟩ := lowerExpr_lowers env e s o₁ s₁ he
      exact ⟨hs, hl.unaryS op⟩
  | .binaryApp op l r, s, o, s', h => by
    simp only [lowerKind] at h
    cases hl : lowerExpr env l s with
    | error _ => simp [hl, bind, Except.bind] at h
    | ok p =>
      obtain ⟨o₁, s₁⟩ := p
      cases hr : lowerExpr env r s₁ with
      | error _ => simp [hl, hr, bind, Except.bind] at h
      | ok q =>
        obtain ⟨o₂, s₂⟩ := q
        simp [hl, hr, bind, Except.bind, pure, Except.pure] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨hs₁, hl₁⟩ := lowerExpr_lowers env l s o₁ s₁ hl
        obtain ⟨hs₂, hl₂⟩ := lowerExpr_lowers env r s₁ o₂ s₂ hr
        exact ⟨hs₁.trans hs₂, (hl₁.mono (LeafOK.grow hs₂.fieldsGrow)).binaryS hl₂ (leafOK_noBoolRef _) op⟩
  | .getAttr e a, s, o, s', h => by
    simp only [lowerKind] at h
    cases he : lowerExpr env e s with
    | error _ => simp [he, bind, Except.bind] at h
    | ok p =>
      obtain ⟨o₁, s₁⟩ := p
      simp [he, bind, Except.bind, pure, Except.pure] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨hs, hl⟩ := lowerExpr_lowers env e s o₁ s₁ he
      exact ⟨hs, hl.getAttr a⟩
  | .hasAttr e attrs, s, o, s', h => by
    simp only [lowerKind] at h
    cases he : lowerExpr env e s with
    | error _ => simp [he, bind, Except.bind] at h
    | ok p =>
      obtain ⟨o₁, s₁⟩ := p
      simp [he, bind, Except.bind, pure, Except.pure] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨hs, hl⟩ := lowerExpr_lowers env e s o₁ s₁ he
      exact ⟨hs, hl.hasPath attrs⟩
  | .like e p, s, o, s', h => by
    simp only [lowerKind] at h
    cases he : lowerExpr env e s with
    | error _ => simp [he, bind, Except.bind] at h
    | ok q =>
      obtain ⟨o₁, s₁⟩ := q
      simp [he, bind, Except.bind, pure, Except.pure] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨hs, hl⟩ := lowerExpr_lowers env e s o₁ s₁ he
      exact ⟨hs, hl.unaryApp _⟩
  | .is e ty none, s, o, s', h => by
    simp only [lowerKind] at h
    cases he : lowerExpr env e s with
    | error _ => simp [he, bind, Except.bind] at h
    | ok q =>
      obtain ⟨o₁, s₁⟩ := q
      simp [he, bind, Except.bind, pure, Except.pure] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨hs, hl⟩ := lowerExpr_lowers env e s o₁ s₁ he
      exact ⟨hs, hl.unaryApp _⟩
  | .is e ty (some x), s, o, s', h => by
    simp only [lowerKind] at h
    cases he : lowerExpr env e s with
    | error _ => simp [he, bind, Except.bind] at h
    | ok p =>
      obtain ⟨o₁, s₁⟩ := p
      cases hx : lowerExpr env x s₁ with
      | error _ => simp [he, hx, bind, Except.bind] at h
      | ok q =>
        obtain ⟨o₂, s₂⟩ := q
        simp [he, hx, bind, Except.bind, pure, Except.pure] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨hs₁, hl₁⟩ := lowerExpr_lowers env e s o₁ s₁ he
        obtain ⟨hs₂, hl₂⟩ := lowerExpr_lowers env x s₁ o₂ s₂ hx
        have hl₁' := hl₁.mono (LeafOK.grow hs₂.fieldsGrow)
        have := (hl₁'.unaryApp (.is ty)).and (hl₁'.binaryApp hl₂ .mem)
        exact ⟨hs₁.trans hs₂, by simpa [List.append_assoc] using this⟩
  | .ite c t e, s, o, s', h => by
    simp only [lowerKind] at h
    cases hc : lowerExpr env c s with
    | error _ => simp [hc, bind, Except.bind] at h
    | ok p =>
      obtain ⟨o₁, s₁⟩ := p
      cases ht : lowerExpr env t s₁ with
      | error _ => simp [hc, ht, bind, Except.bind] at h
      | ok q =>
        obtain ⟨o₂, s₂⟩ := q
        cases he : lowerExpr env e s₂ with
        | error _ => simp [hc, ht, he, bind, Except.bind] at h
        | ok w =>
          obtain ⟨o₃, s₃⟩ := w
          simp [hc, ht, he, bind, Except.bind, pure, Except.pure] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨hs₁, hl₁⟩ := lowerExpr_lowers env c s o₁ s₁ hc
          obtain ⟨hs₂, hl₂⟩ := lowerExpr_lowers env t s₁ o₂ s₂ ht
          obtain ⟨hs₃, hl₃⟩ := lowerExpr_lowers env e s₂ o₃ s₃ he
          exact ⟨(hs₁.trans hs₂).trans hs₃, by
            simpa [List.append_assoc] using (hl₁.mono (LeafOK.grow (hs₂.trans hs₃).fieldsGrow)).ite
              (hl₂.mono (LeafOK.grow hs₃.fieldsGrow)) hl₃⟩
  | .set xs, s, o, s', h => by
    simp only [lowerKind] at h
    cases hx : lowerList env xs s with
    | error _ => simp [hx, bind, Except.bind] at h
    | ok p =>
      obtain ⟨os, s₁⟩ := p
      simp [hx, bind, Except.bind, pure, Except.pure] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨hs, hl⟩ := lowerList_lowers env xs s os s₁ hx
      exact ⟨hs, hl.set⟩
  | .record m, s, o, s', h => by
    simp only [lowerKind] at h
    cases hx : lowerRecord env m s with
    | error _ => simp [hx, bind, Except.bind] at h
    | ok p =>
      obtain ⟨os, s₁⟩ := p
      simp [hx, bind, Except.bind, pure, Except.pure] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨hs, hl⟩ := lowerRecord_lowers env m s os s₁ hx
      exact ⟨hs, hl.record⟩
  | .call name args, s, o, s', h => by
    simp only [lowerKind] at h
    split at h
    · cases hi : toInvocation name args sp with
      | error _ => simp [hi, bind, Except.bind] at h
      | ok inv =>
        simp [hi, bind, Except.bind, pure, Except.pure] at h
        have ho : o = (hoistProvider env inv [] s).1 := by rw [h]
        have hs : s' = (hoistProvider env inv [] s).2 := by rw [h]
        subst ho hs
        exact ⟨Hoists.provider_one env inv [] s, hoistProvider_lowers env inv [] s⟩
    · simp [throw, throwThe, MonadExceptOf.throw] at h
  | .methodCall recv m args, s, o, s', h => by
    simp only [lowerKind] at h
    cases hp : peel ⟨.methodCall recv m args, sp⟩ with
    | error _ => simp [hp, bind, Except.bind] at h
    | ok r =>
      cases r with
      | none => simp [hp, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
      | some r =>
        obtain ⟨accs, inv⟩ := r
        simp only [hp, bind, Except.bind] at h
        split at h
        · simp [throw, throwThe, MonadExceptOf.throw] at h
        · simp [pure, Except.pure] at h
          have ho : o = (hoistProvider env inv (List.filterMap Accessor.method? accs).reverse s).1 := by
            rw [h]
          have hs : s' = (hoistProvider env inv (List.filterMap Accessor.method? accs).reverse s).2 := by
            rw [h]
          subst ho hs
          exact ⟨Hoists.provider_one env inv _ s, hoistProvider_lowers env inv _ s⟩
  | .paramRef _, s, o, s', h => by simp [lowerKind, throw, throwThe, MonadExceptOf.throw] at h

theorem lowerList_lowers (env : Env) : (xs : List Surface.Expr) → (s : St) → (os : List Out) →
    (s' : St) → lowerList env xs s = .ok (os, s') →
    Hoists env s s' ∧ LowersToList (LeafOK s') (os.map (·.spec)) (os.map (·.cedar))
      (os.map (·.refs)).flatten
  | [], s, os, s', h => by
    simp only [lowerList, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨.refl _, lowersToList_nil⟩
  | x :: xs, s, os, s', h => by
    simp only [lowerList] at h
    cases hx : lowerExpr env x s with
    | error _ => simp [hx, bind, Except.bind] at h
    | ok p =>
      obtain ⟨o₁, s₁⟩ := p
      cases hxs : lowerList env xs s₁ with
      | error _ => simp [hx, hxs, bind, Except.bind] at h
      | ok q =>
        obtain ⟨os₂, s₂⟩ := q
        simp [hx, hxs, bind, Except.bind, pure, Except.pure] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨hs₁, hl₁⟩ := lowerExpr_lowers env x s o₁ s₁ hx
        obtain ⟨hs₂, hl₂⟩ := lowerList_lowers env xs s₁ os₂ s₂ hxs
        refine ⟨hs₁.trans hs₂, ?_⟩
        simpa using LowersToList.cons (hl₁.mono (LeafOK.grow hs₂.fieldsGrow)) hl₂

theorem lowerRecord_lowers (env : Env) : (xs : List (String × Surface.Expr)) → (s : St) →
    (os : List (String × Out)) → (s' : St) → lowerRecord env xs s = .ok (os, s') →
    Hoists env s s' ∧ LowersToRecord (LeafOK s') (os.map fun (a, o) => (a, o.spec))
      (os.map fun (a, o) => (a, o.cedar)) (os.map (·.2.refs)).flatten
  | [], s, os, s', h => by
    simp only [lowerRecord, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨.refl _, lowersToRecord_nil⟩
  | (a, x) :: xs, s, os, s', h => by
    simp only [lowerRecord] at h
    cases hx : lowerExpr env x s with
    | error _ => simp [hx, bind, Except.bind] at h
    | ok p =>
      obtain ⟨o₁, s₁⟩ := p
      cases hxs : lowerRecord env xs s₁ with
      | error _ => simp [hx, hxs, bind, Except.bind] at h
      | ok q =>
        obtain ⟨os₂, s₂⟩ := q
        simp [hx, hxs, bind, Except.bind, pure, Except.pure] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨hs₁, hl₁⟩ := lowerExpr_lowers env x s o₁ s₁ hx
        obtain ⟨hs₂, hl₂⟩ := lowerRecord_lowers env xs s₁ os₂ s₂ hxs
        refine ⟨hs₁.trans hs₂, ?_⟩
        simpa using LowersToRecord.cons (a := a) (hl₁.mono (LeafOK.grow hs₂.fieldsGrow)) hl₂

end

end Dogwood.Thm.Frontend.Cedarify
