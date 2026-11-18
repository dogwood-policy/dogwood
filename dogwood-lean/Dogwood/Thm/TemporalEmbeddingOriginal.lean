import Dogwood.Thm.TemporalEmbeddingTyping
import Dogwood.Thm.Conservative

/-!
# The original Cedar policy set

`Dogwood.Thm.validate_cedarVersion` puts a Cedar expression back in place of its leaf in the
lowered rule and checks the result against the schema augmented at every action
(`PolicySet.allAugmentedSchema`, which validates as `PolicySet.augmentedSchema` does,
`Dogwood.Thm.valid_iff_validAll`); "the augmented schema" below means that one. This module states the result
about the Cedar policy set the Dogwood one came from (`validate_original`): let a valid policy set
have the leaf `temporal { φ }`, the translation of the Cedar expression `e`; let `ps` be Cedar
policies that read as the policy set with `e` in the leaf's place (so the leaf is the only one).
Cedar's validation of `ps` against the action schema succeeds, or reports the leaf's rule
impossible.

The step from the augmented schema to the action schema is that Cedar's typing does not see a
context attribute an expression does not read (`typeOf_agree`): in two environments that differ
only there (`EnvAgree`), Cedar types an expression that reads the context only through other
attributes to the same type and capabilities, or fails in both. The errors themselves may differ,
since some name the context's record type. Dogwood's validity has every rule read the context only
outside the hoisted attributes (`PolicySet.Valid.readsContext`); the translated expression reads
only declared context attributes, so none hoisted, wherever Cedar's typing reaches it
(`readsContext_toTemporal`); so validation against the augmented schema transfers
(`typecheckPolicyWithEnvironments_unaugment`).
-/

namespace Dogwood.Thm

open Dogwood.Spec Dogwood.Spec.Temporal
open Cedar.Spec (Prim Var BinaryOp UnaryOp Attr EntityUID)
open Cedar.Validation (TypeEnv RecordType CedarType Capabilities Key typeOf TypedExpr
  ResultType)

/-! ## Typing without an unread context attribute -/

section

open Cedar.Validation (typeOfIf typeOfAnd typeOfOr typeOfUnaryApp typeOfBinaryApp typeOfHasAttr
  typeOfGetAttr typeOfExtHasAttr typeOfSet typeOfCall hasAttrInRecord getAttrInRecord typeOfEq
  typeOfInₑ typeOfInₛ typeOfHasTag typeOfGetTag ifLubThenBool typeOfLit typeOfVar)

/-- What Cedar's typing of an expression shows: its type and capabilities, or that it fails. -/
def sig : ResultType → Option (CedarType × Capabilities)
  | .ok (t, c) => some (t.typeOf, c)
  | .error _ => none

theorem sig_cases {r r' : ResultType} (h : sig r' = sig r) :
    (∃ e e', r = .error e ∧ r' = .error e') ∨
      ∃ t t' c, r = .ok (t, c) ∧ r' = .ok (t', c) ∧ t'.typeOf = t.typeOf := by
  cases r with
  | error e =>
    cases r' with
    | error e' => exact .inl ⟨e, e', rfl, rfl⟩
    | ok p => obtain ⟨_, _⟩ := p; simp [sig] at h
  | ok p =>
    obtain ⟨t, c⟩ := p
    cases r' with
    | error e' => simp [sig] at h
    | ok p' =>
      obtain ⟨t', c'⟩ := p'
      simp only [sig, Option.some.injEq, Prod.mk.injEq] at h
      exact .inr ⟨t, t', c, rfl, by rw [h.2], h.1⟩

theorem sig_bind {r r' : ResultType} {f f' : TypedExpr × Capabilities → ResultType}
    (h : sig r' = sig r)
    (hf : ∀ t t' c, r = .ok (t, c) → t'.typeOf = t.typeOf → sig (f' (t', c)) = sig (f (t, c))) :
    sig (r' >>= f') = sig (r >>= f) := by
  rcases sig_cases h with ⟨e, e', rfl, rfl⟩ | ⟨t, t', c, rfl, rfl, ht⟩
  · rfl
  · exact hf t t' c rfl ht

/-- The environments differ at most in their context record types, outside the attributes `N`,
and in what their actions schemas say beyond the actions, their types, and their ancestors. -/
structure EnvAgree (N : List Attr) (env env' : TypeEnv) : Prop where
  ets : env'.ets = env.ets
  principal : env'.reqty.principal = env.reqty.principal
  action : env'.reqty.action = env.reqty.action
  resource : env'.reqty.resource = env.reqty.resource
  contains : ∀ u, env'.acts.contains u = env.acts.contains u
  descendentOf : ∀ u v, env'.acts.descendentOf u v = env.acts.descendentOf u v
  actionType : ∀ ety, env'.acts.actionType? ety = env.acts.actionType? ety
  envDescendentOf : ∀ e₁ e₂, env'.descendentOf e₁ e₂ = env.descendentOf e₁ e₂
  context : ∀ a, a ∉ N → env'.reqty.context.find? a = env.reqty.context.find? a

variable {N : List Attr} {env env' : TypeEnv}

theorem sig_typeOfIf {t t' : TypedExpr} {c₁ : Capabilities} {r₂ r₂' r₃ r₃' : ResultType}
    (ht : t'.typeOf = t.typeOf) (h₂ : sig r₂' = sig r₂) (h₃ : sig r₃' = sig r₃) :
    sig (typeOfIf (t', c₁) r₂' r₃') = sig (typeOfIf (t, c₁) r₂ r₃) := by
  unfold typeOfIf
  simp only [ht]
  cases t.typeOf with
  | bool b =>
    cases b with
    | tt => exact sig_bind h₂ fun u u' c _ hu => congrArg (fun x => some (x, c₁ ∪ c)) hu
    | ff => exact sig_bind h₃ fun u u' c _ hu => congrArg (fun x => some (x, c)) hu
    | anyBool =>
      refine sig_bind h₂ fun u u' c _ hu => sig_bind h₃ fun v v' d _ hv => ?_
      simp only [hu, hv]
      split <;> rfl
  | _ => rfl

theorem sig_typeOfAnd {t t' : TypedExpr} {c₁ : Capabilities} {r₂ r₂' : ResultType}
    (ht : t'.typeOf = t.typeOf) (h₂ : t.typeOf ≠ .bool .ff → sig r₂' = sig r₂) :
    sig (typeOfAnd (t', c₁) r₂') = sig (typeOfAnd (t, c₁) r₂) := by
  unfold typeOfAnd
  simp only [ht]
  cases hτ : t.typeOf with
  | bool b =>
    rw [hτ] at h₂
    cases b with
    | ff => exact congrArg (fun x => some (x, ∅)) ht
    | tt | anyBool =>
      refine sig_bind (h₂ (by simp)) fun u u' c _ hu => ?_
      simp only [hu]
      split <;> rfl
  | _ => rfl

theorem sig_typeOfOr {t t' : TypedExpr} {c₁ : Capabilities} {r₂ r₂' : ResultType}
    (ht : t'.typeOf = t.typeOf) (h₂ : sig r₂' = sig r₂) :
    sig (typeOfOr (t', c₁) r₂') = sig (typeOfOr (t, c₁) r₂) := by
  unfold typeOfOr
  simp only [ht]
  cases t.typeOf with
  | bool b =>
    cases b with
    | tt => exact congrArg (fun x => some (x, ∅)) ht
    | ff =>
      refine sig_bind h₂ fun u u' c _ hu => ?_
      simp only [hu]
      split <;> rfl
    | anyBool =>
      refine sig_bind h₂ fun u u' c _ hu => ?_
      simp only [hu]
      split <;> rfl
  | _ => rfl

theorem sig_typeOfUnaryApp {op : UnaryOp} {t t' : TypedExpr} (ht : t'.typeOf = t.typeOf) :
    sig (typeOfUnaryApp op t') = sig (typeOfUnaryApp op t) := by
  unfold typeOfUnaryApp
  simp only [ht]
  split <;> rfl

theorem typeOfInₑ_agree (hA : EnvAgree N env env') (e₁ e₂ : Cedar.Spec.EntityType)
    (x₁ x₂ : Cedar.Spec.Expr) : typeOfInₑ e₁ e₂ x₁ x₂ env' = typeOfInₑ e₁ e₂ x₁ x₂ env := by
  simp only [typeOfInₑ, Cedar.Validation.actionUID?, hA.contains, hA.descendentOf,
    hA.envDescendentOf]

theorem typeOfInₛ_agree (hA : EnvAgree N env env') (e₁ e₂ : Cedar.Spec.EntityType)
    (x₁ x₂ : Cedar.Spec.Expr) : typeOfInₛ e₁ e₂ x₁ x₂ env' = typeOfInₛ e₁ e₂ x₁ x₂ env := by
  simp only [typeOfInₛ, Cedar.Validation.actionUID?, hA.contains, hA.descendentOf,
    hA.envDescendentOf]

theorem typeOfHasTag_agree (hA : EnvAgree N env env') (ety : Cedar.Spec.EntityType)
    (x t : Cedar.Spec.Expr) (c : Capabilities) :
    typeOfHasTag ety x t c env' = typeOfHasTag ety x t c env := by
  simp only [typeOfHasTag, hA.ets, hA.actionType]

theorem typeOfGetTag_agree (hA : EnvAgree N env env') (ety : Cedar.Spec.EntityType)
    (x t : Cedar.Spec.Expr) (c : Capabilities) :
    typeOfGetTag ety x t c env' = typeOfGetTag ety x t c env := by
  simp only [typeOfGetTag, hA.ets]

theorem sig_typeOfEq {t₁ t₁' t₂ t₂' : TypedExpr} (h₁ : t₁'.typeOf = t₁.typeOf)
    (h₂ : t₂'.typeOf = t₂.typeOf) (x₁ x₂ : Cedar.Spec.Expr) :
    sig (typeOfEq t₁' t₂' x₁ x₂) = sig (typeOfEq t₁ t₂ x₁ x₂) := by
  unfold typeOfEq
  simp only [h₁, h₂]
  split
  · split <;> rfl
  · split
    · rfl
    · split <;> rfl

theorem sig_typeOfBinaryApp (hA : EnvAgree N env env') {op : BinaryOp} {t₁ t₁' t₂ t₂' : TypedExpr}
    (h₁ : t₁'.typeOf = t₁.typeOf) (h₂ : t₂'.typeOf = t₂.typeOf) (x₁ x₂ : Cedar.Spec.Expr)
    (c : Capabilities) :
    sig (typeOfBinaryApp op t₁' t₂' x₁ x₂ c env') = sig (typeOfBinaryApp op t₁ t₂ x₁ x₂ c env) := by
  unfold typeOfBinaryApp
  simp only [h₁, h₂, typeOfInₑ_agree hA, typeOfInₛ_agree hA, typeOfHasTag_agree hA,
    typeOfGetTag_agree hA]
  split
  · exact sig_typeOfEq h₁ h₂ x₁ x₂
  all_goals first
    | rfl
    | (cases typeOfHasTag _ x₁ x₂ c env with
        | error => rfl
        | ok p => rfl)
    | (cases typeOfGetTag _ x₁ x₂ c env with
        | error => rfl
        | ok p => rfl)
    | (cases ifLubThenBool _ _ with
        | error => rfl
        | ok p => rfl)

/-- Two types agree as subjects of an access to the attribute `a`: they are equal, or they are
record types that find `a` alike. -/
def TyAgreeAt (a : Attr) (T T' : CedarType) : Prop :=
  T' = T ∨ ∃ rty rty', T = .record rty ∧ T' = .record rty' ∧ rty'.find? a = rty.find? a

theorem sig_bind' {α : Type} {R R' : Except Cedar.Validation.TypeError α}
    {g g' : α → ResultType} (h : R'.toOption = R.toOption)
    (hg : ∀ p, R = .ok p → sig (g' p) = sig (g p)) : sig (R' >>= g') = sig (R >>= g) := by
  cases R with
  | error e =>
    cases R' with
    | error => rfl
    | ok => simp [Except.toOption] at h
  | ok p =>
    cases R' with
    | error => simp [Except.toOption] at h
    | ok p' =>
      simp only [Except.toOption, Option.some.injEq] at h
      subst h
      exact hg _ rfl

theorem hasAttrInRecord_agree {rty rty' : RecordType} {a : Attr} (hf : rty'.find? a = rty.find? a)
    (x : Cedar.Spec.Expr) (c : Capabilities) (b : Bool) :
    hasAttrInRecord rty' x a c b = hasAttrInRecord rty x a c b := by
  simp only [hasAttrInRecord, hf]

theorem getAttrInRecord_agree {rty rty' : RecordType} {a : Attr} (hf : rty'.find? a = rty.find? a)
    (T T' : CedarType) (x : Cedar.Spec.Expr) (c : Capabilities) :
    (getAttrInRecord T' rty' x a c).toOption = (getAttrInRecord T rty x a c).toOption := by
  simp only [getAttrInRecord, hf]
  split
  · rfl
  · split <;> rfl
  · rfl

theorem sig_typeOfHasAttr (hA : EnvAgree N env env') {t t' : TypedExpr} {a : Attr}
    (h : TyAgreeAt a t.typeOf t'.typeOf) (x : Cedar.Spec.Expr) (c : Capabilities) :
    sig (typeOfHasAttr t' x a c env') = sig (typeOfHasAttr t x a c env) := by
  unfold typeOfHasAttr
  rcases h with h | ⟨rty, rty', h₁, h₂, hf⟩
  · simp only [h, hA.ets, hA.actionType]
    split
    · cases hasAttrInRecord _ x a c true <;> rfl
    · split
      · cases hasAttrInRecord _ x a c false <;> rfl
      · split <;> rfl
    · rfl
  · simp only [h₁, h₂, hasAttrInRecord_agree hf]
    cases hasAttrInRecord rty x a c true <;> rfl

theorem sig_typeOfGetAttr (hA : EnvAgree N env env') {t t' : TypedExpr} {a : Attr}
    (h : TyAgreeAt a t.typeOf t'.typeOf) (x : Cedar.Spec.Expr) (c : Capabilities) :
    sig (typeOfGetAttr t' x a c env') = sig (typeOfGetAttr t x a c env) := by
  unfold typeOfGetAttr
  rcases h with h | ⟨rty, rty', h₁, h₂, hf⟩
  · simp only [h, hA.ets]
    split
    · exact sig_bind' rfl fun _ _ => rfl
    · split
      · exact sig_bind' rfl fun _ _ => rfl
      · rfl
    · rfl
  · simp only [h₁, h₂]
    exact sig_bind' (getAttrInRecord_agree hf _ _ x c) fun _ _ => rfl

theorem typeOfExtHasAttr_agree (hA : EnvAgree N env env') :
    (bs : List Attr) → (a : Attr) → {t t' : TypedExpr} → TyAgreeAt a t.typeOf t'.typeOf →
      (x : Cedar.Spec.Expr) → (c : Capabilities) →
      (typeOfExtHasAttr t' x (a :: bs) c env').toOption =
        (typeOfExtHasAttr t x (a :: bs) c env).toOption
  | [], a, t, t', h, x, c => by
    simp only [typeOfExtHasAttr]
    rcases sig_cases (sig_typeOfHasAttr hA h x c) with ⟨e, e', he, he'⟩ | ⟨u, u', d, hu, hu', hτ⟩
    · rw [he, he']; rfl
    · rw [hu, hu']
      simp only [Except.bind_ok, hτ]
  | b :: bs, a, t, t', h, x, c => by
    simp only [typeOfExtHasAttr]
    rcases sig_cases (sig_typeOfHasAttr hA h x c) with ⟨e, e', he, he'⟩ | ⟨u, u', d, hu, hu', hτ⟩
    · rw [he, he']; rfl
    · rw [hu, hu']
      simp only [Except.bind_ok, hτ]
      split
      · rfl
      · rcases sig_cases (sig_typeOfGetAttr hA h x (c ∪ d)) with
          ⟨e, e', he, he'⟩ | ⟨v, v', d', hv, hv', hτ'⟩
        · rw [he, he']; rfl
        · rw [hv, hv']
          simp only [Except.bind_ok]
          have ih := typeOfExtHasAttr_agree hA bs b (t := v) (t' := v') (.inl hτ')
            (.getAttr x a) (c ∪ d)
          cases hr : typeOfExtHasAttr v (.getAttr x a) (b :: bs) (c ∪ d) env with
          | error e =>
            cases hr' : typeOfExtHasAttr v' (.getAttr x a) (b :: bs) (c ∪ d) env' with
            | error => rfl
            | ok => rw [hr, hr'] at ih; simp [Except.toOption] at ih
          | ok r =>
            cases hr' : typeOfExtHasAttr v' (.getAttr x a) (b :: bs) (c ∪ d) env' with
            | error => rw [hr, hr'] at ih; simp [Except.toOption] at ih
            | ok r' =>
              rw [hr, hr'] at ih
              simp only [Except.toOption, Option.some.injEq] at ih
              subst ih
              rfl

theorem mapM_agree {α β γ ε : Type} (π : β → γ) (f f' : α → Except ε β) :
    (xs : List α) → (∀ x ∈ xs, (f' x).toOption.map π = (f x).toOption.map π) →
      (xs.mapM f').toOption.map (·.map π) = (xs.mapM f).toOption.map (·.map π)
  | [], _ => rfl
  | x :: xs, h => by
    have ih := mapM_agree π f f' xs (fun y hy => h y (by simp [hy]))
    have hx := h x (by simp)
    simp only [List.mapM_cons]
    cases hf : f x with
    | error e =>
      cases hf' : f' x with
      | error => rfl
      | ok => rw [hf, hf'] at hx; simp [Except.toOption] at hx
    | ok y =>
      cases hf' : f' x with
      | error => rw [hf, hf'] at hx; simp [Except.toOption] at hx
      | ok y' =>
        rw [hf, hf'] at hx
        simp only [Except.toOption, Option.map_some, Option.some.injEq] at hx
        simp only [Except.bind_ok]
        cases hm : xs.mapM f with
        | error e =>
          cases hm' : xs.mapM f' with
          | error => rfl
          | ok => rw [hm, hm'] at ih; simp [Except.toOption] at ih
        | ok ys =>
          cases hm' : xs.mapM f' with
          | error => rw [hm, hm'] at ih; simp [Except.toOption] at ih
          | ok ys' =>
            rw [hm, hm'] at ih
            simp only [Except.toOption, Option.map_some, Option.some.injEq] at ih
            simp [Except.toOption, pure, Except.pure, hx, ih]

theorem sig_bindList {α γ : Type} {π : α → γ} {R R' : Except Cedar.Validation.TypeError (List α)}
    {g g' : List α → ResultType} (h : R'.toOption.map (·.map π) = R.toOption.map (·.map π))
    (hg : ∀ ys ys', R = .ok ys → ys'.map π = ys.map π → sig (g' ys') = sig (g ys)) :
    sig (R' >>= g') = sig (R >>= g) := by
  cases R with
  | error e =>
    cases R' with
    | error => rfl
    | ok => simp [Except.toOption] at h
  | ok ys =>
    cases R' with
    | error => simp [Except.toOption] at h
    | ok ys' =>
      simp only [Except.toOption, Option.map_some, Option.some.injEq] at h
      exact hg ys ys' rfl h

theorem sig_typeOfSet {tys tys' : List TypedExpr}
    (h : tys'.map TypedExpr.typeOf = tys.map TypedExpr.typeOf) :
    sig (typeOfSet tys') = sig (typeOfSet tys) := by
  cases tys with
  | nil => cases tys' with
    | nil => rfl
    | cons => simp at h
  | cons hd tl =>
    cases tys' with
    | nil => simp at h
    | cons hd' tl' =>
      simp only [List.map_cons, List.cons.injEq] at h
      unfold typeOfSet
      simp only [h.1, h.2]
      split <;> rfl

theorem sig_typeOfCall {xfn : Cedar.Spec.ExtFun} {tys tys' : List TypedExpr}
    (h : tys'.map TypedExpr.typeOf = tys.map TypedExpr.typeOf) (xs : List Cedar.Spec.Expr) :
    sig (typeOfCall xfn tys' xs) = sig (typeOfCall xfn tys xs) := by
  unfold typeOfCall
  simp only [h]
  split
  all_goals first
    | rfl
    | (cases Cedar.Validation.typeOfConstructor _ xs _ with
        | error => rfl
        | ok => rfl)

theorem readsContextList_ofCedar :
    (xs : List Cedar.Spec.Expr) → Expr.ReadsContextList N (Expr.ofCedarList xs) →
      ∀ x ∈ xs, (Expr.ofCedar x).ReadsContext N
  | [], _ => fun _ hx => by cases hx
  | y :: ys, h => fun x hx => by
    simp only [Expr.ofCedarList, Expr.ReadsContextList] at h
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h.1
    · exact readsContextList_ofCedar ys h.2 x hx

theorem readsContextRecord_ofCedar :
    (axs : List (Attr × Cedar.Spec.Expr)) → Expr.ReadsContextRecord N (Expr.ofCedarRecord axs) →
      ∀ ax ∈ axs, (Expr.ofCedar ax.2).ReadsContext N
  | [], _ => fun _ hx => by cases hx
  | (a, y) :: ys, h => fun ax hx => by
    simp only [Expr.ofCedarRecord, Expr.ReadsContextRecord] at h
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h.1
    · exact readsContextRecord_ofCedar ys h.2 ax hx

theorem isContext_ofCedar (x : Cedar.Spec.Expr) :
    (Expr.ofCedar x).isContext = true ↔ x = .var .context := by
  cases x with
  | var v => cases v <;> simp [Expr.ofCedar, Expr.isContext]
  | _ => simp [Expr.ofCedar, Expr.isContext]

/-- Cedar types the context variable as its record type, whose attributes the environments find
alike outside `N`. -/
theorem typeOf_context_agree (hA : EnvAgree N env env') {a : Attr} (ha : a ∉ N)
    (c : Capabilities) :
    ∃ t t', typeOf (.var .context) c env = .ok (t, ∅) ∧
      typeOf (.var .context) c env' = .ok (t', ∅) ∧ TyAgreeAt a t.typeOf t'.typeOf :=
  ⟨.var .context (.record env.reqty.context), .var .context (.record env'.reqty.context),
    by simp [typeOf, typeOfVar, Cedar.Validation.ok],
    by simp [typeOf, typeOfVar, Cedar.Validation.ok],
    .inr ⟨_, _, rfl, rfl, hA.context a ha⟩⟩

/-- **Cedar types an expression alike in two environments that differ only in context attributes
it does not read**: to the same type and capabilities, or to an error in both. -/
theorem typeOf_agree (hA : EnvAgree N env env') (x : Cedar.Spec.Expr)
    (hr : (Expr.ofCedar x).ReadsContext N) (c : Capabilities) :
    sig (typeOf x c env') = sig (typeOf x c env) := by
  match x with
  | .lit p =>
    simp only [typeOf, typeOfLit, hA.ets, hA.contains]
  | .var v =>
    cases v with
    | principal => simp only [typeOf, typeOfVar, hA.principal]
    | action => simp only [typeOf, typeOfVar, hA.action]
    | resource => simp only [typeOf, typeOfVar, hA.resource]
    | context => simp [Expr.ofCedar, Expr.ReadsContext] at hr
  | .ite a b d =>
    simp only [Expr.ofCedar, Expr.ReadsContext] at hr
    simp only [typeOf]
    exact sig_bind (typeOf_agree hA a hr.1 c) fun t t' c₁ _ ht =>
      sig_typeOfIf ht (typeOf_agree hA b hr.2.1 _) (typeOf_agree hA d hr.2.2 _)
  | .and a b =>
    simp only [Expr.ofCedar, Expr.ReadsContext] at hr
    simp only [typeOf]
    exact sig_bind (typeOf_agree hA a hr.1 c) fun t t' c₁ _ ht =>
      sig_typeOfAnd ht fun _ => typeOf_agree hA b hr.2 _
  | .or a b =>
    simp only [Expr.ofCedar, Expr.ReadsContext] at hr
    simp only [typeOf]
    exact sig_bind (typeOf_agree hA a hr.1 c) fun t t' c₁ _ ht =>
      sig_typeOfOr ht (typeOf_agree hA b hr.2 _)
  | .unaryApp op a =>
    simp only [Expr.ofCedar, Expr.ReadsContext] at hr
    simp only [typeOf]
    exact sig_bind (typeOf_agree hA a hr c) fun t t' c₁ _ ht => sig_typeOfUnaryApp ht
  | .binaryApp op a b =>
    simp only [Expr.ofCedar, Expr.ReadsContext] at hr
    simp only [typeOf]
    exact sig_bind (typeOf_agree hA a hr.1 c) fun t t' c₁ _ ht =>
      sig_bind (typeOf_agree hA b hr.2 c) fun u u' c₂ _ hu => sig_typeOfBinaryApp hA ht hu a b c
  | .hasAttr y a =>
    simp only [Expr.ofCedar, Expr.ReadsContext] at hr
    simp only [typeOf]
    by_cases hy : y = .var .context
    · subst hy
      simp only [show (Expr.ofCedar (.var .context)).isContext = true from rfl, ↓reduceIte] at hr
      obtain ⟨t, t', h, h', hag⟩ := typeOf_context_agree hA hr c
      rw [h, h']
      exact sig_typeOfHasAttr hA hag _ c
    · have hc : (Expr.ofCedar y).isContext = false := by
        cases h : (Expr.ofCedar y).isContext
        · rfl
        · exact absurd ((isContext_ofCedar y).mp h) hy
      simp only [hc, Bool.false_eq_true, ↓reduceIte] at hr
      exact sig_bind (typeOf_agree hA y hr c) fun t t' c₁ _ ht =>
        sig_typeOfHasAttr hA (.inl ht) _ c
  | .getAttr y a =>
    simp only [Expr.ofCedar, Expr.ReadsContext] at hr
    simp only [typeOf]
    by_cases hy : y = .var .context
    · subst hy
      simp only [show (Expr.ofCedar (.var .context)).isContext = true from rfl, ↓reduceIte] at hr
      obtain ⟨t, t', h, h', hag⟩ := typeOf_context_agree hA hr c
      rw [h, h']
      exact sig_typeOfGetAttr hA hag _ c
    · have hc : (Expr.ofCedar y).isContext = false := by
        cases h : (Expr.ofCedar y).isContext
        · rfl
        · exact absurd ((isContext_ofCedar y).mp h) hy
      simp only [hc, Bool.false_eq_true, ↓reduceIte] at hr
      exact sig_bind (typeOf_agree hA y hr c) fun t t' c₁ _ ht =>
        sig_typeOfGetAttr hA (.inl ht) _ c
  | .extHasAttr y a bs =>
    simp only [Expr.ofCedar, Expr.ReadsContext] at hr
    simp only [typeOf]
    by_cases hy : y = .var .context
    · subst hy
      simp only [show (Expr.ofCedar (.var .context)).isContext = true from rfl, ↓reduceIte] at hr
      obtain ⟨t, t', h, h', hag⟩ := typeOf_context_agree hA hr c
      rw [h, h']
      simp only [Except.bind_ok]
      exact sig_bind' (typeOfExtHasAttr_agree hA bs a hag _ c) fun _ _ => rfl
    · have hc : (Expr.ofCedar y).isContext = false := by
        cases h : (Expr.ofCedar y).isContext
        · rfl
        · exact absurd ((isContext_ofCedar y).mp h) hy
      simp only [hc, Bool.false_eq_true, ↓reduceIte] at hr
      exact sig_bind (typeOf_agree hA y hr c) fun t t' c₁ _ ht =>
        sig_bind' (typeOfExtHasAttr_agree hA bs a (.inl ht) _ c) fun _ _ => rfl
  | .set xs =>
    simp only [Expr.ofCedar, Expr.ReadsContext] at hr
    have hr' := readsContextList_ofCedar xs hr
    simp only [typeOf]
    rw [List.mapM₁_eq_mapM (fun x => Cedar.Validation.justType (typeOf x c env)),
      List.mapM₁_eq_mapM (fun x => Cedar.Validation.justType (typeOf x c env'))]
    refine sig_bindList (π := TypedExpr.typeOf)
      (mapM_agree _ _ _ xs fun x hx => ?_) fun ys ys' _ h => sig_typeOfSet h
    have := typeOf_agree hA x (hr' x hx) c
    rcases sig_cases this with ⟨e, e', he, he'⟩ | ⟨t, t', d, ht, ht', hτ⟩
    · simp [Cedar.Validation.justType, he, he', Except.map, Except.toOption]
    · simp [Cedar.Validation.justType, ht, ht', Except.map, Except.toOption, hτ]
  | .record axs =>
    simp only [Expr.ofCedar, Expr.ReadsContext] at hr
    have hr' := readsContextRecord_ofCedar axs hr
    simp only [typeOf]
    rw [List.mapM₂_eq_mapM (fun ax => (typeOf ax.2 c env).map (fun p => (ax.1, p.1))),
      List.mapM₂_eq_mapM (fun ax => (typeOf ax.2 c env').map (fun p => (ax.1, p.1)))]
    refine sig_bindList (π := fun p => (p.1, p.2.typeOf))
      (mapM_agree _ _ _ axs fun ax hax => ?_) fun ys ys' _ h => ?_
    · have := typeOf_agree hA ax.2 (hr' ax hax) c
      rcases sig_cases this with ⟨e, e', he, he'⟩ | ⟨t, t', d, ht, ht', hτ⟩
      · simp [he, he', Except.map, Except.toOption]
      · simp [ht, ht', Except.map, Except.toOption, hτ]
    · have h' : ys'.map (fun p => (p.1, Cedar.Validation.Qualified.required p.2.typeOf)) =
          ys.map (fun p => (p.1, Cedar.Validation.Qualified.required p.2.typeOf)) := by
        have := congrArg (List.map (fun p => (p.1, Cedar.Validation.Qualified.required p.2))) h
        simpa [List.map_map, Function.comp_def] using this
      simp only [sig, Cedar.Validation.ok]
      exact congrArg (fun l => some (CedarType.record (Cedar.Data.Map.make l), ∅)) h'
  | .call xfn xs =>
    simp only [Expr.ofCedar, Expr.ReadsContext] at hr
    have hr' := readsContextList_ofCedar xs hr
    simp only [typeOf]
    rw [List.mapM₁_eq_mapM (fun x => Cedar.Validation.justType (typeOf x c env)),
      List.mapM₁_eq_mapM (fun x => Cedar.Validation.justType (typeOf x c env'))]
    refine sig_bindList (π := TypedExpr.typeOf)
      (mapM_agree _ _ _ xs fun x hx => ?_) fun ys ys' _ h => sig_typeOfCall h xs
    have := typeOf_agree hA x (hr' x hx) c
    rcases sig_cases this with ⟨e, e', he, he'⟩ | ⟨t, t', d, ht, ht', hτ⟩
    · simp [Cedar.Validation.justType, he, he', Except.map, Except.toOption]
    · simp [Cedar.Validation.justType, ht, ht', Except.map, Except.toOption, hτ]
termination_by sizeOf x
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := List.sizeOf_lt_of_mem hx; omega)
    | (have := List.sizeOf_snd_lt_sizeOf_list hax; omega)

end

/-! ## Reading the context, through action substitution and in the augmented schema -/

section

open Cedar.Validation (mapOnVars Schema ActionSchema QualifiedType)

variable {N : List Attr}

theorem readsContextList_ofCedar_of :
    (xs : List Cedar.Spec.Expr) → (∀ x ∈ xs, (Expr.ofCedar x).ReadsContext N) →
      Expr.ReadsContextList N (Expr.ofCedarList xs)
  | [], _ => trivial
  | y :: ys, h => ⟨h y (by simp), readsContextList_ofCedar_of ys fun x hx => h x (by simp [hx])⟩

theorem readsContextRecord_ofCedar_of :
    (axs : List (Attr × Cedar.Spec.Expr)) → (∀ ax ∈ axs, (Expr.ofCedar ax.2).ReadsContext N) →
      Expr.ReadsContextRecord N (Expr.ofCedarRecord axs)
  | [], _ => trivial
  | (a, y) :: ys, h =>
    ⟨h (a, y) (by simp), readsContextRecord_ofCedar_of ys fun x hx => h x (by simp [hx])⟩

theorem isContext_mapOnVars (u : EntityUID) (x : Cedar.Spec.Expr) :
    (Expr.ofCedar (mapOnVars (actionSubst u) x)).isContext = (Expr.ofCedar x).isContext := by
  cases x with
  | var v => cases v <;> simp [mapOnVars, actionSubst, Expr.ofCedar, Expr.isContext]
  | _ => simp [mapOnVars, Expr.ofCedar, Expr.isContext]

/-- Substituting the action keeps the context read only through other attributes. -/
theorem readsContext_mapOnVars (u : EntityUID) (x : Cedar.Spec.Expr)
    (h : (Expr.ofCedar x).ReadsContext N) :
    (Expr.ofCedar (mapOnVars (actionSubst u) x)).ReadsContext N := by
  match x with
  | .lit _ => simp [mapOnVars, Expr.ofCedar, Expr.ReadsContext]
  | .var v =>
    cases v <;> simp_all [mapOnVars, actionSubst, Expr.ofCedar, Expr.ReadsContext]
  | .ite a b d =>
    simp only [Expr.ofCedar, Expr.ReadsContext, mapOnVars] at h ⊢
    exact ⟨readsContext_mapOnVars u a h.1, readsContext_mapOnVars u b h.2.1,
      readsContext_mapOnVars u d h.2.2⟩
  | .and a b | .or a b | .binaryApp _ a b =>
    simp only [Expr.ofCedar, Expr.ReadsContext, mapOnVars] at h ⊢
    exact ⟨readsContext_mapOnVars u a h.1, readsContext_mapOnVars u b h.2⟩
  | .unaryApp _ a =>
    simp only [Expr.ofCedar, Expr.ReadsContext, mapOnVars] at h ⊢
    exact readsContext_mapOnVars u a h
  | .getAttr a _ | .hasAttr a _ | .extHasAttr a _ _ =>
    simp only [Expr.ofCedar, Expr.ReadsContext, mapOnVars] at h ⊢
    rw [isContext_mapOnVars]
    split
    · simp_all
    · rename_i hc
      simp only [hc, Bool.false_eq_true, ↓reduceIte] at h
      exact readsContext_mapOnVars u a h
  | .set xs | .call _ xs =>
    simp only [Expr.ofCedar, Expr.ReadsContext, mapOnVars] at h ⊢
    rw [List.map₁_eq_map (mapOnVars (actionSubst u)) xs]
    have h' := readsContextList_ofCedar xs h
    refine readsContextList_ofCedar_of _ fun y hy => ?_
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    exact readsContext_mapOnVars u x (h' x hx)
  | .record axs =>
    simp only [Expr.ofCedar, Expr.ReadsContext, mapOnVars] at h ⊢
    rw [List.map₂_eq_map_snd (mapOnVars (actionSubst u))]
    have h' := readsContextRecord_ofCedar axs h
    refine readsContextRecord_ofCedar_of _ fun ay hay => ?_
    obtain ⟨ax, hax, rfl⟩ := List.mem_map.mp hay
    exact readsContext_mapOnVars u ax.2 (h' ax hax)
termination_by sizeOf x
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := List.sizeOf_lt_of_mem hx; omega)
    | (have := List.sizeOf_snd_lt_sizeOf_list hax; omega)

variable {A : Schema} {H : List (Attr × QualifiedType)} {env : TypeEnv}

theorem actionType?_mapOnValues (f : Cedar.Validation.ActionSchemaEntry →
    Cedar.Validation.ActionSchemaEntry) (acts : ActionSchema) (ety : Cedar.Spec.EntityType) :
    ActionSchema.actionType? (acts.mapOnValues f) ety = acts.actionType? ety := by
  simp only [ActionSchema.actionType?, Cedar.Data.Map.keys_mapOnValues]

/-- **An environment and its augmentation agree** outside the hoisted attributes. -/
theorem envAgree_augment (h : env ∈ A.environments) (hH : ∀ p ∈ H, p.1 ∈ N) :
    EnvAgree N (augmentEnv A H env) env where
  ets := rfl
  principal := rfl
  action := rfl
  resource := rfl
  contains u := (augmentEnv_contains h u).symm
  descendentOf u v := by rw [augmentEnv_descendentOf h, environments_acts h]
  actionType ety := by
    simp only [augmentEnv, augment_acts, environments_acts h]
    exact (actionType?_mapOnValues _ _ _).symm
  envDescendentOf e₁ e₂ := by
    unfold TypeEnv.descendentOf
    simp only [show (augmentEnv A H env).ets = env.ets from rfl,
      augmentEnv_maybeDescendentOf, environments_acts h]
  context a ha := by
    simp only [augmentEnv]
    rw [make_append_find?, map_find?_eq]
    have hn : H.find? (·.1 == a) = none := by
      rw [List.find?_eq_none]
      intro p hp hpa
      exact ha (by simpa using (beq_iff_eq.mp hpa) ▸ hH p hp)
    rw [hn]
    cases env.reqty.context.toList.find? (·.1 == a) <;> rfl

open Cedar.Validation (checkEntities) in
/-- Cedar's check of entity literals reads of the schema only its entity types and actions. -/
theorem checkEntities_augment (A : Schema) (H : List (Attr × QualifiedType)) (x : Cedar.Spec.Expr) :
    checkEntities (Schema.augment A H) x = checkEntities A x := by
  have hc : ∀ u, (Schema.augment A H).acts.contains u = A.acts.contains u := fun u =>
    Cedar.Data.Map.contains_mapOnValues _
  have ht : ∀ ety, (Schema.augment A H).acts.actionType? ety = A.acts.actionType? ety := fun ety =>
    actionType?_mapOnValues _ _ _
  match x with
  | .lit p =>
    cases p <;> simp only [checkEntities, hc, show (Schema.augment A H).ets = A.ets from rfl]
  | .var _ => simp only [checkEntities]
  | .unaryApp op a =>
    cases op <;> simp only [checkEntities, ht, checkEntities_augment A H a,
      show (Schema.augment A H).ets = A.ets from rfl]
  | .ite a b d =>
    simp only [checkEntities, checkEntities_augment A H a, checkEntities_augment A H b,
      checkEntities_augment A H d]
  | .and a b | .or a b | .binaryApp _ a b =>
    simp only [checkEntities, checkEntities_augment A H a, checkEntities_augment A H b]
  | .getAttr a _ | .hasAttr a _ | .extHasAttr a _ _ =>
    simp only [checkEntities, checkEntities_augment A H a]
  | .set xs | .call _ xs =>
    simp only [checkEntities]
    congr 1
    funext ⟨y, hy⟩
    exact checkEntities_augment A H y
  | .record axs =>
    simp only [checkEntities]
    congr 1
    funext ⟨ay, hay⟩
    exact checkEntities_augment A H ay.2
termination_by sizeOf x
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := List.sizeOf_lt_of_mem hy; omega)

end

/-! ## Policies, without the hoisted attributes -/

section

open Cedar.Validation (typecheckPolicy typecheckPolicyWithEnvironments checkEntities Schema
  QualifiedType substituteAction subty)

variable {N : List Attr} {env env' : TypeEnv}

/-- **A chain types alike in two environments that agree outside `N`**, when its conjuncts read
the context only outside `N`, and its end does wherever Cedar's typing reaches it. -/
theorem andChain_agree (hA : EnvAgree N env env') :
    (xs : List Cedar.Spec.Expr) → {z : Cedar.Spec.Expr} → (c₀ : Capabilities) →
      (∀ x ∈ xs, (Expr.ofCedar x).ReadsContext N) →
      (∀ ca, Reaches env xs c₀ ca → (Expr.ofCedar z).ReadsContext N) →
      sig (typeOf (andChain xs z) c₀ env') = sig (typeOf (andChain xs z) c₀ env)
  | [], z, c₀, _, hz => typeOf_agree hA z (hz c₀ .nil) c₀
  | x :: xs, z, c₀, hxs, hz => by
    simp only [andChain, typeOf]
    exact sig_bind (typeOf_agree hA x (hxs x (by simp)) c₀) fun t t' c₁ hx ht =>
      sig_typeOfAnd ht fun hne => andChain_agree hA xs (c₀ ∪ c₁)
        (fun y hy => hxs y (by simp [hy])) (fun ca hr => hz ca (.cons hx hne hr))

/-- A policy whose substituted expression types alike in two environments is typed in one when it
is in the other, to the same type. -/
theorem typecheckPolicy_agree (hA : EnvAgree N env env') {Y : Cedar.Spec.Policy}
    (hs : sig (typeOf (substituteAction env.reqty.action Y.toExpr) ∅ env') =
      sig (typeOf (substituteAction env.reqty.action Y.toExpr) ∅ env))
    {tx : TypedExpr} (h : typecheckPolicy Y env = .ok tx) :
    ∃ tx', typecheckPolicy Y env' = .ok tx' ∧ tx'.typeOf = tx.typeOf := by
  unfold typecheckPolicy at h ⊢
  dsimp only at h ⊢
  rw [hA.action]
  rcases sig_cases hs with ⟨e, e', he, he'⟩ | ⟨t, t', c, ht, ht', hτ⟩
  · rw [he] at h; cases h
  · rw [ht] at h
    rw [ht']
    by_cases hsub : (t.typeOf ⊑ .bool .anyBool) = true
    · simp only [hsub, ↓reduceIte, Except.ok.injEq] at h
      subst h
      exact ⟨t', by simp [hτ, hsub], hτ⟩
    · simp [hsub] at h

/-- What Cedar's validation of a policy that succeeds or reports it impossible gives: its entity
literals are declared, and it is typed in every environment. -/
theorem typecheckPolicyWithEnvironments_inv' {L : Cedar.Spec.Policy} {S : Schema}
    (h : typecheckPolicyWithEnvironments typecheckPolicy L S = .ok () ∨
      typecheckPolicyWithEnvironments typecheckPolicy L S = .error (.impossiblePolicy L.id)) :
    checkEntities S L.toExpr = .ok () ∧
      ∀ env ∈ S.environments, ∃ tx, typecheckPolicy L env = .ok tx := by
  rcases h with h | h
  · obtain ⟨hc, hall, -⟩ := typecheckPolicyWithEnvironments_inv h
    exact ⟨hc, hall⟩
  · unfold typecheckPolicyWithEnvironments at h
    cases hc : checkEntities S L.toExpr with
    | error e => simp [hc, Except.mapError] at h
    | ok u =>
      simp only [hc, Except.mapError, Except.bind_ok] at h
      cases hm : S.environments.mapM (typecheckPolicy L) with
      | error e =>
        rw [hm] at h
        change Except.error e = _ at h
        cases h
        obtain ⟨env, -, he⟩ := List.mapM_error_implies_exists_error hm
        unfold typecheckPolicy at he
        dsimp only at he
        split at he
        · split at he <;> cases he
        · cases he
      | ok tys =>
        refine ⟨rfl, fun env henv => ?_⟩
        obtain ⟨y, -, hy⟩ := List.mapM_ok_implies_all_ok hm env henv
        exact ⟨y, hy⟩

/-- **Cedar's validation of a policy typed in every environment, in one as other than `False`,**
succeeds. -/
theorem typecheckPolicyWithEnvironments_of_ne {O : Cedar.Spec.Policy} {S : Schema}
    (hc : checkEntities S O.toExpr = .ok ())
    (hall : ∀ env ∈ S.environments, ∃ tx, typecheckPolicy O env = .ok tx)
    (hne : ∃ env ∈ S.environments, ∃ tx, typecheckPolicy O env = .ok tx ∧ tx.typeOf ≠ .bool .ff) :
    typecheckPolicyWithEnvironments typecheckPolicy O S = .ok () := by
  obtain ⟨tys, htys⟩ := List.all_ok_implies_mapM'_ok (f := typecheckPolicy O) hall
  rw [List.mapM'_eq_mapM] at htys
  unfold typecheckPolicyWithEnvironments
  simp only [hc, Except.mapError, Except.bind_ok, htys]
  split
  · rename_i hf
    obtain ⟨env, henv, tx, htx, hne⟩ := hne
    obtain ⟨y, hy, hy'⟩ := List.mapM_ok_implies_all_ok htys env henv
    rw [htx] at hy'
    cases hy'
    simp only [Cedar.Validation.allFalse, List.all_eq_true] at hf
    exact absurd (by simpa using hf _ hy) hne
  · rfl

/-- **Validation transfers from the augmented schema to the action schema**, for a policy whose
substituted expression types alike in each environment and its augmentation: if Cedar's
validation of the policy against the augmented schema succeeds, or reports it impossible, so does
its validation against the action schema. -/
theorem typecheckPolicyWithEnvironments_unaugment {A : Schema} {H : List (Attr × QualifiedType)}
    (hH : ∀ p ∈ H, p.1 ∈ N) {Y : Cedar.Spec.Policy}
    (hs : ∀ env ∈ A.environments,
      sig (typeOf (substituteAction env.reqty.action Y.toExpr) ∅ env) =
        sig (typeOf (substituteAction env.reqty.action Y.toExpr) ∅ (augmentEnv A H env))) :
    (typecheckPolicyWithEnvironments typecheckPolicy Y (Schema.augment A H) = .ok () →
      typecheckPolicyWithEnvironments typecheckPolicy Y A = .ok ()) ∧
    (typecheckPolicyWithEnvironments typecheckPolicy Y (Schema.augment A H) = .ok () ∨
      typecheckPolicyWithEnvironments typecheckPolicy Y (Schema.augment A H) =
        .error (.impossiblePolicy Y.id) →
      typecheckPolicyWithEnvironments typecheckPolicy Y A = .ok () ∨
      typecheckPolicyWithEnvironments typecheckPolicy Y A = .error (.impossiblePolicy Y.id)) := by
  have hall : ∀ {T : CedarType} (env : TypeEnv), env ∈ A.environments → ∀ tx,
      typecheckPolicy Y (augmentEnv A H env) = .ok tx → tx.typeOf = T →
      ∃ tx', typecheckPolicy Y env = .ok tx' ∧ tx'.typeOf = T := by
    intro T env henv tx htx hT
    obtain ⟨tx', h', hτ⟩ := typecheckPolicy_agree (envAgree_augment henv hH) (hs env henv) htx
    exact ⟨tx', h', hτ.trans hT⟩
  have hce : ∀ {S : Schema}, S = A → checkEntities (Schema.augment A H) Y.toExpr = .ok () →
      checkEntities S Y.toExpr = .ok () := by
    rintro S rfl h
    rwa [checkEntities_augment] at h
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨hc, hallA, envW, henvW, txW, htxW, hneW⟩ := typecheckPolicyWithEnvironments_inv h
    obtain ⟨env₀, henv₀, rfl⟩ := mem_augment_environments henvW
    refine typecheckPolicyWithEnvironments_of_ne (hce rfl hc) (fun env henv => ?_) ?_
    · obtain ⟨tx, htx⟩ := hallA _ (augmentEnv_mem henv)
      obtain ⟨tx', h', -⟩ := hall env henv tx htx rfl
      exact ⟨tx', h'⟩
    · obtain ⟨tx', h', hτ⟩ := hall env₀ henv₀ txW htxW rfl
      exact ⟨env₀, henv₀, tx', h', by rw [hτ]; exact hneW⟩
  · obtain ⟨hc, hallA⟩ := typecheckPolicyWithEnvironments_inv' h
    refine typecheckPolicyWithEnvironments_of (hce rfl hc) fun env henv => ?_
    obtain ⟨tx, htx⟩ := hallA _ (augmentEnv_mem henv)
    obtain ⟨tx', h', -⟩ := hall env henv tx htx rfl
    exact ⟨tx', h'⟩

end

/-! ## Where the translated fragment reads the context -/

section

variable {N : List Attr}

theorem readsContext_ctxAttr : (y : Cedar.Spec.Expr) → (p : Path) → ctxPath y = some p →
    (a : Attr) → (∀ b, (p ++ [a]).head? = some b → b ∉ N) →
    (Expr.ofCedar (.getAttr y a)).ReadsContext N
  | .var .context, p, hp, a, hN => by
    simp only [ctxPath, Option.some.injEq] at hp
    subst hp
    simp only [Expr.ofCedar, Expr.ReadsContext, Expr.isContext, ↓reduceIte]
    exact hN a rfl
  | .getAttr y a', p, hp, a, hN => by
    simp only [ctxPath, Option.map_eq_some_iff] at hp
    obtain ⟨p', hp', rfl⟩ := hp
    have ih := readsContext_ctxAttr y p' hp' a' fun b hb => hN b (by
      cases p' with
      | nil => simpa using hb
      | cons c q => simpa using hb)
    simp only [Expr.ofCedar, Expr.ReadsContext, Expr.isContext, Bool.false_eq_true,
      ↓reduceIte] at ih ⊢
    exact ih
  | .lit _, _, hp, _, _ | .var .principal, _, hp, _, _ | .var .action, _, hp, _, _
  | .var .resource, _, hp, _, _ | .ite .., _, hp, _, _ | .and .., _, hp, _, _
  | .or .., _, hp, _, _ | .unaryApp .., _, hp, _, _ | .binaryApp .., _, hp, _, _
  | .hasAttr .., _, hp, _, _ | .extHasAttr .., _, hp, _, _ | .set .., _, hp, _, _
  | .record .., _, hp, _, _ | .call .., _, hp, _, _ => by cases hp

theorem readsContext_scopePath : (y : Cedar.Spec.Expr) → (rp : ScopeRoot × Path) →
    scopePath y = some rp →
    (Expr.ofCedar y).ReadsContext N ∧ (Expr.ofCedar y).isContext = false
  | .var .principal, _, _ | .var .resource, _, _ => by
    simp [Expr.ofCedar, Expr.ReadsContext, Expr.isContext]
  | .getAttr y a, rp, hp => by
    simp only [scopePath, Option.map_eq_some_iff] at hp
    obtain ⟨rp', hp', -⟩ := hp
    have ih := readsContext_scopePath y rp' hp'
    simp only [Expr.ofCedar, Expr.ReadsContext]
    rw [ih.2]
    exact ⟨ih.1, rfl⟩
  | .lit _, _, hp | .var .action, _, hp | .var .context, _, hp | .ite .., _, hp
  | .and .., _, hp | .or .., _, hp | .unaryApp .., _, hp | .binaryApp .., _, hp
  | .hasAttr .., _, hp | .extHasAttr .., _, hp | .set .., _, hp | .record .., _, hp
  | .call .., _, hp => by cases hp

theorem pathType_head {present : Path → Bool} {rty : RecordType} {pre : Path} {b : Attr}
    {p : Path} {T : CedarType} (h : pathType? present rty pre (b :: p) = some T) :
    rty.find? b ≠ none := by
  unfold pathType? at h
  intro hb
  rw [hb] at h
  cases h

variable {C : TypingCtx}

/-- **A typed term reads the context only through declared attributes**, so through none the
environment lacks. -/
theorem readsContext_toTerm (hfresh : ∀ a ∈ N, C.env.reqty.context.find? a = none) :
    (x : Cedar.Spec.Expr) → (t : Term) → toTerm x = some t → {τ : TType} →
      Term.Typed C [] t τ → (Expr.ofCedar x).ReadsContext N
  | .lit _, _, _, _, _ => by simp [Expr.ofCedar, Expr.ReadsContext]
  | .var .principal, _, _, _, _ | .var .resource, _, _, _, _ => by
    simp [Expr.ofCedar, Expr.ReadsContext]
  | .call xfn xs, t, ht, τ, _ => by
    obtain ⟨s, rfl, rfl, rfl⟩ := toTerm_call ht
    simp [Expr.ofCedar, Expr.ofCedarList, Expr.ReadsContext, Expr.ReadsContextList]
  | .getAttr x a, t, ht, τ, hty => by
    cases hcx : ctxPath x with
    | some p =>
      simp only [toTerm, attrTerm, hcx, Option.some.injEq] at ht
      subst ht
      cases hty with
      | context hT =>
        refine readsContext_ctxAttr x p hcx a fun b hb hbN => ?_
        cases hq : p ++ [a] with
        | nil => simp at hq
        | cons c q =>
          rw [hq] at hb hT
          simp only [List.head?_cons, Option.some.injEq] at hb
          subst hb
          exact pathType_head hT (hfresh _ hbN)
    | none =>
      cases hsx : scopePath x with
      | none => simp [toTerm, attrTerm, hcx, hsx] at ht
      | some rp =>
        have h := readsContext_scopePath (N := N) x rp hsx
        simp only [Expr.ofCedar, Expr.ReadsContext, h.2, Bool.false_eq_true, ↓reduceIte]
        exact h.1
  | .binaryApp .add x y, t, ht, τ, hty | .binaryApp .sub x y, t, ht, τ, hty
  | .binaryApp .mul x y, t, ht, τ, hty => by
    simp only [toTerm, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at ht
    obtain ⟨tx', htx', ty', hty', rfl⟩ := ht
    cases hty with
    | arith hl hr =>
      simp only [Expr.ofCedar, Expr.ReadsContext]
      exact ⟨readsContext_toTerm hfresh x tx' htx' hl, readsContext_toTerm hfresh y ty' hty' hr⟩
  | .var .action, _, ht, _, _ | .var .context, _, ht, _, _
  | .ite .., _, ht, _, _ | .and .., _, ht, _, _ | .or .., _, ht, _, _
  | .unaryApp .., _, ht, _, _ | .binaryApp .eq .., _, ht, _, _
  | .binaryApp .mem .., _, ht, _, _ | .binaryApp .hasTag .., _, ht, _, _
  | .binaryApp .getTag .., _, ht, _, _ | .binaryApp .less .., _, ht, _, _
  | .binaryApp .lessEq .., _, ht, _, _ | .binaryApp .contains .., _, ht, _, _
  | .binaryApp .containsAll .., _, ht, _, _ | .binaryApp .containsAny .., _, ht, _, _
  | .hasAttr .., _, ht, _, _ | .extHasAttr .., _, ht, _, _ | .set .., _, ht, _, _
  | .record .., _, ht, _, _ => by simp [toTerm] at ht

/-- **A Cedar expression whose translation is a well-typed leaf reads the context only through
declared attributes.** -/
theorem readsContext_toTemporal (hfresh : ∀ a ∈ N, C.env.reqty.context.find? a = none) :
    (e : Cedar.Spec.Expr) → (φ : Formula) → toTemporal e = some φ → φ.WellTyped C [] →
      (Expr.ofCedar e).ReadsContext N
  | .binaryApp .eq x y, φ, hφ, hwt | .binaryApp .less x y, φ, hφ, hwt
  | .binaryApp .lessEq x y, φ, hφ, hwt => by
    simp only [toTemporal, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hφ
    obtain ⟨tx, htx, ty, hty, rfl⟩ := hφ
    simp only [Expr.ofCedar, Expr.ReadsContext]
    cases hwt with
    | eq _ hx hy _ | ord _ hx hy =>
      exact ⟨readsContext_toTerm hfresh x tx htx hx, readsContext_toTerm hfresh y ty hty hy⟩
  | .and x y, φ, hφ, hwt => by
    simp only [toTemporal, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hφ
    obtain ⟨φx, hφx, φy, hφy, rfl⟩ := hφ
    simp only [Expr.ofCedar, Expr.ReadsContext]
    cases hwt with
    | and hx hy =>
      exact ⟨readsContext_toTemporal hfresh x φx hφx hx, readsContext_toTemporal hfresh y φy hφy hy⟩
  | .or x y, φ, hφ, hwt => by
    simp only [toTemporal, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hφ
    obtain ⟨φx, hφx, φy, hφy, rfl⟩ := hφ
    simp only [Expr.ofCedar, Expr.ReadsContext]
    cases hwt with
    | not h =>
      cases h with
      | and hx hy =>
        cases hx with
        | not hx =>
          cases hy with
          | not hy =>
            exact ⟨readsContext_toTemporal hfresh x φx hφx hx,
              readsContext_toTemporal hfresh y φy hφy hy⟩
  | .unaryApp .not x, φ, hφ, hwt => by
    simp only [toTemporal, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hφ
    obtain ⟨φx, hφx, rfl⟩ := hφ
    simp only [Expr.ofCedar, Expr.ReadsContext]
    cases hwt with
    | not hx => exact readsContext_toTemporal hfresh x φx hφx hx
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

/-! ## Conditions, and the Cedar policies of rules without leaves -/

section

variable {N : List Attr}

/-- A Cedar condition read as Dogwood. -/
def condOfCedar (c : Cedar.Spec.Condition) : Condition := ⟨c.kind, Expr.ofCedar c.body⟩

theorem condOfCedar_toExpr (c : Cedar.Spec.Condition) :
    (condOfCedar c).toExpr = Expr.ofCedar c.toExpr := by
  obtain ⟨kind, body⟩ := c
  cases kind <;> rfl

theorem readsContext_foldl (l : Conditions) (acc : Expr) :
    (l.foldl (fun e c => .and c.toExpr e) acc).ReadsContext N ↔
      acc.ReadsContext N ∧ ∀ c ∈ l, c.toExpr.ReadsContext N := by
  induction l generalizing acc with
  | nil => simp
  | cons c l ih =>
    simp only [List.foldl_cons, ih, Expr.ReadsContext, List.mem_cons, forall_eq_or_imp]
    constructor
    · rintro ⟨⟨h₁, h₂⟩, h₃⟩; exact ⟨h₂, h₁, h₃⟩
    · rintro ⟨h₁, h₂, h₃⟩; exact ⟨⟨h₂, h₁⟩, h₃⟩

/-- A rule's conditions read the context only outside `N` when each does. -/
theorem readsContext_conditions (cs : Conditions) :
    (Conditions.toExpr cs).ReadsContext N ↔ ∀ c ∈ cs, c.toExpr.ReadsContext N := by
  unfold Conditions.toExpr
  have hm : ∀ c, c ∈ cs ↔ c ∈ cs.reverse := fun c => List.mem_reverse.symm
  simp only [hm]
  cases cs.reverse with
  | nil => simp [Expr.ReadsContext]
  | cons c l =>
    simp only [readsContext_foldl, List.mem_cons, forall_eq_or_imp]

theorem conditions_lowerFrom_ofCedar : (cs : Cedar.Spec.Conditions) → (k : Nat) →
    Conditions.lowerFrom k (cs.map condOfCedar) = (cs, k)
  | [], _ => rfl
  | c :: cs, k => by
    simp only [List.map_cons, Conditions.lowerFrom, condOfCedar, lowerFrom_ofCedar,
      conditions_lowerFrom_ofCedar cs k]

/-- **A Cedar policy is the lowering of its reading as Dogwood**, from any leaf index. -/
theorem policy_ofCedar_lowerFrom (p : Cedar.Spec.Policy) (k : Nat) :
    (Policy.ofCedar p).lowerFrom k = (p, k) := by
  have h := conditions_lowerFrom_ofCedar p.condition k
  have hc : (p.condition.map fun c => (⟨c.kind, Expr.ofCedar c.body⟩ : Condition)) =
      p.condition.map condOfCedar := rfl
  simp only [Policy.lowerFrom, Policy.ofCedar, hc, h]

theorem ofCedar_inj {x y : Cedar.Spec.Expr} (h : Expr.ofCedar x = Expr.ofCedar y) : x = y := by
  have := congrArg (fun z => (z.lowerFrom 0).1) h
  simpa only [lowerFrom_ofCedar] using this

end

/-! ## The original policy set -/

section

open Cedar.Validation (typecheckPolicy typecheckPolicyWithEnvironments mapOnVars substituteAction
  Schema)

theorem forM_append_cons {α ε : Type} {f : α → Except ε Unit} {o : α} {E : ε} :
    {xs : List α} → {ys : List α} → (∀ x ∈ xs, f x = .ok ()) → (∀ y ∈ ys, f y = .ok ()) →
      f o = .ok () ∨ f o = .error E →
      (xs ++ o :: ys).forM f = .ok () ∨ (xs ++ o :: ys).forM f = .error E
  | [], ys, _, hy, ho => by
    simp only [List.nil_append, List.forM]
    rcases ho with ho | ho
    · rw [ho]
      exact .inl (List.all_ok_implies_forM_ok _ _ hy)
    · rw [ho]
      exact .inr rfl
  | x :: xs, ys, hx, hy, ho => by
    simp only [List.cons_append, List.forM, hx x (by simp), Except.bind_ok]
    exact forM_append_cons (xs := xs) (fun z hz => hx z (by simp [hz])) hy ho

/-- **Dogwood's validity of a policy set with a temporal leaf gives Cedar's validation of the
Cedar policy set it came from.** Let a valid policy set have the leaf `temporal { φ }`, the
translation of the Cedar expression `e`, as a condition of one of its rules, and let `ps` be Cedar
policies that read, as Dogwood, as the policy set with `e` in the leaf's place (so the leaf is the
only one). Cedar's validation of `ps` against the action schema succeeds, or reports the leaf's
rule impossible: typed `False` in every environment. -/
theorem validate_original {P : PolicySet} (hv : P.Valid) {qs₁ qs₂ : Policies} {q : Policy}
    {pre post : Conditions} {k : Cedar.Spec.ConditionKind} {e : Cedar.Spec.Expr} {φ : Formula}
    (hφ : toTemporal e = some φ)
    (hps : P.policies = qs₁ ++ q.withCondition pre ⟨k, .temporal φ⟩ post :: qs₂)
    {ps : Cedar.Spec.Policies}
    (hcs : ps.map Policy.ofCedar = qs₁ ++ q.withCondition pre ⟨k, Expr.ofCedar e⟩ post :: qs₂) :
    Cedar.Validation.validate ps P.actionSchema = .ok () ∨
      Cedar.Validation.validate ps P.actionSchema = .error (.impossiblePolicy q.id) := by
  have hq'mem : q.withCondition pre ⟨k, .temporal φ⟩ post ∈ P.policies := by rw [hps]; simp
  have hA := augmentedSchema_eq hv
  have hH : ∀ p ∈ P.leafTypes, p.1 ∈ P.hoistedNames := fun p hp => by
    rw [← leafTypes_keys]; exact List.mem_map_of_mem hp
  have hleaf : P.leafList ≠ [] := by
    intro h
    have hm : (.inl φ : Leaf) ∈ P.leafList :=
      List.mem_flatMap.mpr ⟨_, hq'mem, (mem_leaves_replace (e := e)).mpr (.inr rfl)⟩
    rw [h] at hm
    cases hm
  have hrc := hv.readsContext hleaf
  -- The leaf's rule reads the context outside the hoisted names in its scope and conditions.
  have hrq := hrc _ hq'mem
  simp only [Policy.toExpr, Expr.ReadsContext, Policy.withCondition] at hrq
  obtain ⟨hrps, hras, hrrs, hrcs⟩ := hrq
  rw [readsContext_conditions] at hrcs
  -- The Cedar policies: the other rules, and the leaf's.
  obtain ⟨ps₁, ps₂', rfl, h₁, h₂'⟩ := List.map_eq_append_iff.mp hcs
  obtain ⟨o, ps₂, rfl, ho, h₂⟩ := List.map_eq_cons_iff.mp h₂'
  -- Validation transfers for a rule other than the leaf's.
  have hother : ∀ p ∈ ps₁ ++ ps₂,
      typecheckPolicyWithEnvironments typecheckPolicy p P.actionSchema = .ok () := by
    intro p hp
    have hpmem : Policy.ofCedar p ∈ P.policies := by
      rw [hps]
      rcases List.mem_append.mp hp with hp | hp
      · exact List.mem_append_left _ (h₁ ▸ List.mem_map_of_mem hp)
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ (h₂ ▸ List.mem_map_of_mem hp))
    obtain ⟨j, hmem, -⟩ := lowered_of_mem P.policies 0 _ hpmem
    rw [policy_ofCedar_lowerFrom] at hmem
    have haug := validate_mem hv.toAll.cedar hmem
    rw [hA] at haug
    have hrp : (Expr.ofCedar p.toExpr).ReadsContext P.hoistedNames := by
      rw [← Policy.toExpr_ofCedar]; exact hrc _ hpmem
    refine (typecheckPolicyWithEnvironments_unaugment hH fun env henv => ?_).1 haug
    rw [substituteAction_eq]
    exact typeOf_agree (envAgree_augment henv hH) _ (readsContext_mapOnVars _ _ hrp) ∅
  -- The leaf's rule: its Cedar policy is the Cedar version.
  have hoc := congrArg Policy.condition ho
  simp only [Policy.ofCedar, Policy.withCondition] at hoc
  obtain ⟨preC, cpost, hoce, hpre, hcpost⟩ := List.map_eq_append_iff.mp hoc
  obtain ⟨c, postC, rfl, hc, hpost⟩ := List.map_eq_cons_iff.mp hcpost
  have hck : c.kind = k := congrArg Condition.kind hc
  have hcb : c.body = e := ofCedar_inj (congrArg Condition.body hc)
  have hceq : c = ⟨k, e⟩ := by
    obtain ⟨ck, cb⟩ := c
    simp only at hck hcb
    rw [hck, hcb]
  subst hceq
  have hpre' : pre = preC.map condOfCedar := hpre.symm
  have hpost' : post = postC.map condOfCedar := hpost.symm
  obtain ⟨j, -, hstage⟩ := validate_cedarVersion hv hφ hps
  have hver : cedarVersion (q.withCondition pre ⟨k, .temporal φ⟩ post) pre post k e j = o := by
    have hid := congrArg Policy.id ho
    have hef := congrArg Policy.effect ho
    have hpsc := congrArg Policy.principalScope ho
    have hasc := congrArg Policy.actionScope ho
    have hrsc := congrArg Policy.resourceScope ho
    simp only [Policy.ofCedar, Policy.withCondition] at hid hef hpsc hasc hrsc
    obtain ⟨oid, oef, ops, oas, ors, ocond⟩ := o
    simp only at hoce hid hef hpsc hasc hrsc ⊢
    subst hoce hid hef hpsc hasc hrsc
    unfold cedarVersion
    simp only [Policy.lowerFrom, Policy.withCondition]
    rw [hpre', hpost', conditions_lowerFrom_ofCedar, conditions_lowerFrom_ofCedar]
  rw [hver, hA] at hstage
  -- Its Cedar policy is typed alike in each environment and its augmentation.
  have hscope : ∀ y ∈ [o.principalScope.toExpr, o.actionScope.toExpr, o.resourceScope.toExpr],
      (Expr.ofCedar y).ReadsContext P.hoistedNames := by
    have hpsc := congrArg Policy.principalScope ho
    have hasc := congrArg Policy.actionScope ho
    have hrsc := congrArg Policy.resourceScope ho
    simp only [Policy.ofCedar, Policy.withCondition] at hpsc hasc hrsc
    intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl
    · rw [hpsc]; exact hrps
    · rw [hasc]; exact hras
    · rw [hrsc]; exact hrrs
  have hcondC : ∀ d ∈ preC ++ postC, (Expr.ofCedar d.toExpr).ReadsContext P.hoistedNames := by
    intro d hd
    rw [← condOfCedar_toExpr]
    refine hrcs _ ?_
    rcases List.mem_append.mp hd with hd | hd
    · exact List.mem_append_left _ (hpre' ▸ List.mem_map_of_mem hd)
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ (hpost' ▸ List.mem_map_of_mem hd))
  have hs : ∀ env ∈ P.actionSchema.environments,
      sig (typeOf (substituteAction env.reqty.action o.toExpr) ∅ env) =
        sig (typeOf (substituteAction env.reqty.action o.toExpr) ∅
          (augmentEnv P.actionSchema P.leafTypes env)) := by
    intro env₀ henv₀
    have hA' := envAgree_augment (H := P.leafTypes) henv₀ hH
    rw [substituteAction_eq, policy_toExpr_split o hoce, mapOnVars_andChain]
    refine andChain_agree hA' _ ∅ (fun x hx => ?_) (fun ca hr => ?_)
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      refine readsContext_mapOnVars _ _ ?_
      rcases List.mem_append.mp hy with hy | hy
      · exact hscope y hy
      · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hy
        exact hcondC d (List.mem_append_left _ hd)
    · refine readsContext_mapOnVars _ _ ?_
      -- Where the typing reaches the leaf's condition, the scope admits the environment, so the
      -- leaf is well-typed there and reads only declared context attributes.
      rw [List.map_append] at hr
      obtain ⟨cb, hrs, -⟩ := reaches_append _ _ _ _ hr
      have hadm := admits_of_reaches (A := P.actionSchema)
        (q := q.withCondition pre ⟨k, .temporal φ⟩ post)
        (by rw [show (augmentEnv P.actionSchema P.leafTypes env₀).ets = env₀.ets from rfl,
          environments_ets henv₀])
        augmentEnv_maybeDescendentOf (augmentEnv_descendentOf henv₀)
        (by rw [augmentEnv_contains henv₀, environments_acts henv₀]
            exact environments_action (env := env₀) henv₀)
        (by
          have hpsc := congrArg Policy.principalScope ho
          have hasc := congrArg Policy.actionScope ho
          have hrsc := congrArg Policy.resourceScope ho
          simp only [Policy.ofCedar, Policy.withCondition] at hpsc hasc hrsc
          simp only [Policy.withCondition, ← hpsc, ← hasc, ← hrsc]
          exact hrs)
      have henvq : env₀ ∈ P.envsOf (q.withCondition pre ⟨k, .temporal φ⟩ post) :=
        List.mem_filter.mpr ⟨henv₀, hadm⟩
      obtain ⟨F, hmemF, -⟩ := mem_leafFacts_withCondition (q := q) (pre := pre) (post := post)
        (k := k) (φ := φ)
      have hwt₀ := (hv.temporal _ hq'mem φ F hmemF).wellTyped env₀ henvq
      have hfresh : ∀ a ∈ P.hoistedNames,
          (P.typingCtx env₀ F).env.reqty.context.find? a = none := by
        intro a ha
        obtain ⟨act, entry, _, _, hmem, -, -, rfl⟩ := mem_environments.mp henv₀
        exact hv.namesFresh (act, entry) hmem a ha
      have he := readsContext_toTemporal hfresh e φ hφ hwt₀
      have hck' : (⟨k, e⟩ : Cedar.Spec.Condition).toExpr = Cedar.Spec.Condition.toExpr ⟨k, e⟩ := rfl
      have hce : (Expr.ofCedar (Cedar.Spec.Condition.toExpr ⟨k, e⟩)).ReadsContext
          P.hoistedNames := by
        cases k <;> simpa [Cedar.Spec.Condition.toExpr, Expr.ofCedar, Expr.ReadsContext] using he
      cases postC with
      | nil => exact hce
      | cons d ds =>
        simp only [condTail, Expr.ofCedar, Expr.ReadsContext]
        refine ⟨hce, ?_⟩
        rw [← Conditions.toExpr_ofCedar, readsContext_conditions]
        intro d' hd'
        obtain ⟨d'', hd'', rfl⟩ := List.mem_map.mp hd'
        have := hcondC d'' (List.mem_append_right _ hd'')
        rwa [← condOfCedar_toExpr] at this
  have hoid : o.id = q.id := by
    have := congrArg Policy.id ho
    simpa [Policy.ofCedar, Policy.withCondition] using this
  have hO := (typecheckPolicyWithEnvironments_unaugment hH hs).2 hstage
  rw [hoid] at hO
  -- Cedar validates the rules in order.
  unfold Cedar.Validation.validate
  exact forM_append_cons (fun p hp => hother p (List.mem_append_left _ hp))
    (fun p hp => hother p (List.mem_append_right _ hp)) hO

end

end Dogwood.Thm
