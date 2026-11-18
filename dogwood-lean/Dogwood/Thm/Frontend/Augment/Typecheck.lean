import Cedar.Validation
import Cedar.Thm.Data.List

/-!
# Cedar's typechecker sees only the context attributes an expression reads

Cedar's typechecker (`Cedar.Validation.typeOf`) reads the request context through its record
type. An expression that reads the context only through attribute accesses and `has` tests
(`ReadsOnly R`) of attributes in `R` typechecks alike, with the same result type and
capabilities, in two environments that agree on everything but the context record type, and on
it at the attributes in `R` (`typeOf_agree`). This is what makes the crate's action-selective
augmentation and the specification's all-action augmentation give a rule the same validation
verdict when, at each action, it reads only attributes on which the two contexts agree or its
action scope excludes the action (`validate_selective_agrees`).
-/

namespace Dogwood.Frontend.Augment.Typecheck

open Cedar.Spec Cedar.Validation Cedar.Data

/-! ## What an expression reads of the context -/

mutual

/-- The expression reads the context only as `context.a`, `context has a` or `context has a.b…`,
with `a ∈ R`. -/
def ReadsOnly (R : List Attr) : Expr → Prop
  | .lit _ => True
  | .var v => v ≠ .context
  | .getAttr (.var .context) a => a ∈ R
  | .hasAttr (.var .context) a => a ∈ R
  | .extHasAttr (.var .context) a _ => a ∈ R
  | .getAttr x _ => ReadsOnly R x
  | .hasAttr x _ => ReadsOnly R x
  | .extHasAttr x _ _ => ReadsOnly R x
  | .unaryApp _ x => ReadsOnly R x
  | .ite a b c => ReadsOnly R a ∧ ReadsOnly R b ∧ ReadsOnly R c
  | .and a b => ReadsOnly R a ∧ ReadsOnly R b
  | .or a b => ReadsOnly R a ∧ ReadsOnly R b
  | .binaryApp _ a b => ReadsOnly R a ∧ ReadsOnly R b
  | .set xs => ReadsOnlyList R xs
  | .call _ xs => ReadsOnlyList R xs
  | .record axs => ReadsOnlyRecord R axs

def ReadsOnlyList (R : List Attr) : List Expr → Prop
  | [] => True
  | x :: xs => ReadsOnly R x ∧ ReadsOnlyList R xs

def ReadsOnlyRecord (R : List Attr) : List (Attr × Expr) → Prop
  | [] => True
  | (_, x) :: axs => ReadsOnly R x ∧ ReadsOnlyRecord R axs

end

theorem readsOnlyList_mem {R : List Attr} :
    ∀ {xs : List Expr}, ReadsOnlyList R xs → ∀ x ∈ xs, ReadsOnly R x
  | [], _, _, hx => by simp at hx
  | y :: ys, h, x, hx => by
    simp only [ReadsOnlyList] at h
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h.1
    · exact readsOnlyList_mem h.2 x hx

theorem readsOnlyRecord_mem {R : List Attr} :
    ∀ {axs : List (Attr × Expr)}, ReadsOnlyRecord R axs → ∀ p ∈ axs, ReadsOnly R p.2
  | [], _, _, hx => by simp at hx
  | (a, y) :: ys, h, p, hp => by
    simp only [ReadsOnlyRecord] at h
    rcases List.mem_cons.mp hp with rfl | hp
    · exact h.1
    · exact readsOnlyRecord_mem h.2 p hp

/-! ## Environments that differ only in the context -/

/-- Two typing environments that agree on everything the typechecker reads but the context
record type. -/
structure SameExceptContext (env₁ env₂ : TypeEnv) : Prop where
  ets : env₁.ets = env₂.ets
  principal : env₁.reqty.principal = env₂.reqty.principal
  action : env₁.reqty.action = env₂.reqty.action
  resource : env₁.reqty.resource = env₂.reqty.resource
  contains : ∀ uid, env₁.acts.contains uid = env₂.acts.contains uid
  descendentOf : ∀ u₁ u₂, env₁.acts.descendentOf u₁ u₂ = env₂.acts.descendentOf u₁ u₂
  actionType : ∀ ety, env₁.acts.actionType? ety = env₂.acts.actionType? ety
  maybeDescendentOf : ∀ e₁ e₂, env₁.acts.maybeDescendentOf e₁ e₂ = env₂.acts.maybeDescendentOf e₁ e₂

/-- Two typing results agree: both fail, or both succeed with the same type and capabilities. -/
def Agree {α : Type} (ty : α → CedarType) : Except TypeError (α × Capabilities) →
    Except TypeError (α × Capabilities) → Prop
  | .ok p₁, .ok p₂ => ty p₁.1 = ty p₂.1 ∧ p₁.2 = p₂.2
  | .error _, .error _ => True
  | _, _ => False

theorem agree_refl {α : Type} (ty : α → CedarType) (r : Except TypeError (α × Capabilities)) :
    Agree ty r r := by
  cases r <;> simp [Agree]

theorem agree_of_eq {α : Type} {ty : α → CedarType} {r₁ r₂ : Except TypeError (α × Capabilities)}
    (h : r₁ = r₂) : Agree ty r₁ r₂ := h ▸ agree_refl ty r₁

theorem bind_agree {α β : Type} {ty : α → CedarType} {ty' : β → CedarType}
    {r r' : Except TypeError (α × Capabilities)}
    {k k' : α × Capabilities → Except TypeError (β × Capabilities)} (h : Agree ty r r')
    (hk : ∀ p p', ty p.1 = ty p'.1 → p.2 = p'.2 → Agree ty' (k p) (k' p')) :
    Agree ty' (r >>= k) (r' >>= k') := by
  cases r with
  | error e => cases r' with
    | error _ => simp [Agree, bind, Except.bind]
    | ok _ => simp [Agree] at h
  | ok p => cases r' with
    | error _ => simp [Agree] at h
    | ok p' => simp only [bind, Except.bind]; exact hk p p' h.1 h.2

/-! ## The typechecker's parts -/

section
variable {env₁ env₂ : TypeEnv}

theorem typeOfLit_eq (h : SameExceptContext env₁ env₂) (p : Prim) :
    typeOfLit p env₁ = typeOfLit p env₂ := by
  rcases p with b | i | s | uid
  · cases b <;> rfl
  · rfl
  · rfl
  · simp [typeOfLit, h.ets, h.contains]

theorem typeOfVar_eq (h : SameExceptContext env₁ env₂) (v : Var) (hv : v ≠ .context) :
    typeOfVar v env₁ = typeOfVar v env₂ := by
  cases v <;> simp_all [typeOfVar, h.principal, h.action, h.resource]

end

theorem typeOfIf_agree {r₁ r₁' : TypedExpr × Capabilities} {r₂ r₂' r₃ r₃' : ResultType}
    (h₁ : r₁.1.typeOf = r₁'.1.typeOf) (hc : r₁.2 = r₁'.2) (h₂ : Agree TypedExpr.typeOf r₂ r₂')
    (h₃ : Agree TypedExpr.typeOf r₃ r₃') :
    Agree TypedExpr.typeOf (typeOfIf r₁ r₂ r₃) (typeOfIf r₁' r₂' r₃') := by
  obtain ⟨t₁, c₁⟩ := r₁
  obtain ⟨t₁', c₁'⟩ := r₁'
  simp only at h₁ hc
  subst hc
  unfold typeOfIf
  simp only [h₁]
  split
  · cases r₂ <;> cases r₂' <;> simp_all [Agree, ok, bind, Except.bind, TypedExpr.typeOf]
  · cases r₃ <;> cases r₃' <;> simp_all [Agree, ok, bind, Except.bind, TypedExpr.typeOf]
  · cases r₂ with
    | error e => cases r₂' <;> simp_all [Agree, bind, Except.bind]
    | ok p₂ =>
      cases r₂' with
      | error _ => simp_all [Agree]
      | ok p₂' =>
        cases r₃ with
        | error _ => cases r₃' <;> simp_all [Agree, bind, Except.bind]
        | ok p₃ =>
          cases r₃' with
          | error _ => simp_all [Agree]
          | ok p₃' =>
            obtain ⟨t₂, c₂⟩ := p₂
            obtain ⟨t₂', c₂'⟩ := p₂'
            obtain ⟨t₃, c₃⟩ := p₃
            obtain ⟨t₃', c₃'⟩ := p₃'
            obtain ⟨h2t, h2c⟩ := h₂
            obtain ⟨h3t, h3c⟩ := h₃
            simp only at h2t h2c h3t h3c
            subst h2c h3c
            simp only [bind, Except.bind]
            rw [h2t, h3t]
            cases t₂'.typeOf ⊔ t₃'.typeOf <;> simp [Agree, ok, err, TypedExpr.typeOf]
  · simp [Agree, err]

theorem typeOfAnd_agree {r₁ r₁' : TypedExpr × Capabilities} {r₂ r₂' : ResultType}
    (h₁ : r₁.1.typeOf = r₁'.1.typeOf) (hc : r₁.2 = r₁'.2) (h₂ : Agree TypedExpr.typeOf r₂ r₂') :
    Agree TypedExpr.typeOf (typeOfAnd r₁ r₂) (typeOfAnd r₁' r₂') := by
  obtain ⟨t₁, c₁⟩ := r₁
  obtain ⟨t₁', c₁'⟩ := r₁'
  simp only at h₁ hc
  subst hc
  unfold typeOfAnd
  simp only [h₁]
  split
  · simp [Agree, ok, h₁]
  · cases r₂ with
    | error _ => cases r₂' <;> simp_all [Agree, bind, Except.bind]
    | ok p₂ =>
      cases r₂' with
      | error _ => simp_all [Agree]
      | ok p₂' =>
        obtain ⟨t₂, c₂⟩ := p₂
        obtain ⟨t₂', c₂'⟩ := p₂'
        obtain ⟨h2t, h2c⟩ := h₂
        simp only at h2t h2c
        subst h2c
        simp only [bind, Except.bind]
        rw [h2t]
        split <;> simp [Agree, ok, err, TypedExpr.typeOf]
  · simp [Agree, err]

theorem typeOfOr_agree {r₁ r₁' : TypedExpr × Capabilities} {r₂ r₂' : ResultType}
    (h₁ : r₁.1.typeOf = r₁'.1.typeOf) (hc : r₁.2 = r₁'.2) (h₂ : Agree TypedExpr.typeOf r₂ r₂') :
    Agree TypedExpr.typeOf (typeOfOr r₁ r₂) (typeOfOr r₁' r₂') := by
  obtain ⟨t₁, c₁⟩ := r₁
  obtain ⟨t₁', c₁'⟩ := r₁'
  simp only at h₁ hc
  subst hc
  unfold typeOfOr
  simp only [h₁]
  split
  · simp [Agree, ok, h₁]
  all_goals first
    | simp [Agree, err]; done
    | (cases r₂ with
        | error _ => cases r₂' <;> simp_all [Agree, bind, Except.bind]
        | ok p₂ =>
          cases r₂' with
          | error _ => simp_all [Agree]
          | ok p₂' =>
            obtain ⟨t₂, c₂⟩ := p₂
            obtain ⟨t₂', c₂'⟩ := p₂'
            obtain ⟨h2t, h2c⟩ := h₂
            simp only at h2t h2c
            subst h2c
            simp only [bind, Except.bind]
            rw [h2t]
            split <;> simp [Agree, ok, err, TypedExpr.typeOf])

theorem typeOfUnaryApp_agree {op : UnaryOp} {t t' : TypedExpr} (h : t.typeOf = t'.typeOf) :
    Agree TypedExpr.typeOf (typeOfUnaryApp op t) (typeOfUnaryApp op t') := by
  unfold typeOfUnaryApp
  rw [h]
  split <;> simp [Agree, ok, err, TypedExpr.typeOf]

theorem typeOfEq_agree {t₁ t₁' t₂ t₂' : TypedExpr} {x₁ x₂ : Expr} (h₁ : t₁.typeOf = t₁'.typeOf)
    (h₂ : t₂.typeOf = t₂'.typeOf) :
    Agree TypedExpr.typeOf (typeOfEq t₁ t₂ x₁ x₂) (typeOfEq t₁' t₂' x₁ x₂) := by
  unfold typeOfEq
  rw [h₁, h₂]
  split
  · split <;> simp [Agree, ok, TypedExpr.typeOf]
  · split
    · simp [Agree, ok, TypedExpr.typeOf]
    · split <;> simp [Agree, ok, err, TypedExpr.typeOf]

section
variable {env₁ env₂ : TypeEnv}

theorem actionUID?_eq (h : SameExceptContext env₁ env₂) (x : Expr) :
    actionUID? x env₁.acts = actionUID? x env₂.acts := by
  simp [actionUID?, h.contains]

theorem typeEnv_descendentOf_eq (h : SameExceptContext env₁ env₂) (e₁ e₂ : EntityType) :
    env₁.descendentOf e₁ e₂ = env₂.descendentOf e₁ e₂ := by
  simp [TypeEnv.descendentOf, h.ets, h.maybeDescendentOf]

theorem typeOfInₑ_eq (h : SameExceptContext env₁ env₂) (e₁ e₂ : EntityType) (x₁ x₂ : Expr) :
    typeOfInₑ e₁ e₂ x₁ x₂ env₁ = typeOfInₑ e₁ e₂ x₁ x₂ env₂ := by
  simp [typeOfInₑ, actionUID?_eq h, h.descendentOf, typeEnv_descendentOf_eq h]

theorem typeOfInₛ_eq (h : SameExceptContext env₁ env₂) (e₁ e₂ : EntityType) (x₁ x₂ : Expr) :
    typeOfInₛ e₁ e₂ x₁ x₂ env₁ = typeOfInₛ e₁ e₂ x₁ x₂ env₂ := by
  simp [typeOfInₛ, actionUID?_eq h, h.descendentOf, typeEnv_descendentOf_eq h]

theorem typeOfHasTag_eq (h : SameExceptContext env₁ env₂) (ety : EntityType) (x t : Expr)
    (c : Capabilities) : typeOfHasTag ety x t c env₁ = typeOfHasTag ety x t c env₂ := by
  simp [typeOfHasTag, h.ets, h.actionType]

theorem typeOfGetTag_eq (h : SameExceptContext env₁ env₂) (ety : EntityType) (x t : Expr)
    (c : Capabilities) : typeOfGetTag ety x t c env₁ = typeOfGetTag ety x t c env₂ := by
  simp [typeOfGetTag, h.ets]

theorem typeOfBinaryApp_agree (h : SameExceptContext env₁ env₂) {op : BinaryOp}
    {t₁ t₁' t₂ t₂' : TypedExpr} {x₁ x₂ : Expr} {c : Capabilities} (h₁ : t₁.typeOf = t₁'.typeOf)
    (h₂ : t₂.typeOf = t₂'.typeOf) :
    Agree TypedExpr.typeOf (typeOfBinaryApp op t₁ t₂ x₁ x₂ c env₁)
      (typeOfBinaryApp op t₁' t₂' x₁ x₂ c env₂) := by
  unfold typeOfBinaryApp
  rw [h₁, h₂]
  split
  · exact typeOfEq_agree h₁ h₂
  · simp [Agree, ok, TypedExpr.typeOf, typeOfInₑ_eq h]
  · simp [Agree, ok, TypedExpr.typeOf, typeOfInₛ_eq h]
  · rw [typeOfHasTag_eq h]
    cases typeOfHasTag _ x₁ x₂ c env₂ <;> simp [Agree, ok, bind, Except.bind, TypedExpr.typeOf]
  · rw [typeOfGetTag_eq h]
    cases typeOfGetTag _ x₁ x₂ c env₂ <;> simp [Agree, ok, bind, Except.bind, TypedExpr.typeOf]
  all_goals first
    | simp [Agree, ok, err, TypedExpr.typeOf]; done
    | (rename_i ty₃ _; cases ifLubThenBool t₂'.typeOf ty₃ <;> simp [Agree, ok, bind, Except.bind, TypedExpr.typeOf])
    | (rename_i ty₃ ty₄ _ _; cases ifLubThenBool ty₃ ty₄ <;> simp [Agree, ok, bind, Except.bind, TypedExpr.typeOf])

theorem typeOfHasAttr_agree (h : SameExceptContext env₁ env₂) {t t' : TypedExpr} {x : Expr}
    {a : Attr} {c : Capabilities} (ht : t.typeOf = t'.typeOf) :
    Agree TypedExpr.typeOf (typeOfHasAttr t x a c env₁) (typeOfHasAttr t' x a c env₂) := by
  unfold typeOfHasAttr
  rw [ht]
  split
  · cases hasAttrInRecord _ x a c true <;> simp [Agree, ok, bind, Except.bind, TypedExpr.typeOf]
  · rw [h.ets, h.actionType]
    split
    · cases hasAttrInRecord _ x a c false <;> simp [Agree, ok, bind, Except.bind, TypedExpr.typeOf]
    · split <;> simp [Agree, ok, err, TypedExpr.typeOf]
  · simp [Agree, err]

theorem typeOfGetAttr_agree (h : SameExceptContext env₁ env₂) {t t' : TypedExpr} {x : Expr}
    {a : Attr} {c : Capabilities} (ht : t.typeOf = t'.typeOf) :
    Agree TypedExpr.typeOf (typeOfGetAttr t x a c env₁) (typeOfGetAttr t' x a c env₂) := by
  unfold typeOfGetAttr
  rw [ht]
  split
  · cases getAttrInRecord _ _ x a c <;> simp [Agree, ok, bind, Except.bind, TypedExpr.typeOf]
  · rw [h.ets]
    split
    · cases getAttrInRecord _ _ x a c <;> simp [Agree, ok, bind, Except.bind, TypedExpr.typeOf]
    · simp [Agree, err]
  · simp [Agree, err]

/-- `context has a`, where the two context record types agree at `a`. -/
theorem typeOfHasAttr_context_agree {a : Attr} {c : Capabilities}
    (hctx : env₁.reqty.context.find? a = env₂.reqty.context.find? a) :
    Agree TypedExpr.typeOf
      (typeOfHasAttr (.var .context (.record env₁.reqty.context)) (.var .context) a c env₁)
      (typeOfHasAttr (.var .context (.record env₂.reqty.context)) (.var .context) a c env₂) := by
  simp only [typeOfHasAttr, TypedExpr.typeOf, hasAttrInRecord, hctx]
  split
  · rename_i qty _
    by_cases hcap : (Expr.var Var.context, Key.attr a) ∈ c ∨ qty.isRequired = true <;>
      simp [hcap, Agree, ok, bind, Except.bind, TypedExpr.typeOf]
  · simp [Agree, ok, bind, Except.bind, TypedExpr.typeOf]

/-- `context.a`, where the two context record types agree at `a`. -/
theorem typeOfGetAttr_context_agree {a : Attr} {c : Capabilities}
    (hctx : env₁.reqty.context.find? a = env₂.reqty.context.find? a) :
    Agree TypedExpr.typeOf
      (typeOfGetAttr (.var .context (.record env₁.reqty.context)) (.var .context) a c env₁)
      (typeOfGetAttr (.var .context (.record env₂.reqty.context)) (.var .context) a c env₂) := by
  simp only [typeOfGetAttr, TypedExpr.typeOf, getAttrInRecord, hctx]
  split
  · simp [Agree, ok, bind, Except.bind, TypedExpr.typeOf]
  · split <;> simp [Agree, ok, err, bind, Except.bind, TypedExpr.typeOf]
  · simp [Agree, err, bind, Except.bind]

/-- `x has a.as` (Cedar 4.14's extended `has`), given that `x has a` and `x.a` typecheck alike
under every capability set, and that the rest of the path typechecks alike from operands of the
same type. -/
theorem typeOfExtHasAttr_agree_of {t t' : TypedExpr} {x : Expr} {a : Attr} {as : List Attr}
    (hhas : ∀ c, Agree TypedExpr.typeOf (typeOfHasAttr t x a c env₁) (typeOfHasAttr t' x a c env₂))
    (hget : ∀ c, Agree TypedExpr.typeOf (typeOfGetAttr t x a c env₁) (typeOfGetAttr t' x a c env₂))
    (hrest : ∀ (u u' : TypedExpr) c, u.typeOf = u'.typeOf →
      Agree (fun b => CedarType.bool b) (typeOfExtHasAttr u (.getAttr x a) as c env₁)
        (typeOfExtHasAttr u' (.getAttr x a) as c env₂))
    (c : Capabilities) :
    Agree (fun b => CedarType.bool b) (typeOfExtHasAttr t x (a :: as) c env₁)
      (typeOfExtHasAttr t' x (a :: as) c env₂) := by
  cases as with
  | nil =>
    simp only [typeOfExtHasAttr]
    refine bind_agree (hhas c) fun p p' hp hc => ?_
    obtain ⟨u, cu⟩ := p
    obtain ⟨u', cu'⟩ := p'
    simp only at hp hc ⊢
    subst hc
    rw [hp]
    split <;> simp [Agree]
  | cons b bs =>
    simp only [typeOfExtHasAttr]
    refine bind_agree (hhas c) fun p p' hp hc => ?_
    obtain ⟨u, cu⟩ := p
    obtain ⟨u', cu'⟩ := p'
    simp only at hp hc ⊢
    subst hc
    rw [hp]
    split
    · simp [Agree]
    · refine bind_agree (hget _) fun q q' hq _ => ?_
      obtain ⟨v, _⟩ := q
      obtain ⟨v', _⟩ := q'
      refine bind_agree (hrest v v' _ hq) fun r r' hr hrc => ?_
      obtain ⟨bty, cr⟩ := r
      obtain ⟨bty', cr'⟩ := r'
      simp only [CedarType.bool.injEq] at hr hrc
      subst hr hrc
      split <;> (try split) <;> simp [Agree]

/-- `x has as` (Cedar 4.14's extended `has`) typechecks alike from operands of the same type. -/
theorem typeOfExtHasAttr_agree (h : SameExceptContext env₁ env₂) :
    ∀ (as : List Attr) (x : Expr) (t t' : TypedExpr) (c : Capabilities), t.typeOf = t'.typeOf →
      Agree (fun b => CedarType.bool b) (typeOfExtHasAttr t x as c env₁)
        (typeOfExtHasAttr t' x as c env₂)
  | [], _, _, _, _, _ => by simp [typeOfExtHasAttr, Agree]
  | a :: as, x, t, t', c, ht =>
    typeOfExtHasAttr_agree_of (fun _ => typeOfHasAttr_agree h ht) (fun _ => typeOfGetAttr_agree h ht)
      (fun u u' c hu => typeOfExtHasAttr_agree h as (.getAttr x a) u u' c hu) c

/-- The typing of `x has a.as` from the typing of its path. -/
theorem extHasAttr_agree {r r' : Except TypeError (BoolType × Capabilities)} {u u' : TypedExpr}
    {a : Attr} {as : List Attr} (h : Agree (fun b => CedarType.bool b) r r') :
    Agree TypedExpr.typeOf
      (r >>= fun (p : BoolType × Capabilities) => ok (TypedExpr.extHasAttr u a as (.bool p.1)) p.2)
      (r' >>= fun (p : BoolType × Capabilities) => ok (TypedExpr.extHasAttr u' a as (.bool p.1)) p.2) := by
  cases r with
  | error e => cases r' with
    | error _ => simp [Agree, bind, Except.bind]
    | ok _ => simp [Agree] at h
  | ok p => cases r' with
    | error _ => simp [Agree] at h
    | ok p' =>
      obtain ⟨hp, hc⟩ := h
      simp [Agree, bind, Except.bind, ok, TypedExpr.typeOf, hp, hc]

end

theorem typeOfSet_agree {ts ts' : List TypedExpr} (h : ts.map TypedExpr.typeOf = ts'.map TypedExpr.typeOf) :
    Agree TypedExpr.typeOf (typeOfSet ts) (typeOfSet ts') := by
  unfold typeOfSet
  cases ts with
  | nil => cases ts' with
    | nil => simp [Agree, err]
    | cons _ _ => simp at h
  | cons hd tl =>
    cases ts' with
    | nil => simp at h
    | cons hd' tl' =>
      simp only [List.map_cons, List.cons.injEq] at h
      obtain ⟨hh, ht⟩ := h
      simp only [hh, ht]
      split <;> simp [Agree, ok, err, TypedExpr.typeOf]

theorem typeOfCall_agree {xfn : ExtFun} {ts ts' : List TypedExpr} {xs : List Expr}
    (h : ts.map TypedExpr.typeOf = ts'.map TypedExpr.typeOf) :
    Agree TypedExpr.typeOf (typeOfCall xfn ts xs) (typeOfCall xfn ts' xs) := by
  unfold typeOfCall
  rw [h]
  split <;> first
    | simp [Agree, ok, err, TypedExpr.typeOf]; done
    | (cases typeOfConstructor _ xs _ <;> simp [Agree, ok, bind, Except.bind, TypedExpr.typeOf])

/-! ## Binds -/

/-- Two results agree: both fail, or both succeed with the same image under `ty`. -/
def AgreeV {β γ : Type} (ty : β → γ) : Except TypeError β → Except TypeError β → Prop
  | .ok t, .ok t' => ty t = ty t'
  | .error _, .error _ => True
  | _, _ => False

theorem mapM_agree {α β γ : Type} {ty : β → γ} {xs : List α} {f f' : α → Except TypeError β}
    (h : ∀ x ∈ xs, AgreeV ty (f x) (f' x)) :
    AgreeV (List.map ty) (xs.mapM f) (xs.mapM f') := by
  induction xs with
  | nil => simp [AgreeV, pure, Except.pure]
  | cons x xs ih =>
    have hx := h x (List.mem_cons_self ..)
    have ih := ih fun y hy => h y (List.mem_cons_of_mem _ hy)
    simp only [List.mapM_cons]
    cases hfx : f x <;> cases hfx' : f' x <;> rw [hfx, hfx'] at hx <;> simp only [AgreeV] at hx
    · simp [AgreeV, bind, Except.bind]
    · cases hr : xs.mapM f <;> cases hr' : xs.mapM f' <;> rw [hr, hr'] at ih <;>
        simp_all [AgreeV, bind, Except.bind, pure, Except.pure]

theorem bindV_agree {α β γ : Type} {ty : α → γ} {ty' : β → CedarType}
    {r r' : Except TypeError α} {k k' : α → Except TypeError (β × Capabilities)}
    (h : AgreeV ty r r') (hk : ∀ t t', ty t = ty t' → Agree ty' (k t) (k' t')) :
    Agree ty' (r >>= k) (r' >>= k') := by
  cases r with
  | error e => cases r' with
    | error _ => simp [Agree, bind, Except.bind]
    | ok _ => simp [AgreeV] at h
  | ok p => cases r' with
    | error _ => simp [AgreeV] at h
    | ok p' => simp only [bind, Except.bind]; exact hk p p' h

theorem justType_agree {r r' : ResultType} (h : Agree TypedExpr.typeOf r r') :
    AgreeV TypedExpr.typeOf (justType r) (justType r') := by
  cases r <;> cases r' <;> simp_all [Agree, AgreeV, justType, Except.map]

theorem recordEntry_agree {r r' : Except TypeError (TypedExpr × Capabilities)} {a : Attr}
    (h : Agree TypedExpr.typeOf r r') :
    AgreeV (fun (p : Attr × TypedExpr) => (p.1, Qualified.required p.2.typeOf))
      (r.map (fun (ty, _) => (a, ty))) (r'.map (fun (ty, _) => (a, ty))) := by
  cases r <;> cases r' <;> simp_all [Agree, AgreeV, Except.map]

/-! ## The congruence -/

/-- **The typechecker sees only the context attributes an expression reads.** In two
environments that differ only in the context record type, and agree on it at the attributes in
`R`, an expression that reads the context only at attributes in `R` typechecks alike: both
typings fail, or both succeed with the same type and capabilities. -/
theorem typeOf_agree {env₁ env₂ : TypeEnv} (h : SameExceptContext env₁ env₂) (R : List Attr)
    (hctx : ∀ a ∈ R, env₁.reqty.context.find? a = env₂.reqty.context.find? a) :
    ∀ (x : Expr) (c : Capabilities), ReadsOnly R x →
      Agree TypedExpr.typeOf (typeOf x c env₁) (typeOf x c env₂)
  | .lit p, c, _ => by simp only [typeOf]; exact agree_of_eq (typeOfLit_eq h p)
  | .var v, c, hr => by
    simp only [ReadsOnly] at hr
    simp only [typeOf]; exact agree_of_eq (typeOfVar_eq h v hr)
  | .ite x₁ x₂ x₃, c, hr => by
    simp only [ReadsOnly] at hr
    simp only [typeOf]
    refine bind_agree (typeOf_agree h R hctx x₁ c hr.1) fun p p' ht hc => ?_
    obtain ⟨t, cp⟩ := p
    obtain ⟨t', cp'⟩ := p'
    simp only at ht hc ⊢
    subst hc
    exact typeOfIf_agree ht rfl (typeOf_agree h R hctx x₂ _ hr.2.1) (typeOf_agree h R hctx x₃ c hr.2.2)
  | .and x₁ x₂, c, hr => by
    simp only [ReadsOnly] at hr
    simp only [typeOf]
    refine bind_agree (typeOf_agree h R hctx x₁ c hr.1) fun p p' ht hc => ?_
    obtain ⟨t, cp⟩ := p
    obtain ⟨t', cp'⟩ := p'
    simp only at ht hc ⊢
    subst hc
    exact typeOfAnd_agree ht rfl (typeOf_agree h R hctx x₂ _ hr.2)
  | .or x₁ x₂, c, hr => by
    simp only [ReadsOnly] at hr
    simp only [typeOf]
    refine bind_agree (typeOf_agree h R hctx x₁ c hr.1) fun p p' ht hc => ?_
    obtain ⟨t, cp⟩ := p
    obtain ⟨t', cp'⟩ := p'
    simp only at ht hc ⊢
    subst hc
    exact typeOfOr_agree ht rfl (typeOf_agree h R hctx x₂ c hr.2)
  | .unaryApp op x₁, c, hr => by
    simp only [ReadsOnly] at hr
    simp only [typeOf]
    refine bind_agree (typeOf_agree h R hctx x₁ c hr) fun p p' ht _ => ?_
    obtain ⟨t, cp⟩ := p
    obtain ⟨t', cp'⟩ := p'
    exact typeOfUnaryApp_agree ht
  | .binaryApp op x₁ x₂, c, hr => by
    simp only [ReadsOnly] at hr
    simp only [typeOf]
    refine bind_agree (typeOf_agree h R hctx x₁ c hr.1) fun p p' ht _ => ?_
    obtain ⟨t, cp⟩ := p
    obtain ⟨t', cp'⟩ := p'
    refine bind_agree (typeOf_agree h R hctx x₂ c hr.2) fun q q' ht₂ _ => ?_
    obtain ⟨t₂, cq⟩ := q
    obtain ⟨t₂', cq'⟩ := q'
    exact typeOfBinaryApp_agree h ht ht₂
  | .getAttr x₁ a, c, hr => by
    by_cases hx : x₁ = .var .context
    · subst hx
      simp only [ReadsOnly] at hr
      simp only [typeOf, typeOfVar, ok, Function.comp, bind, Except.bind]
      exact typeOfGetAttr_context_agree (hctx a hr)
    · have hr' : ReadsOnly R x₁ := by
        cases x₁ with
        | var v => cases v <;> simp_all [ReadsOnly]
        | _ => simp_all [ReadsOnly]
      simp only [typeOf]
      refine bind_agree (typeOf_agree h R hctx x₁ c hr') fun p p' ht _ => ?_
      obtain ⟨t, cp⟩ := p
      obtain ⟨t', cp'⟩ := p'
      exact typeOfGetAttr_agree h ht
  | .hasAttr x₁ a, c, hr => by
    by_cases hx : x₁ = .var .context
    · subst hx
      simp only [ReadsOnly] at hr
      simp only [typeOf, typeOfVar, ok, Function.comp, bind, Except.bind]
      exact typeOfHasAttr_context_agree (hctx a hr)
    · have hr' : ReadsOnly R x₁ := by
        cases x₁ with
        | var v => cases v <;> simp_all [ReadsOnly]
        | _ => simp_all [ReadsOnly]
      simp only [typeOf]
      refine bind_agree (typeOf_agree h R hctx x₁ c hr') fun p p' ht _ => ?_
      obtain ⟨t, cp⟩ := p
      obtain ⟨t', cp'⟩ := p'
      exact typeOfHasAttr_agree h ht
  | .extHasAttr x₁ a as, c, hr => by
    by_cases hx : x₁ = .var .context
    · subst hx
      simp only [ReadsOnly] at hr
      simp only [typeOf, typeOfVar, ok, Function.comp]
      exact extHasAttr_agree (typeOfExtHasAttr_agree_of
        (fun _ => typeOfHasAttr_context_agree (hctx a hr))
        (fun _ => typeOfGetAttr_context_agree (hctx a hr))
        (fun u u' c hu => typeOfExtHasAttr_agree h as _ u u' c hu) c)
    · have hr' : ReadsOnly R x₁ := by
        cases x₁ with
        | var v => cases v <;> simp_all [ReadsOnly]
        | _ => simp_all [ReadsOnly]
      simp only [typeOf]
      refine bind_agree (typeOf_agree h R hctx x₁ c hr') fun p p' ht _ => ?_
      obtain ⟨t, cp⟩ := p
      obtain ⟨t', cp'⟩ := p'
      exact extHasAttr_agree (typeOfExtHasAttr_agree h (a :: as) x₁ t t' c ht)
  | .set xs, c, hr => by
    simp only [ReadsOnly] at hr
    simp only [typeOf, List.mapM₁_eq_mapM fun x => justType (typeOf x c env₁),
      List.mapM₁_eq_mapM fun x => justType (typeOf x c env₂)]
    refine bindV_agree (mapM_agree fun x hx => ?_) fun ts ts' hts => typeOfSet_agree hts
    have := List.sizeOf_lt_of_mem hx
    exact justType_agree (typeOf_agree h R hctx x c (readsOnlyList_mem hr x hx))
  | .call xfn xs, c, hr => by
    simp only [ReadsOnly] at hr
    simp only [typeOf, List.mapM₁_eq_mapM fun x => justType (typeOf x c env₁),
      List.mapM₁_eq_mapM fun x => justType (typeOf x c env₂)]
    refine bindV_agree (mapM_agree fun x hx => ?_) fun ts ts' hts => typeOfCall_agree hts
    have := List.sizeOf_lt_of_mem hx
    exact justType_agree (typeOf_agree h R hctx x c (readsOnlyList_mem hr x hx))
  | .record axs, c, hr => by
    simp only [ReadsOnly] at hr
    simp only [typeOf,
      List.mapM₂_eq_mapM fun (x : Attr × Expr) => (typeOf x.snd c env₁).map fun (ty, _) => (x.fst, ty),
      List.mapM₂_eq_mapM fun (x : Attr × Expr) => (typeOf x.snd c env₂).map fun (ty, _) => (x.fst, ty)]
    refine bindV_agree (mapM_agree (ty := fun (p : Attr × TypedExpr) => (p.1, Qualified.required p.2.typeOf))
      fun p hp => ?_) fun ts ts' hts => ?_
    · have h₁ := List.sizeOf_lt_of_mem hp
      have h₂ : sizeOf p.2 < sizeOf p := by obtain ⟨a, x⟩ := p; simp; omega
      exact recordEntry_agree (typeOf_agree h R hctx p.2 c (readsOnlyRecord_mem hr p hp))
    · exact ⟨congrArg (fun l => CedarType.record (Map.make l)) hts, rfl⟩
termination_by x => sizeOf x

/-! ## Policies -/

theorem readsOnly_getAttr_iff {R : List Attr} {y : Expr} {a : Attr} :
    ReadsOnly R (.getAttr y a) ↔ (y = .var .context ∧ a ∈ R) ∨ (y ≠ .var .context ∧ ReadsOnly R y) := by
  cases y with
  | var v => cases v <;> simp [ReadsOnly]
  | _ => simp [ReadsOnly]

theorem readsOnly_hasAttr_iff {R : List Attr} {y : Expr} {a : Attr} :
    ReadsOnly R (.hasAttr y a) ↔ (y = .var .context ∧ a ∈ R) ∨ (y ≠ .var .context ∧ ReadsOnly R y) := by
  cases y with
  | var v => cases v <;> simp [ReadsOnly]
  | _ => simp [ReadsOnly]

theorem readsOnly_extHasAttr_iff {R : List Attr} {y : Expr} {a : Attr} {as : List Attr} :
    ReadsOnly R (.extHasAttr y a as) ↔
      (y = .var .context ∧ a ∈ R) ∨ (y ≠ .var .context ∧ ReadsOnly R y) := by
  cases y with
  | var v => cases v <;> simp [ReadsOnly]
  | _ => simp [ReadsOnly]

/-- The variable substitution of `substituteAction`. -/
def actionSubst (uid : EntityUID) (var : Var) : Expr :=
  match var with
  | .action => .lit (.entityUID uid)
  | _ => .var var

theorem substituteAction_eq (uid : EntityUID) (x : Expr) :
    substituteAction uid x = mapOnVars (actionSubst uid) x := rfl

theorem mapOnVars_actionSubst_context {uid : EntityUID} {x : Expr}
    (h : mapOnVars (actionSubst uid) x = .var .context) : x = .var .context := by
  cases x with
  | var v => cases v <;> simp_all [mapOnVars, actionSubst]
  | _ => simp [mapOnVars] at h

theorem readsOnlyList_of_mem {R : List Attr} :
    ∀ {xs : List Expr}, (∀ x ∈ xs, ReadsOnly R x) → ReadsOnlyList R xs
  | [], _ => trivial
  | x :: _, h => ⟨h x (List.mem_cons_self ..), readsOnlyList_of_mem fun y hy => h y (List.mem_cons_of_mem _ hy)⟩

theorem readsOnlyRecord_of_mem {R : List Attr} :
    ∀ {axs : List (Attr × Expr)}, (∀ p ∈ axs, ReadsOnly R p.2) → ReadsOnlyRecord R axs
  | [], _ => trivial
  | (_, x) :: _, h =>
    ⟨h (_, x) (List.mem_cons_self ..), readsOnlyRecord_of_mem fun p hp => h p (List.mem_cons_of_mem _ hp)⟩

/-- Substituting the action keeps what an expression reads of the context. -/
theorem readsOnly_substituteAction {R : List Attr} (uid : EntityUID) :
    ∀ x, ReadsOnly R x → ReadsOnly R (mapOnVars (actionSubst uid) x)
  | .lit _, _ => by simp [mapOnVars, ReadsOnly]
  | .var v, hr => by cases v <;> simp_all [mapOnVars, actionSubst, ReadsOnly]
  | .ite a b c, hr => by
    simp only [ReadsOnly] at hr
    simp only [mapOnVars, ReadsOnly]
    exact ⟨readsOnly_substituteAction uid a hr.1, readsOnly_substituteAction uid b hr.2.1,
      readsOnly_substituteAction uid c hr.2.2⟩
  | .and a b, hr => by
    simp only [ReadsOnly] at hr
    simp only [mapOnVars, ReadsOnly]
    exact ⟨readsOnly_substituteAction uid a hr.1, readsOnly_substituteAction uid b hr.2⟩
  | .or a b, hr => by
    simp only [ReadsOnly] at hr
    simp only [mapOnVars, ReadsOnly]
    exact ⟨readsOnly_substituteAction uid a hr.1, readsOnly_substituteAction uid b hr.2⟩
  | .binaryApp _ a b, hr => by
    simp only [ReadsOnly] at hr
    simp only [mapOnVars, ReadsOnly]
    exact ⟨readsOnly_substituteAction uid a hr.1, readsOnly_substituteAction uid b hr.2⟩
  | .unaryApp _ a, hr => by
    simp only [ReadsOnly] at hr
    simp only [mapOnVars, ReadsOnly]
    exact readsOnly_substituteAction uid a hr
  | .getAttr x a, hr => by
    simp only [mapOnVars]
    rw [readsOnly_getAttr_iff] at hr ⊢
    rcases hr with ⟨rfl, ha⟩ | ⟨hx, hr⟩
    · left; simp [mapOnVars, actionSubst, ha]
    · right
      exact ⟨fun h => hx (mapOnVars_actionSubst_context h), readsOnly_substituteAction uid x hr⟩
  | .hasAttr x a, hr => by
    simp only [mapOnVars]
    rw [readsOnly_hasAttr_iff] at hr ⊢
    rcases hr with ⟨rfl, ha⟩ | ⟨hx, hr⟩
    · left; simp [mapOnVars, actionSubst, ha]
    · right
      exact ⟨fun h => hx (mapOnVars_actionSubst_context h), readsOnly_substituteAction uid x hr⟩
  | .extHasAttr x a as, hr => by
    simp only [mapOnVars]
    rw [readsOnly_extHasAttr_iff] at hr ⊢
    rcases hr with ⟨rfl, ha⟩ | ⟨hx, hr⟩
    · left; simp [mapOnVars, actionSubst, ha]
    · right
      exact ⟨fun h => hx (mapOnVars_actionSubst_context h), readsOnly_substituteAction uid x hr⟩
  | .set xs, hr => by
    simp only [ReadsOnly] at hr
    simp only [mapOnVars, ReadsOnly, List.map₁_eq_map (mapOnVars (actionSubst uid))]
    refine readsOnlyList_of_mem fun y hy => ?_
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    have := List.sizeOf_lt_of_mem hx
    exact readsOnly_substituteAction uid x (readsOnlyList_mem hr x hx)
  | .call _ xs, hr => by
    simp only [ReadsOnly] at hr
    simp only [mapOnVars, ReadsOnly, List.map₁_eq_map (mapOnVars (actionSubst uid))]
    refine readsOnlyList_of_mem fun y hy => ?_
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    have := List.sizeOf_lt_of_mem hx
    exact readsOnly_substituteAction uid x (readsOnlyList_mem hr x hx)
  | .record axs, hr => by
    simp only [ReadsOnly] at hr
    simp only [mapOnVars, ReadsOnly,
      List.map₂_eq_map fun (p : Attr × Expr) => (p.1, mapOnVars (actionSubst uid) p.2)]
    refine readsOnlyRecord_of_mem fun q hq => ?_
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
    have h₁ := List.sizeOf_lt_of_mem hp
    have h₂ : sizeOf p.2 < sizeOf p := by obtain ⟨a, x⟩ := p; simp; omega
    exact readsOnly_substituteAction uid p.2 (readsOnlyRecord_mem hr p hp)
termination_by x => sizeOf x

theorem readsOnly_scope {R : List Attr} (s : Scope) (v : Var) (hv : v ≠ .context) :
    ReadsOnly R (s.toExpr v) := by
  cases s <;> simp [Scope.toExpr, Var.eqEntityUID, Var.inEntityUID, Var.isEntityType, ReadsOnly, hv]

theorem readsOnly_actionScope {R : List Attr} (s : ActionScope) : ReadsOnly R s.toExpr := by
  cases s with
  | actionScope s => exact readsOnly_scope s .action (by simp)
  | actionInAny es =>
    simp only [ActionScope.toExpr, ReadsOnly, ne_eq, reduceCtorEq, not_false_eq_true, true_and]
    exact readsOnlyList_of_mem fun x hx => by
      obtain ⟨e, _, rfl⟩ := List.mem_map.mp hx; trivial

/-- The rule's action scope, with the environment's action substituted, typechecks as `false`,
or fails to typecheck, whatever the capabilities: the rule cannot apply to the environment's
action, and its typing there does not read the context. -/
def ScopeExcludes (p : Policy) (env : TypeEnv) : Prop :=
  ∀ c, (∃ tx c', typeOf (substituteAction env.reqty.action p.actionScope.toExpr) c env = .ok (tx, c') ∧
    tx.typeOf = .bool .ff) ∨
    ∃ e, typeOf (substituteAction env.reqty.action p.actionScope.toExpr) c env = .error e

/-- **A rule typechecks alike in two environments** that differ only in the context, when it
reads the context only at attributes on which they agree, or when its action scope excludes the
environment's action. -/
theorem typeOf_policy_agree {env₁ env₂ : TypeEnv} (h : SameExceptContext env₁ env₂) (p : Policy)
    (hp : (∃ R, ReadsOnly R p.toExpr ∧ ∀ a ∈ R, env₁.reqty.context.find? a = env₂.reqty.context.find? a) ∨
      ScopeExcludes p env₁) :
    Agree TypedExpr.typeOf (typeOf (substituteAction env₁.reqty.action p.toExpr) ∅ env₁)
      (typeOf (substituteAction env₂.reqty.action p.toExpr) ∅ env₂) := by
  rw [← h.action]
  rcases hp with ⟨R, hR, hctx⟩ | hex
  · exact typeOf_agree h R hctx _ ∅ (readsOnly_substituteAction _ _ hR)
  · have hnoctx : ∀ a ∈ ([] : List Attr), env₁.reqty.context.find? a = env₂.reqty.context.find? a := by
      simp
    have hP : ReadsOnly [] (mapOnVars (actionSubst env₁.reqty.action) p.principalScope.toExpr) := by
      apply readsOnly_substituteAction
      cases p.principalScope; exact readsOnly_scope _ _ (by simp)
    have hA : ReadsOnly [] (mapOnVars (actionSubst env₁.reqty.action) p.actionScope.toExpr) :=
      readsOnly_substituteAction _ _ (readsOnly_actionScope _)
    simp only [substituteAction_eq, Policy.toExpr, mapOnVars]
    simp only [typeOf]
    refine bind_agree (typeOf_agree h [] hnoctx _ ∅ hP) fun q q' ht hc => ?_
    obtain ⟨t, cq⟩ := q
    obtain ⟨t', cq'⟩ := q'
    simp only at ht hc ⊢
    subst hc
    refine typeOfAnd_agree ht rfl ?_
    rcases hex (∅ ∪ cq) with ⟨tx, c', hx, hff⟩ | ⟨e, hx⟩
    rotate_left
    · rw [substituteAction_eq] at hx
      have hagree := typeOf_agree h [] hnoctx _ (∅ ∪ cq) hA
      rw [hx] at hagree
      cases hx' : typeOf (mapOnVars (actionSubst env₁.reqty.action) p.actionScope.toExpr) (∅ ∪ cq) env₂ with
      | ok _ => rw [hx'] at hagree; simp [Agree] at hagree
      | error e' =>
        rw [hx]
        simp [Agree, bind, Except.bind]
    rw [substituteAction_eq] at hx
    have hagree := typeOf_agree h [] hnoctx _ (∅ ∪ cq) hA
    rw [hx] at hagree
    cases hx' : typeOf (mapOnVars (actionSubst env₁.reqty.action) p.actionScope.toExpr) (∅ ∪ cq) env₂ with
    | error _ => rw [hx'] at hagree; simp [Agree] at hagree
    | ok q₂ =>
      rw [hx'] at hagree
      obtain ⟨tx', c''⟩ := q₂
      simp only [Agree] at hagree
      obtain ⟨hty, rfl⟩ := hagree
      rw [hx]
      simp only [bind, Except.bind, typeOfAnd, hff, ← hty]
      simp [Agree, ok, hff, ← hty]

/-- Two policy typings give the same verdict: both fail, or both succeed with the same type. -/
def SameVerdict {ε : Type} : Except ε TypedExpr → Except ε TypedExpr → Prop
  | .ok t, .ok t' => t.typeOf = t'.typeOf
  | .error _, .error _ => True
  | _, _ => False

/-- **Cedar's policy typecheck gives the same verdict** in two environments that differ only in
the context, under the conditions of `typeOf_policy_agree`. -/
theorem typecheckPolicy_agree {env₁ env₂ : TypeEnv} (h : SameExceptContext env₁ env₂) (p : Policy)
    (hp : (∃ R, ReadsOnly R p.toExpr ∧ ∀ a ∈ R, env₁.reqty.context.find? a = env₂.reqty.context.find? a) ∨
      ScopeExcludes p env₁) :
    SameVerdict (typecheckPolicy p env₁) (typecheckPolicy p env₂) := by
  have hag := typeOf_policy_agree h p hp
  unfold typecheckPolicy
  have e : (∅ : Capabilities) = [] := rfl
  rw [e] at hag
  simp only
  cases h₁ : typeOf (substituteAction env₁.reqty.action p.toExpr) [] env₁ <;>
    cases h₂ : typeOf (substituteAction env₂.reqty.action p.toExpr) [] env₂ <;>
    rw [h₁, h₂] at hag <;> simp only [Agree] at hag
  · simp [SameVerdict]
  · rename_i q₁ q₂
    obtain ⟨t₁, c₁⟩ := q₁
    obtain ⟨t₂, c₂⟩ := q₂
    simp only [hag.1]
    split <;> simp [SameVerdict, hag.1]

/-! ## Schemas that differ only in the contexts -/

/-- What an action entry gives the typechecker besides its context. -/
def entrySkeleton (e : ActionSchemaEntry) : Set EntityType × Set EntityType × Set EntityUID :=
  (e.appliesToPrincipal, e.appliesToResource, e.ancestors)

/-- Two action entries, in the same position, are for the same action and agree but in their
contexts. -/
def SkelRel (q₁ q₂ : EntityUID × ActionSchemaEntry) : Prop :=
  q₁.1 = q₂.1 ∧ entrySkeleton q₁.2 = entrySkeleton q₂.2

/-- Two schemas with the same entity types and the same actions, in the same order, each with
the same principal and resource types and ancestors: they differ at most in the actions'
contexts. -/
structure SameSkeleton (A₁ A₂ : Schema) : Prop where
  ets : A₁.ets = A₂.ets
  acts : List.Forall₂ SkelRel A₁.acts.toList A₂.acts.toList

/-- Two optional entries are both absent, or both present with the same skeleton. -/
def OptSkel : Option ActionSchemaEntry → Option ActionSchemaEntry → Prop
  | some e₁, some e₂ => entrySkeleton e₁ = entrySkeleton e₂
  | none, none => True
  | _, _ => False

theorem find?_skel {L₁ L₂ : List (EntityUID × ActionSchemaEntry)} (h : List.Forall₂ SkelRel L₁ L₂)
    (uid : EntityUID) :
    OptSkel ((L₁.find? fun q => q.1 == uid).map Prod.snd) ((L₂.find? fun q => q.1 == uid).map Prod.snd) := by
  induction h with
  | nil => simp [OptSkel]
  | cons hq _ ih =>
    rename_i q₁ q₂ _ _
    obtain ⟨hk, hs⟩ := hq
    simp only [List.find?_cons, hk]
    split
    · simp [OptSkel, hs]
    · exact ih

theorem acts_find?_skel {A₁ A₂ : Schema} (h : SameSkeleton A₁ A₂) (uid : EntityUID) :
    OptSkel (A₁.acts.find? uid) (A₂.acts.find? uid) := by
  have := find?_skel h.acts uid
  have e : ∀ (A : Schema), A.acts.find? uid = (A.acts.toList.find? fun q => q.1 == uid).map Prod.snd := by
    intro A
    simp only [Map.find?]
    cases hf : (A.acts.toList.find? fun q => q.1 == uid) with
    | none => simp
    | some q => obtain ⟨k, v⟩ := q; simp
  rw [e A₁, e A₂]; exact this

theorem acts_contains_eq {A₁ A₂ : Schema} (h : SameSkeleton A₁ A₂) (uid : EntityUID) :
    A₁.acts.contains uid = A₂.acts.contains uid := by
  have := acts_find?_skel h uid
  simp only [ActionSchema.contains]
  cases h₁ : A₁.acts.find? uid <;> cases h₂ : A₂.acts.find? uid <;> rw [h₁, h₂] at this <;>
    simp_all [OptSkel]

theorem acts_descendentOf_eq {A₁ A₂ : Schema} (h : SameSkeleton A₁ A₂) (u₁ u₂ : EntityUID) :
    A₁.acts.descendentOf u₁ u₂ = A₂.acts.descendentOf u₁ u₂ := by
  have := acts_find?_skel h u₁
  simp only [ActionSchema.descendentOf]
  cases h₁ : A₁.acts.find? u₁ <;> cases h₂ : A₂.acts.find? u₁ <;> rw [h₁, h₂] at this <;>
    simp_all [OptSkel, entrySkeleton]

theorem keys_eq {L₁ L₂ : List (EntityUID × ActionSchemaEntry)} (h : List.Forall₂ SkelRel L₁ L₂) :
    L₁.map Prod.fst = L₂.map Prod.fst := by
  induction h with
  | nil => rfl
  | cons hq _ ih => simp [hq.1, ih]

theorem acts_actionType_eq {A₁ A₂ : Schema} (h : SameSkeleton A₁ A₂) (ety : EntityType) :
    A₁.acts.actionType? ety = A₂.acts.actionType? ety := by
  simp only [ActionSchema.actionType?, Map.keys, Set.any, Set.elts, keys_eq h.acts]

theorem acts_maybeDescendentOf_eq {A₁ A₂ : Schema} (h : SameSkeleton A₁ A₂) (e₁ e₂ : EntityType) :
    A₁.acts.maybeDescendentOf e₁ e₂ = A₂.acts.maybeDescendentOf e₁ e₂ := by
  simp only [ActionSchema.maybeDescendentOf]
  have hs := h.acts
  generalize A₁.acts.toList = L₁ at hs ⊢
  generalize A₂.acts.toList = L₂ at hs ⊢
  induction hs with
  | nil => rfl
  | cons hq _ ih =>
    obtain ⟨hk, hsk⟩ := hq
    simp only [entrySkeleton, Prod.mk.injEq] at hsk
    simp [List.any_cons, hk, hsk.2.2, ih]

/-! ## Position-wise relations -/

theorem forall₂_append {α β : Type} {R : α → β → Prop} :
    ∀ {a : List α} {b : List β} {c : List α} {d : List β},
      List.Forall₂ R a b → List.Forall₂ R c d → List.Forall₂ R (a ++ c) (b ++ d)
  | [], [], _, _, .nil, h => h
  | _ :: _, _ :: _, _, _, .cons hab h, hcd => .cons hab (forall₂_append h hcd)

theorem forall₂_flatMap {α β γ δ : Type} {R : α → β → Prop} {S : γ → δ → Prop}
    {f : α → List γ} {g : β → List δ} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ →
      (∀ a b, a ∈ l₁ → b ∈ l₂ → R a b → List.Forall₂ S (f a) (g b)) →
      List.Forall₂ S (l₁.flatMap f) (l₂.flatMap g)
  | [], [], .nil, _ => .nil
  | a :: l₁, b :: l₂, .cons hab h, hS => by
    simp only [List.flatMap_cons]
    exact forall₂_append (hS a b (List.mem_cons_self ..) (List.mem_cons_self ..) hab)
      (forall₂_flatMap h fun a' b' ha hb hr =>
        hS a' b' (List.mem_cons_of_mem _ ha) (List.mem_cons_of_mem _ hb) hr)

theorem forall₂_map_same {α γ δ : Type} {R : γ → δ → Prop} {f : α → γ} {g : α → δ} :
    ∀ {l : List α}, (∀ x ∈ l, R (f x) (g x)) → List.Forall₂ R (l.map f) (l.map g)
  | [], _ => .nil
  | x :: _, h => .cons (h x (List.mem_cons_self ..)) (forall₂_map_same fun y hy => h y (List.mem_cons_of_mem _ hy))

theorem forall₂_map {α β γ δ : Type} {R : γ → δ → Prop} {f : α → γ} {g : β → δ} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ (fun x y => R (f x) (g y)) l₁ l₂ →
      List.Forall₂ R (l₁.map f) (l₂.map g)
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons h t => .cons h (forall₂_map t)

/-! ## The environments of two such schemas -/

/-- Two environments of two schemas with the same skeleton, in the same position: they differ
only in the context, which is that of two corresponding action entries. -/
def EnvPair (A₁ A₂ : Schema) (env₁ env₂ : TypeEnv) : Prop :=
  SameExceptContext env₁ env₂ ∧ env₁.acts = A₁.acts ∧ env₁.ets = A₁.ets ∧
    ∃ q₁ q₂, q₁ ∈ A₁.acts.toList ∧ q₂ ∈ A₂.acts.toList ∧ SkelRel q₁ q₂ ∧
      env₁.reqty.action = q₁.1 ∧ env₁.reqty.context = q₁.2.context ∧
      env₂.reqty.context = q₂.2.context

/-- The environments of a schema, unfolded: one per action, principal type and resource type. -/
theorem environments_eq (A : Schema) : A.environments = (A.acts.toList.flatMap fun (a, e) =>
    (e.appliesToPrincipal.toList.product e.appliesToResource.toList).map fun (p, r) =>
      ({ principal := p, action := a, resource := r, context := e.context } : RequestType)).map
      fun r => { ets := A.ets, acts := A.acts, reqty := r } := rfl

theorem environments_pair {A₁ A₂ : Schema} (h : SameSkeleton A₁ A₂) :
    List.Forall₂ (EnvPair A₁ A₂) A₁.environments A₂.environments := by
  rw [environments_eq, environments_eq]
  apply forall₂_map
  refine forall₂_flatMap h.acts fun q₁ q₂ hq₁ hq₂ hrel => ?_
  obtain ⟨a₁, e₁⟩ := q₁
  obtain ⟨a₂, e₂⟩ := q₂
  obtain ⟨hk, hsk⟩ := hrel
  simp only at hk; subst hk
  simp only [entrySkeleton, Prod.mk.injEq] at hsk
  obtain ⟨hp, hr, _⟩ := hsk
  simp only
  rw [hp, hr]
  refine forall₂_map_same fun x _ => ?_
  refine ⟨?_, rfl, rfl, (a₁, e₁), (a₁, e₂), hq₁, hq₂, ⟨rfl, ?_⟩, rfl, rfl, rfl⟩
  · exact { ets := h.ets, principal := rfl, action := rfl, resource := rfl,
            contains := acts_contains_eq h, descendentOf := acts_descendentOf_eq h,
            actionType := acts_actionType_eq h, maybeDescendentOf := acts_maybeDescendentOf_eq h }
  · simp [entrySkeleton, *]

/-! ## Validation -/

/-- The entity check of a policy looks only at what two schemas with the same skeleton share. -/
theorem checkEntities_eq {A₁ A₂ : Schema} (h : SameSkeleton A₁ A₂) :
    ∀ x, checkEntities A₁ x = checkEntities A₂ x
  | .lit (.entityUID uid) => by simp [checkEntities, h.ets, acts_contains_eq h]
  | .unaryApp (.is ety) x₁ => by
    simp only [checkEntities, h.ets, acts_actionType_eq h, checkEntities_eq h x₁]
  | .lit (.bool _) => by simp [checkEntities]
  | .lit (.int _) => by simp [checkEntities]
  | .lit (.string _) => by simp [checkEntities]
  | .var _ => by simp [checkEntities]
  | .ite x₁ x₂ x₃ => by
    simp only [checkEntities, checkEntities_eq h x₁, checkEntities_eq h x₂, checkEntities_eq h x₃]
  | .binaryApp _ x₁ x₂ => by simp only [checkEntities, checkEntities_eq h x₁, checkEntities_eq h x₂]
  | .and x₁ x₂ => by simp only [checkEntities, checkEntities_eq h x₁, checkEntities_eq h x₂]
  | .or x₁ x₂ => by simp only [checkEntities, checkEntities_eq h x₁, checkEntities_eq h x₂]
  | .getAttr x₁ _ => by simp only [checkEntities, checkEntities_eq h x₁]
  | .hasAttr x₁ _ => by simp only [checkEntities, checkEntities_eq h x₁]
  | .extHasAttr x₁ _ _ => by simp only [checkEntities, checkEntities_eq h x₁]
  | .unaryApp .not x₁ => by simp only [checkEntities, checkEntities_eq h x₁]
  | .unaryApp .neg x₁ => by simp only [checkEntities, checkEntities_eq h x₁]
  | .unaryApp .isEmpty x₁ => by simp only [checkEntities, checkEntities_eq h x₁]
  | .unaryApp (.like _) x₁ => by simp only [checkEntities, checkEntities_eq h x₁]
  | .call _ xs => by
    simp only [checkEntities]
    congr 1
    funext ⟨x, hx⟩
    have := List.sizeOf_lt_of_mem hx
    exact checkEntities_eq h x
  | .set xs => by
    simp only [checkEntities]
    congr 1
    funext ⟨x, hx⟩
    have := List.sizeOf_lt_of_mem hx
    exact checkEntities_eq h x
  | .record axs => by
    simp only [checkEntities]
    congr 1
    funext ⟨x, hx⟩
    exact checkEntities_eq h x.2
termination_by x => sizeOf x

/-- Two typings of a list of policies' environments agree: both fail, or both succeed with the
same types. -/
def SameVerdicts {ε : Type} : Except ε (List TypedExpr) → Except ε (List TypedExpr) → Prop
  | .ok ts, .ok ts' => ts.map TypedExpr.typeOf = ts'.map TypedExpr.typeOf
  | .error _, .error _ => True
  | _, _ => False

theorem mapM_sameVerdicts {α β ε : Type} {f : α → Except ε TypedExpr} {g : β → Except ε TypedExpr} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ (fun a b => SameVerdict (f a) (g b)) l₁ l₂ →
      SameVerdicts (l₁.mapM f) (l₂.mapM g)
  | [], [], .nil => by simp [SameVerdicts, pure, Except.pure]
  | a :: l₁, b :: l₂, .cons hab t => by
    have ih := mapM_sameVerdicts t
    simp only [List.mapM_cons]
    cases hfa : f a <;> cases hgb : g b <;> rw [hfa, hgb] at hab <;> simp only [SameVerdict] at hab
    · simp [SameVerdicts, bind, Except.bind]
    · cases hr : l₁.mapM f <;> cases hr' : l₂.mapM g <;> rw [hr, hr'] at ih <;>
        simp_all [SameVerdicts, bind, Except.bind, pure, Except.pure]

theorem allFalse_eq {ts ts' : List TypedExpr} (h : ts.map TypedExpr.typeOf = ts'.map TypedExpr.typeOf) :
    allFalse ts = allFalse ts' := by
  have e : ∀ l : List TypedExpr, allFalse l = (l.map TypedExpr.typeOf).all (· == .bool .ff) := by
    intro l; simp [allFalse, List.all_map, Function.comp_def]
  rw [e, e, h]

/-- **Cedar validates a rule alike against two schemas that differ only in their actions'
contexts**, when, at every action, either the rule reads the context only at attributes on which
the two contexts agree, or its action scope excludes the action. -/
theorem typecheckPolicyWithEnvironments_agree {A₁ A₂ : Schema} (h : SameSkeleton A₁ A₂) (p : Policy)
    (hp : ∀ q₁ ∈ A₁.acts.toList, ∀ q₂ ∈ A₂.acts.toList, SkelRel q₁ q₂ →
      (∃ R, ReadsOnly R p.toExpr ∧ ∀ a ∈ R, q₁.2.context.find? a = q₂.2.context.find? a) ∨
      (∀ env : TypeEnv, env.acts = A₁.acts → env.ets = A₁.ets → env.reqty.action = q₁.1 →
        ScopeExcludes p env)) :
    (typecheckPolicyWithEnvironments typecheckPolicy p A₁).toBool =
      (typecheckPolicyWithEnvironments typecheckPolicy p A₂).toBool := by
  have hverd : SameVerdicts (A₁.environments.mapM (typecheckPolicy p))
      (A₂.environments.mapM (typecheckPolicy p)) := by
    refine mapM_sameVerdicts (Cedar.List.Forall₂.imp (fun env₁ env₂ hpair => ?_) (environments_pair h))
    obtain ⟨hsame, hacts, hets, q₁, q₂, hq₁, hq₂, hrel, hact, hc₁, hc₂⟩ := hpair
    refine typecheckPolicy_agree hsame p ?_
    rcases hp q₁ hq₁ q₂ hq₂ hrel with ⟨R, hR, hctx⟩ | hex
    · exact .inl ⟨R, hR, fun a ha => by rw [hc₁, hc₂]; exact hctx a ha⟩
    · exact .inr (hex env₁ hacts hets hact)
  unfold typecheckPolicyWithEnvironments
  rw [checkEntities_eq h]
  cases hce : checkEntities A₂ p.toExpr with
  | error _ => simp [Except.mapError, bind, Except.bind, Except.toBool]
  | ok _ =>
    simp only [Except.mapError, bind, Except.bind]
    cases h₁ : A₁.environments.mapM (typecheckPolicy p) <;>
      cases h₂ : A₂.environments.mapM (typecheckPolicy p) <;> rw [h₁, h₂] at hverd <;>
      simp only [SameVerdicts] at hverd
    · simp [Except.toBool]
    · rename_i ts ts'
      simp only [allFalse_eq hverd]

end Dogwood.Frontend.Augment.Typecheck
