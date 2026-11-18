import Dogwood.Thm.Lowering
import Dogwood.Thm.Frontend.Augment.Typecheck

/-!
# What a lowered rule reads of the context

The context attributes a Cedar expression reads directly (`ctxReads`), reading the context only
through attributes outside a list (`CtxAvoids`), and how lowering keeps a rule's reads out of the
other leaves' attributes (`ctxAvoids_lowerFrom`). Moved here from `Dogwood.Thm.Composition`, so
that the action-selective augmentation (`Dogwood.Thm.SelectiveAugment`) can use them.
-/

namespace Dogwood.Thm

open Dogwood.Spec
open Cedar.Spec (Attr)
open Dogwood.Frontend.Augment.Typecheck (ReadsOnly ReadsOnlyList ReadsOnlyRecord)

/-! ## What a lowered rule reads of the context -/

/-- Whether a Cedar expression is `context`. -/
def isCtx : Cedar.Spec.Expr → Bool
  | .var .context => true
  | _ => false

mutual

/-- The context attributes a Cedar expression reads directly, as `context.a`, `context has a`, or
`context has a.b…`. -/
def ctxReads : Cedar.Spec.Expr → List Attr
  | .lit _ | .var _ => []
  | .getAttr x a | .hasAttr x a | .extHasAttr x a _ => if isCtx x then [a] else ctxReads x
  | .unaryApp _ x => ctxReads x
  | .ite a b c => ctxReads a ++ ctxReads b ++ ctxReads c
  | .and a b | .or a b | .binaryApp _ a b => ctxReads a ++ ctxReads b
  | .set xs | .call _ xs => ctxReadsList xs
  | .record axs => ctxReadsRecord axs

def ctxReadsList : List Cedar.Spec.Expr → List Attr
  | [] => []
  | x :: xs => ctxReads x ++ ctxReadsList xs

def ctxReadsRecord : List (Attr × Cedar.Spec.Expr) → List Attr
  | [] => []
  | (_, x) :: axs => ctxReads x ++ ctxReadsRecord axs

end

mutual

/-- A Cedar expression reads the context only through attributes outside `N`, never whole. -/
def CtxAvoids (N : List Attr) : Cedar.Spec.Expr → Prop
  | .lit _ => True
  | .var v => v ≠ .context
  | .getAttr x a | .hasAttr x a | .extHasAttr x a _ => if isCtx x then a ∉ N else CtxAvoids N x
  | .unaryApp _ x => CtxAvoids N x
  | .ite a b c => CtxAvoids N a ∧ CtxAvoids N b ∧ CtxAvoids N c
  | .and a b | .or a b | .binaryApp _ a b => CtxAvoids N a ∧ CtxAvoids N b
  | .set xs | .call _ xs => CtxAvoidsList N xs
  | .record axs => CtxAvoidsRecord N axs

def CtxAvoidsList (N : List Attr) : List Cedar.Spec.Expr → Prop
  | [] => True
  | x :: xs => CtxAvoids N x ∧ CtxAvoidsList N xs

def CtxAvoidsRecord (N : List Attr) : List (Attr × Cedar.Spec.Expr) → Prop
  | [] => True
  | (_, x) :: axs => CtxAvoids N x ∧ CtxAvoidsRecord N axs

end

private theorem readsOnly_getAttr {R : List Attr} {x : Cedar.Spec.Expr} {a : Attr} :
    (if isCtx x then a ∈ R else ReadsOnly R x) → ReadsOnly R (.getAttr x a) := by
  cases x <;> (try rename_i v; cases v) <;> simp [isCtx, ReadsOnly]

private theorem readsOnly_hasAttr {R : List Attr} {x : Cedar.Spec.Expr} {a : Attr} :
    (if isCtx x then a ∈ R else ReadsOnly R x) → ReadsOnly R (.hasAttr x a) := by
  cases x <;> (try rename_i v; cases v) <;> simp [isCtx, ReadsOnly]

private theorem readsOnly_extHasAttr {R : List Attr} {x : Cedar.Spec.Expr} {a : Attr}
    {as₀ : List Attr} :
    (if isCtx x then a ∈ R else ReadsOnly R x) → ReadsOnly R (.extHasAttr x a as₀) := by
  cases x <;> (try rename_i v; cases v) <;> simp [isCtx, ReadsOnly]

mutual

/-- An expression that reads the context only through attributes reads it only at the attributes
`ctxReads` lists, and at any list holding them. -/
theorem readsOnly_of_ctxAvoids {N R : List Attr} :
    (e : Cedar.Spec.Expr) → CtxAvoids N e → (∀ a ∈ ctxReads e, a ∈ R) → ReadsOnly R e
  | .lit _, _, _ => by simp [ReadsOnly]
  | .var v, h, _ => by simpa [ReadsOnly, CtxAvoids] using h
  | .getAttr x a, h, hR => readsOnly_getAttr (by
      simp only [CtxAvoids, ctxReads] at h hR
      split at h
      · rename_i hx; simp only [hx, ↓reduceIte, List.mem_singleton, forall_eq] at hR ⊢; exact hR
      · rename_i hx; simp only [hx, Bool.false_eq_true, ↓reduceIte] at hR ⊢
        exact readsOnly_of_ctxAvoids x h hR)
  | .hasAttr x a, h, hR => readsOnly_hasAttr (by
      simp only [CtxAvoids, ctxReads] at h hR
      split at h
      · rename_i hx; simp only [hx, ↓reduceIte, List.mem_singleton, forall_eq] at hR ⊢; exact hR
      · rename_i hx; simp only [hx, Bool.false_eq_true, ↓reduceIte] at hR ⊢
        exact readsOnly_of_ctxAvoids x h hR)
  | .extHasAttr x a _, h, hR => readsOnly_extHasAttr (by
      simp only [CtxAvoids, ctxReads] at h hR
      split at h
      · rename_i hx; simp only [hx, ↓reduceIte, List.mem_singleton, forall_eq] at hR ⊢; exact hR
      · rename_i hx; simp only [hx, Bool.false_eq_true, ↓reduceIte] at hR ⊢
        exact readsOnly_of_ctxAvoids x h hR)
  | .unaryApp _ x, h, hR => by
    simp only [CtxAvoids, ctxReads] at h hR
    simp only [ReadsOnly]
    exact readsOnly_of_ctxAvoids x h hR
  | .ite a b c, h, hR => by
    simp only [CtxAvoids, ctxReads, List.mem_append] at h hR
    simp only [ReadsOnly]
    exact ⟨readsOnly_of_ctxAvoids a h.1 fun x hx => hR x (.inl (.inl hx)),
      readsOnly_of_ctxAvoids b h.2.1 fun x hx => hR x (.inl (.inr hx)),
      readsOnly_of_ctxAvoids c h.2.2 fun x hx => hR x (.inr hx)⟩
  | .and a b, h, hR => by
    simp only [CtxAvoids, ctxReads, List.mem_append] at h hR
    simp only [ReadsOnly]
    exact ⟨readsOnly_of_ctxAvoids a h.1 fun x hx => hR x (.inl hx),
      readsOnly_of_ctxAvoids b h.2 fun x hx => hR x (.inr hx)⟩
  | .or a b, h, hR => by
    simp only [CtxAvoids, ctxReads, List.mem_append] at h hR
    simp only [ReadsOnly]
    exact ⟨readsOnly_of_ctxAvoids a h.1 fun x hx => hR x (.inl hx),
      readsOnly_of_ctxAvoids b h.2 fun x hx => hR x (.inr hx)⟩
  | .binaryApp _ a b, h, hR => by
    simp only [CtxAvoids, ctxReads, List.mem_append] at h hR
    simp only [ReadsOnly]
    exact ⟨readsOnly_of_ctxAvoids a h.1 fun x hx => hR x (.inl hx),
      readsOnly_of_ctxAvoids b h.2 fun x hx => hR x (.inr hx)⟩
  | .set xs, h, hR => by
    simp only [CtxAvoids, ctxReads] at h hR
    simp only [ReadsOnly]
    exact readsOnlyList_of_ctxAvoids xs h hR
  | .call _ xs, h, hR => by
    simp only [CtxAvoids, ctxReads] at h hR
    simp only [ReadsOnly]
    exact readsOnlyList_of_ctxAvoids xs h hR
  | .record axs, h, hR => by
    simp only [CtxAvoids, ctxReads] at h hR
    simp only [ReadsOnly]
    exact readsOnlyRecord_of_ctxAvoids axs h hR

theorem readsOnlyList_of_ctxAvoids {N R : List Attr} :
    (xs : List Cedar.Spec.Expr) → CtxAvoidsList N xs → (∀ a ∈ ctxReadsList xs, a ∈ R) →
      ReadsOnlyList R xs
  | [], _, _ => by simp [ReadsOnlyList]
  | x :: xs, h, hR => by
    simp only [CtxAvoidsList, ctxReadsList, List.mem_append] at h hR
    simp only [ReadsOnlyList]
    exact ⟨readsOnly_of_ctxAvoids x h.1 fun a ha => hR a (.inl ha),
      readsOnlyList_of_ctxAvoids xs h.2 fun a ha => hR a (.inr ha)⟩

theorem readsOnlyRecord_of_ctxAvoids {N R : List Attr} :
    (axs : List (Attr × Cedar.Spec.Expr)) → CtxAvoidsRecord N axs →
      (∀ a ∈ ctxReadsRecord axs, a ∈ R) → ReadsOnlyRecord R axs
  | [], _, _ => by simp [ReadsOnlyRecord]
  | (_, x) :: axs, h, hR => by
    simp only [CtxAvoidsRecord, ctxReadsRecord, List.mem_append] at h hR
    simp only [ReadsOnlyRecord]
    exact ⟨readsOnly_of_ctxAvoids x h.1 fun a ha => hR a (.inl ha),
      readsOnlyRecord_of_ctxAvoids axs h.2 fun a ha => hR a (.inr ha)⟩

end

mutual

/-- An expression that reads the context only through attributes outside `N` reads none in
`N`. -/
theorem ctxReads_not_mem {N : List Attr} :
    (e : Cedar.Spec.Expr) → CtxAvoids N e → ∀ a ∈ ctxReads e, a ∉ N
  | .lit _, _ => by simp [ctxReads]
  | .var _, _ => by simp [ctxReads]
  | .getAttr x b, h | .hasAttr x b, h | .extHasAttr x b _, h => by
    simp only [CtxAvoids, ctxReads] at h ⊢
    split at h
    · rename_i hx; simp only [hx, ↓reduceIte, List.mem_singleton, forall_eq]; exact h
    · rename_i hx; simp only [hx, Bool.false_eq_true, ↓reduceIte]; exact ctxReads_not_mem x h
  | .unaryApp _ x, h => by
    simp only [CtxAvoids, ctxReads] at h ⊢
    exact ctxReads_not_mem x h
  | .ite a b c, h => by
    simp only [CtxAvoids, ctxReads, List.mem_append] at h ⊢
    rintro x ((hx | hx) | hx)
    · exact ctxReads_not_mem a h.1 x hx
    · exact ctxReads_not_mem b h.2.1 x hx
    · exact ctxReads_not_mem c h.2.2 x hx
  | .and a b, h | .or a b, h | .binaryApp _ a b, h => by
    simp only [CtxAvoids, ctxReads, List.mem_append] at h ⊢
    rintro x (hx | hx)
    · exact ctxReads_not_mem a h.1 x hx
    · exact ctxReads_not_mem b h.2 x hx
  | .set xs, h | .call _ xs, h => by
    simp only [CtxAvoids, ctxReads] at h ⊢
    exact ctxReadsList_not_mem xs h
  | .record axs, h => by
    simp only [CtxAvoids, ctxReads] at h ⊢
    exact ctxReadsRecord_not_mem axs h

theorem ctxReadsList_not_mem {N : List Attr} :
    (xs : List Cedar.Spec.Expr) → CtxAvoidsList N xs → ∀ a ∈ ctxReadsList xs, a ∉ N
  | [], _ => by simp [ctxReadsList]
  | x :: xs, h => by
    simp only [CtxAvoidsList, ctxReadsList, List.mem_append] at h ⊢
    rintro a (ha | ha)
    · exact ctxReads_not_mem x h.1 a ha
    · exact ctxReadsList_not_mem xs h.2 a ha

theorem ctxReadsRecord_not_mem {N : List Attr} :
    (axs : List (Attr × Cedar.Spec.Expr)) → CtxAvoidsRecord N axs →
      ∀ a ∈ ctxReadsRecord axs, a ∉ N
  | [], _ => by simp [ctxReadsRecord]
  | (_, x) :: axs, h => by
    simp only [CtxAvoidsRecord, ctxReadsRecord, List.mem_append] at h ⊢
    rintro a (ha | ha)
    · exact ctxReads_not_mem x h.1 a ha
    · exact ctxReadsRecord_not_mem axs h.2 a ha

end


theorem isCtx_lowerFrom (x : Expr) (k : Nat) : isCtx (x.lowerFrom k).1 = x.isContext := by
  cases x <;> (try rename_i v; cases v) <;> rfl

mutual

/-- **Lowering keeps a rule's context reads out of `N`**, when the rule reads the context only
through attributes outside `N` and its leaves' attributes are outside `N`. -/
theorem ctxAvoids_lowerFrom {N : List Attr} : (x : Expr) → (k : Nat) → x.ReadsContext N →
    (∀ i, k ≤ i → i < k + x.leaves.length → leafAttr i ∉ N) → CtxAvoids N (x.lowerFrom k).1
  | .lit _, _, _, _ => by simp [Expr.lowerFrom, CtxAvoids]
  | .var v, _, h, _ => by simpa [Expr.lowerFrom, CtxAvoids, Expr.ReadsContext] using h
  | .ite a b c, k, h, hk => by
    simp only [Expr.ReadsContext] at h
    simp only [Expr.lowerFrom, CtxAvoids, lowerFrom_snd]
    simp only [Expr.leaves, List.length_append] at hk
    exact ⟨ctxAvoids_lowerFrom a k h.1 fun i h₁ h₂ => hk i h₁ (by omega),
      ctxAvoids_lowerFrom b _ h.2.1 fun i h₁ h₂ => hk i (by omega) (by omega),
      ctxAvoids_lowerFrom c _ h.2.2 fun i h₁ h₂ => hk i (by omega) (by omega)⟩
  | .and a b, k, h, hk => by
    simp only [Expr.ReadsContext] at h
    simp only [Expr.lowerFrom, CtxAvoids, lowerFrom_snd]
    simp only [Expr.leaves, List.length_append] at hk
    exact ⟨ctxAvoids_lowerFrom a k h.1 fun i h₁ h₂ => hk i h₁ (by omega),
      ctxAvoids_lowerFrom b _ h.2 fun i h₁ h₂ => hk i (by omega) (by omega)⟩
  | .or a b, k, h, hk => by
    simp only [Expr.ReadsContext] at h
    simp only [Expr.lowerFrom, CtxAvoids, lowerFrom_snd]
    simp only [Expr.leaves, List.length_append] at hk
    exact ⟨ctxAvoids_lowerFrom a k h.1 fun i h₁ h₂ => hk i h₁ (by omega),
      ctxAvoids_lowerFrom b _ h.2 fun i h₁ h₂ => hk i (by omega) (by omega)⟩
  | .binaryApp _ a b, k, h, hk => by
    simp only [Expr.ReadsContext] at h
    simp only [Expr.lowerFrom, CtxAvoids, lowerFrom_snd]
    simp only [Expr.leaves, List.length_append] at hk
    exact ⟨ctxAvoids_lowerFrom a k h.1 fun i h₁ h₂ => hk i h₁ (by omega),
      ctxAvoids_lowerFrom b _ h.2 fun i h₁ h₂ => hk i (by omega) (by omega)⟩
  | .unaryApp _ a, k, h, hk => by
    simp only [Expr.ReadsContext] at h
    simp only [Expr.lowerFrom, CtxAvoids]
    exact ctxAvoids_lowerFrom a k h hk
  | .getAttr a _, k, h, hk | .hasAttr a _, k, h, hk | .extHasAttr a _ _, k, h, hk => by
    simp only [Expr.ReadsContext] at h
    simp only [Expr.lowerFrom, CtxAvoids, isCtx_lowerFrom]
    split
    · rename_i hx; simpa [hx] using h
    · rename_i hx
      simp only [hx, Bool.false_eq_true, ↓reduceIte] at h
      exact ctxAvoids_lowerFrom a k h hk
  | .set xs, k, h, hk | .call _ xs, k, h, hk => by
    simp only [Expr.ReadsContext] at h
    simp only [Expr.lowerFrom, CtxAvoids]
    exact ctxAvoidsList_lowerFrom xs k h hk
  | .record axs, k, h, hk => by
    simp only [Expr.ReadsContext] at h
    simp only [Expr.lowerFrom, CtxAvoids]
    exact ctxAvoidsRecord_lowerFrom axs k h hk
  | .temporal _, k, _, hk | .provider _, k, _, hk => by
    simp only [Expr.lowerFrom, CtxAvoids, isCtx, ↓reduceIte]
    exact hk k (Nat.le_refl _) (by simp [Expr.leaves])

theorem ctxAvoidsList_lowerFrom {N : List Attr} : (xs : List Expr) → (k : Nat) →
    Expr.ReadsContextList N xs →
    (∀ i, k ≤ i → i < k + (Expr.leavesList xs).length → leafAttr i ∉ N) →
    CtxAvoidsList N (Expr.lowerListFrom k xs).1
  | [], _, _, _ => by simp [Expr.lowerListFrom, CtxAvoidsList]
  | x :: xs, k, h, hk => by
    simp only [Expr.ReadsContextList] at h
    simp only [Expr.lowerListFrom, CtxAvoidsList, lowerFrom_snd]
    simp only [Expr.leavesList, List.length_append] at hk
    exact ⟨ctxAvoids_lowerFrom x k h.1 fun i h₁ h₂ => hk i h₁ (by omega),
      ctxAvoidsList_lowerFrom xs _ h.2 fun i h₁ h₂ => hk i (by omega) (by omega)⟩

theorem ctxAvoidsRecord_lowerFrom {N : List Attr} : (axs : List (Attr × Expr)) → (k : Nat) →
    Expr.ReadsContextRecord N axs →
    (∀ i, k ≤ i → i < k + (Expr.leavesRecord axs).length → leafAttr i ∉ N) →
    CtxAvoidsRecord N (Expr.lowerRecordFrom k axs).1
  | [], _, _, _ => by simp [Expr.lowerRecordFrom, CtxAvoidsRecord]
  | (_, x) :: axs, k, h, hk => by
    simp only [Expr.ReadsContextRecord] at h
    simp only [Expr.lowerRecordFrom, CtxAvoidsRecord, lowerFrom_snd]
    simp only [Expr.leavesRecord, List.length_append] at hk
    exact ⟨ctxAvoids_lowerFrom x k h.1 fun i h₁ h₂ => hk i h₁ (by omega),
      ctxAvoidsRecord_lowerFrom axs _ h.2 fun i h₁ h₂ => hk i (by omega) (by omega)⟩

end

/-! ## What the rules read -/

mutual

theorem readsContext_mono {N N' : List Attr} (hN : ∀ a ∈ N', a ∈ N) :
    (x : Expr) → x.ReadsContext N → x.ReadsContext N'
  | .lit _, h => h
  | .var _, h => h
  | .getAttr x _, h | .hasAttr x _, h | .extHasAttr x _ _, h => by
    simp only [Expr.ReadsContext] at h ⊢
    split
    · rename_i hx; simp only [hx, ↓reduceIte] at h; exact fun h' => h (hN _ h')
    · rename_i hx; simp only [hx, Bool.false_eq_true, ↓reduceIte] at h
      exact readsContext_mono hN x h
  | .unaryApp _ x, h => by
    simp only [Expr.ReadsContext] at h ⊢; exact readsContext_mono hN x h
  | .ite a b c, h => by
    simp only [Expr.ReadsContext] at h ⊢
    exact ⟨readsContext_mono hN a h.1, readsContext_mono hN b h.2.1, readsContext_mono hN c h.2.2⟩
  | .and a b, h | .or a b, h | .binaryApp _ a b, h => by
    simp only [Expr.ReadsContext] at h ⊢
    exact ⟨readsContext_mono hN a h.1, readsContext_mono hN b h.2⟩
  | .set xs, h | .call _ xs, h => by
    simp only [Expr.ReadsContext] at h ⊢; exact readsContextList_mono hN xs h
  | .record axs, h => by
    simp only [Expr.ReadsContext] at h ⊢; exact readsContextRecord_mono hN axs h
  | .temporal _, h | .provider _, h => h

theorem readsContextList_mono {N N' : List Attr} (hN : ∀ a ∈ N', a ∈ N) :
    (xs : List Expr) → Expr.ReadsContextList N xs → Expr.ReadsContextList N' xs
  | [], h => h
  | x :: xs, h => by
    simp only [Expr.ReadsContextList] at h ⊢
    exact ⟨readsContext_mono hN x h.1, readsContextList_mono hN xs h.2⟩

theorem readsContextRecord_mono {N N' : List Attr} (hN : ∀ a ∈ N', a ∈ N) :
    (axs : List (Attr × Expr)) → Expr.ReadsContextRecord N axs → Expr.ReadsContextRecord N' axs
  | [], h => h
  | (_, x) :: axs, h => by
    simp only [Expr.ReadsContextRecord] at h ⊢
    exact ⟨readsContext_mono hN x h.1, readsContextRecord_mono hN axs h.2⟩

end

mutual

theorem readsContext_append {N₁ N₂ : List Attr} :
    (x : Expr) → x.ReadsContext N₁ → x.ReadsContext N₂ → x.ReadsContext (N₁ ++ N₂)
  | .lit _, h, _ => h
  | .var _, h, _ => h
  | .getAttr x _, h₁, h₂ | .hasAttr x _, h₁, h₂ | .extHasAttr x _ _, h₁, h₂ => by
    simp only [Expr.ReadsContext] at h₁ h₂ ⊢
    split
    · rename_i hx; simp only [hx, ↓reduceIte] at h₁ h₂
      simp only [List.mem_append, not_or]; exact ⟨h₁, h₂⟩
    · rename_i hx; simp only [hx, Bool.false_eq_true, ↓reduceIte] at h₁ h₂
      exact readsContext_append x h₁ h₂
  | .unaryApp _ x, h₁, h₂ => by
    simp only [Expr.ReadsContext] at h₁ h₂ ⊢; exact readsContext_append x h₁ h₂
  | .ite a b c, h₁, h₂ => by
    simp only [Expr.ReadsContext] at h₁ h₂ ⊢
    exact ⟨readsContext_append a h₁.1 h₂.1, readsContext_append b h₁.2.1 h₂.2.1,
      readsContext_append c h₁.2.2 h₂.2.2⟩
  | .and a b, h₁, h₂ | .or a b, h₁, h₂ | .binaryApp _ a b, h₁, h₂ => by
    simp only [Expr.ReadsContext] at h₁ h₂ ⊢
    exact ⟨readsContext_append a h₁.1 h₂.1, readsContext_append b h₁.2 h₂.2⟩
  | .set xs, h₁, h₂ | .call _ xs, h₁, h₂ => by
    simp only [Expr.ReadsContext] at h₁ h₂ ⊢; exact readsContextList_append xs h₁ h₂
  | .record axs, h₁, h₂ => by
    simp only [Expr.ReadsContext] at h₁ h₂ ⊢; exact readsContextRecord_append axs h₁ h₂
  | .temporal _, h, _ | .provider _, h, _ => h

theorem readsContextList_append {N₁ N₂ : List Attr} :
    (xs : List Expr) → Expr.ReadsContextList N₁ xs → Expr.ReadsContextList N₂ xs →
      Expr.ReadsContextList (N₁ ++ N₂) xs
  | [], h, _ => h
  | x :: xs, h₁, h₂ => by
    simp only [Expr.ReadsContextList] at h₁ h₂ ⊢
    exact ⟨readsContext_append x h₁.1 h₂.1, readsContextList_append xs h₁.2 h₂.2⟩

theorem readsContextRecord_append {N₁ N₂ : List Attr} :
    (axs : List (Attr × Expr)) → Expr.ReadsContextRecord N₁ axs → Expr.ReadsContextRecord N₂ axs →
      Expr.ReadsContextRecord (N₁ ++ N₂) axs
  | [], h, _ => h
  | (_, x) :: axs, h₁, h₂ => by
    simp only [Expr.ReadsContextRecord] at h₁ h₂ ⊢
    exact ⟨readsContext_append x h₁.1 h₂.1, readsContextRecord_append axs h₁.2 h₂.2⟩

end

end Dogwood.Thm
