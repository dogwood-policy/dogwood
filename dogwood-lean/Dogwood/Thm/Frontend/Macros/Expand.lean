import Dogwood.Frontend.Macros
import Dogwood.Thm.Frontend.Macros.Transport

/-!
# Macro expansion and the library merge

* `expand_expanded`: the output of `Macros.expand` is in the macro-free fragment (no definition,
  no macro call, no `?p`, no macro syntax in a temporal block), and every temporal block of it
  passes the static checks (`checkLeaf`).
* `expand_macroFree`: on a set already in the macro-free fragment, `expand` is the identity,
  and it succeeds exactly when every temporal block passes the static checks.
* `mergeLibrary_lookup`: after the library merge, a name resolves to the policy set's own
  definition when it has one, and to the library's otherwise: a policy's `def` takes precedence
  over a library macro of the same name.

The macro-free fragment is `MacroFreeE false`; `MacroFreeE true` (`Expanded`) also asks that every
temporal block pass the static checks. A call in it is namespace-qualified, an information
provider's, which expansion leaves for cedarify.
-/

namespace Dogwood.Thm.Frontend.Macros

open Dogwood.Frontend Dogwood.Frontend.Macros
open Dogwood.Frontend.Surface (Expr ExprKind PolicySet MacroDef MacroBody Policy Cond)
open Dogwood.Frontend.Surface.Temporal

/-! ## The macro-free fragment -/

mutual

/-- An expression of the macro-free fragment: every call is a provider's (namespace-qualified),
there is no `?p`, and no temporal block holds macro syntax (`noResidue`); with `checked`, every
temporal block also passes the static checks. -/
def MacroFreeE (checked : Bool) : Expr → Prop
  | ⟨.call n args, _⟩ => isQualified n = true ∧ MacroFreeL checked args
  | ⟨.paramRef _, _⟩ => False
  | ⟨.extension b, _⟩ =>
    noResidue b.condition = .ok () ∧ (checked = true → checkLeaf b.condition = .ok ())
  | ⟨.lit _, _⟩ => True
  | ⟨.var _, _⟩ => True
  | ⟨.slot _, _⟩ => True
  | ⟨.unaryApp _ e, _⟩ => MacroFreeE checked e
  | ⟨.binaryApp _ l r, _⟩ => MacroFreeE checked l ∧ MacroFreeE checked r
  | ⟨.getAttr e _, _⟩ => MacroFreeE checked e
  | ⟨.hasAttr e _, _⟩ => MacroFreeE checked e
  | ⟨.like e _, _⟩ => MacroFreeE checked e
  | ⟨.is e _ none, _⟩ => MacroFreeE checked e
  | ⟨.is e _ (some x), _⟩ => MacroFreeE checked e ∧ MacroFreeE checked x
  | ⟨.ite c t e, _⟩ => MacroFreeE checked c ∧ MacroFreeE checked t ∧ MacroFreeE checked e
  | ⟨.set xs, _⟩ => MacroFreeL checked xs
  | ⟨.record es, _⟩ => MacroFreeR checked es
  | ⟨.methodCall r _ args, _⟩ => MacroFreeE checked r ∧ MacroFreeL checked args

def MacroFreeL (checked : Bool) : List Expr → Prop
  | [] => True
  | e :: rest => MacroFreeE checked e ∧ MacroFreeL checked rest

def MacroFreeR (checked : Bool) : List (String × Expr) → Prop
  | [] => True
  | (_, e) :: rest => MacroFreeE checked e ∧ MacroFreeR checked rest

end

/-- The macro-free fragment. -/
abbrev MacroFree : Expr → Prop := MacroFreeE false

/-- The macro-free fragment, every temporal block passing the static checks. -/
abbrev Expanded : Expr → Prop := MacroFreeE true

/-- A policy set of the macro-free fragment: no definition, and every condition macro-free. -/
def SetMacroFree (checked : Bool) (ps : PolicySet) : Prop :=
  ps.defs = [] ∧ ∀ p ∈ ps.policies, ∀ c ∈ p.conditions, MacroFreeE checked c.body

/-! ## `Except` -/

theorem err_ne_ok {α : Type} {m : String} {sp : Span} {a : α} : err m sp ≠ .ok a := by
  intro h; cases h

theorem foldl_lookup_mem {β : Type} (k : String) (v : β) : (m : List (String × β)) →
    (acc : Option β) →
    m.foldl (fun acc (p : String × β) => if p.1 == k then some p.2 else acc) acc = some v →
    (k, v) ∈ m ∨ acc = some v
  | [], _, h => .inr h
  | (k', v') :: m, acc, h => by
    simp only [List.foldl_cons] at h
    rcases foldl_lookup_mem k v m _ h with hm | hacc
    · exact .inl (List.mem_cons_of_mem _ hm)
    · split at hacc
      · rename_i hk
        simp only [beq_iff_eq] at hk
        simp only [Option.some.injEq] at hacc
        subst hk hacc
        exact .inl List.mem_cons_self
      · exact .inr hacc

theorem lookupLast_mem {β : Type} {m : List (String × β)} {k : String} {v : β}
    (h : lookupLast m k = some v) : (k, v) ∈ m := by
  rcases foldl_lookup_mem k v m none h with h | h
  · exact h
  · cases h

theorem lookup_mem {defs : List MacroDef} {n : String} {d : MacroDef}
    (h : lookup defs n = some d) : d ∈ defs :=
  List.mem_of_find?_eq_some h

theorem macroFreeL_iff {ck : Bool} : {xs : List Expr} → (MacroFreeL ck xs ↔ ∀ x ∈ xs, MacroFreeE ck x)
  | [] => by simp [MacroFreeL]
  | x :: xs => by simp only [MacroFreeL, macroFreeL_iff, List.mem_cons, forall_eq_or_imp]

theorem macroFreeR_iff {ck : Bool} : {xs : List (String × Expr)} →
    (MacroFreeR ck xs ↔ ∀ x ∈ xs, MacroFreeE ck x.2)
  | [] => by simp [MacroFreeR]
  | (k, x) :: xs => by simp only [MacroFreeR, macroFreeR_iff, List.mem_cons, forall_eq_or_imp]

/-! ## Cedar substitution -/

mutual

/-- Substituting macro-free arguments into a well-formed Cedar body gives a macro-free
expression. -/
theorem substCedar_mf : (body : Expr) → {declared : List String} → {m : List (String × Expr)} →
    {e' : Expr} → {ck : Bool} → checkCedarBody declared body = .ok () →
    substCedar m body = .ok e' → (∀ a ∈ m, MacroFreeE ck a.2) → MacroFreeE ck e'
  | ⟨.paramRef name, sp⟩, _, m, _, _, _, h, hm => by
    simp only [substCedar] at h
    split at h
    · rename_i a ha
      simp only [pure_eq_ok] at h
      subst h
      exact hm _ (lookupLast_mem ha)
    · exact absurd h err_ne_ok
  | ⟨.call _ _, _⟩, _, _, _, _, hb, _, _ => by simp [checkCedarBody, err_ne_ok] at hb
  | ⟨.extension _, _⟩, _, _, _, _, hb, _, _ => by simp [checkCedarBody, err_ne_ok] at hb
  | ⟨.lit _, _⟩, _, _, _, _, _, h, _ => by
    simp only [substCedar, pure_eq_ok] at h; subst h; trivial
  | ⟨.var _, _⟩, _, _, _, _, _, h, _ => by
    simp only [substCedar, pure_eq_ok] at h; subst h; trivial
  | ⟨.slot _, _⟩, _, _, _, _, _, h, _ => by
    simp only [substCedar, pure_eq_ok] at h; subst h; trivial
  | ⟨.unaryApp _ e, _⟩, _, _, _, _, hb, h, hm => by
    simp only [checkCedarBody] at hb
    simp only [substCedar, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨a, ha, rfl⟩ := h
    simp only [MacroFreeE]
    exact substCedar_mf e hb ha hm
  | ⟨.binaryApp _ l r, _⟩, _, _, _, _, hb, h, hm => by
    simp only [checkCedarBody, seq_eq_ok] at hb
    simp only [substCedar, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨a, ha, b, hb', rfl⟩ := h
    exact ⟨substCedar_mf l hb.1 ha hm, substCedar_mf r hb.2 hb' hm⟩
  | ⟨.getAttr e _, _⟩, _, _, _, _, hb, h, hm => by
    simp only [checkCedarBody] at hb
    simp only [substCedar, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨a, ha, rfl⟩ := h
    simp only [MacroFreeE]
    exact substCedar_mf e hb ha hm
  | ⟨.hasAttr e _, _⟩, _, _, _, _, hb, h, hm => by
    simp only [checkCedarBody] at hb
    simp only [substCedar, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨a, ha, rfl⟩ := h
    simp only [MacroFreeE]
    exact substCedar_mf e hb ha hm
  | ⟨.like e _, _⟩, _, _, _, _, hb, h, hm => by
    simp only [checkCedarBody] at hb
    simp only [substCedar, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨a, ha, rfl⟩ := h
    simp only [MacroFreeE]
    exact substCedar_mf e hb ha hm
  | ⟨.is e _ none, _⟩, _, _, _, _, hb, h, hm => by
    simp only [checkCedarBody] at hb
    simp only [substCedar, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨a, ha, rfl⟩ := h
    simp only [MacroFreeE]
    exact substCedar_mf e hb ha hm
  | ⟨.is e _ (some x), _⟩, _, _, _, _, hb, h, hm => by
    simp only [checkCedarBody, seq_eq_ok] at hb
    simp only [substCedar, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨a, ha, b, hb', rfl⟩ := h
    exact ⟨substCedar_mf e hb.1 ha hm, substCedar_mf x hb.2 hb' hm⟩
  | ⟨.ite c t e, _⟩, _, _, _, _, hb, h, hm => by
    simp only [checkCedarBody, seq_eq_ok] at hb
    simp only [substCedar, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨a, ha, b, hb', d, hd, rfl⟩ := h
    exact ⟨substCedar_mf c hb.1 ha hm, substCedar_mf t hb.2.1 hb' hm,
      substCedar_mf e hb.2.2 hd hm⟩
  | ⟨.set xs, _⟩, _, _, _, _, hb, h, hm => by
    simp only [checkCedarBody] at hb
    simp only [substCedar, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨a, ha, rfl⟩ := h
    simp only [MacroFreeE]
    exact substCedars_mf xs hb ha hm
  | ⟨.record es, _⟩, _, _, _, _, hb, h, hm => by
    simp only [checkCedarBody] at hb
    simp only [substCedar, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨a, ha, rfl⟩ := h
    simp only [MacroFreeE]
    exact substCedarEntries_mf es hb ha hm
  | ⟨.methodCall r _ args, _⟩, _, _, _, _, hb, h, hm => by
    simp only [checkCedarBody, seq_eq_ok] at hb
    simp only [substCedar, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨a, ha, b, hb', rfl⟩ := h
    exact ⟨substCedar_mf r hb.1 ha hm, substCedars_mf args hb.2 hb' hm⟩

theorem substCedars_mf : (xs : List Expr) → {declared : List String} → {m : List (String × Expr)} →
    {xs' : List Expr} → {ck : Bool} → checkCedarBodies declared xs = .ok () →
    substCedars m xs = .ok xs' → (∀ a ∈ m, MacroFreeE ck a.2) → MacroFreeL ck xs'
  | [], _, _, _, _, _, h, _ => by
    simp only [substCedars, pure_eq_ok] at h; subst h; trivial
  | e :: rest, _, _, _, _, hb, h, hm => by
    simp only [checkCedarBodies, seq_eq_ok] at hb
    simp only [substCedars, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨a, ha, b, hb', rfl⟩ := h
    exact ⟨substCedar_mf e hb.1 ha hm, substCedars_mf rest hb.2 hb' hm⟩

theorem substCedarEntries_mf : (xs : List (String × Expr)) → {declared : List String} →
    {m : List (String × Expr)} → {xs' : List (String × Expr)} → {ck : Bool} →
    checkCedarEntries declared xs = .ok () → substCedarEntries m xs = .ok xs' →
    (∀ a ∈ m, MacroFreeE ck a.2) → MacroFreeR ck xs'
  | [], _, _, _, _, _, h, _ => by
    simp only [substCedarEntries, pure_eq_ok] at h; subst h; trivial
  | (k, e) :: rest, _, _, _, _, hb, h, hm => by
    simp only [checkCedarEntries, seq_eq_ok] at hb
    simp only [substCedarEntries, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨a, ha, b, hb', rfl⟩ := h
    exact ⟨substCedar_mf e hb.1 ha hm, substCedarEntries_mf rest hb.2 hb' hm⟩

end

/-! ## The output of expansion is macro-free -/

/-- Every definition of a list is well formed. -/
def DefsChecked (defs : List MacroDef) : Prop := ∀ d ∈ defs, checkDef d = .ok ()

theorem checkDefs_checked {defs : List MacroDef} (h : checkDefs defs = .ok ()) :
    DefsChecked defs := by
  simp only [checkDefs, seq_eq_ok, forM_eq_ok] at h
  exact h.2

theorem atStage_ok {α : Type} {s : Stage} {r : MacroResult α} {a : α} :
    MacroResult.atStage s r = .ok a ↔ r = .ok a := by
  cases r <;> simp [MacroResult.atStage]

theorem mapM_ok {α β ε : Type} {f : α → Except ε β} : {xs : List α} → {ys : List β} →
    xs.mapM f = .ok ys → ∀ y ∈ ys, ∃ x ∈ xs, f x = .ok y
  | [], ys, h => by
    simp only [List.mapM_nil, pure_eq_ok] at h
    subst h; simp
  | x :: xs, ys, h => by
    simp only [List.mapM_cons, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨y, hy, ys', hys, rfl⟩ := h
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact ⟨x, List.mem_cons_self, hy⟩
    · obtain ⟨x', hx', h'⟩ := mapM_ok hys z hz
      exact ⟨x', List.mem_cons_of_mem _ hx', h'⟩

/-- Rebasing an error's span leaves a success alone. -/
theorem rebaseErr_ok {α : Type} {base : Nat} {x : MacroResult α} {a : α} :
    rebaseErr base x = .ok a ↔ x = .ok a := by
  cases x <;> simp [rebaseErr]

theorem expandBlock_ok {defs : List MacroDef} {b b' : Block} (h : expandBlock defs b = .ok b') :
    expandCond defs b.condition = .ok b'.condition ∧ noResidue b'.condition = .ok () ∧
      checkLeaf b'.condition = .ok () ∧ b'.span = b.span := by
  simp only [expandBlock, bind_eq_ok] at h
  obtain ⟨c, hc, u, hr, h⟩ := h
  rw [rebaseErr_ok] at hc hr
  cases u
  split at h
  · rename_i hl
    simp only [pure_eq_ok] at h
    subst h
    exact ⟨hc, hr, hl, rfl⟩
  · exact absurd h err_ne_ok

mutual

theorem expandExpr_expanded : (e : Expr) → {defs : List MacroDef} → {e' : Expr} →
    DefsChecked defs → expandExpr defs e = .ok e' → Expanded e'
  | ⟨.call name args, sp⟩, defs, _, hd, h => by
    simp only [expandExpr, bind_eq_ok] at h
    obtain ⟨args', ha, h⟩ := h
    have hargs := expandExprs_expanded args hd ha
    split at h
    · rename_i hq
      simp only [pure_eq_ok] at h
      subst h
      exact ⟨hq, hargs⟩
    · split at h
      · exact absurd h err_ne_ok
      · rename_i d hl
        split at h
        · rename_i body hbody
          simp only [seq_eq_ok] at h
          have hcd := hd d (lookup_mem hl)
          simp only [checkDef, hbody] at hcd
          refine substCedar_mf body hcd h.2 ?_
          intro a ha'
          exact (macroFreeL_iff.mp hargs) _ (List.of_mem_zip ha').2
        · exact absurd h err_ne_ok
  | ⟨.paramRef _, _⟩, _, _, _, h => by simp [expandExpr, err_ne_ok] at h
  | ⟨.extension t, _⟩, _, _, _, h => by
    simp only [expandExpr, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨b, hb, rfl⟩ := h
    obtain ⟨-, hr, hl, -⟩ := expandBlock_ok hb
    exact ⟨hr, fun _ => hl⟩
  | ⟨.lit _, _⟩, _, _, _, h => by
    simp only [expandExpr, pure_eq_ok] at h; subst h; trivial
  | ⟨.var _, _⟩, _, _, _, h => by
    simp only [expandExpr, pure_eq_ok] at h; subst h; trivial
  | ⟨.slot _, _⟩, _, _, _, h => by
    simp only [expandExpr, pure_eq_ok] at h; subst h; trivial
  | ⟨.unaryApp _ e, _⟩, _, _, hd, h => by
    simp only [expandExpr, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨a, ha, rfl⟩ := h
    simp only [MacroFreeE]
    exact expandExpr_expanded e hd ha
  | ⟨.binaryApp _ l r, _⟩, _, _, hd, h => by
    simp only [expandExpr, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨a, ha, b, hb, rfl⟩ := h
    exact ⟨expandExpr_expanded l hd ha, expandExpr_expanded r hd hb⟩
  | ⟨.getAttr e _, _⟩, _, _, hd, h => by
    simp only [expandExpr, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨a, ha, rfl⟩ := h
    simp only [MacroFreeE]
    exact expandExpr_expanded e hd ha
  | ⟨.hasAttr e _, _⟩, _, _, hd, h => by
    simp only [expandExpr, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨a, ha, rfl⟩ := h
    simp only [MacroFreeE]
    exact expandExpr_expanded e hd ha
  | ⟨.like e _, _⟩, _, _, hd, h => by
    simp only [expandExpr, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨a, ha, rfl⟩ := h
    simp only [MacroFreeE]
    exact expandExpr_expanded e hd ha
  | ⟨.is e _ none, _⟩, _, _, hd, h => by
    simp only [expandExpr, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨a, ha, rfl⟩ := h
    simp only [MacroFreeE]
    exact expandExpr_expanded e hd ha
  | ⟨.is e _ (some x), _⟩, _, _, hd, h => by
    simp only [expandExpr, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨a, ha, b, hb, rfl⟩ := h
    exact ⟨expandExpr_expanded e hd ha, expandExpr_expanded x hd hb⟩
  | ⟨.ite c t e, _⟩, _, _, hd, h => by
    simp only [expandExpr, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨a, ha, b, hb, d, hd', rfl⟩ := h
    exact ⟨expandExpr_expanded c hd ha, expandExpr_expanded t hd hb, expandExpr_expanded e hd hd'⟩
  | ⟨.set xs, _⟩, _, _, hd, h => by
    simp only [expandExpr, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨a, ha, rfl⟩ := h
    simp only [MacroFreeE]
    exact expandExprs_expanded xs hd ha
  | ⟨.record es, _⟩, _, _, hd, h => by
    simp only [expandExpr, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨a, ha, rfl⟩ := h
    simp only [MacroFreeE]
    exact expandEntries_expanded es hd ha
  | ⟨.methodCall r _ args, _⟩, _, _, hd, h => by
    simp only [expandExpr, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨a, ha, b, hb, rfl⟩ := h
    exact ⟨expandExpr_expanded r hd ha, expandExprs_expanded args hd hb⟩

theorem expandExprs_expanded : (xs : List Expr) → {defs : List MacroDef} → {xs' : List Expr} →
    DefsChecked defs → expandExprs defs xs = .ok xs' → MacroFreeL true xs'
  | [], _, _, _, h => by
    simp only [expandExprs, pure_eq_ok] at h; subst h; trivial
  | e :: rest, _, _, hd, h => by
    simp only [expandExprs, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨a, ha, b, hb, rfl⟩ := h
    exact ⟨expandExpr_expanded e hd ha, expandExprs_expanded rest hd hb⟩

theorem expandEntries_expanded : (xs : List (String × Expr)) → {defs : List MacroDef} →
    {xs' : List (String × Expr)} → DefsChecked defs → expandEntries defs xs = .ok xs' →
    MacroFreeR true xs'
  | [], _, _, _, h => by
    simp only [expandEntries, pure_eq_ok] at h; subst h; trivial
  | (k, e) :: rest, _, _, hd, h => by
    simp only [expandEntries, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨a, ha, b, hb, rfl⟩ := h
    exact ⟨expandExpr_expanded e hd ha, expandEntries_expanded rest hd hb⟩

end

theorem expandPolicy_ok {defs : List MacroDef} {p p' : Policy} (h : expandPolicy defs p = .ok p') :
    ∀ c' ∈ p'.conditions, ∃ c ∈ p.conditions, expandExpr defs c.body = .ok c'.body := by
  simp only [expandPolicy, bind_eq_ok, pure_eq_ok] at h
  obtain ⟨cs, hcs, rfl⟩ := h
  intro c' hc'
  obtain ⟨c, hc, h⟩ := mapM_ok hcs c' hc'
  simp only [bind_eq_ok, pure_eq_ok] at h
  obtain ⟨e, he, rfl⟩ := h
  exact ⟨c, hc, he⟩

/-- **Expansion leaves no macro behind.** The output of `expand` has no definition, no macro
call, no `?p`, and no macro syntax in a temporal block, and every temporal block of it passes
the static checks. -/
theorem expand_expanded {ps ps' : PolicySet} (h : expand ps = .ok ps') : SetMacroFree true ps' := by
  simp only [expand, atStage_ok, bind_eq_ok, pure_eq_ok] at h
  obtain ⟨u, hd, pols, hpols, rfl⟩ := h
  cases u
  refine ⟨rfl, fun p' hp' c' hc' => ?_⟩
  obtain ⟨p, -, hp⟩ := mapM_ok hpols p' hp'
  obtain ⟨c, -, hc⟩ := expandPolicy_ok hp c' hc'
  exact expandExpr_expanded c.body (checkDefs_checked hd) hc

/-! ## Expansion is the identity on the macro-free fragment -/

theorem checkConcreteSlot_ok {sp : Span} {s : BinderSlot} (h : noResidueSlot sp s = .ok ()) :
    checkConcreteSlot sp s = .ok () := by
  cases s <;> simp_all [noResidueSlot, checkConcreteSlot, residue, err_ne_ok]

theorem checkConcreteWithin_ok {sp : Span} {w : WithinSpec} (h : noResidueWithin sp w = .ok ()) :
    checkConcreteWithin sp w = .ok () := by
  cases w <;> simp_all [noResidueWithin, checkConcreteWithin, residue, err_ne_ok]

theorem slots_ok {sp sp' : Span} {vs : List TypedBinder}
    (h : (vs.forM fun v => noResidueSlot sp v.slot) = .ok ()) :
    (vs.forM fun v => checkConcreteSlot sp' v.slot) = .ok () := by
  rw [forM_eq_ok] at h ⊢
  intro v hv
  have := h v hv
  cases hs : v.slot <;> simp_all [noResidueSlot, checkConcreteSlot, residue, err_ne_ok]

mutual

theorem checkConcreteTerm_ok : (t : Term) → {sp sp' : Span} → noResidueTerm sp t = .ok () →
    checkConcreteTerm sp' t = .ok ()
  | .paramRef _, _, _, h => by simp [noResidueTerm, residue, err_ne_ok] at h
  | .binderRef _, _, _, h => by simp [noResidueTerm, residue, err_ne_ok] at h
  | .array items, _, _, h => by
    simp only [noResidueTerm] at h
    simp only [checkConcreteTerm]
    exact checkConcreteTerms_ok items h
  | .entity _ _, _, _, _ | .integer _, _, _, _ | .decimal _, _, _, _ | .string _, _, _, _
  | .bool _, _, _, _ | .contextField _, _, _, _ | .scopeField _, _, _, _ | .var _, _, _, _
  | .wildcard, _, _, _ | .agg _, _, _, _ | .arith _ _ _, _, _, _ => rfl

theorem checkConcreteTerms_ok : (ts : List Term) → {sp sp' : Span} → noResidueTerms sp ts = .ok () →
    checkConcreteTerms sp' ts = .ok ()
  | [], _, _, _ => rfl
  | t :: rest, _, _, h => by
    simp only [noResidueTerms, seq_eq_ok] at h
    simp only [checkConcreteTerms, checkConcreteTerm_ok t h.1, checkConcreteTerms_ok rest h.2]
    rfl

end

theorem predArgs_concrete {sp sp' : Span} : {args : List NamedArg} → noResidueArgs sp args = .ok () →
    (args.forM fun a => checkConcreteTerm sp' a.value) = .ok ()
  | [], _ => rfl
  | ⟨_, t⟩ :: rest, h => by
    simp only [noResidueArgs, seq_eq_ok] at h
    have ih := predArgs_concrete (sp' := sp') h.2
    rw [forM_eq_ok] at ih ⊢
    simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨checkConcreteTerm_ok t h.1, ih⟩

mutual

theorem expandCond_id : (c : Condition) → {defs : List MacroDef} → noResidue c = .ok () →
    expandCond defs c = .ok c
  | ⟨sp, .and l r⟩, defs, h => by
    simp only [noResidue, seq_eq_ok] at h
    simp only [expandCond, expandCond_id l h.1, expandCond_id r h.2]; rfl
  | ⟨sp, .or l r⟩, defs, h => by
    simp only [noResidue, seq_eq_ok] at h
    simp only [expandCond, expandCond_id l h.1, expandCond_id r h.2]; rfl
  | ⟨sp, .not c⟩, defs, h => by
    simp only [noResidue] at h
    simp only [expandCond, expandCond_id c h]; rfl
  | ⟨sp, .formerly w b⟩, defs, h => by
    simp only [noResidue, seq_eq_ok] at h
    simp only [expandCond, checkConcreteWithin_ok h.1, expandCond_id b h.2]; rfl
  | ⟨sp, .previous w b⟩, defs, h => by
    simp only [noResidue, seq_eq_ok] at h
    simp only [expandCond, checkConcreteWithin_ok h.1, expandCond_id b h.2]; rfl
  | ⟨sp, .since l w r⟩, defs, h => by
    simp only [noResidue, seq_eq_ok] at h
    simp only [expandCond, checkConcreteWithin_ok h.1, expandCond_id l h.2.1,
      expandCond_id r h.2.2]; rfl
  | ⟨sp, .predicate ⟨psp, ns, a, k, args⟩⟩, defs, h => by
    simp only [noResidue] at h
    simp only [expandCond, predArgs_concrete h]; rfl
  | ⟨sp, .comparison op l r⟩, defs, h => by
    simp only [noResidue, seq_eq_ok] at h
    simp only [expandCond, expandOperand_id l h.1, expandOperand_id r h.2]; rfl
  | ⟨sp, .tp v⟩, defs, h => by
    simp only [noResidue] at h
    simp only [expandCond, checkConcreteSlot_ok h]; rfl
  | ⟨sp, .exists v b⟩, defs, h => by
    simp only [noResidue, seq_eq_ok] at h
    simp only [expandCond, checkConcreteSlot_ok h.1, expandCond_id b h.2]; rfl
  | ⟨_, .call _⟩, _, h => by simp [noResidue, residue, err_ne_ok] at h
  | ⟨_, .sigilRef s _⟩, _, h => by cases s <;> simp [noResidue, residue, err_ne_ok] at h
  | ⟨_, .refine _ _ _⟩, _, h => by simp [noResidue, residue, err_ne_ok] at h

theorem expandOperand_id : (t : Term) → {defs : List MacroDef} → {sp sp' : Span} →
    noResidueTerm sp t = .ok () → expandOperand defs sp' t = .ok t
  | .agg ⟨asp, .sum bv vs b⟩, defs, _, _, h => by
    simp only [noResidueTerm, noResidueAgg, seq_eq_ok] at h
    simp only [expandOperand, checkConcreteSlot_ok h.1, slots_ok h.2.1, expandCond_id b h.2.2]; rfl
  | .agg ⟨asp, .count vs b⟩, defs, _, _, h => by
    simp only [noResidueTerm, noResidueAgg, seq_eq_ok] at h
    simp only [expandOperand, slots_ok h.1, expandCond_id b h.2]; rfl
  | .agg ⟨_, .call _⟩, _, _, _, h => by simp [noResidueTerm, noResidueAgg, residue, err_ne_ok] at h
  | .arith op l r, defs, _, _, h => by
    simp only [noResidueTerm, seq_eq_ok] at h
    simp only [expandOperand, expandOperand_id l h.1, expandOperand_id r h.2]; rfl
  | .paramRef _, _, _, _, h => by simp [noResidueTerm, residue, err_ne_ok] at h
  | .binderRef _, _, _, _, h => by simp [noResidueTerm, residue, err_ne_ok] at h
  | .entity _ _, _, _, _, _ | .integer _, _, _, _, _ | .decimal _, _, _, _, _
  | .string _, _, _, _, _ | .bool _, _, _, _, _ | .contextField _, _, _, _, _
  | .scopeField _, _, _, _, _ | .var _, _, _, _, _ | .wildcard, _, _, _, _
  | .array _, _, _, _, _ => rfl

end

theorem ok_bind {ε α β : Type} {a : α} {f : α → Except ε β} : (Except.ok a >>= f) = f a := rfl

theorem expandBlock_id {defs : List MacroDef} {b : Block} (hr : noResidue b.condition = .ok ())
    (hl : checkLeaf b.condition = .ok ()) : expandBlock defs b = .ok b := by
  simp only [expandBlock, expandCond_id b.condition hr, rebaseErr, ok_bind, hr, hl]; rfl

theorem expandBlock_eq {defs : List MacroDef} {b b' : Block} (hr : noResidue b.condition = .ok ())
    (h : expandBlock defs b = .ok b') : b' = b ∧ checkLeaf b.condition = .ok () := by
  obtain ⟨hc, -, hl, hs⟩ := expandBlock_ok h
  rw [expandCond_id b.condition hr] at hc
  have hc' : b.condition = b'.condition := Except.ok.inj hc
  obtain ⟨c, s⟩ := b
  obtain ⟨c', s'⟩ := b'
  simp only at hc' hs hl ⊢
  subst hc' hs
  exact ⟨rfl, hl⟩

mutual

/-- On a macro-free expression, expansion succeeds only when every temporal block passes the
static checks, and then returns the expression (the converse is `expandExpr_id`). -/
theorem expandExpr_eq : (e : Expr) → {defs : List MacroDef} → {e' : Expr} → {ck : Bool} →
    MacroFreeE ck e → expandExpr defs e = .ok e' → e' = e ∧ Expanded e
  | ⟨.call name args, sp⟩, _, _, _, ⟨hq, hargs⟩, h => by
    simp only [expandExpr, bind_eq_ok] at h
    obtain ⟨args', ha, h⟩ := h
    obtain ⟨rfl, hx⟩ := expandExprs_eq args hargs ha
    simp only [hq, if_true, pure_eq_ok] at h
    exact ⟨h.symm, hq, hx⟩
  | ⟨.paramRef _, _⟩, _, _, _, hm, _ => hm.elim
  | ⟨.extension t, _⟩, _, _, _, ⟨hr, _⟩, h => by
    simp only [expandExpr, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨b, hb, rfl⟩ := h
    obtain ⟨rfl, hl⟩ := expandBlock_eq hr hb
    exact ⟨rfl, hr, fun _ => hl⟩
  | ⟨.lit _, _⟩, _, _, _, _, h => by
    simp only [expandExpr, pure_eq_ok] at h; exact ⟨h.symm, trivial⟩
  | ⟨.var _, _⟩, _, _, _, _, h => by
    simp only [expandExpr, pure_eq_ok] at h; exact ⟨h.symm, trivial⟩
  | ⟨.slot _, _⟩, _, _, _, _, h => by
    simp only [expandExpr, pure_eq_ok] at h; exact ⟨h.symm, trivial⟩
  | ⟨.unaryApp _ e, _⟩, _, _, _, hm, h => by
    simp only [expandExpr, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨a, ha, rfl⟩ := h
    obtain ⟨rfl, hx⟩ := expandExpr_eq e hm ha
    exact ⟨rfl, hx⟩
  | ⟨.binaryApp _ l r, _⟩, _, _, _, ⟨hl, hr⟩, h => by
    simp only [expandExpr, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨a, ha, b, hb, rfl⟩ := h
    obtain ⟨rfl, hx⟩ := expandExpr_eq l hl ha
    obtain ⟨rfl, hy⟩ := expandExpr_eq r hr hb
    exact ⟨rfl, hx, hy⟩
  | ⟨.getAttr e _, _⟩, _, _, _, hm, h => by
    simp only [expandExpr, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨a, ha, rfl⟩ := h
    obtain ⟨rfl, hx⟩ := expandExpr_eq e hm ha
    exact ⟨rfl, hx⟩
  | ⟨.hasAttr e _, _⟩, _, _, _, hm, h => by
    simp only [expandExpr, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨a, ha, rfl⟩ := h
    obtain ⟨rfl, hx⟩ := expandExpr_eq e hm ha
    exact ⟨rfl, hx⟩
  | ⟨.like e _, _⟩, _, _, _, hm, h => by
    simp only [expandExpr, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨a, ha, rfl⟩ := h
    obtain ⟨rfl, hx⟩ := expandExpr_eq e hm ha
    exact ⟨rfl, hx⟩
  | ⟨.is e _ none, _⟩, _, _, _, hm, h => by
    simp only [expandExpr, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨a, ha, rfl⟩ := h
    obtain ⟨rfl, hx⟩ := expandExpr_eq e hm ha
    exact ⟨rfl, hx⟩
  | ⟨.is e _ (some x), _⟩, _, _, _, ⟨hl, hr⟩, h => by
    simp only [expandExpr, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨a, ha, b, hb, rfl⟩ := h
    obtain ⟨rfl, hx⟩ := expandExpr_eq e hl ha
    obtain ⟨rfl, hy⟩ := expandExpr_eq x hr hb
    exact ⟨rfl, hx, hy⟩
  | ⟨.ite c t e, _⟩, _, _, _, ⟨h₁, h₂, h₃⟩, h => by
    simp only [expandExpr, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨a, ha, b, hb, d, hd, rfl⟩ := h
    obtain ⟨rfl, hx⟩ := expandExpr_eq c h₁ ha
    obtain ⟨rfl, hy⟩ := expandExpr_eq t h₂ hb
    obtain ⟨rfl, hz⟩ := expandExpr_eq e h₃ hd
    exact ⟨rfl, hx, hy, hz⟩
  | ⟨.set xs, _⟩, _, _, _, hm, h => by
    simp only [expandExpr, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨a, ha, rfl⟩ := h
    obtain ⟨rfl, hx⟩ := expandExprs_eq xs hm ha
    exact ⟨rfl, hx⟩
  | ⟨.record es, _⟩, _, _, _, hm, h => by
    simp only [expandExpr, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨a, ha, rfl⟩ := h
    obtain ⟨rfl, hx⟩ := expandEntries_eq es hm ha
    exact ⟨rfl, hx⟩
  | ⟨.methodCall r _ args, _⟩, _, _, _, ⟨hl, hr⟩, h => by
    simp only [expandExpr, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨a, ha, b, hb, rfl⟩ := h
    obtain ⟨rfl, hx⟩ := expandExpr_eq r hl ha
    obtain ⟨rfl, hy⟩ := expandExprs_eq args hr hb
    exact ⟨rfl, hx, hy⟩

theorem expandExprs_eq : (xs : List Expr) → {defs : List MacroDef} → {xs' : List Expr} →
    {ck : Bool} → MacroFreeL ck xs → expandExprs defs xs = .ok xs' → xs' = xs ∧ MacroFreeL true xs
  | [], _, _, _, _, h => by
    simp only [expandExprs, pure_eq_ok] at h; exact ⟨h.symm, trivial⟩
  | e :: rest, _, _, _, ⟨hl, hr⟩, h => by
    simp only [expandExprs, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨a, ha, b, hb, rfl⟩ := h
    obtain ⟨rfl, hx⟩ := expandExpr_eq e hl ha
    obtain ⟨rfl, hy⟩ := expandExprs_eq rest hr hb
    exact ⟨rfl, hx, hy⟩

theorem expandEntries_eq : (xs : List (String × Expr)) → {defs : List MacroDef} →
    {xs' : List (String × Expr)} → {ck : Bool} → MacroFreeR ck xs →
    expandEntries defs xs = .ok xs' → xs' = xs ∧ MacroFreeR true xs
  | [], _, _, _, _, h => by
    simp only [expandEntries, pure_eq_ok] at h; exact ⟨h.symm, trivial⟩
  | (k, e) :: rest, _, _, _, ⟨hl, hr⟩, h => by
    simp only [expandEntries, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨a, ha, b, hb, rfl⟩ := h
    obtain ⟨rfl, hx⟩ := expandExpr_eq e hl ha
    obtain ⟨rfl, hy⟩ := expandEntries_eq rest hr hb
    exact ⟨rfl, hx, hy⟩

end

mutual

theorem expandExpr_id : (e : Expr) → {defs : List MacroDef} → Expanded e → expandExpr defs e = .ok e
  | ⟨.call name args, sp⟩, _, ⟨hq, hargs⟩ => by
    simp only [expandExpr, expandExprs_id args hargs, hq]; rfl
  | ⟨.paramRef _, _⟩, _, hm => hm.elim
  | ⟨.extension t, _⟩, _, ⟨hr, hl⟩ => by
    simp only [expandExpr, expandBlock_id hr (hl rfl)]; rfl
  | ⟨.lit _, _⟩, _, _ => rfl
  | ⟨.var _, _⟩, _, _ => rfl
  | ⟨.slot _, _⟩, _, _ => rfl
  | ⟨.unaryApp _ e, _⟩, _, hm => by simp only [expandExpr, expandExpr_id e hm]; rfl
  | ⟨.binaryApp _ l r, _⟩, _, ⟨hl, hr⟩ => by
    simp only [expandExpr, expandExpr_id l hl, expandExpr_id r hr]; rfl
  | ⟨.getAttr e _, _⟩, _, hm => by simp only [expandExpr, expandExpr_id e hm]; rfl
  | ⟨.hasAttr e _, _⟩, _, hm => by simp only [expandExpr, expandExpr_id e hm]; rfl
  | ⟨.like e _, _⟩, _, hm => by simp only [expandExpr, expandExpr_id e hm]; rfl
  | ⟨.is e _ none, _⟩, _, hm => by simp only [expandExpr, expandExpr_id e hm]; rfl
  | ⟨.is e _ (some x), _⟩, _, ⟨hl, hr⟩ => by
    simp only [expandExpr, expandExpr_id e hl, expandExpr_id x hr]; rfl
  | ⟨.ite c t e, _⟩, _, ⟨h₁, h₂, h₃⟩ => by
    simp only [expandExpr, expandExpr_id c h₁, expandExpr_id t h₂, expandExpr_id e h₃]; rfl
  | ⟨.set xs, _⟩, _, hm => by simp only [expandExpr, expandExprs_id xs hm]; rfl
  | ⟨.record es, _⟩, _, hm => by simp only [expandExpr, expandEntries_id es hm]; rfl
  | ⟨.methodCall r _ args, _⟩, _, ⟨hl, hr⟩ => by
    simp only [expandExpr, expandExpr_id r hl, expandExprs_id args hr]; rfl

theorem expandExprs_id : (xs : List Expr) → {defs : List MacroDef} → MacroFreeL true xs →
    expandExprs defs xs = .ok xs
  | [], _, _ => rfl
  | e :: rest, _, ⟨hl, hr⟩ => by
    simp only [expandExprs, expandExpr_id e hl, expandExprs_id rest hr]; rfl

theorem expandEntries_id : (xs : List (String × Expr)) → {defs : List MacroDef} →
    MacroFreeR true xs → expandEntries defs xs = .ok xs
  | [], _, _ => rfl
  | (k, e) :: rest, _, ⟨hl, hr⟩ => by
    simp only [expandEntries, expandExpr_id e hl, expandEntries_id rest hr]; rfl

end

theorem expandPolicy_id {defs : List MacroDef} {p : Policy}
    (h : ∀ c ∈ p.conditions, Expanded c.body) : expandPolicy defs p = .ok p := by
  have : p.conditions.mapM (fun c => (do return { c with body := ← expandExpr defs c.body } :
      MacroResult Cond)) = .ok p.conditions := by
    suffices ∀ cs : List Cond, (∀ c ∈ cs, Expanded c.body) →
        cs.mapM (fun c => (do return { c with body := ← expandExpr defs c.body } :
          MacroResult Cond)) = .ok cs from this _ h
    intro cs
    induction cs with
    | nil => intro _; rfl
    | cons c cs ih =>
      intro hcs
      simp only [List.mapM_cons, expandExpr_id c.body (hcs c List.mem_cons_self),
        ih (fun c hc => hcs c (List.mem_cons_of_mem _ hc))]
      rfl
  simp only [expandPolicy, this]; rfl

theorem expandPolicy_eq {defs : List MacroDef} {p p' : Policy}
    (hm : ∀ c ∈ p.conditions, MacroFree c.body) (h : expandPolicy defs p = .ok p') :
    p' = p ∧ ∀ c ∈ p.conditions, Expanded c.body := by
  simp only [expandPolicy, bind_eq_ok, pure_eq_ok] at h
  obtain ⟨cs, hcs, rfl⟩ := h
  suffices ∀ (xs ys : List Cond), (∀ c ∈ xs, MacroFree c.body) →
      xs.mapM (fun c => (do return { c with body := ← expandExpr defs c.body } :
        MacroResult Cond)) = .ok ys → ys = xs ∧ ∀ c ∈ xs, Expanded c.body by
    obtain ⟨rfl, h⟩ := this _ _ hm hcs
    exact ⟨rfl, h⟩
  intro xs
  induction xs with
  | nil =>
    intro ys _ h
    simp only [List.mapM_nil, pure_eq_ok] at h
    exact ⟨h.symm, by simp⟩
  | cons c xs ih =>
    intro ys hm h
    simp only [List.mapM_cons, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨c', hc, ys', hys, rfl⟩ := h
    obtain ⟨e, he, rfl⟩ := hc
    obtain ⟨he', hx⟩ := expandExpr_eq c.body (hm c List.mem_cons_self) he
    obtain ⟨rfl, hy⟩ := ih ys' (fun c hc => hm c (List.mem_cons_of_mem _ hc)) hys
    subst he'
    refine ⟨rfl, ?_⟩
    intro d hd
    rcases List.mem_cons.mp hd with rfl | hd
    · exact hx
    · exact hy d hd

/-- **Expansion is the identity on the macro-free fragment.** On a set with no definition and no
macro syntax, `expand` returns the set unchanged, and succeeds exactly when every temporal block
passes the static checks. -/
theorem expand_macroFree {ps : PolicySet} (hm : SetMacroFree false ps) :
    (∀ ps', expand ps = .ok ps' → ps' = ps) ∧ (expand ps = .ok ps ↔ SetMacroFree true ps) := by
  obtain ⟨hdefs, hm⟩ := hm
  have hcd : checkDefs ps.defs = .ok () := by rw [hdefs]; rfl
  have eq : ∀ ps', expand ps = .ok ps' → ps' = ps ∧ SetMacroFree true ps := by
    intro ps' h
    simp only [expand, atStage_ok, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨-, -, pols, hpols, rfl⟩ := h
    suffices ∀ (xs ys : List Policy), (∀ p ∈ xs, ∀ c ∈ p.conditions, MacroFree c.body) →
        xs.mapM (expandPolicy ps.defs) = .ok ys →
        ys = xs ∧ ∀ p ∈ xs, ∀ c ∈ p.conditions, Expanded c.body by
      obtain ⟨rfl, h⟩ := this _ _ hm hpols
      obtain ⟨policies, defs⟩ := ps
      simp only at hdefs h ⊢
      subst hdefs
      exact ⟨rfl, rfl, h⟩
    intro xs
    induction xs with
    | nil =>
      intro ys _ h
      simp only [List.mapM_nil, pure_eq_ok] at h
      exact ⟨h.symm, by simp⟩
    | cons p xs ih =>
      intro ys hm h
      simp only [List.mapM_cons, bind_eq_ok, pure_eq_ok] at h
      obtain ⟨p', hp, ys', hys, rfl⟩ := h
      obtain ⟨rfl, hx⟩ := expandPolicy_eq (hm p List.mem_cons_self) hp
      obtain ⟨rfl, hy⟩ := ih ys' (fun p hp => hm p (List.mem_cons_of_mem _ hp)) hys
      refine ⟨rfl, ?_⟩
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact hx
      · exact hy q hq
  refine ⟨fun ps' h => (eq ps' h).1, fun h => (eq ps h).2, fun ⟨_, he⟩ => ?_⟩
  have hpols : ps.policies.mapM (expandPolicy ps.defs) = .ok ps.policies := by
    suffices ∀ xs : List Policy, (∀ p ∈ xs, ∀ c ∈ p.conditions, Expanded c.body) →
        xs.mapM (expandPolicy ps.defs) = .ok xs from this _ he
    intro xs
    induction xs with
    | nil => intro _; rfl
    | cons p xs ih =>
      intro hx
      simp only [List.mapM_cons, expandPolicy_id (hx p List.mem_cons_self),
        ih (fun p hp => hx p (List.mem_cons_of_mem _ hp))]
      rfl
  obtain ⟨policies, defs⟩ := ps
  simp only at hdefs hpols
  subst hdefs
  simp only [expand, hcd, hpols]; rfl

/-! ## The library merge -/

theorem mergeLibrary_ok {ps ps' : PolicySet} {lib : List MacroDef} :
    mergeLibrary ps lib = .ok ps' ↔ checkDefs lib = .ok () ∧ ps' = { ps with defs := mergeDefs ps.defs lib } := by
  simp only [mergeLibrary, atStage_ok, seq_eq_ok, pure_eq_ok]
  exact and_congr_right fun _ => eq_comm

/-- After the merge, a name resolves to the policy set's definition when it has one, and to the
library's otherwise. -/
theorem lookup_mergeDefs (own lib : List MacroDef) (n : String) :
    lookup (mergeDefs own lib) n = (lookup own n).or (lookup lib n) := by
  simp only [lookup, mergeDefs, List.find?_append]
  cases h : own.find? (·.name == n) with
  | some d => rfl
  | none =>
    simp only [Option.none_or]
    rw [List.find?_filter]
    congr 1
    funext d
    by_cases hd : d.name = n
    · have hn : ∀ x ∈ own, ¬x.name = n := fun x hx => by simpa using List.find?_eq_none.mp h x hx
      simp only [hd, beq_self_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true]
      simpa using hn
    · simp [hd]

/-- **A policy's own definition takes precedence.** After `mergeLibrary`, a name resolves (by
`lookup`, the registry `expand` reads) to the policy set's own definition when it has one, and
to the library's otherwise. -/
theorem mergeLibrary_lookup {ps ps' : PolicySet} {lib : List MacroDef}
    (h : mergeLibrary ps lib = .ok ps') (n : String) :
    lookup ps'.defs n = (lookup ps.defs n).or (lookup lib n) := by
  obtain ⟨-, rfl⟩ := mergeLibrary_ok.mp h
  exact lookup_mergeDefs _ _ n

theorem mergeLibrary_own {ps ps' : PolicySet} {lib : List MacroDef}
    (h : mergeLibrary ps lib = .ok ps') {n : String} {d : MacroDef} (hd : lookup ps.defs n = some d) :
    lookup ps'.defs n = some d := by
  rw [mergeLibrary_lookup h, hd]; rfl

end Dogwood.Thm.Frontend.Macros
