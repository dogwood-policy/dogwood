import Dogwood.Thm.Frontend.Validate.Interface
import Cedar.Thm.Data.List.Lemmas
import Cedar.Thm.Data.Map

/-!
# Cedar's validator on renamed hoisted reads

The crate lowers a leaf to an attribute of the request context under its own name (`context.<id>`
for a temporal leaf, `context.providers.<id>` for a provider leaf), the specification under
`__dogwood_leaf_<k>`, and each augments the action schema with those attributes in its own way.
`validate_renameHoisted` shows that Cedar's validator (cedar-lean's `Cedar.Validation.validate`)
accepts the specification's lowering against the specification's augmented schema when it accepts
the crate's against the crate's, given that the two schemas have the same entity types and the
same actions, each action's context related by `CtxRel`, and that the lowered rules read the
context as the crate's context-read check guarantees (`renameOk`).

The proof is a simulation of cedar-lean's typechecker (`Cedar.Validation.typeOf`): on related
request environments, with capabilities related by the renaming (`CapRel`), a successful typing of
an expression gives a successful typing of the renamed expression, with the same type. The
renaming is injective on the expressions that occur (`renameHoisted_inj`), which is what keeps the
capabilities' membership tests in step: a renamed read names an attribute `reserved` holds of,
which no other read does.
-/

namespace Dogwood.Thm.Frontend

open Dogwood.Frontend Dogwood.Frontend.Validate
open Cedar.Validation
open Cedar.Spec (Attr EntityUID Expr Prim Var)
open Cedar.Data (Map)

-- The section variables of the mutual theorems below are used through their recursive calls.
set_option linter.unusedSectionVars false

section

variable {tids pids : List String} {ren : Bool → String → Attr} {reserved : Attr → Bool}

/-! ## The renaming -/

theorem renameHoistedList_eq (tids pids : List String) (ren : Bool → String → Attr) :
    (xs : List Expr) → renameHoistedList tids pids ren xs = xs.map (renameHoisted tids pids ren)
  | [] => rfl
  | x :: xs => by simp [renameHoistedList, renameHoistedList_eq tids pids ren xs]

theorem renameHoistedRecord_eq (tids pids : List String) (ren : Bool → String → Attr) :
    (axs : List (Attr × Expr)) →
      renameHoistedRecord tids pids ren axs = axs.map fun ax => (ax.1, renameHoisted tids pids ren ax.2)
  | [] => rfl
  | (a, x) :: axs => by simp [renameHoistedRecord, renameHoistedRecord_eq tids pids ren axs]

/-- The base of a renamed attribute access. -/
def renBase (tids pids : List String) (ren : Bool → String → Attr) (e : Expr) (a : Attr) : Expr :=
  if isContextC e && tids.contains a then .var .context
  else if isContextProvidersC e && pids.contains a then .var .context
  else renameHoisted tids pids ren e

/-- The attribute of a renamed attribute access. -/
def renAttr (tids pids : List String) (ren : Bool → String → Attr) (e : Expr) (a : Attr) : Attr :=
  if isContextC e && tids.contains a then ren true a
  else if isContextProvidersC e && pids.contains a then ren false a
  else a

theorem renameHoisted_getAttr (e : Expr) (a : Attr) :
    renameHoisted tids pids ren (.getAttr e a) =
      .getAttr (renBase tids pids ren e a) (renAttr tids pids ren e a) := by
  simp only [renameHoisted, renBase, renAttr]
  split <;> (try split) <;> rfl

theorem renameHoisted_var (v : Var) : renameHoisted tids pids ren (.var v) = .var v := by
  simp [renameHoisted]

theorem renameHoisted_lit (p : Prim) : renameHoisted tids pids ren (.lit p) = .lit p := by
  simp [renameHoisted]

theorem renameHoisted_eq_var {x : Expr} {v : Var} :
    renameHoisted tids pids ren x = .var v ↔ x = .var v := by
  cases x with
  | getAttr e a => rw [renameHoisted_getAttr]; simp
  | _ => simp [renameHoisted]

theorem renameHoisted_eq_lit {x : Expr} {p : Prim} :
    renameHoisted tids pids ren x = .lit p ↔ x = .lit p := by
  cases x with
  | getAttr e a => rw [renameHoisted_getAttr]; simp
  | _ => simp [renameHoisted]

theorem entityUID?_renameHoisted (x : Expr) :
    entityUID? (renameHoisted tids pids ren x) = entityUID? x := by
  cases x with
  | lit p => simp [renameHoisted, entityUID?]
  | getAttr e a => rw [renameHoisted_getAttr]; simp [entityUID?]
  | _ => simp [renameHoisted, entityUID?]

theorem entityUIDs?_renameHoisted (x : Expr) :
    entityUIDs? (renameHoisted tids pids ren x) = entityUIDs? x := by
  cases x with
  | set xs =>
    simp only [renameHoisted, renameHoistedList_eq, entityUIDs?, List.mapM_map]
    congr 1
    funext y
    exact entityUID?_renameHoisted y
  | getAttr e a => rw [renameHoisted_getAttr]; simp [entityUIDs?]
  | _ => simp [renameHoisted, entityUIDs?]

/-! ## Injectivity -/

mutual

/-- The expression reads no attribute `reserved` holds of off `context`, other than through a
read the renaming renames. -/
def noReserved (tids pids : List String) (reserved : Attr → Bool) : Expr → Bool
  | .getAttr e a =>
    if isContextC e && tids.contains a then true
    else if isContextProvidersC e && pids.contains a then true
    else (!isContextC e || !reserved a) && noReserved tids pids reserved e
  | .lit _ | .var _ => true
  | .ite c t e => noReserved tids pids reserved c && noReserved tids pids reserved t &&
      noReserved tids pids reserved e
  | .and a b | .or a b | .binaryApp _ a b =>
    noReserved tids pids reserved a && noReserved tids pids reserved b
  | .unaryApp _ e | .hasAttr e _ | .extHasAttr e _ _ => noReserved tids pids reserved e
  | .set xs | .call _ xs => noReservedList tids pids reserved xs
  | .record axs => noReservedRecord tids pids reserved axs

def noReservedList (tids pids : List String) (reserved : Attr → Bool) : List Expr → Bool
  | [] => true
  | x :: xs => noReserved tids pids reserved x && noReservedList tids pids reserved xs

def noReservedRecord (tids pids : List String) (reserved : Attr → Bool) :
    List (Attr × Expr) → Bool
  | [] => true
  | (_, x) :: axs => noReserved tids pids reserved x && noReservedRecord tids pids reserved axs

end


theorem isContextC_eq {e : Expr} (h : isContextC e = true) : e = .var .context := by
  cases e with
  | var v => cases v <;> simp_all [isContextC]
  | _ => simp [isContextC] at h

theorem isContextProvidersC_eq {e : Expr} (h : isContextProvidersC e = true) :
    e = .getAttr (.var .context) "providers" := by
  unfold isContextProvidersC at h
  split at h
  · rfl
  · cases h

mutual

theorem noReserved_of_renameOk : (x : Expr) → renameOk tids pids reserved x = true →
    noReserved tids pids reserved x = true
  | .getAttr e a, h => by
    simp only [renameOk] at h
    simp only [noReserved]
    by_cases hc : isContextC e = true
    · rw [if_pos hc] at h
      have he := isContextC_eq hc
      subst he
      by_cases ht : tids.contains a = true
      · rw [if_pos (by simp only [isContextC, ht, Bool.and_self])]
      · simp only [ht, Bool.false_or, Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true'] at h
        have ht' : tids.contains a = false := by simpa using ht
        simp [isContextC, isContextProvidersC, h.2, noReserved]
    · rw [if_neg hc] at h
      have hc' : isContextC e = false := by simpa using hc
      simp only [hc', Bool.false_and, Bool.false_eq_true, if_false, Bool.not_false, Bool.true_or,
        Bool.true_and]
      split
      · rfl
      · rw [if_neg (by assumption)] at h; exact noReserved_of_renameOk e h
  | .hasAttr e a, h => by
    simp only [renameOk] at h
    simp only [noReserved]
    by_cases hc : isContextC e = true
    · rw [isContextC_eq hc]; rfl
    · rw [if_neg hc] at h; exact noReserved_of_renameOk e h
  | .extHasAttr e a _, h => by
    simp only [renameOk] at h
    simp only [noReserved]
    by_cases hc : isContextC e = true
    · rw [isContextC_eq hc]; rfl
    · rw [if_neg hc, Bool.and_eq_true] at h; exact noReserved_of_renameOk e h.2
  | .lit _, _ => rfl
  | .var _, _ => rfl
  | .ite c t e, h => by
    simp only [renameOk, Bool.and_eq_true] at h
    simp only [noReserved, Bool.and_eq_true]
    exact ⟨⟨noReserved_of_renameOk c h.1.1, noReserved_of_renameOk t h.1.2⟩, noReserved_of_renameOk e h.2⟩
  | .and a b, h | .or a b, h | .binaryApp _ a b, h => by
    simp only [renameOk, Bool.and_eq_true] at h
    simp only [noReserved, Bool.and_eq_true]
    exact ⟨noReserved_of_renameOk a h.1, noReserved_of_renameOk b h.2⟩
  | .unaryApp _ e, h => by
    simp only [renameOk] at h
    simp only [noReserved]
    exact noReserved_of_renameOk e h
  | .set xs, h | .call _ xs, h => by
    simp only [renameOk] at h
    simp only [noReserved]
    exact noReservedList_of_renameOk xs h
  | .record axs, h => by
    simp only [renameOk] at h
    simp only [noReserved]
    exact noReservedRecord_of_renameOk axs h

theorem noReservedList_of_renameOk : (xs : List Expr) → renameOkList tids pids reserved xs = true →
    noReservedList tids pids reserved xs = true
  | [], _ => rfl
  | x :: xs, h => by
    simp only [renameOkList, Bool.and_eq_true] at h
    simp only [noReservedList, Bool.and_eq_true]
    exact ⟨noReserved_of_renameOk x h.1, noReservedList_of_renameOk xs h.2⟩

theorem noReservedRecord_of_renameOk : (axs : List (Attr × Expr)) →
    renameOkRecord tids pids reserved axs = true → noReservedRecord tids pids reserved axs = true
  | [], _ => rfl
  | (_, x) :: axs, h => by
    simp only [renameOkRecord, Bool.and_eq_true] at h
    simp only [noReservedRecord, Bool.and_eq_true]
    exact ⟨noReserved_of_renameOk x h.1, noReservedRecord_of_renameOk axs h.2⟩

end

section Injective

variable (hren : ∀ b₁ i₁ b₂ i₂, i₁ ∈ (if b₁ then tids else pids) → i₂ ∈ (if b₂ then tids else pids) →
      ren b₁ i₁ = ren b₂ i₂ → b₁ = b₂ ∧ i₁ = i₂)
    (hres : ∀ b i, reserved (ren b i) = true)

omit hren hres in
/-- A renamed read is of a temporal leaf's attribute, or of a provider leaf's field of
`context.providers`. -/
theorem renamed_shape {e : Expr} {a : Attr}
    (hc : (isContextC e && tids.contains a) = true ∨ (isContextProvidersC e && pids.contains a) = true) :
    ∃ b, renAttr tids pids ren e a = ren b a ∧ a ∈ (if b then tids else pids) ∧
      e = (if b then .var .context else .getAttr (.var .context) "providers") := by
  by_cases h₁ : (isContextC e && tids.contains a) = true
  · refine ⟨true, by unfold renAttr; rw [if_pos h₁], ?_, ?_⟩
    · simp only [Bool.and_eq_true, List.contains_iff_mem] at h₁; simpa using h₁.2
    · simp only [Bool.and_eq_true] at h₁; simpa using isContextC_eq h₁.1
  · have h₂ : (isContextProvidersC e && pids.contains a) = true := hc.resolve_left h₁
    refine ⟨false, by unfold renAttr; rw [if_neg h₁, if_pos h₂], ?_, ?_⟩
    · simp only [Bool.and_eq_true, List.contains_iff_mem] at h₂; simpa using h₂.2
    · simp only [Bool.and_eq_true] at h₂; simpa using isContextProvidersC_eq h₂.1

include hren in
theorem renamed_inj {e e' : Expr} {a a' : Attr}
    (hc : (isContextC e && tids.contains a) = true ∨ (isContextProvidersC e && pids.contains a) = true)
    (hc' : (isContextC e' && tids.contains a') = true ∨ (isContextProvidersC e' && pids.contains a') = true)
    (ha : renAttr tids pids ren e a = renAttr tids pids ren e' a') : e.getAttr a = e'.getAttr a' := by
  obtain ⟨b, hb, hm, he⟩ := renamed_shape (ren := ren) hc
  obtain ⟨b', hb', hm', he'⟩ := renamed_shape (ren := ren) hc'
  rw [hb, hb'] at ha
  obtain ⟨rfl, rfl⟩ := hren b a b' a' hm hm' ha
  rw [he, he']

include hres in
/-- The renamed attribute access of an unrenamed one, against a renamed one: impossible, since a
renamed read names a reserved attribute. -/
theorem renamed_ne_unrenamed {e e' : Expr} {a a' : Attr}
    (hc : (isContextC e && tids.contains a) = true ∨ (isContextProvidersC e && pids.contains a) = true)
    (hc₁' : (isContextC e' && tids.contains a') = false)
    (hc₂' : (isContextProvidersC e' && pids.contains a') = false)
    (hy : ((!isContextC e' || !reserved a') && noReserved tids pids reserved e') = true)
    (hb : renBase tids pids ren e a = renBase tids pids ren e' a')
    (ha : renAttr tids pids ren e a = renAttr tids pids ren e' a') : False := by
  have hb' : renBase tids pids ren e' a' = renameHoisted tids pids ren e' := by
    simp only [renBase, hc₁', hc₂', Bool.false_eq_true, if_false]
  have ha' : renAttr tids pids ren e' a' = a' := by
    simp only [renAttr, hc₁', hc₂', Bool.false_eq_true, if_false]
  have hbase : renBase tids pids ren e a = .var .context := by
    unfold renBase
    rcases hc with hc | hc
    · rw [if_pos hc]
    · split
      · rfl
      · rfl
  have hattr : ∃ b, renAttr tids pids ren e a = ren b a := by
    unfold renAttr
    rcases hc with hc | hc
    · exact ⟨true, by rw [if_pos hc]⟩
    · split
      · exact ⟨true, rfl⟩
      · exact ⟨false, rfl⟩
  rw [hb', hbase] at hb
  have he' : e' = .var .context := renameHoisted_eq_var.mp hb.symm
  have hctx : isContextC e' = true := by rw [he']; rfl
  simp only [hctx, Bool.not_true, Bool.false_or, Bool.and_eq_true, Bool.not_eq_true'] at hy
  obtain ⟨b, hbr⟩ := hattr
  rw [hbr, ha'] at ha
  have := hres b a
  rw [ha, hy.1] at this
  cases this

include hren hres

mutual

/-- **The renaming is injective** on the expressions that read no reserved attribute. -/
theorem renameHoisted_inj : (x y : Expr) → noReserved tids pids reserved x = true →
    noReserved tids pids reserved y = true →
    renameHoisted tids pids ren x = renameHoisted tids pids ren y → x = y
  | .getAttr e a, y, hx, hy, h => by
    cases y with
    | getAttr e' a' =>
      rw [renameHoisted_getAttr, renameHoisted_getAttr] at h
      simp only [Expr.getAttr.injEq] at h
      obtain ⟨hb, ha⟩ := h
      simp only [noReserved] at hx hy
      cases hc₁ : (isContextC e && tids.contains a) <;> cases hc₂ : (isContextProvidersC e && pids.contains a) <;>
        cases hc₁' : (isContextC e' && tids.contains a') <;>
        cases hc₂' : (isContextProvidersC e' && pids.contains a') <;>
        simp only [hc₁, hc₂, hc₁', hc₂', Bool.false_eq_true, if_false, if_true] at hx hy
      -- neither renamed
      · simp only [renBase, renAttr, hc₁, hc₂, hc₁', hc₂', Bool.false_eq_true, if_false] at hb ha
        simp only [Bool.and_eq_true] at hx hy
        rw [renameHoisted_inj e e' hx.2 hy.2 hb, ha]
      all_goals first
        | exact (renamed_ne_unrenamed hres (Or.inr hc₂) hc₁' hc₂' hy hb ha).elim
        | exact (renamed_ne_unrenamed hres (Or.inl hc₁) hc₁' hc₂' hy hb ha).elim
        | exact (renamed_ne_unrenamed hres (Or.inr hc₂') hc₁ hc₂ hx hb.symm ha.symm).elim
        | exact (renamed_ne_unrenamed hres (Or.inl hc₁') hc₁ hc₂ hx hb.symm ha.symm).elim
        | exact renamed_inj hren (Or.inl hc₁) (Or.inl hc₁') ha
        | exact renamed_inj hren (Or.inl hc₁) (Or.inr hc₂') ha
        | exact renamed_inj hren (Or.inr hc₂) (Or.inl hc₁') ha
        | exact renamed_inj hren (Or.inr hc₂) (Or.inr hc₂') ha
    | _ => rw [renameHoisted_getAttr] at h; simp [renameHoisted] at h
  | .lit p, y, _, _, h => by
    cases y with
    | getAttr => rw [renameHoisted_getAttr] at h; simp [renameHoisted] at h
    | _ => simp_all [renameHoisted]
  | .var v, y, _, _, h => by
    cases y with
    | getAttr => rw [renameHoisted_getAttr] at h; simp [renameHoisted] at h
    | _ => simp_all [renameHoisted]
  | .ite c t e, y, hx, hy, h => by
    cases y with
    | ite c' t' e' =>
      simp only [renameHoisted, Expr.ite.injEq] at h
      simp only [noReserved, Bool.and_eq_true] at hx hy
      rw [renameHoisted_inj c c' hx.1.1 hy.1.1 h.1, renameHoisted_inj t t' hx.1.2 hy.1.2 h.2.1,
        renameHoisted_inj e e' hx.2 hy.2 h.2.2]
    | getAttr => rw [renameHoisted_getAttr] at h; simp [renameHoisted] at h
    | _ => simp [renameHoisted] at h
  | .and a b, y, hx, hy, h => by
    cases y with
    | and a' b' =>
      simp only [renameHoisted, Expr.and.injEq] at h
      simp only [noReserved, Bool.and_eq_true] at hx hy
      rw [renameHoisted_inj a a' hx.1 hy.1 h.1, renameHoisted_inj b b' hx.2 hy.2 h.2]
    | getAttr => rw [renameHoisted_getAttr] at h; simp [renameHoisted] at h
    | _ => simp [renameHoisted] at h
  | .or a b, y, hx, hy, h => by
    cases y with
    | or a' b' =>
      simp only [renameHoisted, Expr.or.injEq] at h
      simp only [noReserved, Bool.and_eq_true] at hx hy
      rw [renameHoisted_inj a a' hx.1 hy.1 h.1, renameHoisted_inj b b' hx.2 hy.2 h.2]
    | getAttr => rw [renameHoisted_getAttr] at h; simp [renameHoisted] at h
    | _ => simp [renameHoisted] at h
  | .binaryApp op a b, y, hx, hy, h => by
    cases y with
    | binaryApp op' a' b' =>
      simp only [renameHoisted, Expr.binaryApp.injEq] at h
      simp only [noReserved, Bool.and_eq_true] at hx hy
      rw [h.1, renameHoisted_inj a a' hx.1 hy.1 h.2.1, renameHoisted_inj b b' hx.2 hy.2 h.2.2]
    | getAttr => rw [renameHoisted_getAttr] at h; simp [renameHoisted] at h
    | _ => simp [renameHoisted] at h
  | .unaryApp op a, y, hx, hy, h => by
    cases y with
    | unaryApp op' a' =>
      simp only [renameHoisted, Expr.unaryApp.injEq] at h
      simp only [noReserved] at hx hy
      rw [h.1, renameHoisted_inj a a' hx hy h.2]
    | getAttr => rw [renameHoisted_getAttr] at h; simp [renameHoisted] at h
    | _ => simp [renameHoisted] at h
  | .hasAttr a x, y, hx, hy, h => by
    cases y with
    | hasAttr a' x' =>
      simp only [renameHoisted, Expr.hasAttr.injEq] at h
      simp only [noReserved] at hx hy
      rw [h.2, renameHoisted_inj a a' hx hy h.1]
    | getAttr => rw [renameHoisted_getAttr] at h; simp [renameHoisted] at h
    | _ => simp [renameHoisted] at h
  | .extHasAttr a x xs, y, hx, hy, h => by
    cases y with
    | extHasAttr a' x' xs' =>
      simp only [renameHoisted, Expr.extHasAttr.injEq] at h
      simp only [noReserved] at hx hy
      rw [h.2.1, h.2.2, renameHoisted_inj a a' hx hy h.1]
    | getAttr => rw [renameHoisted_getAttr] at h; simp [renameHoisted] at h
    | _ => simp [renameHoisted] at h
  | .set xs, y, hx, hy, h => by
    cases y with
    | set ys =>
      simp only [renameHoisted, Expr.set.injEq] at h
      simp only [noReserved] at hx hy
      rw [renameHoistedList_inj xs ys hx hy h]
    | getAttr => rw [renameHoisted_getAttr] at h; simp [renameHoisted] at h
    | _ => simp [renameHoisted] at h
  | .call f xs, y, hx, hy, h => by
    cases y with
    | call f' ys =>
      simp only [renameHoisted, Expr.call.injEq] at h
      simp only [noReserved] at hx hy
      rw [h.1, renameHoistedList_inj xs ys hx hy h.2]
    | getAttr => rw [renameHoisted_getAttr] at h; simp [renameHoisted] at h
    | _ => simp [renameHoisted] at h
  | .record axs, y, hx, hy, h => by
    cases y with
    | record ays =>
      simp only [renameHoisted, Expr.record.injEq] at h
      simp only [noReserved] at hx hy
      rw [renameHoistedRecord_inj axs ays hx hy h]
    | getAttr => rw [renameHoisted_getAttr] at h; simp [renameHoisted] at h
    | _ => simp [renameHoisted] at h

theorem renameHoistedList_inj : (xs ys : List Expr) → noReservedList tids pids reserved xs = true →
    noReservedList tids pids reserved ys = true →
    renameHoistedList tids pids ren xs = renameHoistedList tids pids ren ys → xs = ys
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h => by simp [renameHoistedList] at h
  | _ :: _, [], _, _, h => by simp [renameHoistedList] at h
  | x :: xs, y :: ys, hx, hy, h => by
    simp only [renameHoistedList, List.cons.injEq] at h
    simp only [noReservedList, Bool.and_eq_true] at hx hy
    rw [renameHoisted_inj x y hx.1 hy.1 h.1, renameHoistedList_inj xs ys hx.2 hy.2 h.2]

theorem renameHoistedRecord_inj : (axs ays : List (Attr × Expr)) →
    noReservedRecord tids pids reserved axs = true →
    noReservedRecord tids pids reserved ays = true →
    renameHoistedRecord tids pids ren axs = renameHoistedRecord tids pids ren ays → axs = ays
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h => by simp [renameHoistedRecord] at h
  | _ :: _, [], _, _, h => by simp [renameHoistedRecord] at h
  | (a, x) :: axs, (b, y) :: ays, hx, hy, h => by
    simp only [renameHoistedRecord, List.cons.injEq, Prod.mk.injEq] at h
    simp only [noReservedRecord, Bool.and_eq_true] at hx hy
    rw [h.1.1, renameHoisted_inj x y hx.1 hy.1 h.1.2, renameHoistedRecord_inj axs ays hx.2 hy.2 h.2]

end

end Injective


/-! ## Capabilities -/

/-- A capability key, renamed. -/
def renameKey (tids pids : List String) (ren : Bool → String → Attr) : Key → Key
  | .attr a => .attr a
  | .tag t => .tag (renameHoisted tids pids ren t)

/-- A capability key reads no reserved attribute. -/
def keyOk (tids pids : List String) (reserved : Attr → Bool) : Key → Bool
  | .attr _ => true
  | .tag t => noReserved tids pids reserved t

/-- Two capability sets agree up to the renaming, on the expressions that read no reserved
attribute. -/
def CapRel (tids pids : List String) (ren : Bool → String → Attr) (reserved : Attr → Bool)
    (c₁ c₂ : Capabilities) : Prop :=
  ∀ e k, noReserved tids pids reserved e = true → keyOk tids pids reserved k = true →
    ((e, k) ∈ c₁ ↔ (renameHoisted tids pids ren e, renameKey tids pids ren k) ∈ c₂)

theorem CapRel.nil : CapRel tids pids ren reserved [] [] := by
  intro e k _ _; simp

theorem CapRel.union {a b a' b' : Capabilities} (h : CapRel tids pids ren reserved a a')
    (h' : CapRel tids pids ren reserved b b') : CapRel tids pids ren reserved (a ∪ b) (a' ∪ b') := by
  intro e k he hk
  simp only [List.mem_union_iff]
  rw [h e k he hk, h' e k he hk]

theorem CapRel.inter {a b a' b' : Capabilities} (h : CapRel tids pids ren reserved a a')
    (h' : CapRel tids pids ren reserved b b') : CapRel tids pids ren reserved (a ∩ b) (a' ∩ b') := by
  intro e k he hk
  simp only [List.mem_inter_iff]
  rw [h e k he hk, h' e k he hk]

section Singleton

variable (hren : ∀ b₁ i₁ b₂ i₂, i₁ ∈ (if b₁ then tids else pids) → i₂ ∈ (if b₂ then tids else pids) →
      ren b₁ i₁ = ren b₂ i₂ → b₁ = b₂ ∧ i₁ = i₂)
    (hres : ∀ b i, reserved (ren b i) = true)

include hren hres

theorem renameKey_inj {k k' : Key} (hk : keyOk tids pids reserved k = true)
    (hk' : keyOk tids pids reserved k' = true)
    (h : renameKey tids pids ren k = renameKey tids pids ren k') : k = k' := by
  cases k with
  | attr a => cases k' with
    | attr a' => simpa [renameKey] using h
    | tag t' => simp [renameKey] at h
  | tag t => cases k' with
    | attr a' => simp [renameKey] at h
    | tag t' =>
      simp only [renameKey, Key.tag.injEq] at h
      simp only [keyOk] at hk hk'
      rw [renameHoisted_inj hren hres _ _ hk hk' h]

theorem CapRel.singleton {x : Expr} {k : Key} (hx : noReserved tids pids reserved x = true)
    (hk : keyOk tids pids reserved k = true) :
    CapRel tids pids ren reserved (Capabilities.singleton x k)
      (Capabilities.singleton (renameHoisted tids pids ren x) (renameKey tids pids ren k)) := by
  intro e k' he hk'
  simp only [Capabilities.singleton, List.mem_singleton, Prod.mk.injEq]
  constructor
  · rintro ⟨rfl, rfl⟩; exact ⟨rfl, rfl⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨renameHoisted_inj hren hres _ _ he hx h₁, renameKey_inj hren hres hk' hk h₂⟩

end Singleton

/-! ## Related request environments -/

/-- Mapping each action's entry by `f` keeps the actions the action schema contains. -/
theorem mapOnValues_contains {f : ActionSchemaEntry → ActionSchemaEntry} (m : ActionSchema)
    (uid : EntityUID) : ActionSchema.contains (m.mapOnValues f) uid = ActionSchema.contains m uid := by
  simp only [ActionSchema.contains, Map.find?_mapOnValues, Option.isSome_map]

theorem mapOnValues_descendentOf {f : ActionSchemaEntry → ActionSchemaEntry}
    (hf : ∀ e, (f e).ancestors = e.ancestors) (m : ActionSchema) (u₁ u₂ : EntityUID) :
    ActionSchema.descendentOf (m.mapOnValues f) u₁ u₂ = ActionSchema.descendentOf m u₁ u₂ := by
  simp only [ActionSchema.descendentOf, Map.find?_mapOnValues]
  cases m.find? u₁ <;> simp [hf]

theorem mapOnValues_toList {f : ActionSchemaEntry → ActionSchemaEntry} (m : ActionSchema) :
    (m.mapOnValues f).toList = m.toList.map fun (k, v) => (k, f v) := by
  simp [Map.mapOnValues, Map.toList]

theorem mapOnValues_maybeDescendentOf {f : ActionSchemaEntry → ActionSchemaEntry}
    (hf : ∀ e, (f e).ancestors = e.ancestors) (m : ActionSchema) (e₁ e₂ : Cedar.Spec.EntityType) :
    ActionSchema.maybeDescendentOf (m.mapOnValues f) e₁ e₂ = ActionSchema.maybeDescendentOf m e₁ e₂ := by
  simp only [ActionSchema.maybeDescendentOf, mapOnValues_toList, List.any_map, Function.comp_def, hf]

theorem mapOnValues_actionType? {f : ActionSchemaEntry → ActionSchemaEntry} (m : ActionSchema)
    (ety : Cedar.Spec.EntityType) :
    ActionSchema.actionType? (m.mapOnValues f) ety = ActionSchema.actionType? m ety := by
  simp only [ActionSchema.actionType?, Map.keys, mapOnValues_toList, List.map_map, Function.comp_def]


/-! ## Typing results, related -/

/-- A successful typing on the left gives one on the right, of the same type, with related
capabilities. -/
def ResRel (tids pids : List String) (ren : Bool → String → Attr) (reserved : Attr → Bool)
    (r₁ r₂ : ResultType) : Prop :=
  ∀ tx c, r₁ = .ok (tx, c) →
    ∃ ty c', r₂ = .ok (ty, c') ∧ ty.typeOf = tx.typeOf ∧ CapRel tids pids ren reserved c c'

/-- The same, for a typing step that gives a type rather than a typed expression. -/
def TyRel (tids pids : List String) (ren : Bool → String → Attr) (reserved : Attr → Bool)
    (r₁ r₂ : Except TypeError (CedarType × Capabilities)) : Prop :=
  ∀ t c, r₁ = .ok (t, c) → ∃ c', r₂ = .ok (t, c') ∧ CapRel tids pids ren reserved c c'

theorem typeOfIf_rel {r₁ r₁' : TypedExpr × Capabilities} {r₂ r₂' r₃ r₃' : ResultType}
    (h₁ : r₁'.1.typeOf = r₁.1.typeOf) (hc : CapRel tids pids ren reserved r₁.2 r₁'.2)
    (h₂ : ResRel tids pids ren reserved r₂ r₂') (h₃ : ResRel tids pids ren reserved r₃ r₃') :
    ResRel tids pids ren reserved (typeOfIf r₁ r₂ r₃) (typeOfIf r₁' r₂' r₃') := by
  intro tx c h
  unfold typeOfIf at h ⊢
  rw [h₁]
  split at h
  · cases hr₂ : r₂ with
    | error => rw [hr₂] at h; cases h
    | ok p =>
      obtain ⟨ty₂, c₂⟩ := p
      rw [hr₂] at h
      simp only [Except.bind_ok, ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨ty₂', c₂', hr₂', hty₂, hc₂⟩ := h₂ _ _ hr₂
      rw [hr₂']
      exact ⟨_, _, rfl, hty₂, hc.union hc₂⟩
  · cases hr₃ : r₃ with
    | error => rw [hr₃] at h; cases h
    | ok p =>
      obtain ⟨ty₃, c₃⟩ := p
      rw [hr₃] at h
      simp only [Except.bind_ok, ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨ty₃', c₃', hr₃', hty₃, hc₃⟩ := h₃ _ _ hr₃
      rw [hr₃']
      exact ⟨_, _, rfl, hty₃, hc₃⟩
  · cases hr₂ : r₂ with
    | error => rw [hr₂] at h; cases h
    | ok p =>
      obtain ⟨ty₂, c₂⟩ := p
      cases hr₃ : r₃ with
      | error => rw [hr₂, hr₃] at h; cases h
      | ok q =>
        obtain ⟨ty₃, c₃⟩ := q
        rw [hr₂, hr₃] at h
        simp only [Except.bind_ok] at h
        obtain ⟨ty₂', c₂', hr₂', hty₂, hc₂⟩ := h₂ _ _ hr₂
        obtain ⟨ty₃', c₃', hr₃', hty₃, hc₃⟩ := h₃ _ _ hr₃
        rw [hr₂', hr₃']
        simp only [Except.bind_ok, hty₂, hty₃]
        split at h
        · rename_i ty hlub
          simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h ⊢
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨_, _, ⟨rfl, rfl⟩, rfl, (hc.union hc₂).inter hc₃⟩
        · cases h
  · cases h

theorem typeOfAnd_rel {r₁ r₁' : TypedExpr × Capabilities} {r₂ r₂' : ResultType}
    (h₁ : r₁'.1.typeOf = r₁.1.typeOf) (hc : CapRel tids pids ren reserved r₁.2 r₁'.2)
    (h₂ : ResRel tids pids ren reserved r₂ r₂') :
    ResRel tids pids ren reserved (typeOfAnd r₁ r₂) (typeOfAnd r₁' r₂') := by
  intro tx c h
  unfold typeOfAnd at h ⊢
  rw [h₁]
  split at h
  · simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h ⊢
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨_, _, ⟨rfl, rfl⟩, h₁, CapRel.nil⟩
  · cases hr₂ : r₂ with
    | error => rw [hr₂] at h; cases h
    | ok p =>
      obtain ⟨ty₂, c₂⟩ := p
      rw [hr₂] at h
      simp only [Except.bind_ok] at h
      obtain ⟨ty₂', c₂', hr₂', hty₂, hc₂⟩ := h₂ _ _ hr₂
      rw [hr₂']
      simp only [Except.bind_ok, hty₂]
      split at h <;> (try simp only [ok, err, Except.ok.injEq, Prod.mk.injEq] at h ⊢) <;>
        (try obtain ⟨rfl, rfl⟩ := h) <;>
        first
        | exact ⟨_, _, ⟨rfl, rfl⟩, rfl, CapRel.nil⟩
        | exact ⟨_, _, ⟨rfl, rfl⟩, rfl, hc.union hc₂⟩
  · cases h

theorem typeOfOr_rel {r₁ r₁' : TypedExpr × Capabilities} {r₂ r₂' : ResultType}
    (h₁ : r₁'.1.typeOf = r₁.1.typeOf) (hc : CapRel tids pids ren reserved r₁.2 r₁'.2)
    (h₂ : ResRel tids pids ren reserved r₂ r₂') :
    ResRel tids pids ren reserved (typeOfOr r₁ r₂) (typeOfOr r₁' r₂') := by
  intro tx c h
  unfold typeOfOr at h ⊢
  rw [h₁]
  split at h
  · simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h ⊢
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨_, _, ⟨rfl, rfl⟩, h₁, CapRel.nil⟩
  · cases hr₂ : r₂ with
    | error => rw [hr₂] at h; cases h
    | ok p =>
      obtain ⟨ty₂, c₂⟩ := p
      rw [hr₂] at h
      simp only [Except.bind_ok] at h
      obtain ⟨ty₂', c₂', hr₂', hty₂, hc₂⟩ := h₂ _ _ hr₂
      rw [hr₂']
      simp only [Except.bind_ok, hty₂]
      split at h
      · simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h ⊢
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨_, _, ⟨rfl, rfl⟩, rfl, hc₂⟩
      · cases h
  · cases hr₂ : r₂ with
    | error => rw [hr₂] at h; cases h
    | ok p =>
      obtain ⟨ty₂, c₂⟩ := p
      rw [hr₂] at h
      simp only [Except.bind_ok] at h
      obtain ⟨ty₂', c₂', hr₂', hty₂, hc₂⟩ := h₂ _ _ hr₂
      rw [hr₂']
      simp only [Except.bind_ok, hty₂]
      split at h <;> (try simp only [ok, err, Except.ok.injEq, Prod.mk.injEq] at h ⊢) <;>
        (try obtain ⟨rfl, rfl⟩ := h) <;>
        first
        | exact ⟨_, _, ⟨rfl, rfl⟩, rfl, CapRel.nil⟩
        | exact ⟨_, _, ⟨rfl, rfl⟩, rfl, hc⟩
        | exact ⟨_, _, ⟨rfl, rfl⟩, rfl, hc.inter hc₂⟩
  · cases h

theorem typeOfUnaryApp_rel {op : Cedar.Spec.UnaryOp} {ty ty' : TypedExpr}
    (h : ty'.typeOf = ty.typeOf) :
    ResRel tids pids ren reserved (typeOfUnaryApp op ty) (typeOfUnaryApp op ty') := by
  intro tx c hr
  unfold typeOfUnaryApp at hr ⊢
  rw [h]
  split at hr <;> (try simp only [ok, Function.comp, Except.ok.injEq, Prod.mk.injEq, err] at hr ⊢) <;>
    (try obtain ⟨rfl, rfl⟩ := hr) <;>
    exact ⟨_, _, ⟨rfl, rfl⟩, rfl, CapRel.nil⟩


/-! ## Related request environments -/

/-- A request environment of the crate's augmented schema and the corresponding one of the
specification's: the same entity types and request, the specification's actions the crate's mapped
by `f` (which keeps their ancestors), and contexts related by `CtxRel`. -/
structure EnvRel (tids pids : List String) (ren : Bool → String → Attr) (reserved : Attr → Bool)
    (f : ActionSchemaEntry → ActionSchemaEntry) (env₁ env₂ : TypeEnv) : Prop where
  ets : env₂.ets = env₁.ets
  acts : env₂.acts = env₁.acts.mapOnValues f
  ancestors : ∀ e, (f e).ancestors = e.ancestors
  principal : env₂.reqty.principal = env₁.reqty.principal
  action : env₂.reqty.action = env₁.reqty.action
  resource : env₂.reqty.resource = env₁.reqty.resource
  context : CtxRel tids pids ren reserved env₁.reqty.context env₂.reqty.context
  providers : pids ≠ [] → ∀ q ety, env₁.reqty.context.find? "providers" = some q →
    q.getType ≠ .entity ety

section Env

variable {f : ActionSchemaEntry → ActionSchemaEntry} {env₁ env₂ : TypeEnv}
  (henv : EnvRel tids pids ren reserved f env₁ env₂)

include henv

theorem EnvRel.contains (uid : EntityUID) : env₂.acts.contains uid = env₁.acts.contains uid := by
  rw [henv.acts]; exact mapOnValues_contains _ uid

theorem EnvRel.typeOfLit (p : Prim) : typeOfLit p env₂ = typeOfLit p env₁ := by
  simp only [Cedar.Validation.typeOfLit, henv.ets, henv.contains]

theorem EnvRel.typeOfVar {v : Var} (hv : v ≠ .context) : typeOfVar v env₂ = typeOfVar v env₁ := by
  cases v <;> simp_all [Cedar.Validation.typeOfVar, henv.principal, henv.action, henv.resource]

theorem EnvRel.descendentOf (ety₁ ety₂ : Cedar.Spec.EntityType) :
    env₂.descendentOf ety₁ ety₂ = env₁.descendentOf ety₁ ety₂ := by
  simp only [TypeEnv.descendentOf, henv.ets, henv.acts,
    mapOnValues_maybeDescendentOf henv.ancestors]

theorem EnvRel.actionUID? (x : Expr) :
    actionUID? (renameHoisted tids pids ren x) env₂.acts = actionUID? x env₁.acts := by
  simp only [Cedar.Validation.actionUID?, entityUID?_renameHoisted, henv.contains]

theorem EnvRel.actsDescendentOf (u₁ u₂ : EntityUID) :
    env₂.acts.descendentOf u₁ u₂ = env₁.acts.descendentOf u₁ u₂ := by
  rw [henv.acts]; exact mapOnValues_descendentOf henv.ancestors _ u₁ u₂

theorem EnvRel.actionType? (ety : Cedar.Spec.EntityType) :
    env₂.acts.actionType? ety = env₁.acts.actionType? ety := by
  rw [henv.acts]; exact mapOnValues_actionType? _ ety

theorem EnvRel.typeOfInₑ (ety₁ ety₂ : Cedar.Spec.EntityType) (x₁ x₂ : Expr) :
    typeOfInₑ ety₁ ety₂ (renameHoisted tids pids ren x₁) (renameHoisted tids pids ren x₂) env₂ =
      typeOfInₑ ety₁ ety₂ x₁ x₂ env₁ := by
  simp only [Cedar.Validation.typeOfInₑ, henv.actionUID?, entityUID?_renameHoisted,
    henv.actsDescendentOf, henv.descendentOf]

theorem EnvRel.typeOfInₛ (ety₁ ety₂ : Cedar.Spec.EntityType) (x₁ x₂ : Expr) :
    typeOfInₛ ety₁ ety₂ (renameHoisted tids pids ren x₁) (renameHoisted tids pids ren x₂) env₂ =
      typeOfInₛ ety₁ ety₂ x₁ x₂ env₁ := by
  simp only [Cedar.Validation.typeOfInₛ, henv.actionUID?, entityUIDs?_renameHoisted,
    henv.actsDescendentOf, henv.descendentOf]

end Env


/-! ## The typechecker's steps, on related arguments -/

section Steps

variable (hren : ∀ b₁ i₁ b₂ i₂, i₁ ∈ (if b₁ then tids else pids) → i₂ ∈ (if b₂ then tids else pids) →
      ren b₁ i₁ = ren b₂ i₂ → b₁ = b₂ ∧ i₁ = i₂)
    (hres : ∀ b i, reserved (ren b i) = true)
    {f : ActionSchemaEntry → ActionSchemaEntry} {env₁ env₂ : TypeEnv}
    (henv : EnvRel tids pids ren reserved f env₁ env₂)

omit hren hres in
theorem typeOfEq_rel {ty₁ ty₂ ty₁' ty₂' : TypedExpr} {x₁ x₂ : Expr}
    (h₁ : ty₁'.typeOf = ty₁.typeOf) (h₂ : ty₂'.typeOf = ty₂.typeOf) :
    ResRel tids pids ren reserved (typeOfEq ty₁ ty₂ x₁ x₂)
      (typeOfEq ty₁' ty₂' (renameHoisted tids pids ren x₁) (renameHoisted tids pids ren x₂)) := by
  intro tx c h
  by_cases hl : ∃ p₁ p₂, x₁ = .lit p₁ ∧ x₂ = .lit p₂
  · obtain ⟨p₁, p₂, rfl, rfl⟩ := hl
    simp only [renameHoisted_lit]
    unfold typeOfEq at h ⊢
    simp only at h ⊢
    split at h <;> simp only [ok, Function.comp, Except.ok.injEq, Prod.mk.injEq] at h <;>
      obtain ⟨rfl, rfl⟩ := h <;> rename_i hp <;> simp only [hp, if_true] <;>
      exact ⟨_, _, rfl, rfl, CapRel.nil⟩
  · have hl' : ¬∃ p₁ p₂, renameHoisted tids pids ren x₁ = .lit p₁ ∧
        renameHoisted tids pids ren x₂ = .lit p₂ := by
      simpa only [renameHoisted_eq_lit] using hl
    unfold typeOfEq at h ⊢
    split at h
    · exact (hl ⟨_, _, rfl, rfl⟩).elim
    · split
      · exact (hl' ⟨_, _, by assumption, by assumption⟩).elim
      · rw [h₁, h₂]
        split at h <;> (try simp only [ok, Function.comp, err, Except.ok.injEq, Prod.mk.injEq] at h) <;>
          (try obtain ⟨rfl, rfl⟩ := h)
        · rename_i hlub
          simp only [ok, Function.comp]
          exact ⟨_, _, rfl, rfl, CapRel.nil⟩
        · rename_i hlub
          skip
          split at h <;> (try simp only [Except.ok.injEq, Prod.mk.injEq] at h)
          · obtain ⟨rfl, rfl⟩ := h
            rename_i heq₁ heq₂
            simp only [ok, Function.comp]
            exact ⟨_, _, rfl, rfl, CapRel.nil⟩
          · cases h

include hren hres henv

theorem typeOfHasTag_rel {ety : Cedar.Spec.EntityType} {x t : Expr} {c c' : Capabilities}
    (hx : noReserved tids pids reserved x = true) (ht : noReserved tids pids reserved t = true)
    (hc : CapRel tids pids ren reserved c c') :
    TyRel tids pids ren reserved (typeOfHasTag ety x t c env₁)
      (typeOfHasTag ety (renameHoisted tids pids ren x) (renameHoisted tids pids ren t) c' env₂) := by
  intro ty c₀ h
  unfold typeOfHasTag at h ⊢
  rw [henv.ets, henv.actionType?]
  have hmem := hc x (.tag t) hx ht
  simp only [renameKey] at hmem
  split at h
  · simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h ⊢
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨_, ⟨rfl, rfl⟩, CapRel.nil⟩
  · by_cases hin : (x, Key.tag t) ∈ c
    · rw [if_pos hin] at h
      rw [if_pos (hmem.mp hin)]
      simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h ⊢
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨_, ⟨rfl, rfl⟩, CapRel.nil⟩
    · rw [if_neg hin] at h
      rw [if_neg (fun h' => hin (hmem.mpr h'))]
      simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h ⊢
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨_, ⟨rfl, rfl⟩, CapRel.singleton hren hres hx ht⟩
  · split at h
    · rename_i hact
      rw [if_pos hact]
      simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h ⊢
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨_, ⟨rfl, rfl⟩, CapRel.nil⟩
    · cases h

omit hren hres in
theorem typeOfGetTag_rel {ety : Cedar.Spec.EntityType} {x t : Expr} {c c' : Capabilities}
    (hx : noReserved tids pids reserved x = true) (ht : noReserved tids pids reserved t = true)
    (hc : CapRel tids pids ren reserved c c') :
    TyRel tids pids ren reserved (typeOfGetTag ety x t c env₁)
      (typeOfGetTag ety (renameHoisted tids pids ren x) (renameHoisted tids pids ren t) c' env₂) := by
  intro ty c₀ h
  unfold typeOfGetTag at h ⊢
  rw [henv.ets]
  have hmem := hc x (.tag t) hx ht
  simp only [renameKey] at hmem
  split at h
  · cases h
  · split at h
    · rename_i hin
      rw [if_pos (hmem.mp hin)]
      simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h ⊢
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨_, ⟨rfl, rfl⟩, CapRel.nil⟩
    · cases h
  · cases h

theorem typeOfBinaryApp_rel {op : Cedar.Spec.BinaryOp} {ty₁ ty₂ ty₁' ty₂' : TypedExpr}
    {x₁ x₂ : Expr} {c c' : Capabilities}
    (h₁ : ty₁'.typeOf = ty₁.typeOf) (h₂ : ty₂'.typeOf = ty₂.typeOf)
    (hx₁ : noReserved tids pids reserved x₁ = true) (hx₂ : noReserved tids pids reserved x₂ = true)
    (hc : CapRel tids pids ren reserved c c') :
    ResRel tids pids ren reserved (typeOfBinaryApp op ty₁ ty₂ x₁ x₂ c env₁)
      (typeOfBinaryApp op ty₁' ty₂' (renameHoisted tids pids ren x₁)
        (renameHoisted tids pids ren x₂) c' env₂) := by
  intro tx c₀ h
  unfold typeOfBinaryApp at h ⊢
  rw [h₁, h₂]
  have heq := typeOfEq_rel (tids := tids) (pids := pids) (ren := ren) (reserved := reserved)
    (x₁ := x₁) (x₂ := x₂) h₁ h₂
  generalize ty₁.typeOf = T₁ at h ⊢
  generalize ty₂.typeOf = T₂ at h ⊢
  split at h
  all_goals first
    | cases h
    | exact heq tx c₀ h
    | skip
  all_goals simp only [henv.typeOfInₑ, henv.typeOfInₛ]
  all_goals first
    | exact ⟨_, _, rfl, rfl, CapRel.nil⟩
    | (cases ht : typeOfHasTag _ x₁ x₂ c env₁ with
       | error => rw [ht] at h; cases h
       | ok p =>
         obtain ⟨t, cc⟩ := p
         rw [ht] at h
         simp only [Except.bind_ok, ok, Except.ok.injEq, Prod.mk.injEq] at h
         obtain ⟨rfl, rfl⟩ := h
         obtain ⟨cc', ht', hcc⟩ := typeOfHasTag_rel hren hres henv hx₁ hx₂ hc t cc ht
         rw [ht']
         exact ⟨_, _, rfl, rfl, hcc⟩)
    | (cases ht : typeOfGetTag _ x₁ x₂ c env₁ with
       | error => rw [ht] at h; cases h
       | ok p =>
         obtain ⟨t, cc⟩ := p
         rw [ht] at h
         simp only [Except.bind_ok, ok, Except.ok.injEq, Prod.mk.injEq] at h
         obtain ⟨rfl, rfl⟩ := h
         obtain ⟨cc', ht', hcc⟩ := typeOfGetTag_rel henv hx₁ hx₂ hc t cc ht
         rw [ht']
         exact ⟨_, _, rfl, rfl, hcc⟩)
    | (cases ht : ifLubThenBool _ _ with
       | error => rw [ht] at h; cases h
       | ok p =>
         obtain ⟨t, cc⟩ := p
         rw [ht] at h
         simp only [Except.bind_ok, ok, Except.ok.injEq, Prod.mk.injEq] at h
         obtain ⟨rfl, rfl⟩ := h
         simp only [Except.bind_ok]
         have : cc = [] := by
           unfold ifLubThenBool at ht
           split at ht
           · simp only [ok, Except.ok.injEq, Prod.mk.injEq] at ht; exact ht.2.symm
           · cases ht
         subst this
         exact ⟨_, _, rfl, rfl, CapRel.nil⟩)

omit henv in
theorem hasAttrInRecord_rel {rty : RecordType} {x : Expr} {a : Attr} {c c' : Capabilities}
    {known : Bool} (hx : noReserved tids pids reserved x = true)
    (hc : CapRel tids pids ren reserved c c') :
    TyRel tids pids ren reserved (hasAttrInRecord rty x a c known)
      (hasAttrInRecord rty (renameHoisted tids pids ren x) a c' known) := by
  intro t c₀ h
  have hmem := hc x (.attr a) hx rfl
  simp only [renameKey] at hmem
  have hdec : decide ((renameHoisted tids pids ren x, Key.attr a) ∈ c') =
      decide ((x, Key.attr a) ∈ c) := by
    simp only [hmem]
  unfold hasAttrInRecord at h ⊢
  split at h
  · rename_i qty hfind
    rw [hdec]
    by_cases hb : (decide ((x, Key.attr a) ∈ c) || (qty.isRequired && known)) = true
    · rw [if_pos hb] at h ⊢
      simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h ⊢
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨_, ⟨rfl, rfl⟩, CapRel.nil⟩
    · rw [if_neg hb] at h ⊢
      simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h ⊢
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨_, ⟨rfl, rfl⟩, CapRel.singleton hren hres hx rfl⟩
  · simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h ⊢
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨_, ⟨rfl, rfl⟩, CapRel.nil⟩

omit hren hres henv in
theorem getAttrInRecord_rel {ty ty' : CedarType} {rty : RecordType} {x : Expr} {a : Attr}
    {c c' : Capabilities} (hx : noReserved tids pids reserved x = true)
    (hc : CapRel tids pids ren reserved c c') :
    TyRel tids pids ren reserved (getAttrInRecord ty rty x a c)
      (getAttrInRecord ty' rty (renameHoisted tids pids ren x) a c') := by
  intro t c₀ h
  have hmem := hc x (.attr a) hx rfl
  simp only [renameKey] at hmem
  unfold getAttrInRecord at h ⊢
  split at h
  · simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h ⊢
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨_, ⟨rfl, rfl⟩, CapRel.nil⟩
  · split at h
    · rename_i hin
      rw [if_pos (hmem.mp hin)]
      simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h ⊢
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨_, ⟨rfl, rfl⟩, CapRel.nil⟩
    · cases h
  · cases h

theorem typeOfHasAttr_rel {ty ty' : TypedExpr} {x : Expr} {a : Attr} {c c' : Capabilities}
    (hty : ty'.typeOf = ty.typeOf) (hx : noReserved tids pids reserved x = true)
    (hc : CapRel tids pids ren reserved c c') :
    ResRel tids pids ren reserved (typeOfHasAttr ty x a c env₁)
      (typeOfHasAttr ty' (renameHoisted tids pids ren x) a c' env₂) := by
  intro tx c₀ h
  unfold typeOfHasAttr at h ⊢
  rw [hty, henv.ets]
  simp only [henv.actionType?]
  split at h
  · cases hr : hasAttrInRecord _ x a c true with
    | error => rw [hr] at h; cases h
    | ok p =>
      obtain ⟨t, cc⟩ := p
      rw [hr] at h
      simp only [Except.bind_ok, ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨cc', hr', hcc⟩ := hasAttrInRecord_rel hren hres hx hc t cc hr
      rw [hr']
      exact ⟨_, _, rfl, rfl, hcc⟩
  · split at h
    · cases hr : hasAttrInRecord _ x a c false with
      | error => rw [hr] at h; cases h
      | ok p =>
        obtain ⟨t, cc⟩ := p
        rw [hr] at h
        simp only [Except.bind_ok, ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨cc', hr', hcc⟩ := hasAttrInRecord_rel hren hres hx hc t cc hr
        rename_i hattrs
        simp only [hr', Except.bind_ok]
        exact ⟨_, _, rfl, rfl, hcc⟩
    · rename_i hattrs
      try simp only [hattrs]
      split at h
      · rename_i hact
        rw [if_pos hact]
        simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨_, _, rfl, rfl, CapRel.nil⟩
      · cases h
  · cases h

omit hren hres in
theorem typeOfGetAttr_rel {ty ty' : TypedExpr} {x : Expr} {a : Attr} {c c' : Capabilities}
    (hty : ty'.typeOf = ty.typeOf) (hx : noReserved tids pids reserved x = true)
    (hc : CapRel tids pids ren reserved c c') :
    ResRel tids pids ren reserved (typeOfGetAttr ty x a c env₁)
      (typeOfGetAttr ty' (renameHoisted tids pids ren x) a c' env₂) := by
  intro tx c₀ h
  unfold typeOfGetAttr at h ⊢
  rw [hty, henv.ets]
  split at h
  · cases hr : getAttrInRecord _ _ x a c with
    | error => rw [hr] at h; cases h
    | ok p =>
      obtain ⟨t, cc⟩ := p
      rw [hr] at h
      simp only [Except.bind_ok, ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨cc', hr', hcc⟩ := getAttrInRecord_rel (ty' := ty.typeOf) hx hc t cc hr
      rw [hr']
      exact ⟨_, _, rfl, rfl, hcc⟩
  · split at h
    · cases hr : getAttrInRecord _ _ x a c with
      | error => rw [hr] at h; cases h
      | ok p =>
        obtain ⟨t, cc⟩ := p
        rw [hr] at h
        simp only [Except.bind_ok, ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨cc', hr', hcc⟩ := getAttrInRecord_rel (ty' := ty.typeOf) hx hc t cc hr
        rename_i hattrs
        simp only [hr', Except.bind_ok]
        exact ⟨_, _, rfl, rfl, hcc⟩
    · cases h
  · cases h

omit hren hres henv in
theorem typeOfSet_rel {tys tys' : List TypedExpr}
    (h : tys'.map TypedExpr.typeOf = tys.map TypedExpr.typeOf) :
    ResRel tids pids ren reserved (typeOfSet tys) (typeOfSet tys') := by
  intro tx c₀ hr
  cases tys with
  | nil => simp [typeOfSet, err] at hr
  | cons hd tl =>
    cases tys' with
    | nil => simp at h
    | cons hd' tl' =>
      simp only [List.map_cons, List.cons.injEq] at h
      simp only [typeOfSet] at hr ⊢
      rw [h.1, h.2]
      split at hr
      · simp only [ok, Except.ok.injEq, Prod.mk.injEq] at hr
        obtain ⟨rfl, rfl⟩ := hr
        exact ⟨_, _, rfl, rfl, CapRel.nil⟩
      · cases hr

omit hren hres henv in
theorem typeOfConstructor_rename {α : Type} {mk : String → Option α} {xs : List Expr}
    {ty : CedarType} {p : CedarType × Capabilities} (h : typeOfConstructor mk xs ty = .ok p) :
    typeOfConstructor mk (renameHoistedList tids pids ren xs) ty = .ok p := by
  unfold typeOfConstructor at h
  split at h
  · rename_i s
    simp only [renameHoistedList, renameHoisted_lit, typeOfConstructor]
    exact h
  · cases h

omit hren hres henv in
theorem typeOfCall_rel {xfn : Cedar.Spec.ExtFun} {tys tys' : List TypedExpr} {xs : List Expr}
    (h : tys'.map TypedExpr.typeOf = tys.map TypedExpr.typeOf) :
    ResRel tids pids ren reserved (typeOfCall xfn tys xs)
      (typeOfCall xfn tys' (renameHoistedList tids pids ren xs)) := by
  intro tx c₀ hr
  unfold typeOfCall at hr ⊢
  rw [h]
  split at hr
  all_goals first
    | (cases hr <;> exact ⟨_, _, rfl, rfl, CapRel.nil⟩)
    | (cases ht : typeOfConstructor _ xs _ with
       | error => rw [ht] at hr; cases hr
       | ok p =>
         obtain ⟨t, cc⟩ := p
         rw [ht] at hr
         simp only [Except.bind_ok, ok, Except.ok.injEq, Prod.mk.injEq] at hr
         obtain ⟨rfl, rfl⟩ := hr
         rw [typeOfConstructor_rename ht]
         simp only [Except.bind_ok]
         have : cc = [] := by
           unfold typeOfConstructor at ht
           split at ht
           · split at ht
             · simp only [ok, Except.ok.injEq, Prod.mk.injEq] at ht; exact ht.2.symm
             · cases ht
           · cases ht
         subst this
         exact ⟨_, _, rfl, rfl, CapRel.nil⟩)

/-! ## Extended `has` -/

/-- A typing step that gives a Boolean type: a success on the left gives one on the right, of the
same type, with related capabilities. -/
def BoolRel (tids pids : List String) (ren : Bool → String → Attr) (reserved : Attr → Bool)
    (r₁ r₂ : Except TypeError (BoolType × Capabilities)) : Prop :=
  ∀ b c, r₁ = .ok (b, c) → ∃ c', r₂ = .ok (b, c') ∧ CapRel tids pids ren reserved c c'

/-- `x has a.as` on related operands, given that `x has a` and `x.a` type alike under related
capabilities, and that the rest of the path types alike from `x.a` and its counterpart. -/
theorem typeOfExtHasAttr_rel_of {ty ty' : TypedExpr} {x x' : Expr} {a : Attr} {as : List Attr}
    (hhas : ∀ c c', CapRel tids pids ren reserved c c' →
      ResRel tids pids ren reserved (typeOfHasAttr ty x a c env₁) (typeOfHasAttr ty' x' a c' env₂))
    (hget : ∀ c c', CapRel tids pids ren reserved c c' →
      ResRel tids pids ren reserved (typeOfGetAttr ty x a c env₁) (typeOfGetAttr ty' x' a c' env₂))
    (hrest : ∀ (u u' : TypedExpr) c c', u'.typeOf = u.typeOf → CapRel tids pids ren reserved c c' →
      BoolRel tids pids ren reserved (typeOfExtHasAttr u (.getAttr x a) as c env₁)
        (typeOfExtHasAttr u' (.getAttr x' a) as c' env₂))
    {c c' : Capabilities} (hc : CapRel tids pids ren reserved c c') :
    BoolRel tids pids ren reserved (typeOfExtHasAttr ty x (a :: as) c env₁)
      (typeOfExtHasAttr ty' x' (a :: as) c' env₂) := by
  intro b c₀ h
  cases as with
  | nil =>
    simp only [typeOfExtHasAttr] at h ⊢
    cases hh : typeOfHasAttr ty x a c env₁ with
    | error => rw [hh] at h; cases h
    | ok p =>
      obtain ⟨u, ci⟩ := p
      rw [hh] at h
      obtain ⟨u', ci', hh', hu, hci⟩ := hhas c c' hc u ci hh
      rw [hh']
      simp only [Except.bind_ok] at h ⊢
      rw [hu]
      split at h <;> simp only [Except.ok.injEq, Prod.mk.injEq] at h <;> obtain ⟨rfl, rfl⟩ := h <;>
        exact ⟨_, rfl, hci⟩
  | cons b' bs =>
    simp only [typeOfExtHasAttr] at h ⊢
    cases hh : typeOfHasAttr ty x a c env₁ with
    | error => rw [hh] at h; cases h
    | ok p =>
      obtain ⟨u, ci⟩ := p
      rw [hh] at h
      obtain ⟨u', ci', hh', hu, hci⟩ := hhas c c' hc u ci hh
      rw [hh']
      simp only [Except.bind_ok] at h ⊢
      rw [hu]
      generalize u.typeOf = T at h ⊢
      cases T <;> (try rename_i bt; cases bt) <;> dsimp only at h ⊢
      all_goals first
        | (simp only [Except.ok.injEq, Prod.mk.injEq] at h
           obtain ⟨rfl, rfl⟩ := h
           exact ⟨_, rfl, hci⟩)
        | (cases hg : typeOfGetAttr ty x a (c ∪ ci) env₁ with
           | error => rw [hg] at h; cases h
           | ok q =>
             obtain ⟨v, cv⟩ := q
             rw [hg] at h
             obtain ⟨v', cv', hg', hv, _⟩ := hget (c ∪ ci) (c' ∪ ci') (hc.union hci) v cv hg
             rw [hg']
             simp only [Except.bind_ok] at h ⊢
             cases hr : typeOfExtHasAttr v (.getAttr x a) (b' :: bs) (c ∪ ci) env₁ with
             | error => rw [hr] at h; cases h
             | ok r =>
               obtain ⟨bty, cr⟩ := r
               rw [hr] at h
               obtain ⟨cr', hr', hcr⟩ :=
                 hrest v v' (c ∪ ci) (c' ∪ ci') hv (hc.union hci) bty cr hr
               rw [hr']
               simp only [Except.bind_ok] at h ⊢
               cases bty <;> dsimp only at h ⊢ <;>
                 simp only [Except.ok.injEq, Prod.mk.injEq] at h <;> obtain ⟨rfl, rfl⟩ := h
               all_goals first
                 | exact ⟨_, rfl, CapRel.nil⟩
                 | exact ⟨_, rfl, hci.union hcr⟩)

/-- An operand that is neither `context` nor `context.providers`: no attribute access of it is
renamed. -/
def Deep (x : Expr) : Prop := isContextC x = false ∧ isContextProvidersC x = false

omit hren hres henv in
/-- An attribute access is `context.providers` only off `context`. -/
theorem deep_getAttr {x : Expr} {a : Attr} (hx : x = .var .context → a ≠ "providers") :
    Deep (.getAttr x a) := by
  refine ⟨rfl, ?_⟩
  unfold isContextProvidersC
  split
  · rename_i h
    simp only [Expr.getAttr.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact absurd rfl (hx rfl)
  · rfl

omit hren hres henv in
/-- An attribute access that is not a hoisted read is renamed in its operand only. -/
theorem renameHoisted_getAttr_plain {x : Expr} {a : Attr}
    (hA : (isContextC x && tids.contains a) = false)
    (hB : (isContextProvidersC x && pids.contains a) = false) :
    renameHoisted tids pids ren (.getAttr x a) = .getAttr (renameHoisted tids pids ren x) a := by
  rw [renameHoisted_getAttr]
  simp only [renBase, renAttr, hA, hB, Bool.false_eq_true, if_false]

omit hren hres henv in
theorem noReserved_getAttr_plain {x : Expr} {a : Attr}
    (hA : (isContextC x && tids.contains a) = false)
    (hB : (isContextProvidersC x && pids.contains a) = false) :
    noReserved tids pids reserved (.getAttr x a) =
      ((!isContextC x || !reserved a) && noReserved tids pids reserved x) := by
  simp only [noReserved, hA, hB, Bool.false_eq_true, if_false]

omit hren hres henv in
theorem deep_plainA {x : Expr} (hx : Deep x) (a : Attr) : (isContextC x && tids.contains a) = false := by
  simp [hx.1]

omit hren hres henv in
theorem deep_plainB {x : Expr} (hx : Deep x) (a : Attr) :
    (isContextProvidersC x && pids.contains a) = false := by
  simp [hx.2]

omit hren hres henv in
theorem deep_not_context {x : Expr} (hx : Deep x) : x ≠ .var .context := by
  intro h; subst h; simp [Deep, isContextC] at hx

/-- `x has as`, for an operand none of whose attribute accesses is renamed. -/
theorem typeOfExtHasAttr_rel_deep : ∀ (as : List Attr) (x : Expr), Deep x →
    noReserved tids pids reserved x = true → ∀ (ty ty' : TypedExpr) (c c' : Capabilities),
    ty'.typeOf = ty.typeOf → CapRel tids pids ren reserved c c' →
    BoolRel tids pids ren reserved (typeOfExtHasAttr ty x as c env₁)
      (typeOfExtHasAttr ty' (renameHoisted tids pids ren x) as c' env₂)
  | [], _, _, _, _, _, _, _, _, _ => by
    intro b c₀ h
    unfold typeOfExtHasAttr at h ⊢
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨_, rfl, CapRel.nil⟩
  | a :: as, x, hd, hn, ty, ty', c, c', hty, hc =>
    typeOfExtHasAttr_rel_of hren hres henv
      (fun c c' hc => typeOfHasAttr_rel hren hres henv hty hn hc)
      (fun c c' hc => typeOfGetAttr_rel henv hty hn hc)
      (fun u u' c c' hu hc => by
        have := typeOfExtHasAttr_rel_deep as (.getAttr x a)
          (deep_getAttr fun h => absurd h (deep_not_context hd))
          (by rw [noReserved_getAttr_plain (deep_plainA hd a) (deep_plainB hd a)]; simp [hd.1, hn])
          u u' c c' hu hc
        rwa [renameHoisted_getAttr_plain (deep_plainA hd a) (deep_plainB hd a)] at this) hc



/-! ## The simulation -/

omit hren hres henv in
theorem caps_of_typeOfLit {p : Prim} {env : TypeEnv} {tx : TypedExpr} {c : Capabilities}
    (h : typeOfLit p env = .ok (tx, c)) : c = [] := by
  unfold typeOfLit at h
  split at h <;> (try split at h) <;> simp_all [ok, err, Function.comp]

omit hren hres henv in
theorem caps_of_typeOfVar {v : Var} {env : TypeEnv} {tx : TypedExpr} {c : Capabilities}
    (h : typeOfVar v env = .ok (tx, c)) : c = [] := by
  unfold typeOfVar at h
  split at h <;> simp_all [ok, Function.comp]

omit hren hres henv in
theorem getAttrInRecord_ok {ty t : CedarType} {rty : RecordType} {x : Expr} {a : Attr}
    {c c₀ : Capabilities} (h : getAttrInRecord ty rty x a c = .ok (t, c₀)) :
    ∃ q, rty.find? a = some q ∧ q.getType = t ∧ c₀ = [] := by
  unfold getAttrInRecord at h
  split at h
  · rename_i aty hf
    simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h
    exact ⟨_, hf, h.1, h.2.symm⟩
  · rename_i aty hf
    split at h
    · simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h
      exact ⟨_, hf, h.1, h.2.symm⟩
    · cases h
  · cases h

omit hren hres henv in
theorem getAttrInRecord_required {ty t : CedarType} {rty : RecordType} {x : Expr} {a : Attr}
    {c : Capabilities} (h : rty.find? a = some (.required t)) :
    getAttrInRecord ty rty x a c = .ok (t, []) := by
  unfold getAttrInRecord
  rw [h]
  rfl

omit hren hres henv in
theorem hasAttrInRecord_congr {rty rty' : RecordType} {x : Expr} {a : Attr} {c : Capabilities}
    {known : Bool} (h : rty'.find? a = rty.find? a) :
    hasAttrInRecord rty' x a c known = hasAttrInRecord rty x a c known := by
  unfold hasAttrInRecord; rw [h]

omit hren hres henv in
theorem getAttrInRecord_congr {ty ty' : CedarType} {rty rty' : RecordType} {x : Expr} {a : Attr}
    {c : Capabilities} {t : CedarType} {c₀ : Capabilities} (h : rty'.find? a = rty.find? a)
    (hr : getAttrInRecord ty rty x a c = .ok (t, c₀)) :
    getAttrInRecord ty' rty' x a c = .ok (t, c₀) := by
  unfold getAttrInRecord at hr ⊢
  rw [h]
  split at hr
  · exact hr
  · split at hr
    · rw [if_pos (by assumption)]; exact hr
    · cases hr
  · cases hr

omit hren hres henv in
theorem typeOf_context {c : Capabilities} {env : TypeEnv} :
    typeOf (.var .context) c env = .ok (.var .context (.record env.reqty.context), []) := by
  simp only [typeOf, typeOfVar, ok, Function.comp]; rfl

omit hren hres henv in
theorem typeOf_getAttr_eq {x : Expr} {a : Attr} {c : Capabilities} {env : TypeEnv} :
    typeOf (.getAttr x a) c env = (do let r ← typeOf x c env; typeOfGetAttr r.1 x a c env) := by
  simp only [typeOf]

omit hren hres henv in
theorem typeOfVar_context {env : TypeEnv} :
    typeOfVar .context env = .ok (.var .context (.record env.reqty.context), []) := rfl

omit hren hres henv in
theorem typeOf_getAttr_context {b : Attr} {c c₀ : Capabilities} {env : TypeEnv} {ty : TypedExpr}
    (h : typeOf (.getAttr (.var .context) b) c env = .ok (ty, c₀)) :
    ∃ q, env.reqty.context.find? b = some q ∧ ty.typeOf = q.getType ∧ c₀ = [] := by
  rw [typeOf_getAttr_eq, typeOf_context] at h
  simp only [Except.bind_ok] at h
  unfold typeOfGetAttr at h
  simp only [TypedExpr.typeOf] at h
  cases hr : getAttrInRecord (.record env.reqty.context) env.reqty.context (.var .context) b c with
  | error => rw [hr] at h; cases h
  | ok p =>
    obtain ⟨t, cc⟩ := p
    rw [hr] at h
    simp only [Except.bind_ok, ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨q, hq, hqt, rfl⟩ := getAttrInRecord_ok hr
    exact ⟨q, hq, hqt.symm, rfl⟩

omit hren hres henv in
theorem typeOf_getAttr_context_required {b : Attr} {t : CedarType} {c : Capabilities}
    {env : TypeEnv} (h : env.reqty.context.find? b = some (.required t)) :
    typeOf (.getAttr (.var .context) b) c env =
      .ok (.getAttr (.var .context (.record env.reqty.context)) b t, []) := by
  rw [typeOf_getAttr_eq, typeOf_context]
  simp only [Except.bind_ok]
  unfold typeOfGetAttr
  simp only [TypedExpr.typeOf]
  rw [getAttrInRecord_required h]
  rfl

/-- `context has a`, where the two context record types agree at `a`. -/
theorem typeOfHasAttr_context_rel {a : Attr}
    (hfind : env₂.reqty.context.find? a = env₁.reqty.context.find? a) (c c' : Capabilities)
    (hc : CapRel tids pids ren reserved c c') :
    ResRel tids pids ren reserved
      (typeOfHasAttr (.var .context (.record env₁.reqty.context)) (.var .context) a c env₁)
      (typeOfHasAttr (.var .context (.record env₂.reqty.context)) (.var .context) a c' env₂) := by
  intro tx c₀ h
  unfold typeOfHasAttr at h ⊢
  simp only [TypedExpr.typeOf] at h ⊢
  rw [hasAttrInRecord_congr hfind]
  cases hr : hasAttrInRecord env₁.reqty.context (.var .context) a c true with
  | error => rw [hr] at h; cases h
  | ok p =>
    obtain ⟨t, cc⟩ := p
    rw [hr] at h
    simp only [Except.bind_ok, ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨cc', hr', hcc⟩ := hasAttrInRecord_rel hren hres (x := .var .context) rfl hc t cc hr
    rw [renameHoisted_var] at hr'
    rw [hr']
    exact ⟨_, _, rfl, rfl, hcc⟩

omit hren hres in
/-- `context.a`, where the two context record types agree at `a`. -/
theorem typeOfGetAttr_context_rel {a : Attr}
    (hfind : env₂.reqty.context.find? a = env₁.reqty.context.find? a) (c c' : Capabilities)
    (hc : CapRel tids pids ren reserved c c') :
    ResRel tids pids ren reserved
      (typeOfGetAttr (.var .context (.record env₁.reqty.context)) (.var .context) a c env₁)
      (typeOfGetAttr (.var .context (.record env₂.reqty.context)) (.var .context) a c' env₂) := by
  intro tx c₀ h
  unfold typeOfGetAttr at h ⊢
  simp only [TypedExpr.typeOf] at h ⊢
  cases hr : getAttrInRecord (.record env₁.reqty.context) env₁.reqty.context (.var .context) a c with
  | error => rw [hr] at h; cases h
  | ok p =>
    obtain ⟨t, cc⟩ := p
    rw [hr] at h
    simp only [Except.bind_ok, ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨cc', hr', hcc⟩ := getAttrInRecord_rel (ty' := .record env₁.reqty.context)
      (x := .var .context) rfl hc t cc hr
    rw [renameHoisted_var] at hr'
    rw [getAttrInRecord_congr hfind hr']
    exact ⟨_, _, rfl, rfl, hcc⟩

mutual

/-- **The simulation of the typechecker.** On related request environments, with related
capabilities, a successful typing of an expression the crate's context-read check accepts gives
a successful typing of its renaming, of the same type, with related capabilities. -/
theorem typeOf_rename : (x : Expr) → renameOk tids pids reserved x = true →
    ∀ {c c' : Capabilities}, CapRel tids pids ren reserved c c' →
    ResRel tids pids ren reserved (typeOf x c env₁) (typeOf (renameHoisted tids pids ren x) c' env₂)
  | .lit p, _, c, c', _ => by
    intro tx c₀ h
    simp only [renameHoisted_lit, typeOf] at h ⊢
    rw [henv.typeOfLit, h, caps_of_typeOfLit h]
    exact ⟨tx, [], rfl, rfl, CapRel.nil⟩
  | .var v, hx, c, c', _ => by
    intro tx c₀ h
    simp only [renameOk, bne_iff_ne, ne_eq] at hx
    simp only [renameHoisted_var, typeOf] at h ⊢
    rw [henv.typeOfVar hx, h, caps_of_typeOfVar h]
    exact ⟨tx, [], rfl, rfl, CapRel.nil⟩
  | .ite x₁ x₂ x₃, hx, c, c', hc => by
    simp only [renameOk, Bool.and_eq_true] at hx
    intro tx c₀ h
    simp only [renameHoisted, typeOf] at h ⊢
    cases h₁ : typeOf x₁ c env₁ with
    | error => rw [h₁] at h; cases h
    | ok p =>
      obtain ⟨ty₁, c₁⟩ := p
      rw [h₁] at h
      simp only [Except.bind_ok] at h
      obtain ⟨ty₁', c₁', h₁', hty₁, hc₁⟩ := typeOf_rename x₁ hx.1.1 hc ty₁ c₁ h₁
      rw [h₁']
      simp only [Except.bind_ok]
      exact typeOfIf_rel hty₁ hc₁ (typeOf_rename x₂ hx.1.2 (hc.union hc₁))
        (typeOf_rename x₃ hx.2 hc) tx c₀ h
  | .and x₁ x₂, hx, c, c', hc => by
    simp only [renameOk, Bool.and_eq_true] at hx
    intro tx c₀ h
    simp only [renameHoisted, typeOf] at h ⊢
    cases h₁ : typeOf x₁ c env₁ with
    | error => rw [h₁] at h; cases h
    | ok p =>
      obtain ⟨ty₁, c₁⟩ := p
      rw [h₁] at h
      simp only [Except.bind_ok] at h
      obtain ⟨ty₁', c₁', h₁', hty₁, hc₁⟩ := typeOf_rename x₁ hx.1 hc ty₁ c₁ h₁
      rw [h₁']
      simp only [Except.bind_ok]
      exact typeOfAnd_rel hty₁ hc₁ (typeOf_rename x₂ hx.2 (hc.union hc₁)) tx c₀ h
  | .or x₁ x₂, hx, c, c', hc => by
    simp only [renameOk, Bool.and_eq_true] at hx
    intro tx c₀ h
    simp only [renameHoisted, typeOf] at h ⊢
    cases h₁ : typeOf x₁ c env₁ with
    | error => rw [h₁] at h; cases h
    | ok p =>
      obtain ⟨ty₁, c₁⟩ := p
      rw [h₁] at h
      simp only [Except.bind_ok] at h
      obtain ⟨ty₁', c₁', h₁', hty₁, hc₁⟩ := typeOf_rename x₁ hx.1 hc ty₁ c₁ h₁
      rw [h₁']
      simp only [Except.bind_ok]
      exact typeOfOr_rel hty₁ hc₁ (typeOf_rename x₂ hx.2 hc) tx c₀ h
  | .unaryApp op x₁, hx, c, c', hc => by
    simp only [renameOk] at hx
    intro tx c₀ h
    simp only [renameHoisted, typeOf] at h ⊢
    cases h₁ : typeOf x₁ c env₁ with
    | error => rw [h₁] at h; cases h
    | ok p =>
      obtain ⟨ty₁, c₁⟩ := p
      rw [h₁] at h
      simp only [Except.bind_ok] at h
      obtain ⟨ty₁', c₁', h₁', hty₁, _⟩ := typeOf_rename x₁ hx hc ty₁ c₁ h₁
      rw [h₁']
      simp only [Except.bind_ok]
      exact typeOfUnaryApp_rel hty₁ tx c₀ h
  | .binaryApp op x₁ x₂, hx, c, c', hc => by
    simp only [renameOk, Bool.and_eq_true] at hx
    intro tx c₀ h
    simp only [renameHoisted, typeOf] at h ⊢
    cases h₁ : typeOf x₁ c env₁ with
    | error => rw [h₁] at h; cases h
    | ok p =>
      obtain ⟨ty₁, c₁⟩ := p
      cases h₂ : typeOf x₂ c env₁ with
      | error => rw [h₁, h₂] at h; cases h
      | ok q =>
        obtain ⟨ty₂, c₂⟩ := q
        rw [h₁, h₂] at h
        simp only [Except.bind_ok] at h
        obtain ⟨ty₁', c₁', h₁', hty₁, _⟩ := typeOf_rename x₁ hx.1 hc ty₁ c₁ h₁
        obtain ⟨ty₂', c₂', h₂', hty₂, _⟩ := typeOf_rename x₂ hx.2 hc ty₂ c₂ h₂
        rw [h₁', h₂']
        simp only [Except.bind_ok]
        exact typeOfBinaryApp_rel hren hres henv hty₁ hty₂ (noReserved_of_renameOk x₁ hx.1)
          (noReserved_of_renameOk x₂ hx.2) hc tx c₀ h
  | .hasAttr x₁ a, hx, c, c', hc => by
    simp only [renameOk] at hx
    intro tx c₀ h
    simp only [renameHoisted, typeOf] at h ⊢
    by_cases hctx : isContextC x₁ = true
    · rw [if_pos hctx] at hx
      have := isContextC_eq hctx
      subst this
      simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at hx
      obtain ⟨⟨hnt, hnp⟩, hnr⟩ := hx
      rw [typeOf_context] at h
      rw [renameHoisted_var, typeOf_context]
      simp only [Except.bind_ok] at h ⊢
      unfold typeOfHasAttr at h ⊢
      simp only [TypedExpr.typeOf] at h ⊢
      have hfind := henv.context.other a (by simpa using hnt) hnp hnr
      rw [hasAttrInRecord_congr hfind]
      cases hr : hasAttrInRecord env₁.reqty.context (.var .context) a c true with
      | error => rw [hr] at h; cases h
      | ok p =>
        obtain ⟨t, cc⟩ := p
        rw [hr] at h
        simp only [Except.bind_ok, ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨cc', hr', hcc⟩ := hasAttrInRecord_rel hren hres (x := .var .context) rfl hc t cc hr
        rw [renameHoisted_var] at hr'
        rw [hr']
        exact ⟨_, _, rfl, rfl, hcc⟩
    · rw [if_neg hctx] at hx
      cases h₁ : typeOf x₁ c env₁ with
      | error => rw [h₁] at h; cases h
      | ok p =>
        obtain ⟨ty₁, c₁⟩ := p
        rw [h₁] at h
        simp only [Except.bind_ok] at h
        obtain ⟨ty₁', c₁', h₁', hty₁, _⟩ := typeOf_rename x₁ hx hc ty₁ c₁ h₁
        rw [h₁']
        simp only [Except.bind_ok]
        exact typeOfHasAttr_rel hren hres henv hty₁ (noReserved_of_renameOk x₁ hx) hc tx c₀ h
  | .extHasAttr x₁ a as, hx, c, c', hc => by
    simp only [renameOk] at hx
    intro tx c₀ h
    simp only [renameHoisted, typeOf] at h ⊢
    by_cases hctx : isContextC x₁ = true
    · rw [if_pos hctx] at hx
      have := isContextC_eq hctx
      subst this
      simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at hx
      obtain ⟨⟨hnt, hnp⟩, hnr⟩ := hx
      rw [typeOf_context] at h
      rw [renameHoisted_var, typeOf_context]
      simp only [Except.bind_ok] at h ⊢
      cases hr : typeOfExtHasAttr (.var .context (.record env₁.reqty.context)) (.var .context)
          (a :: as) c env₁ with
      | error => rw [hr] at h; cases h
      | ok p =>
        obtain ⟨bty, cr⟩ := p
        rw [hr] at h
        simp only [Except.bind_ok, ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hfind := henv.context.other a (by simpa using hnt) hnp hnr
        have hA : (isContextC (.var .context) && tids.contains a) = false := by
          simpa [isContextC] using hnt
        have hB : (isContextProvidersC (.var .context) && pids.contains a) = false := by
          simp [isContextProvidersC]
        obtain ⟨cr', hr', hcr⟩ := typeOfExtHasAttr_rel_of hren hres henv
          (typeOfHasAttr_context_rel hren hres henv hfind)
          (typeOfGetAttr_context_rel henv hfind)
          (fun u u' c c' hu hc => by
            have := typeOfExtHasAttr_rel_deep hren hres henv as (.getAttr (.var .context) a)
              (deep_getAttr fun _ => hnp)
              (by rw [noReserved_getAttr_plain hA hB]; simp [isContextC, hnr, noReserved])
              u u' c c' hu hc
            rwa [renameHoisted_getAttr_plain hA hB, renameHoisted_var] at this) hc bty cr hr
        rw [hr']
        simp only [Except.bind_ok, ok]
        exact ⟨_, _, rfl, rfl, hcr⟩
    · rw [if_neg hctx] at hx
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hx
      obtain ⟨hB, hx⟩ := hx
      have hctx' : isContextC x₁ = false := by simpa using hctx
      have hA : (isContextC x₁ && tids.contains a) = false := by simp [hctx']
      cases h₁ : typeOf x₁ c env₁ with
      | error => rw [h₁] at h; cases h
      | ok p =>
        obtain ⟨ty₁, c₁⟩ := p
        rw [h₁] at h
        simp only [Except.bind_ok] at h
        obtain ⟨ty₁', c₁', h₁', hty₁, _⟩ := typeOf_rename x₁ hx hc ty₁ c₁ h₁
        rw [h₁']
        simp only [Except.bind_ok]
        cases hr : typeOfExtHasAttr ty₁ x₁ (a :: as) c env₁ with
        | error => rw [hr] at h; cases h
        | ok q =>
          obtain ⟨bty, cr⟩ := q
          rw [hr] at h
          simp only [Except.bind_ok, ok, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have hn := noReserved_of_renameOk x₁ hx
          obtain ⟨cr', hr', hcr⟩ := typeOfExtHasAttr_rel_of hren hres henv
            (fun c c' hc => typeOfHasAttr_rel hren hres henv hty₁ hn hc)
            (fun c c' hc => typeOfGetAttr_rel henv hty₁ hn hc)
            (fun u u' c c' hu hc => by
              have := typeOfExtHasAttr_rel_deep hren hres henv as (.getAttr x₁ a)
                (deep_getAttr fun h => by subst h; simp [isContextC] at hctx')
                (by rw [noReserved_getAttr_plain hA hB]; simp [hctx', hn])
                u u' c c' hu hc
              rwa [renameHoisted_getAttr_plain hA hB] at this) hc bty cr hr
          rw [hr']
          simp only [Except.bind_ok, ok]
          exact ⟨_, _, rfl, rfl, hcr⟩
  | .getAttr x₁ a, hx, c, c', hc => by
    intro tx c₀ h
    rw [renameHoisted_getAttr]
    by_cases hA : (isContextC x₁ && tids.contains a) = true
    · -- the attribute of a temporal leaf
      have hA' := hA
      simp only [Bool.and_eq_true, List.contains_iff_mem] at hA'
      have hx₁ := isContextC_eq hA'.1
      simp only [renBase, renAttr, if_pos hA]
      subst hx₁
      obtain ⟨q, hq, hqt, rfl⟩ := typeOf_getAttr_context h
      rw [typeOf_getAttr_context_required (henv.context.temporal a (by simpa using hA'.2) q hq)]
      exact ⟨_, _, rfl, hqt.symm, CapRel.nil⟩
    · by_cases hB : (isContextProvidersC x₁ && pids.contains a) = true
      · -- the field of a provider leaf
        have hB' := hB
        simp only [Bool.and_eq_true, List.contains_iff_mem] at hB'
        have hx₁ := isContextProvidersC_eq hB'.1
        have ha : a ∈ pids := by simpa using hB'.2
        simp only [renBase, renAttr, if_neg hA, if_pos hB]
        subst hx₁
        rw [typeOf_getAttr_eq] at h
        cases h₁ : typeOf (.getAttr (.var .context) "providers") c env₁ with
        | error => rw [h₁] at h; cases h
        | ok p =>
          obtain ⟨ty₁, c₁⟩ := p
          rw [h₁] at h
          simp only [Except.bind_ok] at h
          obtain ⟨qp, hqp, hty₁, rfl⟩ := typeOf_getAttr_context h₁
          unfold typeOfGetAttr at h
          rw [hty₁] at h
          cases hpt : qp.getType with
          | record R =>
            rw [hpt] at h
            simp only at h
            cases hr : getAttrInRecord (.record R) R (.getAttr (.var .context) "providers") a c with
            | error => rw [hr] at h; cases h
            | ok r =>
              obtain ⟨t, cc⟩ := r
              rw [hr] at h
              simp only [Except.bind_ok, ok, Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              obtain ⟨q', hq', hq't, rfl⟩ := getAttrInRecord_ok hr
              rw [typeOf_getAttr_context_required
                (henv.context.provider a ha qp R q' hqp hpt hq')]
              exact ⟨_, _, rfl, hq't, CapRel.nil⟩
          | entity ety =>
            exact absurd hpt (henv.providers (List.ne_nil_of_mem ha) qp ety hqp)
          | _ => rw [hpt] at h; cases h
      · simp only [renBase, renAttr, if_neg hA, if_neg hB]
        simp only [renameOk] at hx
        by_cases hctx : isContextC x₁ = true
        · rw [if_pos hctx] at hx
          have hx₁ := isContextC_eq hctx
          subst hx₁
          have hnt : tids.contains a = false := by simpa [isContextC] using hA
          simp only [hnt, Bool.false_or, Bool.and_eq_true, bne_iff_ne, ne_eq,
            Bool.not_eq_true'] at hx
          rw [renameHoisted_var]
          simp only [typeOf] at h ⊢
          rw [typeOfVar_context] at h ⊢
          simp only [Except.bind_ok] at h ⊢
          unfold typeOfGetAttr at h ⊢
          simp only [TypedExpr.typeOf] at h ⊢
          cases hr : getAttrInRecord (.record env₁.reqty.context) env₁.reqty.context (.var .context) a c with
          | error => rw [hr] at h; cases h
          | ok p =>
            obtain ⟨t, cc⟩ := p
            rw [hr] at h
            simp only [Except.bind_ok, ok, Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            obtain ⟨cc', hr', hcc⟩ := getAttrInRecord_rel (ty' := .record env₁.reqty.context)
              (x := .var .context) rfl hc t cc hr
            rw [renameHoisted_var] at hr'
            have hfind := henv.context.other a (by simpa using hnt) hx.1 hx.2
            rw [getAttrInRecord_congr hfind hr']
            exact ⟨_, _, rfl, rfl, hcc⟩
        · rw [if_neg hctx] at hx
          have hB'' : (isContextProvidersC x₁ && pids.contains a) = false := by simpa using hB
          rw [hB''] at hx
          simp only [Bool.false_eq_true, if_false] at hx
          simp only [typeOf] at h ⊢
          cases h₁ : typeOf x₁ c env₁ with
          | error => rw [h₁] at h; cases h
          | ok p =>
            obtain ⟨ty₁, c₁⟩ := p
            rw [h₁] at h
            simp only [Except.bind_ok] at h
            obtain ⟨ty₁', c₁', h₁', hty₁, _⟩ := typeOf_rename x₁ hx hc ty₁ c₁ h₁
            rw [h₁']
            simp only [Except.bind_ok]
            exact typeOfGetAttr_rel henv hty₁ (noReserved_of_renameOk x₁ hx) hc tx c₀ h
  | .set xs, hx, c, c', hc => by
    simp only [renameOk] at hx
    intro tx c₀ h
    simp only [renameHoisted, typeOf] at h ⊢
    rw [List.mapM₁_eq_mapM (fun x => justType (typeOf x c env₁))] at h
    rw [List.mapM₁_eq_mapM (fun x => justType (typeOf x c' env₂)), renameHoistedList_eq]
    cases hs : xs.mapM (fun x => justType (typeOf x c env₁)) with
    | error => rw [hs] at h; cases h
    | ok tys =>
      rw [hs] at h
      simp only [Except.bind_ok] at h
      obtain ⟨tys', hs', htys⟩ := typeOfList_rename xs hx hc tys hs
      rw [hs']
      simp only [Except.bind_ok]
      exact typeOfSet_rel htys tx c₀ h
  | .call xfn xs, hx, c, c', hc => by
    simp only [renameOk] at hx
    intro tx c₀ h
    simp only [renameHoisted, typeOf] at h ⊢
    rw [List.mapM₁_eq_mapM (fun x => justType (typeOf x c env₁))] at h
    rw [List.mapM₁_eq_mapM (fun x => justType (typeOf x c' env₂))]
    cases hs : xs.mapM (fun x => justType (typeOf x c env₁)) with
    | error => rw [hs] at h; cases h
    | ok tys =>
      rw [hs] at h
      simp only [Except.bind_ok] at h
      obtain ⟨tys', hs', htys⟩ := typeOfList_rename xs hx hc tys hs
      have := typeOfCall_rel (tids := tids) (pids := pids) (ren := ren) (reserved := reserved)
        (xfn := xfn) (xs := xs) htys tx c₀ h
      rw [renameHoistedList_eq] at this ⊢
      rw [hs']
      simp only [Except.bind_ok]
      exact this
  | .record axs, hx, c, c', hc => by
    simp only [renameOk] at hx
    intro tx c₀ h
    simp only [renameHoisted, typeOf] at h ⊢
    rw [List.mapM₂_eq_mapM (fun (ax : Attr × Expr) =>
      Except.map (fun y => (ax.1, y.1)) (typeOf ax.2 c env₁))] at h
    rw [List.mapM₂_eq_mapM (fun (ax : Attr × Expr) =>
      Except.map (fun y => (ax.1, y.1)) (typeOf ax.2 c' env₂)), renameHoistedRecord_eq]
    cases hs : axs.mapM (fun (ax : Attr × Expr) => Except.map (fun y => (ax.1, y.1)) (typeOf ax.2 c env₁)) with
    | error => rw [hs] at h; cases h
    | ok atys =>
      rw [hs] at h
      simp only [Except.bind_ok, ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨atys', hs', hatys⟩ := typeOfRecord_rename axs hx hc atys hs
      rw [hs']
      simp only [Except.bind_ok, ok, Except.ok.injEq, Prod.mk.injEq]
      refine ⟨_, _, ⟨rfl, rfl⟩, ?_, CapRel.nil⟩
      show CedarType.record (Map.make (atys'.map fun p => (p.1, Qualified.required p.2.typeOf))) =
        CedarType.record (Map.make (atys.map fun p => (p.1, Qualified.required p.2.typeOf)))
      rw [hatys]

theorem typeOfList_rename : (xs : List Expr) → renameOkList tids pids reserved xs = true →
    ∀ {c c' : Capabilities}, CapRel tids pids ren reserved c c' → ∀ tys,
    xs.mapM (fun x => justType (typeOf x c env₁)) = .ok tys →
    ∃ tys', (xs.map (renameHoisted tids pids ren)).mapM (fun x => justType (typeOf x c' env₂)) =
      .ok tys' ∧ tys'.map TypedExpr.typeOf = tys.map TypedExpr.typeOf
  | [], _, _, _, _, tys, h => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨[], rfl, rfl⟩
  | x :: xs, hx, c, c', hc, tys, h => by
    simp only [renameOkList, Bool.and_eq_true] at hx
    simp only [List.mapM_cons, List.map_cons] at h ⊢
    cases h₁ : typeOf x c env₁ with
    | error e =>
      have hj : justType (typeOf x c env₁) = .error e := by simp [justType, h₁, Except.map]
      rw [hj] at h; cases h
    | ok p =>
      obtain ⟨ty, cc⟩ := p
      have hj : justType (typeOf x c env₁) = .ok ty := by simp [justType, h₁, Except.map]
      rw [hj] at h
      cases h₂ : xs.mapM (fun x => justType (typeOf x c env₁)) with
      | error => rw [h₂] at h; cases h
      | ok tys₀ =>
        rw [h₂] at h
        simp only [Except.bind_ok, pure, Except.pure, Except.ok.injEq] at h
        subst h
        obtain ⟨ty', cc', h₁', hty, _⟩ := typeOf_rename x hx.1 hc ty cc h₁
        obtain ⟨tys', h₂', htys⟩ := typeOfList_rename xs hx.2 hc tys₀ h₂
        have hj' : justType (typeOf (renameHoisted tids pids ren x) c' env₂) = .ok ty' := by
          simp [justType, h₁', Except.map]
        refine ⟨ty' :: tys', ?_, ?_⟩
        · rw [hj', h₂']; rfl
        · simp [hty, htys]


theorem typeOfRecord_rename : (axs : List (Attr × Expr)) →
    renameOkRecord tids pids reserved axs = true →
    ∀ {c c' : Capabilities}, CapRel tids pids ren reserved c c' → ∀ atys,
    axs.mapM (fun (ax : Attr × Expr) => Except.map (fun y => (ax.1, y.1)) (typeOf ax.2 c env₁)) =
      .ok atys →
    ∃ atys', (axs.map fun ax => (ax.1, renameHoisted tids pids ren ax.2)).mapM
        (fun (ax : Attr × Expr) => Except.map (fun y => (ax.1, y.1)) (typeOf ax.2 c' env₂)) =
      .ok atys' ∧
      atys'.map (fun p => (p.1, Qualified.required p.2.typeOf)) =
        atys.map (fun p => (p.1, Qualified.required p.2.typeOf))
  | [], _, _, _, _, atys, h => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨[], rfl, rfl⟩
  | (a, x) :: axs, hx, c, c', hc, atys, h => by
    simp only [renameOkRecord, Bool.and_eq_true] at hx
    simp only [List.mapM_cons, List.map_cons] at h ⊢
    cases h₁ : typeOf x c env₁ with
    | error e =>
      have hj : Except.map (fun y => (a, y.1)) (typeOf x c env₁) = .error e := by
        simp [h₁, Except.map]
      rw [hj] at h; cases h
    | ok p =>
      obtain ⟨ty, cc⟩ := p
      have hj : Except.map (fun y => (a, y.1)) (typeOf x c env₁) = .ok (a, ty) := by
        simp [h₁, Except.map]
      rw [hj] at h
      cases h₂ : axs.mapM (fun (ax : Attr × Expr) => Except.map (fun y => (ax.1, y.1)) (typeOf ax.2 c env₁)) with
      | error => rw [h₂] at h; cases h
      | ok atys₀ =>
        rw [h₂] at h
        simp only [Except.bind_ok, pure, Except.pure, Except.ok.injEq] at h
        subst h
        obtain ⟨ty', cc', h₁', hty, _⟩ := typeOf_rename x hx.1 hc ty cc h₁
        obtain ⟨atys', h₂', hatys⟩ := typeOfRecord_rename axs hx.2 hc atys₀ h₂
        have hj' : Except.map (fun y => (a, y.1)) (typeOf (renameHoisted tids pids ren x) c' env₂) =
            .ok (a, ty') := by
          simp [h₁', Except.map]
        refine ⟨(a, ty') :: atys', ?_, ?_⟩
        · rw [hj', h₂']; rfl
        · simp only [List.map_cons, hty, hatys]

end

end Steps


/-! ## Substituting the action -/

section Substitute

variable {σ : Var → Expr} (hσ : ∀ v, σ v = .var v ∨ ∃ p, σ v = .lit p ∧ v ≠ .context)

include hσ

theorem sigma_context : σ .context = .var .context := by
  rcases hσ .context with h | ⟨_, _, hv⟩
  · exact h
  · exact absurd rfl hv

theorem mapOnVars_eq_context {e : Expr} : mapOnVars σ e = .var .context ↔ e = .var .context := by
  cases e with
  | var v =>
    simp only [mapOnVars]
    rcases hσ v with h | ⟨p, h, hv⟩
    · simp [h]
    · simp [h, hv]
  | _ => simp [mapOnVars]

theorem isContextC_mapOnVars (e : Expr) : isContextC (mapOnVars σ e) = isContextC e := by
  cases h : isContextC e
  · cases h' : isContextC (mapOnVars σ e)
    · rfl
    · have := (mapOnVars_eq_context hσ).mp (isContextC_eq h'); subst this; simp [isContextC] at h
  · rw [isContextC_eq h]; simp only [mapOnVars]
    rcases hσ .context with h | ⟨p, h, hv⟩
    · rw [h]; rfl
    · exact absurd rfl hv

theorem isContextProvidersC_mapOnVars (e : Expr) :
    isContextProvidersC (mapOnVars σ e) = isContextProvidersC e := by
  cases h : isContextProvidersC e
  · cases h' : isContextProvidersC (mapOnVars σ e)
    · rfl
    · have he := isContextProvidersC_eq h'
      cases e with
      | getAttr e' b =>
        simp only [mapOnVars, Expr.getAttr.injEq] at he
        rw [(mapOnVars_eq_context hσ).mp he.1, he.2] at h
        simp [isContextProvidersC] at h
      | var v =>
        simp only [mapOnVars] at he
        rcases hσ v with h₁ | ⟨q, h₁, _⟩ <;> rw [h₁] at he <;> cases he
      | _ => simp [mapOnVars] at he
  · rw [isContextProvidersC_eq h]
    simp only [mapOnVars]
    rcases hσ .context with h₁ | ⟨q, h₁, hv⟩
    · rw [h₁]; rfl
    · exact absurd rfl hv

theorem renameHoisted_sigma (v : Var) : renameHoisted tids pids ren (σ v) = σ v := by
  rcases hσ v with h | ⟨p, h, _⟩ <;> rw [h] <;> simp [renameHoisted]

mutual

theorem mapOnVars_renameHoisted : (x : Expr) →
    mapOnVars σ (renameHoisted tids pids ren x) = renameHoisted tids pids ren (mapOnVars σ x)
  | .getAttr e a => by
    rw [renameHoisted_getAttr]
    simp only [mapOnVars]
    rw [renameHoisted_getAttr]
    simp only [renBase, renAttr, isContextC_mapOnVars hσ, isContextProvidersC_mapOnVars hσ]
    split
    · simp only [mapOnVars]; rw [sigma_context hσ]
    · split
      · simp only [mapOnVars]; rw [sigma_context hσ]
      · rw [mapOnVars_renameHoisted e]
  | .lit _ => by simp [renameHoisted, mapOnVars]
  | .var v => by simp only [renameHoisted, mapOnVars]; exact (renameHoisted_sigma hσ v).symm
  | .ite a b c => by
    simp only [renameHoisted, mapOnVars, mapOnVars_renameHoisted a, mapOnVars_renameHoisted b,
      mapOnVars_renameHoisted c]
  | .and a b => by simp only [renameHoisted, mapOnVars, mapOnVars_renameHoisted a, mapOnVars_renameHoisted b]
  | .or a b => by simp only [renameHoisted, mapOnVars, mapOnVars_renameHoisted a, mapOnVars_renameHoisted b]
  | .binaryApp _ a b => by
    simp only [renameHoisted, mapOnVars, mapOnVars_renameHoisted a, mapOnVars_renameHoisted b]
  | .unaryApp _ a => by simp only [renameHoisted, mapOnVars, mapOnVars_renameHoisted a]
  | .hasAttr a _ => by simp only [renameHoisted, mapOnVars, mapOnVars_renameHoisted a]
  | .extHasAttr a _ _ => by simp only [renameHoisted, mapOnVars, mapOnVars_renameHoisted a]
  | .set xs => by
    simp only [renameHoisted, mapOnVars, List.map₁_eq_map (mapOnVars σ), renameHoistedList_eq]
    rw [mapOnVars_renameHoistedList xs]
  | .call _ xs => by
    simp only [renameHoisted, mapOnVars, List.map₁_eq_map (mapOnVars σ), renameHoistedList_eq]
    rw [mapOnVars_renameHoistedList xs]
  | .record axs => by
    simp only [renameHoisted, mapOnVars, renameHoistedRecord_eq]
    rw [List.map₂_eq_map_snd (mapOnVars σ), List.map₂_eq_map_snd (mapOnVars σ)]
    rw [mapOnVars_renameHoistedRecord axs]

theorem mapOnVars_renameHoistedList : (xs : List Expr) →
    (xs.map (renameHoisted tids pids ren)).map (mapOnVars σ) =
      (xs.map (mapOnVars σ)).map (renameHoisted tids pids ren)
  | [] => rfl
  | x :: xs => by
    simp only [List.map_cons, mapOnVars_renameHoisted x, List.cons.injEq, true_and]
    exact mapOnVars_renameHoistedList xs

theorem mapOnVars_renameHoistedRecord : (axs : List (Attr × Expr)) →
    ((axs.map fun ax => (ax.1, renameHoisted tids pids ren ax.2)).map fun (a, b) => (a, mapOnVars σ b)) =
      ((axs.map fun (a, b) => (a, mapOnVars σ b)).map fun ax => (ax.1, renameHoisted tids pids ren ax.2))
  | [] => rfl
  | (a, x) :: axs => by
    simp only [List.map_cons, mapOnVars_renameHoisted x, List.cons.injEq, true_and]
    exact mapOnVars_renameHoistedRecord axs

end

mutual

theorem renameOk_mapOnVars : (x : Expr) →
    renameOk tids pids reserved (mapOnVars σ x) = renameOk tids pids reserved x
  | .getAttr e a => by
    simp only [mapOnVars, renameOk, isContextC_mapOnVars hσ, isContextProvidersC_mapOnVars hσ,
      renameOk_mapOnVars e]
  | .hasAttr e a => by
    simp only [mapOnVars, renameOk, isContextC_mapOnVars hσ, renameOk_mapOnVars e]
  | .extHasAttr e a _ => by
    simp only [mapOnVars, renameOk, isContextC_mapOnVars hσ, isContextProvidersC_mapOnVars hσ,
      renameOk_mapOnVars e]
  | .lit _ => by simp [mapOnVars, renameOk]
  | .var v => by
    simp only [mapOnVars]
    rcases hσ v with h | ⟨p, h, hv⟩
    · rw [h]
    · rw [h]; simp [renameOk, hv]
  | .ite a b c => by
    simp only [mapOnVars, renameOk, renameOk_mapOnVars a, renameOk_mapOnVars b, renameOk_mapOnVars c]
  | .and a b => by simp only [mapOnVars, renameOk, renameOk_mapOnVars a, renameOk_mapOnVars b]
  | .or a b => by simp only [mapOnVars, renameOk, renameOk_mapOnVars a, renameOk_mapOnVars b]
  | .binaryApp _ a b => by
    simp only [mapOnVars, renameOk, renameOk_mapOnVars a, renameOk_mapOnVars b]
  | .unaryApp _ a => by simp only [mapOnVars, renameOk, renameOk_mapOnVars a]
  | .set xs => by
    simp only [mapOnVars, renameOk, List.map₁_eq_map (mapOnVars σ)]
    exact renameOkList_mapOnVars xs
  | .call _ xs => by
    simp only [mapOnVars, renameOk, List.map₁_eq_map (mapOnVars σ)]
    exact renameOkList_mapOnVars xs
  | .record axs => by
    simp only [mapOnVars, renameOk]
    rw [List.map₂_eq_map_snd (mapOnVars σ)]
    exact renameOkRecord_mapOnVars axs

theorem renameOkList_mapOnVars : (xs : List Expr) →
    renameOkList tids pids reserved (xs.map (mapOnVars σ)) = renameOkList tids pids reserved xs
  | [] => rfl
  | x :: xs => by
    simp only [List.map_cons, renameOkList, renameOk_mapOnVars x, renameOkList_mapOnVars xs]

theorem renameOkRecord_mapOnVars : (axs : List (Attr × Expr)) →
    renameOkRecord tids pids reserved (axs.map fun (a, b) => (a, mapOnVars σ b)) =
      renameOkRecord tids pids reserved axs
  | [] => rfl
  | (a, x) :: axs => by
    simp only [List.map_cons, renameOkRecord, renameOk_mapOnVars x, renameOkRecord_mapOnVars axs]

end

end Substitute


/-! ## Rules, entities, environments -/

theorem renameHoisted_scope (sc : Cedar.Spec.Scope) (v : Var) :
    renameHoisted tids pids ren (sc.toExpr v) = sc.toExpr v := by
  cases sc <;> simp [Cedar.Spec.Scope.toExpr, Var.eqEntityUID, Var.inEntityUID, Var.isEntityType,
    renameHoisted]

theorem renameHoisted_actionScope (sc : Cedar.Spec.ActionScope) :
    renameHoisted tids pids ren sc.toExpr = sc.toExpr := by
  cases sc with
  | actionScope sc => exact renameHoisted_scope sc .action
  | actionInAny es =>
    simp [Cedar.Spec.ActionScope.toExpr, renameHoisted, renameHoistedList_eq, List.map_map,
      Function.comp_def]

theorem renameHoisted_condition (c : Cedar.Spec.Condition) :
    ({ c with body := renameHoisted tids pids ren c.body } : Cedar.Spec.Condition).toExpr =
      renameHoisted tids pids ren c.toExpr := by
  obtain ⟨k, b⟩ := c
  cases k <;> simp [Cedar.Spec.Condition.toExpr, renameHoisted]

theorem renameHoisted_foldl (cs : List Cedar.Spec.Condition) (acc : Expr) :
    (cs.map fun c => ({ c with body := renameHoisted tids pids ren c.body } : Cedar.Spec.Condition)).foldl
        (fun expr c => .and c.toExpr expr) (renameHoisted tids pids ren acc) =
      renameHoisted tids pids ren (cs.foldl (fun expr c => .and c.toExpr expr) acc) := by
  induction cs generalizing acc with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.map_cons, List.foldl_cons]
    rw [renameHoisted_condition, ← ih]
    rfl

theorem toExpr_renamePolicy (p : Cedar.Spec.Policy) :
    (renamePolicy tids pids ren p).toExpr = renameHoisted tids pids ren p.toExpr := by
  simp only [Cedar.Spec.Policy.toExpr, renamePolicy, renameHoisted]
  obtain ⟨_, _, ps, as, rs, cs⟩ := p
  simp only
  cases ps with | principalScope ps =>
  cases rs with | resourceScope rs =>
  simp only [Cedar.Spec.PrincipalScope.toExpr, Cedar.Spec.ResourceScope.toExpr,
    renameHoisted_scope, renameHoisted_actionScope]
  congr 3
  unfold Cedar.Spec.Conditions.toExpr
  rw [← List.map_reverse]
  cases cs.reverse with
  | nil => simp [renameHoisted]
  | cons c rest =>
    simp only [List.map_cons]
    rw [renameHoisted_condition, renameHoisted_foldl]

section Entities

variable {S₁ S₂ : Schema} (hets : S₂.ets = S₁.ets)
    (hcont : ∀ uid, S₂.acts.contains uid = S₁.acts.contains uid)
    (htype : ∀ ety, S₂.acts.actionType? ety = S₁.acts.actionType? ety)

include hets hcont htype

mutual

theorem checkEntities_rename : (x : Expr) → checkEntities S₁ x = .ok () →
    checkEntities S₂ (renameHoisted tids pids ren x) = .ok ()
  | .lit p, h => by
    rw [renameHoisted_lit]
    cases p <;> simp_all [checkEntities]
  | .var v, h => by rw [renameHoisted_var]; simp [checkEntities]
  | .getAttr e a, h => by
    rw [renameHoisted_getAttr]
    simp only [checkEntities] at h ⊢
    unfold renBase
    split
    · simp [checkEntities]
    · split
      · simp [checkEntities]
      · exact checkEntities_rename e h
  | .hasAttr e a, h => by
    simp only [renameHoisted, checkEntities] at h ⊢
    exact checkEntities_rename e h
  | .extHasAttr e a _, h => by
    simp only [renameHoisted, checkEntities] at h ⊢
    exact checkEntities_rename e h
  | .unaryApp op e, h => by
    simp only [renameHoisted]
    cases op with
    | is ety =>
      simp only [checkEntities, hets, htype] at h ⊢
      split at h
      · rw [if_pos (by assumption)]; exact checkEntities_rename e h
      · cases h
    | _ => simp only [checkEntities] at h ⊢; exact checkEntities_rename e h
  | .ite a b c, h => by
    simp only [renameHoisted, checkEntities] at h ⊢
    cases ha : checkEntities S₁ a <;> cases hb : checkEntities S₁ b <;> cases hc : checkEntities S₁ c <;>
      simp only [ha, hb, hc, Except.bind_ok, Except.bind_err] at h <;> (try cases h)
    rw [checkEntities_rename a ha, checkEntities_rename b hb, checkEntities_rename c hc]
    rfl
  | .and a b, h | .or a b, h | .binaryApp _ a b, h => by
    simp only [renameHoisted, checkEntities] at h ⊢
    cases ha : checkEntities S₁ a <;> cases hb : checkEntities S₁ b <;>
      simp only [ha, hb, Except.bind_ok, Except.bind_err] at h <;> (try cases h)
    rw [checkEntities_rename a ha, checkEntities_rename b hb]
    rfl
  | .set xs, h | .call _ xs, h => by
    simp only [renameHoisted, checkEntities] at h ⊢
    have hall : ∀ x ∈ xs, checkEntities S₁ x = .ok () := fun x hx =>
      List.forM_ok_implies_all_ok _ _ h ⟨x, hx⟩ (List.mem_attach _ _)
    apply List.all_ok_implies_forM_ok
    rintro ⟨v, hv⟩ _
    rw [renameHoistedList_eq] at hv
    obtain ⟨x, hx, hxy⟩ := List.mem_map.mp hv
    show checkEntities S₂ v = .ok ()
    rw [← hxy]
    exact checkEntitiesList_rename xs hall x hx
  | .record axs, h => by
    simp only [renameHoisted, checkEntities] at h ⊢
    have hall : ∀ ax ∈ axs, checkEntities S₁ ax.2 = .ok () := by
      intro ax hax
      have := List.forM_ok_implies_all_ok _ _ h
      apply this ⟨ax, List.sizeOf_snd_lt_sizeOf_list hax⟩
      simp only [List.attach₂, List.mem_pmap]
      exact ⟨ax, hax, rfl⟩
    apply List.all_ok_implies_forM_ok
    intro y hy
    have hy' := List.mem_attach₂ hy
    obtain ⟨⟨a, v⟩, _⟩ := y
    simp only at hy' ⊢
    rw [renameHoistedRecord_eq] at hy'
    obtain ⟨ax, hax, hxy⟩ := List.mem_map.mp hy'
    have : v = renameHoisted tids pids ren ax.2 := by
      have := congrArg Prod.snd hxy; simpa using this.symm
    rw [this]
    exact checkEntitiesRecord_rename axs hall ax hax

theorem checkEntitiesList_rename : (xs : List Expr) → (∀ x ∈ xs, checkEntities S₁ x = .ok ()) →
    ∀ x ∈ xs, checkEntities S₂ (renameHoisted tids pids ren x) = .ok ()
  | [], _, _, hx => by cases hx
  | x :: xs, h, y, hy => by
    rcases List.mem_cons.mp hy with hyx | hy
    · rw [hyx]; exact checkEntities_rename x (h x (by simp))
    · exact checkEntitiesList_rename xs (fun z hz => h z (by simp [hz])) y hy

theorem checkEntitiesRecord_rename : (axs : List (Attr × Expr)) →
    (∀ ax ∈ axs, checkEntities S₁ ax.2 = .ok ()) →
    ∀ ax ∈ axs, checkEntities S₂ (renameHoisted tids pids ren ax.2) = .ok ()
  | [], _, _, hx => by cases hx
  | (a, x) :: axs, h, ay, hy => by
    rcases List.mem_cons.mp hy with hyx | hy
    · rw [hyx]; exact checkEntities_rename x (h (a, x) (by simp))
    · exact checkEntitiesRecord_rename axs (fun z hz => h z (by simp [hz])) ay hy

end

end Entities


/-! ## Environments -/

/-- The request environments of a schema, by action, action entry, principal type and resource
type. -/
def envQuads (S : Schema) : List (EntityUID × ActionSchemaEntry × Cedar.Spec.EntityType × Cedar.Spec.EntityType) :=
  S.acts.toList.flatMap fun (a, e) =>
    (e.appliesToPrincipal.toList.product e.appliesToResource.toList).map fun (p, r) => (a, e, p, r)

/-- The request environment of a quadruple, with the context an entry gives. -/
def quadEnv (S : Schema) (ctx : ActionSchemaEntry → RecordType)
    (q : EntityUID × ActionSchemaEntry × Cedar.Spec.EntityType × Cedar.Spec.EntityType) : TypeEnv :=
  { ets := S.ets, acts := S.acts,
    reqty := { principal := q.2.2.1, action := q.1, resource := q.2.2.2, context := ctx q.2.1 } }

theorem environments_eq_quads (S : Schema) :
    S.environments = (envQuads S).map (quadEnv S (·.context)) := by
  show ((S.acts.toList.flatMap (fun (a, e) =>
    (e.appliesToPrincipal.toList.product e.appliesToResource.toList).map (fun (p, r) =>
      ({ principal := p, action := a, resource := r, context := e.context } : RequestType)))).map
    (fun rt => ({ ets := S.ets, acts := S.acts, reqty := rt } : TypeEnv))) = _
  simp only [envQuads, List.map_flatMap, List.map_map]
  rfl

theorem environments_mapOnValues {S₁ S₂ : Schema} {f : ActionSchemaEntry → ActionSchemaEntry}
    (hacts : S₂.acts = S₁.acts.mapOnValues f)
    (hf : ∀ e, (f e).appliesToPrincipal = e.appliesToPrincipal ∧
      (f e).appliesToResource = e.appliesToResource) :
    S₂.environments = (envQuads S₁).map (quadEnv S₂ fun e => (f e).context) := by
  rw [environments_eq_quads]
  have : envQuads S₂ = (envQuads S₁).map fun q => (q.1, f q.2.1, q.2.2) := by
    simp only [envQuads, hacts, mapOnValues_toList, List.flatMap_map, List.map_flatMap, List.map_map]
    congr 1
    funext ae
    obtain ⟨a, e⟩ := ae
    simp only [(hf e).1, (hf e).2]
    rfl
  rw [this, List.map_map]
  rfl

theorem mem_envQuads {S : Schema} {q} (h : q ∈ envQuads S) : (q.1, q.2.1) ∈ S.acts.toList := by
  simp only [envQuads, List.mem_flatMap, List.mem_map] at h
  obtain ⟨⟨a, e⟩, hae, ⟨p, r⟩, _, rfl⟩ := h
  exact hae

/-- Pointwise related successes of a `mapM` give related successes. -/
theorem mapM_typeOf_rel {α : Type} {f₁ f₂ : α → Except ValidationError TypedExpr} :
    (L : List α) → (∀ q ∈ L, ∀ t, f₁ q = .ok t → ∃ t', f₂ q = .ok t' ∧ t'.typeOf = t.typeOf) →
    ∀ ts, L.mapM f₁ = .ok ts → ∃ ts', L.mapM f₂ = .ok ts' ∧ ts'.map TypedExpr.typeOf = ts.map TypedExpr.typeOf
  | [], _, ts, h => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h; exact ⟨[], rfl, rfl⟩
  | q :: L, hpt, ts, h => by
    simp only [List.mapM_cons] at h ⊢
    cases h₁ : f₁ q with
    | error => rw [h₁] at h; cases h
    | ok t =>
      cases h₂ : L.mapM f₁ with
      | error => rw [h₁, h₂] at h; cases h
      | ok ts₀ =>
        rw [h₁, h₂] at h
        simp only [Except.bind_ok, pure, Except.pure, Except.ok.injEq] at h
        subst h
        obtain ⟨t', h₁', ht⟩ := hpt q (by simp) t h₁
        obtain ⟨ts', h₂', hts⟩ := mapM_typeOf_rel L (fun q' hq' => hpt q' (by simp [hq'])) ts₀ h₂
        refine ⟨t' :: ts', ?_, by simp [ht, hts]⟩
        rw [h₁', h₂']; rfl

section Final

variable (hren : ∀ b₁ i₁ b₂ i₂, i₁ ∈ (if b₁ then tids else pids) → i₂ ∈ (if b₂ then tids else pids) →
      ren b₁ i₁ = ren b₂ i₂ → b₁ = b₂ ∧ i₁ = i₂)
    (hres : ∀ b i, reserved (ren b i) = true)

include hren hres

theorem typecheckPolicy_rename {f : ActionSchemaEntry → ActionSchemaEntry} {env₁ env₂ : TypeEnv}
    (henv : EnvRel tids pids ren reserved f env₁ env₂) {p : Cedar.Spec.Policy}
    (hp : renameOk tids pids reserved p.toExpr = true) {tx : TypedExpr}
    (h : typecheckPolicy p env₁ = .ok tx) :
    ∃ tx', typecheckPolicy (renamePolicy tids pids ren p) env₂ = .ok tx' ∧ tx'.typeOf = tx.typeOf := by
  unfold typecheckPolicy at h ⊢
  rw [toExpr_renamePolicy, henv.action]
  let σ : Var → Expr := fun var => match var with
    | .action => .lit (.entityUID env₁.reqty.action)
    | _ => .var var
  have hσ : ∀ v, σ v = .var v ∨ ∃ q, σ v = .lit q ∧ v ≠ .context := by
    intro v; cases v <;> simp [σ]
  have hsub : ∀ x, substituteAction env₁.reqty.action x = mapOnVars σ x := fun _ => rfl
  rw [hsub, mapOnVars_renameHoisted hσ]
  rw [hsub] at h
  have hok : renameOk tids pids reserved (mapOnVars σ p.toExpr) = true := by
    rw [renameOk_mapOnVars hσ]; exact hp
  dsimp only at h ⊢
  simp only [show (∅ : Capabilities) = [] from rfl] at h ⊢
  cases ht : typeOf (mapOnVars σ p.toExpr) [] env₁ with
  | error => rw [ht] at h; cases h
  | ok r =>
    obtain ⟨t, c⟩ := r
    rw [ht] at h
    simp only at h
    obtain ⟨t', c', ht', hty, _⟩ := typeOf_rename hren hres henv _ hok CapRel.nil t c ht
    rw [ht']
    simp only [hty]
    split at h
    · rename_i hsub'
      rw [if_pos hsub']
      simp only [Except.ok.injEq] at h
      subst h
      exact ⟨t', rfl, hty⟩
    · cases h

/-- **Cedar's validator accepts the renamed rules against the related schema** when it accepts
the crate's against the crate's: the schemas have the same entity types, the specification's
actions are the crate's mapped by `f` (which keeps their `appliesTo` and their ancestors, and
relates their contexts by `CtxRel`), and the rules read the context as the crate's context-read
check guarantees. Two side conditions: the crate's action map is well-formed (so that every
environment's action entry is the one `CtxRel` is given for), and, when there is a provider leaf,
no action declares `providers` as an entity (whose attributes would be read through it). -/
theorem validate_renameHoisted {S₁ S₂ : Schema} {xs : Cedar.Spec.Policies}
    {f : ActionSchemaEntry → ActionSchemaEntry}
    (hets : S₂.ets = S₁.ets) (hacts : S₂.acts = S₁.acts.mapOnValues f)
    (hf : ∀ e, (f e).appliesToPrincipal = e.appliesToPrincipal ∧
      (f e).appliesToResource = e.appliesToResource ∧ (f e).ancestors = e.ancestors)
    (hctx : ∀ uid e, S₁.acts.find? uid = some e → CtxRel tids pids ren reserved e.context (f e).context)
    (hwf : S₁.acts.WellFormed)
    (hprov : pids ≠ [] → ∀ uid e q ety, S₁.acts.find? uid = some e →
      e.context.find? "providers" = some q → q.getType ≠ .entity ety)
    (hx : ∀ p ∈ xs, renameOk tids pids reserved p.toExpr = true)
    (h : Cedar.Validation.validate xs S₁ = .ok ()) :
    Cedar.Validation.validate (xs.map (renamePolicy tids pids ren)) S₂ = .ok () := by
  have hcont : ∀ uid, S₂.acts.contains uid = S₁.acts.contains uid := by
    intro uid; rw [hacts]; exact mapOnValues_contains _ uid
  have htype : ∀ ety, S₂.acts.actionType? ety = S₁.acts.actionType? ety := by
    intro ety; rw [hacts]; exact mapOnValues_actionType? _ ety
  unfold Cedar.Validation.validate at h ⊢
  apply List.all_ok_implies_forM_ok
  intro p' hp'
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hp'
  have hp₁ := List.forM_ok_implies_all_ok _ _ h p hp
  unfold typecheckPolicyWithEnvironments at hp₁ ⊢
  cases hce : checkEntities S₁ p.toExpr with
  | error => rw [hce] at hp₁; cases hp₁
  | ok u =>
    rw [hce] at hp₁
    have hce' : checkEntities S₂ (renamePolicy tids pids ren p).toExpr = .ok () := by
      rw [toExpr_renamePolicy]; exact checkEntities_rename hets hcont htype _ hce
    rw [hce']
    simp only [Except.mapError, Except.bind_ok] at hp₁ ⊢
    rw [environments_eq_quads S₁] at hp₁
    rw [environments_mapOnValues hacts (fun e => ⟨(hf e).1, (hf e).2.1⟩)]
    rw [List.mapM_map] at hp₁ ⊢
    cases hm : (envQuads S₁).mapM (typecheckPolicy p ∘ quadEnv S₁ (·.context)) with
    | error => rw [hm] at hp₁; cases hp₁
    | ok tys =>
      rw [hm] at hp₁
      have hpt : ∀ q ∈ envQuads S₁, ∀ t, (typecheckPolicy p ∘ quadEnv S₁ (·.context)) q = .ok t →
          ∃ t', (typecheckPolicy (renamePolicy tids pids ren p) ∘
            quadEnv S₂ (fun e => (f e).context)) q = .ok t' ∧ t'.typeOf = t.typeOf := by
        intro q hq t ht
        have hmem := mem_envQuads hq
        have hfind : S₁.acts.find? q.1 = some q.2.1 := Map.mem_toList_find? hwf hmem
        have henv : EnvRel tids pids ren reserved f (quadEnv S₁ (·.context) q)
            (quadEnv S₂ (fun e => (f e).context) q) :=
          { ets := hets, acts := hacts, ancestors := fun e => (hf e).2.2, principal := rfl,
            action := rfl, resource := rfl, context := hctx q.1 q.2.1 hfind,
            providers := fun hne qq ety hq' => hprov hne q.1 q.2.1 qq ety hfind hq' }
        exact typecheckPolicy_rename hren hres henv (hx p hp) ht
      obtain ⟨tys', hm', htys⟩ := mapM_typeOf_rel _ hpt tys hm
      rw [hm']
      simp only [Except.bind_ok] at hp₁ ⊢
      have hall : allFalse tys' = allFalse tys := by
        have hm : ∀ ts : List TypedExpr, allFalse ts =
            (ts.map TypedExpr.typeOf).all (· == CedarType.bool .ff) := by
          intro ts; simp [allFalse, List.all_map, Function.comp_def]
        rw [hm, hm, htys]
      rw [hall]
      exact hp₁

end Final

end

end Dogwood.Thm.Frontend
