import Dogwood.Thm.Frontend.Validate.CedarRename
import Dogwood.Spec.Validity

/-!
# Cedar's validator on renamed hoisted reads: the converse

`validate_renameHoisted_converse` is the converse of `validate_renameHoisted`: Cedar's validator
(cedar-lean's `Cedar.Validation.validate`) accepts the crate's lowering against the crate's
augmented schema when it accepts the specification's against the specification's, under the same
assumptions, and one more (`graftOk`): in every request environment the rule's scope admits
(`Dogwood.Spec.Policy.admits`), the crate's context declares each hoisted read of the rule as the
crate's lowering reads it, a temporal leaf's `context.<id>` as a required attribute and a provider
leaf's `context.providers.<id>` as a required field of a required `providers` record. `CtxRel`
then gives the read the specification's type.

The proof has two parts.

* **A simulation of the typechecker, backwards** (`typeOf_unrename`): on related request
  environments, with related capabilities, a successful typing of the renamed expression gives a
  successful typing of the crate's, of the same type, when the crate's context declares the
  expression's hoisted reads.
* **Scopes** (`typesFF_policy`): in a request environment the rule's scope does not admit, the
  scope types as `false`, whatever the context, and Cedar's typechecker does not type what follows
  a conjunct typed `false` (`typeOfAnd`); so the crate's rule types there as the specification's
  does without reading the context. The same fact gives `exists_admitted_of_validate`: a rule
  Cedar's validator accepts admits some request environment of the schema.
-/

namespace Dogwood.Thm.Frontend.CedarComplete

open Dogwood.Frontend Dogwood.Frontend.Validate
open Cedar.Validation
open Cedar.Spec (Attr EntityUID Expr Prim Var)
open Cedar.Data (Map)

-- The section variables of the mutual theorems below are used through their recursive calls.
set_option linter.unusedSectionVars false

section

variable {tids pids : List String} {ren : Bool → String → Attr} {reserved : Attr → Bool}

/-! ## Declared hoisted reads -/

/-- The record type declares the attribute `a`, required. -/
def declaredRequired (C : RecordType) (a : Attr) : Bool :=
  match C.find? a with
  | some (.required _) => true
  | _ => false

/-- The record type declares `providers` as a required record, which declares `a`, required. -/
def declaredProvider (C : RecordType) (a : Attr) : Bool :=
  match C.find? "providers" with
  | some (.required (.record R)) => declaredRequired R a
  | _ => false

theorem declaredRequired_iff {C : RecordType} {a : Attr} :
    declaredRequired C a = true ↔ ∃ t, C.find? a = some (.required t) := by
  unfold declaredRequired
  split <;> simp_all

theorem declaredProvider_iff {C : RecordType} {a : Attr} :
    declaredProvider C a = true ↔ ∃ R t, C.find? "providers" = some (.required (.record R)) ∧
      R.find? a = some (.required t) := by
  unfold declaredProvider
  split <;> simp_all [declaredRequired_iff]

mutual

/-- Every hoisted read of the expression is declared in the context record type `C` as the crate's
lowering reads it: `context.<id>` of a temporal leaf `id ∈ tids` as a required attribute, and
`context.providers.<id>` of a provider leaf `id ∈ pids` as a required field of a required
`providers` record. The tests are `renameHoisted`'s. -/
def graftOk (tids pids : List String) (C : RecordType) : Expr → Bool
  | .getAttr e a =>
    if isContextC e && tids.contains a then declaredRequired C a
    else if isContextProvidersC e && pids.contains a then declaredProvider C a
    else graftOk tids pids C e
  | .lit _ | .var _ => true
  | .ite c t e => graftOk tids pids C c && graftOk tids pids C t && graftOk tids pids C e
  | .and a b | .or a b | .binaryApp _ a b => graftOk tids pids C a && graftOk tids pids C b
  | .unaryApp _ e | .hasAttr e _ | .extHasAttr e _ _ => graftOk tids pids C e
  | .set xs | .call _ xs => graftOkList tids pids C xs
  | .record axs => graftOkRecord tids pids C axs

def graftOkList (tids pids : List String) (C : RecordType) : List Expr → Bool
  | [] => true
  | x :: xs => graftOk tids pids C x && graftOkList tids pids C xs

def graftOkRecord (tids pids : List String) (C : RecordType) : List (Attr × Expr) → Bool
  | [] => true
  | (_, x) :: axs => graftOk tids pids C x && graftOkRecord tids pids C axs

end

mutual

/-- A context that declares every temporal leaf's attribute and every provider leaf's field
declares every hoisted read. -/
theorem graftOk_of_forall {C : RecordType} (ht : ∀ a ∈ tids, declaredRequired C a = true)
    (hp : ∀ a ∈ pids, declaredProvider C a = true) : (x : Expr) → graftOk tids pids C x = true
  | .getAttr e a => by
    simp only [graftOk]
    split
    · rename_i h
      simp only [Bool.and_eq_true, List.contains_iff_mem] at h
      exact ht a h.2
    · split
      · rename_i _ h
        simp only [Bool.and_eq_true, List.contains_iff_mem] at h
        exact hp a h.2
      · exact graftOk_of_forall ht hp e
  | .lit _ | .var _ => by simp [graftOk]
  | .ite a b c => by
    simp only [graftOk, graftOk_of_forall ht hp a, graftOk_of_forall ht hp b,
      graftOk_of_forall ht hp c, Bool.and_self]
  | .and a b | .or a b | .binaryApp _ a b => by
    simp only [graftOk, graftOk_of_forall ht hp a, graftOk_of_forall ht hp b, Bool.and_self]
  | .unaryApp _ a | .hasAttr a _ | .extHasAttr a _ _ => by
    simp only [graftOk, graftOk_of_forall ht hp a]
  | .set xs | .call _ xs => by simp only [graftOk, graftOkList_of_forall ht hp xs]
  | .record axs => by simp only [graftOk, graftOkRecord_of_forall ht hp axs]

theorem graftOkList_of_forall {C : RecordType} (ht : ∀ a ∈ tids, declaredRequired C a = true)
    (hp : ∀ a ∈ pids, declaredProvider C a = true) : (xs : List Expr) → graftOkList tids pids C xs = true
  | [] => rfl
  | x :: xs => by simp only [graftOkList, graftOk_of_forall ht hp x, graftOkList_of_forall ht hp xs,
      Bool.and_self]

theorem graftOkRecord_of_forall {C : RecordType} (ht : ∀ a ∈ tids, declaredRequired C a = true)
    (hp : ∀ a ∈ pids, declaredProvider C a = true) :
    (axs : List (Attr × Expr)) → graftOkRecord tids pids C axs = true
  | [] => rfl
  | (_, x) :: axs => by
    simp only [graftOkRecord, graftOk_of_forall ht hp x, graftOkRecord_of_forall ht hp axs,
      Bool.and_self]

end

/-! ## Typing results, related backwards -/

/-- A successful typing on the right (the specification's) gives one on the left (the crate's), of
the same type, with related capabilities. -/
def ResRelB (tids pids : List String) (ren : Bool → String → Attr) (reserved : Attr → Bool)
    (r₁ r₂ : ResultType) : Prop :=
  ∀ ty c', r₂ = .ok (ty, c') →
    ∃ tx c, r₁ = .ok (tx, c) ∧ tx.typeOf = ty.typeOf ∧ CapRel tids pids ren reserved c c'

/-- The same, for a typing step that gives a type rather than a typed expression. -/
def TyRelB (tids pids : List String) (ren : Bool → String → Attr) (reserved : Attr → Bool)
    (r₁ r₂ : Except TypeError (CedarType × Capabilities)) : Prop :=
  ∀ t c', r₂ = .ok (t, c') → ∃ c, r₁ = .ok (t, c) ∧ CapRel tids pids ren reserved c c'

/-- The same, for the typing of an extended `has` path (`typeOfExtHasAttr`), which gives a Boolean
type. -/
def BoolRelB (tids pids : List String) (ren : Bool → String → Attr) (reserved : Attr → Bool)
    (r₁ r₂ : Except TypeError (BoolType × Capabilities)) : Prop :=
  ∀ b c', r₂ = .ok (b, c') → ∃ c, r₁ = .ok (b, c) ∧ CapRel tids pids ren reserved c c'

theorem typeOfIf_bwd {r₁ r₁' : TypedExpr × Capabilities} {r₂ r₂' r₃ r₃' : ResultType}
    (h₁ : r₁'.1.typeOf = r₁.1.typeOf) (hc : CapRel tids pids ren reserved r₁.2 r₁'.2)
    (h₂ : ResRelB tids pids ren reserved r₂ r₂') (h₃ : ResRelB tids pids ren reserved r₃ r₃') :
    ResRelB tids pids ren reserved (typeOfIf r₁ r₂ r₃) (typeOfIf r₁' r₂' r₃') := by
  intro ty c' h
  unfold typeOfIf at h ⊢
  rw [h₁] at h
  split at h
  · cases hr₂ : r₂' with
    | error => rw [hr₂] at h; cases h
    | ok p =>
      obtain ⟨ty₂, c₂⟩ := p
      rw [hr₂] at h
      simp only [Except.bind_ok, ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨tx₂, cx₂, hr₂', hty₂, hc₂⟩ := h₂ _ _ hr₂
      rw [hr₂']
      exact ⟨_, _, rfl, hty₂, hc.union hc₂⟩
  · cases hr₃ : r₃' with
    | error => rw [hr₃] at h; cases h
    | ok p =>
      obtain ⟨ty₃, c₃⟩ := p
      rw [hr₃] at h
      simp only [Except.bind_ok, ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨tx₃, cx₃, hr₃', hty₃, hc₃⟩ := h₃ _ _ hr₃
      rw [hr₃']
      exact ⟨_, _, rfl, hty₃, hc₃⟩
  · cases hr₂ : r₂' with
    | error => rw [hr₂] at h; cases h
    | ok p =>
      obtain ⟨ty₂, c₂⟩ := p
      cases hr₃ : r₃' with
      | error => rw [hr₂, hr₃] at h; cases h
      | ok q =>
        obtain ⟨ty₃, c₃⟩ := q
        rw [hr₂, hr₃] at h
        simp only [Except.bind_ok] at h
        obtain ⟨tx₂, cx₂, hr₂', hty₂, hc₂⟩ := h₂ _ _ hr₂
        obtain ⟨tx₃, cx₃, hr₃', hty₃, hc₃⟩ := h₃ _ _ hr₃
        rw [hr₂', hr₃']
        simp only [Except.bind_ok, hty₂, hty₃]
        split at h
        · simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h ⊢
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨_, _, ⟨rfl, rfl⟩, rfl, (hc.union hc₂).inter hc₃⟩
        · cases h
  · cases h

theorem typeOfAnd_bwd {r₁ r₁' : TypedExpr × Capabilities} {r₂ r₂' : ResultType}
    (h₁ : r₁'.1.typeOf = r₁.1.typeOf) (hc : CapRel tids pids ren reserved r₁.2 r₁'.2)
    (h₂ : ResRelB tids pids ren reserved r₂ r₂') :
    ResRelB tids pids ren reserved (typeOfAnd r₁ r₂) (typeOfAnd r₁' r₂') := by
  intro ty c' h
  unfold typeOfAnd at h ⊢
  rw [h₁] at h
  split at h
  · simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h ⊢
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨_, _, ⟨rfl, rfl⟩, h₁.symm, CapRel.nil⟩
  · cases hr₂ : r₂' with
    | error => rw [hr₂] at h; cases h
    | ok p =>
      obtain ⟨ty₂, c₂⟩ := p
      rw [hr₂] at h
      simp only [Except.bind_ok] at h
      obtain ⟨tx₂, cx₂, hr₂', hty₂, hc₂⟩ := h₂ _ _ hr₂
      rw [hr₂']
      simp only [Except.bind_ok, hty₂]
      split at h <;> (try simp only [ok, err, Except.ok.injEq, Prod.mk.injEq] at h ⊢) <;>
        (try obtain ⟨rfl, rfl⟩ := h) <;>
        first
        | exact ⟨_, _, ⟨rfl, rfl⟩, rfl, CapRel.nil⟩
        | exact ⟨_, _, ⟨rfl, rfl⟩, rfl, hc.union hc₂⟩
  · cases h

theorem typeOfOr_bwd {r₁ r₁' : TypedExpr × Capabilities} {r₂ r₂' : ResultType}
    (h₁ : r₁'.1.typeOf = r₁.1.typeOf) (hc : CapRel tids pids ren reserved r₁.2 r₁'.2)
    (h₂ : ResRelB tids pids ren reserved r₂ r₂') :
    ResRelB tids pids ren reserved (typeOfOr r₁ r₂) (typeOfOr r₁' r₂') := by
  intro ty c' h
  unfold typeOfOr at h ⊢
  rw [h₁] at h
  split at h
  · simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h ⊢
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨_, _, ⟨rfl, rfl⟩, h₁.symm, CapRel.nil⟩
  · cases hr₂ : r₂' with
    | error => rw [hr₂] at h; cases h
    | ok p =>
      obtain ⟨ty₂, c₂⟩ := p
      rw [hr₂] at h
      simp only [Except.bind_ok] at h
      obtain ⟨tx₂, cx₂, hr₂', hty₂, hc₂⟩ := h₂ _ _ hr₂
      rw [hr₂']
      simp only [Except.bind_ok, hty₂]
      split at h
      · simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h ⊢
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨_, _, ⟨rfl, rfl⟩, rfl, hc₂⟩
      · cases h
  · cases hr₂ : r₂' with
    | error => rw [hr₂] at h; cases h
    | ok p =>
      obtain ⟨ty₂, c₂⟩ := p
      rw [hr₂] at h
      simp only [Except.bind_ok] at h
      obtain ⟨tx₂, cx₂, hr₂', hty₂, hc₂⟩ := h₂ _ _ hr₂
      rw [hr₂']
      simp only [Except.bind_ok, hty₂]
      split at h <;> (try simp only [ok, err, Except.ok.injEq, Prod.mk.injEq] at h ⊢) <;>
        (try obtain ⟨rfl, rfl⟩ := h) <;>
        first
        | exact ⟨_, _, ⟨rfl, rfl⟩, rfl, CapRel.nil⟩
        | exact ⟨_, _, ⟨rfl, rfl⟩, rfl, hc⟩
        | exact ⟨_, _, ⟨rfl, rfl⟩, rfl, hc.inter hc₂⟩
  · cases h

theorem typeOfUnaryApp_bwd {op : Cedar.Spec.UnaryOp} {ty ty' : TypedExpr}
    (h : ty'.typeOf = ty.typeOf) :
    ResRelB tids pids ren reserved (typeOfUnaryApp op ty) (typeOfUnaryApp op ty') := by
  intro tx c hr
  unfold typeOfUnaryApp at hr ⊢
  rw [h] at hr
  split at hr <;> (try simp only [ok, Function.comp, Except.ok.injEq, Prod.mk.injEq, err] at hr ⊢) <;>
    (try obtain ⟨rfl, rfl⟩ := hr) <;>
    exact ⟨_, _, ⟨rfl, rfl⟩, rfl, CapRel.nil⟩


/-! ## The typechecker's steps, backwards -/

section Steps

variable (hren : ∀ b₁ i₁ b₂ i₂, i₁ ∈ (if b₁ then tids else pids) → i₂ ∈ (if b₂ then tids else pids) →
      ren b₁ i₁ = ren b₂ i₂ → b₁ = b₂ ∧ i₁ = i₂)
    (hres : ∀ b i, reserved (ren b i) = true)
    {f : ActionSchemaEntry → ActionSchemaEntry} {env₁ env₂ : TypeEnv}
    (henv : EnvRel tids pids ren reserved f env₁ env₂)

omit hren hres in
theorem typeOfEq_bwd {ty₁ ty₂ ty₁' ty₂' : TypedExpr} {x₁ x₂ : Expr}
    (h₁ : ty₁'.typeOf = ty₁.typeOf) (h₂ : ty₂'.typeOf = ty₂.typeOf) :
    ResRelB tids pids ren reserved (typeOfEq ty₁ ty₂ x₁ x₂)
      (typeOfEq ty₁' ty₂' (renameHoisted tids pids ren x₁) (renameHoisted tids pids ren x₂)) := by
  intro ty c h
  by_cases hl : ∃ p₁ p₂, x₁ = .lit p₁ ∧ x₂ = .lit p₂
  · obtain ⟨p₁, p₂, rfl, rfl⟩ := hl
    simp only [renameHoisted_lit] at h
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
    · exact (hl' ⟨_, _, by assumption, by assumption⟩).elim
    · split
      · exact (hl ⟨_, _, rfl, rfl⟩).elim
      · rw [h₁, h₂] at h
        split at h <;> (try simp only [ok, Function.comp, err, Except.ok.injEq, Prod.mk.injEq] at h) <;>
          (try obtain ⟨rfl, rfl⟩ := h)
        · simp only [ok, Function.comp]
          exact ⟨_, _, rfl, rfl, CapRel.nil⟩
        · split at h <;> (try simp only [Except.ok.injEq, Prod.mk.injEq] at h)
          · obtain ⟨rfl, rfl⟩ := h
            simp only [ok, Function.comp]
            exact ⟨_, _, rfl, rfl, CapRel.nil⟩
          · cases h

include hren hres henv

theorem typeOfHasTag_bwd {ety : Cedar.Spec.EntityType} {x t : Expr} {c c' : Capabilities}
    (hx : noReserved tids pids reserved x = true) (ht : noReserved tids pids reserved t = true)
    (hc : CapRel tids pids ren reserved c c') :
    TyRelB tids pids ren reserved (typeOfHasTag ety x t c env₁)
      (typeOfHasTag ety (renameHoisted tids pids ren x) (renameHoisted tids pids ren t) c' env₂) := by
  intro ty c₀ h
  unfold typeOfHasTag at h ⊢
  rw [henv.ets, henv.actionType?] at h
  have hmem := hc x (.tag t) hx ht
  simp only [renameKey] at hmem
  split at h
  · simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h ⊢
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨_, ⟨rfl, rfl⟩, CapRel.nil⟩
  · by_cases hin : (x, Key.tag t) ∈ c
    · rw [if_pos (hmem.mp hin)] at h
      rw [if_pos hin]
      simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h ⊢
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨_, ⟨rfl, rfl⟩, CapRel.nil⟩
    · rw [if_neg (fun h' => hin (hmem.mpr h'))] at h
      rw [if_neg hin]
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
theorem typeOfGetTag_bwd {ety : Cedar.Spec.EntityType} {x t : Expr} {c c' : Capabilities}
    (hx : noReserved tids pids reserved x = true) (ht : noReserved tids pids reserved t = true)
    (hc : CapRel tids pids ren reserved c c') :
    TyRelB tids pids ren reserved (typeOfGetTag ety x t c env₁)
      (typeOfGetTag ety (renameHoisted tids pids ren x) (renameHoisted tids pids ren t) c' env₂) := by
  intro ty c₀ h
  unfold typeOfGetTag at h ⊢
  rw [henv.ets] at h
  have hmem := hc x (.tag t) hx ht
  simp only [renameKey] at hmem
  split at h
  · cases h
  · split at h
    · rename_i hin
      rw [if_pos (hmem.mpr hin)]
      simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h ⊢
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨_, ⟨rfl, rfl⟩, CapRel.nil⟩
    · cases h
  · cases h

theorem typeOfBinaryApp_bwd {op : Cedar.Spec.BinaryOp} {ty₁ ty₂ ty₁' ty₂' : TypedExpr}
    {x₁ x₂ : Expr} {c c' : Capabilities}
    (h₁ : ty₁'.typeOf = ty₁.typeOf) (h₂ : ty₂'.typeOf = ty₂.typeOf)
    (hx₁ : noReserved tids pids reserved x₁ = true) (hx₂ : noReserved tids pids reserved x₂ = true)
    (hc : CapRel tids pids ren reserved c c') :
    ResRelB tids pids ren reserved (typeOfBinaryApp op ty₁ ty₂ x₁ x₂ c env₁)
      (typeOfBinaryApp op ty₁' ty₂' (renameHoisted tids pids ren x₁)
        (renameHoisted tids pids ren x₂) c' env₂) := by
  intro ty c₀ h
  unfold typeOfBinaryApp at h ⊢
  rw [h₁, h₂] at h
  have heq := typeOfEq_bwd (tids := tids) (pids := pids) (ren := ren) (reserved := reserved)
    (x₁ := x₁) (x₂ := x₂) h₁ h₂
  generalize ty₁.typeOf = T₁ at h ⊢
  generalize ty₂.typeOf = T₂ at h ⊢
  split at h
  all_goals first
    | (cases h; done)
    | exact heq ty c₀ h
    | skip
  all_goals (try simp only [henv.typeOfInₑ, henv.typeOfInₛ] at h)
  all_goals first
    | (simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h
       obtain ⟨rfl, rfl⟩ := h
       exact ⟨_, _, rfl, rfl, CapRel.nil⟩)
    | (cases ht : typeOfHasTag _ (renameHoisted tids pids ren x₁) (renameHoisted tids pids ren x₂) c'
          env₂ with
       | error => rw [ht] at h; cases h
       | ok p =>
         obtain ⟨t, cc'⟩ := p
         rw [ht] at h
         simp only [Except.bind_ok, ok, Except.ok.injEq, Prod.mk.injEq] at h
         obtain ⟨rfl, rfl⟩ := h
         obtain ⟨cc, ht', hcc⟩ := typeOfHasTag_bwd hren hres henv hx₁ hx₂ hc t cc' ht
         rw [ht']
         exact ⟨_, _, rfl, rfl, hcc⟩)
    | (cases ht : typeOfGetTag _ (renameHoisted tids pids ren x₁) (renameHoisted tids pids ren x₂) c'
          env₂ with
       | error => rw [ht] at h; cases h
       | ok p =>
         obtain ⟨t, cc'⟩ := p
         rw [ht] at h
         simp only [Except.bind_ok, ok, Except.ok.injEq, Prod.mk.injEq] at h
         obtain ⟨rfl, rfl⟩ := h
         obtain ⟨cc, ht', hcc⟩ := typeOfGetTag_bwd henv hx₁ hx₂ hc t cc' ht
         rw [ht']
         exact ⟨_, _, rfl, rfl, hcc⟩)
    | (cases ht : ifLubThenBool _ _ with
       | error => rw [ht] at h; cases h
       | ok p =>
         obtain ⟨t, cc⟩ := p
         rw [ht] at h
         simp only [Except.bind_ok, ok, Except.ok.injEq, Prod.mk.injEq] at h
         obtain ⟨rfl, rfl⟩ := h
         have : cc = [] := by
           unfold ifLubThenBool at ht
           split at ht
           · simp only [ok, Except.ok.injEq, Prod.mk.injEq] at ht; exact ht.2.symm
           · cases ht
         subst this
         exact ⟨_, _, rfl, rfl, CapRel.nil⟩)

omit henv in
theorem hasAttrInRecord_bwd {rty : RecordType} {x : Expr} {a : Attr} {c c' : Capabilities}
    {known : Bool} (hx : noReserved tids pids reserved x = true)
    (hc : CapRel tids pids ren reserved c c') :
    TyRelB tids pids ren reserved (hasAttrInRecord rty x a c known)
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
    rw [hdec] at h
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
theorem getAttrInRecord_bwd {ty ty' : CedarType} {rty : RecordType} {x : Expr} {a : Attr}
    {c c' : Capabilities} (hx : noReserved tids pids reserved x = true)
    (hc : CapRel tids pids ren reserved c c') :
    TyRelB tids pids ren reserved (getAttrInRecord ty rty x a c)
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
      rw [if_pos (hmem.mpr hin)]
      simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h ⊢
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨_, ⟨rfl, rfl⟩, CapRel.nil⟩
    · cases h
  · cases h

theorem typeOfHasAttr_bwd {ty ty' : TypedExpr} {x : Expr} {a : Attr} {c c' : Capabilities}
    (hty : ty'.typeOf = ty.typeOf) (hx : noReserved tids pids reserved x = true)
    (hc : CapRel tids pids ren reserved c c') :
    ResRelB tids pids ren reserved (typeOfHasAttr ty x a c env₁)
      (typeOfHasAttr ty' (renameHoisted tids pids ren x) a c' env₂) := by
  intro tx c₀ h
  unfold typeOfHasAttr at h ⊢
  rw [hty, henv.ets] at h
  simp only [henv.actionType?] at h
  split at h
  · cases hr : hasAttrInRecord _ (renameHoisted tids pids ren x) a c' true with
    | error => rw [hr] at h; cases h
    | ok p =>
      obtain ⟨t, cc'⟩ := p
      rw [hr] at h
      simp only [Except.bind_ok, ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨cc, hr', hcc⟩ := hasAttrInRecord_bwd hren hres hx hc t cc' hr
      rw [hr']
      exact ⟨_, _, rfl, rfl, hcc⟩
  · split at h
    · cases hr : hasAttrInRecord _ (renameHoisted tids pids ren x) a c' false with
      | error => rw [hr] at h; cases h
      | ok p =>
        obtain ⟨t, cc'⟩ := p
        rw [hr] at h
        simp only [Except.bind_ok, ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨cc, hr', hcc⟩ := hasAttrInRecord_bwd hren hres hx hc t cc' hr
        simp only [hr', Except.bind_ok]
        exact ⟨_, _, rfl, rfl, hcc⟩
    · split at h
      · rename_i hact
        rw [if_pos hact]
        simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨_, _, rfl, rfl, CapRel.nil⟩
      · cases h
  · cases h

omit hren hres in
theorem typeOfGetAttr_bwd {ty ty' : TypedExpr} {x : Expr} {a : Attr} {c c' : Capabilities}
    (hty : ty'.typeOf = ty.typeOf) (hx : noReserved tids pids reserved x = true)
    (hc : CapRel tids pids ren reserved c c') :
    ResRelB tids pids ren reserved (typeOfGetAttr ty x a c env₁)
      (typeOfGetAttr ty' (renameHoisted tids pids ren x) a c' env₂) := by
  intro tx c₀ h
  unfold typeOfGetAttr at h ⊢
  rw [hty, henv.ets] at h
  split at h
  · cases hr : getAttrInRecord _ _ (renameHoisted tids pids ren x) a c' with
    | error => rw [hr] at h; cases h
    | ok p =>
      obtain ⟨t, cc'⟩ := p
      rw [hr] at h
      simp only [Except.bind_ok, ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨cc, hr', hcc⟩ := getAttrInRecord_bwd (ty := ty.typeOf) hx hc t cc' hr
      rw [hr']
      exact ⟨_, _, rfl, rfl, hcc⟩
  · split at h
    · cases hr : getAttrInRecord _ _ (renameHoisted tids pids ren x) a c' with
      | error => rw [hr] at h; cases h
      | ok p =>
        obtain ⟨t, cc'⟩ := p
        rw [hr] at h
        simp only [Except.bind_ok, ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨cc, hr', hcc⟩ := getAttrInRecord_bwd (ty := ty.typeOf) hx hc t cc' hr
        simp only [hr', Except.bind_ok]
        exact ⟨_, _, rfl, rfl, hcc⟩
    · cases h
  · cases h

omit hren hres henv in
/-- `x has a.as` (Cedar 4.14's extended `has`), backwards, given that `x has a` and `x.a` type
alike backwards under related capabilities, and that the rest of the path does from operands of
the same type. -/
theorem typeOfExtHasAttr_bwd_of {ty ty' : TypedExpr} {x x' : Expr} {a : Attr} {as : List Attr}
    (hhas : ∀ c c', CapRel tids pids ren reserved c c' →
      ResRelB tids pids ren reserved (typeOfHasAttr ty x a c env₁) (typeOfHasAttr ty' x' a c' env₂))
    (hget : ∀ c c', CapRel tids pids ren reserved c c' →
      ResRelB tids pids ren reserved (typeOfGetAttr ty x a c env₁) (typeOfGetAttr ty' x' a c' env₂))
    (hrest : ∀ (u u' : TypedExpr) c c', u'.typeOf = u.typeOf → CapRel tids pids ren reserved c c' →
      BoolRelB tids pids ren reserved (typeOfExtHasAttr u (.getAttr x a) as c env₁)
        (typeOfExtHasAttr u' (.getAttr x' a) as c' env₂))
    {c c' : Capabilities} (hc : CapRel tids pids ren reserved c c') :
    BoolRelB tids pids ren reserved (typeOfExtHasAttr ty x (a :: as) c env₁)
      (typeOfExtHasAttr ty' x' (a :: as) c' env₂) := by
  intro b c₀ h
  cases as with
  | nil =>
    simp only [typeOfExtHasAttr] at h ⊢
    cases h₁ : typeOfHasAttr ty' x' a c' env₂ with
    | error => rw [h₁] at h; cases h
    | ok p =>
      obtain ⟨u', cu'⟩ := p
      rw [h₁] at h
      simp only [Except.bind_ok] at h
      obtain ⟨u, cu, h₁', hu, hcu⟩ := hhas c c' hc u' cu' h₁
      rw [h₁']
      simp only [Except.bind_ok]
      rw [hu]
      split at h <;> simp only [Except.ok.injEq, Prod.mk.injEq] at h <;> obtain ⟨rfl, rfl⟩ := h <;>
        exact ⟨_, rfl, hcu⟩
  | cons a₂ as =>
    simp only [typeOfExtHasAttr] at h ⊢
    cases h₁ : typeOfHasAttr ty' x' a c' env₂ with
    | error => rw [h₁] at h; cases h
    | ok p =>
      obtain ⟨u', cu'⟩ := p
      rw [h₁] at h
      simp only [Except.bind_ok] at h
      obtain ⟨u, cu, h₁', hu, hcu⟩ := hhas c c' hc u' cu' h₁
      rw [h₁']
      simp only [Except.bind_ok]
      rw [hu]
      split at h
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h ⊢
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨_, ⟨rfl, rfl⟩, hcu⟩
      · · cases h₂ : typeOfGetAttr ty' x' a (c' ∪ cu') env₂ with
          | error => rw [h₂] at h; cases h
          | ok q =>
            obtain ⟨v', cv'⟩ := q
            rw [h₂] at h
            simp only [Except.bind_ok] at h
            obtain ⟨v, cv, h₂', hv, -⟩ := hget _ _ (hc.union hcu) v' cv' h₂
            rw [h₂']
            simp only [Except.bind_ok]
            cases h₃ : typeOfExtHasAttr v' (.getAttr x' a) (a₂ :: as) (c' ∪ cu') env₂ with
            | error => rw [h₃] at h; cases h
            | ok r =>
              obtain ⟨bty, cr'⟩ := r
              rw [h₃] at h
              simp only [Except.bind_ok] at h
              obtain ⟨cr, h₃', hcr⟩ := hrest v v' _ _ hv.symm (hc.union hcu) bty cr' h₃
              rw [h₃']
              simp only [Except.bind_ok]
              cases bty with
              | anyBool =>
                simp only [Except.ok.injEq, Prod.mk.injEq] at h ⊢
                obtain ⟨rfl, rfl⟩ := h
                exact ⟨_, ⟨rfl, rfl⟩, hcu.union hcr⟩
              | tt =>
                simp only at h ⊢
                split at h <;> simp only [Except.ok.injEq, Prod.mk.injEq] at h <;>
                  obtain ⟨rfl, rfl⟩ := h <;> exact ⟨_, rfl, hcu.union hcr⟩
              | ff =>
                simp only [Except.ok.injEq, Prod.mk.injEq] at h ⊢
                obtain ⟨rfl, rfl⟩ := h
                exact ⟨_, ⟨rfl, rfl⟩, fun _ _ _ _ => by simp [EmptyCollection.emptyCollection]⟩

omit hren hres henv in
/-- The renaming keeps the attribute access `x.a` of an operand that is neither `context` nor
`context.providers`. -/
theorem renameHoisted_getAttr_plain {x : Expr} {a : Attr} (hcx : isContextC x = false)
    (hpx : isContextProvidersC x = false) :
    renameHoisted tids pids ren (.getAttr x a) = .getAttr (renameHoisted tids pids ren x) a := by
  rw [renameHoisted_getAttr]
  simp [renBase, renAttr, hcx, hpx]

omit hren hres henv in
theorem isContextProvidersC_getAttr {x : Expr} {a : Attr} (hcx : isContextC x = false) :
    isContextProvidersC (.getAttr x a) = false := by
  cases x with
  | var v => cases v <;> simp_all [isContextC, isContextProvidersC]
  | _ => simp [isContextProvidersC]

/-- `x has as` (Cedar 4.14's extended `has`), backwards, for an operand `x` that is neither
`context` nor `context.providers`: no prefix of the path is then a hoisted read, and the renaming
keeps the path. -/
theorem typeOfExtHasAttr_bwd : ∀ (as : List Attr) (x : Expr),
    noReserved tids pids reserved x = true → isContextC x = false →
    isContextProvidersC x = false →
    ∀ {ty ty' : TypedExpr} {c c' : Capabilities}, ty'.typeOf = ty.typeOf →
      CapRel tids pids ren reserved c c' →
      BoolRelB tids pids ren reserved (typeOfExtHasAttr ty x as c env₁)
        (typeOfExtHasAttr ty' (renameHoisted tids pids ren x) as c' env₂)
  | [], _, _, _, _, _, _, _, _, _, _ => by
    intro b c₀ h
    simp only [typeOfExtHasAttr, Except.ok.injEq, Prod.mk.injEq] at h ⊢
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨_, ⟨rfl, rfl⟩, fun _ _ _ _ => by simp [EmptyCollection.emptyCollection]⟩
  | a :: as, x, hx, hcx, hpx, ty, ty', c, c', hty, hc => by
    have hnr : noReserved tids pids reserved (.getAttr x a) = true := by
      simp [noReserved, hcx, hpx, hx]
    have hcg : isContextC (.getAttr x a) = false := rfl
    exact typeOfExtHasAttr_bwd_of
      (fun _ _ hc => typeOfHasAttr_bwd hren hres henv hty hx hc)
      (fun _ _ hc => typeOfGetAttr_bwd henv hty hx hc)
      (fun u u' _ _ hu hc => by
        have := typeOfExtHasAttr_bwd as (.getAttr x a) hnr hcg (isContextProvidersC_getAttr hcx)
          hu hc
        rwa [renameHoisted_getAttr_plain hcx hpx] at this) hc

/-- `context has a`, backwards, for an attribute outside lowering's names. -/
theorem typeOfHasAttr_context_bwd {a : Attr} (hnt : tids.contains a = false)
    (hnp : ¬a = "providers") (hnr : reserved a = false) {c c' : Capabilities}
    (hc : CapRel tids pids ren reserved c c') :
    ResRelB tids pids ren reserved
      (typeOfHasAttr (.var .context (.record env₁.reqty.context)) (.var .context) a c env₁)
      (typeOfHasAttr (.var .context (.record env₂.reqty.context)) (.var .context) a c' env₂) := by
  intro ty c₀ h
  unfold typeOfHasAttr at h ⊢
  simp only [TypedExpr.typeOf] at h ⊢
  have hfind := henv.context.other a (by simpa using hnt) hnp hnr
  rw [hasAttrInRecord_congr hfind] at h
  cases hr : hasAttrInRecord env₁.reqty.context (.var .context) a c' true with
  | error => rw [hr] at h; cases h
  | ok p =>
    obtain ⟨t, cc'⟩ := p
    rw [hr] at h
    simp only [Except.bind_ok, ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨cc, hr', hcc⟩ := hasAttrInRecord_bwd hren hres (x := .var .context) rfl hc t cc'
      (by rw [renameHoisted_var]; exact hr)
    rw [hr']
    exact ⟨_, _, rfl, rfl, hcc⟩

omit hren hres in
/-- `context.a`, backwards, for an attribute outside lowering's names. -/
theorem typeOfGetAttr_context_bwd {a : Attr} (hnt : tids.contains a = false)
    (hnp : ¬a = "providers") (hnr : reserved a = false) {c c' : Capabilities}
    (hc : CapRel tids pids ren reserved c c') :
    ResRelB tids pids ren reserved
      (typeOfGetAttr (.var .context (.record env₁.reqty.context)) (.var .context) a c env₁)
      (typeOfGetAttr (.var .context (.record env₂.reqty.context)) (.var .context) a c' env₂) := by
  intro ty c₀ h
  unfold typeOfGetAttr at h ⊢
  simp only [TypedExpr.typeOf] at h ⊢
  have hfind := henv.context.other a (by simpa using hnt) hnp hnr
  cases hr : getAttrInRecord (.record env₂.reqty.context) env₂.reqty.context (.var .context) a c'
    with
  | error => rw [hr] at h; cases h
  | ok p =>
    obtain ⟨t, cc'⟩ := p
    rw [hr] at h
    simp only [Except.bind_ok, ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hr₁ := getAttrInRecord_congr (ty' := .record env₂.reqty.context) hfind.symm hr
    obtain ⟨cc, hr', hcc⟩ := getAttrInRecord_bwd (ty := .record env₁.reqty.context)
      (x := .var .context) rfl hc t cc' (by rw [renameHoisted_var]; exact hr₁)
    rw [hr']
    exact ⟨_, _, rfl, rfl, hcc⟩

omit hren hres henv in
theorem typeOfSet_bwd {tys tys' : List TypedExpr}
    (h : tys.map TypedExpr.typeOf = tys'.map TypedExpr.typeOf) :
    ResRelB tids pids ren reserved (typeOfSet tys) (typeOfSet tys') := by
  intro tx c₀ hr
  cases tys' with
  | nil => simp [typeOfSet, err] at hr
  | cons hd' tl' =>
    cases tys with
    | nil => simp at h
    | cons hd tl =>
      simp only [List.map_cons, List.cons.injEq] at h
      simp only [typeOfSet] at hr ⊢
      rw [h.1, h.2]
      split at hr
      · simp only [ok, Except.ok.injEq, Prod.mk.injEq] at hr
        obtain ⟨rfl, rfl⟩ := hr
        exact ⟨_, _, rfl, rfl, CapRel.nil⟩
      · cases hr

omit hren hres henv in
theorem typeOfConstructor_unrename {α : Type} {mk : String → Option α} {xs : List Expr}
    {ty : CedarType} {p : CedarType × Capabilities}
    (h : typeOfConstructor mk (renameHoistedList tids pids ren xs) ty = .ok p) :
    typeOfConstructor mk xs ty = .ok p := by
  rw [renameHoistedList_eq] at h
  rcases xs with _ | ⟨x, _ | ⟨y, ys⟩⟩
  · exact h
  · cases x with
    | lit q => simpa only [List.map_cons, List.map_nil, renameHoisted_lit] using h
    | getAttr e a =>
      simp only [List.map_cons, List.map_nil, renameHoisted_getAttr] at h
      simp [typeOfConstructor, err] at h
    | _ => simp [renameHoisted, typeOfConstructor, err] at h
  · simp [typeOfConstructor, err] at h

omit hren hres henv in
theorem typeOfCall_bwd {xfn : Cedar.Spec.ExtFun} {tys tys' : List TypedExpr} {xs : List Expr}
    (h : tys.map TypedExpr.typeOf = tys'.map TypedExpr.typeOf) :
    ResRelB tids pids ren reserved (typeOfCall xfn tys xs)
      (typeOfCall xfn tys' (renameHoistedList tids pids ren xs)) := by
  intro tx c₀ hr
  unfold typeOfCall at hr ⊢
  rw [h]
  split at hr
  all_goals first
    | (cases hr <;> exact ⟨_, _, rfl, rfl, CapRel.nil⟩)
    | (cases ht : typeOfConstructor _ (renameHoistedList tids pids ren xs) _ with
       | error => rw [ht] at hr; cases hr
       | ok p =>
         obtain ⟨t, cc⟩ := p
         rw [ht] at hr
         simp only [Except.bind_ok, ok, Except.ok.injEq, Prod.mk.injEq] at hr
         obtain ⟨rfl, rfl⟩ := hr
         rw [typeOfConstructor_unrename ht]
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

end Steps


/-! ## The simulation, backwards -/

section Simulation

variable (hren : ∀ b₁ i₁ b₂ i₂, i₁ ∈ (if b₁ then tids else pids) → i₂ ∈ (if b₂ then tids else pids) →
      ren b₁ i₁ = ren b₂ i₂ → b₁ = b₂ ∧ i₁ = i₂)
    (hres : ∀ b i, reserved (ren b i) = true)
    {f : ActionSchemaEntry → ActionSchemaEntry} {env₁ env₂ : TypeEnv}
    (henv : EnvRel tids pids ren reserved f env₁ env₂)
    -- No temporal leaf is named `providers`, the record the provider leaves' fields are read off
    -- (lowering names a temporal leaf `<rule>__temporal_<n>`; `tidsNotProviders`). Since Cedar 4.14
    -- keeps `x has a.b` as one node, without the access `x.a` that the renaming would rename, a
    -- leaf named `providers` would be read differently by `context.providers has p.b` and
    -- `context.providers.p has b`.
    (htp : tids.contains "providers" = false)

include hren hres henv htp

mutual

/-- **The simulation of the typechecker, backwards.** On related request environments, with
related capabilities, a successful typing of the renaming of an expression the crate's
context-read check accepts gives a successful typing of the expression, of the same type, with
related capabilities, when the crate's context declares the expression's hoisted reads. -/
theorem typeOf_unrename : (x : Expr) → renameOk tids pids reserved x = true →
    graftOk tids pids env₁.reqty.context x = true →
    ∀ {c c' : Capabilities}, CapRel tids pids ren reserved c c' →
    ResRelB tids pids ren reserved (typeOf x c env₁) (typeOf (renameHoisted tids pids ren x) c' env₂)
  | .lit p, _, _, c, c', _ => by
    intro ty c₀ h
    simp only [renameHoisted_lit, typeOf] at h ⊢
    rw [henv.typeOfLit] at h
    exact ⟨ty, c₀, h, rfl, by rw [caps_of_typeOfLit h]; exact CapRel.nil⟩
  | .var v, hx, _, c, c', _ => by
    intro ty c₀ h
    simp only [renameOk, bne_iff_ne, ne_eq] at hx
    simp only [renameHoisted_var, typeOf] at h ⊢
    rw [henv.typeOfVar hx] at h
    exact ⟨ty, c₀, h, rfl, by rw [caps_of_typeOfVar h]; exact CapRel.nil⟩
  | .ite x₁ x₂ x₃, hx, hg, c, c', hc => by
    simp only [renameOk, Bool.and_eq_true] at hx
    simp only [graftOk, Bool.and_eq_true] at hg
    intro ty c₀ h
    simp only [renameHoisted, typeOf] at h ⊢
    cases h₁ : typeOf (renameHoisted tids pids ren x₁) c' env₂ with
    | error => rw [h₁] at h; cases h
    | ok p =>
      obtain ⟨ty₁, c₁⟩ := p
      rw [h₁] at h
      simp only [Except.bind_ok] at h
      obtain ⟨tx₁, cx₁, h₁', hty₁, hc₁⟩ := typeOf_unrename x₁ hx.1.1 hg.1.1 hc ty₁ c₁ h₁
      rw [h₁']
      simp only [Except.bind_ok]
      exact typeOfIf_bwd hty₁.symm hc₁ (typeOf_unrename x₂ hx.1.2 hg.1.2 (hc.union hc₁))
        (typeOf_unrename x₃ hx.2 hg.2 hc) ty c₀ h
  | .and x₁ x₂, hx, hg, c, c', hc => by
    simp only [renameOk, Bool.and_eq_true] at hx
    simp only [graftOk, Bool.and_eq_true] at hg
    intro ty c₀ h
    simp only [renameHoisted, typeOf] at h ⊢
    cases h₁ : typeOf (renameHoisted tids pids ren x₁) c' env₂ with
    | error => rw [h₁] at h; cases h
    | ok p =>
      obtain ⟨ty₁, c₁⟩ := p
      rw [h₁] at h
      simp only [Except.bind_ok] at h
      obtain ⟨tx₁, cx₁, h₁', hty₁, hc₁⟩ := typeOf_unrename x₁ hx.1 hg.1 hc ty₁ c₁ h₁
      rw [h₁']
      simp only [Except.bind_ok]
      exact typeOfAnd_bwd hty₁.symm hc₁ (typeOf_unrename x₂ hx.2 hg.2 (hc.union hc₁)) ty c₀ h
  | .or x₁ x₂, hx, hg, c, c', hc => by
    simp only [renameOk, Bool.and_eq_true] at hx
    simp only [graftOk, Bool.and_eq_true] at hg
    intro ty c₀ h
    simp only [renameHoisted, typeOf] at h ⊢
    cases h₁ : typeOf (renameHoisted tids pids ren x₁) c' env₂ with
    | error => rw [h₁] at h; cases h
    | ok p =>
      obtain ⟨ty₁, c₁⟩ := p
      rw [h₁] at h
      simp only [Except.bind_ok] at h
      obtain ⟨tx₁, cx₁, h₁', hty₁, hc₁⟩ := typeOf_unrename x₁ hx.1 hg.1 hc ty₁ c₁ h₁
      rw [h₁']
      simp only [Except.bind_ok]
      exact typeOfOr_bwd hty₁.symm hc₁ (typeOf_unrename x₂ hx.2 hg.2 hc) ty c₀ h
  | .unaryApp op x₁, hx, hg, c, c', hc => by
    simp only [renameOk] at hx
    simp only [graftOk] at hg
    intro ty c₀ h
    simp only [renameHoisted, typeOf] at h ⊢
    cases h₁ : typeOf (renameHoisted tids pids ren x₁) c' env₂ with
    | error => rw [h₁] at h; cases h
    | ok p =>
      obtain ⟨ty₁, c₁⟩ := p
      rw [h₁] at h
      simp only [Except.bind_ok] at h
      obtain ⟨tx₁, cx₁, h₁', hty₁, _⟩ := typeOf_unrename x₁ hx hg hc ty₁ c₁ h₁
      rw [h₁']
      simp only [Except.bind_ok]
      exact typeOfUnaryApp_bwd hty₁.symm ty c₀ h
  | .binaryApp op x₁ x₂, hx, hg, c, c', hc => by
    simp only [renameOk, Bool.and_eq_true] at hx
    simp only [graftOk, Bool.and_eq_true] at hg
    intro ty c₀ h
    simp only [renameHoisted, typeOf] at h ⊢
    cases h₁ : typeOf (renameHoisted tids pids ren x₁) c' env₂ with
    | error => rw [h₁] at h; cases h
    | ok p =>
      obtain ⟨ty₁, c₁⟩ := p
      cases h₂ : typeOf (renameHoisted tids pids ren x₂) c' env₂ with
      | error => rw [h₁, h₂] at h; cases h
      | ok q =>
        obtain ⟨ty₂, c₂⟩ := q
        rw [h₁, h₂] at h
        simp only [Except.bind_ok] at h
        obtain ⟨tx₁, cx₁, h₁', hty₁, _⟩ := typeOf_unrename x₁ hx.1 hg.1 hc ty₁ c₁ h₁
        obtain ⟨tx₂, cx₂, h₂', hty₂, _⟩ := typeOf_unrename x₂ hx.2 hg.2 hc ty₂ c₂ h₂
        rw [h₁', h₂']
        simp only [Except.bind_ok]
        exact typeOfBinaryApp_bwd hren hres henv hty₁.symm hty₂.symm (noReserved_of_renameOk x₁ hx.1)
          (noReserved_of_renameOk x₂ hx.2) hc ty c₀ h
  | .hasAttr x₁ a, hx, hg, c, c', hc => by
    simp only [renameOk] at hx
    simp only [graftOk] at hg
    intro ty c₀ h
    simp only [renameHoisted, typeOf] at h ⊢
    by_cases hctx : isContextC x₁ = true
    · rw [if_pos hctx] at hx
      have := isContextC_eq hctx
      subst this
      simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at hx
      obtain ⟨⟨hnt, hnp⟩, hnr⟩ := hx
      rw [renameHoisted_var, typeOf_context] at h
      rw [typeOf_context]
      simp only [Except.bind_ok] at h ⊢
      unfold typeOfHasAttr at h ⊢
      simp only [TypedExpr.typeOf] at h ⊢
      have hfind := henv.context.other a (by simpa using hnt) hnp hnr
      rw [hasAttrInRecord_congr hfind] at h
      cases hr : hasAttrInRecord env₁.reqty.context (.var .context) a c' true with
      | error => rw [hr] at h; cases h
      | ok p =>
        obtain ⟨t, cc'⟩ := p
        rw [hr] at h
        simp only [Except.bind_ok, ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨cc, hr', hcc⟩ := hasAttrInRecord_bwd hren hres (x := .var .context) rfl hc t cc'
          (by rw [renameHoisted_var]; exact hr)
        rw [hr']
        exact ⟨_, _, rfl, rfl, hcc⟩
    · rw [if_neg hctx] at hx
      cases h₁ : typeOf (renameHoisted tids pids ren x₁) c' env₂ with
      | error => rw [h₁] at h; cases h
      | ok p =>
        obtain ⟨ty₁, c₁⟩ := p
        rw [h₁] at h
        simp only [Except.bind_ok] at h
        obtain ⟨tx₁, cx₁, h₁', hty₁, _⟩ := typeOf_unrename x₁ hx hg hc ty₁ c₁ h₁
        rw [h₁']
        simp only [Except.bind_ok]
        exact typeOfHasAttr_bwd hren hres henv hty₁.symm (noReserved_of_renameOk x₁ hx) hc ty c₀ h
  | .extHasAttr x₁ a as, hx, hg, c, c', hc => by
    simp only [renameOk] at hx
    simp only [graftOk] at hg
    intro ty c₀ h
    simp only [renameHoisted, typeOf] at h ⊢
    by_cases hctx : isContextC x₁ = true
    · rw [if_pos hctx] at hx
      have := isContextC_eq hctx
      subst this
      simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at hx
      obtain ⟨⟨hnt, hnp⟩, hnr⟩ := hx
      rw [renameHoisted_var, typeOf_context] at h
      rw [typeOf_context]
      simp only [Except.bind_ok] at h ⊢
      cases h₁ : typeOfExtHasAttr (.var .context (.record env₂.reqty.context)) (.var .context)
          (a :: as) c' env₂ with
      | error => rw [h₁] at h; cases h
      | ok r =>
        obtain ⟨bty, cr'⟩ := r
        rw [h₁] at h
        simp only [Except.bind_ok, ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hnra : noReserved tids pids reserved (.getAttr (.var .context) a) = true := by
          simp [noReserved, isContextC, isContextProvidersC, hnt, hnr]
        have hpa : isContextProvidersC (.getAttr (.var .context) a) = false := by
          simp [isContextProvidersC, hnp]
        have hga : renameHoisted tids pids ren (.getAttr (.var .context) a) =
            .getAttr (.var .context) a := by
          have hnt' : a ∉ tids := by simpa using hnt
          rw [renameHoisted_getAttr]
          simp [renBase, renAttr, isContextC, isContextProvidersC, hnt', renameHoisted_var]
        obtain ⟨cr, h₁', hcr⟩ := typeOfExtHasAttr_bwd_of
          (fun _ _ hc => typeOfHasAttr_context_bwd hren hres henv hnt hnp hnr hc)
          (fun _ _ hc => typeOfGetAttr_context_bwd henv hnt hnp hnr hc)
          (fun u u' _ _ hu hc => by
            have := typeOfExtHasAttr_bwd hren hres henv as (.getAttr (.var .context) a) hnra rfl
              hpa hu hc
            rwa [hga] at this) hc bty cr' h₁
        rw [h₁']
        simp only [Except.bind_ok, ok]
        exact ⟨_, _, rfl, rfl, hcr⟩
    · rw [if_neg hctx, Bool.and_eq_true] at hx
      obtain ⟨-, hx⟩ := hx
      have hcx : isContextC x₁ = false := by simpa using hctx
      have hpx : isContextProvidersC x₁ = false := by
        cases hp : isContextProvidersC x₁
        · rfl
        · have := isContextProvidersC_eq hp
          subst this
          have htp' : "providers" ∉ tids := by simpa using htp
          simp [renameOk, isContextC] at hx
          exact absurd hx htp'
      cases h₁ : typeOf (renameHoisted tids pids ren x₁) c' env₂ with
      | error => rw [h₁] at h; cases h
      | ok p =>
        obtain ⟨ty₁, c₁⟩ := p
        rw [h₁] at h
        simp only [Except.bind_ok] at h
        obtain ⟨tx₁, cx₁, h₁', hty₁, _⟩ := typeOf_unrename x₁ hx hg hc ty₁ c₁ h₁
        rw [h₁']
        simp only [Except.bind_ok]
        cases h₂ : typeOfExtHasAttr ty₁ (renameHoisted tids pids ren x₁) (a :: as) c' env₂ with
        | error => rw [h₂] at h; cases h
        | ok r =>
          obtain ⟨bty, cr'⟩ := r
          rw [h₂] at h
          simp only [Except.bind_ok, ok, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨cr, h₂', hcr⟩ := typeOfExtHasAttr_bwd hren hres henv (a :: as) x₁
            (noReserved_of_renameOk x₁ hx) hcx hpx hty₁.symm hc bty cr' h₂
          rw [h₂']
          simp only [Except.bind_ok, ok]
          exact ⟨_, _, rfl, rfl, hcr⟩
  | .getAttr x₁ a, hx, hg, c, c', hc => by
    intro ty c₀ h
    rw [renameHoisted_getAttr] at h
    by_cases hA : (isContextC x₁ && tids.contains a) = true
    · -- the attribute of a temporal leaf
      have hA' := hA
      simp only [Bool.and_eq_true, List.contains_iff_mem] at hA'
      have hx₁ := isContextC_eq hA'.1
      simp only [renBase, renAttr, if_pos hA] at h
      simp only [graftOk, if_pos hA] at hg
      subst hx₁
      obtain ⟨t, ht⟩ := declaredRequired_iff.mp hg
      obtain ⟨q, hq, hqt, rfl⟩ := typeOf_getAttr_context h
      have hq' := henv.context.temporal a (by simpa using hA'.2) _ ht
      rw [hq] at hq'
      cases hq'
      rw [typeOf_getAttr_context_required ht]
      exact ⟨_, _, rfl, hqt.symm, CapRel.nil⟩
    · by_cases hB : (isContextProvidersC x₁ && pids.contains a) = true
      · -- the field of a provider leaf
        have hB' := hB
        simp only [Bool.and_eq_true, List.contains_iff_mem] at hB'
        have hx₁ := isContextProvidersC_eq hB'.1
        have ha : a ∈ pids := by simpa using hB'.2
        simp only [renBase, renAttr, if_neg hA, if_pos hB] at h
        simp only [graftOk, if_neg hA, if_pos hB] at hg
        subst hx₁
        obtain ⟨R, t, hR, ht⟩ := declaredProvider_iff.mp hg
        obtain ⟨q, hq, hqt, rfl⟩ := typeOf_getAttr_context h
        have hq' := henv.context.provider a ha _ R _ hR rfl ht
        rw [hq] at hq'
        cases hq'
        rw [typeOf_getAttr_eq, typeOf_getAttr_context_required hR]
        simp only [Except.bind_ok]
        unfold typeOfGetAttr
        simp only [TypedExpr.typeOf]
        rw [getAttrInRecord_required ht]
        exact ⟨_, _, rfl, hqt.symm, CapRel.nil⟩
      · simp only [renBase, renAttr, if_neg hA, if_neg hB] at h
        simp only [graftOk, if_neg hA, if_neg hB] at hg
        simp only [renameOk] at hx
        by_cases hctx : isContextC x₁ = true
        · rw [if_pos hctx] at hx
          have hx₁ := isContextC_eq hctx
          subst hx₁
          have hnt : tids.contains a = false := by simpa [isContextC] using hA
          simp only [hnt, Bool.false_or, Bool.and_eq_true, bne_iff_ne, ne_eq,
            Bool.not_eq_true'] at hx
          rw [renameHoisted_var] at h
          simp only [typeOf] at h ⊢
          rw [typeOfVar_context] at h ⊢
          simp only [Except.bind_ok] at h ⊢
          unfold typeOfGetAttr at h ⊢
          simp only [TypedExpr.typeOf] at h ⊢
          have hfind := henv.context.other a (by simpa using hnt) hx.1 hx.2
          cases hr : getAttrInRecord (.record env₂.reqty.context) env₂.reqty.context (.var .context) a c' with
          | error => rw [hr] at h; cases h
          | ok p =>
            obtain ⟨t, cc'⟩ := p
            rw [hr] at h
            simp only [Except.bind_ok, ok, Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            have hr₁ := getAttrInRecord_congr (ty' := .record env₂.reqty.context) hfind.symm hr
            obtain ⟨cc, hr', hcc⟩ := getAttrInRecord_bwd (ty := .record env₁.reqty.context)
              (x := .var .context) rfl hc t cc' (by rw [renameHoisted_var]; exact hr₁)
            rw [hr']
            exact ⟨_, _, rfl, rfl, hcc⟩
        · rw [if_neg hctx] at hx
          have hB'' : (isContextProvidersC x₁ && pids.contains a) = false := by simpa using hB
          rw [hB''] at hx
          simp only [Bool.false_eq_true, if_false] at hx
          simp only [typeOf] at h ⊢
          cases h₁ : typeOf (renameHoisted tids pids ren x₁) c' env₂ with
          | error => rw [h₁] at h; cases h
          | ok p =>
            obtain ⟨ty₁, c₁⟩ := p
            rw [h₁] at h
            simp only [Except.bind_ok] at h
            obtain ⟨tx₁, cx₁, h₁', hty₁, _⟩ := typeOf_unrename x₁ hx hg hc ty₁ c₁ h₁
            rw [h₁']
            simp only [Except.bind_ok]
            exact typeOfGetAttr_bwd henv hty₁.symm (noReserved_of_renameOk x₁ hx) hc ty c₀ h
  | .set xs, hx, hg, c, c', hc => by
    simp only [renameOk] at hx
    simp only [graftOk] at hg
    intro ty c₀ h
    simp only [renameHoisted, typeOf] at h ⊢
    rw [List.mapM₁_eq_mapM (fun x => justType (typeOf x c env₁))]
    rw [List.mapM₁_eq_mapM (fun x => justType (typeOf x c' env₂)), renameHoistedList_eq] at h
    cases hs : (xs.map (renameHoisted tids pids ren)).mapM (fun x => justType (typeOf x c' env₂)) with
    | error => rw [hs] at h; cases h
    | ok tys' =>
      rw [hs] at h
      simp only [Except.bind_ok] at h
      obtain ⟨tys, hs', htys⟩ := typeOfList_unrename xs hx hg hc tys' hs
      rw [hs']
      simp only [Except.bind_ok]
      exact typeOfSet_bwd htys ty c₀ h
  | .call xfn xs, hx, hg, c, c', hc => by
    simp only [renameOk] at hx
    simp only [graftOk] at hg
    intro ty c₀ h
    simp only [renameHoisted, typeOf] at h ⊢
    rw [List.mapM₁_eq_mapM (fun x => justType (typeOf x c env₁))]
    rw [List.mapM₁_eq_mapM (fun x => justType (typeOf x c' env₂))] at h
    have h' := h
    rw [renameHoistedList_eq] at h'
    cases hs : (xs.map (renameHoisted tids pids ren)).mapM (fun x => justType (typeOf x c' env₂)) with
    | error => rw [hs] at h'; cases h'
    | ok tys' =>
      obtain ⟨tys, hs', htys⟩ := typeOfList_unrename xs hx hg hc tys' hs
      rw [hs']
      simp only [Except.bind_ok]
      have hs₂ : (renameHoistedList tids pids ren xs).mapM (fun x => justType (typeOf x c' env₂)) =
          .ok tys' := by
        rw [renameHoistedList_eq]; exact hs
      rw [hs₂] at h
      simp only [Except.bind_ok] at h
      exact typeOfCall_bwd htys ty c₀ h
  | .record axs, hx, hg, c, c', hc => by
    simp only [renameOk] at hx
    simp only [graftOk] at hg
    intro ty c₀ h
    simp only [renameHoisted, typeOf] at h ⊢
    rw [List.mapM₂_eq_mapM (fun (ax : Attr × Expr) =>
      Except.map (fun y => (ax.1, y.1)) (typeOf ax.2 c env₁))]
    rw [List.mapM₂_eq_mapM (fun (ax : Attr × Expr) =>
      Except.map (fun y => (ax.1, y.1)) (typeOf ax.2 c' env₂)), renameHoistedRecord_eq] at h
    cases hs : (axs.map fun ax => (ax.1, renameHoisted tids pids ren ax.2)).mapM
        (fun (ax : Attr × Expr) => Except.map (fun y => (ax.1, y.1)) (typeOf ax.2 c' env₂)) with
    | error => rw [hs] at h; cases h
    | ok atys' =>
      rw [hs] at h
      simp only [Except.bind_ok, ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨atys, hs', hatys⟩ := typeOfRecord_unrename axs hx hg hc atys' hs
      rw [hs']
      simp only [Except.bind_ok, ok, Except.ok.injEq, Prod.mk.injEq]
      refine ⟨_, _, ⟨rfl, rfl⟩, ?_, CapRel.nil⟩
      show CedarType.record (Map.make (atys.map fun p => (p.1, Qualified.required p.2.typeOf))) =
        CedarType.record (Map.make (atys'.map fun p => (p.1, Qualified.required p.2.typeOf)))
      rw [hatys]

theorem typeOfList_unrename : (xs : List Expr) → renameOkList tids pids reserved xs = true →
    graftOkList tids pids env₁.reqty.context xs = true →
    ∀ {c c' : Capabilities}, CapRel tids pids ren reserved c c' → ∀ tys',
    (xs.map (renameHoisted tids pids ren)).mapM (fun x => justType (typeOf x c' env₂)) = .ok tys' →
    ∃ tys, xs.mapM (fun x => justType (typeOf x c env₁)) = .ok tys ∧
      tys.map TypedExpr.typeOf = tys'.map TypedExpr.typeOf
  | [], _, _, _, _, _, tys', h => by
    simp only [List.map_nil, List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨[], rfl, rfl⟩
  | x :: xs, hx, hg, c, c', hc, tys', h => by
    simp only [renameOkList, Bool.and_eq_true] at hx
    simp only [graftOkList, Bool.and_eq_true] at hg
    simp only [List.mapM_cons, List.map_cons] at h ⊢
    cases h₁ : typeOf (renameHoisted tids pids ren x) c' env₂ with
    | error e =>
      have hj : justType (typeOf (renameHoisted tids pids ren x) c' env₂) = .error e := by
        simp [justType, h₁, Except.map]
      rw [hj] at h; cases h
    | ok p =>
      obtain ⟨ty', cc'⟩ := p
      have hj : justType (typeOf (renameHoisted tids pids ren x) c' env₂) = .ok ty' := by
        simp [justType, h₁, Except.map]
      rw [hj] at h
      cases h₂ : (xs.map (renameHoisted tids pids ren)).mapM (fun x => justType (typeOf x c' env₂)) with
      | error => rw [h₂] at h; cases h
      | ok tys₀ =>
        rw [h₂] at h
        simp only [Except.bind_ok, pure, Except.pure, Except.ok.injEq] at h
        subst h
        obtain ⟨ty, cc, h₁', hty, _⟩ := typeOf_unrename x hx.1 hg.1 hc ty' cc' h₁
        obtain ⟨tys, h₂', htys⟩ := typeOfList_unrename xs hx.2 hg.2 hc tys₀ h₂
        have hj' : justType (typeOf x c env₁) = .ok ty := by
          simp [justType, h₁', Except.map]
        refine ⟨ty :: tys, ?_, ?_⟩
        · rw [hj', h₂']; rfl
        · simp [hty, htys]

theorem typeOfRecord_unrename : (axs : List (Attr × Expr)) →
    renameOkRecord tids pids reserved axs = true →
    graftOkRecord tids pids env₁.reqty.context axs = true →
    ∀ {c c' : Capabilities}, CapRel tids pids ren reserved c c' → ∀ atys',
    (axs.map fun ax => (ax.1, renameHoisted tids pids ren ax.2)).mapM
        (fun (ax : Attr × Expr) => Except.map (fun y => (ax.1, y.1)) (typeOf ax.2 c' env₂)) =
      .ok atys' →
    ∃ atys, axs.mapM (fun (ax : Attr × Expr) => Except.map (fun y => (ax.1, y.1)) (typeOf ax.2 c env₁)) =
      .ok atys ∧
      atys.map (fun p => (p.1, Qualified.required p.2.typeOf)) =
        atys'.map (fun p => (p.1, Qualified.required p.2.typeOf))
  | [], _, _, _, _, _, atys', h => by
    simp only [List.map_nil, List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨[], rfl, rfl⟩
  | (a, x) :: axs, hx, hg, c, c', hc, atys', h => by
    simp only [renameOkRecord, Bool.and_eq_true] at hx
    simp only [graftOkRecord, Bool.and_eq_true] at hg
    simp only [List.mapM_cons, List.map_cons] at h ⊢
    cases h₁ : typeOf (renameHoisted tids pids ren x) c' env₂ with
    | error e =>
      have hj : Except.map (fun y => (a, y.1)) (typeOf (renameHoisted tids pids ren x) c' env₂) =
          .error e := by
        simp [h₁, Except.map]
      rw [hj] at h; cases h
    | ok p =>
      obtain ⟨ty', cc'⟩ := p
      have hj : Except.map (fun y => (a, y.1)) (typeOf (renameHoisted tids pids ren x) c' env₂) =
          .ok (a, ty') := by
        simp [h₁, Except.map]
      rw [hj] at h
      cases h₂ : (axs.map fun ax => (ax.1, renameHoisted tids pids ren ax.2)).mapM
          (fun (ax : Attr × Expr) => Except.map (fun y => (ax.1, y.1)) (typeOf ax.2 c' env₂)) with
      | error => rw [h₂] at h; cases h
      | ok atys₀ =>
        rw [h₂] at h
        simp only [Except.bind_ok, pure, Except.pure, Except.ok.injEq] at h
        subst h
        obtain ⟨ty, cc, h₁', hty, _⟩ := typeOf_unrename x hx.1 hg.1 hc ty' cc' h₁
        obtain ⟨atys, h₂', hatys⟩ := typeOfRecord_unrename axs hx.2 hg.2 hc atys₀ h₂
        have hj' : Except.map (fun y => (a, y.1)) (typeOf x c env₁) = .ok (a, ty) := by
          simp [h₁', Except.map]
        refine ⟨(a, ty) :: atys, ?_, ?_⟩
        · rw [hj', h₂']; rfl
        · simp only [List.map_cons, hty, hatys]

end

end Simulation


/-! ## Substituting the action -/

/-- The substitution of `substituteAction`. -/
def actionSubst (uid : EntityUID) : Var → Expr := fun var => match var with
  | .action => .lit (.entityUID uid)
  | _ => .var var

theorem substituteAction_eq (uid : EntityUID) (x : Expr) :
    substituteAction uid x = mapOnVars (actionSubst uid) x := by
  unfold substituteAction
  congr 1

theorem actionSubst_ok (uid : EntityUID) :
    ∀ v, actionSubst uid v = .var v ∨ ∃ p, actionSubst uid v = .lit p ∧ v ≠ .context := by
  intro v; cases v <;> simp [actionSubst]

section Substitute

variable {σ : Var → Expr} (hσ : ∀ v, σ v = .var v ∨ ∃ p, σ v = .lit p ∧ v ≠ .context)

include hσ

mutual

theorem graftOk_mapOnVars {C : RecordType} : (x : Expr) →
    graftOk tids pids C (mapOnVars σ x) = graftOk tids pids C x
  | .getAttr e a => by
    simp only [mapOnVars, graftOk, isContextC_mapOnVars hσ, isContextProvidersC_mapOnVars hσ,
      graftOk_mapOnVars e]
  | .hasAttr e _ => by simp only [mapOnVars, graftOk, graftOk_mapOnVars e]
  | .extHasAttr e _ _ => by simp only [mapOnVars, graftOk, graftOk_mapOnVars e]
  | .lit _ => by simp [mapOnVars, graftOk]
  | .var v => by
    simp only [mapOnVars]
    rcases hσ v with h | ⟨p, h, _⟩
    · rw [h]
    · rw [h]; simp [graftOk]
  | .ite a b c => by
    simp only [mapOnVars, graftOk, graftOk_mapOnVars a, graftOk_mapOnVars b, graftOk_mapOnVars c]
  | .and a b => by simp only [mapOnVars, graftOk, graftOk_mapOnVars a, graftOk_mapOnVars b]
  | .or a b => by simp only [mapOnVars, graftOk, graftOk_mapOnVars a, graftOk_mapOnVars b]
  | .binaryApp _ a b => by
    simp only [mapOnVars, graftOk, graftOk_mapOnVars a, graftOk_mapOnVars b]
  | .unaryApp _ a => by simp only [mapOnVars, graftOk, graftOk_mapOnVars a]
  | .set xs => by
    simp only [mapOnVars, graftOk, List.map₁_eq_map (mapOnVars σ)]
    exact graftOkList_mapOnVars xs
  | .call _ xs => by
    simp only [mapOnVars, graftOk, List.map₁_eq_map (mapOnVars σ)]
    exact graftOkList_mapOnVars xs
  | .record axs => by
    simp only [mapOnVars, graftOk]
    rw [List.map₂_eq_map_snd (mapOnVars σ)]
    exact graftOkRecord_mapOnVars axs

theorem graftOkList_mapOnVars {C : RecordType} : (xs : List Expr) →
    graftOkList tids pids C (xs.map (mapOnVars σ)) = graftOkList tids pids C xs
  | [] => rfl
  | x :: xs => by
    simp only [List.map_cons, graftOkList, graftOk_mapOnVars x, graftOkList_mapOnVars xs]

theorem graftOkRecord_mapOnVars {C : RecordType} : (axs : List (Attr × Expr)) →
    graftOkRecord tids pids C (axs.map fun (a, b) => (a, mapOnVars σ b)) =
      graftOkRecord tids pids C axs
  | [] => rfl
  | (a, x) :: axs => by
    simp only [List.map_cons, graftOkRecord, graftOk_mapOnVars x, graftOkRecord_mapOnVars axs]

end

end Substitute

theorem graftOk_scope (C : RecordType) (s : Cedar.Spec.Scope) (v : Var) :
    graftOk tids pids C (s.toExpr v) = true := by
  cases s <;> simp [Cedar.Spec.Scope.toExpr, Cedar.Spec.Var.eqEntityUID, Cedar.Spec.Var.inEntityUID,
    Cedar.Spec.Var.isEntityType, graftOk]

theorem graftOkList_lits (C : RecordType) (ls : List EntityUID) :
    graftOkList tids pids C (ls.map fun e => .lit (.entityUID e)) = true := by
  induction ls with
  | nil => rfl
  | cons e ls ih => simp only [List.map_cons, graftOkList, graftOk, ih, Bool.and_self]

theorem graftOk_actionScope (C : RecordType) (as : Cedar.Spec.ActionScope) :
    graftOk tids pids C as.toExpr = true := by
  cases as with
  | actionScope s => exact graftOk_scope C s .action
  | actionInAny ls =>
    simp only [Cedar.Spec.ActionScope.toExpr, graftOk, graftOkList_lits, Bool.and_self]

theorem substituteAction_scope (uid : EntityUID) (s : Cedar.Spec.Scope) {v : Var}
    (hv : v ≠ .action) : substituteAction uid (s.toExpr v) = s.toExpr v := by
  rw [substituteAction_eq]
  cases v
  all_goals first
    | exact absurd rfl hv
    | cases s <;> simp [mapOnVars, actionSubst, Cedar.Spec.Scope.toExpr, Cedar.Spec.Var.eqEntityUID,
        Cedar.Spec.Var.inEntityUID, Cedar.Spec.Var.isEntityType]

theorem substituteAction_and (uid : EntityUID) (x₁ x₂ : Expr) :
    substituteAction uid (.and x₁ x₂) = .and (substituteAction uid x₁) (substituteAction uid x₂) := by
  simp only [substituteAction_eq, mapOnVars]

/-! ## Scopes -/

/-- Whenever the expression types in the environment, it has the type `T`. -/
def TypesAs (env : TypeEnv) (x : Expr) (T : CedarType) : Prop :=
  ∀ c tx c₀, typeOf x c env = .ok (tx, c₀) → tx.typeOf = T

theorem typeOf_binaryApp_eq {op : Cedar.Spec.BinaryOp} {x₁ x₂ : Expr} {c : Capabilities}
    {env : TypeEnv} :
    typeOf (.binaryApp op x₁ x₂) c env = (do
      let (ty₁, _) ← typeOf x₁ c env
      let (ty₂, _) ← typeOf x₂ c env
      typeOfBinaryApp op ty₁ ty₂ x₁ x₂ c env) := by
  simp only [typeOf]

theorem typesAs_principal {env : TypeEnv} :
    TypesAs env (.var .principal) (.entity env.reqty.principal) := by
  intro c tx c₀ h
  simp only [typeOf, typeOfVar, ok, Function.comp, Except.ok.injEq, Prod.mk.injEq] at h
  rw [← h.1]; rfl

theorem typesAs_resource {env : TypeEnv} :
    TypesAs env (.var .resource) (.entity env.reqty.resource) := by
  intro c tx c₀ h
  simp only [typeOf, typeOfVar, ok, Function.comp, Except.ok.injEq, Prod.mk.injEq] at h
  rw [← h.1]; rfl

theorem typesAs_uid {env : TypeEnv} {uid : EntityUID} :
    TypesAs env (.lit (.entityUID uid)) (.entity uid.ty) := by
  intro c tx c₀ h
  simp only [typeOf, typeOfLit] at h
  split at h
  · simp only [ok, Function.comp, Except.ok.injEq, Prod.mk.injEq] at h
    rw [← h.1]; rfl
  · cases h

theorem typesAs_set {env : TypeEnv} {xs : List Expr} {c : Capabilities} {tx : TypedExpr}
    {c₀ : Capabilities} (h : typeOf (.set xs) c env = .ok (tx, c₀)) : ∃ T, tx.typeOf = .set T := by
  simp only [typeOf] at h
  rw [List.mapM₁_eq_mapM (fun x => justType (typeOf x c env))] at h
  cases hs : xs.mapM (fun x => justType (typeOf x c env)) with
  | error => rw [hs] at h; cases h
  | ok tys =>
    rw [hs] at h
    simp only [Except.bind_ok] at h
    unfold typeOfSet at h
    split at h
    · cases h
    · split at h
      · simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h
        rw [← h.1]
        exact ⟨_, rfl⟩
      · cases h

theorem typesFF_and_left {env : TypeEnv} {x₁ x₂ : Expr} (h : TypesAs env x₁ (.bool .ff)) :
    TypesAs env (.and x₁ x₂) (.bool .ff) := by
  intro c tx c₀ hx
  simp only [typeOf] at hx
  cases h₁ : typeOf x₁ c env with
  | error => rw [h₁] at hx; cases hx
  | ok p =>
    obtain ⟨ty₁, c₁⟩ := p
    rw [h₁] at hx
    simp only [Except.bind_ok] at hx
    have hff := h c ty₁ c₁ h₁
    unfold typeOfAnd at hx
    simp only [hff, ok, Except.ok.injEq, Prod.mk.injEq] at hx
    rw [← hx.1]
    exact hff

theorem typesFF_and_right {env : TypeEnv} {x₁ x₂ : Expr} (h : TypesAs env x₂ (.bool .ff)) :
    TypesAs env (.and x₁ x₂) (.bool .ff) := by
  intro c tx c₀ hx
  simp only [typeOf] at hx
  cases h₁ : typeOf x₁ c env with
  | error => rw [h₁] at hx; cases hx
  | ok p =>
    obtain ⟨ty₁, c₁⟩ := p
    rw [h₁] at hx
    simp only [Except.bind_ok] at hx
    unfold typeOfAnd at hx
    split at hx
    · rename_i hff
      simp only [ok, Except.ok.injEq, Prod.mk.injEq] at hx
      rw [← hx.1]
      exact hff
    · cases h₂ : typeOf x₂ (c ∪ c₁) env with
      | error => rw [h₂] at hx; cases hx
      | ok q =>
        obtain ⟨ty₂, c₂⟩ := q
        rw [h₂] at hx
        simp only [Except.bind_ok, h _ _ _ h₂, ok, Except.ok.injEq, Prod.mk.injEq] at hx
        rw [← hx.1]
        rfl
    · cases hx

theorem typesFF_is {env : TypeEnv} {x : Expr} {ety ety' : Cedar.Spec.EntityType}
    (hx : TypesAs env x (.entity ety)) (hne : ety' ≠ ety) :
    TypesAs env (.unaryApp (.is ety') x) (.bool .ff) := by
  intro c tx c₀ h
  simp only [typeOf] at h
  cases h₁ : typeOf x c env with
  | error => rw [h₁] at h; cases h
  | ok p =>
    obtain ⟨ty₁, c₁⟩ := p
    rw [h₁] at h
    simp only [Except.bind_ok] at h
    unfold typeOfUnaryApp at h
    simp only [hx _ _ _ h₁, hne, if_false, ok, Function.comp, Except.ok.injEq,
      Prod.mk.injEq] at h
    rw [← h.1]
    rfl

theorem typesFF_eq {env : TypeEnv} {x₁ x₂ : Expr} {e₁ e₂ : Cedar.Spec.EntityType}
    (hx₁ : TypesAs env x₁ (.entity e₁)) (hx₂ : TypesAs env x₂ (.entity e₂)) (hne : e₁ ≠ e₂)
    (hnl : ∀ p, x₁ ≠ .lit p) : TypesAs env (.binaryApp .eq x₁ x₂) (.bool .ff) := by
  intro c tx c₀ h
  rw [typeOf_binaryApp_eq] at h
  cases h₁ : typeOf x₁ c env with
  | error => rw [h₁] at h; cases h
  | ok p =>
    obtain ⟨ty₁, c₁⟩ := p
    cases h₂ : typeOf x₂ c env with
    | error => rw [h₁, h₂] at h; cases h
    | ok q =>
      obtain ⟨ty₂, c₂⟩ := q
      rw [h₁, h₂] at h
      simp only [Except.bind_ok] at h
      unfold typeOfBinaryApp typeOfEq at h
      simp only at h
      split at h
      · exact absurd rfl (hnl _)
      · rw [hx₁ _ _ _ h₁, hx₂ _ _ _ h₂] at h
        have hlub : (CedarType.entity e₁ ⊔ CedarType.entity e₂) = none := by
          simp [lub?, hne]
        simp only [hlub, ok, Function.comp, Except.ok.injEq, Prod.mk.injEq] at h
        rw [← h.1]
        rfl

theorem typesFF_eq_lit {env : TypeEnv} {p₁ p₂ : Prim} (hne : p₁ ≠ p₂) :
    TypesAs env (.binaryApp .eq (.lit p₁) (.lit p₂)) (.bool .ff) := by
  intro c tx c₀ h
  rw [typeOf_binaryApp_eq] at h
  cases h₁ : typeOf (.lit p₁) c env with
  | error => rw [h₁] at h; cases h
  | ok p =>
    obtain ⟨ty₁, c₁⟩ := p
    cases h₂ : typeOf (.lit p₂) c env with
    | error => rw [h₁, h₂] at h; cases h
    | ok q =>
      obtain ⟨ty₂, c₂⟩ := q
      rw [h₁, h₂] at h
      simp only [Except.bind_ok, typeOfBinaryApp, typeOfEq, beq_iff_eq, hne, if_false, ok,
        Function.comp, Except.ok.injEq, Prod.mk.injEq] at h
      rw [← h.1]
      rfl

theorem typesFF_mem {env : TypeEnv} {x₁ x₂ : Expr} {e₁ e₂ : Cedar.Spec.EntityType}
    (hx₁ : TypesAs env x₁ (.entity e₁)) (hx₂ : TypesAs env x₂ (.entity e₂))
    (hin : typeOfInₑ e₁ e₂ x₁ x₂ env = .ff) : TypesAs env (.binaryApp .mem x₁ x₂) (.bool .ff) := by
  intro c tx c₀ h
  rw [typeOf_binaryApp_eq] at h
  cases h₁ : typeOf x₁ c env with
  | error => rw [h₁] at h; cases h
  | ok p =>
    obtain ⟨ty₁, c₁⟩ := p
    cases h₂ : typeOf x₂ c env with
    | error => rw [h₁, h₂] at h; cases h
    | ok q =>
      obtain ⟨ty₂, c₂⟩ := q
      rw [h₁, h₂] at h
      simp only [Except.bind_ok] at h
      unfold typeOfBinaryApp at h
      rw [hx₁ _ _ _ h₁, hx₂ _ _ _ h₂] at h
      simp only [hin, ok, Except.ok.injEq, Prod.mk.injEq] at h
      rw [← h.1]
      rfl

theorem typesFF_mem_set {env : TypeEnv} {x₁ x₂ : Expr} {e₁ : Cedar.Spec.EntityType}
    (hx₁ : TypesAs env x₁ (.entity e₁))
    (hx₂ : ∀ c tx c₀, typeOf x₂ c env = .ok (tx, c₀) → ∃ T, tx.typeOf = .set T)
    (hin : ∀ e₂, typeOfInₛ e₁ e₂ x₁ x₂ env = .ff) :
    TypesAs env (.binaryApp .mem x₁ x₂) (.bool .ff) := by
  intro c tx c₀ h
  rw [typeOf_binaryApp_eq] at h
  cases h₁ : typeOf x₁ c env with
  | error => rw [h₁] at h; cases h
  | ok p =>
    obtain ⟨ty₁, c₁⟩ := p
    cases h₂ : typeOf x₂ c env with
    | error => rw [h₁, h₂] at h; cases h
    | ok q =>
      obtain ⟨ty₂, c₂⟩ := q
      rw [h₁, h₂] at h
      simp only [Except.bind_ok] at h
      obtain ⟨T, hT⟩ := hx₂ _ _ _ h₂
      unfold typeOfBinaryApp at h
      rw [hx₁ _ _ _ h₁, hT] at h
      cases T with
      | entity e₂ =>
        simp only [hin, ok, Except.ok.injEq, Prod.mk.injEq] at h
        rw [← h.1]
        rfl
      | _ => simp [err] at h

theorem descendentOf_eq_false {S : Schema} {env : TypeEnv} (hets : env.ets = S.ets)
    (hacts : env.acts = S.acts) {ety ety' : Cedar.Spec.EntityType}
    (h : Dogwood.Spec.Schema.memberOfType S ety ety' = false) : env.descendentOf ety ety' = false := by
  unfold Dogwood.Spec.Schema.memberOfType at h
  simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at h
  obtain ⟨⟨hne, hanc⟩, hmd⟩ := h
  unfold TypeEnv.descendentOf
  rw [if_neg hne, hets, hacts]
  split
  · rename_i entry hfind
    simp only [hfind] at hanc
    exact hanc
  · exact hmd

theorem actionUID?_lit {acts : ActionSchema} {uid : EntityUID} (h : acts.contains uid = true) :
    actionUID? (.lit (.entityUID uid)) acts = some uid := by
  simp [actionUID?, entityUID?, h]

theorem entityUIDs?_lits (ls : List EntityUID) :
    entityUIDs? (.set (ls.map fun e => .lit (.entityUID e))) = some ls := by
  simp only [entityUIDs?]
  induction ls with
  | nil => rfl
  | cons e ls ih => simp only [List.map_cons, List.mapM_cons, ih]; rfl

/-- **A principal or resource scope types as `false` in an environment whose scope type it does
not admit**, whatever the context. -/
theorem typesFF_scope {S : Schema} {env : TypeEnv} (hets : env.ets = S.ets)
    (hacts : env.acts = S.acts) {v : Var} {ety : Cedar.Spec.EntityType}
    (hv : TypesAs env (.var v) (.entity ety)) {s : Cedar.Spec.Scope}
    (hs : Dogwood.Spec.scopeAdmitsType S s ety = false) : TypesAs env (s.toExpr v) (.bool .ff) := by
  cases s with
  | any => simp [Dogwood.Spec.scopeAdmitsType] at hs
  | eq uid =>
    simp only [Dogwood.Spec.scopeAdmitsType, beq_eq_false_iff_ne, ne_eq] at hs
    exact typesFF_eq hv typesAs_uid (fun h => hs h.symm) (fun p h => by cases h)
  | mem uid =>
    simp only [Dogwood.Spec.scopeAdmitsType] at hs
    exact typesFF_mem hv typesAs_uid (by
      simp [typeOfInₑ, actionUID?, entityUID?, descendentOf_eq_false hets hacts hs])
  | is ety' =>
    simp only [Dogwood.Spec.scopeAdmitsType, beq_eq_false_iff_ne] at hs
    exact typesFF_is hv hs
  | isMem ety' uid =>
    simp only [Dogwood.Spec.scopeAdmitsType, beq_eq_false_iff_ne] at hs
    exact typesFF_and_left (typesFF_is hv hs)

/-- **An action scope types as `false`, once the action is substituted, in an environment whose
action it does not admit**, whatever the context. -/
theorem typesFF_actionScope {S : Schema} {env : TypeEnv} (hacts : env.acts = S.acts)
    (hact : S.acts.contains env.reqty.action = true) {as : Cedar.Spec.ActionScope}
    (hs : Dogwood.Spec.actionScopeAdmits S env.reqty.action as = false) :
    TypesAs env (substituteAction env.reqty.action as.toExpr) (.bool .ff) := by
  have hact' : env.acts.contains env.reqty.action = true := by rw [hacts]; exact hact
  simp only [substituteAction_eq]
  cases as with
  | actionScope s =>
    cases s with
    | any => simp [Dogwood.Spec.actionScopeAdmits] at hs
    | eq uid =>
      simp only [Dogwood.Spec.actionScopeAdmits, beq_eq_false_iff_ne, ne_eq] at hs
      simp only [Cedar.Spec.ActionScope.toExpr, Cedar.Spec.Scope.toExpr,
        Cedar.Spec.Var.eqEntityUID, mapOnVars, actionSubst]
      exact typesFF_eq_lit (fun h => hs (by injection h))
    | mem uid =>
      simp only [Dogwood.Spec.actionScopeAdmits] at hs
      simp only [Cedar.Spec.ActionScope.toExpr, Cedar.Spec.Scope.toExpr,
        Cedar.Spec.Var.inEntityUID, mapOnVars, actionSubst]
      exact typesFF_mem typesAs_uid typesAs_uid (by
        simp [typeOfInₑ, actionUID?, entityUID?, hacts, hact, hs])
    | is ety =>
      simp only [Dogwood.Spec.actionScopeAdmits, beq_eq_false_iff_ne] at hs
      simp only [Cedar.Spec.ActionScope.toExpr, Cedar.Spec.Scope.toExpr,
        Cedar.Spec.Var.isEntityType, mapOnVars, actionSubst]
      exact typesFF_is typesAs_uid (Ne.symm hs)
    | isMem ety uid =>
      simp only [Dogwood.Spec.actionScopeAdmits, Bool.and_eq_false_iff, beq_eq_false_iff_ne] at hs
      simp only [Cedar.Spec.ActionScope.toExpr, Cedar.Spec.Scope.toExpr, Cedar.Spec.Var.isEntityType,
        Cedar.Spec.Var.inEntityUID, mapOnVars, actionSubst]
      rcases hs with hs | hs
      · exact typesFF_and_left (typesFF_is typesAs_uid (Ne.symm hs))
      · exact typesFF_and_right (typesFF_mem typesAs_uid typesAs_uid (by
          simp [typeOfInₑ, actionUID?, entityUID?, hacts, hact, hs]))
  | actionInAny ls =>
    simp only [Dogwood.Spec.actionScopeAdmits] at hs
    simp only [Cedar.Spec.ActionScope.toExpr, mapOnVars, actionSubst,
      List.map₁_eq_map (mapOnVars (actionSubst env.reqty.action)), List.map_map, Function.comp_def]
    exact typesFF_mem_set typesAs_uid (fun _ _ _ h => typesAs_set h) (fun e₂ => by
      unfold typeOfInₛ
      rw [actionUID?_lit hact', entityUIDs?_lits]
      simp only [hacts, hs, Bool.false_eq_true, if_false])


/-- A principal, action or resource scope the rule's scope does not admit types as `false`, and
so does the rule. -/
theorem typesFF_policy {S : Schema} {env : TypeEnv} (hets : env.ets = S.ets)
    (hacts : env.acts = S.acts) (hact : S.acts.contains env.reqty.action = true)
    {p : Cedar.Spec.Policy} (hadm : (Dogwood.Spec.Policy.ofCedar p).admits S env = false) :
    TypesAs env (substituteAction env.reqty.action p.toExpr) (.bool .ff) := by
  obtain ⟨pid, eff, ps, as, rs, cs⟩ := p
  cases ps with | principalScope ps =>
  cases rs with | resourceScope rs =>
  simp only [Dogwood.Spec.Policy.admits, Dogwood.Spec.Policy.ofCedar, Bool.and_eq_false_iff] at hadm
  simp only [Cedar.Spec.Policy.toExpr, Cedar.Spec.PrincipalScope.toExpr,
    Cedar.Spec.ResourceScope.toExpr, substituteAction_and]
  rcases hadm with (hadm | hadm) | hadm
  · rw [substituteAction_scope env.reqty.action ps (v := .principal) (by decide)]
    exact typesFF_and_left (typesFF_scope hets hacts typesAs_principal hadm)
  · exact typesFF_and_right (typesFF_and_left (typesFF_actionScope hacts hact hadm))
  · rw [substituteAction_scope env.reqty.action rs (v := .resource) (by decide)]
    exact typesFF_and_right (typesFF_and_right (typesFF_and_left
      (typesFF_scope hets hacts typesAs_resource hadm)))

/-! ## Rules -/

/-- The typings of `x` in `env₁` and of `x'` in `env₂`, related backwards, under every pair of
related capabilities. -/
def SimB (tids pids : List String) (ren : Bool → String → Attr) (reserved : Attr → Bool)
    (env₁ env₂ : TypeEnv) (x x' : Expr) : Prop :=
  ∀ c c', CapRel tids pids ren reserved c c' →
    ResRelB tids pids ren reserved (typeOf x c env₁) (typeOf x' c' env₂)

theorem simB_and {env₁ env₂ : TypeEnv} {x₁ x₂ x₁' x₂' : Expr}
    (h₁ : SimB tids pids ren reserved env₁ env₂ x₁ x₁')
    (h₂ : SimB tids pids ren reserved env₁ env₂ x₂ x₂') :
    SimB tids pids ren reserved env₁ env₂ (.and x₁ x₂) (.and x₁' x₂') := by
  intro c c' hc ty c₀ h
  simp only [typeOf] at h ⊢
  cases h₁' : typeOf x₁' c' env₂ with
  | error => rw [h₁'] at h; cases h
  | ok p =>
    obtain ⟨ty₁, c₁⟩ := p
    rw [h₁'] at h
    simp only [Except.bind_ok] at h
    obtain ⟨tx₁, cx₁, h₁'', hty₁, hc₁⟩ := h₁ c c' hc ty₁ c₁ h₁'
    rw [h₁'']
    simp only [Except.bind_ok]
    exact typeOfAnd_bwd hty₁.symm hc₁ (h₂ _ _ (hc.union hc₁)) ty c₀ h

/-- A conjunction whose first conjunct types as `false` types without its second. -/
theorem simB_and_ff {env₁ env₂ : TypeEnv} {x₁ x₂ x₁' x₂' : Expr}
    (h₁ : SimB tids pids ren reserved env₁ env₂ x₁ x₁') (hff : TypesAs env₁ x₁ (.bool .ff)) :
    SimB tids pids ren reserved env₁ env₂ (.and x₁ x₂) (.and x₁' x₂') := by
  intro c c' hc ty c₀ h
  simp only [typeOf] at h ⊢
  cases h₁' : typeOf x₁' c' env₂ with
  | error => rw [h₁'] at h; cases h
  | ok p =>
    obtain ⟨ty₁, c₁⟩ := p
    rw [h₁'] at h
    simp only [Except.bind_ok] at h
    obtain ⟨tx₁, cx₁, h₁'', hty₁, _⟩ := h₁ c c' hc ty₁ c₁ h₁'
    have hff₁ := hff c tx₁ cx₁ h₁''
    rw [h₁'']
    simp only [Except.bind_ok]
    unfold typeOfAnd at h ⊢
    simp only [← hty₁, hff₁, ok, Except.ok.injEq, Prod.mk.injEq] at h ⊢
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨_, _, ⟨rfl, rfl⟩, hty₁, CapRel.nil⟩

section Rules

variable (hren : ∀ b₁ i₁ b₂ i₂, i₁ ∈ (if b₁ then tids else pids) → i₂ ∈ (if b₂ then tids else pids) →
      ren b₁ i₁ = ren b₂ i₂ → b₁ = b₂ ∧ i₁ = i₂)
    (hres : ∀ b i, reserved (ren b i) = true)
    {f : ActionSchemaEntry → ActionSchemaEntry} {env₁ env₂ : TypeEnv}
    (henv : EnvRel tids pids ren reserved f env₁ env₂)
    (htp : tids.contains "providers" = false)

include hren hres henv htp

theorem simB_substituteAction {X : Expr} (hX : renameOk tids pids reserved X = true)
    (hgX : graftOk tids pids env₁.reqty.context X = true) :
    SimB tids pids ren reserved env₁ env₂ (substituteAction env₁.reqty.action X)
      (renameHoisted tids pids ren (substituteAction env₁.reqty.action X)) := fun _ _ hc =>
  typeOf_unrename hren hres henv htp _
    (by rw [substituteAction_eq, renameOk_mapOnVars (actionSubst_ok _)]; exact hX)
    (by rw [substituteAction_eq, graftOk_mapOnVars (actionSubst_ok _)]; exact hgX) hc

/-- **In an environment the rule's scope does not admit, the crate's rule types as the
specification's**, whatever either context declares: a scope conjunct types as `false`, the same
on both sides, and Cedar's typechecker types nothing after it. -/
theorem simB_not_admits {S : Schema} (hets : env₁.ets = S.ets) (hacts : env₁.acts = S.acts)
    (hact : S.acts.contains env₁.reqty.action = true) {p : Cedar.Spec.Policy}
    (hp : renameOk tids pids reserved p.toExpr = true)
    (hadm : (Dogwood.Spec.Policy.ofCedar p).admits S env₁ = false) :
    SimB tids pids ren reserved env₁ env₂ (substituteAction env₁.reqty.action p.toExpr)
      (renameHoisted tids pids ren (substituteAction env₁.reqty.action p.toExpr)) := by
  obtain ⟨pid, eff, ps, as, rs, cs⟩ := p
  cases ps with | principalScope ps =>
  cases rs with | resourceScope rs =>
  simp only [Dogwood.Spec.Policy.admits, Dogwood.Spec.Policy.ofCedar, Bool.and_eq_false_iff] at hadm
  simp only [Cedar.Spec.Policy.toExpr, Cedar.Spec.PrincipalScope.toExpr,
    Cedar.Spec.ResourceScope.toExpr, renameOk, Bool.and_eq_true] at hp
  obtain ⟨hP, hA, hR, _⟩ := hp
  have sP := simB_substituteAction hren hres henv htp hP (graftOk_scope _ ps .principal)
  have sA := simB_substituteAction hren hres henv htp hA (graftOk_actionScope _ as)
  have sR := simB_substituteAction hren hres henv htp hR (graftOk_scope _ rs .resource)
  simp only [Cedar.Spec.Policy.toExpr, Cedar.Spec.PrincipalScope.toExpr,
    Cedar.Spec.ResourceScope.toExpr, substituteAction_and, renameHoisted]
  rcases hadm with (hadm | hadm) | hadm
  · refine simB_and_ff sP ?_
    rw [substituteAction_scope env₁.reqty.action ps (v := .principal) (by decide)]
    exact typesFF_scope hets hacts typesAs_principal hadm
  · exact simB_and sP (simB_and_ff sA (typesFF_actionScope hacts hact hadm))
  · refine simB_and sP (simB_and sA (simB_and_ff sR ?_))
    rw [substituteAction_scope env₁.reqty.action rs (v := .resource) (by decide)]
    exact typesFF_scope hets hacts typesAs_resource hadm

/-- **A rule's typing, backwards**, in an environment of the crate's schema `S`: the crate's rule
types as the renamed one, when the crate's context declares the rule's hoisted reads wherever the
rule's scope admits the environment. -/
theorem typecheckPolicy_unrename {S : Schema} (hets : env₁.ets = S.ets) (hacts : env₁.acts = S.acts)
    (hact : S.acts.contains env₁.reqty.action = true) {p : Cedar.Spec.Policy}
    (hp : renameOk tids pids reserved p.toExpr = true)
    (hg : (Dogwood.Spec.Policy.ofCedar p).admits S env₁ = true →
      graftOk tids pids env₁.reqty.context p.toExpr = true)
    {ty : TypedExpr} (h : typecheckPolicy (renamePolicy tids pids ren p) env₂ = .ok ty) :
    ∃ tx, typecheckPolicy p env₁ = .ok tx ∧ tx.typeOf = ty.typeOf := by
  have hsim : SimB tids pids ren reserved env₁ env₂ (substituteAction env₁.reqty.action p.toExpr)
      (renameHoisted tids pids ren (substituteAction env₁.reqty.action p.toExpr)) := by
    cases hadm : (Dogwood.Spec.Policy.ofCedar p).admits S env₁
    · exact simB_not_admits hren hres henv htp hets hacts hact hp hadm
    · exact simB_substituteAction hren hres henv htp hp (hg hadm)
  have hexpr : substituteAction env₂.reqty.action (renamePolicy tids pids ren p).toExpr =
      renameHoisted tids pids ren (substituteAction env₁.reqty.action p.toExpr) := by
    rw [toExpr_renamePolicy, henv.action, substituteAction_eq, substituteAction_eq,
      mapOnVars_renameHoisted (actionSubst_ok _)]
  unfold typecheckPolicy at h ⊢
  rw [hexpr] at h
  dsimp only at h ⊢
  simp only [show (∅ : Capabilities) = [] from rfl] at h ⊢
  cases ht : typeOf (renameHoisted tids pids ren (substituteAction env₁.reqty.action p.toExpr)) []
      env₂ with
  | error => rw [ht] at h; cases h
  | ok r =>
    obtain ⟨t', c'⟩ := r
    rw [ht] at h
    simp only at h
    obtain ⟨t, c, ht', hty, _⟩ := hsim [] [] CapRel.nil t' c' ht
    rw [ht']
    simp only [hty]
    split at h
    · rename_i hsub
      rw [if_pos hsub]
      simp only [Except.ok.injEq] at h
      subst h
      exact ⟨t, rfl, hty⟩
    · cases h

end Rules

/-! ## Entities and environments -/

section Entities

variable {S₁ S₂ : Schema} (hets : S₂.ets = S₁.ets)
    (hcont : ∀ uid, S₂.acts.contains uid = S₁.acts.contains uid)
    (htype : ∀ ety, S₂.acts.actionType? ety = S₁.acts.actionType? ety)

include hets hcont htype

mutual

theorem checkEntities_unrename : (x : Expr) →
    checkEntities S₂ (renameHoisted tids pids ren x) = .ok () → checkEntities S₁ x = .ok ()
  | .lit p, h => by
    rw [renameHoisted_lit] at h
    cases p <;> simp_all [checkEntities]
  | .var v, _ => by simp [checkEntities]
  | .getAttr e a, h => by
    rw [renameHoisted_getAttr] at h
    simp only [checkEntities] at h ⊢
    unfold renBase at h
    split at h
    · rename_i hA
      simp only [Bool.and_eq_true] at hA
      rw [isContextC_eq hA.1]
      simp [checkEntities]
    · split at h
      · rename_i _ hB
        simp only [Bool.and_eq_true] at hB
        rw [isContextProvidersC_eq hB.1]
        simp [checkEntities]
      · exact checkEntities_unrename e h
  | .hasAttr e a, h => by
    simp only [renameHoisted, checkEntities] at h ⊢
    exact checkEntities_unrename e h
  | .extHasAttr e a _, h => by
    simp only [renameHoisted, checkEntities] at h ⊢
    exact checkEntities_unrename e h
  | .unaryApp op e, h => by
    simp only [renameHoisted] at h
    cases op with
    | is ety =>
      simp only [checkEntities, hets, htype] at h ⊢
      split at h
      · rw [if_pos (by assumption)]; exact checkEntities_unrename e h
      · cases h
    | _ => simp only [checkEntities] at h ⊢; exact checkEntities_unrename e h
  | .ite a b c, h => by
    simp only [renameHoisted, checkEntities] at h ⊢
    cases ha : checkEntities S₂ (renameHoisted tids pids ren a) <;>
      cases hb : checkEntities S₂ (renameHoisted tids pids ren b) <;>
      cases hc : checkEntities S₂ (renameHoisted tids pids ren c) <;>
      simp only [ha, hb, hc, Except.bind_ok, Except.bind_err] at h <;> (try cases h)
    rw [checkEntities_unrename a ha, checkEntities_unrename b hb, checkEntities_unrename c hc]
    rfl
  | .and a b, h | .or a b, h | .binaryApp _ a b, h => by
    simp only [renameHoisted, checkEntities] at h ⊢
    cases ha : checkEntities S₂ (renameHoisted tids pids ren a) <;>
      cases hb : checkEntities S₂ (renameHoisted tids pids ren b) <;>
      simp only [ha, hb, Except.bind_ok, Except.bind_err] at h <;> (try cases h)
    rw [checkEntities_unrename a ha, checkEntities_unrename b hb]
    rfl
  | .set xs, h | .call _ xs, h => by
    simp only [renameHoisted, checkEntities] at h ⊢
    have hall : ∀ x ∈ xs, checkEntities S₂ (renameHoisted tids pids ren x) = .ok () := by
      intro x hx
      have hmem : renameHoisted tids pids ren x ∈ renameHoistedList tids pids ren xs := by
        rw [renameHoistedList_eq]; exact List.mem_map_of_mem hx
      exact List.forM_ok_implies_all_ok _ _ h ⟨_, hmem⟩ (List.mem_attach _ _)
    apply List.all_ok_implies_forM_ok
    rintro ⟨v, hv⟩ _
    exact checkEntitiesList_unrename xs hall v hv
  | .record axs, h => by
    simp only [renameHoisted, checkEntities] at h ⊢
    have hall : ∀ ax ∈ axs, checkEntities S₂ (renameHoisted tids pids ren ax.2) = .ok () := by
      intro ax hax
      have hmem : (ax.1, renameHoisted tids pids ren ax.2) ∈ renameHoistedRecord tids pids ren axs := by
        rw [renameHoistedRecord_eq]
        exact List.mem_map_of_mem (f := fun ax => (ax.1, renameHoisted tids pids ren ax.2)) hax
      have := List.forM_ok_implies_all_ok _ _ h
      apply this ⟨_, List.sizeOf_snd_lt_sizeOf_list hmem⟩
      simp only [List.attach₂, List.mem_pmap]
      exact ⟨_, hmem, rfl⟩
    apply List.all_ok_implies_forM_ok
    intro y hy
    have hy' := List.mem_attach₂ hy
    obtain ⟨⟨a, v⟩, _⟩ := y
    simp only at hy' ⊢
    exact checkEntitiesRecord_unrename axs hall (a, v) hy'

theorem checkEntitiesList_unrename : (xs : List Expr) →
    (∀ x ∈ xs, checkEntities S₂ (renameHoisted tids pids ren x) = .ok ()) →
    ∀ x ∈ xs, checkEntities S₁ x = .ok ()
  | [], _, _, hx => by cases hx
  | x :: xs, h, y, hy => by
    rcases List.mem_cons.mp hy with hyx | hy
    · rw [hyx]; exact checkEntities_unrename x (h x (by simp))
    · exact checkEntitiesList_unrename xs (fun z hz => h z (by simp [hz])) y hy

theorem checkEntitiesRecord_unrename : (axs : List (Attr × Expr)) →
    (∀ ax ∈ axs, checkEntities S₂ (renameHoisted tids pids ren ax.2) = .ok ()) →
    ∀ ax ∈ axs, checkEntities S₁ ax.2 = .ok ()
  | [], _, _, hx => by cases hx
  | (a, x) :: axs, h, ay, hy => by
    rcases List.mem_cons.mp hy with hyx | hy
    · rw [hyx]; exact checkEntities_unrename x (h (a, x) (by simp))
    · exact checkEntitiesRecord_unrename axs (fun z hz => h z (by simp [hz])) ay hy

end

end Entities

theorem env_of_mem_environments {S : Schema} {env : TypeEnv} (h : env ∈ S.environments) :
    env.ets = S.ets ∧ env.acts = S.acts ∧ S.acts.contains env.reqty.action = true := by
  rw [environments_eq_quads] at h
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp h
  refine ⟨rfl, rfl, ?_⟩
  have := Map.in_list_implies_contains (mem_envQuads hq)
  simp only [ActionSchema.contains, Map.contains] at this ⊢
  exact this

/-- A rule types as `false` in every environment of the schema its scope does not admit. -/
theorem typecheckPolicy_ff {S : Schema} {env : TypeEnv} (henv : env ∈ S.environments)
    {p : Cedar.Spec.Policy} (hadm : (Dogwood.Spec.Policy.ofCedar p).admits S env = false)
    {t : TypedExpr} (h : typecheckPolicy p env = .ok t) : t.typeOf = .bool .ff := by
  obtain ⟨hets, hacts, hact⟩ := env_of_mem_environments henv
  unfold typecheckPolicy at h
  dsimp only at h
  cases ht : typeOf (substituteAction env.reqty.action p.toExpr) ∅ env with
  | error => rw [ht] at h; cases h
  | ok r =>
    obtain ⟨tx, c⟩ := r
    rw [ht] at h
    simp only at h
    split at h
    · simp only [Except.ok.injEq] at h
      subst h
      exact typesFF_policy hets hacts hact hadm _ _ _ ht
    · cases h

end

end Dogwood.Thm.Frontend.CedarComplete

namespace Dogwood.Thm.Frontend

open Dogwood.Frontend Dogwood.Frontend.Validate
open Cedar.Validation
open Cedar.Spec (Attr EntityUID)
open Cedar.Data (Map)
open CedarComplete

/-- **A rule Cedar's validator accepts admits some request environment of the schema**: in every
environment its scope does not admit, the rule types as `false` (`typecheckPolicy_ff`), and the
validator rejects a rule that types as `false` in every environment. -/
theorem exists_admitted_of_validate {ps : Cedar.Spec.Policies} {S : Schema}
    (h : Cedar.Validation.validate ps S = .ok ()) {p : Cedar.Spec.Policy} (hp : p ∈ ps) :
    ∃ env ∈ S.environments, (Dogwood.Spec.Policy.ofCedar p).admits S env = true := by
  have hp₁ := List.forM_ok_implies_all_ok _ _ h p hp
  unfold typecheckPolicyWithEnvironments at hp₁
  cases hce : checkEntities S p.toExpr with
  | error => rw [hce] at hp₁; cases hp₁
  | ok u =>
    rw [hce] at hp₁
    simp only [Except.mapError, Except.bind_ok] at hp₁
    cases hm : S.environments.mapM (typecheckPolicy p) with
    | error => rw [hm] at hp₁; cases hp₁
    | ok tys =>
      rw [hm] at hp₁
      simp only [Except.bind_ok] at hp₁
      by_cases hex : ∃ env ∈ S.environments, (Dogwood.Spec.Policy.ofCedar p).admits S env = true
      · exact hex
      · exfalso
        have hff : allFalse tys = true := by
          simp only [allFalse, List.all_eq_true, beq_iff_eq]
          intro t ht
          obtain ⟨env, henv, het⟩ := List.mapM_ok_implies_all_from_ok hm t ht
          have hadm : (Dogwood.Spec.Policy.ofCedar p).admits S env = false := by
            cases hb : (Dogwood.Spec.Policy.ofCedar p).admits S env
            · rfl
            · exact absurd ⟨env, henv, hb⟩ hex
          exact typecheckPolicy_ff henv hadm het
        rw [hff] at hp₁
        cases hp₁

/-- **Cedar's validator accepts the crate's rules against the crate's augmented schema** when it
accepts the renamed rules against the specification's, under the assumptions of
`validate_renameHoisted` and one more, `hgraft`: in every request environment of the crate's
schema that a rule's scope admits, the action's context declares each hoisted read of the rule as
the crate's lowering reads it (`graftOk`; `CtxRel` then gives each the specification's type). In
an environment the scope does not admit, the rule types as `false` on both sides without reading
the context, so the crate's context need not declare the leaves of rules that do not apply to
it. -/
theorem validate_renameHoisted_converse {tids pids : List String} {ren : Bool → String → Attr}
    {reserved : Attr → Bool}
    (hren : ∀ b₁ i₁ b₂ i₂, i₁ ∈ (if b₁ then tids else pids) → i₂ ∈ (if b₂ then tids else pids) →
      ren b₁ i₁ = ren b₂ i₂ → b₁ = b₂ ∧ i₁ = i₂)
    (hres : ∀ b i, reserved (ren b i) = true) (htp : tids.contains "providers" = false)
    {S₁ S₂ : Schema} {xs : Cedar.Spec.Policies} {f : ActionSchemaEntry → ActionSchemaEntry}
    (hets : S₂.ets = S₁.ets) (hacts : S₂.acts = S₁.acts.mapOnValues f)
    (hf : ∀ e, (f e).appliesToPrincipal = e.appliesToPrincipal ∧
      (f e).appliesToResource = e.appliesToResource ∧ (f e).ancestors = e.ancestors)
    (hctx : ∀ uid e, S₁.acts.find? uid = some e → CtxRel tids pids ren reserved e.context (f e).context)
    (hwf : S₁.acts.WellFormed)
    (hprov : pids ≠ [] → ∀ uid e q ety, S₁.acts.find? uid = some e →
      e.context.find? "providers" = some q → q.getType ≠ .entity ety)
    (hx : ∀ p ∈ xs, renameOk tids pids reserved p.toExpr = true)
    (hgraft : ∀ p ∈ xs, ∀ env ∈ S₁.environments,
      (Dogwood.Spec.Policy.ofCedar p).admits S₁ env = true →
        graftOk tids pids env.reqty.context p.toExpr = true)
    (h₂ : Cedar.Validation.validate (xs.map (renamePolicy tids pids ren)) S₂ = .ok ()) :
    Cedar.Validation.validate xs S₁ = .ok () := by
  have hcont : ∀ uid, S₂.acts.contains uid = S₁.acts.contains uid := by
    intro uid; rw [hacts]; exact mapOnValues_contains _ uid
  have htype : ∀ ety, S₂.acts.actionType? ety = S₁.acts.actionType? ety := by
    intro ety; rw [hacts]; exact mapOnValues_actionType? _ ety
  unfold Cedar.Validation.validate at h₂ ⊢
  apply List.all_ok_implies_forM_ok
  intro p hp
  have hp₂ := List.forM_ok_implies_all_ok _ _ h₂ (renamePolicy tids pids ren p)
    (List.mem_map_of_mem hp)
  unfold typecheckPolicyWithEnvironments at hp₂ ⊢
  cases hce : checkEntities S₂ (renamePolicy tids pids ren p).toExpr with
  | error => rw [hce] at hp₂; cases hp₂
  | ok u =>
    rw [hce] at hp₂
    have hce' : checkEntities S₁ p.toExpr = .ok () := by
      rw [toExpr_renamePolicy] at hce
      exact checkEntities_unrename hets hcont htype _ hce
    rw [hce']
    simp only [Except.mapError, Except.bind_ok] at hp₂ ⊢
    rw [environments_eq_quads S₁]
    rw [environments_mapOnValues hacts (fun e => ⟨(hf e).1, (hf e).2.1⟩)] at hp₂
    rw [List.mapM_map] at hp₂ ⊢
    cases hm : (envQuads S₁).mapM (typecheckPolicy (renamePolicy tids pids ren p) ∘
        quadEnv S₂ (fun e => (f e).context)) with
    | error => rw [hm] at hp₂; cases hp₂
    | ok tys' =>
      rw [hm] at hp₂
      have hpt : ∀ q ∈ envQuads S₁, ∀ t, (typecheckPolicy (renamePolicy tids pids ren p) ∘
          quadEnv S₂ (fun e => (f e).context)) q = .ok t →
          ∃ t', (typecheckPolicy p ∘ quadEnv S₁ (·.context)) q = .ok t' ∧ t'.typeOf = t.typeOf := by
        intro q hq t ht
        have hmem := mem_envQuads hq
        have hfind : S₁.acts.find? q.1 = some q.2.1 := Map.mem_toList_find? hwf hmem
        have henv : EnvRel tids pids ren reserved f (quadEnv S₁ (·.context) q)
            (quadEnv S₂ (fun e => (f e).context) q) :=
          { ets := hets, acts := hacts, ancestors := fun e => (hf e).2.2, principal := rfl,
            action := rfl, resource := rfl, context := hctx q.1 q.2.1 hfind,
            providers := fun hne qq ety hq' => hprov hne q.1 q.2.1 qq ety hfind hq' }
        have hin : quadEnv S₁ (·.context) q ∈ S₁.environments := by
          rw [environments_eq_quads]; exact List.mem_map_of_mem hq
        obtain ⟨_, _, hact⟩ := env_of_mem_environments hin
        exact typecheckPolicy_unrename hren hres henv htp (S := S₁) rfl rfl hact (hx p hp)
          (hgraft p hp _ hin) ht
      obtain ⟨tys, hm', htys⟩ := mapM_typeOf_rel _ hpt tys' hm
      rw [hm']
      simp only [Except.bind_ok] at hp₂ ⊢
      have hall : allFalse tys = allFalse tys' := by
        have hm : ∀ ts : List TypedExpr, allFalse ts =
            (ts.map TypedExpr.typeOf).all (· == CedarType.bool .ff) := by
          intro ts; simp [allFalse, List.all_map, Function.comp_def]
        rw [hm, hm, htys]
      rw [hall]
      exact hp₂

end Dogwood.Thm.Frontend
