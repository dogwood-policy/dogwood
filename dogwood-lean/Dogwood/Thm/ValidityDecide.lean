import Dogwood.Eval.Validity
import Dogwood.Thm.SafetyDecide
import Dogwood.Thm.TypingDecide
import Dogwood.Thm.ScopesDecide

/-!
# The validity check decides validity

`validationFindings_eq_nil_iff`: validation finds no problem in a policy set exactly when it is
valid. Validity is decidable.
-/

namespace Dogwood.Thm

open Dogwood.Spec Dogwood.Spec.Temporal Dogwood.Eval

mutual

theorem Expr.readsContextB_iff (reserved : List Cedar.Spec.Attr) : (x : Expr) →
    (x.readsContextB reserved = true ↔ x.ReadsContext reserved)
  | .lit _ => by simp [Expr.readsContextB, Expr.ReadsContext]
  | .var v => by cases v <;> simp [Expr.readsContextB, Expr.ReadsContext]
  | .getAttr x a | .hasAttr x a | .extHasAttr x a _ => by
    simp only [Expr.readsContextB, Expr.ReadsContext]
    split
    · simp
    · exact Expr.readsContextB_iff reserved x
  | .unaryApp _ x => by
    simp only [Expr.readsContextB, Expr.ReadsContext]; exact Expr.readsContextB_iff reserved x
  | .ite a b c => by
    simp [Expr.readsContextB, Expr.ReadsContext, Expr.readsContextB_iff reserved a,
      Expr.readsContextB_iff reserved b, Expr.readsContextB_iff reserved c, and_assoc]
  | .and a b | .or a b | .binaryApp _ a b => by
    simp [Expr.readsContextB, Expr.ReadsContext, Expr.readsContextB_iff reserved a,
      Expr.readsContextB_iff reserved b]
  | .set xs | .call _ xs => by
    simp only [Expr.readsContextB, Expr.ReadsContext]; exact Expr.readsContextListB_iff reserved xs
  | .record axs => by
    simp only [Expr.readsContextB, Expr.ReadsContext]
    exact Expr.readsContextRecordB_iff reserved axs
  | .temporal _ | .provider _ => by simp [Expr.readsContextB, Expr.ReadsContext]

theorem Expr.readsContextListB_iff (reserved : List Cedar.Spec.Attr) : (xs : List Expr) →
    (Expr.readsContextListB reserved xs = true ↔ Expr.ReadsContextList reserved xs)
  | [] => by simp [Expr.readsContextListB, Expr.ReadsContextList]
  | x :: xs => by
    simp [Expr.readsContextListB, Expr.ReadsContextList, Expr.readsContextB_iff reserved x,
      Expr.readsContextListB_iff reserved xs]

theorem Expr.readsContextRecordB_iff (reserved : List Cedar.Spec.Attr) :
    (axs : List (Cedar.Spec.Attr × Expr)) →
      (Expr.readsContextRecordB reserved axs = true ↔ Expr.ReadsContextRecord reserved axs)
  | [] => by simp [Expr.readsContextRecordB, Expr.ReadsContextRecord]
  | (_, x) :: axs => by
    simp [Expr.readsContextRecordB, Expr.ReadsContextRecord, Expr.readsContextB_iff reserved x,
      Expr.readsContextRecordB_iff reserved axs]

end

theorem argsMatchDeclB_iff (args : List Provider.Arg) (tys : List Cedar.Validation.CedarType) :
    Provider.argsMatchDeclB args tys = true ↔ Provider.argsMatchDecl args tys := by
  simp [Provider.argsMatchDeclB, Provider.argsMatchDecl, List.all_eq_true]

theorem chainsB_iff (sig : Provider.Signature) : (s : Cedar.Validation.CedarType) →
    (ms : List Provider.MethodCall) → (sig.chainsB s ms = true ↔ sig.Chains s ms)
  | _, [] => by simp [Provider.Signature.chainsB, Provider.Signature.Chains]
  | s, m :: ms => by
    unfold Provider.Signature.chainsB Provider.Signature.Chains
    cases sig.methods.find? (·.name == m.name) with
    | none => simp
    | some msig =>
      simp only [Bool.and_eq_true, Bool.or_eq_true, Option.isNone_iff_eq_none, beq_iff_eq,
        chainsB_iff sig msig.output ms]

theorem declaredB_iff (D : Provider.Declarations) (c : Provider.Call) :
    c.declaredB D = true ↔ c.Declared D := by
  unfold Provider.Call.declaredB Provider.Call.Declared
  cases h : D.find? c.function with
  | none => simp
  | some sig =>
    simp only [Bool.and_eq_true, argsMatchDeclB_iff, List.all_eq_true, List.any_eq_true,
      beq_iff_eq, Option.some.injEq, exists_eq_left', chainsB_iff, and_assoc]

theorem argsTypedInB_iff (C : TypingCtx) (args : List Provider.Arg)
    (tys : List Cedar.Validation.CedarType) :
    Provider.argsTypedInB C args tys = true ↔ Provider.ArgsTypedIn C args tys := by
  simp [Provider.argsTypedInB, Provider.ArgsTypedIn, List.all_eq_true]

theorem typedInB_iff (C : TypingCtx) (D : Provider.Declarations) (c : Provider.Call) :
    c.typedInB C D = true ↔ c.TypedIn C D := by
  unfold Provider.Call.typedInB Provider.Call.TypedIn
  cases h : D.find? c.function with
  | none => simp
  | some sig =>
    simp only [Bool.and_eq_true, argsTypedInB_iff, List.all_eq_true, List.any_eq_true,
      beq_iff_eq, Option.some.injEq, exists_eq_left']

theorem leafFindings_eq_nil_iff (P : PolicySet) (p : Policy) (F : List Guard) (φ : Formula) :
    P.leafFindings p F φ = [] ↔ P.LeafValid p F φ := by
  simp only [PolicySet.leafFindings, List.append_eq_nil_iff, List.flatMap_eq_nil_iff,
    Formula.check_eq_nil_iff]
  constructor
  · rintro ⟨⟨h₁, h₂⟩, h₃⟩
    refine ⟨h₁, (isSafeB_iff φ).mp ?_, (monitorsTimeB_iff φ).mp ?_⟩
    · split at h₂ <;> simp_all
    · split at h₃ <;> simp_all
  · rintro ⟨h₁, h₂, h₃⟩
    refine ⟨⟨h₁, ?_⟩, ?_⟩
    · rw [if_pos ((isSafeB_iff φ).mpr h₂)]
    · rw [if_pos ((monitorsTimeB_iff φ).mpr h₃)]

theorem ruleFindings_eq_nil_iff (P : PolicySet) (p : Policy) :
    P.ruleFindings p = [] ↔
      (∀ φ F, (.inl φ, F) ∈ p.toExpr.leafFacts [] → P.LeafValid p F φ) ∧
      (∀ c F, (.inr c, F) ∈ p.toExpr.leafFacts [] → c.Declared P.providerDecls ∧
        ∀ env ∈ P.envsOf p, c.TypedIn (P.typingCtx env F) P.providerDecls) := by
  simp only [PolicySet.ruleFindings, List.flatMap_eq_nil_iff]
  constructor
  · intro h
    refine ⟨fun φ F hm => (leafFindings_eq_nil_iff P p F φ).mp (h _ hm), fun c F hm => ?_⟩
    have := h _ hm
    simp only at this
    split at this
    · rename_i hd
      simp only [Bool.and_eq_true, List.all_eq_true] at hd
      exact ⟨(declaredB_iff _ _).mp hd.1, fun env henv => (typedInB_iff _ _ _).mp (hd.2 env henv)⟩
    · cases this
  · rintro ⟨h₁, h₂⟩ ⟨l, F⟩ hm
    cases l with
    | inl φ => exact (leafFindings_eq_nil_iff P p F φ).mpr (h₁ φ F hm)
    | inr c =>
      simp only
      rw [if_pos]
      simp only [Bool.and_eq_true, List.all_eq_true]
      exact ⟨(declaredB_iff _ _).mpr (h₂ c F hm).1,
        fun env henv => (typedInB_iff _ _ _).mpr ((h₂ c F hm).2 env henv)⟩

/-- **The validity check decides validity.** -/
theorem validationFindings_eq_nil_iff (P : PolicySet) :
    P.validationFindings = [] ↔ P.Valid := by
  simp only [PolicySet.validationFindings, List.append_eq_nil_iff, List.flatMap_eq_nil_iff,
    ruleFindings_eq_nil_iff]
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨⟨⟨h₁, h₂⟩, h₃⟩, h₄w⟩, h₄s⟩, h₄i⟩, h₄⟩, h₅⟩, h₆⟩
    have hH : ∀ H, P.maxHorizon = some H → ∀ φ ∈ P.temporalLeaves, φ.horizon .seconds ≤ H := by
      intro H hm
      rw [hm] at h₆
      simp only at h₆
      split at h₆
      · rename_i hall
        simpa [List.all_eq_true] using hall
      · cases h₆
    have hT : P.hoistedTypes?.isSome = true := by split at h₁ <;> simp_all
    have hN : P.hoistedNames.Nodup ∧ P.namesFreshB = true := by split at h₂ <;> simp_all
    have hR : P.leafList.isEmpty || P.policies.all (·.toExpr.readsContextB P.hoistedNames) =
        true := by
      split at h₃ <;> simp_all
    have hW : P.augmentedSchema.validateWellFormed = .ok () := by
      split at h₄w
      · assumption
      · cases h₄w
    have hS : P.augmentedSchema.standardAncestors = true := by
      split at h₄s
      · assumption
      · cases h₄s
    have hI : P.policies ≠ [] → P.externalTypes = [] ∧ P.externalActions = [] := by
      intro hp
      have : (P.policies.isEmpty || (P.externalTypes.isEmpty && P.externalActions.isEmpty)) =
          true := by
        split at h₄i
        · assumption
        · cases h₄i
      simpa [List.isEmpty_iff, hp] using this
    have hC : Cedar.Validation.validate P.lowered P.augmentedSchema = .ok () := by
      rw [if_pos hT] at h₄
      split at h₄
      · assumption
      · cases h₄
    have hR' : P.leafList ≠ [] → ∀ p ∈ P.policies, p.toExpr.ReadsContext P.hoistedNames := by
      intro hL
      have : P.policies.all (·.toExpr.readsContextB P.hoistedNames) = true := by
        simpa [List.isEmpty_iff, hL] using hR
      simpa [List.all_eq_true, Expr.readsContextB_iff] using this
    refine ⟨hT, hN.1, ?_, hR', hW, hS, hI, hC, fun p hp => (h₅ p hp).1, fun p hp => (h₅ p hp).2,
      hH⟩
    have hF := hN.2
    simp only [PolicySet.namesFreshB, List.all_eq_true, Option.isNone_iff_eq_none] at hF
    exact fun act hact a ha => hF act hact a ha
  · intro hv
    refine ⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩,
      fun p hp => ⟨hv.temporal p hp, hv.providers p hp⟩⟩, ?_⟩
    · rw [if_pos hv.leafTypes]
    · rw [if_pos ⟨hv.namesNodup, by
        simp only [PolicySet.namesFreshB, List.all_eq_true, Option.isNone_iff_eq_none]
        exact fun act hact a ha => hv.namesFresh act hact a ha⟩]
    · rw [if_pos]
      by_cases hL : P.leafList = []
      · simp [hL]
      · simpa [List.all_eq_true, Expr.readsContextB_iff, List.isEmpty_iff, hL] using
          hv.readsContext hL
    · rw [hv.wellFormed]
    · rw [if_pos hv.standardAncestors]
    · rw [if_pos]
      by_cases hp : P.policies = []
      · simp [hp]
      · obtain ⟨h₁, h₂⟩ := hv.complete hp
        simp [h₁, h₂]
    · rw [if_pos hv.leafTypes, hv.cedar]
    · cases hm : P.maxHorizon with
      | none => rfl
      | some H =>
        simp only
        rw [if_pos (by simpa [List.all_eq_true] using hv.horizon H hm)]

instance (P : PolicySet) : Decidable P.Valid :=
  decidable_of_iff _ (validationFindings_eq_nil_iff P)

end Dogwood.Thm
