import Dogwood.Eval.Decision
import Dogwood.Spec.Validity
import Dogwood.Thm.Monitorable
import Dogwood.Thm.Temporal
import Dogwood.Thm.Valuation
import Dogwood.Thm.Leaves
import Dogwood.Thm.Implementation
import Dogwood.Thm.Injection
import Dogwood.Thm.Facts

/-!
# The evaluator decides the semantics

`eval_iff`: for a safe condition, the evaluator returns `true` exactly when the condition holds,
at every timepoint up to the candidates' bound `J`, under every valuation. `denote_iff` and
`total_iff` state the same for operands and aggregates.

The proof follows the monitorability theorems. An `exists` holds exactly when one of its
candidates witnesses it (`sat_exist_iff`), and the rows that satisfy an aggregate's body are
drawn from its candidates (`rows_mem_product`), so searching the candidates loses nothing.
-/

namespace Dogwood.Thm

open Dogwood.Spec Dogwood.Spec.Temporal Dogwood.Eval
open Cedar.Spec (Value)

/-! ## The Boolean checks -/

theorem holds_iff (op : CmpOp) (a b : CVal) : CmpOp.holds op a b = true ↔ op.Holds a b := by
  cases op <;> cases a <;> cases b <;> simp [CmpOp.holds, CmpOp.Holds]

theorem matchesB_iff (e : Event) (v : Valuation) (t : Term) (w : Value) :
    matchesB e v t w = true ↔ t.Matches e v w := by
  cases t <;> simp [matchesB, Term.Matches]

theorem argsMatchB_iff (e : Event) (v : Valuation) (ev : Event) (args : List (Path × Term)) :
    argsMatchB e v ev args = true ↔ ArgsMatch e v ev args := by
  simp only [argsMatchB, ArgsMatch, List.all_eq_true]
  refine forall_congr' fun a => imp_congr_right fun _ => ?_
  cases h : recordPath? ev.logged a.1 with
  | none => simp
  | some w => simp [matchesB_iff]

theorem inWindowB_iff {rate : TickRate} (σ : Trace) (j k : Nat) (w : Window) :
    inWindowB rate σ j k w = true ↔ InWindow rate σ j k w := by
  unfold inWindowB InWindow
  cases hj : σ[j]? <;> cases hk : σ[k]? <;> simp

/-! ## Deduplicated candidates -/

theorem uniq_go_spec {α : Type} [BEq α] [LawfulBEq α] :
    ∀ (xs acc : List α), acc.Nodup →
      (uniq.go xs acc).Nodup ∧ ∀ y, y ∈ uniq.go xs acc ↔ y ∈ acc ∨ y ∈ xs
  | [], acc, h => ⟨List.pairwise_reverse.mpr (h.imp Ne.symm), fun y => by simp [uniq.go]⟩
  | x :: xs, acc, h => by
    by_cases hx : x ∈ acc
    · have hc : acc.contains x = true := List.contains_iff_mem.mpr hx
      simp only [uniq.go, hc, if_true]
      obtain ⟨h1, h2⟩ := uniq_go_spec xs acc h
      refine ⟨h1, fun y => ?_⟩
      rw [h2]
      constructor
      · rintro (h | h)
        · exact .inl h
        · exact .inr (List.mem_cons_of_mem _ h)
      · rintro (h | h)
        · exact .inl h
        · rcases List.mem_cons.mp h with rfl | h
          · exact .inl hx
          · exact .inr h
    · have hc : acc.contains x = false := by
        cases h' : acc.contains x
        · rfl
        · exact absurd (List.contains_iff_mem.mp h') hx
      simp only [uniq.go, hc, Bool.false_eq_true, if_false]
      obtain ⟨h1, h2⟩ := uniq_go_spec xs (x :: acc) (List.nodup_cons.mpr ⟨hx, h⟩)
      refine ⟨h1, fun y => ?_⟩
      rw [h2]
      simp only [List.mem_cons]
      constructor
      · rintro ((h | h) | h)
        · exact .inr (.inl h)
        · exact .inl h
        · exact .inr (.inr h)
      · rintro (h | h | h)
        · exact .inl (.inr h)
        · exact .inl (.inl h)
        · exact .inr h

theorem mem_uniq {α : Type} [BEq α] [LawfulBEq α] {x : α} {xs : List α} : x ∈ uniq xs ↔ x ∈ xs := by
  simp [uniq, (uniq_go_spec xs [] List.nodup_nil).2]

theorem nodup_uniq {α : Type} [BEq α] [LawfulBEq α] (xs : List α) : (uniq xs).Nodup :=
  (uniq_go_spec xs [] List.nodup_nil).1

theorem nodup_flatMap_cons {α : Type} {P : List (List α)} (hP : P.Nodup) :
    ∀ {zs : List α}, zs.Nodup → (zs.flatMap fun x => P.map (x :: ·)).Nodup
  | [], _ => List.nodup_nil
  | x :: zs, h => by
    obtain ⟨hx, hzs⟩ := List.nodup_cons.mp h
    rw [List.flatMap_cons, List.nodup_append]
    refine ⟨hP.map _ fun _ _ hne h => hne (List.cons.inj h).2, nodup_flatMap_cons hP hzs, ?_⟩
    intro a ha b hb hab
    obtain ⟨p, _, rfl⟩ := List.mem_map.mp ha
    obtain ⟨y, hy, hb⟩ := List.mem_flatMap.mp hb
    obtain ⟨q, _, rfl⟩ := List.mem_map.mp hb
    exact hx ((List.cons.inj hab).1 ▸ hy)

theorem nodup_product {α : Type} {xs : List α} (h : xs.Nodup) : ∀ m, (product xs m).Nodup
  | 0 => by simp [product]
  | m + 1 => by
    simp only [product]
    exact nodup_flatMap_cons (nodup_product h m) h

theorem mem_product_uniq {α : Type} [BEq α] [LawfulBEq α] {xs : List α} {m : Nat} {row : List α} :
    row ∈ product (uniq xs) m ↔ row ∈ product xs m := by
  simp [mem_product, mem_uniq]

/-! ## Operands denote at most one value -/

section

variable {ι : ImplChoices} {rate : TickRate} {σ : Trace} {e : Event} {vis : Nat → Prop}

theorem denotes_unique : (t : Term) → ∀ {v : Valuation} {j : Nat} {c c' : CVal},
    Denotes ι rate σ e vis v j t c → Denotes ι rate σ e vis v j t c' → c = c'
  | .agg a, v, j, c, c', h, h' => by
    simp only [Denotes] at h h'
    obtain ⟨n, hn, hc⟩ := h
    obtain ⟨n', hn', hc'⟩ := h'
    rw [total_unique hn hn', hc'] at hc
    exact (Option.some.inj hc).symm
  | .arith op l r, v, j, c, c', h, h' => by
    simp only [Denotes] at h h'
    obtain ⟨m, n, hl, hr, hc⟩ := h
    obtain ⟨m', n', hl', hr', hc'⟩ := h'
    have hm := denotes_unique l hl hl'
    have hn := denotes_unique r hr hr'
    simp only [CVal.num.injEq] at hm hn
    subst hm hn
    rw [hc'] at hc
    exact (Option.some.inj hc).symm
  | .entity _, _, _, _, _, h, h' | .long _, _, _, _, _, h, h' | .decimal _, _, _, _, _, h, h'
  | .string _, _, _, _, _, h, h' | .bool _, _, _, _, _, h, h' | .context _, _, _, _, _, h, h'
  | .scope _ _, _, _, _, _, h, h' | .var _, _, _, _, _, h, h' | .wildcard, _, _, _, _, h, h' => by
    simp only [Denotes] at h h'
    obtain ⟨w, hw, rfl⟩ := h
    obtain ⟨w', hw', rfl⟩ := h'
    rw [hw] at hw'
    cases hw'
    rfl

end

/-! ## Binding equalities -/

/-- What a binding equality found by `bindingValue?` gives: its value side is safe, does not
mention `x`, and wherever the condition holds, denotes `x`'s value. -/
theorem bindingValue?_spec {x : VarName} : {φ : Formula} → {t : Term} →
    bindingValue? x φ = some t → ∀ {R : VarName → Prop}, φ.Safe R →
      t.Safe (fun _ => True) ∧ x ∉ t.fv ∧
      ∀ {ι : ImplChoices} {rate : TickRate} {σ : Trace} {e : Event} {vis : Nat → Prop} {v : Valuation} {j : Nat},
        Sat ι rate σ e vis v j φ →
          ∃ c, Denotes ι rate σ e vis v j t c ∧ ∃ w, v x = some w ∧ c = CVal.ofTVal w
  | .and φ ψ, t, h, R, hs => by
    simp only [bindingValue?] at h
    split at h
    · rename_i r hr
      cases h
      obtain ⟨h1, h2, h3⟩ := bindingValue?_spec hr hs.1
      exact ⟨h1, h2, fun hs => h3 hs.1⟩
    · obtain ⟨h1, h2, h3⟩ := bindingValue?_spec h hs.2
      exact ⟨h1, h2, fun hs => h3 hs.2⟩
  | .cmp op l r, t, h, R, hs => by
    cases op <;> simp only [bindingValue?] at h
    all_goals try (cases h; done)
    split at h
    · rename_i hcond
      simp only [Option.some.injEq] at h
      subst h
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hcond
      obtain ⟨heq, hfv⟩ := hcond
      have hnot : x ∉ (valueSide x l r).fv := fun hm => by
        rw [List.contains_iff_mem.mpr hm] at hfv; cases hfv
      obtain ⟨_, hsl, hsr⟩ := hs
      rcases valueSide_of_eq heq with ⟨hl, hv⟩ | ⟨hr, hv⟩
      · rw [hv] at hnot ⊢
        refine ⟨Term.safe_mono r (fun _ _ => trivial) hsr, hnot, fun {ι rate σ e vis v j} hs => ?_⟩
        obtain ⟨a, b, ha, hb, hab⟩ := hs
        subst hl
        simp only [CmpOp.Holds] at hab
        subst hab
        obtain ⟨w, hw, rfl⟩ := denotes_var ha
        exact ⟨_, hb, w, hw, rfl⟩
      · rw [hv] at hnot ⊢
        refine ⟨Term.safe_mono l (fun _ _ => trivial) hsl, hnot, fun {ι rate σ e vis v j} hs => ?_⟩
        obtain ⟨a, b, ha, hb, hab⟩ := hs
        subst hr
        simp only [CmpOp.Holds] at hab
        subst hab
        obtain ⟨w, hw, rfl⟩ := denotes_var hb
        exact ⟨_, ha, w, hw, rfl⟩
    · cases h
  | .exist y φ, t, h, R, hs => by
    simp only [bindingValue?] at h
    split at h
    · cases h
    · rename_i hyx
      split at h
      · rename_i t' hb
        split at h
        · cases h
        · rename_i hy
          cases h
          obtain ⟨h1, h2, h3⟩ := bindingValue?_spec hb hs.2
          refine ⟨h1, h2, fun {ι rate σ e vis v j} hsat => ?_⟩
          obtain ⟨w', hw'⟩ := hsat
          obtain ⟨c, hc, w, hw, rfl⟩ := h3 hw'
          refine ⟨_, (denotes_congr_val _ v (v.bind y.name w') j ?_ _).mpr hc, w, ?_, rfl⟩
          · intro z hz
            have hzy : z ≠ y.name := fun hzy => by
              subst hzy
              exact hy (List.contains_iff_mem.mpr hz)
            simp [Valuation.bind, hzy]
          · have hxy : x ≠ y.name := fun hxy => hyx (by simp [hxy])
            simpa [Valuation.bind, hxy] using hw
      · cases h
  | .not _, _, h, _, _ | .formerly _ _, _, h, _, _ | .previous _ _, _, h, _, _
  | .since _ _ _, _, h, _, _ | .pred _ _ _, _, h, _, _
  | .tp _, _, h, _, _ => by simp [bindingValue?] at h

/-! ## Correctness -/

section

variable (ι : ImplChoices) (rate : TickRate) (σ : Trace) (e : Event) (vis : Nat → Prop) (visB : Nat → Bool)
  (hvis : ∀ k, visB k = true ↔ vis k) (J : Nat)

include hvis

set_option linter.unusedSectionVars false

theorem visB_false_iff (k : Nat) : visB k = false ↔ ¬ vis k := by
  rw [← hvis]; simp

mutual

/-- **The evaluator decides `Sat`** on safe conditions. -/
theorem eval_iff : (φ : Formula) → φ.Safe (fun _ => True) → ∀ (v : Valuation) (j : Nat), j ≤ J →
    (eval ι rate σ e visB J v j φ = true ↔ Sat ι rate σ e vis v j φ)
  | .and φ ψ, hs, v, j, hj => by
    have h₁ := Formula.safe_mono φ (fun _ _ => trivial) hs.1
    have h₂ := Formula.safe_mono ψ (fun _ _ => trivial) hs.2
    simp only [eval, Sat, Bool.and_eq_true]
    rw [eval_iff φ h₁ v j hj, eval_iff ψ h₂ v j hj]
  | .not φ, hs, v, j, hj => by
    simp only [eval, Sat]
    rw [← eval_iff φ hs.2 v j hj]
    cases eval ι rate σ e visB J v j φ <;> simp
  | .formerly w φ, hs, v, j, hj => by
    simp only [eval, Sat, List.any_eq_true, List.mem_range, Bool.and_eq_true, hvis, inWindowB_iff]
    constructor
    · rintro ⟨k, hk, ⟨hv, hw⟩, he⟩
      exact ⟨k, by omega, hv, hw, (eval_iff φ hs v k (by omega)).mp he⟩
    · rintro ⟨k, hk, hv, hw, hs'⟩
      exact ⟨k, by omega, ⟨hv, hw⟩, (eval_iff φ hs v k (by omega)).mpr hs'⟩
  | .previous w φ, hs, v, j, hj => by
    simp only [eval, Sat, List.any_eq_true, List.all_eq_true, List.mem_range, Bool.and_eq_true,
      Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, hvis, inWindowB_iff,
      visB_false_iff vis visB hvis]
    constructor
    · rintro ⟨k, hk, ⟨⟨hv, hlast⟩, hw⟩, he⟩
      refine ⟨k, hk, hv, fun k' h1 h2 => ?_, hw, (eval_iff φ hs v k (by omega)).mp he⟩
      rcases hlast k' h2 with h | h
      · exact absurd h1 h
      · exact h
    · rintro ⟨k, hk, hv, hlast, hw, hs'⟩
      refine ⟨k, hk, ⟨⟨hv, fun k' h2 => ?_⟩, hw⟩, (eval_iff φ hs v k (by omega)).mpr hs'⟩
      by_cases h1 : k < k'
      · exact .inr (hlast k' h1 h2)
      · exact .inl h1
  | .since φ w ψ, hs, v, j, hj => by
    have hφ := Formula.safe_mono φ (fun _ _ => trivial) hs.2.2
    simp only [eval, Sat, List.any_eq_true, List.all_eq_true, List.mem_range, Bool.and_eq_true,
      Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, hvis, inWindowB_iff,
      visB_false_iff vis visB hvis]
    constructor
    · rintro ⟨k, hk, ⟨⟨hv, hw⟩, hs'⟩, hall⟩
      refine ⟨k, by omega, hv, hw, (eval_iff ψ hs.1 v k (by omega)).mp hs',
        fun k' h1 h2 hv' => ?_⟩
      rcases hall k' (by omega) with (h | h) | h
      · exact absurd h1 h
      · exact absurd hv' h
      · exact (eval_iff φ hφ v k' (by omega)).mp h
    · rintro ⟨k, hk, hv, hw, hs', hall⟩
      refine ⟨k, by omega, ⟨⟨hv, hw⟩, (eval_iff ψ hs.1 v k (by omega)).mpr hs'⟩, fun k' h2 => ?_⟩
      by_cases h1 : k < k'
      · by_cases hv' : vis k'
        · exact .inr ((eval_iff φ hφ v k' (by omega)).mpr (hall k' h1 (by omega) hv'))
        · exact .inl (.inr hv')
      · exact .inl (.inl h1)
  | .pred a kd args, _, v, j, _ => by
    simp only [eval, Sat]
    cases hσ : σ[j]? with
    | none => simp
    | some p => simp [argsMatchB_iff, and_assoc]
  | .cmp op l r, hs, v, j, hj => by
    have ihl := denote_iff l hs.2.1 v j hj
    have ihr := denote_iff r hs.2.2 v j hj
    simp only [eval, Sat]
    cases hl : denote ι rate σ e visB J v j l with
    | none =>
      simp only [Bool.false_eq_true, false_iff, not_exists, not_and]
      intro a b ha; have := (ihl a).mpr ha; rw [hl] at this; cases this
    | some a =>
      cases hr : denote ι rate σ e visB J v j r with
      | none =>
        simp only [Bool.false_eq_true, false_iff, not_exists, not_and]
        intro a' b hb' hb; have := (ihr b).mpr hb; rw [hr] at this; cases this
      | some b =>
        simp only
        rw [holds_iff]
        constructor
        · intro h; exact ⟨a, b, (ihl a).mp hl, (ihr b).mp hr, h⟩
        · rintro ⟨a', b', ha', hb', h⟩
          have e1 := (ihl a').mpr ha'; rw [hl] at e1; cases e1
          have e2 := (ihr b').mpr hb'; rw [hr] at e2; cases e2
          exact h
  | .exist x φ, hs, v, j, hj => by
    have hφ : φ.Safe (fun _ => True) := Formula.safe_mono φ (fun _ _ => trivial) hs.2
    simp only [eval]
    split
    · -- A binding equality fixes the only possible witness: the value its other side denotes.
      rename_i t hb
      obtain ⟨hts, hxt, hsat⟩ := bindingValue?_spec hb hs.2
      have hsz := bindingValue?_sizeOf hb
      have ihT := denote_iff t hts v j hj
      have hwit : ∀ w, Sat ι rate σ e vis (v.bind x.name w) j φ →
          Denotes ι rate σ e vis v j t (CVal.ofTVal w) := by
        intro w hs
        obtain ⟨c, hd, w', hw', rfl⟩ := hsat hs
        simp only [Valuation.bind, if_true, Option.some.injEq] at hw'
        subst hw'
        refine (denotes_congr_val t _ _ j (fun y hy => ?_) _).mp hd
        have hy' : y ≠ x.name := fun h => hxt (h ▸ hy)
        simp [Valuation.bind, hy']
      simp only [Sat]
      cases hd : denote ι rate σ e visB J v j t with
      | none =>
        simp only [Bool.false_eq_true, false_iff, not_exists]
        intro w hs
        have := (ihT _).mpr (hwit w hs); rw [hd] at this; cases this
      | some c =>
        simp only
        rw [eval_iff φ hφ (v.bind x.name c.toTVal) j hj]
        constructor
        · intro hs; exact ⟨_, hs⟩
        · rintro ⟨w, hs⟩
          have := (ihT _).mpr (hwit w hs)
          rw [hd, Option.some.injEq] at this
          subst this
          rw [CVal.toTVal_ofTVal]; exact hs
    · rw [sat_exist_iff hs v hj]
      simp only [List.any_eq_true, mem_uniq]
      constructor
      · rintro ⟨w, hw, he⟩
        exact ⟨w, hw, (eval_iff φ hφ (v.bind x.name w) j hj).mp he⟩
      · rintro ⟨w, hw, hs⟩
        exact ⟨w, hw, (eval_iff φ hφ (v.bind x.name w) j hj).mpr hs⟩
  | .tp x, _, v, j, _ => by simp [eval, Sat]
termination_by φ => sizeOf φ

/-- **The evaluator computes what an operand denotes.** -/
theorem denote_iff : (t : Term) → t.Safe (fun _ => True) → ∀ (v : Valuation) (j : Nat), j ≤ J →
    ∀ (c : CVal), (denote ι rate σ e visB J v j t = some c ↔ Denotes ι rate σ e vis v j t c)
  | .agg a, hs, v, j, hj, c => by
    have ht := total_iff a hs v j hj
    simp only [denote, Denotes]
    constructor
    · intro h; exact ⟨_, ht, h⟩
    · rintro ⟨n, hn', hv⟩; rw [total_unique hn' ht] at hv; exact hv
  | .arith op l r, hs, v, j, hj, c => by
    have ihl := denote_iff l hs.1 v j hj
    have ihr := denote_iff r hs.2 v j hj
    simp only [denote, Denotes]
    constructor
    · intro h
      cases hl : denote ι rate σ e visB J v j l with
      | none => rw [hl] at h; cases h
      | some a =>
        cases hr : denote ι rate σ e visB J v j r with
        | none => rw [hl, hr] at h; cases a <;> cases h
        | some b =>
          rw [hl, hr] at h
          cases a with
          | val _ => cases h
          | tp _ => cases h
          | num m =>
            cases b with
            | val _ => cases h
            | tp _ => cases h
            | num n => exact ⟨m, n, (ihl _).mp hl, (ihr _).mp hr, h⟩
    · rintro ⟨m, n, hl, hr, hv⟩
      rw [(ihl _).mpr hl, (ihr _).mpr hr]
      exact hv
  | .entity _, _, v, _, _, c | .long _, _, v, _, _, c
  | .decimal _, _, v, _, _, c | .string _, _, v, _, _, c
  | .bool _, _, v, _, _, c | .context _, _, v, _, _, c
  | .scope _ _, _, v, _, _, c | .var _, _, v, _, _, c
  | .wildcard, _, v, _, _, c => by
    simp only [denote, Denotes, Option.map_eq_some_iff]
    exact exists_congr fun w => and_congr_right fun _ => eq_comm
termination_by t => sizeOf t

/-- **The evaluator computes an aggregate's total.** -/
theorem total_iff : (a : Aggregate) → a.Safe (fun _ => True) → ∀ (v : Valuation) (j : Nat),
    j ≤ J → Total ι rate σ e vis v j a (total ι rate σ e visB J v j a)
  | .count dom body, hs, v, j, hj => by
    have hb := Formula.safe_mono body (fun _ _ => trivial) hs.2
    refine ⟨_, (nodup_product (nodup_uniq _) _).sublist List.filter_sublist, fun row => ?_,
      by rw [total]⟩
    simp only [List.mem_filter, mem_product_uniq]
    rw [eval_iff body hb _ j hj]
    constructor
    · rintro ⟨hp, hs⟩
      exact ⟨(mem_product.mp hp).1, hs⟩
    · intro h
      exact ⟨rows_mem_product ι rate σ e vis J hs.1 hs.2 (fun y hy => hy) (SeedOk.ofList _ v) hj h,
        h.2⟩
  | .sum s dom body, hs, v, j, hj => by
    have hb := Formula.safe_mono body (fun _ _ => trivial) hs.2
    refine ⟨_, (nodup_product (nodup_uniq _) _).sublist List.filter_sublist, fun row => ?_,
      by rw [total]⟩
    simp only [List.mem_filter, mem_product_uniq]
    rw [eval_iff body hb _ j hj]
    constructor
    · rintro ⟨hp, hs⟩
      exact ⟨(mem_product.mp hp).1, hs⟩
    · intro h
      exact ⟨rows_mem_product ι rate σ e vis J hs.1 hs.2 (fun y hy => hy) (SeedOk.ofList _ v) hj h,
        h.2⟩
termination_by a => sizeOf a

end

end

/-! ## Visibility -/

theorem mineB_iff (S : EventSchema) (e ev : Event) : mineB S e ev = true ↔ S.Mine e ev := by
  simp only [mineB, EventSchema.Mine, Bool.and_eq_true, List.any_eq_true, List.all_eq_true,
    decide_eq_true_eq]
  refine and_congr (by simp) (forall_congr' fun p => imp_congr_right fun _ => ?_)
  cases h₁ : recordPath? ev.logged p.field <;> cases h₂ : p.ref.toTerm.eval? e Valuation.empty <;>
    simp [eq_comm]

theorem visibleB_iff (S : EventSchema) (σ : Trace) (e : Event) (k : Nat) :
    visibleB S σ e k = true ↔ S.Visible σ e k := by
  unfold visibleB EventSchema.Visible
  cases h : σ[k]? <;> simp [mineB_iff]

/-! ## Decisions -/

/-- **A leaf is decided correctly.** For a safe temporal leaf, the evaluator, run after pin
injection, decides whether the leaf holds at the decision. -/
theorem leafHolds_iff {ι : ImplChoices} {P : PolicySet} {σ : Trace} {n : Nat} {φ : Formula}
    (hφ : φ.IsSafe) : Eval.leafHolds ι P σ n φ = true ↔ P.LeafHolds ι σ n φ := by
  have hs : (φ.injectPins P.schema).Safe (fun _ => True) :=
    Formula.IsSafe.safe_top ((Formula.isSafe_injectPins P.schema φ).mpr hφ)
  unfold Eval.leafHolds PolicySet.LeafHolds
  cases hσ : σ[n]? with
  | none => simp
  | some p =>
    simp only [Option.some.injEq, exists_eq_left']
    exact eval_iff ι P.tickRate σ p.event _ _ (visibleB_iff P.schema σ p.event) n _ hs Valuation.empty n
      (Nat.le_refl n)

/-- **The executable decision is the specification's.** Under a total reading, for a policy set
whose temporal leaves are all safe, the evaluator's outcome at every timepoint of every trace is
`PolicySet.authorize`'s. -/
theorem authorize_eq {ι : ImplChoices} {P : PolicySet} {ω : Provider.Providers} (hι : ι.Total)
    (hwf : ∀ φ ∈ P.temporalLeaves, φ.IsSafe) (σ : Trace) (n : Nat) :
    Eval.authorize ι P ω σ n = P.authorize ι ω σ n := by
  unfold Eval.authorize PolicySet.authorize
  refine decideWith_congr rfl fun p pr rs _ _ => ?_
  rw [respond_total hι, Option.some.injEq]
  apply isAuthorized_congr
  intro q hq l hl
  cases l with
  | inl φ =>
    show Eval.leafHolds ι P σ n φ = @decide (P.LeafHolds ι σ n φ) (Classical.propDecidable _)
    rw [Bool.eq_iff_iff]; simp only [decide_eq_true_eq]
    exact leafHolds_iff (hwf φ (mem_temporalLeaves hq hl))
  | inr c => rfl

/-- **Replay is the specification's**, at every timepoint. -/
theorem replay_eq {ι : ImplChoices} {P : PolicySet} {ω : Provider.Providers} (hι : ι.Total)
    (hwf : ∀ φ ∈ P.temporalLeaves, φ.IsSafe) (σ : Trace) :
    Eval.replay ι P ω σ = (List.range σ.length).map (P.authorize ι ω σ) :=
  List.map_congr_left fun n _ => authorize_eq hι hwf σ n

/-- The temporal leaves of a valid policy set are safe. -/
theorem PolicySet.Valid.leaves_safe {P : PolicySet} (hv : P.Valid) :
    ∀ φ ∈ P.temporalLeaves, φ.IsSafe := by
  intro φ hφ
  simp only [PolicySet.temporalLeaves, List.mem_flatMap, List.mem_filterMap] at hφ
  obtain ⟨p, hp, l, hl, hlφ⟩ := hφ
  cases l with
  | inr _ => cases hlφ
  | inl φ' =>
    cases hlφ
    obtain ⟨F, hF⟩ := exists_leafFacts hl []
    exact (hv.temporal p hp φ F hF).safe

end Dogwood.Thm
