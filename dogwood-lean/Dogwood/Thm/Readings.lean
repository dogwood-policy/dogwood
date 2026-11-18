import Dogwood.Spec.Temporal.Readings

/-!
# Readings of out-of-range results

* Widening, clamping, and reporting errors are admissible (`widen_admissible`,
  `clamp_admissible`, `error_admissible`); widening and clamping are total.
* Every reading has a completion (`exists_completes`); a total reading is its own only
  completion (`eq_of_completes_total`), and a completion of an admissible reading is admissible
  (`ImplChoices.Completes.admissible`). The completions of the erroring reading are exactly the total
  admissible readings (`completes_error_iff`).
* **The decision under a reading** (`ImplChoices.supervaluate`): it is the value every
  completion gives (`supervaluate_eq_some_iff`); under a total reading it is the reading's own
  value (`supervaluate_total`); it fails exactly when two completions disagree
  (`supervaluate_eq_none_iff`); and it either fails or equals the value of every completion
  (`supervaluate_dichotomy`).
* **In range, the readings agree** (`sat_readings_agree`): a condition every result of which is
  in range under one reading has the same truth value under every reading.
* **Interior thresholds** (`readLong_interior`, `sat_interior_threshold`): every admissible
  reading that reads an out-of-range total, rather than reporting an error, compares it with a
  threshold strictly inside the range as the exact total compares.
-/

namespace Dogwood.Thm

open Dogwood.Spec Dogwood.Spec.Temporal

/-! ## The readings of the language -/

theorem clampLong_sides (n : Int) :
    (Int64.MAX < n → Int64.MAX ≤ clampLong n) ∧ (n < Int64.MIN → clampLong n ≤ Int64.MIN) := by
  simp only [clampLong, Int64.MIN, Int64.MAX]
  constructor <;> intro h <;> omega

theorem widen_admissible : ImplChoices.widen.Admissible :=
  ⟨fun n m h => by
    simp only [ImplChoices.widen, Option.some.injEq] at h
    subst h
    exact ⟨Int.le_of_lt, Int.le_of_lt⟩,
   fun n m h => by
    simp only [ImplChoices.widen, Option.some.injEq] at h
    subst h
    exact ⟨Int.le_of_lt, Int.le_of_lt⟩⟩

theorem clamp_admissible : ImplChoices.clamp.Admissible :=
  ⟨fun n m h => by simp [ImplChoices.clamp] at h; subst h; exact clampLong_sides n,
   fun n m h => by simp [ImplChoices.clamp] at h; subst h; exact clampLong_sides n⟩

theorem error_admissible : ImplChoices.error.Admissible :=
  ⟨fun _ _ h => (by cases h), fun _ _ h => (by cases h)⟩

theorem widen_total : ImplChoices.widen.Total := ⟨fun _ => rfl, fun _ => rfl⟩

theorem clamp_total : ImplChoices.clamp.Total := ⟨fun _ => rfl, fun _ => rfl⟩

/-! ## Completions -/

/-- `f` with every error read as the clamped result. -/
def fillClamp (f : Int → Option Int) (n : Int) : Option Int :=
  match f n with
  | some m => some m
  | none => some (clampLong n)

theorem fillClamp_completes (f : Int → Option Int) : ReadingCompletes (fillClamp f) f where
  total n := by unfold fillClamp; split <;> rfl
  agrees n m h := by simp [fillClamp, h]
  sides n m h h' := by
    simp only [fillClamp, h, Option.some.injEq] at h'
    subst h'
    exact clampLong_sides n

/-- **Every reading has a completion**: read every result it reports an error for as the
clamped result. -/
theorem exists_completes (ι : ImplChoices) : ∃ ι' : ImplChoices, ι'.Completes ι :=
  ⟨⟨fillClamp ι.outOfRange, fillClamp ι.arithOutOfRange⟩,
   ⟨fillClamp_completes _, fillClamp_completes _⟩⟩

theorem readingCompletes_self {f : Int → Option Int} (h : ∀ n, (f n).isSome = true) :
    ReadingCompletes f f :=
  ⟨h, fun _ _ h => h, fun n _ hn _ => by have := h n; rw [hn] at this; cases this⟩

theorem eq_of_readingCompletes {f f' : Int → Option Int} (h : ∀ n, (f n).isSome = true)
    (hc : ReadingCompletes f' f) : f' = f := by
  funext n
  cases hf : f n with
  | none => have := h n; rw [hf] at this; cases this
  | some m => exact hc.agrees n m hf

/-- A total reading completes itself. -/
theorem completes_self {ι : ImplChoices} (h : ι.Total) : ι.Completes ι :=
  ⟨readingCompletes_self h.aggregate, readingCompletes_self h.arith⟩

/-- **A total reading is its own only completion.** -/
theorem eq_of_completes_total {ι ι' : ImplChoices} (h : ι.Total) (hc : ι'.Completes ι) :
    ι' = ι := by
  have h₁ := eq_of_readingCompletes h.aggregate hc.aggregate
  have h₂ := eq_of_readingCompletes h.arith hc.arith
  cases ι; cases ι'
  simp_all

theorem _root_.Dogwood.Spec.Temporal.ImplChoices.Completes.total {ι ι' : ImplChoices} (hc : ι'.Completes ι) : ι'.Total :=
  ⟨hc.aggregate.total, hc.arith.total⟩

theorem sidePreserving_of_readingCompletes {f f' : Int → Option Int} (hf : SidePreserving f)
    (hc : ReadingCompletes f' f) : SidePreserving f' := by
  intro n m h'
  cases hn : f n with
  | none => exact hc.sides n m hn h'
  | some m' =>
    have := hc.agrees n m' hn
    rw [h', Option.some.injEq] at this
    subst this
    exact hf n m hn

/-- A completion of an admissible reading is admissible. -/
theorem _root_.Dogwood.Spec.Temporal.ImplChoices.Completes.admissible {ι ι' : ImplChoices} (hι : ι.Admissible) (hc : ι'.Completes ι) :
    ι'.Admissible :=
  ⟨sidePreserving_of_readingCompletes hι.aggregate hc.aggregate,
   sidePreserving_of_readingCompletes hι.arith hc.arith⟩

theorem readingCompletes_none_iff {f' : Int → Option Int} :
    ReadingCompletes f' (fun _ => none) ↔ (∀ n, (f' n).isSome = true) ∧ SidePreserving f' :=
  ⟨fun h => ⟨h.total, fun n m h' => h.sides n m rfl h'⟩,
   fun ⟨ht, hs⟩ => ⟨ht, fun _ _ h => (by cases h), fun n m _ h' => hs n m h'⟩⟩

/-- **The completions of the erroring reading are the total admissible readings.** -/
theorem completes_error_iff {ι' : ImplChoices} :
    ι'.Completes .error ↔ ι'.Total ∧ ι'.Admissible := by
  constructor
  · intro h
    obtain ⟨ha₁, ha₂⟩ := readingCompletes_none_iff.mp h.aggregate
    obtain ⟨hr₁, hr₂⟩ := readingCompletes_none_iff.mp h.arith
    exact ⟨⟨ha₁, hr₁⟩, ⟨ha₂, hr₂⟩⟩
  · rintro ⟨ht, hadm⟩
    exact ⟨readingCompletes_none_iff.mpr ⟨ht.aggregate, hadm.aggregate⟩,
      readingCompletes_none_iff.mpr ⟨ht.arith, hadm.arith⟩⟩

/-! ## The decision under a reading -/

section

variable {α : Type} {ι : ImplChoices} {rate : TickRate} {f g : ImplChoices → α}

/-- **The decision under a reading is the value every completion gives.** -/
theorem supervaluate_eq_some_iff {r : α} :
    ι.supervaluate f = some r ↔ ∀ ι', ι'.Completes ι → f ι' = r := by
  unfold ImplChoices.supervaluate
  constructor
  · intro h
    split at h
    · rename_i hex
      rw [Option.some.injEq] at h
      subst h
      exact hex.choose_spec
    · cases h
  · intro h
    have hex : ∃ r, ∀ ι', ι'.Completes ι → f ι' = r := ⟨r, h⟩
    rw [dif_pos hex, Option.some.injEq]
    obtain ⟨ι₀, h₀⟩ := exists_completes ι
    exact (hex.choose_spec ι₀ h₀).symm.trans (h ι₀ h₀)

/-- **The decision under a reading fails exactly when two completions disagree.** -/
theorem supervaluate_eq_none_iff :
    ι.supervaluate f = none ↔ ∃ ι₁ ι₂, ι₁.Completes ι ∧ ι₂.Completes ι ∧ f ι₁ ≠ f ι₂ := by
  unfold ImplChoices.supervaluate
  constructor
  · intro h
    split at h
    · cases h
    · rename_i hex
      obtain ⟨ι₁, h₁⟩ := exists_completes ι
      refine ⟨ι₁, ?_⟩
      apply Classical.byContradiction
      intro hno
      apply hex
      refine ⟨f ι₁, fun ι' h' => ?_⟩
      apply Classical.byContradiction
      intro hne
      exact hno ⟨ι', h₁, h', fun heq => hne heq.symm⟩
  · rintro ⟨ι₁, ι₂, h₁, h₂, hne⟩
    rw [dif_neg]
    rintro ⟨r, hr⟩
    exact hne ((hr ι₁ h₁).trans (hr ι₂ h₂).symm)

/-- **Under a total reading, the decision is the reading's own.** -/
theorem supervaluate_total (h : ι.Total) : ι.supervaluate f = some (f ι) :=
  supervaluate_eq_some_iff.mpr fun _ hc => by rw [eq_of_completes_total h hc]

/-- **The decision under a reading fails, or is the value of every completion.** -/
theorem supervaluate_dichotomy :
    ι.supervaluate f = none ∨ ∀ ι', ι'.Completes ι → ι.supervaluate f = some (f ι') := by
  cases h : ι.supervaluate f with
  | none => exact .inl rfl
  | some r =>
    refine .inr fun ι' hc => ?_
    rw [supervaluate_eq_some_iff.mp h ι' hc]

/-- The decision under a reading depends only on the completions' values. -/
theorem supervaluate_congr (h : ∀ ι', ι'.Completes ι → f ι' = g ι') :
    ι.supervaluate f = ι.supervaluate g := by
  cases hf : ι.supervaluate f with
  | none =>
    obtain ⟨ι₁, ι₂, h₁, h₂, hne⟩ := supervaluate_eq_none_iff.mp hf
    exact (supervaluate_eq_none_iff.mpr ⟨ι₁, ι₂, h₁, h₂, by rw [← h ι₁ h₁, ← h ι₂ h₂]; exact hne⟩).symm
  | some r =>
    have := supervaluate_eq_some_iff.mp hf
    exact (supervaluate_eq_some_iff.mpr fun ι' hc => (h ι' hc).symm.trans (this ι' hc)).symm

/-- A value that does not depend on the reading is decided under every reading. -/
theorem supervaluate_const (r : α) : ι.supervaluate (fun _ => r) = some r :=
  supervaluate_eq_some_iff.mpr fun _ _ => rfl

/-- The decision under a reading maps through a function of the value. -/
theorem supervaluate_map {β : Type} (k : α → β) {r : α} (h : ι.supervaluate f = some r) :
    ι.supervaluate (fun ι' => k (f ι')) = some (k r) :=
  supervaluate_eq_some_iff.mpr fun ι' hc => by rw [supervaluate_eq_some_iff.mp h ι' hc]

end

/-! ## In range, the readings agree -/

theorem readLong_inLong (f : Int → Option Int) {n : Int} (h : InLong n) :
    readLong f n = some (.num n) := by
  simp [readLong, h.1, h.2]

section

variable {σ : Trace} {e : Event} {vis : Nat → Prop}

mutual

/-- **In range, the readings agree.** A condition every result of which is in range under the
reading `ι` has the same truth value under every reading `ι'`. -/
theorem sat_readings_agree {rate : TickRate} (ι ι' : ImplChoices) : (v : Valuation) → (j : Nat) → (φ : Formula) →
    φ.InRange ι rate σ e vis v j → (Sat ι' rate σ e vis v j φ ↔ Sat ι rate σ e vis v j φ)
  | v, j, .and φ ψ, ⟨h₁, h₂⟩ => by
    simp only [Sat, sat_readings_agree ι ι' v j φ h₁, sat_readings_agree ι ι' v j ψ h₂]
  | v, j, .not φ, h => by simp only [Sat, sat_readings_agree ι ι' v j φ h]
  | v, j, .formerly w φ, h => by
    simp only [Sat]
    exact exists_congr fun k => ⟨fun ⟨hk, hv, hw, hs⟩ =>
        ⟨hk, hv, hw, (sat_readings_agree ι ι' v k φ (h k hk)).mp hs⟩,
      fun ⟨hk, hv, hw, hs⟩ => ⟨hk, hv, hw, (sat_readings_agree ι ι' v k φ (h k hk)).mpr hs⟩⟩
  | v, j, .previous w φ, h => by
    simp only [Sat]
    exact exists_congr fun k => ⟨fun ⟨hk, hv, hl, hw, hs⟩ =>
        ⟨hk, hv, hl, hw, (sat_readings_agree ι ι' v k φ (h k hk)).mp hs⟩,
      fun ⟨hk, hv, hl, hw, hs⟩ =>
        ⟨hk, hv, hl, hw, (sat_readings_agree ι ι' v k φ (h k hk)).mpr hs⟩⟩
  | v, j, .since φ w ψ, h => by
    simp only [Sat]
    refine exists_congr fun k => ⟨fun ⟨hk, hv, hw, hs, hall⟩ => ⟨hk, hv, hw,
        (sat_readings_agree ι ι' v k ψ (h k hk).2).mp hs, fun k' h₁ h₂ h₃ =>
          (sat_readings_agree ι ι' v k' φ (h k' h₂).1).mp (hall k' h₁ h₂ h₃)⟩,
      fun ⟨hk, hv, hw, hs, hall⟩ => ⟨hk, hv, hw,
        (sat_readings_agree ι ι' v k ψ (h k hk).2).mpr hs, fun k' h₁ h₂ h₃ =>
          (sat_readings_agree ι ι' v k' φ (h k' h₂).1).mpr (hall k' h₁ h₂ h₃)⟩⟩
  | v, j, .pred _ _ _, _ => by simp only [Sat]
  | v, j, .cmp op l r, ⟨hl, hr⟩ => by
    simp only [Sat]
    exact exists_congr fun a => exists_congr fun b => by
      rw [denotes_readings_agree ι ι' v j l hl a, denotes_readings_agree ι ι' v j r hr b]
  | v, j, .exist x φ, h => by
    simp only [Sat]
    exact exists_congr fun w => sat_readings_agree ι ι' (v.bind x.name w) j φ (h w)
  | v, j, .tp _, _ => by simp only [Sat]

theorem denotes_readings_agree {rate : TickRate} (ι ι' : ImplChoices) : (v : Valuation) → (j : Nat) → (t : Term) →
    t.InRange ι rate σ e vis v j → ∀ c, (Denotes ι' rate σ e vis v j t c ↔ Denotes ι rate σ e vis v j t c)
  | v, j, .agg a, ⟨ha, hn⟩, c => by
    simp only [Denotes]
    refine exists_congr fun n => ?_
    rw [total_readings_agree ι ι' v j a ha n]
    constructor
    · rintro ⟨ht, hc⟩
      refine ⟨ht, ?_⟩
      rw [ImplChoices.aggregateValue, readLong_inLong _ (hn n ht)] at hc ⊢
      exact hc
    · rintro ⟨ht, hc⟩
      refine ⟨ht, ?_⟩
      rw [ImplChoices.aggregateValue, readLong_inLong _ (hn n ht)] at hc ⊢
      exact hc
  | v, j, .arith op l r, ⟨hl, hr, hn⟩, c => by
    simp only [Denotes]
    refine exists_congr fun m => exists_congr fun n => ?_
    rw [denotes_readings_agree ι ι' v j l hl, denotes_readings_agree ι ι' v j r hr]
    constructor
    · rintro ⟨h₁, h₂, hc⟩
      refine ⟨h₁, h₂, ?_⟩
      rw [ImplChoices.arithValue, readLong_inLong _ (hn m n h₁ h₂)] at hc ⊢
      exact hc
    · rintro ⟨h₁, h₂, hc⟩
      refine ⟨h₁, h₂, ?_⟩
      rw [ImplChoices.arithValue, readLong_inLong _ (hn m n h₁ h₂)] at hc ⊢
      exact hc
  | _, _, .entity _, _, _ | _, _, .long _, _, _ | _, _, .decimal _, _, _
  | _, _, .string _, _, _ | _, _, .bool _, _, _ | _, _, .context _, _, _
  | _, _, .scope _ _, _, _ | _, _, .var _, _, _ | _, _, .wildcard, _, _ => by
    simp only [Denotes]

theorem total_readings_agree {rate : TickRate} (ι ι' : ImplChoices) : (v : Valuation) → (j : Nat) →
    (a : Aggregate) → a.InRange ι rate σ e vis v j → ∀ n,
      (Total ι' rate σ e vis v j a n ↔ Total ι rate σ e vis v j a n)
  | v, j, .count dom body, h, n => by
    simp only [Total]
    refine exists_congr fun rows => and_congr_right fun _ => and_congr_left fun _ => ?_
    refine forall_congr' fun row => ?_
    rw [sat_readings_agree ι ι' (v.bindAll (domainNames dom) row) j body (h row)]
  | v, j, .sum s dom body, h, n => by
    simp only [Total]
    refine exists_congr fun rows => and_congr_right fun _ => and_congr_left fun _ => ?_
    refine forall_congr' fun row => ?_
    rw [sat_readings_agree ι ι' (v.bindAll (domainNames dom) row) j body (h row)]

end

end

/-! ## Interior thresholds -/

/-- **An interior threshold is compared alike under every admissible reading.** An exact
result `n`, read by a side-preserving reading as `m`, compares with a threshold `c` strictly
inside the range as `n` itself does. -/
theorem readLong_interior {f : Int → Option Int} (hf : SidePreserving f) {n : Int} {m : Int}
    (hm : readLong f n = some (.num m)) {c : Int} (hc₁ : Int64.MIN < c) (hc₂ : c < Int64.MAX)
    (op : CmpOp) :
    op.Holds (.num m) (.num c) ↔ op.Holds (.num n) (.num c) := by
  unfold readLong at hm
  split at hm
  · simp only [Option.some.injEq, CVal.num.injEq] at hm
    subst hm
    exact Iff.rfl
  · rename_i hn
    simp only [Option.map_eq_some_iff, CVal.num.injEq] at hm
    obtain ⟨m', hm', rfl⟩ := hm
    have hs := hf n m' hm'
    simp only [Int64.MIN, Int64.MAX] at hs hn hc₁ hc₂ ⊢
    have hcases : 9223372036854775807 < n ∨ n < -9223372036854775808 := by omega
    rcases hcases with h | h
    · have := hs.1 h
      cases op <;> simp only [CmpOp.Holds, ne_eq, CVal.num.injEq] <;> omega
    · have := hs.2 h
      cases op <;> simp only [CmpOp.Holds, ne_eq, CVal.num.injEq] <;> omega

/-- **An aggregate compared with an interior threshold is read alike by every admissible total
reading**, when its body's results are in range: two admissible total readings agree on whether
`a op c` holds, for a threshold `c` strictly inside the `Long` range. -/
theorem sat_interior_threshold {rate : TickRate} {σ : Trace} {e : Event} {vis : Nat → Prop} {ι₁ ι₂ : ImplChoices}
    (h₁ : ι₁.Admissible) (h₂ : ι₂.Admissible) (ht₁ : ι₁.Total) (ht₂ : ι₂.Total)
    {v : Valuation} {j : Nat} {a : Aggregate} (ha : a.InRange ι₁ rate σ e vis v j)
    {c : Int64} (hc₁ : Int64.MIN < c.toInt) (hc₂ : c.toInt < Int64.MAX) (op : CmpOp) :
    Sat ι₁ rate σ e vis v j (.cmp op (.agg a) (.long c)) ↔
      Sat ι₂ rate σ e vis v j (.cmp op (.agg a) (.long c)) := by
  have key : ∀ (ι : ImplChoices), ι.Admissible → ι.Total →
      (Sat ι rate σ e vis v j (.cmp op (.agg a) (.long c)) ↔
        ∃ n, Total ι₁ rate σ e vis v j a n ∧ op.Holds (.num n) (.num c.toInt)) := by
    intro ι hadm htot
    simp only [Sat, Denotes, Term.eval?, Option.some.injEq]
    constructor
    · rintro ⟨x, y, ⟨n, hn, hx⟩, ⟨w, rfl, rfl⟩, hop⟩
      have hn₁ := (total_readings_agree ι₁ ι v j a ha n).mp hn
      unfold ImplChoices.aggregateValue at hx
      have hx' : ∃ m, x = .num m ∧ readLong ι.outOfRange n = some (.num m) := by
        unfold readLong at hx ⊢
        split at hx
        · simp only [Option.some.injEq] at hx
          exact ⟨n, hx.symm, by simp_all⟩
        · simp only [Option.map_eq_some_iff] at hx
          obtain ⟨m, hm, rfl⟩ := hx
          rename_i hr
          exact ⟨m, rfl, by simp [hr, hm]⟩
      obtain ⟨m, rfl, hm⟩ := hx'
      refine ⟨n, hn₁, ?_⟩
      simp only [CVal.ofTVal, CVal.ofValue] at hop
      exact (readLong_interior hadm.aggregate hm hc₁ hc₂ op).mp hop
    · rintro ⟨n, hn, hop⟩
      have hn' := (total_readings_agree ι₁ ι v j a ha n).mpr hn
      have hsome := htot.aggregate n
      cases hf : ι.outOfRange n with
      | none => rw [hf] at hsome; cases hsome
      | some m' =>
        have hm : ∃ m, readLong ι.outOfRange n = some (.num m) := by
          unfold readLong
          split
          · exact ⟨n, rfl⟩
          · exact ⟨m', by simp [hf]⟩
        obtain ⟨m, hm⟩ := hm
        refine ⟨.num m, .num c.toInt, ⟨n, hn', hm⟩, ⟨.val (.prim (.int c)), rfl, rfl⟩, ?_⟩
        exact (readLong_interior hadm.aggregate hm hc₁ hc₂ op).mpr hop
  rw [key ι₁ h₁ ht₁, key ι₂ h₂ ht₂]

end Dogwood.Thm
