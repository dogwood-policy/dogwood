import Dogwood.Spec.Temporal.Horizon
import Dogwood.Spec.Temporal.Semantics
import Dogwood.Thm.Renumber

/-!
# Satisfaction over a subsequence of the trace

An implementation that partitions or prunes its history evaluates a condition over a
subsequence of the trace: the events of one partition, in order, with their original
timestamps, or the events it has not pruned. `sat_subseq` states that satisfaction at a
timepoint of the subsequence is satisfaction at the corresponding timepoint of the whole trace,
when the visible timepoints of the trace are exactly the images of the visible timepoints of the
subsequence, and the valuation's timepoints are renumbered alike. `sat_slice` is the case where
every timepoint of the subsequence is visible, so that exactly the subsequence is visible in the
trace. It is the specification's key-local reading (`EventSchema.Visible`), realized by storing
only the visible events.

A condition observes a timepoint's index only through equality (`tp`, and equality of two
timepoints), so a renumbering of the timepoints by a bijection changes nothing
(`Dogwood.Thm.Renumber`). The subsequence renumbers its timepoints by an injection, which
`exists_renumbering` extends to a bijection. So the lemmas hold of every condition, `tp`
included.

`subTrace_filter` shows that the events of a prefix of the trace that satisfy a predicate form
such a subsequence, so that `sat_slice` applies to a partition's events.
-/

namespace Dogwood.Thm

open Dogwood.Spec Dogwood.Spec.Temporal

/-! ## Subsequences -/

/-- `σ'` is the subsequence of `σ` at the indices `f 0 < f 1 < …`, and the timepoints `vis`
marks in `σ` are exactly the images of the timepoints `vis'` marks in `σ'`. -/
structure Subsequence (σ σ' : Trace) (f : Nat → Nat) (vis' vis : Nat → Prop) : Prop where
  get : ∀ i < σ'.length, σ'[i]? = σ[f i]?
  mono : ∀ i j, i < j → j < σ'.length → f i < f j
  vis_iff : ∀ K, vis K ↔ ∃ i < σ'.length, f i = K ∧ vis' i

/-- `σ'` is the subsequence of `σ` at the indices `f 0 < f 1 < …`, and `vis` holds of exactly
those indices. -/
structure SubTrace (σ σ' : Trace) (f : Nat → Nat) (vis : Nat → Prop) : Prop where
  get : ∀ i < σ'.length, σ'[i]? = σ[f i]?
  mono : ∀ i j, i < j → j < σ'.length → f i < f j
  vis_iff : ∀ K, vis K ↔ ∃ i < σ'.length, f i = K

namespace Subsequence

variable {σ σ' : Trace} {f : Nat → Nat} {vis' vis : Nat → Prop}

theorem lt_iff (h : Subsequence σ σ' f vis' vis) {i j : Nat} (hi : i < σ'.length)
    (hj : j < σ'.length) : f i < f j ↔ i < j := by
  constructor
  · intro hf
    by_contra hij
    rcases Nat.lt_or_ge j i with h' | h'
    · have := h.mono j i h' hi; omega
    · have : i = j := by omega
      subst this; omega
  · intro hij; exact h.mono i j hij hj

theorem le_iff (h : Subsequence σ σ' f vis' vis) {i j : Nat} (hi : i < σ'.length)
    (hj : j < σ'.length) : f i ≤ f j ↔ i ≤ j := by
  have := h.lt_iff hj hi
  constructor
  · intro hf; by_contra h'; have := this.mpr (by omega); omega
  · intro hij; by_contra h'; have := this.mp (by omega); omega

theorem inWindow_iff {rate : TickRate} (h : Subsequence σ σ' f vis' vis) {i k : Nat} (hi : i < σ'.length)
    (hk : k < σ'.length) (w : Window) : InWindow rate σ' i k w ↔ InWindow rate σ (f i) (f k) w := by
  simp only [InWindow, h.get i hi, h.get k hk]

/-- Every timepoint of `σ'` is a timepoint of `σ`. -/
theorem lt_length (h : Subsequence σ σ' f vis' vis) {i : Nat} (hi : i < σ'.length) :
    f i < σ.length := by
  have := h.get i hi
  rw [List.getElem?_eq_getElem hi] at this
  by_contra hf
  rw [List.getElem?_eq_none (by omega)] at this
  cases this

end Subsequence

/-- A subtrace whose every timepoint is visible. -/
theorem SubTrace.toSubsequence {σ σ' : Trace} {f : Nat → Nat} {vis : Nat → Prop}
    (h : SubTrace σ σ' f vis) : Subsequence σ σ' f (fun _ => True) vis :=
  ⟨h.get, h.mono, fun K => (h.vis_iff K).trans
    ⟨fun ⟨i, hi, hf⟩ => ⟨i, hi, hf, trivial⟩, fun ⟨i, hi, hf, _⟩ => ⟨i, hi, hf⟩⟩⟩

theorem SubTrace.lt_iff {σ σ' : Trace} {f : Nat → Nat} {vis : Nat → Prop}
    (h : SubTrace σ σ' f vis) {i j : Nat} (hi : i < σ'.length) (hj : j < σ'.length) :
    f i < f j ↔ i < j :=
  h.toSubsequence.lt_iff hi hj

theorem SubTrace.le_iff {σ σ' : Trace} {f : Nat → Nat} {vis : Nat → Prop}
    (h : SubTrace σ σ' f vis) {i j : Nat} (hi : i < σ'.length) (hj : j < σ'.length) :
    f i ≤ f j ↔ i ≤ j :=
  h.toSubsequence.le_iff hi hj

theorem SubTrace.inWindow_iff {rate : TickRate} {σ σ' : Trace} {f : Nat → Nat} {vis : Nat → Prop}
    (h : SubTrace σ σ' f vis) {i k : Nat} (hi : i < σ'.length) (hk : k < σ'.length)
    (w : Window) : InWindow rate σ' i k w ↔ InWindow rate σ (f i) (f k) w :=
  h.toSubsequence.inWindow_iff hi hk w

theorem SubTrace.lt_length {σ σ' : Trace} {f : Nat → Nat} {vis : Nat → Prop}
    (h : SubTrace σ σ' f vis) {i : Nat} (hi : i < σ'.length) : f i < σ.length :=
  h.toSubsequence.lt_length hi

/-! ## Renumberings -/

/-- A bijection `π` of the indices, with inverse `ρ`, that sends each timepoint of the
subsequence `σ'` to its timepoint `f i` of the trace. -/
structure Renumbering (σ' : Trace) (f : Nat → Nat) (π ρ : Nat → Nat) : Prop where
  agree : ∀ i < σ'.length, π i = f i
  left : ∀ x, ρ (π x) = x
  right : ∀ x, π (ρ x) = x

theorem Renumbering.inj {σ' : Trace} {f π ρ : Nat → Nat} (h : Renumbering σ' f π ρ) {x y : Nat}
    (hxy : π x = π y) : x = y := by
  have := congrArg ρ hxy
  rwa [h.left, h.left] at this

/-- **Every subsequence has a renumbering**: its index map extends to a bijection. -/
theorem exists_renumbering {σ σ' : Trace} {f : Nat → Nat} {vis' vis : Nat → Prop}
    (h : Subsequence σ σ' f vis' vis) : ∃ π ρ, Renumbering σ' f π ρ := by
  refine ⟨extendPerm f σ'.length, extendPermInv f σ'.length,
    ⟨extendPerm_agree f _ ?_, extendPermInv_extendPerm f _, extendPerm_extendPermInv f _⟩⟩
  intro i j hi hj hf
  rcases Nat.lt_trichotomy i j with hij | rfl | hij
  · have := h.mono i j hij hj; omega
  · rfl
  · have := h.mono j i hij hi; omega

/-- The valuation gives no variable a timepoint. -/
def _root_.Dogwood.Spec.Temporal.Valuation.NoTp (v : Valuation) : Prop :=
  ∀ x k, v x ≠ some (.tp k)

theorem Valuation.rename_of_noTp {v : Valuation} (hv : v.NoTp) (π : Nat → Nat) :
    v.rename π = v := by
  funext x
  simp only [Valuation.rename]
  cases h : v x with
  | none => rfl
  | some w =>
    cases w with
    | val _ => rfl
    | tp k => exact absurd h (hv x k)

theorem Valuation.noTp_empty : Valuation.empty.NoTp := fun _ _ h => by cases h

/-! ## The slice lemma -/

section

variable {ι : ImplChoices} {rate : TickRate} {σ σ' : Trace} {e : Event} {f : Nat → Nat} {vis' vis : Nat → Prop}
  {π ρ : Nat → Nat}

theorem matches_rename (π : Nat → Nat) (e : Event) (v : Valuation) (t : Term) (w : Cedar.Spec.Value) :
    t.Matches e (v.rename π) w ↔ t.Matches e v w := by
  cases t with
  | wildcard => exact Iff.rfl
  | _ =>
    simp only [Term.Matches, eval_rename]
    constructor
    · intro h
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨w', hw', hr⟩ := h
      cases w' with
      | val a => simp only [TVal.rename, TVal.val.injEq] at hr; rw [hw', hr]
      | tp k => cases hr
    · intro h; rw [h]; rfl

theorem argsMatch_rename (π : Nat → Nat) (e : Event) (v : Valuation) (ev : Event)
    (args : List (Path × Term)) : ArgsMatch e (v.rename π) ev args ↔ ArgsMatch e v ev args := by
  simp only [ArgsMatch, matches_rename]

theorem rename_map_rename {ρ π : Nat → Nat} (h : ∀ x, π (ρ x) = x) (row : List TVal) :
    (row.map (TVal.rename ρ)).map (TVal.rename π) = row := by
  rw [List.map_map]
  conv => rhs; rw [← List.map_id row]
  exact List.map_congr_left fun w _ => TVal.rename_comp h w

theorem readLong_num' {g : Int → Option Int} {n : Int} {c : CVal} (h : readLong g n = some c) :
    ∃ m, c = .num m := by
  unfold readLong at h
  split at h
  · simp only [Option.some.injEq] at h; exact ⟨n, h.symm⟩
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨m, _, rfl⟩ := h
    exact ⟨m, rfl⟩

theorem map_rename_injective {π ρ : Nat → Nat} (hl : ∀ x, ρ (π x) = x) :
    Function.Injective (List.map (TVal.rename π)) := by
  intro a b hab
  have := congrArg (List.map (TVal.rename ρ)) hab
  rwa [rename_map_rename hl, rename_map_rename hl] at this

/-- The rows of an aggregation, renumbered: a set of rows with property `P` corresponds to a
set of rows with property `Q`, when `Q` is `P` renumbered, and a total of the rows is unchanged by
renumbering. -/
theorem rows_congr {π ρ : Nat → Nat} (hl : ∀ x, ρ (π x) = x) (hr : ∀ x, π (ρ x) = x)
    {P Q : List TVal → Prop} (ih : ∀ row, P row ↔ Q (row.map (TVal.rename π))) (len : Nat)
    (F : List (List TVal) → Int) (hF : ∀ rows, F (rows.map (List.map (TVal.rename π))) = F rows)
    (n : Int) :
    (∃ rows : List (List TVal), rows.Nodup ∧ (∀ row, row ∈ rows ↔ row.length = len ∧ P row) ∧
      n = F rows) ↔
    (∃ rows : List (List TVal), rows.Nodup ∧ (∀ row, row ∈ rows ↔ row.length = len ∧ Q row) ∧
      n = F rows) := by
  have hinj := map_rename_injective hl
  constructor
  · rintro ⟨rows, hnd, hmem, rfl⟩
    refine ⟨rows.map (List.map (TVal.rename π)), hnd.map _ (fun a b hab h => hab (hinj h)), fun row' => ?_, (hF rows).symm⟩
    constructor
    · intro h
      obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp h
      obtain ⟨hlen, hP⟩ := (hmem row).mp hrow
      exact ⟨by simpa using hlen, (ih row).mp hP⟩
    · rintro ⟨hlen, hQ⟩
      refine List.mem_map.mpr ⟨row'.map (TVal.rename ρ), (hmem _).mpr ⟨by simpa using hlen, ?_⟩,
        rename_map_rename hr row'⟩
      exact (ih _).mpr (by rw [rename_map_rename hr]; exact hQ)
  · rintro ⟨rows', hnd, hmem, rfl⟩
    have hback : (rows'.map (List.map (TVal.rename ρ))).map (List.map (TVal.rename π)) = rows' := by
      rw [List.map_map]
      conv => rhs; rw [← List.map_id rows']
      exact List.map_congr_left fun row _ => rename_map_rename hr row
    refine ⟨rows'.map (List.map (TVal.rename ρ)), hnd.map _ (fun a b hab h => hab (map_rename_injective hr h)), fun row => ?_, ?_⟩
    · constructor
      · intro h
        obtain ⟨row', hrow', rfl⟩ := List.mem_map.mp h
        obtain ⟨hlen, hQ⟩ := (hmem row').mp hrow'
        exact ⟨by simpa using hlen, (ih _).mpr (by rw [rename_map_rename hr]; exact hQ)⟩
      · rintro ⟨hlen, hP⟩
        refine List.mem_map.mpr ⟨row.map (TVal.rename π), (hmem _).mpr ⟨by simpa using hlen,
          (ih row).mp hP⟩, rename_map_rename hl row⟩
    · rw [← hF (rows'.map (List.map (TVal.rename ρ))), hback]

mutual

/-- **Satisfaction over a subsequence.** Satisfaction at timepoint `i` of the subsequence, under
its visibility `vis'`, is satisfaction at timepoint `f i` of the trace, under the image
visibility `vis`, with the valuation's timepoints renumbered by the renumbering. -/
theorem sat_subseq (h : Subsequence σ σ' f vis' vis) (hπ : Renumbering σ' f π ρ) :
    (φ : Formula) → ∀ (v : Valuation) (i : Nat), i < σ'.length →
      (Sat ι rate σ' e vis' v i φ ↔ Sat ι rate σ e vis (v.rename π) (f i) φ)
  | .and φ ψ, v, i, hi => by
    simp only [Sat]
    rw [sat_subseq h hπ φ v i hi, sat_subseq h hπ ψ v i hi]
  | .not φ, v, i, hi => by
    simp only [Sat]
    rw [sat_subseq h hπ φ v i hi]
  | .formerly w φ, v, i, hi => by
    simp only [Sat]
    constructor
    · rintro ⟨k, hk, hv, hw, hs⟩
      have hk' : k < σ'.length := by omega
      exact ⟨f k, (h.le_iff hk' hi).mpr hk, (h.vis_iff _).mpr ⟨k, hk', rfl, hv⟩,
        (h.inWindow_iff hi hk' w).mp hw, (sat_subseq h hπ φ v k hk').mp hs⟩
    · rintro ⟨K, hK, hv, hw, hs⟩
      obtain ⟨k, hk', rfl, hv'⟩ := (h.vis_iff K).mp hv
      exact ⟨k, (h.le_iff hk' hi).mp hK, hv', (h.inWindow_iff hi hk' w).mpr hw,
        (sat_subseq h hπ φ v k hk').mpr hs⟩
  | .previous w φ, v, i, hi => by
    simp only [Sat]
    constructor
    · rintro ⟨k, hk, hv, hlast, hw, hs⟩
      have hk' : k < σ'.length := by omega
      refine ⟨f k, (h.lt_iff hk' hi).mpr hk, (h.vis_iff _).mpr ⟨k, hk', rfl, hv⟩, ?_,
        (h.inWindow_iff hi hk' w).mp hw, (sat_subseq h hπ φ v k hk').mp hs⟩
      intro K h1 h2 hvK
      obtain ⟨j, hj, rfl, hvj⟩ := (h.vis_iff K).mp hvK
      exact hlast j ((h.lt_iff hk' hj).mp h1) ((h.lt_iff hj hi).mp h2) hvj
    · rintro ⟨K, hK, hv, hlast, hw, hs⟩
      obtain ⟨k, hk', rfl, hv'⟩ := (h.vis_iff K).mp hv
      refine ⟨k, (h.lt_iff hk' hi).mp hK, hv', ?_, (h.inWindow_iff hi hk' w).mpr hw,
        (sat_subseq h hπ φ v k hk').mpr hs⟩
      intro j h1 h2 hvj
      exact hlast (f j) ((h.lt_iff hk' (by omega)).mpr h1) ((h.lt_iff (by omega) hi).mpr h2)
        ((h.vis_iff _).mpr ⟨j, by omega, rfl, hvj⟩)
  | .since φ w ψ, v, i, hi => by
    simp only [Sat]
    constructor
    · rintro ⟨k, hk, hv, hw, hs, hall⟩
      have hk' : k < σ'.length := by omega
      refine ⟨f k, (h.le_iff hk' hi).mpr hk, (h.vis_iff _).mpr ⟨k, hk', rfl, hv⟩,
        (h.inWindow_iff hi hk' w).mp hw, (sat_subseq h hπ ψ v k hk').mp hs, ?_⟩
      intro K h1 h2 hvK
      obtain ⟨j, hj, rfl, hvj⟩ := (h.vis_iff K).mp hvK
      exact (sat_subseq h hπ φ v j hj).mp
        (hall j ((h.lt_iff hk' hj).mp h1) ((h.le_iff hj hi).mp h2) hvj)
    · rintro ⟨K, hK, hv, hw, hs, hall⟩
      obtain ⟨k, hk', rfl, hv'⟩ := (h.vis_iff K).mp hv
      refine ⟨k, (h.le_iff hk' hi).mp hK, hv', (h.inWindow_iff hi hk' w).mpr hw,
        (sat_subseq h hπ ψ v k hk').mpr hs, ?_⟩
      intro j h1 h2 hvj
      have hj : j < σ'.length := by omega
      exact (sat_subseq h hπ φ v j hj).mpr (hall (f j) ((h.lt_iff hk' hj).mpr h1)
        ((h.le_iff hj hi).mpr h2) ((h.vis_iff _).mpr ⟨j, hj, rfl, hvj⟩))
  | .pred a kd args, v, i, hi => by
    simp only [Sat, h.get i hi, argsMatch_rename]
  | .cmp op l r, v, i, hi => by
    simp only [Sat]
    constructor
    · rintro ⟨a, b, ha, hb, hop⟩
      exact ⟨a.rename π, b.rename π, (denotes_subseq h hπ l v i hi a).mp ha,
        (denotes_subseq h hπ r v i hi b).mp hb, (holds_rename hπ.inj op a b).mpr hop⟩
    · rintro ⟨a', b', ha, hb, hop⟩
      have ha' : a' = (a'.rename ρ).rename π := (CVal.rename_comp hπ.right a').symm
      have hb' : b' = (b'.rename ρ).rename π := (CVal.rename_comp hπ.right b').symm
      rw [ha'] at ha hop
      rw [hb'] at hb hop
      exact ⟨a'.rename ρ, b'.rename ρ, (denotes_subseq h hπ l v i hi _).mpr ha,
        (denotes_subseq h hπ r v i hi _).mpr hb, (holds_rename hπ.inj op _ _).mp hop⟩
  | .exist x φ, v, i, hi => by
    simp only [Sat]
    constructor
    · rintro ⟨w, hs⟩
      refine ⟨w.rename π, ?_⟩
      rw [← Valuation.rename_bind]
      exact (sat_subseq h hπ φ (v.bind x.name w) i hi).mp hs
    · rintro ⟨w', hs⟩
      refine ⟨w'.rename ρ, (sat_subseq h hπ φ (v.bind x.name (w'.rename ρ)) i hi).mpr ?_⟩
      rw [Valuation.rename_bind, TVal.rename_comp hπ.right]
      exact hs
  | .tp x, v, i, hi => by
    simp only [Sat, tpValue, Valuation.rename]
    constructor
    · intro hx; rw [hx]; simp [TVal.rename, hπ.agree i hi]
    · intro hx
      simp only [Option.map_eq_some_iff] at hx
      obtain ⟨w, hw, hr⟩ := hx
      cases w with
      | val _ => cases hr
      | tp k =>
        simp only [TVal.rename, TVal.tp.injEq] at hr
        rw [← hπ.agree i hi] at hr
        rw [hw, hπ.inj hr]

theorem denotes_subseq (h : Subsequence σ σ' f vis' vis) (hπ : Renumbering σ' f π ρ) :
    (t : Term) → ∀ (v : Valuation) (i : Nat), i < σ'.length → ∀ c,
      (Denotes ι rate σ' e vis' v i t c ↔ Denotes ι rate σ e vis (v.rename π) (f i) t (c.rename π))
  | .agg a, v, i, hi, c => by
    simp only [Denotes]
    refine exists_congr fun n => ?_
    rw [total_subseq h hπ a v i hi n]
    refine and_congr_right fun _ => ?_
    constructor
    · intro hc
      obtain ⟨m, rfl⟩ := readLong_num' hc
      exact hc
    · intro hc
      obtain ⟨m, hm⟩ := readLong_num' hc
      cases c with
      | num _ => exact hc
      | val _ => exact hc
      | tp _ => cases hm
  | .arith op l r, v, i, hi, c => by
    simp only [Denotes]
    refine exists_congr fun m => exists_congr fun n => ?_
    have hl := denotes_subseq h hπ l v i hi (.num m)
    have hr := denotes_subseq h hπ r v i hi (.num n)
    simp only [CVal.rename] at hl hr
    rw [hl, hr]
    refine and_congr_right fun _ => and_congr_right fun _ => ?_
    constructor
    · intro hc
      obtain ⟨m', rfl⟩ := readLong_num' hc
      exact hc
    · intro hc
      obtain ⟨m', hm⟩ := readLong_num' hc
      cases c with
      | num _ => exact hc
      | val _ => exact hc
      | tp _ => cases hm
  | .entity _, v, i, hi, c | .long _, v, i, hi, c | .decimal _, v, i, hi, c
  | .string _, v, i, hi, c | .bool _, v, i, hi, c | .context _, v, i, hi, c
  | .scope _ _, v, i, hi, c | .var _, v, i, hi, c | .wildcard, v, i, hi, c => by
    simp only [Denotes, eval_rename]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w.rename π, by rw [hw]; rfl, (ofTVal_rename π w).symm⟩
    · rintro ⟨w', hw', hc⟩
      simp only [Option.map_eq_some_iff] at hw'
      obtain ⟨w, hw, rfl⟩ := hw'
      exact ⟨w, hw, CVal.rename_inj hπ.inj (by rw [hc, ofTVal_rename])⟩

theorem total_subseq (h : Subsequence σ σ' f vis' vis) (hπ : Renumbering σ' f π ρ) :
    (a : Aggregate) → ∀ (v : Valuation) (i : Nat), i < σ'.length →
      ∀ n, (Total ι rate σ' e vis' v i a n ↔ Total ι rate σ e vis (v.rename π) (f i) a n)
  | .count dom body, v, i, hi, n => by
    have ih := fun (row : List TVal) => sat_subseq h hπ body (v.bindAll (domainNames dom) row) i hi
    simp only [Valuation.rename_bindAll] at ih
    simp only [Total]
    exact rows_congr hπ.left hπ.right ih _ (fun rows => (rows.length : Int))
      (fun rows => by simp) n
  | .sum s dom body, v, i, hi, n => by
    have ih := fun (row : List TVal) => sat_subseq h hπ body (v.bindAll (domainNames dom) row) i hi
    simp only [Valuation.rename_bindAll] at ih
    simp only [Total]
    exact rows_congr hπ.left hπ.right ih _ (fun rows => (rows.map (summand s (domainNames dom))).sum)
      (fun rows => by simp [List.map_map, Function.comp_def, summand_rename]) n

end

/-- **Satisfaction over a subsequence, under a valuation without timepoints**: satisfaction at
timepoint `i` of the subsequence is satisfaction at timepoint `f i` of the trace, for every
condition. -/
theorem sat_subseq_noTp (h : Subsequence σ σ' f vis' vis) (φ : Formula) {v : Valuation}
    (hv : v.NoTp) (i : Nat) (hi : i < σ'.length) :
    Sat ι rate σ' e vis' v i φ ↔ Sat ι rate σ e vis v (f i) φ := by
  obtain ⟨π, ρ, hπ⟩ := exists_renumbering h
  rw [sat_subseq h hπ φ v i hi, Valuation.rename_of_noTp hv]

/-- **The slice lemma.** Satisfaction at timepoint `i` of the subsequence with every timepoint
visible is satisfaction at timepoint `f i` of the trace with the subsequence's timepoints
visible, under a valuation without timepoints. -/
theorem sat_slice {vis : Nat → Prop} (h : SubTrace σ σ' f vis) (φ : Formula) {v : Valuation}
    (hv : v.NoTp) (i : Nat) (hi : i < σ'.length) :
    Sat ι rate σ' e (fun _ => True) v i φ ↔ Sat ι rate σ e vis v (f i) φ :=
  sat_subseq_noTp h.toSubsequence φ hv i hi

end

/-! ## Filtered prefixes are subtraces -/

theorem take_succ_eq {σ : Trace} {n : Nat} (hn : n < σ.length) :
    σ.take (n + 1) = σ.take n ++ [σ[n]] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hn]
  rfl

theorem take_succ_filter (σ : Trace) (P : TimePoint → Bool) {n : Nat} (hn : n < σ.length) :
    (σ.take (n + 1)).filter P = (σ.take n).filter P ++ (if P σ[n] then [σ[n]] else []) := by
  rw [take_succ_eq hn, List.filter_append]
  by_cases h : P σ[n] = true <;> simp [h]

/-- The events of `σ[0] … σ[m − 1]` that satisfy `P` form a subsequence of `σ`, whose
timepoints are exactly the indices below `m` of the events satisfying `P`. -/
theorem subTrace_filter (σ : Trace) (P : TimePoint → Bool) : ∀ m, m ≤ σ.length →
    ∃ f, SubTrace σ ((σ.take m).filter P) f
      (fun K => K < m ∧ ∃ p, σ[K]? = some p ∧ P p = true)
  | 0, _ => ⟨fun _ => 0, ⟨by simp, by simp, fun K => by simp⟩⟩
  | m + 1, hm => by
    obtain ⟨f, hf⟩ := subTrace_filter σ P m (by omega)
    have hmσ : m < σ.length := by omega
    rw [take_succ_filter σ P hmσ]
    generalize hτ : (σ.take m).filter P = τ at hf
    -- Every timepoint of the old subsequence lies below `m`.
    have hlt : ∀ i < τ.length, f i < m := fun i hi => ((hf.vis_iff (f i)).mpr ⟨i, hi, rfl⟩).1
    by_cases hp : P σ[m] = true
    · simp only [hp, if_true]
      refine ⟨fun i => if i < τ.length then f i else m, ?_, ?_, ?_⟩
      · intro i hi
        simp only [List.length_append, List.length_singleton] at hi
        by_cases hil : i < τ.length
        · simp only [hil, if_true]
          rw [List.getElem?_append_left hil]
          exact hf.get i hil
        · have : i = τ.length := by omega
          subst this
          simp [List.getElem?_eq_getElem hmσ]
      · intro i j hij hj
        simp only [List.length_append, List.length_singleton] at hj
        have hil : i < τ.length := by omega
        by_cases hjl : j < τ.length
        · simp only [hil, hjl, if_true]
          exact hf.mono i j hij hjl
        · simp only [hil, hjl, if_true, if_false]
          exact hlt i hil
      · intro K
        simp only [List.length_append, List.length_singleton]
        constructor
        · rintro ⟨hK, p, hp', hP⟩
          by_cases hKm : K < m
          · obtain ⟨i, hi, rfl⟩ := (hf.vis_iff K).mp ⟨hKm, p, hp', hP⟩
            exact ⟨i, by omega, by simp [hi]⟩
          · have hKe : K = m := by omega
            subst hKe
            exact ⟨τ.length, by omega, by simp⟩
        · rintro ⟨i, hi, rfl⟩
          by_cases hil : i < τ.length
          · simp only [hil, if_true]
            obtain ⟨hK, p, hp', hP⟩ := (hf.vis_iff (f i)).mpr ⟨i, hil, rfl⟩
            exact ⟨by omega, p, hp', hP⟩
          · simp only [hil, if_false]
            exact ⟨by omega, σ[m], List.getElem?_eq_getElem hmσ, hp⟩
    · simp only [hp, Bool.false_eq_true, if_false, List.append_nil]
      refine ⟨f, hf.get, hf.mono, ?_⟩
      intro K
      constructor
      · rintro ⟨hK, p, hp', hP⟩
        by_cases hKm : K < m
        · exact (hf.vis_iff K).mp ⟨hKm, p, hp', hP⟩
        · have hKe : K = m := by omega
          subst hKe
          rw [List.getElem?_eq_getElem hmσ] at hp'
          cases hp'
          exact absurd hP hp
      · intro h'
        obtain ⟨hK, p, hp', hP⟩ := (hf.vis_iff K).mpr h'
        exact ⟨by omega, p, hp', hP⟩

/-- A suffix of the trace is a subsequence of it: timepoint `i` of `σ.drop off` is timepoint
`off + i` of `σ`. -/
theorem subsequence_drop (σ : Trace) (off : Nat) (vis : Nat → Prop) :
    Subsequence σ (σ.drop off) (off + ·) (fun i => vis (off + i))
      (fun K => vis K ∧ off ≤ K ∧ K < σ.length) := by
  refine ⟨fun i _ => List.getElem?_drop .., fun i j hij _ => by omega, fun K => ?_⟩
  simp only [List.length_drop]
  constructor
  · rintro ⟨hv, hoff, hK⟩
    exact ⟨K - off, by omega, by omega, by rw [Nat.add_sub_cancel' hoff]; exact hv⟩
  · rintro ⟨i, hi, rfl, hv⟩
    exact ⟨hv, by omega, by omega⟩

end Dogwood.Thm
