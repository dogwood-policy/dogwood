import Dogwood.Thm.Frontend.Relativization.Ord
import Dogwood.Thm.Trace
import Dogwood.Thm.Frontend.LeafPasses.Relativize

/-!
# What the relativization rewrite's encodings mean

The rewrite replaces `previous` and a general `since` by encodings over timepoint variables
(`LeafPasses.encodePrevious`, `LeafPasses.encodeSince`). Read under `RSat`, with every timepoint
visible, and with μ holding exactly at the visible timepoints, they mean:

* `rsat_encodePrevious`: some `k < j` in the window has the guarded body, and no visible
  timepoint strictly between `k` and `j` is in the window;
* `rsat_encodeSince`: some `k ≤ j` in the window has the guarded anchor, and the left holds at
  every visible timepoint of `(k, j]` in the window. The two counts of the encoding are equal
  exactly when this holds, provided that a count fits a `Long` (`σ.length ≤ Int64.MAX`).

The guarded body, the anchor and the left are taken as black boxes, given by what they mean under
every valuation that agrees with the current one off the rewrite's fresh names (`AgreeOff`).
On a trace whose timestamps never decrease, a timepoint between a timepoint in the window and
the timepoint the window looks back from is in the window too (`inWindow_between`); that is the
step from "in the window" to "the key's", which the relativization theorem takes.
-/

namespace Dogwood.Thm.Frontend

open Dogwood.Frontend Dogwood.Frontend.LeafPasses Surface.Temporal
open Dogwood.Spec (Event Trace TickRate TimePoint)
open Dogwood.Spec.Temporal (Valuation ImplChoices CVal TVal CmpOp InWindow Window readLong
  domainNames)

/-! ## Windows -/

/-- **A timepoint between a timepoint in the window and the window's end is in the window**, on
a trace whose timestamps never decrease. -/
theorem inWindow_between {rate : TickRate} {σ : Trace} (hσ : σ.Nondecreasing) {j k m : Nat}
    {w : Window} (h : InWindow rate σ j k w) (hkm : k ≤ m) (hmj : m ≤ j) : InWindow rate σ j m w := by
  obtain ⟨pj, pk, hpj, hpk, h₁, h₂⟩ := h
  have hj : j < σ.length := by
    rcases Nat.lt_or_ge j σ.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hpj; cases hpj
  obtain ⟨pm, hpm⟩ : ∃ pm, σ[m]? = some pm := ⟨σ[m], List.getElem?_eq_getElem (by omega)⟩
  have := Dogwood.Spec.Trace.Nondecreasing.ts_le hσ hkm hpk hpm
  have := Dogwood.Spec.Trace.Nondecreasing.ts_le hσ hmj hpm hpj
  exact ⟨pj, pm, hpj, hpm, by omega, by omega⟩

theorem inWindow_lt_length {rate : TickRate} {σ : Trace} {j k : Nat} {w : Window}
    (h : InWindow rate σ j k w) : j < σ.length := by
  obtain ⟨pj, _, hpj, _⟩ := h
  rcases Nat.lt_or_ge j σ.length with h | h
  · exact h
  · rw [List.getElem?_eq_none h] at hpj; cases hpj

/-! ## Counting -/

/-- A duplicate-free list of rows `[tp m]`, one for each `m` of a bounded set, has the size of
the set. -/
theorem rows_card {P : List TVal → Prop} {Q : Nat → Prop} {f : Nat → Bool} {L : Nat} {N : Int}
    (hf : ∀ m, f m = true ↔ Q m) (hP : ∀ row, P row ↔ ∃ m, row = [.tp m] ∧ Q m)
    (hb : ∀ m, Q m → m < L) :
    (∃ rows : List (List TVal), rows.Nodup ∧ (∀ row, row ∈ rows ↔ P row) ∧ N = rows.length) ↔
      N = (((List.range L).filter f).length : Int) := by
  let R : List (List TVal) := ((List.range L).filter f).map fun m => [.tp m]
  have hRmem : ∀ row, row ∈ R ↔ P row := by
    intro row
    rw [hP]
    simp only [R, List.mem_map, List.mem_filter, List.mem_range, hf]
    constructor
    · rintro ⟨m, ⟨_, hq⟩, rfl⟩; exact ⟨m, rfl, hq⟩
    · rintro ⟨m, rfl, hq⟩; exact ⟨m, ⟨hb m hq, hq⟩, rfl⟩
  have hRnd : R.Nodup :=
    List.Pairwise.map _ (fun a b hab h => hab (by simpa using h))
      (List.Pairwise.filter _ List.nodup_range)
  have hRlen : R.length = ((List.range L).filter f).length := by
    simp [R]
  constructor
  · rintro ⟨rows, hnd, hmem, rfl⟩
    have hperm : rows.Perm R := (List.perm_ext_iff_of_nodup hnd hRnd).mpr fun a => by
      rw [hmem, hRmem]
    rw [hperm.length_eq, hRlen]
  · intro hN
    exact ⟨R, hRnd, hRmem, by rw [hN, hRlen]⟩

theorem length_filter_and_eq {α : Type} (p q : α → Bool) (l : List α) :
    (l.filter fun a => p a && q a).length = (l.filter p).length ↔ ∀ a ∈ l, p a = true → q a = true := by
  have : (l.filter fun a => p a && q a) = (l.filter p).filter q := by
    rw [List.filter_filter]; congr 1; funext a; exact Bool.and_comm _ _
  rw [this, List.length_filter_eq_length_iff]
  simp only [List.mem_filter, and_imp]

theorem length_filter_range_le (L : Nat) (f : Nat → Bool) : ((List.range L).filter f).length ≤ L := by
  have := List.length_filter_le f (List.range L)
  simpa using this

/-- A count that fits a `Long` is read as itself. -/
theorem aggregateValue_of_le {ι : ImplChoices} {N : Int} (h₀ : 0 ≤ N) (h : N ≤ Int64.MAX) :
    ι.aggregateValue N = some (.num N) := by
  simp only [ImplChoices.aggregateValue, readLong]
  rw [if_pos ⟨by simp only [Int64.MIN]; omega, h⟩]

/-- The `Long` a count that fits is bound to. -/
def longOf (N : Int) : TVal := .val (.prim (.int (Int64.ofInt N)))

theorem ofTVal_longOf {N : Int} (h₀ : 0 ≤ N) (h : N ≤ Int64.MAX) : CVal.ofTVal (longOf N) = .num N := by
  simp only [longOf, CVal.ofTVal, CVal.ofValue]
  rw [Int64.toInt_ofInt_of_le (by omega) (by simp only [Int64.MAX] at h; omega)]

/-! ## The building blocks, under `RSat` -/

section
variable {ι : ImplChoices} {rate : TickRate} {σ : Trace} {e : Event} {vis : Nat → Prop} {pre : String}

theorem rsat_mkTp (sp : Span) (x : String) (v : Valuation) (j : Nat) :
    RSat ι rate σ e vis v j (mkTp sp x) ↔ v x = some (.tp j) := by
  simp [mkTp, XSat, BinderSlot.toName, pure, Except.pure, Dogwood.Spec.Temporal.tpValue]

theorem rsat_mkAnd (sp : Span) (a b : Condition) (v : Valuation) (j : Nat) :
    RSat ι rate σ e vis v j (mkAnd sp a b) ↔ RSat ι rate σ e vis v j a ∧ RSat ι rate σ e vis v j b :=
  Iff.rfl

theorem rsat_mkAnds (sp : Span) (c : Condition) (cs : List Condition) (v : Valuation) (j : Nat) :
    RSat ι rate σ e vis v j (mkAnds sp (c :: cs)) ↔ ∀ c' ∈ c :: cs, RSat ι rate σ e vis v j c' :=
  xsat_mkAnds sp v j c cs

theorem rsat_mkNot (sp : Span) (a : Condition) (v : Valuation) (j : Nat) :
    RSat ι rate σ e vis v j (mkNot sp a) ↔ ¬ RSat ι rate σ e vis v j a :=
  Iff.rfl

theorem rsat_mkExistsTp (sp : Span) (x : String) (b : Condition) (v : Valuation) (j : Nat) :
    RSat ι rate σ e vis v j (mkExistsTp sp x b) ↔ ∃ w, RSat ι rate σ e vis (v.bind x w) j b := by
  simp [mkExistsTp, XSat, BinderSlot.toName, pure, Except.pure, anyValue]

theorem rsat_mkExistsLong (sp : Span) (x : String) (b : Condition) (v : Valuation) (j : Nat) :
    RSat ι rate σ e vis v j (mkExistsLong sp x b) ↔ ∃ w, RSat ι rate σ e vis (v.bind x w) j b := by
  simp [mkExistsLong, XSat, BinderSlot.toName, pure, Except.pure, anyValue]

theorem rsat_mkFormerly {sp : Span} {w : WithinSpec} {win : Window} (hw : w.toSpec = .ok win)
    (c : Condition) (v : Valuation) (j : Nat) :
    RSat ι rate σ e vis v j (mkFormerly sp w c) ↔
      ∃ k, k ≤ j ∧ vis k ∧ InWindow rate σ j k win ∧ RSat ι rate σ e vis v k c := by
  simp [mkFormerly, XSat, hw]

theorem rsat_mkCmp (sp : Span) (op : CmpOp) (a b : String) (v : Valuation) (j : Nat) :
    RSat ι rate σ e vis v j (mkCmp sp op a b) ↔
      ∃ wa wb, v a = some wa ∧ v b = some wb ∧ xHolds true op (CVal.ofTVal wa) (CVal.ofTVal wb) := by
  simp only [mkCmp, XSat, xdenotes_var]
  constructor
  · rintro ⟨_, _, ⟨wa, ha, rfl⟩, ⟨wb, hb, rfl⟩, h⟩; exact ⟨wa, wb, ha, hb, h⟩
  · rintro ⟨wa, wb, ha, hb, h⟩; exact ⟨_, _, ⟨wa, ha, rfl⟩, ⟨wb, hb, rfl⟩, h⟩

theorem xHolds_tp_lt {m n : Nat} : xHolds true .lt (.tp m) (.tp n) ↔ m < n := by
  simp [xHolds, CmpOp.Holds, tpOrders]

theorem xHolds_tp_le {m n : Nat} : xHolds true .le (.tp m) (.tp n) ↔ m ≤ n := by
  simp [xHolds, CmpOp.Holds, tpOrders]

theorem rsat_mkCmp_tp {sp : Span} {op : CmpOp} {a b : String} {v : Valuation} {m n : Nat}
    (ha : v a = some (.tp m)) (hb : v b = some (.tp n)) (j : Nat) :
    RSat ι rate σ e vis v j (mkCmp sp op a b) ↔ xHolds true op (.tp m) (.tp n) := by
  rw [rsat_mkCmp, ha, hb]
  simp [CVal.ofTVal]

theorem rsat_mkCmp_eq (sp : Span) (a b : String) (v : Valuation) (j : Nat) :
    RSat ι rate σ e vis v j (mkCmp sp .eq a b) ↔
      ∃ wa wb, v a = some wa ∧ v b = some wb ∧ CVal.ofTVal wa = CVal.ofTVal wb := by
  rw [rsat_mkCmp]
  simp only [xHolds_eq]

/-- `(count for (x: Timepoint). where body) == n`: the count's rows are the timepoints `body`
holds of, and it reads as the value of `n`. -/
theorem rsat_mkAggEq_count (sp : Span) (x : String) (body : Condition) (n : String) (v : Valuation)
    (j : Nat) :
    RSat ι rate σ e vis v j (mkAggEq sp (mkCount sp x body) n) ↔
      ∃ c, v n = some c ∧ ∃ N : Int, (∃ rows : List (List TVal), rows.Nodup ∧
        (∀ row, row ∈ rows ↔ ∃ r₀, row = [r₀] ∧ RSat ι rate σ e vis (v.bind x r₀) j body) ∧
        N = rows.length) ∧ ι.aggregateValue N = some (CVal.ofTVal c) := by
  have hrow : ∀ row : List TVal, (row.length = (domainNames [⟨x, .timepoint⟩]).length ∧
      RowIn anyValue [⟨x, .timepoint⟩] row ∧
      RSat ι rate σ e vis (v.bindAll (domainNames [⟨x, .timepoint⟩]) row) j body) ↔
      ∃ r₀, row = [r₀] ∧ RSat ι rate σ e vis (v.bind x r₀) j body := by
    intro row
    simp only [domainNames, Dogwood.Spec.Temporal.dedup, List.map_cons, List.map_nil,
      List.filter_nil, List.length_cons, List.length_nil]
    constructor
    · rintro ⟨hl, _, hs⟩
      match row, hl with
      | [r₀], _ => exact ⟨r₀, rfl, hs⟩
    · rintro ⟨r₀, rfl, hs⟩
      exact ⟨rfl, fun _ _ => trivial, hs⟩
  have hagg : ∀ a, XDenotes ι rate σ e vis true anyValue v j (mkCount sp x body) a ↔
      ∃ N : Int, (∃ rows : List (List TVal), rows.Nodup ∧
        (∀ row, row ∈ rows ↔ ∃ r₀, row = [r₀] ∧ RSat ι rate σ e vis (v.bind x r₀) j body) ∧
        N = rows.length) ∧ ι.aggregateValue N = some a := by
    intro a
    simp only [mkCount, XDenotes, XTotal, List.mapM_cons, List.mapM_nil, TypedBinder.toSpec,
      BinderSlot.toName, pure, Except.pure, bind, Except.bind]
    constructor
    · rintro ⟨N, ⟨bs, hbs, rows, hnd, hmem, hN⟩, ha⟩
      simp only [Except.ok.injEq] at hbs
      subst hbs
      exact ⟨N, ⟨rows, hnd, fun row => (hmem row).trans (hrow row), hN⟩, ha⟩
    · rintro ⟨N, ⟨rows, hnd, hmem, hN⟩, ha⟩
      exact ⟨N, ⟨_, rfl, rows, hnd, fun row => (hmem row).trans (hrow row).symm, hN⟩, ha⟩
  show (∃ a b, XDenotes ι rate σ e vis true anyValue v j (mkCount sp x body) a ∧
    XDenotes ι rate σ e vis true anyValue v j (.var n) b ∧ xHolds true .eq a b) ↔ _
  simp only [xdenotes_var, xHolds_eq, hagg]
  constructor
  · rintro ⟨a, b, hN, ⟨c, hc, rfl⟩, rfl⟩
    exact ⟨c, hc, hN⟩
  · rintro ⟨c, hc, hN⟩
    exact ⟨_, _, hN, ⟨c, hc, rfl⟩, rfl⟩

/-! ## The anchors -/

/-- `formerly within w (B && tp(t))`: some timepoint of the window has `B`, and `t` is it. -/
theorem rsat_anchor {sp : Span} {w : WithinSpec} {win : Window} (hw : w.toSpec = .ok win)
    {B : Condition} {t : String} {v V : Valuation} {Bs : Nat → Prop}
    (hB : ∀ v' k, AgreeOff pre v v' → (RSat ι rate σ e (fun _ => True) v' k B ↔ Bs k))
    (hV : AgreeOff pre v V) (j : Nat) :
    RSat ι rate σ e (fun _ => True) V j (mkFormerly sp w (mkAnd sp B (mkTp sp t))) ↔
      ∃ k, k ≤ j ∧ InWindow rate σ j k win ∧ Bs k ∧ V t = some (.tp k) := by
  rw [rsat_mkFormerly hw]
  simp only [rsat_mkAnd, rsat_mkTp, true_and, hB V _ hV]

/-- `formerly within w (μ && tp(t))`: some visible timepoint of the window is `t`. -/
theorem rsat_muAnchor {μ : Span → Condition} {Vis : Nat → Prop}
    (hμ : ∀ sp v k, RSat ι rate σ e (fun _ => True) v k (μ sp) ↔ Vis k)
    {sp : Span} {w : WithinSpec} {win : Window} (hw : w.toSpec = .ok win) {t : String}
    (V : Valuation) (j : Nat) :
    RSat ι rate σ e (fun _ => True) V j (mkFormerly sp w (mkAnd sp (μ sp) (mkTp sp t))) ↔
      ∃ m, m ≤ j ∧ InWindow rate σ j m win ∧ Vis m ∧ V t = some (.tp m) := by
  rw [rsat_mkFormerly hw]
  simp only [rsat_mkAnd, rsat_mkTp, true_and, hμ]

/-! ## `previous` -/

/-- **The `previous` encoding**: some timepoint `k < j` of the window has the guarded body, and
no visible timepoint strictly between `k` and `j` is in the window. -/
theorem rsat_encodePrevious {μ : Span → Condition} {Vis : Nat → Prop}
    (hμ : ∀ sp v k, RSat ι rate σ e (fun _ => True) v k (μ sp) ↔ Vis k)
    {sp : Span} {w : WithinSpec} {win : Window} (hw : w.toSpec = .ok win) {B : Condition}
    {ti tj tk : String} (hti : hasPrefix pre ti = true) (htj : hasPrefix pre tj = true)
    (htk : hasPrefix pre tk = true) (hij : ti ≠ tj) (hik : ti ≠ tk) (hjk : tj ≠ tk)
    {v : Valuation} {Bs : Nat → Prop}
    (hB : ∀ v' k, AgreeOff pre v v' → (RSat ι rate σ e (fun _ => True) v' k B ↔ Bs k)) (j : Nat) :
    RSat ι rate σ e (fun _ => True) v j (encodePrevious μ sp w B ti tj tk) ↔
      ∃ k, k < j ∧ InWindow rate σ j k win ∧ Bs k ∧
        ¬ ∃ m, k < m ∧ m < j ∧ InWindow rate σ j m win ∧ Vis m := by
  simp only [encodePrevious, rsat_mkExistsTp]
  -- The conjuncts, under the valuation that binds `ti` and `tj`.
  have between : ∀ k, ∀ V : Valuation, AgreeOff pre v V → V ti = some (.tp j) →
      V tj = some (.tp k) → Bs k → k ≤ j → InWindow rate σ j k win →
      (RSat ι rate σ e (fun _ => True) V j (mkExistsTp sp tk (mkAnds sp
        [mkFormerly sp w (mkAnd sp (μ sp) (mkTp sp tk)), mkFormerly sp w (mkAnd sp B (mkTp sp tj)),
          mkTp sp ti, mkCmp sp .lt tj tk, mkCmp sp .lt tk ti])) ↔
        ∃ m, k < m ∧ m < j ∧ InWindow rate σ j m win ∧ Vis m) := by
    intro k V hV hVi hVj hBk hkj hiw
    rw [rsat_mkExistsTp]
    constructor
    · rintro ⟨w₃, h⟩
      rw [rsat_mkAnds] at h
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq] at h
      obtain ⟨hf, _, _, hlt₁, hlt₂⟩ := h
      obtain ⟨m, hmj, hiwm, hvm, hm⟩ := (rsat_muAnchor hμ hw _ j).mp hf
      simp only [Valuation.bind, if_pos, Option.some.injEq] at hm
      subst hm
      have hVk' : (V.bind tk (.tp m)) tj = some (.tp k) := by simp [Valuation.bind, hjk, hVj]
      have hVi' : (V.bind tk (.tp m)) ti = some (.tp j) := by simp [Valuation.bind, hik, hVi]
      have hVt : (V.bind tk (.tp m)) tk = some (.tp m) := by simp [Valuation.bind]
      rw [rsat_mkCmp_tp hVk' hVt, xHolds_tp_lt] at hlt₁
      rw [rsat_mkCmp_tp hVt hVi', xHolds_tp_lt] at hlt₂
      exact ⟨m, hlt₁, hlt₂, hiwm, hvm⟩
    · rintro ⟨m, hkm, hmj, hiwm, hvm⟩
      refine ⟨.tp m, ?_⟩
      have hVk' : (V.bind tk (.tp m)) tj = some (.tp k) := by simp [Valuation.bind, hjk, hVj]
      have hVi' : (V.bind tk (.tp m)) ti = some (.tp j) := by simp [Valuation.bind, hik, hVi]
      have hVt : (V.bind tk (.tp m)) tk = some (.tp m) := by simp [Valuation.bind]
      rw [rsat_mkAnds]
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
      refine ⟨(rsat_muAnchor hμ hw _ j).mpr ⟨m, by omega, hiwm, hvm, hVt⟩,
        (rsat_anchor hw hB (hV.bind htk _) j).mpr ⟨k, hkj, hiw, hBk, hVk'⟩,
        (rsat_mkTp _ _ _ _).mpr hVi', ?_, ?_⟩
      · rw [rsat_mkCmp_tp hVk' hVt, xHolds_tp_lt]; exact hkm
      · rw [rsat_mkCmp_tp hVt hVi', xHolds_tp_lt]; exact hmj
  constructor
  · rintro ⟨w₁, w₂, h⟩
    rw [rsat_mkAnds] at h
    simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq] at h
    obtain ⟨hti', ha, hlt, hnb⟩ := h
    have hA : AgreeOff pre v ((v.bind ti w₁).bind tj w₂) := ((AgreeOff.refl pre v).bind hti w₁).bind htj w₂
    have hVi : ((v.bind ti w₁).bind tj w₂) ti = some w₁ := by simp [Valuation.bind, hij]
    have hVj : ((v.bind ti w₁).bind tj w₂) tj = some w₂ := by simp [Valuation.bind]
    rw [rsat_mkTp, hVi] at hti'
    cases hti'
    obtain ⟨k, hkj, hiw, hBk, hk⟩ := (rsat_anchor hw hB hA j).mp ha
    rw [hVj] at hk
    cases hk
    rw [rsat_mkCmp_tp hVj hVi, xHolds_tp_lt] at hlt
    rw [rsat_mkNot, between k _ hA hVi hVj hBk hkj hiw] at hnb
    exact ⟨k, hlt, hiw, hBk, hnb⟩
  · rintro ⟨k, hkj, hiw, hBk, hno⟩
    refine ⟨.tp j, .tp k, ?_⟩
    have hA : AgreeOff pre v ((v.bind ti (.tp j)).bind tj (.tp k)) :=
      ((AgreeOff.refl pre v).bind hti _).bind htj _
    have hVi : ((v.bind ti (.tp j)).bind tj (.tp k)) ti = some (.tp j) := by simp [Valuation.bind, hij]
    have hVj : ((v.bind ti (.tp j)).bind tj (.tp k)) tj = some (.tp k) := by simp [Valuation.bind]
    rw [rsat_mkAnds]
    simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
    refine ⟨(rsat_mkTp _ _ _ _).mpr hVi, (rsat_anchor hw hB hA j).mpr ⟨k, by omega, hiw, hBk, hVj⟩,
      ?_, ?_⟩
    · rw [rsat_mkCmp_tp hVj hVi, xHolds_tp_lt]; exact hkj
    · rw [rsat_mkNot, between k _ hA hVi hVj hBk (by omega) hiw]; exact hno

/-! ## `since` -/

/-- The number of timepoints up to `j` that satisfy `Q`. -/
noncomputable def countUpTo (j : Nat) (Q : Nat → Prop) : Int :=
  (((List.range (j + 1)).filter fun m => @decide (Q m) (Classical.propDecidable _)).length : Int)

theorem countUpTo_nonneg (j : Nat) (Q : Nat → Prop) : 0 ≤ countUpTo j Q := by
  unfold countUpTo; omega

theorem countUpTo_le_length {σ : Trace} {j : Nat} (hj : j < σ.length) (Q : Nat → Prop) :
    countUpTo j Q ≤ σ.length := by
  unfold countUpTo
  have := length_filter_range_le (j + 1) (fun m => @decide (Q m) (Classical.propDecidable _))
  omega

theorem countUpTo_and_eq {j : Nat} {Q L : Nat → Prop} :
    countUpTo j (fun m => Q m ∧ L m) = countUpTo j Q ↔ ∀ m, m ≤ j → Q m → L m := by
  unfold countUpTo
  rw [Int.ofNat_inj]
  have := length_filter_and_eq (fun m => @decide (Q m) (Classical.propDecidable _))
    (fun m => @decide (L m) (Classical.propDecidable _)) (List.range (j + 1))
  have hc : (fun m => @decide (Q m ∧ L m) (Classical.propDecidable _)) =
      (fun m => @decide (Q m) (Classical.propDecidable _) && @decide (L m) (Classical.propDecidable _)) := by
    funext m
    by_cases hq : Q m <;> by_cases hl : L m <;> simp [hq, hl]
  rw [hc, this]
  simp only [List.mem_range, decide_eq_true_eq]
  exact ⟨fun h m hm => h m (by omega), fun h m hm => h m (by omega)⟩

/-- The range of the `since` encoding's counts, `R(t)`, with the count's own first conjunct
`formerly within w (D && tp(t))`: the rows are the timepoints `m ∈ (k, j]` of the window at
which `D` holds. -/
theorem rsat_sinceRange {sp : Span} {w : WithinSpec} {win : Window} (hw : w.toSpec = .ok win)
    {a D : Condition} {ti tj t : String} (ht : hasPrefix pre t = true) (hti : t ≠ ti)
    (htj : t ≠ tj) {v V : Valuation} (hV : AgreeOff pre v V) {As Ds : Nat → Prop}
    (ha : ∀ v' k, AgreeOff pre v v' → (RSat ι rate σ e (fun _ => True) v' k a ↔ As k))
    (hD : ∀ v' m, AgreeOff pre v v' → (RSat ι rate σ e (fun _ => True) v' m D ↔ Ds m))
    {j k : Nat} (hVi : V ti = some (.tp j)) (hVj : V tj = some (.tp k)) (hk : k ≤ j)
    (hiw : InWindow rate σ j k win) (hAk : As k) (r₀ : TVal) :
    RSat ι rate σ e (fun _ => True) (V.bind t r₀) j (mkAnds sp
      (mkFormerly sp w (mkAnd sp D (mkTp sp t)) ::
        [mkFormerly sp w (mkAnd sp a (mkTp sp tj)), mkTp sp ti, mkCmp sp .lt tj t, mkCmp sp .le t ti])) ↔
      ∃ m, r₀ = .tp m ∧ (m ≤ j ∧ InWindow rate σ j m win ∧ Ds m ∧ k < m) := by
  have hV' : AgreeOff pre v (V.bind t r₀) := hV.bind ht r₀
  have hVi' : (V.bind t r₀) ti = some (.tp j) := by simp [Valuation.bind, Ne.symm hti, hVi]
  have hVj' : (V.bind t r₀) tj = some (.tp k) := by simp [Valuation.bind, Ne.symm htj, hVj]
  have hVt : (V.bind t r₀) t = some r₀ := by simp [Valuation.bind]
  rw [rsat_mkAnds]
  simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
  constructor
  · rintro ⟨hf, _, _, hlt, hle⟩
    obtain ⟨m, hmj, hiwm, hDm, hm⟩ := (rsat_anchor hw hD hV' j).mp hf
    rw [hVt, Option.some.injEq] at hm
    subst hm
    rw [rsat_mkCmp_tp hVj' hVt, xHolds_tp_lt] at hlt
    exact ⟨m, rfl, hmj, hiwm, hDm, hlt⟩
  · rintro ⟨m, rfl, hmj, hiwm, hDm, hkm⟩
    refine ⟨(rsat_anchor hw hD hV' j).mpr ⟨m, hmj, hiwm, hDm, hVt⟩,
      (rsat_anchor hw ha hV' j).mpr ⟨k, hk, hiw, hAk, hVj'⟩, (rsat_mkTp _ _ _ _).mpr hVi', ?_, ?_⟩
    · rw [rsat_mkCmp_tp hVj' hVt, xHolds_tp_lt]; exact hkm
    · rw [rsat_mkCmp_tp hVt hVi', xHolds_tp_le]; exact hmj

/-- One count of the `since` encoding, `(count t. where formerly within w (D && tp(t)) && R(t)) ==
n`: `n` holds the number of timepoints of `(k, j]` in the window at which `D` holds. -/
theorem rsat_sinceCount {sp : Span} {w : WithinSpec} {win : Window} (hw : w.toSpec = .ok win)
    {a D : Condition} {ti tj t n : String} (ht : hasPrefix pre t = true) (hti : t ≠ ti)
    (htj : t ≠ tj) {v V : Valuation} (hV : AgreeOff pre v V) {As Ds : Nat → Prop}
    (ha : ∀ v' k, AgreeOff pre v v' → (RSat ι rate σ e (fun _ => True) v' k a ↔ As k))
    (hD : ∀ v' m, AgreeOff pre v v' → (RSat ι rate σ e (fun _ => True) v' m D ↔ Ds m))
    {j k : Nat} (hVi : V ti = some (.tp j)) (hVj : V tj = some (.tp k)) (hk : k ≤ j)
    (hiw : InWindow rate σ j k win) (hAk : As k) {c : TVal} (hVn : V n = some c)
    (hlen : (σ.length : Int) ≤ Int64.MAX) :
    RSat ι rate σ e (fun _ => True) V j (mkAggEq sp (mkCount sp t (mkAnds sp
      (mkFormerly sp w (mkAnd sp D (mkTp sp t)) ::
        [mkFormerly sp w (mkAnd sp a (mkTp sp tj)), mkTp sp ti, mkCmp sp .lt tj t, mkCmp sp .le t ti]))) n) ↔
      CVal.ofTVal c = .num (countUpTo j fun m => m ≤ j ∧ InWindow rate σ j m win ∧ Ds m ∧ k < m) := by
  rw [rsat_mkAggEq_count]
  have hj := inWindow_lt_length hiw
  have key : ∀ N : Int, (∃ rows : List (List TVal), rows.Nodup ∧
      (∀ row, row ∈ rows ↔ ∃ r₀, row = [r₀] ∧ RSat ι rate σ e (fun _ => True) (V.bind t r₀) j (mkAnds sp
        (mkFormerly sp w (mkAnd sp D (mkTp sp t)) ::
          [mkFormerly sp w (mkAnd sp a (mkTp sp tj)), mkTp sp ti, mkCmp sp .lt tj t, mkCmp sp .le t ti]))) ∧
      N = rows.length) ↔
      N = countUpTo j fun m => m ≤ j ∧ InWindow rate σ j m win ∧ Ds m ∧ k < m := by
    intro N
    refine rows_card (L := j + 1) (fun m => @decide_eq_true_iff _ (Classical.propDecidable _)) (fun row => ?_)
      (fun m hm => by omega)
    simp only [rsat_sinceRange hw ht hti htj hV ha hD hVi hVj hk hiw hAk]
    constructor
    · rintro ⟨r₀, rfl, m, rfl, hq⟩; exact ⟨m, rfl, hq⟩
    · rintro ⟨m, rfl, hq⟩; exact ⟨_, rfl, m, rfl, hq⟩
  have hle := countUpTo_le_length hj (fun m => m ≤ j ∧ InWindow rate σ j m win ∧ Ds m ∧ k < m)
  have h0 := countUpTo_nonneg j (fun m => m ≤ j ∧ InWindow rate σ j m win ∧ Ds m ∧ k < m)
  simp only [key, hVn, Option.some.injEq, exists_eq_left', exists_eq_left]
  rw [aggregateValue_of_le h0 (by omega), Option.some.injEq]
  exact eq_comm

theorem countUpTo_congr {j : Nat} {Q Q' : Nat → Prop} (h : ∀ m, Q m ↔ Q' m) :
    countUpTo j Q = countUpTo j Q' := by
  have : Q = Q' := funext fun m => propext (h m)
  rw [this]

/-- **The general `since` encoding**: some timepoint `k ≤ j` of the window has the guarded
anchor, and the left holds at every visible timepoint of `(k, j]` in the window. -/
theorem rsat_encodeSince {μ : Span → Condition} {Vis : Nat → Prop}
    (hμ : ∀ sp v k, RSat ι rate σ e (fun _ => True) v k (μ sp) ↔ Vis k)
    {sp : Span} {w : WithinSpec} {win : Window} (hw : w.toSpec = .ok win) {l a : Condition}
    {ti tj tkAll tkLeft n1 n2 : String}
    (hfi : hasPrefix pre ti = true) (hfj : hasPrefix pre tj = true)
    (hfa : hasPrefix pre tkAll = true) (hfl : hasPrefix pre tkLeft = true)
    (hf1 : hasPrefix pre n1 = true) (hf2 : hasPrefix pre n2 = true)
    (hij : ti ≠ tj) (hi1 : ti ≠ n1) (hi2 : ti ≠ n2) (hj1 : tj ≠ n1) (hj2 : tj ≠ n2) (h12 : n1 ≠ n2)
    (hai : tkAll ≠ ti) (haj : tkAll ≠ tj) (hli : tkLeft ≠ ti) (hlj : tkLeft ≠ tj)
    (hlen : (σ.length : Int) ≤ Int64.MAX) {v : Valuation} {As Ls : Nat → Prop}
    (ha : ∀ v' k, AgreeOff pre v v' → (RSat ι rate σ e (fun _ => True) v' k a ↔ As k))
    (hl : ∀ v' k, AgreeOff pre v v' → (RSat ι rate σ e (fun _ => True) v' k l ↔ Ls k)) (j : Nat) :
    RSat ι rate σ e (fun _ => True) v j (encodeSince μ sp l w a ti tj tkAll tkLeft n1 n2) ↔
      ∃ k, k ≤ j ∧ InWindow rate σ j k win ∧ As k ∧
        ∀ m, k < m → m ≤ j → InWindow rate σ j m win → Vis m → Ls m := by
  have hD1 : ∀ v' m, AgreeOff pre v v' → (RSat ι rate σ e (fun _ => True) v' m (μ sp) ↔ Vis m) :=
    fun v' m _ => hμ sp v' m
  have hD2 : ∀ v' m, AgreeOff pre v v' →
      (RSat ι rate σ e (fun _ => True) v' m (mkAnd sp (μ sp) l) ↔ Vis m ∧ Ls m) :=
    fun v' m h => by rw [rsat_mkAnd, hμ, hl v' m h]
  simp only [encodeSince, rsat_mkExistsTp, rsat_mkExistsLong]
  -- The valuation that binds the four outer names.
  have facts : ∀ w₁ w₂ c₁ c₂ : TVal,
      let V := (((v.bind ti w₁).bind tj w₂).bind n1 c₁).bind n2 c₂
      AgreeOff pre v V ∧ V ti = some w₁ ∧ V tj = some w₂ ∧ V n1 = some c₁ ∧ V n2 = some c₂ := by
    intro w₁ w₂ c₁ c₂
    refine ⟨((((AgreeOff.refl pre v).bind hfi w₁).bind hfj w₂).bind hf1 c₁).bind hf2 c₂, ?_, ?_, ?_, ?_⟩ <;>
      simp [Valuation.bind, hij, hi1, hi2, hj1, hj2, h12]
  constructor
  · rintro ⟨w₁, w₂, c₁, c₂, h⟩
    obtain ⟨hA, hVi, hVj, hV1, hV2⟩ := facts w₁ w₂ c₁ c₂
    rw [rsat_mkAnds] at h
    simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq] at h
    obtain ⟨htp, hanc, hc1, hc2, heq⟩ := h
    rw [rsat_mkTp, hVi, Option.some.injEq] at htp
    subst htp
    obtain ⟨k, hkj, hiw, hAk, hk⟩ := (rsat_anchor hw ha hA j).mp hanc
    rw [hVj, Option.some.injEq] at hk
    subst hk
    rw [rsat_sinceCount hw hfa hai haj hA ha hD1 hVi hVj hkj hiw hAk hV1 hlen] at hc1
    rw [rsat_sinceCount hw hfl hli hlj hA ha hD2 hVi hVj hkj hiw hAk hV2 hlen] at hc2
    rw [rsat_mkCmp_eq] at heq
    obtain ⟨wa, wb, hwa, hwb, hab⟩ := heq
    rw [hV1, Option.some.injEq] at hwa
    rw [hV2, Option.some.injEq] at hwb
    subst hwa; subst hwb
    rw [hc1, hc2, CVal.num.injEq] at hab
    rw [countUpTo_congr (Q := fun m => m ≤ j ∧ InWindow rate σ j m win ∧ (Vis m ∧ Ls m) ∧ k < m)
      (Q' := fun m => (m ≤ j ∧ InWindow rate σ j m win ∧ Vis m ∧ k < m) ∧ Ls m)
      (fun m => ⟨fun ⟨h₁, h₂, ⟨h₃, h₄⟩, h₅⟩ => ⟨⟨h₁, h₂, h₃, h₅⟩, h₄⟩,
        fun ⟨⟨h₁, h₂, h₃, h₅⟩, h₄⟩ => ⟨h₁, h₂, ⟨h₃, h₄⟩, h₅⟩⟩)] at hab
    have hall := countUpTo_and_eq.mp hab.symm
    exact ⟨k, hkj, hiw, hAk, fun m hkm hmj hiwm hvm => hall m hmj ⟨hmj, hiwm, hvm, hkm⟩⟩
  · rintro ⟨k, hkj, hiw, hAk, hall⟩
    have hj := inWindow_lt_length hiw
    let N := countUpTo j fun m => m ≤ j ∧ InWindow rate σ j m win ∧ Vis m ∧ k < m
    have hN0 : 0 ≤ N := countUpTo_nonneg _ _
    have hNle : N ≤ Int64.MAX := by
      have := countUpTo_le_length hj (fun m => m ≤ j ∧ InWindow rate σ j m win ∧ Vis m ∧ k < m)
      omega
    refine ⟨.tp j, .tp k, longOf N, longOf N, ?_⟩
    obtain ⟨hA, hVi, hVj, hV1, hV2⟩ := facts (.tp j) (.tp k) (longOf N) (longOf N)
    rw [rsat_mkAnds]
    simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
    refine ⟨(rsat_mkTp _ _ _ _).mpr hVi, (rsat_anchor hw ha hA j).mpr ⟨k, hkj, hiw, hAk, hVj⟩, ?_, ?_, ?_⟩
    · rw [rsat_sinceCount hw hfa hai haj hA ha hD1 hVi hVj hkj hiw hAk hV1 hlen, ofTVal_longOf hN0 hNle]
    · rw [rsat_sinceCount hw hfl hli hlj hA ha hD2 hVi hVj hkj hiw hAk hV2 hlen, ofTVal_longOf hN0 hNle,
        CVal.num.injEq]
      rw [countUpTo_congr (Q := fun m => m ≤ j ∧ InWindow rate σ j m win ∧ (Vis m ∧ Ls m) ∧ k < m)
      (Q' := fun m => (m ≤ j ∧ InWindow rate σ j m win ∧ Vis m ∧ k < m) ∧ Ls m)
        (fun m => ⟨fun ⟨h₁, h₂, ⟨h₃, h₄⟩, h₅⟩ => ⟨⟨h₁, h₂, h₃, h₅⟩, h₄⟩,
        fun ⟨⟨h₁, h₂, h₃, h₅⟩, h₄⟩ => ⟨h₁, h₂, ⟨h₃, h₄⟩, h₅⟩⟩)]
      exact (countUpTo_and_eq.mpr fun m hmj ⟨_, hiwm, hvm, hkm⟩ => hall m hkm hmj hiwm hvm).symm
    · rw [rsat_mkCmp_eq]
      exact ⟨_, _, hV1, hV2, rfl⟩

end

end Dogwood.Thm.Frontend
