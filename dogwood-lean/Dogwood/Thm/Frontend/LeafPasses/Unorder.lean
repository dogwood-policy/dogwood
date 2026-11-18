import Dogwood.Thm.Frontend.LeafPasses.Basic
import Dogwood.Thm.Monitorable

/-!
# The executable form of a leaf

`LeafPasses.unorderTimepoints` turns every comparison that orders a `Timepoint` variable, or
computes with one, into `0 == 1`.

* On a leaf it changes nothing on, it is the identity (`unorderCond_eq_self`).
* **Under the sorted reading** (a `Timepoint` binder holds a timepoint, any other binder a
  value), the executable form with timepoints ordered (`ord = o`, any `o`) means what the authored
  leaf means with timepoints unordered, as in the specification (`xsat_unorder`). So the pass makes
  the crate's position-ordered timepoints behave as the specification says.
* **Under the specification's own reading**, where `exists` ranges over every value whatever its
  declared type, the pass does not preserve satisfaction: `exists (x: Timepoint). x < 5` holds,
  and its executable form does not (`unorder_not_sat_preserving`). Validity makes the witnesses
  sorted (`Dogwood.Thm.sat_exist_sorted`), which is where the two readings meet.
* Under the relation the relativized leaves are read under (`RSat`, timepoints ordered), the pass
  changes the meaning of a leaf that orders timepoints (`unorder_changes_rsat`): it is meant to.
-/

namespace Dogwood.Thm.Frontend

open Dogwood.Frontend Dogwood.Frontend.LeafPasses Surface.Temporal
open Dogwood.Spec (Event Trace TickRate TimePoint)
open Dogwood.Spec.Temporal (Valuation ImplChoices Sat Denotes Total Formula Aggregate CVal CmpOp TVal Binder
  domainNames BinderType readLong)

/-! ## The identity on a leaf with no timepoint ordering -/

mutual

theorem unorderCond_eq_self : (c : Condition) → (Γ : TpScope) → unorderFree Γ c = true →
    unorderCond Γ c = c
  | ⟨sp, .and l r⟩, Γ, h => by
    simp only [unorderFree, unorderFreeKind, Bool.and_eq_true] at h
    simp only [unorderCond, unorderKind, unorderCond_eq_self l Γ h.1, unorderCond_eq_self r Γ h.2]
  | ⟨sp, .or l r⟩, Γ, h => by
    simp only [unorderFree, unorderFreeKind, Bool.and_eq_true] at h
    simp only [unorderCond, unorderKind, unorderCond_eq_self l Γ h.1, unorderCond_eq_self r Γ h.2]
  | ⟨sp, .not c⟩, Γ, h => by
    simp only [unorderFree, unorderFreeKind] at h
    simp only [unorderCond, unorderKind, unorderCond_eq_self c Γ h]
  | ⟨sp, .formerly w c⟩, Γ, h => by
    simp only [unorderFree, unorderFreeKind] at h
    simp only [unorderCond, unorderKind, unorderCond_eq_self c Γ h]
  | ⟨sp, .previous w c⟩, Γ, h => by
    simp only [unorderFree, unorderFreeKind] at h
    simp only [unorderCond, unorderKind, unorderCond_eq_self c Γ h]
  | ⟨sp, .since l w r⟩, Γ, h => by
    simp only [unorderFree, unorderFreeKind, Bool.and_eq_true] at h
    simp only [unorderCond, unorderKind, unorderCond_eq_self l Γ h.1, unorderCond_eq_self r Γ h.2]
  | ⟨sp, .exists x c⟩, Γ, h => by
    simp only [unorderFree, unorderFreeKind] at h
    simp only [unorderCond, unorderKind, unorderCond_eq_self c _ h]
  | ⟨sp, .comparison op l r⟩, Γ, h => by
    simp only [unorderFree, unorderFreeKind, Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨⟨hc, hl⟩, hr⟩ := h
    simp only [unorderCond, unorderKind, unorderTerm_eq_self l Γ hl, unorderTerm_eq_self r Γ hr, hc]
    rfl
  | ⟨sp, .predicate _⟩, Γ, _ => rfl
  | ⟨sp, .tp _⟩, Γ, _ => rfl
  | ⟨sp, .call _⟩, Γ, _ => rfl
  | ⟨sp, .sigilRef _ _⟩, Γ, _ => rfl
  | ⟨sp, .refine _ _ _⟩, Γ, _ => rfl

theorem unorderTerm_eq_self : (t : Surface.Temporal.Term) → (Γ : TpScope) → unorderFreeTerm Γ t = true →
    unorderTerm Γ t = t
  | .agg ⟨sp, k⟩, Γ, h => by
    simp only [unorderFreeTerm] at h
    simp only [unorderTerm, unorderAgg, unorderAggKind_eq_self k Γ h]
  | .arith op l r, Γ, h => by
    simp only [unorderFreeTerm, Bool.and_eq_true] at h
    simp only [unorderTerm, unorderTerm_eq_self l Γ h.1, unorderTerm_eq_self r Γ h.2]
  | .entity _ _, _, _ => rfl
  | .integer _, _, _ => rfl
  | .decimal _, _, _ => rfl
  | .string _, _, _ => rfl
  | .bool _, _, _ => rfl
  | .contextField _, _, _ => rfl
  | .scopeField _, _, _ => rfl
  | .var _, _, _ => rfl
  | .wildcard, _, _ => rfl
  | .array _, _, _ => rfl
  | .paramRef _, _, _ => rfl
  | .binderRef _, _, _ => rfl

theorem unorderAggKind_eq_self : (k : AggExprKind) → (Γ : TpScope) → unorderFreeAgg Γ k = true →
    unorderAggKind Γ k = k
  | .count vs b, Γ, h => by
    simp only [unorderFreeAgg] at h
    simp only [unorderAggKind, unorderCond_eq_self b _ h]
  | .sum v vs b, Γ, h => by
    simp only [unorderFreeAgg] at h
    simp only [unorderAggKind, unorderCond_eq_self b _ h]
  | .call _, _, _ => rfl

end

theorem unorderTimepoints_eq_self {c : Condition} (h : unorderFree [] c = true) :
    unorderTimepoints c = .ok c := by
  simp [unorderTimepoints, unorderCond_eq_self c [] h, pure, Except.pure]

/-! ## The executable form under the sorted reading -/

/-- The valuation gives each variable a value of the sort its innermost binder in `Γ` declares: a
timepoint to a `Timepoint` binder, a value to any other, and a value to a free variable. -/
def ScopeSorted (Γ : TpScope) (v : Valuation) : Prop :=
  ∀ x w, v x = some w → ((∃ k, w = .tp k) ↔ isTimepoint Γ x = true)

theorem ofTVal_eq_tp {w : TVal} {k : Nat} : CVal.ofTVal w = .tp k ↔ w = .tp k := by
  cases w with
  | tp m => simp [CVal.ofTVal]
  | val u =>
    simp only [CVal.ofTVal, reduceCtorEq, iff_false]
    unfold CVal.ofValue; split <;> simp

theorem readLong_ne_tp {f : Int → Option Int} {n : Int} {k : Nat} : readLong f n ≠ some (.tp k) := by
  unfold readLong; split
  · simp
  · cases f n <;> simp

theorem eval_eq_tp {e : Event} {v : Valuation} {t : Dogwood.Spec.Temporal.Term} {k : Nat}
    (h : t.eval? e v = some (.tp k)) : ∃ x, t = .var x ∧ v x = some (.tp k) := by
  cases t <;> simp [Dogwood.Spec.Temporal.Term.eval?] at h
  exact ⟨_, rfl, h⟩

theorem toSpec_eq_var {t : Surface.Temporal.Term} {x : String} (h : t.toSpec = .ok (.var x)) :
    t = .var x := by
  cases t with
  | var y => simp [Surface.Temporal.Term.toSpec, pure, Except.pure] at h; rw [h]
  | scopeField p =>
    rcases p with _ | ⟨hd, rest⟩
    · simp [Surface.Temporal.Term.toSpec, throw, throwThe, MonadExceptOf.throw] at h
    · by_cases h1 : hd = "principal"
      · subst h1; simp [Surface.Temporal.Term.toSpec, pure, Except.pure] at h
      · by_cases h2 : hd = "resource"
        · subst h2; simp [Surface.Temporal.Term.toSpec, pure, Except.pure] at h
        · simp [Surface.Temporal.Term.toSpec, h1, h2, throw, throwThe, MonadExceptOf.throw] at h
  | agg a =>
    obtain ⟨_, k⟩ := a
    simp only [Surface.Temporal.Term.toSpec, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨_, _, h⟩ := h; cases h
  | arith op l r =>
    simp only [Surface.Temporal.Term.toSpec, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨_, _, _, _, h⟩ := h; cases h
  | entity ty id =>
    simp only [Surface.Temporal.Term.toSpec, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨_, _, h⟩ := h; cases h
  | _ => simp [Surface.Temporal.Term.toSpec, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw] at h

section
variable {ι : ImplChoices} {rate : TickRate} {σ : Trace} {e : Event} {vis : Nat → Prop}

/-- Only a variable denotes a timepoint. -/
theorem xdenotes_tp {ord : Bool} {dom : Domain} {v : Valuation} {j : Nat} {t : Surface.Temporal.Term} {k : Nat}
    (h : XDenotes ι rate σ e vis ord dom v j t (.tp k)) : ∃ x, t = .var x ∧ v x = some (.tp k) := by
  match t, h with
  | .agg ⟨_, _⟩, ⟨_, _, hn⟩ => exact absurd hn readLong_ne_tp
  | .arith _ _ _, ⟨_, _, _, _, hn⟩ => exact absurd hn readLong_ne_tp
  | .entity _ _, ⟨t', ht, w, hw, hc⟩ | .integer _, ⟨t', ht, w, hw, hc⟩ | .decimal _, ⟨t', ht, w, hw, hc⟩
  | .string _, ⟨t', ht, w, hw, hc⟩ | .bool _, ⟨t', ht, w, hw, hc⟩
  | .contextField _, ⟨t', ht, w, hw, hc⟩ | .scopeField _, ⟨t', ht, w, hw, hc⟩
  | .var _, ⟨t', ht, w, hw, hc⟩ | .wildcard, ⟨t', ht, w, hw, hc⟩ | .array _, ⟨t', ht, w, hw, hc⟩
  | .paramRef _, ⟨t', ht, w, hw, hc⟩ | .binderRef _, ⟨t', ht, w, hw, hc⟩ =>
    have hw' : w = .tp k := ofTVal_eq_tp.mp hc.symm
    subst hw'
    obtain ⟨x, rfl, hx⟩ := eval_eq_tp hw
    exact ⟨x, toSpec_eq_var ht, hx⟩

theorem xdenotes_var {ord : Bool} {dom : Domain} {v : Valuation} {j : Nat} {x : String} {c : CVal} :
    XDenotes ι rate σ e vis ord dom v j (.var x) c ↔ ∃ w, v x = some w ∧ c = CVal.ofTVal w := by
  simp [XDenotes, Surface.Temporal.Term.toSpec, pure, Except.pure, Dogwood.Spec.Temporal.Term.eval?]

theorem isTimepointVar_unorderTerm (Γ : TpScope) (t : Surface.Temporal.Term) :
    isTimepointVar Γ (unorderTerm Γ t) = isTimepointVar Γ t := by
  cases t <;> rfl

theorem computes_unorderTerm (Γ : TpScope) : (t : Surface.Temporal.Term) →
    computesWithTimepoint Γ (unorderTerm Γ t) = computesWithTimepoint Γ t
  | .arith op l r => by
    simp only [unorderTerm, computesWithTimepoint, isTimepointVar_unorderTerm,
      computes_unorderTerm Γ l, computes_unorderTerm Γ r]
  | .agg _ => rfl
  | .entity _ _ | .integer _ | .decimal _ | .string _ | .bool _ | .contextField _ | .scopeField _
  | .var _ | .wildcard | .array _ | .paramRef _ | .binderRef _ => rfl

/-- A compound with a timepoint atom denotes nothing, under a sorted valuation. -/
theorem not_xdenotes_of_computes {ord : Bool} {dom : Domain} {Γ : TpScope} {v : Valuation} {j : Nat}
    (hv : ScopeSorted Γ v) : (t : Surface.Temporal.Term) → computesWithTimepoint Γ t = true →
    ∀ c, ¬ XDenotes ι rate σ e vis ord dom v j t c
  | .arith op l r, h, c, ⟨m, n, hl, hr, _⟩ => by
    simp only [computesWithTimepoint, Bool.or_eq_true] at h
    have atom : ∀ (t : Surface.Temporal.Term) (m : Int), isTimepointVar Γ t = true →
        ¬ XDenotes ι rate σ e vis ord dom v j t (.num m) := by
      intro t m ht hd
      cases t <;> simp only [isTimepointVar, reduceCtorEq] at ht
      case var x =>
        obtain ⟨w, hw, hc⟩ := xdenotes_var.mp hd
        obtain ⟨k, rfl⟩ := (hv x w hw).mpr ht
        simp [CVal.ofTVal] at hc
    rcases h with ((hl' | hr') | hl') | hr'
    · exact atom l m hl' hl
    · exact atom r n hr' hr
    · exact not_xdenotes_of_computes hv l hl' _ hl
    · exact not_xdenotes_of_computes hv r hr' _ hr
  | .agg _, h, _, _ => by simp [computesWithTimepoint] at h
  | .entity _ _, h, _, _ | .integer _, h, _, _ | .decimal _, h, _, _ | .string _, h, _, _
  | .bool _, h, _, _ | .contextField _, h, _, _ | .scopeField _, h, _, _ | .var _, h, _, _
  | .wildcard, h, _, _ | .array _, h, _, _ | .paramRef _, h, _, _ | .binderRef _, h, _, _ => by
    simp [computesWithTimepoint] at h

theorem holds_tp_left {op : CmpOp} (ho : LeafPasses.CmpOp.orders op = true) {k : Nat} {b : CVal} :
    ¬ op.Holds (.tp k) b := by
  cases op <;> simp_all [LeafPasses.CmpOp.orders, CmpOp.Holds]

theorem holds_tp_right {op : CmpOp} (ho : LeafPasses.CmpOp.orders op = true) {k : Nat} {a : CVal} :
    ¬ op.Holds a (.tp k) := by
  cases op <;> cases a <;> simp_all [LeafPasses.CmpOp.orders, CmpOp.Holds]

theorem tpOrders_spec {op : CmpOp} {a b : CVal} (h : tpOrders op a b) :
    LeafPasses.CmpOp.orders op = true ∧ (∃ m, a = .tp m) ∧ (∃ n, b = .tp n) := by
  cases op <;> cases a <;> cases b <;> simp_all [tpOrders, LeafPasses.CmpOp.orders]

theorem scopeSorted_bind {Γ : TpScope} {v : Valuation} {x : String} {ty : BinderType} {w : TVal}
    (hv : ScopeSorted Γ v) (hw : sortedValue ty w) :
    ScopeSorted ((x, ty == .timepoint) :: Γ) (v.bind x w) := by
  intro y u hu
  by_cases hy : y = x
  · subst hy
    simp only [Valuation.bind, if_pos, Option.some.injEq] at hu
    subst hu
    simp only [isTimepoint, List.find?_cons, beq_self_eq_true, beq_iff_eq]
    exact hw.symm
  · simp only [Valuation.bind, if_neg hy] at hu
    have hxy : (x == y) = false := by simp [Ne.symm hy]
    simp only [isTimepoint, List.find?_cons, hxy]
    exact hv y u hu

theorem bindAll_some {v : Valuation} : ∀ {xs : List String} {ws : List TVal}, ws.length = xs.length →
    ∀ {y : String} {w : TVal}, (v.bindAll xs ws) y = some w → (y, w) ∈ xs.zip ws ∨ (y ∉ xs ∧ v y = some w)
  | [], [], _, y, w, h => Or.inr ⟨by simp, h⟩
  | x :: xs, w' :: ws, hl, y, w, h => by
    simp only [Valuation.bindAll] at h
    rcases bindAll_some (v := v.bind x w') (xs := xs) (ws := ws) (by simpa using hl) h with hm | ⟨hn, hb⟩
    · exact Or.inl (by simp [hm])
    · by_cases hy : y = x
      · subst hy
        simp only [Valuation.bind, if_pos, Option.some.injEq] at hb
        subst hb
        exact Or.inl (by simp)
      · simp only [Valuation.bind, if_neg hy] at hb
        exact Or.inr ⟨by simp [hy, hn], hb⟩
  | [], _ :: _, hl, _, _, _ => by simp at hl
  | _ :: _, [], hl, _, _, _ => by simp at hl

theorem map_binding {vs : List TypedBinder} {bs : List Binder} (h : vs.mapM TypedBinder.toSpec = .ok bs) :
    vs.map binding = bs.map fun b => (b.name, b.ty == .timepoint) := by
  induction vs generalizing bs with
  | nil => simp [pure, Except.pure] at h; subst h; rfl
  | cons b vs ih =>
    simp only [List.mapM_cons, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨b', hb, bs', hbs, rfl⟩ := h
    obtain ⟨s, ty⟩ := b
    simp only [TypedBinder.toSpec, bind_eq_ok, pure_eq_ok] at hb
    obtain ⟨n, hn, rfl⟩ := hb
    cases s <;> simp [BinderSlot.toName, throw, throwThe, MonadExceptOf.throw, pure, Except.pure] at hn
    subst hn
    simp [ih hbs, binding]

theorem scopeSorted_bindAll {Γ : TpScope} {v : Valuation} {vs : List TypedBinder} {bs : List Binder}
    {row : List TVal} (hv : ScopeSorted Γ v) (hbs : vs.mapM TypedBinder.toSpec = .ok bs)
    (hlen : row.length = (domainNames bs).length) (hrow : RowIn sortedValue bs row) :
    ScopeSorted ((vs.map binding).reverse ++ Γ) (v.bindAll (domainNames bs) row) := by
  intro y w hw
  have hfind : isTimepoint ((vs.map binding).reverse ++ Γ) y =
      match bs.reverse.find? (·.name == y) with
      | some b => b.ty == .timepoint
      | none => isTimepoint Γ y := by
    rw [map_binding hbs, ← List.map_reverse]
    simp only [isTimepoint, List.find?_append, List.find?_map]
    have hc : ((fun x : String × Bool => x.fst == y) ∘ fun b : Binder => (b.name, b.ty == BinderType.timepoint)) =
        (·.name == y) := rfl
    rw [hc]
    cases bs.reverse.find? (·.name == y) <;> simp
  rw [hfind]
  rcases bindAll_some hlen hw with hm | ⟨hn, hvy⟩
  · have hs := hrow _ hm
    have hy : y ∈ domainNames bs := (List.of_mem_zip hm).1
    simp only [domainNames, Dogwood.Thm.mem_dedup, List.mem_map] at hy
    obtain ⟨b, hb, rfl⟩ := hy
    obtain ⟨b₀, hb₀⟩ : ∃ b₀, bs.reverse.find? (·.name == b.name) = some b₀ := by
      cases h : bs.reverse.find? (·.name == b.name) with
      | some b₀ => exact ⟨b₀, rfl⟩
      | none => exact absurd (List.find?_eq_none.mp h b (List.mem_reverse.mpr hb)) (by simp)
    simp only [columnType, hb₀, Option.map_some, Option.getD_some, sortedValue] at hs
    simp only [hb₀, beq_iff_eq]
    exact hs.symm
  · have hnone : bs.reverse.find? (·.name == y) = none := by
      apply List.find?_eq_none.mpr
      intro b hb hby
      apply hn
      simp only [domainNames, Dogwood.Thm.mem_dedup, List.mem_map]
      exact ⟨b, List.mem_reverse.mp hb, by simpa using hby⟩
    simp only [hnone]
    exact hv y w hvy

mutual

/-- **The executable form means the authored leaf, under the sorted reading.** -/
theorem xsat_unorder : (c : Condition) → (Γ : TpScope) → (v : Valuation) → ScopeSorted Γ v →
    (j : Nat) → (o : Bool) →
    (XSat ι rate σ e vis o sortedValue v j (unorderCond Γ c) ↔
      XSat ι rate σ e vis false sortedValue v j c)
  | ⟨sp, .and l r⟩, Γ, v, hv, j, o => by
    simp only [unorderCond, unorderKind, XSat, xsat_unorder l Γ v hv j o, xsat_unorder r Γ v hv j o]
  | ⟨sp, .or l r⟩, Γ, v, hv, j, o => by
    simp only [unorderCond, unorderKind, XSat, xsat_unorder l Γ v hv j o, xsat_unorder r Γ v hv j o]
  | ⟨sp, .not c⟩, Γ, v, hv, j, o => by
    simp only [unorderCond, unorderKind, XSat, xsat_unorder c Γ v hv j o]
  | ⟨sp, .formerly w c⟩, Γ, v, hv, j, o => by
    simp only [unorderCond, unorderKind, XSat]
    exact exists_congr fun win => and_congr_right' (exists_congr fun k =>
      and_congr_right' (and_congr_right' (and_congr_right' (xsat_unorder c Γ v hv k o))))
  | ⟨sp, .previous w c⟩, Γ, v, hv, j, o => by
    simp only [unorderCond, unorderKind, XSat]
    exact exists_congr fun win => and_congr_right' (exists_congr fun k =>
      and_congr_right' (and_congr_right' (and_congr_right' (and_congr_right'
        (xsat_unorder c Γ v hv k o)))))
  | ⟨sp, .since l w r⟩, Γ, v, hv, j, o => by
    simp only [unorderCond, unorderKind, XSat]
    exact exists_congr fun win => and_congr_right' (exists_congr fun k =>
      and_congr_right' (and_congr_right' (and_congr_right' (and_congr (xsat_unorder r Γ v hv k o)
        (forall_congr' fun k' => imp_congr_right fun _ => imp_congr_right fun _ =>
          imp_congr_right fun _ => xsat_unorder l Γ v hv k' o)))))
  | ⟨sp, .exists ⟨s, ty⟩ c⟩, Γ, v, hv, j, o => by
    simp only [unorderCond, unorderKind, XSat]
    cases s with
    | name x =>
      simp only [BinderSlot.toName, pure, Except.pure, Except.ok.injEq, exists_eq_left']
      exact exists_congr fun w => and_congr_right fun hw =>
        xsat_unorder c ((x, ty == .timepoint) :: Γ) _ (scopeSorted_bind hv hw) j o
    | paramRef p => simp [BinderSlot.toName, throw, throwThe, MonadExceptOf.throw]
    | binderRef b => simp [BinderSlot.toName, throw, throwThe, MonadExceptOf.throw]
  | ⟨sp, .comparison op l r⟩, Γ, v, hv, j, o => by
    simp only [unorderCond, unorderKind]
    split
    · rename_i hc
      have hlhs : ¬ XSat ι rate σ e vis o sortedValue v j (constantFalse sp) := by
        rintro ⟨a, b, ha, hb, hh⟩
        simp only [XDenotes, Surface.Temporal.Term.toSpec, pure, Except.pure, Except.ok.injEq,
          exists_eq_left', Dogwood.Spec.Temporal.Term.eval?, Option.some.injEq] at ha hb
        obtain ⟨_, rfl, rfl⟩ := ha
        obtain ⟨_, rfl, rfl⟩ := hb
        rcases hh with hh | ⟨_, hh⟩
        · simp [CmpOp.Holds, CVal.ofTVal, CVal.ofValue] at hh
        · simp [tpOrders] at hh
      simp only [hlhs, false_iff]
      rintro ⟨a, b, ha, hb, hh⟩
      simp only [unordersComparison, computes_unorderTerm, isTimepointVar_unorderTerm,
        Bool.or_eq_true, Bool.and_eq_true] at hc
      have hh' : op.Holds a b := by simpa [xHolds] using hh
      rcases hc with (hcl | hcr) | ⟨hord, hl | hr⟩
      · exact not_xdenotes_of_computes hv l hcl a ha
      · exact not_xdenotes_of_computes hv r hcr b hb
      · cases l <;> simp only [isTimepointVar, reduceCtorEq] at hl
        case var x =>
          obtain ⟨w, hw, rfl⟩ := xdenotes_var.mp ha
          obtain ⟨k, rfl⟩ := (hv x w hw).mpr hl
          exact holds_tp_left hord hh'
      · cases r <;> simp only [isTimepointVar, reduceCtorEq] at hr
        case var x =>
          obtain ⟨w, hw, rfl⟩ := xdenotes_var.mp hb
          obtain ⟨k, rfl⟩ := (hv x w hw).mpr hr
          exact holds_tp_right hord hh'
    · rename_i hc
      simp only [XSat]
      refine exists_congr fun a => exists_congr fun b => ?_
      rw [xdenotes_unorder l Γ v hv j o a, xdenotes_unorder r Γ v hv j o b]
      constructor
      · rintro ⟨ha, hb, hh⟩
        refine ⟨ha, hb, Or.inl ?_⟩
        rcases hh with hh | ⟨_, ht⟩
        · exact hh
        · exfalso
          obtain ⟨hord, ⟨m, rfl⟩, -⟩ := tpOrders_spec ht
          obtain ⟨x, rfl, hx⟩ := xdenotes_tp ha
          apply hc
          simp only [unordersComparison, isTimepointVar_unorderTerm, hord, Bool.true_and,
            Bool.or_eq_true]
          exact Or.inr (Or.inl ((hv x _ hx).mp ⟨m, rfl⟩))
      · rintro ⟨ha, hb, hh⟩
        exact ⟨ha, hb, Or.inl (by simpa [xHolds] using hh)⟩
  | ⟨sp, .predicate ⟨_, _, _, _, _⟩⟩, Γ, v, hv, j, o => Iff.rfl
  | ⟨sp, .tp _⟩, Γ, v, hv, j, o => Iff.rfl
  | ⟨sp, .call _⟩, Γ, v, hv, j, o => Iff.rfl
  | ⟨sp, .sigilRef _ _⟩, Γ, v, hv, j, o => Iff.rfl
  | ⟨sp, .refine _ _ _⟩, Γ, v, hv, j, o => Iff.rfl

theorem xdenotes_unorder : (t : Surface.Temporal.Term) → (Γ : TpScope) → (v : Valuation) →
    ScopeSorted Γ v → (j : Nat) → (o : Bool) → (c : CVal) →
    (XDenotes ι rate σ e vis o sortedValue v j (unorderTerm Γ t) c ↔
      XDenotes ι rate σ e vis false sortedValue v j t c)
  | .agg ⟨sp, k⟩, Γ, v, hv, j, o, c => by
    simp only [unorderTerm, unorderAgg, XDenotes]
    exact exists_congr fun n => and_congr_left' (xtotal_unorder k Γ v hv j o n)
  | .arith op l r, Γ, v, hv, j, o, c => by
    simp only [unorderTerm, XDenotes]
    exact exists_congr fun m => exists_congr fun n =>
      and_congr (xdenotes_unorder l Γ v hv j o _) (and_congr_left' (xdenotes_unorder r Γ v hv j o _))
  | .entity _ _, _, _, _, _, _, _ | .integer _, _, _, _, _, _, _ | .decimal _, _, _, _, _, _, _
  | .string _, _, _, _, _, _, _ | .bool _, _, _, _, _, _, _ | .contextField _, _, _, _, _, _, _
  | .scopeField _, _, _, _, _, _, _ | .var _, _, _, _, _, _, _ | .wildcard, _, _, _, _, _, _
  | .array _, _, _, _, _, _, _ | .paramRef _, _, _, _, _, _, _ | .binderRef _, _, _, _, _, _, _ => Iff.rfl

theorem xtotal_unorder : (k : AggExprKind) → (Γ : TpScope) → (v : Valuation) → ScopeSorted Γ v →
    (j : Nat) → (o : Bool) → (n : Int) →
    (XTotal ι rate σ e vis o sortedValue v j (unorderAggKind Γ k) n ↔
      XTotal ι rate σ e vis false sortedValue v j k n)
  | .count vs b, Γ, v, hv, j, o, n => by
    simp only [unorderAggKind, XTotal]
    refine exists_congr fun bs => and_congr_right fun hbs => exists_congr fun rows =>
      and_congr_right' (and_congr_left' (forall_congr' fun row => iff_congr Iff.rfl ?_))
    constructor
    · rintro ⟨hl, hr, hs⟩
      exact ⟨hl, hr, (xsat_unorder b _ _ (scopeSorted_bindAll hv hbs hl hr) j o).mp hs⟩
    · rintro ⟨hl, hr, hs⟩
      exact ⟨hl, hr, (xsat_unorder b _ _ (scopeSorted_bindAll hv hbs hl hr) j o).mpr hs⟩
  | .sum s vs b, Γ, v, hv, j, o, n => by
    simp only [unorderAggKind, XTotal]
    refine exists_congr fun x => exists_congr fun bs => and_congr_right' (and_congr_right fun hbs =>
      exists_congr fun rows =>
      and_congr_right' (and_congr_left' (forall_congr' fun row => iff_congr Iff.rfl ?_)))
    constructor
    · rintro ⟨hl, hr, hs⟩
      exact ⟨hl, hr, (xsat_unorder b _ _ (scopeSorted_bindAll hv hbs hl hr) j o).mp hs⟩
    · rintro ⟨hl, hr, hs⟩
      exact ⟨hl, hr, (xsat_unorder b _ _ (scopeSorted_bindAll hv hbs hl hr) j o).mpr hs⟩
  | .call _, _, _, _, _, _, _ => Iff.rfl

end

end

/-! ## Counterexamples -/

section
variable (ι : ImplChoices) (rate : TickRate) (σ : Trace) (e : Event) (vis : Nat → Prop)

/-- The leaf `exists (x: Timepoint). x < 5`. -/
def tpBelowFive : Condition :=
  ⟨⟨0, 0⟩, .exists ⟨.name "x", .timepoint⟩ ⟨⟨0, 0⟩, .comparison .lt (.var "x") (.integer 5)⟩⟩

/-- **`unorderTimepoints` does not preserve the specification's satisfaction** in general. In the
specification, `exists` ranges over every value, whatever the binder's declared type, so
`exists (x: Timepoint). x < 5` holds (take `x = 0`); its executable form
`exists (x: Timepoint). 0 == 1` holds nowhere, under either ordering. The pass is correct on the
sorted reading (`xsat_unorder`), which validity provides; the leaf is invalid (it orders a
timepoint). -/
theorem unorder_not_sat_preserving :
    (∃ φ, tpBelowFive.toFormula = .ok φ ∧ Sat ι rate σ e vis Valuation.empty 0 φ) ∧
    ∀ o, ¬ XSat ι rate σ e vis o anyValue Valuation.empty 0 (unorderCond [] tpBelowFive) := by
  constructor
  · refine ⟨.exist ⟨"x", .timepoint⟩ (.cmp .lt (.var "x") (.long 5)), rfl, ?_⟩
    refine ⟨.val (.prim (.int 0)), .num 0, .num 5, ?_, ?_, ?_⟩
    · exact ⟨_, rfl, rfl⟩
    · exact ⟨_, rfl, rfl⟩
    · show (0 : Int) < 5; decide
  · intro o h
    obtain ⟨x, _, w, _, a, b, ha, hb, hh⟩ := h
    simp only [XDenotes, Surface.Temporal.Term.toSpec, pure, Except.pure, Except.ok.injEq,
      exists_eq_left', Dogwood.Spec.Temporal.Term.eval?, Option.some.injEq] at ha hb
    obtain ⟨_, rfl, rfl⟩ := ha
    obtain ⟨_, rfl, rfl⟩ := hb
    rcases hh with hh | ⟨_, hh⟩
    · simp [CmpOp.Holds, CVal.ofTVal, CVal.ofValue] at hh
    · simp [tpOrders] at hh

/-- The leaf `exists (s: Timepoint). exists (t: Timepoint). formerly within 1s tp(s) && tp(t) && s < t`. -/
def tpOrdered : Condition :=
  ⟨⟨0, 0⟩, .exists ⟨.name "s", .timepoint⟩ ⟨⟨0, 0⟩, .exists ⟨.name "t", .timepoint⟩
    ⟨⟨0, 0⟩, .and ⟨⟨0, 0⟩, .and ⟨⟨0, 0⟩, .formerly (.concrete ⟨1, .seconds⟩) ⟨⟨0, 0⟩, .tp (.name "s")⟩⟩
      ⟨⟨0, 0⟩, .tp (.name "t")⟩⟩ ⟨⟨0, 0⟩, .comparison .lt (.var "s") (.var "t")⟩⟩⟩⟩

/-- **The extended relation orders timepoints, and the executable form does not**: over a trace of
two events at one time, `tpOrdered` holds at the second under `RSat` (`s` the first timepoint,
`t` the second), and its executable form does not, under any reading of the binders. So the
pass is not the identity on the relation the relativized leaves are read under: it gives the
authored orderings the specification's meaning, false, and leaves the rewrite's own orderings,
which come after it, to order. -/
theorem unorder_changes_rsat (p : TimePoint) :
    RSat ι rate [p, p] p.event (fun _ => True) Valuation.empty 1 tpOrdered ∧
    ∀ o dom, ¬ XSat ι rate [p, p] p.event (fun _ => True) o dom Valuation.empty 1
      (unorderCond [] tpOrdered) := by
  constructor
  · refine ⟨"s", rfl, .tp 0, trivial, "t", rfl, .tp 1, trivial, ⟨?_, ?_⟩, ?_⟩
    · refine ⟨⟨1, .seconds⟩, rfl, 0, by omega, trivial, ?_, ?_⟩
      · refine ⟨p, p, rfl, rfl, by omega, ?_⟩
        simp only [Int.sub_self, Dogwood.Spec.Temporal.Window.ticks, Dogwood.Spec.Temporal.Window.seconds]
        have := rate.pos
        simp [Dogwood.Spec.Temporal.TimeUnit.toSeconds]
      · exact ⟨"s", rfl, by simp [Valuation.bind, Dogwood.Spec.Temporal.tpValue]⟩
    · exact ⟨"t", rfl, by simp [Valuation.bind, Dogwood.Spec.Temporal.tpValue]⟩
    · refine ⟨.tp 0, .tp 1, ?_, ?_, Or.inr ⟨rfl, ?_⟩⟩
      · exact ⟨_, rfl, .tp 0, by simp [Dogwood.Spec.Temporal.Term.eval?, Valuation.bind], rfl⟩
      · exact ⟨_, rfl, .tp 1, by simp [Dogwood.Spec.Temporal.Term.eval?, Valuation.bind], rfl⟩
      · show 0 < 1; omega
  · intro o dom h
    obtain ⟨_, _, _, _, _, _, _, _, _, a, b, ha, hb, hh⟩ := h
    simp only [XDenotes, Surface.Temporal.Term.toSpec, pure, Except.pure, Except.ok.injEq,
      exists_eq_left', Dogwood.Spec.Temporal.Term.eval?, Option.some.injEq] at ha hb
    obtain ⟨_, rfl, rfl⟩ := ha
    obtain ⟨_, rfl, rfl⟩ := hb
    rcases hh with hh | ⟨_, hh⟩
    · simp [CmpOp.Holds, CVal.ofTVal, CVal.ofValue] at hh
    · simp [tpOrders] at hh

end

end Dogwood.Thm.Frontend
