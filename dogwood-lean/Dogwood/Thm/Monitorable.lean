import Dogwood.Eval.Candidates
import Dogwood.Thm.Restriction
import Batteries.Data.List.Perm

/-!
# Safe conditions are monitorable

Safety (`Formula.Safe`) is designed so that a condition denotes something a monitor can compute.
This module proves the two facts that make that so, for every safe condition, at every
timepoint up to `J`:

* **Range restriction is sound** (`rr_sound`): in any satisfying assignment, a range-restricted
  variable holds one of the condition's finitely many candidate values (`Formula.cand`). The
  candidates depend on the assignment only through the values of the variables restricted
  outside the condition.
* **Aggregates are total** (`total_exists`): every aggregate operand has a total — its rows form
  a finite set.

Consequently an `exists` holds exactly when some candidate witnesses it (`sat_exist_iff`).

Safety is monotone in the variables restricted outside (`Formula.safe_mono`), so these facts
need only `φ.Safe fun _ => True`: every variable the condition quantifies over is restricted by
its scope, whatever the condition's free variables are. A temporal leaf's condition is safe from
nothing (`Formula.IsSafe`), which implies it.
-/

namespace Dogwood.Thm

open Dogwood.Spec Dogwood.Spec.Temporal
open Cedar.Spec (Value)

/-! ## Safety is monotone -/

mutual

theorem Formula.safe_mono : (φ : Formula) → {R R' : VarName → Prop} → (∀ z, R z → R' z) →
    φ.Safe R → φ.Safe R'
  | .and φ ψ, R, R', hR, ⟨h₁, h₂⟩ => by
    have hC : ∀ z, (Formula.and φ ψ).Restricts R z → (Formula.and φ ψ).Restricts R' z :=
      fun z hz => Formula.restricts_mono (.and φ ψ) hR hz
    exact ⟨Formula.safe_mono φ hC h₁, Formula.safe_mono ψ hC h₂⟩
  | .not φ, _, _, hR, ⟨h₁, h₂⟩ => ⟨fun y hy => hR y (h₁ y hy), Formula.safe_mono φ hR h₂⟩
  | .formerly _ φ, _, _, hR, h => Formula.safe_mono φ hR h
  | .previous _ φ, _, _, hR, h => Formula.safe_mono φ hR h
  | .since φ _ ψ, _, _, hR, ⟨h₁, h₂, h₃⟩ => by
    have hC : ∀ z, ψ.Restricted _ z → ψ.Restricted _ z := fun z hz => Formula.restricted_mono hR hz
    exact ⟨Formula.safe_mono ψ hR h₁, fun y hy => hC y (h₂ y hy), Formula.safe_mono φ hC h₃⟩
  | .pred _ _ _, _, _, _, h => h
  | .tp _, _, _, _, h => h
  | .cmp _ l r, _, _, hR, ⟨h₁, h₂, h₃⟩ =>
    ⟨fun y hy => Formula.restricted_mono hR (h₁ y hy), Term.safe_mono l hR h₂,
      Term.safe_mono r hR h₃⟩
  | .exist x φ, _, _, hR, ⟨h₁, h₂⟩ => by
    have hR' : ∀ z, (z ≠ x.name ∧ _) → (z ≠ x.name ∧ _) := fun z hz => ⟨hz.1, hR z hz.2⟩
    exact ⟨Formula.restricts_mono φ hR' h₁, Formula.safe_mono φ hR' h₂⟩

theorem Term.safe_mono : (t : Term) → {R R' : VarName → Prop} → (∀ z, R z → R' z) →
    t.Safe R → t.Safe R'
  | .agg a, _, _, hR, h => Aggregate.safe_mono a hR h
  | .arith _ l r, _, _, hR, ⟨h₁, h₂⟩ => ⟨Term.safe_mono l hR h₁, Term.safe_mono r hR h₂⟩
  | .entity _, _, _, _, h | .long _, _, _, _, h | .decimal _, _, _, _, h | .string _, _, _, _, h
  | .bool _, _, _, _, h | .context _, _, _, _, h | .scope _ _, _, _, _, h | .var _, _, _, _, h
  | .wildcard, _, _, _, h => h

theorem Aggregate.safe_mono : (a : Aggregate) → {R R' : VarName → Prop} → (∀ z, R z → R' z) →
    a.Safe R → a.Safe R'
  | .count dom body, _, _, hR, ⟨h₁, h₂⟩ | .sum _ dom body, _, _, hR, ⟨h₁, h₂⟩ => by
    have hR' : ∀ z, (z ∉ dom.map (·.name) ∧ _) → (z ∉ dom.map (·.name) ∧ _) :=
      fun z hz => ⟨hz.1, hR z hz.2⟩
    exact ⟨fun b hb => Formula.restricts_mono body hR' (h₁ b hb), Formula.safe_mono body hR' h₂⟩

end

/-- A safe leaf condition is safe relative to any free variables. -/
theorem Formula.IsSafe.safe_top {φ : Formula} (h : φ.IsSafe) : φ.Safe fun _ => True :=
  Formula.safe_mono φ (fun _ h => h.elim) h

/-! ## Lists -/

theorem mem_product {α : Type} {xs : List α} {m : Nat} {row : List α} :
    row ∈ product xs m ↔ row.length = m ∧ ∀ y ∈ row, y ∈ xs := by
  induction m generalizing row with
  | zero => cases row <;> simp [product]
  | succ m ih =>
    cases row with
    | nil => simp [product]
    | cons y row =>
      simp only [product, List.mem_flatMap, List.mem_map, List.cons.injEq, ih,
        List.length_cons, List.mem_cons, forall_eq_or_imp]
      constructor
      · rintro ⟨x, hx, row', ⟨hl, hr⟩, rfl, rfl⟩
        exact ⟨by omega, hx, hr⟩
      · rintro ⟨hl, hy, hr⟩
        exact ⟨y, hy, row, ⟨by omega, hr⟩, rfl, rfl⟩

theorem mem_dedup {α : Type} [BEq α] [LawfulBEq α] {x : α} {xs : List α} :
    x ∈ dedup xs ↔ x ∈ xs := by
  induction xs with
  | nil => simp [dedup]
  | cons y xs ih =>
    simp only [dedup, List.mem_cons, List.mem_filter, ih, bne_iff_ne, ne_eq]
    by_cases h : x = y <;> simp [h]

theorem nodup_dedup {α : Type} [BEq α] [LawfulBEq α] (xs : List α) : (dedup xs).Nodup := by
  induction xs with
  | nil => exact List.nodup_nil
  | cons y xs ih =>
    simp only [dedup]
    refine List.nodup_cons.mpr ⟨by simp, ih.sublist List.filter_sublist⟩

private theorem sum_le_of_sublist {l₁ l₂ : List Nat} (h : l₁.Sublist l₂) : l₁.sum ≤ l₂.sum := by
  induction h with
  | slnil => simp
  | cons _ _ ih => simp only [List.sum_cons]; omega
  | cons_cons _ _ ih => simp only [List.sum_cons]; omega

private theorem natAbs_sum_le (l : List Int) : l.sum.natAbs ≤ (l.map Int.natAbs).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.sum_cons, List.map_cons]
    exact Nat.le_trans (Int.natAbs_add_le _ _) (Nat.add_le_add_left ih _)

/-- A duplicate-free list drawn from `L` has a sum of absolute values at most `L`'s. -/
private theorem abs_sum_le_of_subset {α : Type} {rows L : List α} (f : α → Int)
    (hnd : rows.Nodup) (hsub : ∀ r ∈ rows, r ∈ L) :
    (rows.map f).sum.natAbs ≤ (L.map fun r => (f r).natAbs).sum := by
  obtain ⟨l, hperm, hsl⟩ := List.subperm_of_subset hnd hsub
  have h₁ : (rows.map f).sum.natAbs ≤ (rows.map fun r => (f r).natAbs).sum := by
    have := natAbs_sum_le (rows.map f)
    simpa [List.map_map, Function.comp_def] using this
  have h₂ : (rows.map fun r => (f r).natAbs).sum = (l.map fun r => (f r).natAbs).sum :=
    (hperm.map _).symm.sum_nat
  have h₃ := sum_le_of_sublist (hsl.map fun r => (f r).natAbs)
  omega

/-! ## Valuations and values -/

theorem bindAll_not_mem {v : Valuation} {xs : List VarName} {ws : List TVal} {x : VarName}
    (h : x ∉ xs) : (v.bindAll xs ws) x = v x := by
  induction xs generalizing v ws with
  | nil => cases ws <;> rfl
  | cons y xs ih =>
    cases ws with
    | nil => rfl
    | cons w ws =>
      simp only [List.mem_cons, not_or] at h
      simp only [Valuation.bindAll]
      rw [ih h.2]
      simp [Valuation.bind, h.1]

/-- With distinct names, each value of a row is the binding of one of the names. -/
theorem bindAll_cover {v : Valuation} {xs : List VarName} {row : List TVal} (hnd : xs.Nodup)
    (hlen : row.length = xs.length) :
    ∀ y ∈ row, ∃ x ∈ xs, (v.bindAll xs row) x = some y := by
  induction xs generalizing v row with
  | nil => cases row <;> simp_all
  | cons x xs ih =>
    cases row with
    | nil => simp at hlen
    | cons w row =>
      have ⟨hx, hnd'⟩ := List.nodup_cons.mp hnd
      intro y hy
      simp only [List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact ⟨x, by simp, by simp [Valuation.bindAll, bindAll_not_mem hx, Valuation.bind]⟩
      · obtain ⟨x', hx', h⟩ := ih (v := v.bind x w) hnd' (by simpa using hlen) y hy
        exact ⟨x', by simp [hx'], h⟩

theorem CVal.toTVal_ofTVal (w : TVal) : (CVal.ofTVal w).toTVal = w := by
  cases w with
  | tp k => rfl
  | val v =>
    cases v with
    | prim p => cases p <;> simp [CVal.ofTVal, CVal.ofValue, CVal.toTVal]
    | _ => rfl

theorem mem_aggValues {ι : ImplChoices} {lo hi n : Int} {c : CVal} (hlo : lo ≤ n) (hhi : n ≤ hi)
    (h : ι.aggregateValue n = some c) : c ∈ aggValues ι lo hi := by
  simp only [aggValues, List.mem_filterMap, List.mem_map, List.mem_range]
  refine ⟨n, ⟨(n - lo).toNat, by omega, by omega⟩, h⟩

theorem eval_ground {e : Event} {v : Valuation} {t : Term} (hv : ∀ x, t ≠ .var x) :
    t.eval? e v = t.eval? e Valuation.empty := by
  cases t <;> simp_all [Term.eval?]

theorem denotes_var {ι : ImplChoices} {rate : TickRate} {σ : Trace} {e : Event} {vis : Nat → Prop} {v : Valuation}
    {j : Nat} {x : VarName} {c : CVal} (h : Denotes ι rate σ e vis v j (.var x) c) :
    ∃ w, v x = some w ∧ c = CVal.ofTVal w := by
  simpa [Denotes, Term.eval?] using h

theorem eqRestricted_cases {l r : Term} {x : VarName} (h : eqRestricted? l r = some x) :
    l = .var x ∨ (r = .var x ∧ ∀ y, l ≠ .var y) := by
  cases l <;> cases r <;> simp only [eqRestricted?] at h <;>
    first
    | (split at h <;> simp_all)
    | simp_all

theorem valueSide_of_eq {l r : Term} {x : VarName} (h : eqRestricted? l r = some x) :
    (l = .var x ∧ valueSide x l r = r) ∨ (r = .var x ∧ valueSide x l r = l) := by
  rcases eqRestricted_cases h with rfl | ⟨rfl, hl⟩
  · exact .inl ⟨rfl, by simp [valueSide]⟩
  · refine .inr ⟨rfl, ?_⟩
    unfold valueSide
    split
    · rename_i z; exact absurd rfl (hl z)
    · rfl

/-! ## Seeds -/

/-- Every variable of `R` that `v` binds holds a value of `X`. -/
def SeedOk (R : VarName → Prop) (X : List TVal) (v : Valuation) : Prop :=
  ∀ y, R y → ∀ w, v y = some w → w ∈ X

/-- The values `v` gives the variables `xs`: a seed for them. -/
theorem SeedOk.ofList (xs : List VarName) (v : Valuation) :
    SeedOk (· ∈ xs) (xs.filterMap v) v :=
  fun y hy _ hw => List.mem_filterMap.mpr ⟨y, hy, hw⟩

/-- The seed of an aggregate's body, under a row's bindings: the variables restricted outside
it, minus the aggregate's own `for` variables. -/
theorem SeedOk.bindAll_dom {dom : List Binder} {R : VarName → Prop} {X : List TVal}
    {v : Valuation} {row : List TVal} (h : SeedOk R X v) :
    SeedOk (fun z => z ∉ dom.map (·.name) ∧ R z) X (v.bindAll (domainNames dom) row) := by
  intro y hy w hw
  have hy' : y ∉ domainNames dom := fun hm => hy.1 (mem_dedup.mp hm)
  rw [bindAll_not_mem hy'] at hw
  exact h y hy.2 w hw

theorem mem_iter_of_mem {f : List TVal → List TVal} (hf : ∀ Y, ∀ w ∈ Y, w ∈ f Y) :
    ∀ (n : Nat) {Y : List TVal} {w : TVal}, w ∈ Y → w ∈ iter f n Y
  | 0, _, _, h => h
  | n + 1, _, _, h => hf _ _ (mem_iter_of_mem hf n h)

/-! ## Soundness of range restriction -/

section

variable (ι : ImplChoices) (rate : TickRate) (σ : Trace) (e : Event) (vis : Nat → Prop) (J : Nat)

theorem mem_traceValues {paths : List Path} {j : Nat} {p : TimePoint} {path : Path} {w : Value}
    (hj : j ≤ J) (hp : σ[j]? = some p) (hpath : path ∈ paths)
    (hw : recordPath? p.event.logged path = some w) : TVal.val w ∈ traceValues σ J paths := by
  simp only [traceValues, List.mem_flatMap, List.mem_range]
  refine ⟨j, by omega, ?_⟩
  simp only [hp, List.mem_map, List.mem_filterMap]
  exact ⟨w, ⟨path, hpath, hw⟩, rfl⟩

theorem mem_tpValues {j : Nat} (hj : j ≤ J) : tpValue j ∈ tpValues J := by
  simp only [tpValues, List.mem_map, List.mem_range]
  exact ⟨j, by omega, rfl⟩

/-- The value of a restricted variable, or a variable restricted outside. -/
def Witnessed (R : VarName → Prop) (C : List TVal) (v : Valuation) (x : VarName) : Prop :=
  (∃ w, v x = some w ∧ w ∈ C) ∨ R x

/-- A `for` variable an aggregation's body restricts from everything outside it, the body
restricts from the variables restricted outside the aggregate, when those include the
aggregate's free variables. -/
theorem domain_restricts_congr {dom : List Binder} {body : Formula} {R : VarName → Prop}
    (hfv : ∀ y ∈ body.fv.filter (fun x => !(dom.map (·.name)).contains x), R y)
    {x : VarName} (hx : x ∈ dom.map (·.name)) :
    body.Restricts (fun z => z ∉ dom.map (·.name) ∧ True) x ↔
      body.Restricts (fun z => z ∉ dom.map (·.name) ∧ R z) x := by
  refine Formula.restricts_congr body (fun y hy => ?_) (by simp [hx])
  by_cases hyd : y ∈ dom.map (·.name)
  · simp [hyd]
  · have : R y := hfv y (List.mem_filter.mpr ⟨hy, by simpa using hyd⟩)
    simp [hyd, this]

/-- The `for` variables of a safe aggregation, as names. -/
theorem hdom' {dom : List Binder} {body : Formula}
    (h : ∀ b ∈ dom, body.Restricts (fun z => z ∉ dom.map (·.name) ∧ True) b.name)
    {x : VarName} (hx : x ∈ dom.map (·.name)) :
    body.Restricts (fun z => z ∉ dom.map (·.name) ∧ True) x := by
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
  exact h b hb

mutual

/-- **Range restriction is sound.** In a safe condition, a variable restricted from `R` holds a
candidate value in every satisfying assignment that gives `R`'s variables values of `X`, unless
it is one of `R`'s variables itself. -/
theorem rr_sound : (φ : Formula) → φ.Safe (fun _ => True) → (R : VarName → Prop) →
    (X : List TVal) → ∀ (v : Valuation), SeedOk R X v → ∀ (j : Nat), j ≤ J →
      Sat ι rate σ e vis v j φ → ∀ x, φ.Restricts R x → Witnessed R (φ.cand ι σ e J X) v x
  | .and φ ψ, hs, R, X, v, hseed, j, hj, hsat, x, hx => by
    have hs' : φ.Safe (fun _ => True) ∧ ψ.Safe (fun _ => True) :=
      ⟨Formula.safe_mono φ (fun _ _ => trivial) hs.1, Formula.safe_mono ψ (fun _ _ => trivial) hs.2⟩
    let f : List TVal → List TVal := fun Y =>
      (Y ++ φ.cand ι σ e J Y ++ ψ.cand ι σ e J Y).eraseDups
    have hf : ∀ Y, ∀ w ∈ Y, w ∈ f Y := fun _ _ hw =>
      List.mem_eraseDups.mpr (List.mem_append_left _ (List.mem_append_left _ hw))
    have hfφ : ∀ Y, ∀ w ∈ φ.cand ι σ e J Y, w ∈ f Y := fun _ _ hw =>
      List.mem_eraseDups.mpr (List.mem_append_left _ (List.mem_append_right _ hw))
    have hfψ : ∀ Y, ∀ w ∈ ψ.cand ι σ e J Y, w ∈ f Y := fun _ _ hw =>
      List.mem_eraseDups.mpr (List.mem_append_right _ hw)
    -- Round `i` of the closure holds candidates of round `i` of the iteration.
    have stage : ∀ i, ∀ z, Formula.stage R φ ψ i z →
        Witnessed R (iter f i X) v z := by
      intro i
      induction i with
      | zero => intro z hz; exact .inr hz
      | succ i ih =>
        have hseed' : SeedOk (Formula.stage R φ ψ i) (iter f i X) v := by
          intro y hy w hw
          rcases ih y hy with ⟨w', hw', hm⟩ | hR
          · rw [hw] at hw'; cases hw'; exact hm
          · exact mem_iter_of_mem hf i (hseed y hR w hw)
        intro z hz
        rcases hz with hz | hz | hz
        · rcases ih z hz with ⟨w, hw, hm⟩ | hR
          · exact .inl ⟨w, hw, hf _ w hm⟩
          · exact .inr hR
        · rcases rr_sound φ hs'.1 _ _ v hseed' j hj hsat.1 z hz with ⟨w, hw, hm⟩ | hst
          · exact .inl ⟨w, hw, hfφ _ w hm⟩
          · rcases ih z hst with ⟨w, hw, hm⟩ | hR
            · exact .inl ⟨w, hw, hf _ w hm⟩
            · exact .inr hR
        · rcases rr_sound ψ hs'.2 _ _ v hseed' j hj hsat.2 z hz with ⟨w, hw, hm⟩ | hst
          · exact .inl ⟨w, hw, hfψ _ w hm⟩
          · rcases ih z hst with ⟨w, hw, hm⟩ | hR
            · exact .inl ⟨w, hw, hf _ w hm⟩
            · exact .inr hR
    exact stage _ x (Formula.restricts_and_iff.mp hx)
  | .not _, _, _, _, _, _, _, _, _, _, hx => hx.elim
  | .formerly _ φ, hs, R, X, v, hseed, j, hj, hsat, x, hx => by
    obtain ⟨k, hk, _, _, hs'⟩ := hsat
    exact rr_sound φ hs R X v hseed k (Nat.le_trans hk hj) hs' x hx
  | .previous _ φ, hs, R, X, v, hseed, j, hj, hsat, x, hx => by
    obtain ⟨k, hk, _, _, _, hs'⟩ := hsat
    exact rr_sound φ hs R X v hseed k (by omega) hs' x hx
  | .since φ _ ψ, hs, R, X, v, hseed, j, hj, hsat, x, hx => by
    obtain ⟨k, hk, _, _, hs', _⟩ := hsat
    exact rr_sound ψ hs.1 R X v hseed k (Nat.le_trans hk hj) hs' x hx
  | .pred a k args, _, R, X, v, _, j, hj, hsat, x, ⟨path, harg⟩ => by
    obtain ⟨p, hp, _, _, hargs⟩ := hsat
    obtain ⟨w, hw, hm⟩ := hargs (path, .var x) harg
    simp only [Term.Matches, Term.eval?] at hm
    exact .inl ⟨.val w, hm, mem_traceValues σ J hj hp (List.mem_map.mpr ⟨_, harg, rfl⟩) hw⟩
  | .cmp op l r, hs, R, X, v, hseed, j, hj, hsat, x, hx => by
    cases op <;> simp only [Formula.Restricts] at hx
    obtain ⟨hx, hvs⟩ := hx
    obtain ⟨_, hsl, hsr⟩ := hs
    obtain ⟨a, b, ha, hb, hab⟩ := hsat
    simp only [CmpOp.Holds] at hab
    subst hab
    rcases valueSide_of_eq hx with ⟨rfl, hv⟩ | ⟨rfl, hv⟩
    · rw [hv] at hvs
      obtain ⟨w, hw, rfl⟩ := denotes_var ha
      exact .inl ⟨w, hw, List.mem_map.mpr ⟨_, List.mem_append_right _
        (opCand_sound r hsr R X hvs v hseed j hj _ hb), CVal.toTVal_ofTVal w⟩⟩
    · rw [hv] at hvs
      obtain ⟨w, hw, hbw⟩ := denotes_var hb
      refine .inl ⟨w, hw, List.mem_map.mpr ⟨_, List.mem_append_left _
        (opCand_sound l hsl R X hvs v hseed j hj _ ha), ?_⟩⟩
      rw [hbw, CVal.toTVal_ofTVal]
  | .exist y φ, hs, R, X, v, hseed, j, hj, hsat, x, ⟨hne, hx⟩ => by
    obtain ⟨w', hs'⟩ := hsat
    have hseed' : SeedOk (fun z => z ≠ y.name ∧ R z) X (v.bind y.name w') := by
      intro z hz w hw
      simp only [Valuation.bind, hz.1, if_false] at hw
      exact hseed z hz.2 w hw
    have hsafe : φ.Safe (fun _ => True) := Formula.safe_mono φ (fun _ _ => trivial) hs.2
    rcases rr_sound φ hsafe _ X _ hseed' j hj hs' x hx with ⟨w, hw, hm⟩ | hR
    · simp only [Valuation.bind, hne, if_false] at hw
      exact .inl ⟨w, hw, hm⟩
    · exact .inr hR.2
  | .tp y, _, R, X, v, _, j, hj, hsat, x, hx => by
    simp only [Formula.Restricts] at hx
    subst hx
    exact .inl ⟨tpValue j, hsat, mem_tpValues J hj⟩

/-- A comparison operand denotes one of its candidates, when its variables are restricted by
the seed. -/
theorem opCand_sound : (t : Term) → t.Safe (fun _ => True) → (R : VarName → Prop) →
    (X : List TVal) → (∀ y ∈ t.fv, R y) → ∀ (v : Valuation), SeedOk R X v →
      ∀ (j : Nat), j ≤ J → ∀ c, Denotes ι rate σ e vis v j t c → c ∈ t.opCand ι σ e J X
  | .var y, _, R, X, hfv, v, hseed, j, _, c, hd => by
    obtain ⟨w, hw, rfl⟩ := denotes_var hd
    exact List.mem_map.mpr ⟨w, hseed y (hfv y (by simp [Term.fv])) w hw, rfl⟩
  | .wildcard, _, _, _, _, _, _, _, _, c, hd => by simp [Denotes, Term.eval?] at hd
  | .agg a, hs, R, X, hfv, v, hseed, j, hj, c, hd => by
    simp only [Denotes] at hd
    obtain ⟨n, htot, hval⟩ := hd
    exact agg_sound a hs R X hfv v hseed j hj n c htot hval
  | .arith op l r, hs, R, X, hfv, v, hseed, j, hj, c, hd => by
    simp only [Term.fv, List.mem_append] at hfv
    simp only [Denotes] at hd
    obtain ⟨m, n, hl, hr, hval⟩ := hd
    have hml := opCand_sound l hs.1 R X (fun y hy => hfv y (Or.inl hy)) v hseed j hj _ hl
    have hmr := opCand_sound r hs.2 R X (fun y hy => hfv y (Or.inr hy)) v hseed j hj _ hr
    simp only [Term.opCand, List.mem_flatMap, List.mem_filterMap]
    exact ⟨_, hml, _, hmr, hval⟩
  | .entity _, _, _, _, _, v, _, _, _, c, hd
  | .long _, _, _, _, _, v, _, _, _, c, hd
  | .decimal _, _, _, _, _, v, _, _, _, c, hd
  | .string _, _, _, _, _, v, _, _, _, c, hd
  | .bool _, _, _, _, _, v, _, _, _, c, hd
  | .context _, _, _, _, _, v, _, _, _, c, hd
  | .scope _ _, _, _, _, _, v, _, _, _, c, hd => by
    simp only [Denotes] at hd
    obtain ⟨w, hw, rfl⟩ := hd
    rw [eval_ground (by simp)] at hw
    simp [Term.opCand, hw]

/-- A safe aggregate's total, as compared, is one of its candidates, when its free variables
are restricted by the seed. -/
theorem agg_sound : (a : Aggregate) → a.Safe (fun _ => True) → (R : VarName → Prop) →
    (X : List TVal) → (∀ y ∈ a.fv, R y) → ∀ (v : Valuation), SeedOk R X v →
      ∀ (j : Nat), j ≤ J → ∀ (n : Int) (c : CVal),
        Total ι rate σ e vis v j a n → ι.aggregateValue n = some c → c ∈ a.cand ι σ e J X
  | .count dom body, ⟨hdom, hbody⟩, R, X, hfv, v, hseed, j, hj, n, c, htot, hval => by
    obtain ⟨rows, hnd, hmem, rfl⟩ := htot
    have hbody' := Formula.safe_mono body (fun _ _ => trivial) hbody
    have hsub : ∀ row ∈ rows, row ∈ product (body.cand ι σ e J X) (domainNames dom).length := by
      intro row hrow
      obtain ⟨hl, hsat⟩ := (hmem row).mp hrow
      refine mem_product.mpr ⟨hl, fun y hy => ?_⟩
      obtain ⟨x, hx, hb⟩ := bindAll_cover (v := v) (nodup_dedup _) hl y hy
      replace hb : (v.bindAll (domainNames dom) row) x = some y := hb
      have hxd : x ∈ dom.map (·.name) := mem_dedup.mp hx
      have hr := (domain_restricts_congr hfv hxd).mp (hdom' hdom hxd)
      rcases rr_sound body hbody' _ X _ hseed.bindAll_dom j hj hsat x hr with ⟨w, hw, hm⟩ | hR
      · rw [hb] at hw; cases hw; exact hm
      · exact absurd hxd hR.1
    have hlen := (List.subperm_of_subset hnd hsub).length_le
    simp only [Aggregate.cand]
    exact mem_aggValues (by omega) (by omega) hval
  | .sum s dom body, ⟨hdom, hbody⟩, R, X, hfv, v, hseed, j, hj, n, c, htot, hval => by
    obtain ⟨rows, hnd, hmem, rfl⟩ := htot
    have hbody' := Formula.safe_mono body (fun _ _ => trivial) hbody
    have hsub : ∀ row ∈ rows, row ∈ product (body.cand ι σ e J X) (domainNames dom).length := by
      intro row hrow
      obtain ⟨hl, hsat⟩ := (hmem row).mp hrow
      refine mem_product.mpr ⟨hl, fun y hy => ?_⟩
      obtain ⟨x, hx, hb⟩ := bindAll_cover (v := v) (nodup_dedup _) hl y hy
      replace hb : (v.bindAll (domainNames dom) row) x = some y := hb
      have hxd : x ∈ dom.map (·.name) := mem_dedup.mp hx
      have hr := (domain_restricts_congr hfv hxd).mp (hdom' hdom hxd)
      rcases rr_sound body hbody' _ X _ hseed.bindAll_dom j hj hsat x hr with ⟨w, hw, hm⟩ | hR
      · rw [hb] at hw; cases hw; exact hm
      · exact absurd hxd hR.1
    have habs := abs_sum_le_of_subset (summand s (domainNames dom)) hnd hsub
    simp only [Aggregate.cand]
    exact mem_aggValues (by omega) (by omega) hval

end

/-- The rows of a safe aggregation are drawn from its body's candidates, when the variables
restricted outside it, its free variables among them, have values of the seed. -/
theorem rows_mem_product {dom : List Binder} {body : Formula}
    (hdom : ∀ b ∈ dom, body.Restricts (fun z => z ∉ dom.map (·.name) ∧ True) b.name)
    (hbody : body.Safe (fun z => z ∉ dom.map (·.name) ∧ True)) {R : VarName → Prop}
    {X : List TVal} (hfv : ∀ y ∈ body.fv.filter (fun x => !(dom.map (·.name)).contains x), R y)
    {v : Valuation} (hseed : SeedOk R X v) {j : Nat} (hj : j ≤ J) {row : List TVal}
    (hrow : row.length = (domainNames dom).length ∧
      Sat ι rate σ e vis (v.bindAll (domainNames dom) row) j body) :
    row ∈ product (body.cand ι σ e J X) (domainNames dom).length := by
  have hbody' := Formula.safe_mono body (fun _ _ => trivial) hbody
  refine mem_product.mpr ⟨hrow.1, fun y hy => ?_⟩
  obtain ⟨x, hx, hb⟩ := bindAll_cover (v := v) (nodup_dedup _) hrow.1 y hy
  replace hb : (v.bindAll (domainNames dom) row) x = some y := hb
  have hxd : x ∈ dom.map (·.name) := mem_dedup.mp hx
  have hr := (domain_restricts_congr hfv hxd).mp (hdom' hdom hxd)
  rcases rr_sound ι rate σ e vis J body hbody' _ X _ hseed.bindAll_dom j hj hrow.2 x hr with
    ⟨w, hw, hm⟩ | hR
  · rw [hb] at hw; cases hw; exact hm
  · exact absurd hxd hR.1

end

/-! ## Consequences -/

section

variable {ι : ImplChoices} {rate : TickRate} {σ : Trace} {e : Event} {vis : Nat → Prop} {J : Nat}

/-- **Aggregates are total.** A safe aggregate has a total at every timepoint up to `J`, under
every valuation. -/
theorem total_exists {a : Aggregate} {R : VarName → Prop} (hs : a.Safe R) (v : Valuation)
    {j : Nat} (hj : j ≤ J) : ∃ n, Total ι rate σ e vis v j a n := by
  classical
  have hs' := Aggregate.safe_mono a (fun _ _ => trivial) hs
  have hseed := SeedOk.ofList a.fv v
  cases a with
  | count dom body =>
    obtain ⟨hdom, hbody⟩ := hs'
    let L := (product (body.cand ι σ e J (Aggregate.fv (.count dom body) |>.filterMap v))
      (domainNames dom).length) |> dedup
    let rows := L.filter fun row => decide (Sat ι rate σ e vis (v.bindAll (domainNames dom) row) j body)
    refine ⟨rows.length, rows, ?_, fun row => ?_, rfl⟩
    · exact (nodup_dedup _).sublist List.filter_sublist
    · simp only [rows, L, List.mem_filter, mem_dedup, decide_eq_true_eq]
      constructor
      · rintro ⟨hp, hs⟩
        exact ⟨(mem_product.mp hp).1, hs⟩
      · intro h
        exact ⟨rows_mem_product ι rate σ e vis J hdom hbody (fun y hy => hy) hseed hj h, h.2⟩
  | sum s dom body =>
    obtain ⟨hdom, hbody⟩ := hs'
    let L := (product (body.cand ι σ e J (Aggregate.fv (.sum s dom body) |>.filterMap v))
      (domainNames dom).length) |> dedup
    let rows := L.filter fun row => decide (Sat ι rate σ e vis (v.bindAll (domainNames dom) row) j body)
    refine ⟨(rows.map (summand s (domainNames dom))).sum, rows, ?_, fun row => ?_, rfl⟩
    · exact (nodup_dedup _).sublist List.filter_sublist
    · simp only [rows, L, List.mem_filter, mem_dedup, decide_eq_true_eq]
      constructor
      · rintro ⟨hp, hs⟩
        exact ⟨(mem_product.mp hp).1, hs⟩
      · intro h
        exact ⟨rows_mem_product ι rate σ e vis J hdom hbody (fun y hy => hy) hseed hj h, h.2⟩

/-- **Quantifiers are witnessed by candidates.** A safe `exists` holds exactly when one of its
body's candidates witnesses it, computed from the values `v` gives the free variables of the
`exists`. -/
theorem sat_exist_iff {x : Binder} {φ : Formula} {R : VarName → Prop}
    (hs : (Formula.exist x φ).Safe R) (v : Valuation) {j : Nat} (hj : j ≤ J) :
    Sat ι rate σ e vis v j (.exist x φ) ↔
      ∃ w ∈ φ.cand ι σ e J ((Formula.exist x φ).fv.filterMap v),
        Sat ι rate σ e vis (v.bind x.name w) j φ := by
  constructor
  · rintro ⟨w, hsat⟩
    let R₀ : VarName → Prop := fun z => z ≠ x.name ∧ z ∈ (Formula.exist x φ).fv
    have hr₁ : φ.Restricts (fun z => z ≠ x.name ∧ True) x.name :=
      Formula.restricts_mono φ (fun z hz => ⟨hz.1, trivial⟩) hs.1
    have hr : φ.Restricts R₀ x.name := by
      refine (Formula.restricts_congr φ (fun y hy => ?_) (by simp [R₀])).mp hr₁
      by_cases hyx : y = x.name
      · simp [R₀, hyx]
      · simp only [ne_eq, hyx, not_false_eq_true, true_and, R₀, true_iff]
        simp [Formula.fv, hy, hyx]
    have hseed : SeedOk R₀ ((Formula.exist x φ).fv.filterMap v) (v.bind x.name w) := by
      intro z hz u hu
      simp only [Valuation.bind, hz.1, if_false] at hu
      exact List.mem_filterMap.mpr ⟨z, hz.2, hu⟩
    have hsafe : φ.Safe (fun _ => True) := Formula.safe_mono φ (fun _ _ => trivial) hs.2
    rcases rr_sound ι rate σ e vis J φ hsafe R₀ _ _ hseed j hj hsat x.name hr with ⟨w', hw', hm⟩ | hR
    · simp only [Valuation.bind, if_true, Option.some.injEq] at hw'
      exact ⟨w, hw' ▸ hm, hsat⟩
    · exact absurd rfl hR.1
  · rintro ⟨w, _, hs⟩
    exact ⟨w, hs⟩

end

end Dogwood.Thm
