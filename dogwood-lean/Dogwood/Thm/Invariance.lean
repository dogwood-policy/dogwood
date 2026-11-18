import Dogwood.Thm.Scale
import Dogwood.Thm.Valuation
import Cedar.Thm.Data.Set
import Dogwood.Thm.Authorization
import Dogwood.Thm.Partitioned
import Dogwood.Thm.Log
import Dogwood.Spec.Ingest

/-!
# Invariances: what a decision does not depend on

* **Shifting time** (`sat_shift`, `authorize_shift`; partitioned, `authorizePart_shift`; with
  deployed rules, `authorizeDeployed_shift`; over a log, `Log.decide_shift`; at ingestion,
  `submit_shift`, `ingest_shift`): adding a constant to every timestamp, or to every clock reading
  an authorizer stamps, changes no truth value, no decision and no reply. The semantics reads
  timestamps only through their differences (`InWindow`), `tp(x)` tests a timepoint's index, not
  its timestamp, and stamping commutes with shifting (`stamp_shift`). Together with
  `authorize_scale` (timestamps multiplied by a positive natural, with the policy set's rate made
  finer by the same factor), a decision does not depend on where or in what unit the clock starts
  counting.
* **The order of conjuncts in a temporal condition** (`sat_and_comm`,
  `Formula.restricts_and_comm`, `Formula.safe_and_comm`, `Formula.wellTyped_and_comm`,
  `Formula.monitorsTime_and_comm`, `Formula.horizon_and_comm`, `Formula.mem_fv_and_comm`, and
  `leafValid_and_comm`): swapping the two sides of a temporal `&&` changes no truth value,
  restriction, safety, typing, time dependence, horizon, or free variable, so no part of a leaf's
  validity. This is about the temporal sub-language only. Cedar's `&&` in a rule's condition
  evaluates left to right and short-circuits, so swapping its sides can change whether the rule
  errs, and which `has` tests guard a temporal leaf (`Expr.leafFacts`), and so validity.
* **Renaming variables** (`sat_rename`, `sat_exist_alpha`, `total_alpha`, `leafHolds_rename`,
  `partLeafHolds_rename`, `leafHoldsFrom_rename`): satisfaction is invariant under an injective
  renaming of every variable, free and bound, with the valuation renamed alike; so a bound
  variable, of an `exists` or of an aggregate, can be renamed to one the condition does not use
  free (alpha-equivalence), and a leaf means the same with its variables renamed (pin injection
  commutes with renaming, `Formula.rename_injectPins`). Safety (`Formula.safe_rename`,
  `Formula.isSafe_rename`, with `Formula.restricts_rename` and `Formula.fv_rename`) and the
  time-dependence check (`Formula.monitorsTime_rename`) are invariant under an injective renaming;
  typing survives one that keeps reserved binder names reserved (`Formula.WellTyped.rename`), and
  is invariant under swapping two names that are not reserved (`wellTyped_swap_iff`, via
  `Formula.rename_rename` and `Formula.rename_id`). So alpha-renaming a leaf keeps it valid, and
  an invalid leaf invalid (`leafValid_swap_iff`).
* **Renaming policy ids** (`isAuthorized_renameIds`, `authorize_renameIds`): the decision does not
  read policy ids; renaming them renames the determining and erroring policies and changes
  nothing else, per request at every leaf valuation, and over a trace under a total reading, or
  under every reading for an injective renaming (`authorize_renameIds_of_injective`).
-/

namespace Dogwood.Thm

open Dogwood.Spec Dogwood.Spec.Temporal

/-! ## Shifting time -/

/-- The trace with every timestamp shifted by `d`. -/
def _root_.Dogwood.Spec.Trace.shift (d : Int) (σ : Trace) : Trace :=
  σ.map fun p => ⟨p.ts + d, p.event⟩

theorem shift_getElem? (d : Int) (σ : Trace) (k : Nat) :
    (σ.shift d)[k]? = σ[k]?.map fun p => ⟨p.ts + d, p.event⟩ := by
  simp [Trace.shift, List.getElem?_map]

theorem shift_length (d : Int) (σ : Trace) : (σ.shift d).length = σ.length := by
  simp [Trace.shift]

/-- The events of a shifted trace are the trace's. -/
theorem shift_event? (d : Int) (σ : Trace) (k : Nat) :
    (σ.shift d)[k]?.map (·.event) = σ[k]?.map (·.event) := by
  rw [shift_getElem?]
  cases σ[k]? <;> rfl

/-- Shifting keeps timestamps strictly increasing. -/
theorem shift_strictlyIncreasing {d : Int} {σ : Trace} (h : Trace.StrictlyIncreasing σ) :
    Trace.StrictlyIncreasing (σ.shift d) := by
  unfold Trace.StrictlyIncreasing Trace.shift at *
  rw [List.pairwise_map]
  exact h.imp fun hlt => by simp only; omega

theorem inWindow_shift {rate : TickRate} {d : Int} {σ : Trace} {j k : Nat} {w : Window} :
    InWindow rate (σ.shift d) j k w ↔ InWindow rate σ j k w := by
  unfold InWindow
  rw [shift_getElem?, shift_getElem?]
  cases σ[j]? with
  | none => simp
  | some pj =>
    cases σ[k]? with
    | none => simp
    | some pk =>
      simp only [Option.map_some, Option.some.injEq]
      constructor
      · rintro ⟨_, _, rfl, rfl, h₀, h₁⟩
        exact ⟨pj, pk, rfl, rfl, by simp only at h₀; omega, by simp only at h₁; omega⟩
      · rintro ⟨_, _, rfl, rfl, h₀, h₁⟩
        exact ⟨_, _, rfl, rfl, by simp only; omega, by simp only; omega⟩

section

variable {ι : ImplChoices} {rate : TickRate} {d : Int} {σ : Trace} {e : Event} {vis : Nat → Prop}

mutual

/-- **Shifting time preserves satisfaction.** -/
theorem sat_shift : (φ : Formula) → (v : Valuation) → (j : Nat) →
    (Sat ι rate (σ.shift d) e vis v j φ ↔ Sat ι rate σ e vis v j φ)
  | .and φ ψ, v, j => by
    simp only [Sat]; rw [sat_shift φ v j, sat_shift ψ v j]
  | .not φ, v, j => by
    simp only [Sat]; rw [sat_shift φ v j]
  | .formerly w φ, v, j => by
    simp only [Sat, inWindow_shift]
    exact exists_congr fun k => and_congr_right fun _ => and_congr_right fun _ =>
      and_congr_right fun _ => sat_shift φ v k
  | .previous w φ, v, j => by
    simp only [Sat, inWindow_shift]
    exact exists_congr fun k => and_congr_right fun _ => and_congr_right fun _ =>
      and_congr_right fun _ => and_congr_right fun _ => sat_shift φ v k
  | .since φ w ψ, v, j => by
    simp only [Sat, inWindow_shift]
    refine exists_congr fun k => and_congr_right fun _ => and_congr_right fun _ =>
      and_congr_right fun _ => ?_
    rw [sat_shift ψ v k]
    exact and_congr_right fun _ => forall_congr' fun k' => imp_congr_right fun _ =>
      imp_congr_right fun _ => imp_congr_right fun _ => sat_shift φ v k'
  | .pred a kd args, v, j => by
    simp only [Sat, shift_getElem?]
    cases σ[j]? <;> simp
  | .cmp op l r, v, j => by
    simp only [Sat]
    exact exists_congr fun a => exists_congr fun b => by
      rw [denotes_shift l v j a, denotes_shift r v j b]
  | .exist x φ, v, j => by
    simp only [Sat]
    exact exists_congr fun w => sat_shift φ (v.bind x.name w) j
  | .tp x, v, j => by
    simp only [Sat]

theorem denotes_shift : (t : Term) → (v : Valuation) → (j : Nat) → (c : CVal) →
    (Denotes ι rate (σ.shift d) e vis v j t c ↔ Denotes ι rate σ e vis v j t c)
  | .agg a, v, j, c => by
    simp only [Denotes]
    exact exists_congr fun n => and_congr_left fun _ => total_shift a v j n
  | .arith _ l r, v, j, c => by
    simp only [Denotes]
    exact exists_congr fun m => exists_congr fun n => by
      rw [denotes_shift l v j (.num m), denotes_shift r v j (.num n)]
  | .entity _, _, _, _ => by simp only [Denotes]
  | .long _, _, _, _ => by simp only [Denotes]
  | .decimal _, _, _, _ => by simp only [Denotes]
  | .string _, _, _, _ => by simp only [Denotes]
  | .bool _, _, _, _ => by simp only [Denotes]
  | .context _, _, _, _ => by simp only [Denotes]
  | .scope _ _, _, _, _ => by simp only [Denotes]
  | .var _, _, _, _ => by simp only [Denotes]
  | .wildcard, _, _, _ => by simp only [Denotes]

theorem total_shift : (a : Aggregate) → (v : Valuation) → (j : Nat) → (n : Int) →
    (Total ι rate (σ.shift d) e vis v j a n ↔ Total ι rate σ e vis v j a n)
  | .count dom body, v, j, n => by
    have ih := fun v' => sat_shift body v' j
    simp only [Total, ih]
  | .sum s dom body, v, j, n => by
    have ih := fun v' => sat_shift body v' j
    simp only [Total, ih]

end

end

/-- The schema's visibility does not read timestamps. -/
theorem visible_shift (S : EventSchema) (d : Int) (σ : Trace) (e : Event) (k : Nat) :
    S.Visible (σ.shift d) e k ↔ S.Visible σ e k := by
  unfold EventSchema.Visible
  rw [shift_getElem?]
  cases σ[k]? <;> simp

theorem leafHolds_shift {ι : ImplChoices} {P : PolicySet} {d : Int} {σ : Trace} {n : Nat}
    {φ : Formula} : P.LeafHolds ι (σ.shift d) n φ ↔ P.LeafHolds ι σ n φ := by
  unfold PolicySet.LeafHolds
  rw [shift_getElem?]
  cases hσ : σ[n]? with
  | none => simp
  | some p =>
    simp only [Option.map_some, Option.some.injEq, exists_eq_left']
    have hvis : P.schema.Visible (σ.shift d) p.event = P.schema.Visible σ p.event :=
      funext fun k => propext (visible_shift _ d σ _ k)
    rw [hvis]
    exact sat_shift _ _ _

/-- **Shifting time preserves decisions.** The decision at timepoint `n` of the trace with every
timestamp shifted by `d` is the decision at `n` of the trace. -/
theorem authorize_shift {ι : ImplChoices} {P : PolicySet} {ω : Provider.Providers} (d : Int)
    (σ : Trace) (n : Nat) : P.authorize ι ω (σ.shift d) n = P.authorize ι ω σ n := by
  unfold PolicySet.authorize
  refine decideWith_congr_event (shift_event? d σ n) fun p pr rs _ _ => ?_
  simp only [PolicySet.respond]
  refine supervaluate_congr fun ι' _ => ?_
  have hleaves : P.leaves ι' ω (σ.shift d) n p.event = P.leaves ι' ω σ n p.event := by
    simp only [PolicySet.leaves, Leaves.mk.injEq, and_true]
    funext φ
    exact decide_eq_decide.mpr leafHolds_shift
  rw [hleaves]

/-! ## Shifting time, for every kind of decision -/

/-- Stamping one event commutes with shifting: `max (c + d) (l + d + 1) = max c (l + 1) + d`. -/
theorem stampAfter_shift (d : Int) : ∀ (last : Option Int) (c : Int),
    stampAfter (last.map (· + d)) (c + d) = stampAfter last c + d
  | none, _ => rfl
  | some l, c => by simp only [Option.map_some, stampAfter]; omega

private theorem stamp_go_shift (d : Int) : ∀ (last : Option Int) (σ : Trace),
    Trace.stamp.go (last.map (· + d)) (σ.shift d) = (Trace.stamp.go last σ).shift d
  | _, [] => rfl
  | last, p :: σ => by
    simp only [Trace.shift, List.map_cons, Trace.stamp.go] at *
    rw [stampAfter_shift d last p.ts]
    have := stamp_go_shift d (some (stampAfter last p.ts)) σ
    simp only [Option.map_some, Trace.shift] at this
    rw [this]

/-- **Stamping commutes with shifting**: stamping a shifted trace is shifting the stamped one. -/
theorem stamp_shift (d : Int) (σ : Trace) : (σ.shift d).stamp = σ.stamp.shift d :=
  stamp_go_shift d none σ

theorem partitionLog_shift (S : EventSchema) (d : Int) (ρ : Trace) (n : Nat) (e : Event) :
    S.partitionLog (ρ.shift d) n e = (S.partitionLog ρ n e).shift d := by
  simp only [EventSchema.partitionLog, EventSchema.keyLog, Trace.shift]
  rw [← List.map_take, List.filter_map]
  rfl

theorem partLeafHolds_shift {ι : ImplChoices} {P : PolicySet} {d : Int} {ρ : Trace} {n : Nat}
    {φ : Formula} : P.PartLeafHolds ι (ρ.shift d) n φ ↔ P.PartLeafHolds ι ρ n φ := by
  unfold PolicySet.PartLeafHolds
  rw [shift_getElem?]
  cases ρ[n]? with
  | none => simp
  | some p =>
    simp only [Option.map_some, Option.some.injEq, exists_eq_left']
    rw [partitionLog_shift, stamp_shift, shift_length]
    exact sat_shift _ _ _

/-- **Shifting time preserves partitioned decisions.** -/
theorem authorizePart_shift {ι : ImplChoices} {P : PolicySet} {ω : Provider.Providers} (d : Int)
    (ρ : Trace) (n : Nat) : P.authorizePart ι ω (ρ.shift d) n = P.authorizePart ι ω ρ n := by
  unfold PolicySet.authorizePart
  refine decideWith_congr_event (shift_event? d ρ n) fun p pr rs _ _ => ?_
  simp only [PolicySet.respondPart]
  refine supervaluate_congr fun ι' _ => ?_
  have : P.partLeaves ι' ω (ρ.shift d) n p.event = P.partLeaves ι' ω ρ n p.event := by
    simp only [PolicySet.partLeaves, Leaves.mk.injEq, and_true]
    funext φ
    exact decide_eq_decide.mpr partLeafHolds_shift
  rw [this]

theorem leafHoldsFrom_shift {ι : ImplChoices} {P : PolicySet} {d : Int} {σ : Trace} {s n : Nat}
    {φ : Formula} : P.LeafHoldsFrom ι (σ.shift d) s n φ ↔ P.LeafHoldsFrom ι σ s n φ := by
  unfold PolicySet.LeafHoldsFrom
  rw [shift_getElem?]
  cases σ[n]? with
  | none => simp
  | some p =>
    simp only [Option.map_some, Option.some.injEq, exists_eq_left']
    have hvis : (fun k => s ≤ k ∧ P.schema.Visible (σ.shift d) p.event k) =
        (fun k => s ≤ k ∧ P.schema.Visible σ p.event k) :=
      funext fun k => by rw [visible_shift]
    rw [hvis]
    exact sat_shift _ _ _

/-- **Shifting time preserves decisions with rules deployed from timepoints of their own.** -/
theorem authorizeDeployed_shift {ι : ImplChoices} {P : PolicySet} {ω : Provider.Providers}
    (d : Int) (σ : Trace) (n : Nat) (rules : List (Policy × Nat)) :
    P.authorizeDeployed ι ω (σ.shift d) n rules = P.authorizeDeployed ι ω σ n rules := by
  unfold PolicySet.authorizeDeployed
  refine decideWith_congr_event (shift_event? d σ n) fun p pr rs _ _ => ?_
  refine supervaluate_congr fun ι' _ => ?_
  have : ∀ s, P.leavesFrom ι' ω (σ.shift d) s n p.event = P.leavesFrom ι' ω σ s n p.event := by
    intro s
    simp only [PolicySet.leavesFrom, Leaves.mk.injEq, and_true]
    funext φ
    exact decide_eq_decide.mpr leafHoldsFrom_shift
  simp only [this]

/-- A log with the timestamp of every event shifted by `d`. -/
def _root_.Dogwood.Spec.Log.shift (d : Int) (log : Log) : Log :=
  log.map fun
    | .event p => .event ⟨p.ts + d, p.event⟩
    | .deploy rs => .deploy rs

theorem Log.trace_shift (d : Int) (log : Log) : (log.shift d).trace = log.trace.shift d := by
  induction log with
  | nil => rfl
  | cons x log ih =>
    cases x <;> simp_all [Log.shift, Log.trace, Entry.event?, Trace.shift, List.filterMap_cons]

private theorem step_shift (d : Int) (st : Log.State) (x : Entry) :
    st.step (match x with
      | .event p => .event ⟨p.ts + d, p.event⟩
      | .deploy rs => .deploy rs) = st.step x := by
  cases x <;> rfl

theorem Log.state_shift (P : PolicySet) (d : Int) (log : Log) :
    Log.state P (log.shift d) = Log.state P log := by
  unfold Log.state Log.shift
  rw [List.foldl_map]
  exact congrArg (fun g => List.foldl g (Log.State.initial P) log)
    (funext fun st => funext fun x => step_shift d st x)

/-- **Shifting time preserves decisions over a log of events and deployments.** -/
theorem Log.decide_shift (reading : UpdateReading) (ι : ImplChoices) (P : PolicySet)
    (ω : Provider.Providers) (d : Int) (log : Log) (i : Nat) :
    Log.decide reading ι P ω (log.shift d) i = Log.decide reading ι P ω log i := by
  unfold Log.decide
  have hget : (log.shift d)[i]? = log[i]?.map fun
      | .event p => .event ⟨p.ts + d, p.event⟩
      | .deploy rs => .deploy rs := by
    simp [Log.shift, List.getElem?_map]
  have htake : (log.shift d).take i = Log.shift d (log.take i) := by
    simp [Log.shift]
  rw [hget, htake, Log.state_shift, Log.trace_shift]
  cases log[i]? with
  | none => rfl
  | some x =>
    cases x with
    | event p => exact authorizeDeployed_shift d _ _ _
    | deploy rs => rfl

/-- An arrival with its clock reading shifted by `d`. -/
def _root_.Dogwood.Spec.Arrival.shift (d : Int) : Arrival → Arrival
  | .event e c => .event e (c + d)
  | .deploy rs => .deploy rs

private theorem lastTs?_shift (d : Int) (log : Log) :
    (log.shift d).lastTs? = log.lastTs?.map (· + d) := by
  simp [Log.lastTs?, Log.trace_shift, Trace.shift, List.getLast?_map, Option.map_map]
  rfl

private theorem entry_shift (d : Int) (last : Option Int) (x : Arrival) :
    (x.shift d).entry (last.map (· + d)) =
      (match x.entry last with
        | .event p => Entry.event ⟨p.ts + d, p.event⟩
        | .deploy rs => .deploy rs) := by
  cases x with
  | event e c => simp only [Arrival.shift, Arrival.entry, stampAfter_shift]
  | deploy rs => rfl

/-- **Shifting the clock commutes with ingestion**, one arrival: the log is the shifted log, and
the reply is the same. -/
theorem submit_shift (reading : UpdateReading) (ι : Temporal.ImplChoices) (P : PolicySet)
    (ω : Provider.Providers) (d : Int) (log : Log) (x : Arrival) :
    Log.submit reading ι P ω (log.shift d) (x.shift d) =
      ((Log.submit reading ι P ω log x).1.shift d, (Log.submit reading ι P ω log x).2) := by
  have hn : (x.shift d).nonconformance? P = x.nonconformance? P := by cases x <;> rfl
  unfold Log.submit
  rw [hn]
  cases x.nonconformance? P with
  | some r => rfl
  | none =>
    simp only [lastTs?_shift, entry_shift]
    have : log.shift d ++ [match x.entry log.lastTs? with
        | .event p => Entry.event ⟨p.ts + d, p.event⟩
        | .deploy rs => .deploy rs] = (log ++ [x.entry log.lastTs?]).shift d := by
      simp only [Log.shift, List.map_append, List.map_cons, List.map_nil]
    rw [this, Log.decide_shift]
    simp [Log.shift]

/-- **Shifting the clock commutes with ingestion**, over a stream of arrivals. -/
theorem ingest_shift (reading : UpdateReading) (ι : Temporal.ImplChoices) (P : PolicySet)
    (ω : Provider.Providers) (d : Int) : ∀ (log : Log) (xs : List Arrival),
    Log.ingest reading ι P ω (log.shift d) (xs.map (Arrival.shift d)) =
      ((Log.ingest reading ι P ω log xs).1.shift d, (Log.ingest reading ι P ω log xs).2)
  | _, [] => rfl
  | log, x :: xs => by
    simp only [List.map_cons, Log.ingest, submit_shift, ingest_shift reading ι P ω d _ xs]

/-! ## The order of conjuncts -/

section

variable {ι : ImplChoices} {rate : TickRate} {σ : Trace} {e : Event} {vis : Nat → Prop}

/-- **`&&` is commutative.** -/
theorem sat_and_comm {v : Valuation} {j : Nat} {φ ψ : Formula} :
    Sat ι rate σ e vis v j (.and φ ψ) ↔ Sat ι rate σ e vis v j (.and ψ φ) := by
  simp only [Sat]
  exact And.comm

end

/-- **Restriction does not depend on the order of conjuncts.** -/
theorem _root_.Dogwood.Spec.Temporal.Formula.restricts_and_comm {R : VarName → Prop}
    {φ ψ : Formula} {x : VarName} :
    (Formula.and φ ψ).Restricts R x ↔ (Formula.and ψ φ).Restricts R x := by
  simp only [Formula.Restricts]
  exact forall_congr' fun S => imp_congr_right fun _ =>
    ⟨fun h h₂ h₁ => h h₁ h₂, fun h h₁ h₂ => h h₂ h₁⟩

/-- **Safety does not depend on the order of conjuncts.** -/
theorem _root_.Dogwood.Spec.Temporal.Formula.safe_and_comm {R : VarName → Prop}
    {φ ψ : Formula} : (Formula.and φ ψ).Safe R ↔ (Formula.and ψ φ).Safe R := by
  have : (Formula.and φ ψ).Restricts R = (Formula.and ψ φ).Restricts R :=
    funext fun _ => propext Formula.restricts_and_comm
  simp only [Formula.Safe, this]
  exact And.comm

/-- **Typing does not depend on the order of conjuncts.** -/
theorem _root_.Dogwood.Spec.Temporal.Formula.wellTyped_and_comm {C : TypingCtx} {Γ : Bindings}
    {φ ψ : Formula} :
    Formula.WellTyped C Γ (.and φ ψ) ↔ Formula.WellTyped C Γ (.and ψ φ) := by
  constructor <;> intro h <;> cases h with
  | and h₁ h₂ => exact .and h₂ h₁

/-- **The horizon does not depend on the order of conjuncts.** -/
theorem _root_.Dogwood.Spec.Temporal.Formula.horizon_and_comm {rate : TickRate}
    {φ ψ : Formula} :
    (Formula.and φ ψ).horizon rate = (Formula.and ψ φ).horizon rate := by
  simp only [Formula.horizon]
  exact Int.max_comm _ _

/-- **The free variables do not depend on the order of conjuncts**, as a set. -/
theorem _root_.Dogwood.Spec.Temporal.Formula.mem_fv_and_comm {φ ψ : Formula} {x : VarName} :
    x ∈ (Formula.and φ ψ).fv ↔ x ∈ (Formula.and ψ φ).fv := by
  simp only [Formula.fv, List.mem_append]
  exact Or.comm

/-! ## Renaming policy ids -/

open Cedar.Spec (Request Entities Response PolicyID Effect)
open Cedar.Data (Set)

/-- The policies with their ids renamed by `f`. -/
def renameIds (f : PolicyID → PolicyID) (ps : Policies) : Policies :=
  ps.map fun p => { p with id := f p.id }

/-- A response with its determining and erroring policies renamed by `f`. -/
def _root_.Cedar.Spec.Response.renameIds (f : PolicyID → PolicyID) (r : Response) : Response where
  decision := r.decision
  determiningPolicies := r.determiningPolicies.map f
  erroringPolicies := r.erroringPolicies.map f

section

variable (θ : Leaves) (f : PolicyID → PolicyID)

theorem satisfiedPolicies_renameIds (eff : Effect) (ps : Policies) (req : Request)
    (es : Entities) :
    satisfiedPolicies θ eff (renameIds f ps) req es =
      (satisfiedPolicies θ eff ps req es).map f := by
  unfold satisfiedPolicies
  rw [Set.map_make, renameIds, List.filterMap_map, List.map_filterMap]
  congr 1
  refine Cedar.List.filterMap_congr fun p _ => ?_
  unfold satisfiedWithEffect
  rw [apply_ite (Option.map f)]
  rfl

theorem errorPolicies_renameIds (ps : Policies) (req : Request) (es : Entities) :
    errorPolicies θ (renameIds f ps) req es =
      (errorPolicies θ ps req es).map f := by
  unfold errorPolicies
  rw [Set.map_make, renameIds, List.filterMap_map, List.map_filterMap]
  congr 1
  refine Cedar.List.filterMap_congr fun p _ => ?_
  unfold errored
  rw [apply_ite (Option.map f)]
  rfl

private theorem isEmpty_map (s : Set PolicyID) : (s.map f).isEmpty = s.isEmpty := by
  cases s with
  | mk l =>
    rw [Bool.eq_iff_iff, Set.map, Set.isEmpty_make, Set.isEmpty_iff_eq_empty, Set.empty,
      Set.mk.injEq]
    exact List.map_eq_nil_iff

/-- **The authorizer does not read policy ids.** Renaming the policies' ids gives the same
decision, with the determining and erroring policies renamed alike. -/
theorem isAuthorized_renameIds (req : Request) (es : Entities) (ps : Policies) :
    isAuthorized θ req es (renameIds f ps) = (isAuthorized θ req es ps).renameIds f := by
  unfold isAuthorized
  dsimp only
  rw [satisfiedPolicies_renameIds, satisfiedPolicies_renameIds, errorPolicies_renameIds,
    isEmpty_map, isEmpty_map]
  split <;> rfl

/-- **The decision does not read policy ids**, per request. -/
theorem isAuthorized_renameIds_decision (req : Request) (es : Entities) (ps : Policies) :
    (isAuthorized θ req es (renameIds f ps)).decision = (isAuthorized θ req es ps).decision := by
  rw [isAuthorized_renameIds]
  rfl

end

/-- An outcome with the policies of its response renamed by `f`. -/
def _root_.Dogwood.Spec.Outcome.renameIds (f : PolicyID → PolicyID) : Outcome → Outcome
  | .noDecision => .noDecision
  | .failClosed r => .failClosed r
  | .decided r => .decided (r.renameIds f)

theorem _root_.Dogwood.Spec.Outcome.renameIds_decision? (f : PolicyID → PolicyID) (o : Outcome) :
    (o.renameIds f).decision? = o.decision? := by
  cases o <;> rfl

private theorem providerCalls_renameIds (f : PolicyID → PolicyID) (ps : Policies) :
    (renameIds f ps).providerCalls = ps.providerCalls := by
  simp only [renameIds, Policies.providerCalls, List.flatMap_map]
  rfl

private theorem scopeEntitiesSupplied_renameIds (f : PolicyID → PolicyID) (P : PolicySet)
    (ps : Policies) (e : Event) (pr rs : Cedar.Spec.EntityUID) :
    P.scopeEntitiesSupplied (renameIds f ps) e pr rs = P.scopeEntitiesSupplied ps e pr rs := by
  simp only [PolicySet.scopeEntitiesSupplied, renameIds, List.all_map]
  rfl

/-- A decision whose response is mapped by `k` is the decision mapped by `k`. -/
private theorem decideWith_map_response {P : PolicySet} {rules : Policies}
    {ω : Provider.Providers} {σ : Trace} {n : Nat}
    {respond : Event → Cedar.Spec.EntityUID → Cedar.Spec.EntityUID → Option Response}
    (f : PolicyID → PolicyID) :
    P.decideWith rules ω σ n (fun e pr rs => (respond e pr rs).map (·.renameIds f)) =
      (P.decideWith rules ω σ n respond).renameIds f := by
  cases hd : P.decideWith rules ω σ n respond with
  | decided r =>
    obtain ⟨p, pr, rs, hσ, ha, hr⟩ := decideWith_eq_decided hd
    rw [decideWith_of_admits hσ ha, hr]
    rfl
  | failClosed reason =>
    by_cases ht : reason = .temporalError
    · subst ht
      obtain ⟨p, pr, rs, hσ, ha, hr⟩ := decideWith_eq_temporalError hd
      rw [decideWith_of_admits hσ ha, hr]
      rfl
    · have hc : P.decideWith rules ω σ n (fun e pr rs => (respond e pr rs).map (·.renameIds f)) =
          P.decideWith rules ω σ n respond := by
        refine decideWith_congr rfl fun p pr rs hσ ha => ?_
        exfalso
        rw [decideWith_of_admits hσ ha] at hd
        cases hr : respond p.event pr rs <;> rw [hr] at hd <;> simp at hd
        exact ht hd.symm
      rw [hc, hd]
      rfl
  | noDecision =>
    have hc : P.decideWith rules ω σ n (fun e pr rs => (respond e pr rs).map (·.renameIds f)) =
        P.decideWith rules ω σ n respond := by
      refine decideWith_congr rfl fun p pr rs hσ ha => ?_
      exfalso
      rw [decideWith_of_admits hσ ha] at hd
      cases hr : respond p.event pr rs <;> rw [hr] at hd <;> simp at hd
    rw [hc, hd]
    rfl

/-- Renaming policy ids changes a decision over a trace only through its response. -/
private theorem authorize_renameIds_of_respond {ι : ImplChoices} {P : PolicySet}
    {ω : Provider.Providers} {f : PolicyID → PolicyID} {σ : Trace} {n : Nat}
    (h : ∀ p pr rs, σ[n]? = some p → P.Admits P.policies ω p pr rs →
      ({ P with policies := renameIds f P.policies } : PolicySet).respond ι ω σ n p.event pr rs =
        (P.respond ι ω σ n p.event pr rs).map (·.renameIds f)) :
    ({ P with policies := renameIds f P.policies } : PolicySet).authorize ι ω σ n =
      (P.authorize ι ω σ n).renameIds f := by
  unfold PolicySet.authorize
  have hP : ∀ rules respond, ({ P with policies := renameIds f P.policies } : PolicySet).decideWith
      rules ω σ n respond = P.decideWith rules ω σ n respond := fun _ _ => rfl
  rw [hP, decideWith_rules_congr (rules₂ := P.policies)
    (fun e => by simp only [Policies.providersFail, providerCalls_renameIds])
    (fun e => by simp only [PolicySet.providerOutputsConform, providerCalls_renameIds])
    (fun e pr rs => scopeEntitiesSupplied_renameIds f P P.policies e pr rs),
    ← decideWith_map_response]
  exact decideWith_congr rfl h

/-- **Decisions do not read policy ids**, over a trace, under a total reading: the policy set with
its rules' ids renamed by `f` has the outcome of the policy set, with the policies of its response
renamed alike. -/
theorem authorize_renameIds {ι : ImplChoices} (hι : ι.Total) {P : PolicySet}
    {ω : Provider.Providers} (f : PolicyID → PolicyID) (σ : Trace) (n : Nat) :
    ({ P with policies := renameIds f P.policies } : PolicySet).authorize ι ω σ n =
      (P.authorize ι ω σ n).renameIds f := by
  refine authorize_renameIds_of_respond fun p pr rs _ _ => ?_
  rw [respond_total hι, respond_total hι]
  simp only [Option.map_some]
  exact congrArg some (isAuthorized_renameIds _ f _ _ _)

/-- **The decision does not read policy ids**, over a trace, under a total reading. -/
theorem authorize_renameIds_decision? {ι : ImplChoices} (hι : ι.Total) {P : PolicySet}
    {ω : Provider.Providers} (f : PolicyID → PolicyID) (σ : Trace) (n : Nat) :
    (({ P with policies := renameIds f P.policies } : PolicySet).authorize ι ω σ n).decision? =
      (P.authorize ι ω σ n).decision? := by
  rw [authorize_renameIds hι, Outcome.renameIds_decision?]

/-! ## Policy ids, under every reading -/

private theorem equiv_of_map_equiv {f : PolicyID → PolicyID} (hf : Function.Injective f)
    {a b : List PolicyID} (h : a.map f ≡ b.map f) : a ≡ b := by
  simp only [List.Equiv, List.subset_def, List.mem_map] at *
  refine ⟨fun {x} hx => ?_, fun {x} hx => ?_⟩
  · obtain ⟨y, hy, hxy⟩ := h.1 ⟨x, hx, rfl⟩
    rw [← hf hxy]
    exact hy
  · obtain ⟨y, hy, hxy⟩ := h.2 ⟨x, hx, rfl⟩
    rw [← hf hxy]
    exact hy

private theorem map_make_inj {f : PolicyID → PolicyID} (hf : Function.Injective f)
    {a b : List PolicyID} (h : (Set.make a).map f = (Set.make b).map f) :
    Set.make a = Set.make b := by
  rw [Set.map_make, Set.map_make, Set.make_make_eqv] at h
  rw [Set.make_make_eqv]
  exact equiv_of_map_equiv hf h

/-- The policy sets of a response are canonical, as `isAuthorized` builds them. -/
private def CanonResponse (r : Response) : Prop :=
  ∃ a b, r.determiningPolicies = Set.make a ∧ r.erroringPolicies = Set.make b

private theorem renameIds_inj {f : PolicyID → PolicyID} (hf : Function.Injective f)
    {r₁ r₂ : Response} (h₁ : CanonResponse r₁) (h₂ : CanonResponse r₂)
    (h : r₁.renameIds f = r₂.renameIds f) : r₁ = r₂ := by
  obtain ⟨a₁, b₁, hd₁, he₁⟩ := h₁
  obtain ⟨a₂, b₂, hd₂, he₂⟩ := h₂
  cases r₁
  cases r₂
  simp only [Response.renameIds, Response.mk.injEq] at h hd₁ he₁ hd₂ he₂ ⊢
  subst hd₁ he₁ hd₂ he₂
  exact ⟨h.1, map_make_inj hf h.2.1, map_make_inj hf h.2.2⟩

private theorem canon_isAuthorized (θ : Leaves) (req : Request) (es : Entities) (ps : Policies) :
    CanonResponse (isAuthorized θ req es ps) := by
  unfold isAuthorized satisfiedPolicies errorPolicies
  dsimp only
  split
  · exact ⟨_, _, rfl, rfl⟩
  · exact ⟨_, _, rfl, rfl⟩

private theorem supervaluate_map_inj {α β : Type} {ι : ImplChoices} {g : ImplChoices → α}
    (k : α → β) (C : α → Prop) (hC : ∀ ι', C (g ι')) (hk : ∀ x y, C x → C y → k x = k y → x = y) :
    ι.supervaluate (fun ι' => k (g ι')) = (ι.supervaluate g).map k := by
  cases h : ι.supervaluate g with
  | some r => exact supervaluate_map k h
  | none =>
    obtain ⟨ι₁, ι₂, h₁, h₂, hne⟩ := supervaluate_eq_none_iff.mp h
    exact supervaluate_eq_none_iff.mpr ⟨ι₁, ι₂, h₁, h₂, fun he => hne (hk _ _ (hC _) (hC _) he)⟩

/-- **Decisions do not read policy ids**, over a trace, under every reading, for an injective
renaming: supervaluation compares responses, and an injective renaming keeps distinct responses
distinct. -/
theorem authorize_renameIds_of_injective {ι : ImplChoices} {P : PolicySet}
    {ω : Provider.Providers} {f : PolicyID → PolicyID} (hf : Function.Injective f)
    (σ : Trace) (n : Nat) :
    ({ P with policies := renameIds f P.policies } : PolicySet).authorize ι ω σ n =
      (P.authorize ι ω σ n).renameIds f := by
  refine authorize_renameIds_of_respond fun p pr rs _ _ => ?_
  simp only [PolicySet.respond]
  have : ∀ ι', isAuthorized (P.leaves ι' ω σ n p.event) (p.event.request pr rs)
      (P.decisionEntities p.event) (renameIds f P.policies) =
      (isAuthorized (P.leaves ι' ω σ n p.event) (p.event.request pr rs)
        (P.decisionEntities p.event) P.policies).renameIds f :=
    fun ι' => isAuthorized_renameIds _ f _ _ _
  refine (supervaluate_congr fun ι' _ => this ι').trans ?_
  exact supervaluate_map_inj (Response.renameIds f) CanonResponse
    (fun _ => canon_isAuthorized _ _ _ _) fun _ _ h₁ h₂ h => renameIds_inj hf h₁ h₂ h

end Dogwood.Thm

/-! ## Renaming variables -/

namespace Dogwood.Spec.Temporal

/-- A binder renamed by `ρ`. -/
def Binder.rename (ρ : VarName → VarName) (b : Binder) : Binder := { b with name := ρ b.name }

mutual

/-- A term with every variable renamed by `ρ`. -/
def Term.rename (ρ : VarName → VarName) : Term → Term
  | .var x => .var (ρ x)
  | .agg a => .agg (a.rename ρ)
  | .arith op l r => .arith op (l.rename ρ) (r.rename ρ)
  | t => t

/-- An aggregate with every variable, its `for` variables and summand included, renamed by `ρ`. -/
def Aggregate.rename (ρ : VarName → VarName) : Aggregate → Aggregate
  | .count dom body => .count (dom.map (Binder.rename ρ)) (body.rename ρ)
  | .sum s dom body => .sum (ρ s) (dom.map (Binder.rename ρ)) (body.rename ρ)

/-- A condition with every variable, free and bound, renamed by `ρ`. -/
def Formula.rename (ρ : VarName → VarName) : Formula → Formula
  | .and φ ψ => .and (φ.rename ρ) (ψ.rename ρ)
  | .not φ => .not (φ.rename ρ)
  | .formerly w φ => .formerly w (φ.rename ρ)
  | .previous w φ => .previous w (φ.rename ρ)
  | .since φ w ψ => .since (φ.rename ρ) w (ψ.rename ρ)
  | .pred a kd args => .pred a kd (Formula.argsRename ρ args)
  | .cmp op l r => .cmp op (l.rename ρ) (r.rename ρ)
  | .exist x φ => .exist (x.rename ρ) (φ.rename ρ)
  | .tp x => .tp (ρ x)

def Formula.argsRename (ρ : VarName → VarName) : List (Path × Term) → List (Path × Term)
  | [] => []
  | (p, t) :: args => (p, t.rename ρ) :: Formula.argsRename ρ args

end

theorem Formula.argsRename_eq (ρ : VarName → VarName) :
    (args : List (Path × Term)) → Formula.argsRename ρ args = args.map fun a => (a.1, a.2.rename ρ)
  | [] => rfl
  | (_, _) :: args => by simp only [Formula.argsRename, List.map_cons, argsRename_eq ρ args]

end Dogwood.Spec.Temporal

namespace Dogwood.Thm

open Dogwood.Spec Dogwood.Spec.Temporal

section

variable {ρ : VarName → VarName} (hρ : Function.Injective ρ)

include hρ

private theorem bind_rename {v v' : Valuation} {x z : VarName} {w : TVal}
    (h : z = x ∨ v' (ρ z) = v z) : (v'.bind (ρ x) w) (ρ z) = (v.bind x w) z := by
  unfold Valuation.bind
  by_cases hz : z = x
  · subst hz
    simp
  · have : ρ z ≠ ρ x := fun h' => hz (hρ h')
    simp only [this, hz, ite_false]
    exact h.resolve_left hz

private theorem bindAll_rename : (names : List VarName) → (row : List TVal) →
    {v v' : Valuation} → {z : VarName} → row.length = names.length →
    (z ∈ names ∨ v' (ρ z) = v z) →
    (v'.bindAll (names.map ρ) row) (ρ z) = (v.bindAll names row) z
  | [], [], _, _, _, _, h => by
    simp only [List.not_mem_nil, false_or] at h
    exact h
  | x :: xs, w :: ws, v, v', z, hlen, h => by
    simp only [List.map_cons, Valuation.bindAll]
    refine bindAll_rename xs ws (by simpa using hlen) ?_
    by_cases hz : z ∈ xs
    · exact .inl hz
    · refine .inr (bind_rename hρ ?_)
      rcases h with h | h
      · rcases List.mem_cons.mp h with h | h
        · exact .inl h
        · exact absurd h hz
      · by_cases hzx : z = x
        · exact .inl hzx
        · exact .inr h
  | [], _ :: _, _, _, _, hlen, _ => by simp at hlen
  | _ :: _, [], _, _, _, hlen, _ => by simp at hlen

private theorem dedup_map : (xs : List VarName) → dedup (xs.map ρ) = (dedup xs).map ρ
  | [] => rfl
  | x :: xs => by
    simp only [List.map_cons, dedup, dedup_map xs, List.filter_map]
    congr 2
    refine List.filter_congr fun y _ => ?_
    show (ρ y != ρ x) = (y != x)
    by_cases h : y = x
    · subst h
      simp
    · have : ρ y ≠ ρ x := fun h' => h (hρ h')
      rw [Bool.eq_iff_iff, bne_iff_ne, bne_iff_ne]
      exact ⟨fun _ => h, fun _ => this⟩

private theorem domainNames_rename (dom : List Binder) :
    domainNames (dom.map (Binder.rename ρ)) = (domainNames dom).map ρ := by
  have : (dom.map (Binder.rename ρ)).map (·.name) = (dom.map (·.name)).map ρ := by
    simp only [List.map_map]
    rfl
  simp only [domainNames, this]
  exact dedup_map hρ (dom.map (·.name))

private theorem summand_varRename (s : VarName) : (names : List VarName) → (row : List TVal) →
    summand (ρ s) (names.map ρ) row = summand s names row := by
  intro names row
  unfold summand
  congr 1
  induction names generalizing row with
  | nil => rfl
  | cons x xs ih =>
    cases row with
    | nil => rfl
    | cons w ws =>
      simp only [List.map_cons, List.zip_cons_cons]
      by_cases h : s = x
      · subst h
        simp [List.lookup]
      · have : ρ s ≠ ρ x := fun h' => h (hρ h')
        have h₁ : (ρ s == ρ x) = false := by simp [this]
        have h₂ : (s == x) = false := by simp [h]
        simp only [List.lookup, h₁, h₂]
        exact ih ws

omit hρ in
private theorem matches_varRename {e : Event} {v v' : Valuation} (t : Term) (w : Cedar.Spec.Value)
    (hv : ∀ z ∈ t.fv, v' (ρ z) = v z) :
    (t.rename ρ).Matches e v' w ↔ t.Matches e v w := by
  cases t with
  | wildcard => exact Iff.rfl
  | var x =>
    have hx : v' (ρ x) = v x := hv x (by simp [Term.fv])
    simp only [Term.Matches, Term.rename, Term.eval?, hx]
  | agg a => exact Iff.rfl
  | arith op l r => exact Iff.rfl
  | entity _ => exact Iff.rfl
  | long _ => exact Iff.rfl
  | decimal _ => exact Iff.rfl
  | string _ => exact Iff.rfl
  | bool _ => exact Iff.rfl
  | context _ => exact Iff.rfl
  | scope _ _ => exact Iff.rfl

omit hρ in
private theorem argsFv_mem {args : List (Path × Term)} {a : Path × Term} (ha : a ∈ args)
    {z : VarName} (hz : z ∈ a.2.fv) : z ∈ Formula.argsFv args := by
  induction args with
  | nil => cases ha
  | cons b bs ih =>
    rcases List.mem_cons.mp ha with rfl | h
    · simp only [Formula.argsFv, List.mem_append]
      exact .inl hz
    · simp only [Formula.argsFv, List.mem_append]
      exact .inr (ih h)

variable {ι : ImplChoices} {rate : TickRate} {σ : Trace} {e : Event} {vis : Nat → Prop}

-- The members of a mutual block reach a section hypothesis only through each other's calls,
-- which the unused-variable linter does not see.
set_option linter.unusedSectionVars false in
mutual

/-- **Satisfaction is invariant under an injective renaming of variables.** A condition with its
variables renamed by an injective `ρ` holds under `v'` exactly when the condition holds under `v`,
where `v'` gives each renamed free variable `ρ z` the value `v` gives `z`. -/
theorem sat_rename : (φ : Formula) → (v v' : Valuation) → (j : Nat) →
    (∀ z ∈ φ.fv, v' (ρ z) = v z) →
    (Sat ι rate σ e vis v' j (φ.rename ρ) ↔ Sat ι rate σ e vis v j φ)
  | .and φ ψ, v, v', j, h => by
    simp only [Formula.fv, List.mem_append] at h
    simp only [Formula.rename, Sat]
    rw [sat_rename φ v v' j fun z hz => h z (.inl hz),
      sat_rename ψ v v' j fun z hz => h z (.inr hz)]
  | .not φ, v, v', j, h => by
    simp only [Formula.fv] at h
    simp only [Formula.rename, Sat]
    rw [sat_rename φ v v' j h]
  | .formerly w φ, v, v', j, h => by
    simp only [Formula.fv] at h
    simp only [Formula.rename, Sat]
    exact exists_congr fun k => and_congr_right fun _ => and_congr_right fun _ =>
      and_congr_right fun _ => sat_rename φ v v' k h
  | .previous w φ, v, v', j, h => by
    simp only [Formula.fv] at h
    simp only [Formula.rename, Sat]
    exact exists_congr fun k => and_congr_right fun _ => and_congr_right fun _ =>
      and_congr_right fun _ => and_congr_right fun _ => sat_rename φ v v' k h
  | .since φ w ψ, v, v', j, h => by
    simp only [Formula.fv, List.mem_append] at h
    simp only [Formula.rename, Sat]
    refine exists_congr fun k => and_congr_right fun _ => and_congr_right fun _ =>
      and_congr_right fun _ => ?_
    rw [sat_rename ψ v v' k fun z hz => h z (.inr hz)]
    exact and_congr_right fun _ => forall_congr' fun k' => imp_congr_right fun _ =>
      imp_congr_right fun _ => imp_congr_right fun _ =>
        sat_rename φ v v' k' fun z hz => h z (.inl hz)
  | .pred a kd args, v, v', j, h => by
    simp only [Formula.fv] at h
    simp only [Formula.rename, Sat, Formula.argsRename_eq, ArgsMatch, List.forall_mem_map]
    refine exists_congr fun p => and_congr_right fun _ => and_congr_right fun _ =>
      and_congr_right fun _ => forall_congr' fun b => imp_congr_right fun hb => ?_
    exact exists_congr fun w => and_congr_right fun _ =>
      matches_varRename b.2 w fun z hz => h z (argsFv_mem hb hz)
  | .cmp op l r, v, v', j, h => by
    simp only [Formula.fv, List.mem_append] at h
    simp only [Formula.rename, Sat]
    exact exists_congr fun a => exists_congr fun b => by
      rw [denotes_rename l v v' j a fun z hz => h z (.inl hz),
        denotes_rename r v v' j b fun z hz => h z (.inr hz)]
  | .exist x φ, v, v', j, h => by
    simp only [Formula.fv, List.mem_filter, bne_iff_ne, ne_eq] at h
    simp only [Formula.rename, Sat, Binder.rename]
    exact exists_congr fun w => sat_rename φ (v.bind x.name w) (v'.bind (ρ x.name) w) j
      fun z hz => bind_rename hρ (by
        by_cases hzx : z = x.name
        · exact .inl hzx
        · exact .inr (h z ⟨hz, hzx⟩))
  | .tp x, v, v', j, h => by
    simp only [Formula.fv, List.mem_singleton, forall_eq] at h
    simp only [Formula.rename, Sat, h]

theorem denotes_rename : (t : Term) → (v v' : Valuation) → (j : Nat) → (c : CVal) →
    (∀ z ∈ t.fv, v' (ρ z) = v z) →
    (Denotes ι rate σ e vis v' j (t.rename ρ) c ↔ Denotes ι rate σ e vis v j t c)
  | .agg a, v, v', j, c, h => by
    simp only [Term.fv] at h
    simp only [Term.rename, Denotes]
    exact exists_congr fun n => and_congr_left fun _ => total_rename a v v' j n h
  | .arith _ l r, v, v', j, c, h => by
    simp only [Term.fv, List.mem_append] at h
    simp only [Term.rename, Denotes]
    exact exists_congr fun m => exists_congr fun n => by
      rw [denotes_rename l v v' j (.num m) fun z hz => h z (.inl hz),
        denotes_rename r v v' j (.num n) fun z hz => h z (.inr hz)]
  | .var x, v, v', j, c, h => by
    simp only [Term.fv, List.mem_singleton, forall_eq] at h
    simp only [Term.rename, Denotes, Term.eval?, h]
  | .entity _, _, _, _, _, _ => Iff.rfl
  | .long _, _, _, _, _, _ => Iff.rfl
  | .decimal _, _, _, _, _, _ => Iff.rfl
  | .string _, _, _, _, _, _ => Iff.rfl
  | .bool _, _, _, _, _, _ => Iff.rfl
  | .context _, _, _, _, _, _ => Iff.rfl
  | .scope _ _, _, _, _, _, _ => Iff.rfl
  | .wildcard, _, _, _, _, _ => Iff.rfl

theorem total_rename : (a : Aggregate) → (v v' : Valuation) → (j : Nat) → (n : Int) →
    (∀ z ∈ a.fv, v' (ρ z) = v z) →
    (Total ι rate σ e vis v' j (a.rename ρ) n ↔ Total ι rate σ e vis v j a n)
  | .count dom body, v, v', j, n, h => by
    have key : ∀ row : List TVal, row.length = (domainNames dom).length →
        (Sat ι rate σ e vis (v'.bindAll ((domainNames dom).map ρ) row) j (body.rename ρ) ↔
          Sat ι rate σ e vis (v.bindAll (domainNames dom) row) j body) := fun row hl =>
      sat_rename body _ _ j fun z hz => bindAll_rename hρ _ row hl (by
        by_cases hzd : z ∈ domainNames dom
        · exact .inl hzd
        · refine .inr (h z ?_)
          simp only [Aggregate.fv, List.mem_filter, Bool.not_eq_true', List.contains_eq_mem,
            decide_eq_false_iff_not]
          refine ⟨hz, fun hm => hzd ?_⟩
          simpa [domainNames, mem_dedup] using hm)
    simp only [Aggregate.rename, Total, domainNames_rename hρ, List.length_map]
    constructor
    · rintro ⟨rows, hd, hm, rfl⟩
      exact ⟨rows, hd, fun row => (hm row).trans
        ⟨fun ⟨hl, hs⟩ => ⟨hl, (key row hl).mp hs⟩, fun ⟨hl, hs⟩ => ⟨hl, (key row hl).mpr hs⟩⟩, rfl⟩
    · rintro ⟨rows, hd, hm, rfl⟩
      exact ⟨rows, hd, fun row => (hm row).trans
        ⟨fun ⟨hl, hs⟩ => ⟨hl, (key row hl).mpr hs⟩, fun ⟨hl, hs⟩ => ⟨hl, (key row hl).mp hs⟩⟩, rfl⟩
  | .sum s dom body, v, v', j, n, h => by
    have key : ∀ row : List TVal, row.length = (domainNames dom).length →
        (Sat ι rate σ e vis (v'.bindAll ((domainNames dom).map ρ) row) j (body.rename ρ) ↔
          Sat ι rate σ e vis (v.bindAll (domainNames dom) row) j body) := fun row hl =>
      sat_rename body _ _ j fun z hz => bindAll_rename hρ _ row hl (by
        by_cases hzd : z ∈ domainNames dom
        · exact .inl hzd
        · refine .inr (h z ?_)
          simp only [Aggregate.fv, List.mem_filter, Bool.not_eq_true', List.contains_eq_mem,
            decide_eq_false_iff_not]
          refine ⟨hz, fun hm => hzd ?_⟩
          simpa [domainNames, mem_dedup] using hm)
    have hsum : ∀ rows : List (List TVal),
        (rows.map (summand (ρ s) ((domainNames dom).map ρ))).sum =
          (rows.map (summand s (domainNames dom))).sum := fun rows => by
      congr 1
      exact List.map_congr_left fun row _ => summand_varRename hρ s _ row
    simp only [Aggregate.rename, Total, domainNames_rename hρ, List.length_map, hsum]
    constructor
    · rintro ⟨rows, hd, hm, rfl⟩
      exact ⟨rows, hd, fun row => (hm row).trans
        ⟨fun ⟨hl, hs⟩ => ⟨hl, (key row hl).mp hs⟩, fun ⟨hl, hs⟩ => ⟨hl, (key row hl).mpr hs⟩⟩, rfl⟩
    · rintro ⟨rows, hd, hm, rfl⟩
      exact ⟨rows, hd, fun row => (hm row).trans
        ⟨fun ⟨hl, hs⟩ => ⟨hl, (key row hl).mpr hs⟩, fun ⟨hl, hs⟩ => ⟨hl, (key row hl).mp hs⟩⟩, rfl⟩

end

end

/-- The renaming that swaps `x` and `y`. -/
def swapVar (x y : VarName) (z : VarName) : VarName :=
  if z = x then y else if z = y then x else z

theorem swapVar_injective {x y : VarName} : Function.Injective (swapVar x y) := by
  intro a b h
  unfold swapVar at h
  by_cases ha : a = x <;> by_cases hb : b = x <;> by_cases ha' : a = y <;> by_cases hb' : b = y <;>
    simp_all

/-- **Alpha-equivalence.** Renaming the variable an `exists` binds to one the condition does not
use free (swapping the two throughout the body) changes no truth value. -/
theorem sat_exist_alpha {ι : ImplChoices} {rate : TickRate} {σ : Trace} {e : Event}
    {vis : Nat → Prop} {v : Valuation} {j : Nat} {b : Binder} {φ : Formula} {y : VarName}
    (hy : y ∉ (Formula.exist b φ).fv) :
    Sat ι rate σ e vis v j (.exist b φ) ↔
      Sat ι rate σ e vis v j (.exist { b with name := y } (φ.rename (swapVar b.name y))) := by
  have hname : swapVar b.name y b.name = y := by simp [swapVar]
  have := sat_rename (ρ := swapVar b.name y) swapVar_injective (ι := ι) (rate := rate) (σ := σ)
    (e := e) (vis := vis) (.exist b φ) v v j (fun z hz => by
      simp only [Formula.fv, List.mem_filter, bne_iff_ne, ne_eq] at hz
      have hzy : z ≠ y := fun h => hy (by
        subst h
        simp only [Formula.fv, List.mem_filter, bne_iff_ne, ne_eq]
        exact hz)
      simp [swapVar, hz.2, hzy])
  simp only [Formula.rename, Binder.rename, hname] at this
  exact this.symm

end Dogwood.Thm

/-! ## The time-dependence check, and pin injection, under the invariances -/

namespace Dogwood.Spec.Temporal

private theorem term_varies_congr {E E' : List VarName} (h : ∀ x, x ∈ E ↔ x ∈ E') :
    (t : Term) → (t.Varies E ↔ t.Varies E')
  | .var x => h x
  | .agg _ => Iff.rfl
  | .arith _ l r => by simp only [Term.Varies, term_varies_congr h l, term_varies_congr h r]
  | .entity _ | .long _ | .decimal _ | .string _ | .bool _ | .context _ | .scope _ _
  | .wildcard => Iff.rfl

private theorem formula_varies_congr {E E' : List VarName} (h : ∀ x, x ∈ E ↔ x ∈ E') :
    (φ : Formula) → (φ.Varies E ↔ φ.Varies E')
  | .cmp _ l r => by simp only [Formula.Varies, term_varies_congr h l, term_varies_congr h r]
  | .not φ => by simp only [Formula.Varies, formula_varies_congr h φ]
  | .and φ ψ => by
    simp only [Formula.Varies, formula_varies_congr h φ, formula_varies_congr h ψ]
  | .pred _ _ _ | .tp _ | .formerly _ _ | .previous _ _ | .since _ _ _ | .exist _ _ => Iff.rfl

mutual

private theorem formula_scopesVary_congr : {E E' : List VarName} → (∀ x, x ∈ E ↔ x ∈ E') →
    (φ : Formula) → (φ.ScopesVary E ↔ φ.ScopesVary E')
  | _, _, h, .cmp _ l r => by
    simp only [Formula.ScopesVary, term_scopesVary_congr h l, term_scopesVary_congr h r]
  | _, _, h, .not φ => by simp only [Formula.ScopesVary, formula_scopesVary_congr h φ]
  | _, _, h, .and φ ψ => by
    simp only [Formula.ScopesVary, formula_scopesVary_congr h φ, formula_scopesVary_congr h ψ]
  | _, _, h, .formerly _ φ => by
    simp only [Formula.ScopesVary, formula_scopesVary_congr h φ, formula_varies_congr h φ]
  | _, _, h, .previous _ φ => by
    simp only [Formula.ScopesVary, formula_scopesVary_congr h φ, formula_varies_congr h φ]
  | _, _, h, .since φ _ ψ => by
    simp only [Formula.ScopesVary, formula_scopesVary_congr h φ, formula_varies_congr h φ,
      formula_scopesVary_congr h ψ, formula_varies_congr h ψ]
  | E, E', h, .exist x φ => by
    have h' : ∀ z, z ∈ x.name :: E ↔ z ∈ x.name :: E' := fun z => by
      simp only [List.mem_cons, h z]
    simp only [Formula.ScopesVary, formula_scopesVary_congr h' φ, formula_varies_congr h' φ]
  | _, _, _, .pred _ _ _ | _, _, _, .tp _ => Iff.rfl

private theorem term_scopesVary_congr : {E E' : List VarName} → (∀ x, x ∈ E ↔ x ∈ E') →
    (t : Term) → (t.ScopesVary E ↔ t.ScopesVary E')
  | _, _, h, .agg (.count _ body) => by
    simp only [Term.ScopesVary, formula_scopesVary_congr h body, formula_varies_congr h body]
  | E, E', h, .agg (.sum s _ body) => by
    have h' : ∀ z, z ∈ s :: E ↔ z ∈ s :: E' := fun z => by simp only [List.mem_cons, h z]
    simp only [Term.ScopesVary, formula_scopesVary_congr h' body, formula_varies_congr h' body]
  | _, _, h, .arith _ l r => by
    simp only [Term.ScopesVary, term_scopesVary_congr h l, term_scopesVary_congr h r]
  | _, _, _, .var _ | _, _, _, .entity _ | _, _, _, .long _ | _, _, _, .decimal _
  | _, _, _, .string _ | _, _, _, .bool _ | _, _, _, .context _ | _, _, _, .scope _ _
  | _, _, _, .wildcard => Iff.rfl

end

/-- **The time-dependence check does not depend on the order of conjuncts.** With typing and
safety, every part of a temporal leaf's validity is order-independent. -/
theorem Formula.monitorsTime_and_comm {φ ψ : Formula} :
    (Formula.and φ ψ).MonitorsTime ↔ (Formula.and ψ φ).MonitorsTime := by
  have h : ∀ x, x ∈ (Formula.and φ ψ).ruleWideBinders ↔
      x ∈ (Formula.and ψ φ).ruleWideBinders :=
    fun x => by simp only [Formula.ruleWideBinders, List.mem_append]; exact Or.comm
  simp only [Formula.MonitorsTime, Formula.conjuncts, List.mem_append]
  constructor <;> intro H c hc
  · have := H c hc.symm
    exact ⟨(formula_varies_congr h c).mp this.1, (formula_scopesVary_congr h c).mp this.2⟩
  · have := H c hc.symm
    exact ⟨(formula_varies_congr h c).mpr this.1, (formula_scopesVary_congr h c).mpr this.2⟩

private theorem pinRef_toTerm_rename (ρ : VarName → VarName) (r : PinRef) :
    r.toTerm.rename ρ = r.toTerm := by
  cases r <;> rfl

mutual

/-- **Pin injection commutes with renaming variables**: the injected arguments are request-side
paths, which name no variable. -/
theorem Formula.rename_injectPins (ρ : VarName → VarName) (S : EventSchema) :
    (φ : Formula) → (φ.injectPins S).rename ρ = (φ.rename ρ).injectPins S
  | .and φ ψ => by
    simp only [Formula.injectPins, Formula.rename, Formula.rename_injectPins ρ S φ,
      Formula.rename_injectPins ρ S ψ]
  | .not φ => by simp only [Formula.injectPins, Formula.rename, Formula.rename_injectPins ρ S φ]
  | .formerly w φ => by
    simp only [Formula.injectPins, Formula.rename, Formula.rename_injectPins ρ S φ]
  | .previous w φ => by
    simp only [Formula.injectPins, Formula.rename, Formula.rename_injectPins ρ S φ]
  | .since φ w ψ => by
    simp only [Formula.injectPins, Formula.rename, Formula.rename_injectPins ρ S φ,
      Formula.rename_injectPins ρ S ψ]
  | .pred a k args => by
    simp only [Formula.injectPins, Formula.rename, Formula.argsRename_eq, List.map_append,
      List.map_map]
    congr 2
    exact List.map_congr_left fun p _ => by
      simp only [Function.comp, pinRef_toTerm_rename]
  | .cmp op l r => by
    simp only [Formula.injectPins, Formula.rename, Term.rename_injectPins ρ S l,
      Term.rename_injectPins ρ S r]
  | .exist x φ => by
    simp only [Formula.injectPins, Formula.rename, Formula.rename_injectPins ρ S φ]
  | .tp x => rfl

theorem Term.rename_injectPins (ρ : VarName → VarName) (S : EventSchema) :
    (t : Term) → (t.injectPins S).rename ρ = (t.rename ρ).injectPins S
  | .agg (.count dom body) => by
    simp only [Term.injectPins, Aggregate.injectPins, Term.rename, Aggregate.rename,
      Formula.rename_injectPins ρ S body]
  | .agg (.sum s dom body) => by
    simp only [Term.injectPins, Aggregate.injectPins, Term.rename, Aggregate.rename,
      Formula.rename_injectPins ρ S body]
  | .arith op l r => by
    simp only [Term.injectPins, Term.rename, Term.rename_injectPins ρ S l,
      Term.rename_injectPins ρ S r]
  | .var _ | .entity _ | .long _ | .decimal _ | .string _ | .bool _ | .context _ | .scope _ _
  | .wildcard => rfl

end

end Dogwood.Spec.Temporal

namespace Dogwood.Thm

open Dogwood.Spec Dogwood.Spec.Temporal

/-- **A leaf means the same with its variables renamed**, by any injective renaming: a leaf is
evaluated under the empty valuation, so no free variable needs a value. -/
theorem leafHolds_rename {ι : ImplChoices} {P : PolicySet} {σ : Trace} {n : Nat}
    {ρ : VarName → VarName} (hρ : Function.Injective ρ) {φ : Formula} :
    P.LeafHolds ι σ n (φ.rename ρ) ↔ P.LeafHolds ι σ n φ := by
  unfold PolicySet.LeafHolds
  refine exists_congr fun p => and_congr_right fun _ => ?_
  rw [← Formula.rename_injectPins]
  exact sat_rename hρ _ _ _ _ fun _ _ => rfl

/-- **Alpha-equivalence for aggregates.** Swapping two variables neither of which the aggregate
uses free, such as a `for` variable and a fresh name, throughout the aggregate, binders included,
changes no total. -/
theorem total_alpha {ι : ImplChoices} {rate : TickRate} {σ : Trace} {e : Event}
    {vis : Nat → Prop} {v : Valuation} {j : Nat} {a : Aggregate} {x y : VarName} {n : Int}
    (hx : x ∉ a.fv) (hy : y ∉ a.fv) :
    Total ι rate σ e vis v j (a.rename (swapVar x y)) n ↔ Total ι rate σ e vis v j a n :=
  total_rename swapVar_injective a v v j n fun z hz => by
    have hzx : z ≠ x := fun h => hx (h ▸ hz)
    have hzy : z ≠ y := fun h => hy (h ▸ hz)
    simp [swapVar, hzx, hzy]

end Dogwood.Thm

/-! ## Safety and typing under renaming -/

namespace Dogwood.Spec.Temporal

section

variable {ρ : VarName → VarName} (hρ : Function.Injective ρ)

include hρ

private theorem filter_bne_map {l : List VarName} {x : VarName} :
    (l.map ρ).filter (· != ρ x) = (l.filter (· != x)).map ρ := by
  rw [List.filter_map]
  congr 1
  refine List.filter_congr fun y _ => ?_
  show (ρ y != ρ x) = (y != x)
  by_cases h : y = x
  · subst h
    simp
  · have : ρ y ≠ ρ x := fun h' => h (hρ h')
    rw [Bool.eq_iff_iff, bne_iff_ne, bne_iff_ne]
    exact ⟨fun _ => h, fun _ => this⟩

private theorem contains_map {l : List VarName} {x : VarName} :
    (l.map ρ).contains (ρ x) = l.contains x := by
  rw [Bool.eq_iff_iff, List.contains_iff_mem, List.contains_iff_mem, List.mem_map]
  exact ⟨fun ⟨z, hz, he⟩ => hρ he ▸ hz, fun h => ⟨x, h, rfl⟩⟩

-- The members of a mutual block reach a section hypothesis only through each other's calls,
-- which the unused-variable linter does not see.
set_option linter.unusedSectionVars false in
mutual

/-- Renaming renames the free variables. -/
theorem Term.fv_rename : (t : Term) → (t.rename ρ).fv = t.fv.map ρ
  | .var _ => rfl
  | .agg a => by simp only [Term.rename, Term.fv, Aggregate.fv_rename a]
  | .arith _ l r => by
    simp only [Term.rename, Term.fv, Term.fv_rename l, Term.fv_rename r, List.map_append]
  | .entity _ | .long _ | .decimal _ | .string _ | .bool _ | .context _ | .scope _ _
  | .wildcard => rfl

theorem Aggregate.fv_rename : (a : Aggregate) → (a.rename ρ).fv = a.fv.map ρ
  | .count dom body | .sum _ dom body => by
    simp only [Aggregate.rename, Aggregate.fv, Formula.fv_rename body, List.filter_map]
    congr 1
    refine List.filter_congr fun z _ => ?_
    have : (dom.map (Binder.rename ρ)).map (·.name) = (dom.map (·.name)).map ρ := by
      simp only [List.map_map]
      rfl
    simp only [Function.comp, this, contains_map hρ]

theorem Formula.fv_rename : (φ : Formula) → (φ.rename ρ).fv = φ.fv.map ρ
  | .and φ ψ | .since φ _ ψ => by
    simp only [Formula.rename, Formula.fv, Formula.fv_rename φ, Formula.fv_rename ψ,
      List.map_append]
  | .not φ | .formerly _ φ | .previous _ φ => by
    simp only [Formula.rename, Formula.fv, Formula.fv_rename φ]
  | .pred _ _ args => by simp only [Formula.rename, Formula.fv, Formula.argsFv_rename args]
  | .cmp _ l r => by
    simp only [Formula.rename, Formula.fv, Term.fv_rename l, Term.fv_rename r, List.map_append]
  | .exist x φ => by
    simp only [Formula.rename, Formula.fv, Binder.rename, Formula.fv_rename φ]
    exact filter_bne_map hρ
  | .tp _ => rfl

theorem Formula.argsFv_rename : (args : List (Path × Term)) →
    Formula.argsFv (Formula.argsRename ρ args) = (Formula.argsFv args).map ρ
  | [] => rfl
  | (_, t) :: args => by
    simp only [Formula.argsRename, Formula.argsFv, Term.fv_rename t,
      Formula.argsFv_rename args, List.map_append]

end

end

private theorem rename_eq_var {ρ : VarName → VarName} {t : Term} {u : VarName} :
    t.rename ρ = .var u ↔ ∃ z, t = .var z ∧ ρ z = u := by
  cases t <;> simp [Term.rename]

private theorem hasWildcard_rename (ρ : VarName → VarName) :
    (t : Term) → (t.rename ρ).hasWildcard = t.hasWildcard
  | .arith _ l r => by
    simp only [Term.rename, Term.hasWildcard, hasWildcard_rename ρ l, hasWildcard_rename ρ r]
  | .var _ | .agg _ | .entity _ | .long _ | .decimal _ | .string _ | .bool _ | .context _
  | .scope _ _ | .wildcard => rfl

private theorem eqRestricted?_rename (ρ : VarName → VarName) (l r : Term) :
    eqRestricted? (l.rename ρ) (r.rename ρ) = (eqRestricted? l r).map ρ := by
  cases l <;> cases r <;>
    simp [eqRestricted?, Term.rename, Term.hasWildcard, hasWildcard_rename] <;> split <;> simp_all

private theorem valueSide_rename {ρ : VarName → VarName} (hρ : Function.Injective ρ)
    (x : VarName) (l r : Term) :
    valueSide (ρ x) (l.rename ρ) (r.rename ρ) = (valueSide x l r).rename ρ := by
  cases l with
  | var z =>
    simp only [Term.rename, valueSide]
    by_cases h : z = x
    · subst h
      simp
    · have : ρ z ≠ ρ x := fun h' => h (hρ h')
      simp [h, this, Term.rename]
  | _ => rfl

section

variable {ρ : VarName → VarName} (hinj : Function.Injective ρ)

include hinj

/-- **Restriction is invariant under an injective renaming**, with the restricted-outside
variables renamed alike. -/
theorem Formula.restricts_rename : (φ : Formula) → ∀ (R R' : VarName → Prop),
    (∀ z, R' (ρ z) ↔ R z) → ∀ x, ((φ.rename ρ).Restricts R' (ρ x) ↔ φ.Restricts R x)
  | .pred _ _ args, R, R', _, x => by
    simp only [Formula.rename, Formula.Restricts, Formula.argsRename_eq, List.mem_map,
      Prod.mk.injEq]
    constructor
    · rintro ⟨p, a, ha, rfl, he⟩
      obtain ⟨z, hz, hzx⟩ := rename_eq_var.mp he
      have := hinj hzx
      subst this
      exact ⟨a.1, by rw [← hz]; exact ha⟩
    · rintro ⟨p, hp⟩
      exact ⟨p, (p, .var x), hp, rfl, rfl⟩
  | .tp y, R, R', _, x => by
    simp only [Formula.rename, Formula.Restricts]
    exact ⟨fun h => hinj h, fun h => h ▸ rfl⟩
  | .cmp op l r, R, R', hR, x => by
    cases op with
    | eq =>
      simp only [Formula.rename, Formula.Restricts, eqRestricted?_rename,
        valueSide_rename hinj, Term.fv_rename hinj, List.mem_map]
      constructor
      · rintro ⟨h₁, h₂⟩
        obtain ⟨z, hz, hzx⟩ := Option.map_eq_some_iff.mp h₁
        have := hinj hzx
        subst this
        exact ⟨hz, fun y hy => (hR y).mp (h₂ (ρ y) ⟨y, hy, rfl⟩)⟩
      · rintro ⟨h₁, h₂⟩
        refine ⟨by rw [h₁]; rfl, ?_⟩
        rintro _ ⟨y, hy, rfl⟩
        exact (hR y).mpr (h₂ y hy)
    | _ => simp only [Formula.rename, Formula.Restricts]
  | .not _, _, _, _, _ => by simp only [Formula.rename, Formula.Restricts]
  | .formerly _ φ, R, R', hR, x => by
    simp only [Formula.rename, Formula.Restricts]
    exact Formula.restricts_rename φ R R' hR x
  | .previous _ φ, R, R', hR, x => by
    simp only [Formula.rename, Formula.Restricts]
    exact Formula.restricts_rename φ R R' hR x
  | .since _ _ ψ, R, R', hR, x => by
    simp only [Formula.rename, Formula.Restricts]
    exact Formula.restricts_rename ψ R R' hR x
  | .exist y φ, R, R', hR, x => by
    simp only [Formula.rename, Formula.Restricts, Binder.rename]
    have hR' : ∀ z, ((fun u => u ≠ ρ y.name ∧ R' u) (ρ z) ↔ (fun u => u ≠ y.name ∧ R u) z) :=
      fun z => by
        simp only
        exact and_congr ⟨fun h h' => h (h' ▸ rfl), fun h h' => h (hinj h')⟩ (hR z)
    rw [Formula.restricts_rename φ _ _ hR' x]
    exact and_congr_left fun _ => ⟨fun h h' => h (h' ▸ rfl), fun h h' => h (hinj h')⟩
  | .and φ ψ, R, R', hR, x => by
    simp only [Formula.rename, Formula.Restricts]
    constructor
    · intro h S hS hφ hψ
      let S' : VarName → Prop := fun u => ∀ z, ρ z = u → S z
      have hS' : ∀ z, S' (ρ z) ↔ S z :=
        fun z => ⟨fun h => h z rfl, fun h z' hz' => hinj hz' ▸ h⟩
      have := h S' (fun u hu z hz => by
          subst hz
          exact hS z ((hR z).mp hu))
        (fun u hu z hz => by
          subst hz
          exact hφ z ((Formula.restricts_rename φ S S' hS' z).mp hu))
        (fun u hu z hz => by
          subst hz
          exact hψ z ((Formula.restricts_rename ψ S S' hS' z).mp hu))
      exact (hS' x).mp this
    · intro h S' hS' hφ hψ
      exact h (fun z => S' (ρ z)) (fun z hz => hS' _ ((hR z).mpr hz))
        (fun z hz => hφ _ ((Formula.restricts_rename φ _ S' (fun _ => Iff.rfl) z).mpr hz))
        (fun z hz => hψ _ ((Formula.restricts_rename ψ _ S' (fun _ => Iff.rfl) z).mpr hz))

private theorem restricted_rename {φ : Formula} {R R' : VarName → Prop}
    (hR : ∀ z, R' (ρ z) ↔ R z) (x : VarName) :
    (φ.rename ρ).Restricted R' (ρ x) ↔ φ.Restricted R x := by
  unfold Formula.Restricted
  rw [hR x, Formula.restricts_rename hinj φ R R' hR x]

omit hinj in
private theorem forall_mem_map {l : List VarName} {P Q : VarName → Prop}
    (h : ∀ z, P (ρ z) ↔ Q z) : (∀ y ∈ l.map ρ, P y) ↔ ∀ y ∈ l, Q y := by
  simp only [List.forall_mem_map]
  exact forall_congr' fun y => imp_congr_right fun _ => h y

-- The members of a mutual block reach a section hypothesis only through each other's calls,
-- which the unused-variable linter does not see.
set_option linter.unusedSectionVars false in
mutual

/-- **Safety is invariant under an injective renaming**, with the restricted-outside variables
renamed alike. -/
theorem Formula.safe_rename : (φ : Formula) → ∀ (R R' : VarName → Prop),
    (∀ z, R' (ρ z) ↔ R z) → ((φ.rename ρ).Safe R' ↔ φ.Safe R)
  | .and φ ψ, R, R', hR => by
    have h := Formula.restricts_rename hinj (.and φ ψ) R R' hR
    simp only [Formula.rename] at h
    simp only [Formula.rename, Formula.Safe]
    rw [Formula.safe_rename φ _ _ h, Formula.safe_rename ψ _ _ h]
  | .not φ, R, R', hR => by
    simp only [Formula.rename, Formula.Safe, Formula.fv_rename hinj]
    rw [forall_mem_map hR, Formula.safe_rename φ R R' hR]
  | .formerly _ φ, R, R', hR => by
    simp only [Formula.rename, Formula.Safe]
    exact Formula.safe_rename φ R R' hR
  | .previous _ φ, R, R', hR => by
    simp only [Formula.rename, Formula.Safe]
    exact Formula.safe_rename φ R R' hR
  | .since φ _ ψ, R, R', hR => by
    simp only [Formula.rename, Formula.Safe, Formula.fv_rename hinj]
    rw [Formula.safe_rename ψ R R' hR, forall_mem_map (restricted_rename hinj hR),
      Formula.safe_rename φ _ _ (restricted_rename hinj hR)]
  | .pred _ _ _, _, _, _ => by simp only [Formula.rename, Formula.Safe]
  | .tp _, _, _, _ => by simp only [Formula.rename, Formula.Safe]
  | .cmp op l r, R, R', hR => by
    have h := restricted_rename hinj (φ := .cmp op l r) hR
    simp only [Formula.rename] at h
    simp only [Formula.rename, Formula.Safe, Term.fv_rename hinj, ← List.map_append]
    rw [forall_mem_map h, Term.safe_rename l R R' hR, Term.safe_rename r R R' hR]
  | .exist x φ, R, R', hR => by
    have hR' : ∀ z, ((fun u => u ≠ ρ x.name ∧ R' u) (ρ z) ↔ (fun u => u ≠ x.name ∧ R u) z) :=
      fun z => by
        simp only
        exact and_congr ⟨fun h h' => h (h' ▸ rfl), fun h h' => h (hinj h')⟩ (hR z)
    simp only [Formula.rename, Formula.Safe, Binder.rename]
    rw [Formula.restricts_rename hinj φ _ _ hR' x.name, Formula.safe_rename φ _ _ hR']

theorem Term.safe_rename : (t : Term) → ∀ (R R' : VarName → Prop),
    (∀ z, R' (ρ z) ↔ R z) → ((t.rename ρ).Safe R' ↔ t.Safe R)
  | .agg a, R, R', hR => by
    simp only [Term.rename, Term.Safe]
    exact Aggregate.safe_rename a R R' hR
  | .arith _ l r, R, R', hR => by
    simp only [Term.rename, Term.Safe]
    rw [Term.safe_rename l R R' hR, Term.safe_rename r R R' hR]
  | .var _, _, _, _ | .entity _, _, _, _ | .long _, _, _, _ | .decimal _, _, _, _
  | .string _, _, _, _ | .bool _, _, _, _ | .context _, _, _, _ | .scope _ _, _, _, _
  | .wildcard, _, _, _ => by simp only [Term.rename, Term.Safe]

theorem Aggregate.safe_rename : (a : Aggregate) → ∀ (R R' : VarName → Prop),
    (∀ z, R' (ρ z) ↔ R z) → ((a.rename ρ).Safe R' ↔ a.Safe R)
  | .count dom body, R, R', hR | .sum _ dom body, R, R', hR => by
    have hnames : (dom.map (Binder.rename ρ)).map (·.name) = (dom.map (·.name)).map ρ := by
      simp only [List.map_map]
      rfl
    have hR' : ∀ z, ((fun u => u ∉ (dom.map (Binder.rename ρ)).map (·.name) ∧ R' u) (ρ z) ↔
        (fun u => u ∉ dom.map (·.name) ∧ R u) z) := fun z => by
      simp only [hnames, List.mem_map]
      exact and_congr (not_congr ⟨fun ⟨u, hu, he⟩ => hinj he ▸ hu, fun h => ⟨z, h, rfl⟩⟩)
        (hR z)
    simp only [Aggregate.rename, Aggregate.Safe, List.forall_mem_map, Binder.rename]
    rw [Formula.safe_rename body _ _ hR']
    exact and_congr_left fun _ => forall_congr' fun b => imp_congr_right fun _ =>
      Formula.restricts_rename hinj body _ _ hR' b.name

end

/-- **A leaf's safety is invariant under an injective renaming.** -/
theorem Formula.isSafe_rename {φ : Formula} : (φ.rename ρ).IsSafe ↔ φ.IsSafe :=
  Formula.safe_rename hinj φ _ _ fun _ => Iff.rfl

end

end Dogwood.Spec.Temporal

namespace Dogwood.Spec.Temporal

/-- Bindings with their names renamed by `ρ`. -/
def Bindings.rename (ρ : VarName → VarName) (Γ : Bindings) : Bindings :=
  Γ.map fun b => (ρ b.1, b.2)

section

variable {ρ : VarName → VarName} (hinj : Function.Injective ρ)
  (hres : ∀ x, reservedBinderNames.contains (ρ x) = reservedBinderNames.contains x)

include hinj

private theorem lookup_rename : (Γ : Bindings) → (x : VarName) →
    (Γ.rename ρ).lookup (ρ x) = Γ.lookup x
  | [], _ => rfl
  | b :: Γ, x => by
    have ih := lookup_rename Γ x
    simp only [Bindings.rename, Bindings.lookup] at ih ⊢
    rw [List.map_cons, List.find?_cons, List.find?_cons]
    by_cases h : b.1 = x
    · subst h
      simp
    · have h₁ : (ρ b.1 == ρ x) = false := by
        simp only [beq_eq_false_iff_ne]
        exact fun h' => h (hinj h')
      have h₂ : (b.1 == x) = false := by simp [h]
      simp only [h₁, h₂]
      exact ih

include hres

omit hinj in
private theorem binder_sort?_rename (ets : Cedar.Validation.EntitySchema) (x : Binder) :
    (x.rename ρ).sort? ets = (x.sort? ets).map fun p => (ρ p.1, p.2) := by
  unfold Binder.sort? Binder.rename
  dsimp only
  rw [hres x.name]
  split
  · rfl
  · rw [Option.map_map]
    rfl

omit hinj in
private theorem mapM_sort?_rename (ets : Cedar.Validation.EntitySchema) : (dom : List Binder) →
    (dom.map (Binder.rename ρ)).mapM (Binder.sort? ets) =
      (dom.mapM (Binder.sort? ets)).map (Bindings.rename ρ)
  | [] => rfl
  | b :: dom => by
    simp only [List.map_cons, List.mapM_cons, binder_sort?_rename hres,
      mapM_sort?_rename ets dom]
    cases b.sort? ets with
    | none => rfl
    | some p =>
      cases dom.mapM (Binder.sort? ets) with
      | none => rfl
      | some Δ => rfl

private theorem domainSorts?_rename (ets : Cedar.Validation.EntitySchema) (dom : List Binder) :
    domainSorts? ets (dom.map (Binder.rename ρ)) =
      (domainSorts? ets dom).map (Bindings.rename ρ) := by
  have hnames : (dom.map (Binder.rename ρ)).map (·.name) = (dom.map (·.name)).map ρ := by
    simp only [List.map_map]
    rfl
  have hnd : ((dom.map (·.name)).map ρ).Nodup ↔ (dom.map (·.name)).Nodup := by
    unfold List.Nodup
    rw [List.pairwise_map]
    exact ⟨fun h => h.imp fun h' e => h' (congrArg ρ e), fun h => h.imp fun h' e => h' (hinj e)⟩
  unfold domainSorts?
  rw [hnames]
  by_cases h : (dom.map (·.name)).Nodup
  · simp only [hnd, h, ↓reduceIte, mapM_sort?_rename hres]
  · simp only [hnd, h, ↓reduceIte]
    rfl

omit hinj hres in
private theorem eqCompatible_rename {l r : Term} {τ₁ τ₂ : TType} (h : EqCompatible l r τ₁ τ₂) :
    EqCompatible (l.rename ρ) (r.rename ρ) τ₁ τ₂ := by
  unfold EqCompatible at *
  rw [eqRestricted?_rename]
  rcases h with h | ⟨hn, he⟩
  · exact .inl h
  · exact .inr ⟨by rw [hn]; rfl, he⟩

omit hinj hres in
private theorem simple_rename {t : Term} (h : t.Simple) : (t.rename ρ).Simple := by
  cases t <;> simp_all [Term.Simple, Term.rename]

omit hinj hres in
private theorem rename_ne_wildcard {t : Term} (h : t ≠ .wildcard) : t.rename ρ ≠ .wildcard := by
  cases t <;> simp_all [Term.rename]

omit hinj hres in
private theorem bindings_rename_append (Δ Γ : Bindings) :
    (Δ ++ Γ).rename ρ = Δ.rename ρ ++ Γ.rename ρ := List.map_append

variable {C : TypingCtx}

-- The members of a mutual block reach a section hypothesis only through each other's calls,
-- which the unused-variable linter does not see.
set_option linter.unusedSectionVars false in
mutual

/-- **Typing survives renaming variables**, with the bindings renamed alike, for an injective
renaming that keeps reserved binder names reserved and others not. -/
theorem Term.Typed.rename {Γ : Bindings} {t : Term} {τ : TType} :
    Term.Typed C Γ t τ → Term.Typed C (Γ.rename ρ) (t.rename ρ) τ
  | .entity h => .entity h
  | .long => .long
  | .decimal h => .decimal h
  | .string => .string
  | .bool => .bool
  | .context h hs => .context h hs
  | .scopeRoot => .scopeRoot
  | .scopeAttr h₁ h₂ hs => .scopeAttr h₁ h₂ hs
  | .var (x := x) h => .var (by rw [lookup_rename hinj]; exact h)
  | .agg h => .agg (Aggregate.Typed.rename h)
  | .arith hl hr => .arith (Term.Typed.rename hl) (Term.Typed.rename hr)

theorem Aggregate.Typed.rename {Γ : Bindings} {a : Aggregate} :
    Aggregate.Typed C Γ a → Aggregate.Typed C (Γ.rename ρ) (a.rename ρ)
  | .count (Δ := Δ) hd hb =>
    .count (Δ := Δ.rename ρ) (by rw [domainSorts?_rename hinj hres, hd]; rfl)
      (by rw [← bindings_rename_append]; exact Formula.WellTyped.rename hb)
  | .sum (Δ := Δ) hd hs hb =>
    .sum (Δ := Δ.rename ρ) (by rw [domainSorts?_rename hinj hres, hd]; rfl)
      (List.mem_map_of_mem (f := fun b => (ρ b.1, b.2)) hs)
      (by rw [← bindings_rename_append]; exact Formula.WellTyped.rename hb)

theorem Formula.WellTyped.rename {Γ : Bindings} {φ : Formula} :
    Formula.WellTyped C Γ φ → Formula.WellTyped C (Γ.rename ρ) (φ.rename ρ)
  | .and h₁ h₂ => .and (Formula.WellTyped.rename h₁) (Formula.WellTyped.rename h₂)
  | .not h => .not (Formula.WellTyped.rename h)
  | .formerly hw h => .formerly hw (Formula.WellTyped.rename h)
  | .previous hw h => .previous hw (Formula.WellTyped.rename h)
  | .since hw h₁ h₂ => .since hw (Formula.WellTyped.rename h₁) (Formula.WellTyped.rename h₂)
  | .pred (args := args) hsig hargs hpins => .pred hsig (fun arg harg => by
      rw [Formula.argsRename_eq] at harg
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp harg
      exact Formula.ArgTyped.rename (hargs a ha)) hpins
  | .eq hop hl hr hc => .eq hop (Term.Typed.rename hl) (Term.Typed.rename hr)
      (eqCompatible_rename hc)
  | .ord hop hl hr => .ord hop (Term.Typed.rename hl) (Term.Typed.rename hr)
  | .exist (x := x) (b := b) hs h => .exist (b := (ρ b.1, b.2))
      (by rw [binder_sort?_rename hres, hs]; rfl) (Formula.WellTyped.rename h)
  | .tp (x := x) h => .tp (by rw [lookup_rename hinj]; exact h)

theorem Formula.ArgTyped.rename {Γ : Bindings} {sig : EventSignature} {a : Path × Term} :
    Formula.ArgTyped C Γ sig a → Formula.ArgTyped C (Γ.rename ρ) sig (a.1, a.2.rename ρ)
  | .wildcard hf => .wildcard hf
  | .var (x := x) hf hl hw => .var hf (by rw [lookup_rename hinj]; exact hl) hw
  | .term (t := t) hf hs hv hw ht ha => .term hf (simple_rename hs)
      (fun x hx => by
        obtain ⟨z, hz, _⟩ := rename_eq_var.mp hx
        exact hv z hz)
      (rename_ne_wildcard hw) (Term.Typed.rename ht) ha

end

end

end Dogwood.Spec.Temporal

/-! ## Renamings compose, and leaf validity under the invariances -/

namespace Dogwood.Spec.Temporal

open Dogwood.Thm

private theorem binder_rename_id (b : Binder) : b.rename id = b := by
  cases b
  rfl

mutual

theorem Term.rename_rename (ρ τ : VarName → VarName) :
    (t : Term) → (t.rename ρ).rename τ = t.rename (τ ∘ ρ)
  | .var _ => rfl
  | .agg a => by simp only [Term.rename, Aggregate.rename_rename ρ τ a]
  | .arith _ l r => by
    simp only [Term.rename, Term.rename_rename ρ τ l, Term.rename_rename ρ τ r]
  | .entity _ | .long _ | .decimal _ | .string _ | .bool _ | .context _ | .scope _ _
  | .wildcard => rfl

theorem Aggregate.rename_rename (ρ τ : VarName → VarName) :
    (a : Aggregate) → (a.rename ρ).rename τ = a.rename (τ ∘ ρ)
  | .count dom body => by
    simp only [Aggregate.rename, Formula.rename_rename ρ τ body, List.map_map]
    rfl
  | .sum s dom body => by
    simp only [Aggregate.rename, Formula.rename_rename ρ τ body, List.map_map]
    rfl

/-- **Renamings compose.** -/
theorem Formula.rename_rename (ρ τ : VarName → VarName) :
    (φ : Formula) → (φ.rename ρ).rename τ = φ.rename (τ ∘ ρ)
  | .and φ ψ | .since φ _ ψ => by
    simp only [Formula.rename, Formula.rename_rename ρ τ φ, Formula.rename_rename ρ τ ψ]
  | .not φ | .formerly _ φ | .previous _ φ => by
    simp only [Formula.rename, Formula.rename_rename ρ τ φ]
  | .exist x φ => by
    simp only [Formula.rename, Formula.rename_rename ρ τ φ]
    rfl
  | .tp _ => rfl
  | .cmp _ l r => by
    simp only [Formula.rename, Term.rename_rename ρ τ l, Term.rename_rename ρ τ r]
  | .pred _ _ args => by simp only [Formula.rename, Formula.argsRename_rename ρ τ args]

theorem Formula.argsRename_rename (ρ τ : VarName → VarName) : (args : List (Path × Term)) →
    Formula.argsRename τ (Formula.argsRename ρ args) = Formula.argsRename (τ ∘ ρ) args
  | [] => rfl
  | (_, t) :: args => by
    simp only [Formula.argsRename, Term.rename_rename ρ τ t, Formula.argsRename_rename ρ τ args]

end

mutual

theorem Term.rename_id : (t : Term) → t.rename id = t
  | .var _ => rfl
  | .agg a => by simp only [Term.rename, Aggregate.rename_id a]
  | .arith _ l r => by simp only [Term.rename, Term.rename_id l, Term.rename_id r]
  | .entity _ | .long _ | .decimal _ | .string _ | .bool _ | .context _ | .scope _ _
  | .wildcard => rfl

theorem Aggregate.rename_id : (a : Aggregate) → a.rename id = a
  | .count dom body => by
    have hd : dom.map (Binder.rename id) = dom :=
      (List.map_congr_left fun b _ => binder_rename_id b).trans (List.map_id dom)
    simp only [Aggregate.rename, Formula.rename_id body, hd]
  | .sum s dom body => by
    have hd : dom.map (Binder.rename id) = dom :=
      (List.map_congr_left fun b _ => binder_rename_id b).trans (List.map_id dom)
    simp only [Aggregate.rename, Formula.rename_id body, hd, id]

/-- **Renaming by the identity changes nothing.** -/
theorem Formula.rename_id : (φ : Formula) → φ.rename id = φ
  | .and φ ψ | .since φ _ ψ => by
    simp only [Formula.rename, Formula.rename_id φ, Formula.rename_id ψ]
  | .not φ | .formerly _ φ | .previous _ φ => by simp only [Formula.rename, Formula.rename_id φ]
  | .exist x φ => by simp only [Formula.rename, Formula.rename_id φ, binder_rename_id]
  | .tp _ => rfl
  | .cmp _ l r => by simp only [Formula.rename, Term.rename_id l, Term.rename_id r]
  | .pred _ _ args => by simp only [Formula.rename, Formula.argsRename_id args]

theorem Formula.argsRename_id : (args : List (Path × Term)) → Formula.argsRename id args = args
  | [] => rfl
  | (_, t) :: args => by
    simp only [Formula.argsRename, Term.rename_id t, Formula.argsRename_id args]

end

theorem Bindings.rename_rename (ρ τ : VarName → VarName) (Γ : Bindings) :
    (Γ.rename ρ).rename τ = Γ.rename (τ ∘ ρ) := by
  simp only [Bindings.rename, List.map_map]
  rfl

theorem Bindings.rename_id (Γ : Bindings) : Γ.rename id = Γ := by
  simp only [Bindings.rename, id]
  exact List.map_id' Γ |>.trans rfl

section

variable {ρ : VarName → VarName} (hinj : Function.Injective ρ)

include hinj

private theorem mem_map_inj {E : List VarName} {x : VarName} : ρ x ∈ E.map ρ ↔ x ∈ E := by
  rw [List.mem_map]
  exact ⟨fun ⟨z, hz, he⟩ => hinj he ▸ hz, fun h => ⟨x, h, rfl⟩⟩

private theorem term_varies_rename (E : List VarName) :
    (t : Term) → ((t.rename ρ).Varies (E.map ρ) ↔ t.Varies E)
  | .var x => by simp only [Term.rename, Term.Varies]; exact mem_map_inj hinj
  | .agg _ => Iff.rfl
  | .arith _ l r => by
    simp only [Term.rename, Term.Varies, term_varies_rename E l, term_varies_rename E r]
  | .entity _ | .long _ | .decimal _ | .string _ | .bool _ | .context _ | .scope _ _
  | .wildcard => Iff.rfl

private theorem formula_varies_rename (E : List VarName) :
    (φ : Formula) → ((φ.rename ρ).Varies (E.map ρ) ↔ φ.Varies E)
  | .cmp _ l r => by
    simp only [Formula.rename, Formula.Varies, term_varies_rename hinj E l,
      term_varies_rename hinj E r]
  | .not φ => by simp only [Formula.rename, Formula.Varies, formula_varies_rename E φ]
  | .and φ ψ => by
    simp only [Formula.rename, Formula.Varies, formula_varies_rename E φ, formula_varies_rename E ψ]
  | .pred _ _ _ | .tp _ | .formerly _ _ | .previous _ _ | .since _ _ _ | .exist _ _ => Iff.rfl

-- The members of a mutual block reach a section hypothesis only through each other's calls,
-- which the unused-variable linter does not see.
set_option linter.unusedSectionVars false in
mutual

private theorem formula_scopesVary_rename : (E : List VarName) →
    (φ : Formula) → ((φ.rename ρ).ScopesVary (E.map ρ) ↔ φ.ScopesVary E)
  | E, .cmp _ l r => by
    simp only [Formula.rename, Formula.ScopesVary, term_scopesVary_rename E l,
      term_scopesVary_rename E r]
  | E, .not φ => by simp only [Formula.rename, Formula.ScopesVary, formula_scopesVary_rename E φ]
  | E, .and φ ψ => by
    simp only [Formula.rename, Formula.ScopesVary, formula_scopesVary_rename E φ,
      formula_scopesVary_rename E ψ]
  | E, .formerly _ φ => by
    simp only [Formula.rename, Formula.ScopesVary, formula_scopesVary_rename E φ,
      formula_varies_rename hinj E φ]
  | E, .previous _ φ => by
    simp only [Formula.rename, Formula.ScopesVary, formula_scopesVary_rename E φ,
      formula_varies_rename hinj E φ]
  | E, .since φ _ ψ => by
    simp only [Formula.rename, Formula.ScopesVary, formula_scopesVary_rename E φ,
      formula_varies_rename hinj E φ, formula_scopesVary_rename E ψ, formula_varies_rename hinj E ψ]
  | E, .exist x φ => by
    have h := formula_scopesVary_rename (x.name :: E) φ
    have h' := formula_varies_rename hinj (x.name :: E) φ
    simp only [List.map_cons] at h h'
    simp only [Formula.rename, Formula.ScopesVary, Binder.rename, h, h']
  | _, .pred _ _ _ | _, .tp _ => Iff.rfl

private theorem term_scopesVary_rename : (E : List VarName) →
    (t : Term) → ((t.rename ρ).ScopesVary (E.map ρ) ↔ t.ScopesVary E)
  | E, .agg (.count _ body) => by
    simp only [Term.rename, Aggregate.rename, Term.ScopesVary, formula_scopesVary_rename E body,
      formula_varies_rename hinj E body]
  | E, .agg (.sum s _ body) => by
    have h := formula_scopesVary_rename (s :: E) body
    have h' := formula_varies_rename hinj (s :: E) body
    simp only [List.map_cons] at h h'
    simp only [Term.rename, Aggregate.rename, Term.ScopesVary, h, h']
  | E, .arith _ l r => by
    simp only [Term.rename, Term.ScopesVary, term_scopesVary_rename E l, term_scopesVary_rename E r]
  | _, .var _ | _, .entity _ | _, .long _ | _, .decimal _ | _, .string _ | _, .bool _
  | _, .context _ | _, .scope _ _ | _, .wildcard => Iff.rfl

end

omit hinj in
private theorem argsBinders_rename : (args : List (Path × Term)) →
    (Formula.argsRename ρ args).filterMap (fun
      | (_, .var x) => some x
      | _ => none) =
    (args.filterMap (fun
      | (_, .var x) => some x
      | _ => none)).map ρ
  | [] => rfl
  | (_, t) :: args => by
    cases t <;> simp [Formula.argsRename, Term.rename, argsBinders_rename args]

omit hinj in
private theorem ruleWideBinders_rename :
    (φ : Formula) → (φ.rename ρ).ruleWideBinders = φ.ruleWideBinders.map ρ
  | .and φ ψ | .since φ _ ψ => by
    simp only [Formula.rename, Formula.ruleWideBinders, ruleWideBinders_rename φ,
      ruleWideBinders_rename ψ, List.map_append]
  | .formerly _ φ | .previous _ φ | .exist _ φ => by
    simp only [Formula.rename, Formula.ruleWideBinders, ruleWideBinders_rename φ]
  | .pred _ _ args => by
    simp only [Formula.rename, Formula.ruleWideBinders]
    exact argsBinders_rename args
  | .not _ | .cmp _ _ _ | .tp _ => rfl

omit hinj in
private theorem conjuncts_rename :
    (φ : Formula) → (φ.rename ρ).conjuncts = φ.conjuncts.map (·.rename ρ)
  | .and φ ψ => by
    simp only [Formula.rename, Formula.conjuncts, conjuncts_rename φ, conjuncts_rename ψ,
      List.map_append]
  | .not _ | .formerly _ _ | .previous _ _ | .since _ _ _ | .pred _ _ _ | .cmp _ _ _
  | .exist _ _ | .tp _ => rfl

/-- **The time-dependence check is invariant under an injective renaming.** -/
theorem Formula.monitorsTime_rename {φ : Formula} : (φ.rename ρ).MonitorsTime ↔ φ.MonitorsTime := by
  simp only [Formula.MonitorsTime, conjuncts_rename, ruleWideBinders_rename, List.forall_mem_map]
  exact forall_congr' fun c => imp_congr_right fun _ =>
    and_congr (formula_varies_rename hinj _ c) (formula_scopesVary_rename hinj _ c)

end

end Dogwood.Spec.Temporal

namespace Dogwood.Thm

open Dogwood.Spec Dogwood.Spec.Temporal

theorem swapVar_swapVar (x y z : VarName) : swapVar x y (swapVar x y z) = z := by
  unfold swapVar
  by_cases h₁ : z = x <;> by_cases h₂ : z = y <;> simp_all

/-- Swapping two names that are not reserved keeps every name reserved or not. -/
theorem swapVar_reserved {x y : VarName} (hx : reservedBinderNames.contains x = false)
    (hy : reservedBinderNames.contains y = false) (z : VarName) :
    reservedBinderNames.contains (swapVar x y z) = reservedBinderNames.contains z := by
  unfold swapVar
  by_cases h₁ : z = x
  · subst h₁
    simp only [↓reduceIte]
    rw [hx, hy]
  · by_cases h₂ : z = y
    · subst h₂
      simp only [h₁, ↓reduceIte]
      rw [hx, hy]
    · simp [h₁, h₂]

/-- **Typing is invariant under swapping two names that are not reserved**, with the bindings
swapped alike. -/
theorem wellTyped_swap_iff {C : TypingCtx} {Γ : Bindings} {φ : Formula} {x y : VarName}
    (hx : reservedBinderNames.contains x = false) (hy : reservedBinderNames.contains y = false) :
    Formula.WellTyped C (Γ.rename (swapVar x y)) (φ.rename (swapVar x y)) ↔
      Formula.WellTyped C Γ φ := by
  have hsw : swapVar x y ∘ swapVar x y = id := funext (swapVar_swapVar x y)
  constructor
  · intro h
    have := Formula.WellTyped.rename swapVar_injective (swapVar_reserved hx hy) h
    rwa [Bindings.rename_rename, Formula.rename_rename, hsw, Bindings.rename_id,
      Formula.rename_id] at this
  · exact Formula.WellTyped.rename swapVar_injective (swapVar_reserved hx hy)

/-- **A leaf's validity does not depend on the order of its conjuncts.** -/
theorem leafValid_and_comm {P : PolicySet} {p : Policy} {F : List Guard} {φ ψ : Formula} :
    P.LeafValid p F (.and φ ψ) ↔ P.LeafValid p F (.and ψ φ) := by
  constructor <;> rintro ⟨hw, hs, hm⟩ <;>
    exact ⟨fun env henv => Formula.wellTyped_and_comm.mp (hw env henv),
      Formula.safe_and_comm.mp hs, Formula.monitorsTime_and_comm.mp hm⟩

/-- **A leaf's validity is invariant under swapping two names that are not reserved**,
throughout the leaf: alpha-renaming a leaf keeps it valid, and an invalid leaf invalid. -/
theorem leafValid_swap_iff {P : PolicySet} {p : Policy} {F : List Guard} {φ : Formula}
    {x y : VarName} (hx : reservedBinderNames.contains x = false)
    (hy : reservedBinderNames.contains y = false) :
    P.LeafValid p F (φ.rename (swapVar x y)) ↔ P.LeafValid p F φ := by
  have hw : ∀ env, (φ.rename (swapVar x y)).WellTyped (P.typingCtx env F) [] ↔
      φ.WellTyped (P.typingCtx env F) [] := fun env =>
    wellTyped_swap_iff (Γ := []) hx hy
  constructor <;> rintro ⟨h₁, h₂, h₃⟩
  · exact ⟨fun env henv => (hw env).mp (h₁ env henv),
      (Formula.isSafe_rename swapVar_injective).mp h₂,
      (Formula.monitorsTime_rename swapVar_injective).mp h₃⟩
  · exact ⟨fun env henv => (hw env).mpr (h₁ env henv),
      (Formula.isSafe_rename swapVar_injective).mpr h₂,
      (Formula.monitorsTime_rename swapVar_injective).mpr h₃⟩

/-- `leafHolds_rename` under partitioned evaluation. -/
theorem partLeafHolds_rename {ι : ImplChoices} {P : PolicySet} {ρ' : Trace} {n : Nat}
    {ρ : VarName → VarName} (hρ : Function.Injective ρ) {φ : Formula} :
    P.PartLeafHolds ι ρ' n (φ.rename ρ) ↔ P.PartLeafHolds ι ρ' n φ := by
  unfold PolicySet.PartLeafHolds
  refine exists_congr fun p => and_congr_right fun _ => ?_
  rw [← Formula.rename_injectPins]
  exact sat_rename hρ _ _ _ _ fun _ _ => rfl

/-- `leafHolds_rename` for a rule that observes the trace from a timepoint of its own. -/
theorem leafHoldsFrom_rename {ι : ImplChoices} {P : PolicySet} {σ : Trace} {s n : Nat}
    {ρ : VarName → VarName} (hρ : Function.Injective ρ) {φ : Formula} :
    P.LeafHoldsFrom ι σ s n (φ.rename ρ) ↔ P.LeafHoldsFrom ι σ s n φ := by
  unfold PolicySet.LeafHoldsFrom
  refine exists_congr fun p => and_congr_right fun _ => ?_
  rw [← Formula.rename_injectPins]
  exact sat_rename hρ _ _ _ _ fun _ _ => rfl

end Dogwood.Thm
