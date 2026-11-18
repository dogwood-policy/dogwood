import Dogwood.Examples.ConcurrencyCap

/-!
# Worked example: a balance, computed over 128-bit integers

A balance check: a withdrawal is allowed while the caller's deposits in the window cover the
caller's withdrawals in it, the one being decided included.

```text
permit (principal, action == Drupe::Action::"Withdraw", resource)
when temporal {
    (sum a for (a: Long), (t: Timepoint). where (
        formerly within W (Drupe::Action::"Deposit"::response{ input.amount: a } && tp(t))))
    - (sum a for (a: Long), (t: Timepoint). where (
        formerly within W (Drupe::Action::"Withdraw"::request{ input.amount: a } && tp(t)))) >= 0
};
```

under the default (pinned) event schema. A sum of `Long`s can leave the `Long` range, so how an
out-of-range result is read matters: two sums each read as `Int64.MAX` subtract to `0`, whatever
they were. An implementation that computes over 128-bit integers computes every result exactly
while it does not overflow; `ExactBelow ι (2 ^ 127)` states that of the reading, here and not in
the semantics.

* **What an allow means** (`allowed_withdraw_balance`): at an allowed withdrawal, the caller's
  deposits in the window, minus the caller's withdrawals in it, counted exactly (`windowSum`),
  are not negative, on every trace of fewer than `2 ^ 63` events, under every reading exact below
  `2 ^ 127` (no admissibility needed). Each sum then has magnitude below `2 ^ 126`, and their
  difference below `2 ^ 127`.
* **Under clamping** (`allowed_withdraw_balance_of_inLong`): the same, under every admissible
  reading, when each window sum is within the `Long` range. This covers the reference
  interpreter, which clamps aggregate totals and saturates arithmetic.
* **Under exact aggregates and clamped arithmetic** (`allowed_withdraw_balance_mixed`): the same,
  on every trace of fewer than `2 ^ 63` events, with no hypothesis on the amounts: only the sums
  need to be exact, since the difference's sign survives clamping. This is a change to the
  reference interpreter's reading that makes the example hold without a hypothesis on the
  amounts.
* Denied withdrawals count too: the check is on requests, so a denied request lowers the window's
  balance.
-/

namespace Dogwood.Examples.Balance

open Dogwood.Spec Dogwood.Spec.Temporal Dogwood.Thm Dogwood.Examples
open Dogwood.Examples.RateLimit (leafHolds_of_allow)
open Dogwood.Examples.ConcurrencyCap (readLong_of_range)
open Cedar.Spec (EntityUID Value)

/-! ## Readings exact below a bound -/

/-- The reading computes exactly every result below `bound` in magnitude, as arithmetic over
128-bit integers does while it does not overflow (`bound = 2 ^ 127`). -/
structure ExactBelow (ι : ImplChoices) (bound : Int) : Prop where
  aggregate : ∀ n, -bound ≤ n → n < bound → ι.outOfRange n = some n
  arith : ∀ n, -bound ≤ n → n < bound → ι.arithOutOfRange n = some n

/-- A completion of a reading exact below a bound is exact below it. -/
theorem ExactBelow.completes {ι ι' : ImplChoices} {bound : Int} (h : ExactBelow ι bound)
    (hc : ι'.Completes ι) : ExactBelow ι' bound :=
  ⟨fun n h₁ h₂ => hc.aggregate.agrees n n (h.aggregate n h₁ h₂),
    fun n h₁ h₂ => hc.arith.agrees n n (h.arith n h₁ h₂)⟩

theorem readLong_exact {f : Int → Option Int} {bound n : Int}
    (hf : ∀ n, -bound ≤ n → n < bound → f n = some n) (h₁ : -bound ≤ n) (h₂ : n < bound) :
    readLong f n = some (.num n) := by
  unfold readLong
  split
  · rfl
  · rw [hf n h₁ h₂]; rfl

/-! ## The policy -/

def deposit : EntityUID := action "Deposit"
def withdraw : EntityUID := action "Withdraw"

def actions : List ActionDecl := [(deposit, [("amount", .int)]), (withdraw, [("amount", .int)])]

def schema : EventSchema := defaultSchema true actions

def domain : List Binder := [⟨"a", .named ["Long"]⟩, ⟨"t", .timepoint⟩]

def sumOf (w : Window) (a : EntityUID) (kind : String) : Aggregate :=
  .sum "a" domain (.formerly w (.and (.pred a kind [(["input", "amount"], .var "a")]) (.tp "t")))

def balance (w : Window) : Formula :=
  .cmp .ge (.arith .sub (.agg (sumOf w deposit "response")) (.agg (sumOf w withdraw "request")))
    (.long 0)

def policySet (w : Window) : PolicySet := onePolicy withdraw (balance w) schema actions

theorem policySet_valid : (policySet ⟨24, .hours⟩).Valid :=
  onePolicy_valid (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem universalPins_schema : schema.universalPins = [callerPin] := by decide

/-- A predicate on the amount, after injection of the caller pin. -/
def amountPred (a : EntityUID) (kind : String) : Formula :=
  .pred a kind [(["input", "amount"], .var "a"), (["callerPrincipal"], .scope .principal [])]

def pinnedSum (w : Window) (a : EntityUID) (kind : String) : Aggregate :=
  .sum "a" domain (.formerly w (.and (amountPred a kind) (.tp "t")))

theorem balance_injected (w : Window) :
    (balance w).injectPins schema =
      .cmp .ge (.arith .sub (.agg (pinnedSum w deposit "response"))
        (.agg (pinnedSum w withdraw "request"))) (.long 0) := by
  have h₁ : schema.pinsOf deposit "response" = [callerPin] := by decide
  have h₂ : schema.pinsOf withdraw "request" = [callerPin] := by decide
  simp [balance, sumOf, pinnedSum, amountPred, Formula.injectPins, Term.injectPins,
    Aggregate.injectPins, h₁, h₂, callerPin, PinRef.toTerm]

/-! ## Exact window sums -/

open Dogwood.Examples.ConcurrencyCap (inWindowB inWindowB_iff)

/-- The amount an event logs. -/
def amountOf (p : TimePoint) : Option Value := recordPath? p.event.logged ["input", "amount"]

/-- A logged amount, as an integer: `0` unless it is a `Long`. -/
def amtInt : Option Value → Int
  | some (.prim (.int i)) => i.toInt
  | _ => 0

/-- Whether the event at `k` is `u`'s, of action `a` and kind `kind`, within `w` before `j`, and
logs an amount. -/
def matchB (σ : Trace) (u a : EntityUID) (kind : String) (w : Window) (j k : Nat) : Bool :=
  inWindowB σ u a kind w j k && (σ[k]?.bind amountOf).isSome

/-- The sum of the amounts of `u`'s events of action `a` and kind `kind` within `w` before `j`. -/
def windowSum (σ : Trace) (u a : EntityUID) (kind : String) (w : Window) (j : Nat) : Int :=
  (((List.range (j + 1)).filter (matchB σ u a kind w j)).map
    fun k => amtInt (σ[k]?.bind amountOf)).sum

/-- The row of the event at `k`: its amount and its timepoint. -/
def rowAt (σ : Trace) (k : Nat) : List TVal :=
  [.val ((σ[k]?.bind amountOf).getD default), tpValue k]

theorem bindAll_a (ra rt : TVal) : (Valuation.empty.bindAll ["a", "t"] [ra, rt]) "a" = some ra := by
  simp [Valuation.bindAll, Valuation.bind]

theorem bindAll_t (ra rt : TVal) : (Valuation.empty.bindAll ["a", "t"] [ra, rt]) "t" = some rt := by
  simp [Valuation.bindAll, Valuation.bind]

theorem summand_val (v : Value) (rt : TVal) :
    summand "a" ["a", "t"] [.val v, rt] = amtInt (some v) := by
  simp only [summand, List.zip, List.zipWith, List.lookup, BEq.rfl]
  cases v with
  | prim pv => cases pv <;> rfl
  | _ => rfl

theorem sat_amountPred {ι : ImplChoices} {rate : TickRate} {σ : Trace} {e : Event}
    {vis : Nat → Prop} {u : EntityUID} (he : e.principal = some u) (a : EntityUID) (kind : String)
    (v : Valuation) (k : Nat) :
    Sat ι rate σ e vis v k (amountPred a kind) ↔
      ∃ p, σ[k]? = some p ∧ ByCaller u a kind p ∧
        ∃ w, amountOf p = some w ∧ v "a" = some (.val w) := by
  simp only [Sat, amountPred, ArgsMatch, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq]
  simp only [Term.Matches, Term.eval?, Event.scopePath?, Event.scope, he, Option.map_some,
    Option.some.injEq, TVal.val.injEq, ByCaller, amountOf]
  constructor
  · rintro ⟨p, hp, ha, hk, ⟨w, hw, hv⟩, ⟨w', hw', rfl⟩⟩
    exact ⟨p, hp, ⟨ha, hk, hw'⟩, w, hw, hv⟩
  · rintro ⟨p, hp, ⟨ha, hk, hpin⟩, w, hw, hv⟩
    exact ⟨p, hp, ha, hk, ⟨w, hw, hv⟩, ⟨_, hpin, rfl⟩⟩

/-- **A pinned sum in a window is the sum of the caller's amounts in it.** -/
theorem total_sum_eq {ι : ImplChoices} {σ : Trace} {u a : EntityUID} {kind : String}
    (hsig : ∃ s ∈ schema, s.action = a ∧ s.kind = kind) {w : Window} {j : Nat} {e : Event}
    (he : e.principal = some u) :
    Total ι .seconds σ e (schema.Visible σ e) Valuation.empty j (pinnedSum w a kind)
      (windowSum σ u a kind w j) := by
  have hdom : domainNames domain = ["a", "t"] := rfl
  refine ⟨((List.range (j + 1)).filter (matchB σ u a kind w j)).map (rowAt σ), ?_,
    fun row => ?_, ?_⟩
  · rw [List.Nodup, List.pairwise_map]
    refine (List.nodup_range.sublist List.filter_sublist).imp fun hne heq => hne ?_
    simp only [rowAt, tpValue, List.cons.injEq, TVal.tp.injEq] at heq
    exact heq.2.1
  · rw [hdom]
    constructor
    · intro hrow
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hrow
      obtain ⟨hkr, hb⟩ := List.mem_filter.mp hk
      simp only [matchB, Bool.and_eq_true] at hb
      obtain ⟨hwin, hsome⟩ := hb
      obtain ⟨pk, hpk, hbk, hin⟩ := inWindowB_iff.mp hwin
      rw [hpk, Option.bind_some, Option.isSome_iff_exists] at hsome
      obtain ⟨v, hv⟩ := hsome
      refine ⟨rfl, k, Nat.le_of_lt_succ (List.mem_range.mp hkr),
        visible_of_byCaller universalPins_schema hsig he hpk hbk, hin, ?_, ?_⟩
      · refine (sat_amountPred he a kind _ k).mpr ⟨pk, hpk, hbk, v, hv, ?_⟩
        rw [rowAt, hpk, Option.bind_some, hv, Option.getD_some, bindAll_a]
      · simp only [Sat, rowAt, bindAll_t]
    · rintro ⟨hl, k, hk, -, hin, hpred, ht⟩
      obtain ⟨pk, hpk, hbk, v, hv, hva⟩ := (sat_amountPred he a kind _ k).mp hpred
      match row, hl with
      | [ra, rt], _ =>
        rw [bindAll_a, Option.some.injEq] at hva
        simp only [Sat, bindAll_t, Option.some.injEq] at ht
        subst hva ht
        refine List.mem_map.mpr ⟨k, List.mem_filter.mpr ⟨List.mem_range.mpr (by omega), ?_⟩, ?_⟩
        · simp only [matchB, Bool.and_eq_true]
          exact ⟨inWindowB_iff.mpr ⟨pk, hpk, hbk, hin⟩, by rw [hpk, Option.bind_some, hv]; rfl⟩
        · rw [rowAt, hpk, Option.bind_some, hv, Option.getD_some]
  · rw [List.map_map, hdom]
    unfold windowSum
    congr 1
    refine List.map_congr_left fun k hk => ?_
    obtain ⟨-, hb⟩ := List.mem_filter.mp hk
    simp only [matchB, Bool.and_eq_true] at hb
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hb.2
    simp only [Function.comp, rowAt, hv, Option.getD_some, summand_val]

/-! ## Bounds -/

theorem amtInt_bounds (v : Option Value) : -(2 ^ 63 : Int) ≤ amtInt v ∧ amtInt v ≤ 2 ^ 63 := by
  unfold amtInt
  split
  · rename_i i
    have h₁ := Int64.le_toInt i
    have h₂ := Int64.toInt_lt i
    constructor <;> omega
  · constructor <;> decide

theorem sum_bounds (f : Nat → Int) (hf : ∀ k, -(2 ^ 63 : Int) ≤ f k ∧ f k ≤ 2 ^ 63) :
    (L : List Nat) → -(L.length * 2 ^ 63 : Int) ≤ (L.map f).sum ∧ (L.map f).sum ≤ L.length * 2 ^ 63
  | [] => by simp
  | k :: L => by
    have ih := sum_bounds f hf L
    have := hf k
    simp only [List.map_cons, List.sum_cons, List.length_cons, Int.natCast_add, Int.natCast_one,
      Int.add_mul, Int.one_mul]
    constructor <;> omega

theorem windowSum_bounds (σ : Trace) (u a : EntityUID) (kind : String) (w : Window) (j : Nat) :
    -((j + 1 : Nat) * 2 ^ 63 : Int) ≤ windowSum σ u a kind w j ∧
      windowSum σ u a kind w j ≤ (j + 1 : Nat) * 2 ^ 63 := by
  have hlen := List.length_filter_le (matchB σ u a kind w j) (List.range (j + 1))
  simp only [List.length_range] at hlen
  have hb := sum_bounds (fun k => amtInt (σ[k]?.bind amountOf)) (fun k => amtInt_bounds _)
    ((List.range (j + 1)).filter (matchB σ u a kind w j))
  unfold windowSum
  have h₀ : (0 : Int) ≤ 2 ^ 63 := by decide
  have hm := Int.mul_le_mul_of_nonneg_right (Int.ofNat_le.mpr hlen) h₀
  constructor <;> omega

/-! ## What an allow means -/

theorem sig_deposit : ∃ s ∈ schema, s.action = deposit ∧ s.kind = "response" :=
  sig_defaultSchema (ins := [("amount", .int)]) (by simp [actions]) (.inr (.inl rfl))

theorem sig_withdraw : ∃ s ∈ schema, s.action = withdraw ∧ s.kind = "request" :=
  sig_defaultSchema (ins := [("amount", .int)]) (by simp [actions]) (.inl rfl)

/-- **At an allowed withdrawal, the caller's deposits in the window cover the caller's
withdrawals in it**, counted exactly, on every trace of fewer than `2 ^ 63` events, under every
reading exact below `2 ^ 127`, as arithmetic over 128-bit integers is. -/
theorem allowed_withdraw_balance {ι : ImplChoices} (hx : ExactBelow ι (2 ^ 127))
    {ω : Provider.Providers} {σ : Trace} {w : Window} {q : Nat} {pq : TimePoint} {u : EntityUID}
    (h : ((policySet w).authorize ι ω σ q).decision? = some .allow)
    (hpq : σ[q]? = some pq) (hu : pq.event.principal = some u)
    (hlen : (σ.length : Int) < 2 ^ 63) :
    0 ≤ windowSum σ u deposit "response" w q - windowSum σ u withdraw "request" w q := by
  obtain ⟨ι₀, hc, pq', hpq', hsat⟩ := leafHolds_of_allow h
  have hx₀ := hx.completes hc
  rw [hpq] at hpq'
  cases hpq'
  change Sat ι₀ .seconds σ pq.event (schema.Visible σ pq.event) Valuation.empty q
    ((balance w).injectPins schema) at hsat
  rw [balance_injected] at hsat
  obtain ⟨x, y, ⟨m, n, ⟨t₁, ht₁, hm⟩, ⟨t₂, ht₂, hn⟩, hxv⟩, ⟨_, hy, rfl⟩, hh⟩ := hsat
  simp only [Term.eval?, Option.some.injEq] at hy
  subst hy
  have e₁ := total_unique ht₁ (total_sum_eq sig_deposit hu)
  have e₂ := total_unique ht₂ (total_sum_eq sig_withdraw hu)
  subst e₁ e₂
  -- Each sum has magnitude below `2 ^ 126`, and their difference below `2 ^ 127`.
  have hq : (q : Int) + 1 ≤ σ.length := by
    have := (List.getElem?_eq_some_iff.mp hpq).1; omega
  have hmul : ((q + 1 : Nat) : Int) * 2 ^ 63 < 2 ^ 126 := by
    have h₀ : ((q + 1 : Nat) : Int) ≤ 2 ^ 63 - 1 := by push_cast; omega
    have := Int.mul_le_mul_of_nonneg_right h₀ (by decide : (0 : Int) ≤ 2 ^ 63)
    have hc : ((2 : Int) ^ 63 - 1) * 2 ^ 63 < 2 ^ 126 := by decide
    omega
  obtain ⟨d₁, d₂⟩ := windowSum_bounds σ u deposit "response" w q
  obtain ⟨w₁, w₂⟩ := windowSum_bounds σ u withdraw "request" w q
  have h126 : (2 : Int) ^ 126 ≤ 2 ^ 127 := by decide
  simp only [ImplChoices.aggregateValue] at hm hn
  rw [readLong_exact hx₀.aggregate (by omega) (by omega), Option.some.injEq, CVal.num.injEq]
    at hm hn
  subst hm hn
  have hsum : (2 : Int) ^ 126 + 2 ^ 126 = 2 ^ 127 := by decide
  simp only [ImplChoices.arithValue, ArithOp.apply] at hxv
  rw [readLong_exact hx₀.arith (by omega) (by omega), Option.some.injEq] at hxv
  subst hxv
  simpa [CVal.ofTVal, CVal.ofValue, CmpOp.Holds] using hh

/-! ## Variants: clamping, and exact aggregates with clamped arithmetic

The guarantee needs each window sum read exactly; the difference itself only needs a reading
that keeps its side of the range (`SidePreserving`), since a difference above the range read as
at least `Int64.MAX`, or below it as at most `Int64.MIN`, keeps its sign, and `>= 0` reads only
the sign. So it holds under clamping when each sum is within the `Long` range
(`allowed_withdraw_balance_of_inLong`, which covers the reference interpreter), and under a
reading that computes aggregates exactly and clamps arithmetic
(`allowed_withdraw_balance_mixed`), on traces of fewer than `2 ^ 63` events. -/

/-- A completion of a reading whose arithmetic keeps sides keeps sides. -/
theorem sidePreserving_completes {f f' : Int → Option Int} (hf : SidePreserving f)
    (hc : ReadingCompletes f' f) : SidePreserving f' := by
  intro n m hm
  cases h : f n with
  | none => exact hc.sides n m h hm
  | some m' =>
    have := hc.agrees n m' h
    rw [this, Option.some.injEq] at hm
    subst hm
    exact hf n m' h

/-- **The core**: at a decision whose leaf holds under a reading that reads both window sums
exactly and keeps the side of an out-of-range difference, the exact balance is not negative. -/
theorem balance_of_leaf {ι₀ : ImplChoices} {σ : Trace} {w : Window} {q : Nat} {pq : TimePoint}
    {u : EntityUID} (hpq : σ[q]? = some pq) (hu : pq.event.principal = some u)
    (hleaf : (policySet w).LeafHolds ι₀ σ q (balance w))
    (h₁ : readLong ι₀.outOfRange (windowSum σ u deposit "response" w q) =
      some (.num (windowSum σ u deposit "response" w q)))
    (h₂ : readLong ι₀.outOfRange (windowSum σ u withdraw "request" w q) =
      some (.num (windowSum σ u withdraw "request" w q)))
    (harith : SidePreserving ι₀.arithOutOfRange) :
    0 ≤ windowSum σ u deposit "response" w q - windowSum σ u withdraw "request" w q := by
  obtain ⟨pq', hpq', hsat⟩ := hleaf
  rw [hpq] at hpq'
  cases hpq'
  change Sat ι₀ .seconds σ pq.event (schema.Visible σ pq.event) Valuation.empty q
    ((balance w).injectPins schema) at hsat
  rw [balance_injected] at hsat
  obtain ⟨x, y, ⟨m, n, ⟨t₁, ht₁, hm⟩, ⟨t₂, ht₂, hn⟩, hxv⟩, ⟨_, hy, rfl⟩, hh⟩ := hsat
  simp only [Term.eval?, Option.some.injEq] at hy
  subst hy
  have e₁ := total_unique ht₁ (total_sum_eq sig_deposit hu)
  have e₂ := total_unique ht₂ (total_sum_eq sig_withdraw hu)
  subst e₁ e₂
  simp only [ImplChoices.aggregateValue] at hm hn
  rw [h₁, Option.some.injEq, CVal.num.injEq] at hm
  rw [h₂, Option.some.injEq, CVal.num.injEq] at hn
  subst hm hn
  simp only [ImplChoices.arithValue, ArithOp.apply] at hxv
  generalize hd : windowSum σ u deposit "response" w q - windowSum σ u withdraw "request" w q = d
    at hxv ⊢
  unfold readLong at hxv
  split at hxv
  · simp only [Option.some.injEq] at hxv
    subst hxv
    simpa [CVal.ofTVal, CVal.ofValue, CmpOp.Holds] using hh
  · rename_i hout
    simp only [Option.map_eq_some_iff] at hxv
    obtain ⟨m', hm', rfl⟩ := hxv
    have hs := harith d m' hm'
    simp only [CVal.ofTVal, CVal.ofValue, CmpOp.Holds, Int64.toInt_zero] at hh
    have hmin : Int64.MIN < 0 := by decide
    have hmax : (0 : Int) < Int64.MAX := by decide
    by_cases hlo : d < Int64.MIN
    · have := hs.2 hlo; omega
    · omega

/-- **Under every admissible reading, clamping included, the balance is exact when each window
sum is within the `Long` range**: at an allowed withdrawal, the caller's deposits minus
withdrawals in the window are not negative. This covers the reference interpreter, which clamps
aggregate totals and saturates arithmetic. -/
theorem allowed_withdraw_balance_of_inLong {ι : ImplChoices} (hι : ι.Admissible)
    {ω : Provider.Providers} {σ : Trace} {w : Window} {q : Nat} {pq : TimePoint} {u : EntityUID}
    (h : ((policySet w).authorize ι ω σ q).decision? = some .allow)
    (hpq : σ[q]? = some pq) (hu : pq.event.principal = some u)
    (hd : InLong (windowSum σ u deposit "response" w q))
    (hw : InLong (windowSum σ u withdraw "request" w q)) :
    0 ≤ windowSum σ u deposit "response" w q - windowSum σ u withdraw "request" w q := by
  obtain ⟨ι₀, hc, hleaf⟩ := leafHolds_of_allow h
  exact balance_of_leaf hpq hu hleaf (readLong_of_range hd.1 hd.2) (readLong_of_range hw.1 hw.2)
    (hc.admissible hι).arith

/-- **Under a reading that computes aggregates exactly below `2 ^ 127` and keeps the side of an
out-of-range arithmetic result, as clamping does, the balance is exact on every trace of fewer
than `2 ^ 63` events**: a change to the reference interpreter's reading that makes the example
hold without a hypothesis on the amounts. -/
theorem allowed_withdraw_balance_mixed {ι : ImplChoices}
    (hagg : ∀ n, -(2 ^ 127 : Int) ≤ n → n < 2 ^ 127 → ι.outOfRange n = some n)
    (harith : SidePreserving ι.arithOutOfRange)
    {ω : Provider.Providers} {σ : Trace} {w : Window} {q : Nat} {pq : TimePoint} {u : EntityUID}
    (h : ((policySet w).authorize ι ω σ q).decision? = some .allow)
    (hpq : σ[q]? = some pq) (hu : pq.event.principal = some u)
    (hlen : (σ.length : Int) < 2 ^ 63) :
    0 ≤ windowSum σ u deposit "response" w q - windowSum σ u withdraw "request" w q := by
  obtain ⟨ι₀, hc, hleaf⟩ := leafHolds_of_allow h
  have hagg₀ : ∀ n, -(2 ^ 127 : Int) ≤ n → n < 2 ^ 127 → ι₀.outOfRange n = some n :=
    fun n h₁ h₂ => hc.aggregate.agrees n n (hagg n h₁ h₂)
  have hq : (q : Int) + 1 ≤ σ.length := by
    have := (List.getElem?_eq_some_iff.mp hpq).1; omega
  have hmul : ((q + 1 : Nat) : Int) * 2 ^ 63 < 2 ^ 126 := by
    have h₀ : ((q + 1 : Nat) : Int) ≤ 2 ^ 63 - 1 := by push_cast; omega
    have := Int.mul_le_mul_of_nonneg_right h₀ (by decide : (0 : Int) ≤ 2 ^ 63)
    have hc : ((2 : Int) ^ 63 - 1) * 2 ^ 63 < 2 ^ 126 := by decide
    omega
  have h126 : (2 : Int) ^ 126 ≤ 2 ^ 127 := by decide
  obtain ⟨d₁, d₂⟩ := windowSum_bounds σ u deposit "response" w q
  obtain ⟨w₁, w₂⟩ := windowSum_bounds σ u withdraw "request" w q
  exact balance_of_leaf hpq hu hleaf (readLong_exact hagg₀ (by omega) (by omega))
    (readLong_exact hagg₀ (by omega) (by omega)) (sidePreserving_completes harith hc.arith)

end Dogwood.Examples.Balance
