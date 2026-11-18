import Dogwood.Spec.Temporal.Syntax

/-!
# Temporal conditions: satisfaction

`Sat ι rate σ e vis v j φ` — *the condition `φ` holds at timepoint `j` of the
trace `σ`, under the valuation `v`* — for a condition belonging to a decision
made at the event `e`. This is the semantics of guide chapter 4 ("Evaluation
semantics"), stated as a satisfaction relation in the style of metric
first-order temporal logic rather than as the reference interpreter's
binding-threading evaluator (`interpreter/eval.rs`).

Five parameters fix the context of a satisfaction question:

* `ι` — the implementation-defined reading of an out-of-range aggregate total
  or arithmetic result (`ImplChoices`);
* `rate` — the resolution of the clock the trace's timestamps are counted in
  (`TickRate`): a window of `w` seconds spans `w × rate.perSecond` ticks;
* `σ` — the trace;
* `e` — the **decision event**. Request-side terms (`context.*`, `principal`,
  `resource`) denote values of the *current request* at every timepoint an
  operator scans, never of a matched past event;
* `vis` — the timepoints the condition can observe. Under global semantics
  every timepoint is visible; under key-local semantics (a universal symmetric
  pin, see `Dogwood.Spec.EventSchema`) only the events agreeing with the
  current request on the pinned fields are. Windows are always measured from
  the timepoint being evaluated, by timestamp, in ticks.

The relation is not executable: `exists` quantifies over all values, and an
aggregate denotes the size (or total) of a set of valuations. A condition that
is safe (`Dogwood.Spec.Temporal.Formula.Safe`) is monitorable: every such set
is finite (`Dogwood.Thm.Monitorable`), and the verified evaluator decides the
relation (`Dogwood.Thm.eval_iff`).

## Timepoints are a sort of their own

A variable holds a `TVal`: a Cedar value, or a timepoint. `tp(x)` holds when
`x` holds the timepoint being evaluated; `x` itself is bound by an `exists` or a
`for` list. A timepoint is equal to itself and to nothing
else, and no operator orders it, adds to it, or compares it with a Cedar value.
So a condition cannot observe how timepoints are numbered, only which of them
are the same. An implementation may number timepoints as it likes: per
partition, from a monitor's installation, or from 1 (`Dogwood.Thm.sat_subseq`).
-/

namespace Dogwood.Spec.Temporal

open Cedar.Spec (Value)

/-! ## Values of variables -/

/-- The value of a temporal variable: a Cedar value, or a timepoint. -/
inductive TVal where
  | val (v : Value)
  /-- The timepoint at index `k` of the trace. Only equality observes the index. -/
  | tp (k : Nat)
deriving DecidableEq, Repr, Inhabited

/-! ## Valuations -/

/-- An assignment of values to temporal variables; `none` means unbound. -/
abbrev Valuation := VarName → Option TVal

def Valuation.empty : Valuation := fun _ => none

/-- `v` with `x` bound to `w`, shadowing any outer binding of `x`. -/
def Valuation.bind (v : Valuation) (x : VarName) (w : TVal) : Valuation :=
  fun y => if y = x then some w else v y

/-- `v` with each `xᵢ` bound to `wᵢ`, left to right. -/
def Valuation.bindAll (v : Valuation) : List VarName → List TVal → Valuation
  | x :: xs, w :: ws => (v.bind x w).bindAll xs ws
  | _, _ => v

/-- The value `tp(x)` requires of `x` at timepoint `j`. -/
def tpValue (j : Nat) : TVal := .tp j

/-! ## Terms -/

/-- The value of a non-aggregate term, under `v`, for a decision at `e`;
`none` when the term does not resolve (an unbound variable, a wildcard, an
absent field, a `decimal` payload Cedar rejects). Neither an aggregate nor a
compound operand resolves here: both are well-placed only in comparison-operand
position, where `Denotes` gives their meaning. -/
def Term.eval? (e : Event) (v : Valuation) : Term → Option TVal
  | .entity uid => some (.val (.prim (.entityUID uid)))
  | .long i => some (.val (.prim (.int i)))
  | .decimal s => (Cedar.Spec.Ext.Decimal.parse s).map fun d => .val (.ext (.decimal d))
  | .string s => some (.val (.prim (.string s)))
  | .bool b => some (.val (.prim (.bool b)))
  | .context p => (e.contextPath? p).map .val
  | .scope r p => (e.scopePath? r p).map .val
  | .var x => v x
  | .wildcard => none
  | .agg _ => none
  | .arith _ _ _ => none

/-- The term of a predicate argument matches the event field value `w`: a
wildcard matches anything; any other term must resolve to `w`. A timepoint
never matches a field value. -/
def Term.Matches (e : Event) (v : Valuation) (t : Term) (w : Value) : Prop :=
  match t with
  | .wildcard => True
  | t => t.eval? e v = some (.val w)

/-- Every named argument of a predicate is matched by the event `ev`: the
field is present in the logged record, and its value matches the argument's
term. A mentioned field that is absent fails the match, even against `*`. -/
def ArgsMatch (e : Event) (v : Valuation) (ev : Event) (args : List (Path × Term)) : Prop :=
  ∀ a ∈ args, ∃ w, recordPath? ev.logged a.1 = some w ∧ a.2.Matches e v w

/-! ## Comparisons -/

/-- A comparison operand's value. A `Long` is read as the integer it denotes,
so that an aggregate total (an unbounded integer) compares with it. -/
inductive CVal where
  | num (n : Int)
  /-- Any Cedar value that is not a `Long`. -/
  | val (v : Value)
  /-- A timepoint. -/
  | tp (k : Nat)
deriving DecidableEq

/-- A Cedar value, as a comparison operand. -/
def CVal.ofValue : Value → CVal
  | .prim (.int i) => .num i.toInt
  | v => .val v

/-- A variable's value, as a comparison operand. -/
def CVal.ofTVal : TVal → CVal
  | .val v => .ofValue v
  | .tp k => .tp k

/-- Equality is domain equality; ordering requires two integers and is false
otherwise (a `decimal` is equality-only in the temporal sub-language, and a
timepoint is equality-only). -/
def CmpOp.Holds : CmpOp → CVal → CVal → Prop
  | .eq, a, b => a = b
  | .ne, a, b => a ≠ b
  | .lt, .num m, .num n => m < n
  | .le, .num m, .num n => m ≤ n
  | .gt, .num m, .num n => m > n
  | .ge, .num m, .num n => m ≥ n
  | _, _, _ => False

/-! ## Implementation-defined behavior -/

/-- The readings of integer results outside the `Long` range, which the
language leaves implementation-defined (guide chapter 8, §5.4, "Aggregate
value" and "Arithmetic out-of-range results"). `outOfRange n` is the integer a
comparison sees in place of an aggregate's exact total `n`; `arithOutOfRange n`
is the integer an arithmetic operation's exact result `n` is read as, by the
comparison or by the enclosing operation. Either is `none` for an
implementation that reports an error. Results inside the range are never
affected.

A decision under a reading that reports errors fails closed when its response
depends on how the erroring results are read (`PolicySet.respond`,
`FailClosed.temporalError`). `ImplChoices.Admissible` states which readings
are conforming. -/
structure ImplChoices where
  outOfRange : Int → Option Int
  arithOutOfRange : Int → Option Int

/-- Clamp `n` to the `Long` range. -/
def clampLong (n : Int) : Int := max Int64.MIN (min n Int64.MAX)

/-- Compute at a wider precision: the exact result. -/
def ImplChoices.widen : ImplChoices := ⟨some, some⟩

/-- Clamp to the nearest endpoint of the `Long` range — the reference
interpreter's choice, for aggregate totals (`sum_column`) and for each
arithmetic operation in tree order (`saturating_add` / `_sub` / `_mul`). -/
def ImplChoices.clamp : ImplChoices := ⟨fun n => some (clampLong n), fun n => some (clampLong n)⟩

/-- Report an error. -/
def ImplChoices.error : ImplChoices := ⟨fun _ => none, fun _ => none⟩

/-- The integer an exact result `n` is read as under the out-of-range
reading `f`. -/
def readLong (f : Int → Option Int) (n : Int) : Option CVal :=
  if Int64.MIN ≤ n ∧ n ≤ Int64.MAX then some (.num n) else (f n).map .num

/-- The operand value of an aggregate whose exact total is `n`. -/
def ImplChoices.aggregateValue (ι : ImplChoices) (n : Int) : Option CVal :=
  readLong ι.outOfRange n

/-- The operand value of an arithmetic operation whose exact result is `n`. -/
def ImplChoices.arithValue (ι : ImplChoices) (n : Int) : Option CVal :=
  readLong ι.arithOutOfRange n

/-! ## Windows -/

/-- Timepoint `k` lies in the window `w` looking back from timepoint `j`:
`0 ≤ ts(j) − ts(k) ≤ w`, closed at both ends, with the window's length in ticks
of the rate `rate`. -/
def InWindow (rate : TickRate) (σ : Trace) (j k : Nat) (w : Window) : Prop :=
  ∃ pj pk, σ[j]? = some pj ∧ σ[k]? = some pk ∧
    0 ≤ pj.ts - pk.ts ∧ pj.ts - pk.ts ≤ w.ticks rate

/-! ## Satisfaction -/

/-- The summand of an aggregation row: the value the row gives the summed
variable, when it is a `Long`. A row whose summand is not a `Long` adds
nothing — though `count` over the same rows still counts it. Validation makes
every summand a `Long` binder (`Formula.WellTyped`), and conformance makes
every value it binds a `Long` (`Dogwood.Thm.rows_sorted`). -/
def summand (s : VarName) (names : List VarName) (row : List TVal) : Int :=
  match (names.zip row).lookup s with
  | some (.val (.prim (.int i))) => i.toInt
  | _ => 0

/-- `xs` without repetitions, keeping each first occurrence. -/
def dedup {α : Type} [BEq α] : List α → List α
  | [] => []
  | x :: xs => x :: (dedup xs).filter (· != x)

/-- The variables an aggregation's rows assign: its `for` variables, each
once. Validation makes them distinct (`Formula.WellTyped`); a variable listed
twice would be one column of the rows, as in the reference interpreter's
projection (`project_dedup`). -/
def domainNames (dom : List Binder) : List VarName := dedup (dom.map (·.name))

section

variable (ι : ImplChoices) (rate : TickRate) (σ : Trace) (e : Event) (vis : Nat → Prop)

mutual

/-- `φ` holds at timepoint `j` under the valuation `v`. -/
def Sat (v : Valuation) (j : Nat) : Formula → Prop
  | .and φ ψ => Sat v j φ ∧ Sat v j ψ
  | .not φ => ¬ Sat v j φ
  -- `φ` held at some visible timepoint in the window, `j` itself included.
  | .formerly w φ => ∃ k, k ≤ j ∧ vis k ∧ InWindow rate σ j k w ∧ Sat v k φ
  -- `φ` held at the last visible timepoint before `j`, and that timepoint is
  -- in the window. False when there is none.
  | .previous w φ =>
    ∃ k, k < j ∧ vis k ∧ (∀ k', k < k' → k' < j → ¬ vis k') ∧
      InWindow rate σ j k w ∧ Sat v k φ
  -- The anchor `ψ` held at some visible timepoint `k` in the window, and `φ`
  -- has held at every visible timepoint after `k`, through `j`.
  | .since φ w ψ =>
    ∃ k, k ≤ j ∧ vis k ∧ InWindow rate σ j k w ∧ Sat v k ψ ∧
      ∀ k', k < k' → k' ≤ j → vis k' → Sat v k' φ
  | .pred a kd args =>
    ∃ p, σ[j]? = some p ∧ p.event.action = a ∧ p.event.kind = kd ∧
      ArgsMatch e v p.event args
  | .cmp op l r => ∃ a b, Denotes v j l a ∧ Denotes v j r b ∧ op.Holds a b
  | .exist x φ => ∃ w, Sat (v.bind x.name w) j φ
  | .tp x => v x = some (tpValue j)

/-- The comparison operand `t` denotes `c` at timepoint `j` under `v`. A
comparison holds only when both of its operands denote a value, so a comparison
with an operand that does not resolve is false, under `!=` too: `a != b` and
`!(a == b)` differ when `a` or `b` does not resolve. A
compound operand denotes the reading of its operator's exact result on two
integers its operands denote; when an operand denotes no integer (it is not a
`Long`, or does not resolve, as a wildcard never does), the compound denotes
nothing. -/
def Denotes (v : Valuation) (j : Nat) : Term → CVal → Prop
  | .agg a, c => ∃ n, Total v j a n ∧ ι.aggregateValue n = some c
  | .arith op l r, c => ∃ m n, Denotes v j l (.num m) ∧ Denotes v j r (.num n) ∧
      ι.arithValue (op.apply m n) = some c
  | t, c => ∃ w, t.eval? e v = some w ∧ c = CVal.ofTVal w

/-- The aggregate `a` has the exact total `n` at timepoint `j` under `v`.

The rows of an aggregation are the satisfying assignments of its `where`
body to its `for` domain — a *set*, so distinctness is the author's choice of
domain (include a timepoint variable constrained by `tp` to keep one row per
timepoint).
`count` is the number of rows; `sum s` adds each row's `Long` value of `s`.
When the body has infinitely many satisfying assignments no total exists;
a safe condition never has that property (`Dogwood.Thm.total_exists`). -/
def Total (v : Valuation) (j : Nat) : Aggregate → Int → Prop
  | .count dom body, n =>
    ∃ rows : List (List TVal), rows.Nodup ∧
      (∀ row, row ∈ rows ↔
        (row.length = (domainNames dom).length ∧
          Sat (v.bindAll (domainNames dom) row) j body)) ∧
      n = rows.length
  | .sum s dom body, n =>
    ∃ rows : List (List TVal), rows.Nodup ∧
      (∀ row, row ∈ rows ↔
        (row.length = (domainNames dom).length ∧
          Sat (v.bindAll (domainNames dom) row) j body)) ∧
      n = (rows.map (summand s (domainNames dom))).sum

end

end

end Dogwood.Spec.Temporal
