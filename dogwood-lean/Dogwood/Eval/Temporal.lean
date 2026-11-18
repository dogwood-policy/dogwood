import Dogwood.Eval.Candidates
import Dogwood.Spec.EventSchema

/-!
# An executable evaluator for temporal conditions

`eval ι rate σ e vis J v j φ` decides whether `φ` holds at timepoint `j` of the trace `σ`, whose
timestamps count ticks of the rate `rate`, for a decision at `e`, observing the timepoints `vis`
marks, under the valuation `v`.
`Dogwood.Thm.eval_iff` proves that it decides `Sat` for every safe condition, at every timepoint
up to `J`.

The temporal operators search the finitely many earlier timepoints. What `Sat` quantifies over
all values, the evaluator searches among the candidates of `Dogwood.Eval.Candidates`, seeded
with the values `v` gives the free variables of the quantifier:

* an `exists` whose body binds its variable by an equality `x == t` (or `t == x`) among its
  top-level conjuncts, possibly under nested `exists` of other variables, with `t` mentioning
  none of them, tries only the value `t` denotes (`bindingValue?`): any witness must be that
  value. Any other `exists` tries each candidate value of its variable;
* an aggregate's rows are the rows of candidate values that satisfy its body. The candidates are
  deduplicated first, so the rows are distinct without deduplicating them.

The search is exhaustive, so its cost is exponential in the number of variables an aggregate's
domain binds. It is meant for checking the specification against the reference implementation,
not for enforcement.
-/

namespace Dogwood.Eval

open Dogwood.Spec Dogwood.Spec.Temporal
open Cedar.Spec (Value)

/-- `xs` without repetitions, keeping each first occurrence; tail-recursive. -/
def uniq {α : Type} [BEq α] (xs : List α) : List α :=
  go xs []
where
  go : List α → List α → List α
    | [], acc => acc.reverse
    | x :: xs, acc => if acc.contains x then go xs acc else go xs (x :: acc)

/-- `CmpOp.Holds`, as a Boolean. -/
def CmpOp.holds : CmpOp → CVal → CVal → Bool
  | .eq, a, b => decide (a = b)
  | .ne, a, b => decide (a ≠ b)
  | .lt, .num m, .num n => decide (m < n)
  | .le, .num m, .num n => decide (m ≤ n)
  | .gt, .num m, .num n => decide (m > n)
  | .ge, .num m, .num n => decide (m ≥ n)
  | _, _, _ => false

/-- `Term.Matches`, as a Boolean. -/
def matchesB (e : Event) (v : Valuation) (t : Term) (w : Value) : Bool :=
  match t with
  | .wildcard => true
  | t => decide (t.eval? e v = some (.val w))

/-- `ArgsMatch`, as a Boolean. -/
def argsMatchB (e : Event) (v : Valuation) (ev : Event) (args : List (Path × Term)) : Bool :=
  args.all fun a =>
    match recordPath? ev.logged a.1 with
    | some w => matchesB e v a.2 w
    | none => false

/-- `InWindow`, as a Boolean. -/
def inWindowB (rate : TickRate) (σ : Trace) (j k : Nat) (w : Window) : Bool :=
  match σ[j]?, σ[k]? with
  | some pj, some pk => decide (0 ≤ pj.ts - pk.ts ∧ pj.ts - pk.ts ≤ w.ticks rate)
  | _, _ => false

/-- The value side of a binding equality for `x` among the top-level conjuncts of a condition:
the first equality `x == t` or `t == x` that restricts `x` and whose value side `t` does not
mention `x`. A binding under a nested `exists` of another variable counts when its value side
does not mention that variable either. -/
def bindingValue? (x : VarName) : Formula → Option Term
  | .and φ ψ =>
    match bindingValue? x φ with
    | some t => some t
    | none => bindingValue? x ψ
  | .cmp .eq l r =>
    if eqRestricted? l r == some x && !(valueSide x l r).fv.contains x then
      some (valueSide x l r)
    else none
  | .exist y φ =>
    if y.name == x then none
    else
      match bindingValue? x φ with
      | some t => if t.fv.contains y.name then none else some t
      | none => none
  | _ => none

theorem valueSide_sizeOf (x : VarName) (op : CmpOp) (l r : Term) :
    sizeOf (valueSide x l r) < sizeOf (Formula.cmp op l r) := by
  unfold valueSide
  split
  · split <;> simp only [Formula.cmp.sizeOf_spec] <;> omega
  · simp only [Formula.cmp.sizeOf_spec]; omega

theorem bindingValue?_sizeOf {x : VarName} : {φ : Formula} → {t : Term} →
    bindingValue? x φ = some t → sizeOf t < sizeOf φ
  | .and φ ψ, t, h => by
    simp only [bindingValue?] at h
    split at h
    · rename_i r hr
      cases h
      have := bindingValue?_sizeOf hr
      simp only [Formula.and.sizeOf_spec]; omega
    · have := bindingValue?_sizeOf h
      simp only [Formula.and.sizeOf_spec]; omega
  | .cmp op l r, t, h => by
    cases op <;> simp only [bindingValue?] at h
    all_goals first
      | (split at h
         · simp only [Option.some.injEq] at h
           subst h
           exact valueSide_sizeOf x _ l r
         · cases h)
      | cases h
  | .exist y φ, t, h => by
    simp only [bindingValue?] at h
    split at h
    · cases h
    · split at h
      · rename_i t' ht'
        split at h
        · cases h
        · cases h
          have := bindingValue?_sizeOf ht'
          simp only [Formula.exist.sizeOf_spec]; omega
      · cases h
  | .not _, _, h | .formerly _ _, _, h | .previous _ _, _, h | .since _ _ _, _, h
  | .pred _ _ _, _, h | .tp _, _, h => by simp [bindingValue?] at h

section

variable (ι : ImplChoices) (rate : TickRate) (σ : Trace) (e : Event) (vis : Nat → Bool) (J : Nat)

mutual

/-- Whether `φ` holds at timepoint `j` under `v`. -/
def eval (v : Valuation) (j : Nat) : Formula → Bool
  | .and φ ψ => eval v j φ && eval v j ψ
  | .not φ => !eval v j φ
  | .formerly w φ =>
    (List.range (j + 1)).any fun k => vis k && inWindowB rate σ j k w && eval v k φ
  | .previous w φ =>
    (List.range j).any fun k =>
      vis k && ((List.range j).all fun k' => !decide (k < k') || !vis k') &&
        inWindowB rate σ j k w && eval v k φ
  | .since φ w ψ =>
    (List.range (j + 1)).any fun k =>
      vis k && inWindowB rate σ j k w && eval v k ψ &&
        (List.range (j + 1)).all fun k' => !decide (k < k') || !vis k' || eval v k' φ
  | .pred a kd args =>
    match σ[j]? with
    | some p => decide (p.event.action = a) && decide (p.event.kind = kd) &&
        argsMatchB e v p.event args
    | none => false
  | .cmp op l r =>
    match denote v j l, denote v j r with
    | some a, some b => CmpOp.holds op a b
    | _, _ => false
  | .exist x φ =>
    match h : bindingValue? x.name φ with
    | some t =>
      have := bindingValue?_sizeOf h
      match denote v j t with
      | some c => eval (v.bind x.name c.toTVal) j φ
      | none => false
    | none =>
      (uniq (φ.cand ι σ e J ((Formula.exist x φ).fv.filterMap v))).any fun w =>
        eval (v.bind x.name w) j φ
  | .tp x => decide (v x = some (tpValue j))
termination_by φ => sizeOf φ

/-- The value the comparison operand `t` denotes at timepoint `j` under `v`, if any. -/
def denote (v : Valuation) (j : Nat) : Term → Option CVal
  | .agg a => ι.aggregateValue (total v j a)
  | .arith op l r =>
    match denote v j l, denote v j r with
    | some (.num m), some (.num n) => ι.arithValue (op.apply m n)
    | _, _ => none
  | t => (t.eval? e v).map CVal.ofTVal
termination_by t => sizeOf t

/-- The exact total of the aggregate `a` at timepoint `j` under `v`. -/
def total (v : Valuation) (j : Nat) : Aggregate → Int
  | .count dom body =>
    ((product (uniq (body.cand ι σ e J ((Aggregate.count dom body).fv.filterMap v)))
      (domainNames dom).length).filter
      fun row => eval (v.bindAll (domainNames dom) row) j body).length
  | .sum s dom body =>
    (((product (uniq (body.cand ι σ e J ((Aggregate.sum s dom body).fv.filterMap v)))
      (domainNames dom).length).filter
      fun row => eval (v.bindAll (domainNames dom) row) j body).map
        (summand s (domainNames dom))).sum
termination_by a => sizeOf a

end

end

/-! ## Visibility -/

/-- `EventSchema.Mine`, as a Boolean. -/
def mineB (S : EventSchema) (e ev : Event) : Bool :=
  S.any (fun s => decide (s.action = ev.action) && decide (s.kind = ev.kind)) &&
  S.universalPins.all fun p =>
    match recordPath? ev.logged p.field, p.ref.toTerm.eval? e Valuation.empty with
    | some w, some w' => decide (TVal.val w = w')
    | _, _ => false

/-- `EventSchema.Visible`, as a Boolean. -/
def visibleB (S : EventSchema) (σ : Trace) (e : Event) (k : Nat) : Bool :=
  S.universalPins.isEmpty ||
    match σ[k]? with
    | some p => mineB S e p.event
    | none => false

end Dogwood.Eval
