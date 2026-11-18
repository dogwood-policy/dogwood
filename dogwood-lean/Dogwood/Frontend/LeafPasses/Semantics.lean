import Dogwood.Frontend.LeafPasses
import Dogwood.Frontend.Conformance
import Dogwood.Spec.Decision
import Dogwood.Spec.Temporal.Typing

/-!
# What the relativized leaves mean

The relativization rewrite (`LeafPasses.relativize`) produces conditions that are not formulas of
the specification's logic: μ is a disjunction over the event signatures, and the encodings of
`previous` and `since` order timepoints (`tj < ti`). The specification states key-local semantics
directly instead, by visibility (`EventSchema.Visible`), and an ordering of two timepoints is
false there (`CmpOp.Holds`). This module gives the crate's temporal AST a satisfaction relation
that extends the specification's `Sat` with the two things the rewrite needs, and states the
theorem that relates the rewrite to the specification.

## The extended relation

`XSat ι rate σ e vis ord dom v j c` is `Sat` over the crate's AST (`Surface.Temporal.Condition`),
with the same five parameters, and two more:

* `ord`: whether an ordering of two timepoints compares their positions. With `ord = true`, as in
  the crate's interpreter, which represents a timepoint by its index, `tj < ti` holds when `tj`
  is an earlier position than `ti`; with `ord = false`, as in the specification, it is false;
* `dom`: the values a binder of a declared type ranges over, in `exists` and in a `for` list.
  The specification's `exists` ranges over every value and every timepoint (`anyValue`); the
  sorted reading (`sortedValue`) lets a `Timepoint` binder range over timepoints only, and any
  other binder over values only.

`or` holds when either side does. A predicate, a term, a window and a binder mean what their
projections (`Condition.toFormula`) mean in the specification; a node the projection rejects
(a macro form, `within ?w`, an array constant, a scope term not rooted at `principal` or
`resource`) holds of nothing, or denotes nothing. So `XSat` with `ord = false` and `dom =
anyValue` is the specification's `Sat` on every projectable condition
(`Dogwood.Thm.Frontend.xsat_iff_sat`), and `RSat`, with `ord = true` and `dom = anyValue`, is
the relation the relativized leaves are read under.

## The relativization theorem

`RelativizationTheorem` states, as a proposition, what the rewrite is for: on traces whose
timestamps strictly increase, the relativized executable leaf, evaluated under `RSat` with every
timepoint visible, holds exactly when the specification's `LeafHolds` holds. It is proved in
`Dogwood.Thm.Frontend.Relativization` (`Dogwood.Thm.Frontend.relativization_correct`).
-/

namespace Dogwood.Frontend.LeafPasses

open Surface.Temporal
open Dogwood.Spec (Event Trace TickRate PolicySet EventSchema)
open Dogwood.Spec.Temporal (Valuation TVal CVal CmpOp BinderType Binder VarName ImplChoices
  InWindow ArgsMatch tpValue domainNames summand Formula TypingCtx)

/-! ## Domains and orderings -/

/-- The values a binder of a declared type may take. -/
abbrev Domain := BinderType → TVal → Prop

/-- Every value and every timepoint, whatever the declared type: the specification's reading. -/
def anyValue : Domain := fun _ _ => True

/-- The sorted reading: a `Timepoint` binder ranges over timepoints, any other over values. -/
def sortedValue : Domain := fun ty w => (ty = .timepoint ↔ ∃ k, w = .tp k)

/-- An ordering of two timepoints, by position. -/
def tpOrders : CmpOp → CVal → CVal → Prop
  | .lt, .tp m, .tp n => m < n
  | .le, .tp m, .tp n => m ≤ n
  | .gt, .tp m, .tp n => m > n
  | .ge, .tp m, .tp n => m ≥ n
  | _, _, _ => False

/-- A comparison holds: as in the specification, or, when `ord` holds, as an ordering of two
timepoints by position. -/
def xHolds (ord : Bool) (op : CmpOp) (a b : CVal) : Prop :=
  op.Holds a b ∨ (ord = true ∧ tpOrders op a b)

/-- The declared type of the column `x` of a `for` list: the type of its last binder named `x`,
which is the binder in scope over the body (`unorderAggKind`). -/
def columnType (bs : List Binder) (x : VarName) : BinderType :=
  ((bs.reverse.find? (·.name == x)).map (·.ty)).getD .timepoint

/-- Every value of the row is in the domain of its column's declared type. -/
def RowIn (dom : Domain) (bs : List Binder) (row : List TVal) : Prop :=
  ∀ p ∈ (domainNames bs).zip row, dom (columnType bs p.1) p.2

/-! ## Satisfaction -/

section

variable (ι : ImplChoices) (rate : TickRate) (σ : Trace) (e : Event) (vis : Nat → Prop)
  (ord : Bool) (dom : Domain)

mutual

/-- `c` holds at timepoint `j` under the valuation `v`: the specification's `Sat`, with `or`, the
orderings of timepoints `ord` allows, and binders ranging over `dom`. -/
def XSat (v : Valuation) (j : Nat) : Condition → Prop
  | ⟨_, .and l r⟩ => XSat v j l ∧ XSat v j r
  | ⟨_, .or l r⟩ => XSat v j l ∨ XSat v j r
  | ⟨_, .not c⟩ => ¬ XSat v j c
  | ⟨_, .formerly w c⟩ => ∃ win, w.toSpec = .ok win ∧
      ∃ k, k ≤ j ∧ vis k ∧ InWindow rate σ j k win ∧ XSat v k c
  | ⟨_, .previous w c⟩ => ∃ win, w.toSpec = .ok win ∧
      ∃ k, k < j ∧ vis k ∧ (∀ k', k < k' → k' < j → ¬ vis k') ∧
        InWindow rate σ j k win ∧ XSat v k c
  | ⟨_, .since l w r⟩ => ∃ win, w.toSpec = .ok win ∧
      ∃ k, k ≤ j ∧ vis k ∧ InWindow rate σ j k win ∧ XSat v k r ∧
        ∀ k', k < k' → k' ≤ j → vis k' → XSat v k' l
  | ⟨_, .predicate ⟨_, ns, a, kd, args⟩⟩ =>
    ∃ uid args', entityUid ("::".intercalate ns) a = .ok uid ∧
      NamedArg.toSpecList args = .ok args' ∧
      ∃ p, σ[j]? = some p ∧ p.event.action = uid ∧ p.event.kind = kd ∧
        ArgsMatch e v p.event args'
  | ⟨_, .comparison op l r⟩ => ∃ a b, XDenotes v j l a ∧ XDenotes v j r b ∧ xHolds ord op a b
  | ⟨_, .exists ⟨s, ty⟩ c⟩ => ∃ x, s.toName = .ok x ∧ ∃ w, dom ty w ∧ XSat (v.bind x w) j c
  | ⟨_, .tp s⟩ => ∃ x, s.toName = .ok x ∧ v x = some (tpValue j)
  | ⟨_, .call _⟩ => False
  | ⟨_, .sigilRef _ _⟩ => False
  | ⟨_, .refine _ _ _⟩ => False

/-- The comparison operand `t` denotes `c` at timepoint `j` under `v` (the specification's
`Denotes`). -/
def XDenotes (v : Valuation) (j : Nat) : Surface.Temporal.Term → CVal → Prop
  | .agg ⟨_, k⟩, c => ∃ n, XTotal v j k n ∧ ι.aggregateValue n = some c
  | .arith op l r, c => ∃ m n, XDenotes v j l (.num m) ∧ XDenotes v j r (.num n) ∧
      ι.arithValue (op.apply m n) = some c
  | t, c => ∃ t', t.toSpec = .ok t' ∧ ∃ w, t'.eval? e v = some w ∧ c = CVal.ofTVal w

/-- The aggregate has the exact total `n` at timepoint `j` under `v` (the specification's
`Total`), its rows drawn from `dom`. -/
def XTotal (v : Valuation) (j : Nat) : AggExprKind → Int → Prop
  | .count vs body, n => ∃ bs, vs.mapM TypedBinder.toSpec = .ok bs ∧
      ∃ rows : List (List TVal), rows.Nodup ∧
        (∀ row, row ∈ rows ↔ (row.length = (domainNames bs).length ∧ RowIn dom bs row ∧
          XSat (v.bindAll (domainNames bs) row) j body)) ∧
        n = rows.length
  | .sum s vs body, n => ∃ x bs, s.toName = .ok x ∧ vs.mapM TypedBinder.toSpec = .ok bs ∧
      ∃ rows : List (List TVal), rows.Nodup ∧
        (∀ row, row ∈ rows ↔ (row.length = (domainNames bs).length ∧ RowIn dom bs row ∧
          XSat (v.bindAll (domainNames bs) row) j body)) ∧
        n = (rows.map (summand x (domainNames bs))).sum
  | .call _, _ => False

end

end

/-- The relation the relativized leaves are read under: timepoints ordered by position, and
binders ranging over every value, as in the specification. -/
abbrev RSat (ι : ImplChoices) (rate : TickRate) (σ : Trace) (e : Event) (vis : Nat → Prop) :
    Valuation → Nat → Condition → Prop :=
  XSat ι rate σ e vis true anyValue

/-! ## The relativization theorem -/

/-- The derived event schema `d` is the specification's `S`, up to the fields' types: the same
signatures in the same order, with the same pins (`toSpecUntyped`); each event's action name, as
a predicate's projection reads it, is the signature's action; and each pinned field's path
survives the text form of a predicate argument. -/
structure Agrees (d : DerivedEventSchema) (S : EventSchema) : Prop where
  untyped : d.toSpecUntyped = .ok (S.map fun s => { s with fields := [] })
  names : ∀ ev ∈ d.events,
    entityUid ("::".intercalate ev.namespace) ev.action = .ok (actionUid ev.namespace ev.action)
  paths : ∀ ev ∈ d.events, ∀ p ∈ ev.pins, fieldPathSplit (fieldPathJoin p.fieldPath) = p.fieldPath

/-- No variable of the condition starts with `pre`, so none is a fresh name of the
relativization rewrite drawn with the prefix `pre` (`fresh`). The rewrite's prefix is chosen so
(`freshPrefix`). -/
def NoFreshNames (pre : String) (c : Condition) : Prop :=
  ∀ x ∈ condNames c, hasPrefix pre x = false

/-- **The relativization theorem** (a statement; `Dogwood.Thm.Frontend.relativization_correct`
proves it).

Let `c` be a temporal leaf in the crate's AST, authored as the specification's `φ`, and `d` the
crate's derived event schema, which agrees with the policy set's schema `P.schema`. Let the leaf
be well-typed in a typing context over `P.schema`, and safe; let pin injection commute with the
projection on it (`Dogwood.Thm.Frontend.injectCond_toFormula_of_agrees` gives this from `Agrees`
and the faithfulness of its action names). Let `r` be the crate's relativized executable leaf: `c`
with its pins injected, its timepoint orderings made false, and relativized for the universal
symmetric pins of `d`.

Then on a trace whose timestamps strictly increase, and which is not longer than the largest
`Long` (so that the counts of the `since` encoding are `Long`s), `r` holds at the timepoint `n`,
evaluated under `RSat` with every timepoint visible, exactly when the specification's leaf
`LeafHolds ι P σ n φ` holds.

Why each hypothesis is there:

* strictly increasing (or at least nondecreasing) timestamps: the encodings of `previous` and
  `since` find "the mine positions between `tj` and `ti`" through windows measured from `ti`
  (`REFERENCE.md`, "Relationship to the reference implementation", the item "Key-local
  semantics with out-of-order timestamps");
* the length bound: with an out-of-range count, a clamping reading makes two different counts
  equal;
* typing and safety: `unorderTimepoints` turns an ordering of a `Timepoint` binder into `false`,
  which is the specification's meaning only when the binder holds a timepoint; and a predicate
  confines its body to the key only when it names a declared signature, whose pins include the
  universal ones (`implies_mine`).

The leaf's own names need no hypothesis: the rewrite draws its fresh names with a prefix that no
variable of the leaf starts with (`freshPrefix`). If the prefix were the fixed `__pin_`, a leaf
that binds `__pin_ti0` and uses it inside a `previous` would see the rewrite's own `__pin_ti0`
there instead. -/
def RelativizationTheorem : Prop :=
  ∀ (ι : ImplChoices) (P : PolicySet) (d : DerivedEventSchema) (pins : List Pin)
    (c : Condition) (φ : Formula) (r : Condition) (σ : Trace) (n : Nat),
    Agrees d P.schema →
    universalPins d = .ok pins →
    c.toFormula = .ok φ →
    (injectCond d c).toFormula = .ok (φ.injectPins P.schema) →
    (∃ C : TypingCtx, C.events = P.schema ∧ φ.WellTyped C []) →
    φ.IsSafe →
    relativize d pins (unorderCond [] (injectCond d c)) = .ok r →
    σ.StrictlyIncreasing →
    σ.length ≤ Int64.MAX →
    ((∃ p, σ[n]? = some p ∧ RSat ι P.tickRate σ p.event (fun _ => True) Valuation.empty n r) ↔
      P.LeafHolds ι σ n φ)

end Dogwood.Frontend.LeafPasses
