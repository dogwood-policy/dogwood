import Dogwood.Thm.Leaves
import Dogwood.Thm.Conservative
import Dogwood.Thm.Refinement
import Dogwood.Thm.DecisionSoundness

/-!
# Cedar expressions written as temporal leaves

Some constructs of Cedar have counterparts in the temporal sub-language: `Long`, `String`,
`Bool`, and entity literals, `decimal("…")`, `principal` and `resource`, `context.<path>`,
`principal.<path>` and `resource.<path>`, `+`, `-`, `*`, `==`, `<`, `<=`, `&&`, `||`, and `!`.
A Cedar expression built from them can be written as a temporal leaf instead, `temporal { … }`,
and means the same. `toTemporal` is that translation; it is partial, and a new construct with a
temporal counterpart is a new case of it and of the agreement proofs.

* **One expression** (`sat_toTemporal_iff`): where Cedar evaluates the expression to a `Bool`,
  its translation holds at a decision event carrying the request's context, principal, and
  resource exactly when the `Bool` is `true`, under every reading, over every trace, at every
  timepoint, with a store that reads entities as the event supplies them (`StoreFits`, which
  every decision's store satisfies). Two shapes are excluded (`Fits`): an attribute access
  through an entity other than the scope's root (a temporal path descends records only, where
  Cedar also reads an entity's attributes), and an ordering of `datetime`s or `duration`s (the
  temporal orderings apply to `Long`s only). Arithmetic agrees where Cedar evaluates it, so where
  it does not overflow, and then under every reading.
* **Predicate arguments** (`matches_toTerm`, `sat_pred_toArgs_iff`): a translated term as a
  predicate argument matches a logged value exactly when Cedar's `==` holds between the
  expression, at the current request, and the value; so a predicate whose arguments are
  translations holds at a timepoint exactly when its event, of the predicate's action and kind,
  logged at each field the value Cedar evaluates the argument to now.
* **Provider arguments** (`resolve_toArg`, `resolve_toArg_error`, `resolve_toSetArg`): a
  translated argument resolves to the value Cedar evaluates the expression to, and is `absent`
  (a null to the provider) exactly where Cedar errs; a set literal reaches the provider as the
  list of its items' values as written, in order and with duplicates, where Cedar's is a set.
  For a valid policy set, at a decision event that passes the checks, an argument is exactly
  what Cedar evaluates its expression to, or absent where Cedar errs, with no other hypothesis:
  its typing gives its fit and makes the entity it reads one the store reads as supplied
  (`resolve_providerArg_of_valid`).
* **The leaf** (`leaves_toTemporal`): the translation's value in a decision's leaf valuation is
  the expression's value. A translation reads only the decision event, and names no event (pin
  injection leaves it alone, `toTemporal_injectPins`).
* **A decision** (`authorize_toTemporal`): replacing a rule's condition `ofCedar e` by
  `temporal { φ }`, with `φ` the translation of `e`, changes no outcome at a timepoint, under
  every reading, where every decision event that passes the checks and evaluates the condition
  (the rule's scope holds, and so do the facts of the conditions before it) evaluates `e` to a
  `Bool` that fits, and supplies the scope entities whose attributes `φ` reads. The leaf invokes
  no provider; its scope reads are checked (check 6).
* **A valid policy set** (`authorize_toTemporal_of_valid`): for a valid policy set, the
  replacement changes no outcome at a timepoint where the leaf is well-typed, the scope entities
  are supplied, and Cedar's arithmetic does not overflow. Typing discharges the rest
  (`fits_of_wellTyped`): at an event that is an instance of the request's environment and where
  the leaf's facts hold, a typed attribute access resolves through records, and a typed ordering
  compares `Long`s, so Cedar evaluates `e` to a `Bool` that fits, or overflows. Validity is asked
  of the Cedar original and typing of the leaf, not validity of the set with the leaf: a
  translation reads only the decision event, so it monitors nothing, and validation rejects it as
  a leaf of its own (`toTemporal_not_monitorsTime`), a rule with no semantic consequence. Cedar's
  typing alone does not suffice either: it admits accesses through entities and orderings of
  `datetime`s and `duration`s, which `Fits` excludes.

Where Cedar errs, the temporal semantics has no error: an unresolved term makes its comparison
false, and a negation of it true. That is why the agreements are stated where Cedar evaluates
`e`. Two differences remain, each a theorem:

* An overflow errs in Cedar, which skips the rule; under a reading that reads the result the
  translation holds, and under one that reports an error its negation holds
  (`overflow_differs`). No reading agrees with Cedar on both `when` and `unless` rules.
* An unsupplied scope entity errs in Cedar's attribute read, which skips the rule; a leaf that
  reads it fails the whole decision closed (`authorize_toTemporal_missing`).
-/

namespace Dogwood.Thm

open Dogwood.Spec Dogwood.Spec.Temporal
open Cedar.Spec (Request Entities Value Prim Var BinaryOp UnaryOp Attr EntityUID)

/-! ## The translation -/

/-- The path of a Cedar `context.a.b…` access: `some []` for `context`, `none` for anything else. -/
def ctxPath : Cedar.Spec.Expr → Option Path
  | .var .context => some []
  | .getAttr x a => (ctxPath x).map (· ++ [a])
  | _ => none

/-- The root and path of a Cedar `principal.a.b…` or `resource.a.b…` access: the empty path for
the bare root, `none` for anything else. -/
def scopePath : Cedar.Spec.Expr → Option (ScopeRoot × Path)
  | .var .principal => some (.principal, [])
  | .var .resource => some (.resource, [])
  | .getAttr x a => (scopePath x).map fun rp => (rp.1, rp.2 ++ [a])
  | _ => none

/-- A Cedar attribute access `x.a` as a temporal term: a context path, or a path of `principal`
or `resource`. `id` and `type` are attributes like any other, on both sides. -/
def attrTerm (x : Cedar.Spec.Expr) (a : Attr) : Option Term :=
  match ctxPath x, scopePath x with
  | some p, _ => some (.context (p ++ [a]))
  | none, some (r, p) => some (.scope r (p ++ [a]))
  | none, none => none

/-- A Cedar expression as a temporal term: a literal, a `decimal("…")` literal, `principal`,
`resource`, an attribute access (`attrTerm`), or a sum, difference, or product of such. -/
def toTerm : Cedar.Spec.Expr → Option Term
  | .lit (.int i) => some (.long i)
  | .lit (.string s) => some (.string s)
  | .lit (.bool b) => some (.bool b)
  | .lit (.entityUID u) => some (.entity u)
  | .call .decimal [.lit (.string s)] => some (.decimal s)
  | .var .principal => some (.scope .principal [])
  | .var .resource => some (.scope .resource [])
  | .getAttr x a => attrTerm x a
  | .binaryApp .add x y => do pure (.arith .add (← toTerm x) (← toTerm y))
  | .binaryApp .sub x y => do pure (.arith .sub (← toTerm x) (← toTerm y))
  | .binaryApp .mul x y => do pure (.arith .mul (← toTerm x) (← toTerm y))
  | _ => none

/-- **A Cedar expression as a temporal condition**: a comparison of two terms with `==`, `<`, or
`<=`, or a conjunction, disjunction, or negation of such. `||` becomes `!(!· && !·)`. -/
def toTemporal : Cedar.Spec.Expr → Option Formula
  | .binaryApp .eq x y => do pure (.cmp .eq (← toTerm x) (← toTerm y))
  | .binaryApp .less x y => do pure (.cmp .lt (← toTerm x) (← toTerm y))
  | .binaryApp .lessEq x y => do pure (.cmp .le (← toTerm x) (← toTerm y))
  | .and x y => do pure (.and (← toTemporal x) (← toTemporal y))
  | .or x y => do pure (.not (.and (.not (← toTemporal x)) (.not (← toTemporal y))))
  | .unaryApp .not x => do pure (.not (← toTemporal x))
  | _ => none

/-! ## Where the two agree -/

section

variable (req : Request) (es : Entities)

/-- A term's attribute accesses run through records: every subject of an access other than
`principal` and `resource` that Cedar evaluates is a record. -/
def TermFits : Cedar.Spec.Expr → Prop
  | .getAttr x _ => TermFits x ∧ (x = .var .principal ∨ x = .var .resource ∨
      ∀ v, Cedar.Spec.evaluate x req es = .ok v → ∃ r, v = .record r)
  | .binaryApp _ x y => TermFits x ∧ TermFits y
  | _ => True

/-- **The expression fits the temporal sub-language** at the request: its attribute accesses run
through records, and its orderings compare `Long`s. -/
def Fits : Cedar.Spec.Expr → Prop
  | .binaryApp .eq x y => TermFits req es x ∧ TermFits req es y
  | .binaryApp .less x y | .binaryApp .lessEq x y =>
    TermFits req es x ∧ TermFits req es y ∧
      ∀ vx vy, Cedar.Spec.evaluate x req es = .ok vx → Cedar.Spec.evaluate y req es = .ok vy →
        (∃ i, vx = .prim (.int i)) ∧ ∃ j, vy = .prim (.int j)
  | .and x y | .or x y => Fits x ∧ Fits y
  | .unaryApp _ x => Fits x
  | _ => True

end

/-- Cedar's store reads an entity as the event supplies it, or with no attributes: the entity
store of a decision holds the schema's actions, which have none, and the event's entities
(`storeFits_decisionEntities`). -/
def StoreFits (es : Entities) (ev : Event) : Prop :=
  ∀ uid d, es.find? uid = some d → d.attrs = Cedar.Data.Map.empty ∨ ev.entities.find? uid = some d

theorem storeFits_decisionEntities (P : PolicySet) (ev : Event) :
    StoreFits (P.decisionEntities ev) ev := by
  intro uid d h
  rw [decisionEntities_find?] at h
  cases hact : P.actionSchema.acts.find? uid with
  | some entry =>
    rw [hact] at h
    simp only [Option.map_some, Option.some_or, Option.some.injEq] at h
    subst h
    exact .inl rfl
  | none =>
    rw [hact] at h
    simp only [Option.map_none, Option.none_or] at h
    exact .inr h

theorem valuePath_append (v : Value) : (p q : Path) →
    valuePath? v (p ++ q) = (valuePath? v p).bind (valuePath? · q)
  | [], q => rfl
  | a :: p, q => by
    cases v with
    | record r =>
      simp only [List.cons_append, valuePath?]
      cases r.find? a with
      | none => rfl
      | some w => exact valuePath_append w p q
    | _ => rfl

theorem ctxPath_var {x : Cedar.Spec.Expr} {p : Path} (h : ctxPath x = some p) :
    x ≠ .var .principal ∧ x ≠ .var .resource := by
  constructor <;> rintro rfl <;> simp [ctxPath] at h

/-- A context path Cedar evaluates through records is the record path of the context. -/
theorem valuePath_of_ctxPath {req : Request} {es : Entities} :
    (x : Cedar.Spec.Expr) → (p : Path) → ctxPath x = some p → TermFits req es x → (v : Value) →
      Cedar.Spec.evaluate x req es = .ok v → valuePath? (.record req.context) p = some v
  | .var .context, p, hp, _, v, hv => by
    simp only [ctxPath, Option.some.injEq] at hp
    subst hp
    simp only [Cedar.Spec.evaluate, Except.ok.injEq] at hv
    subst hv
    rfl
  | .getAttr x a, p, hp, hfit, v, hv => by
    simp only [ctxPath, Option.map_eq_some_iff] at hp
    obtain ⟨p', hp', rfl⟩ := hp
    simp only [TermFits] at hfit
    obtain ⟨hfit', hrec⟩ := hfit
    have hrec : ∀ v, Cedar.Spec.evaluate x req es = .ok v → ∃ r, v = .record r := by
      rcases hrec with h | h | h
      · exact absurd h (ctxPath_var hp').1
      · exact absurd h (ctxPath_var hp').2
      · exact h
    simp only [Cedar.Spec.evaluate] at hv
    cases hx : Cedar.Spec.evaluate x req es with
    | error e => rw [hx] at hv; cases hv
    | ok vx =>
      rw [hx] at hv
      obtain ⟨r, rfl⟩ := hrec vx hx
      have ih := valuePath_of_ctxPath x p' hp' hfit' _ hx
      simp only [Except.bind_ok, Cedar.Spec.getAttr, Cedar.Spec.attrsOf,
        Cedar.Data.Map.findOrErr] at hv
      cases hf : r.find? a with
      | none => rw [hf] at hv; cases hv
      | some w =>
        rw [hf] at hv
        simp only [Except.ok.injEq] at hv
        subst hv
        rw [valuePath_append, ih]
        simp [valuePath?, hf]
  | .lit _, _, hp, _, _, _ | .var .principal, _, hp, _, _, _ | .var .action, _, hp, _, _, _
  | .var .resource, _, hp, _, _, _ | .ite .., _, hp, _, _, _ | .and .., _, hp, _, _, _
  | .or .., _, hp, _, _, _ | .unaryApp .., _, hp, _, _, _ | .binaryApp .., _, hp, _, _, _
  | .hasAttr .., _, hp, _, _, _ | .extHasAttr .., _, hp, _, _, _ | .set .., _, hp, _, _, _
  | .record .., _, hp, _, _, _ | .call .., _, hp, _, _, _ => by cases hp

theorem recordPath_eq_valuePath (r : Cedar.Data.Map Attr Value) {q : Path} (hq : q ≠ []) :
    recordPath? r q = valuePath? (.record r) q := by
  cases q with
  | nil => exact absurd rfl hq
  | cons a q => rfl

theorem scopePath_nil {x : Cedar.Spec.Expr} {r : ScopeRoot} (h : scopePath x = some (r, [])) :
    (r = .principal ∧ x = .var .principal) ∨ (r = .resource ∧ x = .var .resource) := by
  rcases x with _ | ⟨_ | _ | _ | _⟩ | _ | _ | _ | _ | _ | ⟨x, a⟩ | _ | _ | _ | _ | _
  all_goals simp_all [scopePath]

theorem scopePath_var {x : Cedar.Spec.Expr} {r : ScopeRoot} {p : Path}
    (h : scopePath x = some (r, p)) (hp : p ≠ []) : x ≠ .var .principal ∧ x ≠ .var .resource := by
  constructor <;> rintro rfl <;> simp only [scopePath, Option.some.injEq, Prod.mk.injEq] at h <;>
    exact hp h.2.symm

section

variable {req : Request} {es : Entities} {ev : Event}

/-- **A scope path Cedar evaluates is the event's entity data**: at a decision event that carries
the request's principal and resource, with a store that reads entities as the event supplies
them, a `principal.a.b…` (or `resource`) that Cedar evaluates through records reads the same
value off the event's entity data. -/
theorem entityAttr_of_scopePath (hpr : ev.principal = some req.principal)
    (hrs : ev.resource = some req.resource) (hes : StoreFits es ev) :
    (x : Cedar.Spec.Expr) → (r : ScopeRoot) → (p : Path) → scopePath x = some (r, p) → p ≠ [] →
      TermFits req es x → (v : Value) → Cedar.Spec.evaluate x req es = .ok v →
      ∃ uid, ev.scope r = some uid ∧ ev.entityAttr? uid p = some v
  | .getAttr x a, r, p, hp, _, hfit, v, hv => by
    simp only [scopePath, Option.map_eq_some_iff, Prod.exists] at hp
    obtain ⟨r', p', hp', hrp⟩ := hp
    simp only [Prod.mk.injEq] at hrp
    obtain ⟨rfl, rfl⟩ := hrp
    simp only [TermFits] at hfit
    obtain ⟨hfit', hrec⟩ := hfit
    simp only [Cedar.Spec.evaluate] at hv
    cases hx : Cedar.Spec.evaluate x req es with
    | error e => rw [hx] at hv; cases hv
    | ok vx =>
      rw [hx] at hv
      simp only [Except.bind_ok] at hv
      by_cases hnil : p' = []
      · subst hnil
        -- The subject is the root: Cedar reads the entity's attributes off its store.
        have hroot : ∃ uid, ev.scope r' = some uid ∧ vx = .prim (.entityUID uid) := by
          rcases scopePath_nil hp' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · simp only [Cedar.Spec.evaluate, Except.ok.injEq] at hx
            exact ⟨_, hpr, hx.symm⟩
          · simp only [Cedar.Spec.evaluate, Except.ok.injEq] at hx
            exact ⟨_, hrs, hx.symm⟩
        obtain ⟨uid, huid, rfl⟩ := hroot
        refine ⟨uid, huid, ?_⟩
        simp only [Cedar.Spec.getAttr, Cedar.Spec.attrsOf, Entities.attrs,
          Cedar.Data.Map.findOrErr] at hv
        cases hd : es.find? uid with
        | none => rw [hd] at hv; cases hv
        | some d =>
          rw [hd] at hv
          simp only [Except.bind_ok] at hv
          cases hw : d.attrs.find? a with
          | none => rw [hw] at hv; cases hv
          | some w =>
            rw [hw] at hv
            simp only [Except.ok.injEq] at hv
            subst hv
            rcases hes uid d hd with he | he
            · rw [he] at hw; cases hw
            · simp [Event.entityAttr?, he, hw, valuePath?]
      · -- The subject is an attribute: a record, by the fit.
        have hrec : ∃ rec, vx = .record rec := by
          rcases hrec with h | h | h
          · exact absurd h (scopePath_var hp' hnil).1
          · exact absurd h (scopePath_var hp' hnil).2
          · exact h vx hx
        obtain ⟨rec, rfl⟩ := hrec
        obtain ⟨uid, huid, ih⟩ := entityAttr_of_scopePath hpr hrs hes x r' p' hp' hnil hfit' _ hx
        refine ⟨uid, huid, ?_⟩
        simp only [Cedar.Spec.getAttr, Cedar.Spec.attrsOf, Cedar.Data.Map.findOrErr,
          Except.bind_ok] at hv
        cases hw : rec.find? a with
        | none => rw [hw] at hv; cases hv
        | some w =>
          rw [hw] at hv
          simp only [Except.ok.injEq] at hv
          subst hv
          obtain ⟨b, q, rfl⟩ := List.exists_cons_of_ne_nil hnil
          simp only [Event.entityAttr?, List.cons_append] at ih ⊢
          rw [Option.bind_congr (fun w _ => valuePath_append w q [a]), ← Option.bind_assoc, ih]
          simp [valuePath?, hw]
  | .var .principal, _, _, hp, hne, _, _, _ | .var .resource, _, _, hp, hne, _, _, _ => by
    simp only [scopePath, Option.some.injEq, Prod.mk.injEq] at hp
    exact absurd hp.2.symm hne
  | .lit _, _, _, hp, _, _, _, _ | .var .action, _, _, hp, _, _, _, _
  | .var .context, _, _, hp, _, _, _, _ | .ite .., _, _, hp, _, _, _, _
  | .and .., _, _, hp, _, _, _, _ | .or .., _, _, hp, _, _, _, _
  | .unaryApp .., _, _, hp, _, _, _, _ | .binaryApp .., _, _, hp, _, _, _, _
  | .hasAttr .., _, _, hp, _, _, _, _ | .extHasAttr .., _, _, hp, _, _, _, _
  | .set .., _, _, hp, _, _, _, _ | .record .., _, _, hp, _, _, _, _
  | .call .., _, _, hp, _, _, _, _ => by cases hp

theorem toTerm_call {xfn : Cedar.Spec.ExtFun} {xs : List Cedar.Spec.Expr} {t : Term}
    (h : toTerm (.call xfn xs) = some t) :
    ∃ s, xfn = .decimal ∧ xs = [.lit (.string s)] ∧ t = .decimal s := by
  unfold toTerm at h
  split at h <;> simp_all

private theorem binary_ok {op : BinaryOp} {x y : Cedar.Spec.Expr} {w : Value}
    (h : Cedar.Spec.evaluate (.binaryApp op x y) req es = .ok w) :
    ∃ vx vy, Cedar.Spec.evaluate x req es = .ok vx ∧ Cedar.Spec.evaluate y req es = .ok vy ∧
      Cedar.Spec.apply₂ op vx vy es = .ok w := by
  simp only [Cedar.Spec.evaluate] at h
  cases hx : Cedar.Spec.evaluate x req es with
  | error e => rw [hx] at h; cases h
  | ok vx =>
    cases hy : Cedar.Spec.evaluate y req es with
    | error e => rw [hx, hy] at h; cases h
    | ok vy =>
      rw [hx, hy] at h
      exact ⟨vx, vy, rfl, rfl, h⟩

/-- The arithmetic operators, and the temporal operator each is. -/
def arithOf : BinaryOp → Option ArithOp
  | .add => some .add
  | .sub => some .sub
  | .mul => some .mul
  | _ => none

/-- A Cedar arithmetic operation that evaluates is of two `Long`s, and its result is the exact
one, within the `Long` range. -/
theorem apply₂_arith {op : BinaryOp} {aop : ArithOp} (hop : arithOf op = some aop)
    {vx vy v : Value} (h : Cedar.Spec.apply₂ op vx vy es = .ok v) :
    ∃ i j, vx = .prim (.int i) ∧ vy = .prim (.int j) ∧
      Int64.MIN ≤ aop.apply i.toInt j.toInt ∧ aop.apply i.toInt j.toInt ≤ Int64.MAX ∧
      v = .prim (.int (Int64.ofInt (aop.apply i.toInt j.toInt))) := by
  have hint : ∀ n : Int, Cedar.Spec.intOrErr (Int64.ofInt? n) = .ok v →
      Int64.MIN ≤ n ∧ n ≤ Int64.MAX ∧ v = .prim (.int (Int64.ofInt n)) := by
    intro n hn
    by_cases hr : Int64.MIN ≤ n ∧ n ≤ Int64.MAX
    · rw [Int64.ofInt?_some_iff.mp hr] at hn
      simp only [Cedar.Spec.intOrErr, Except.ok.injEq] at hn
      exact ⟨hr.1, hr.2, hn.symm⟩
    · have : n < Int64.MIN ∨ n > Int64.MAX := by omega
      rw [Int64.ofInt?_none_iff.mp this] at hn
      cases hn
  cases op <;> simp only [arithOf, reduceCtorEq, Option.some.injEq] at hop <;> subst hop <;>
    simp only [Cedar.Spec.apply₂] at h <;> split at h <;> (try cases h) <;>
    first
    | exact ⟨_, _, rfl, rfl, hint _ h⟩
    | simp_all

theorem readLong_in_range {f : Int → Option Int} {n : Int} (hlo : Int64.MIN ≤ n)
    (hhi : n ≤ Int64.MAX) : readLong f n = some (.num n) := by
  simp [readLong, hlo, hhi]

variable {ι : ImplChoices} {rate : TickRate} {σ : Trace} {vis : Nat → Prop} {v₀ : Valuation}
  {j : Nat}

private theorem denotes_arith {op : BinaryOp} {aop : ArithOp} (hop : arithOf op = some aop)
    {x y : Cedar.Spec.Expr} {tx ty : Term}
    (ihx : ∀ v, Cedar.Spec.evaluate x req es = .ok v →
      ∀ c, Denotes ι rate σ ev vis v₀ j tx c ↔ c = CVal.ofValue v)
    (ihy : ∀ v, Cedar.Spec.evaluate y req es = .ok v →
      ∀ c, Denotes ι rate σ ev vis v₀ j ty c ↔ c = CVal.ofValue v)
    {v : Value} (hv : Cedar.Spec.evaluate (.binaryApp op x y) req es = .ok v) :
    ∀ c, Denotes ι rate σ ev vis v₀ j (.arith aop tx ty) c ↔ c = CVal.ofValue v := by
  obtain ⟨vx, vy, hx, hy, ha⟩ := binary_ok hv
  obtain ⟨i, k, rfl, rfl, hlo, hhi, rfl⟩ := apply₂_arith hop ha
  intro c
  have hlo' := hlo
  have hhi' := hhi
  simp only [Int64.MIN, Int64.MAX] at hlo' hhi'
  simp only [Denotes, ihx _ hx, ihy _ hy, CVal.ofValue, CVal.num.injEq, ImplChoices.arithValue]
  simp [readLong_in_range hlo hhi,
    Int64.toInt_ofInt_of_le (by omega : -2 ^ 63 ≤ aop.apply i.toInt k.toInt) (by omega), eq_comm]

/-- **A translated term denotes what Cedar evaluates it to**, at a decision event that carries the
request's context, principal, and resource, with a store that reads entities as the event
supplies them (`StoreFits`), under every reading: a Cedar arithmetic operation that evaluates
does not overflow, and the temporal operation computes the same `Long`. -/
theorem denotes_toTerm (hc : ev.context = req.context) (hpr : ev.principal = some req.principal)
    (hrs : ev.resource = some req.resource) (hes : StoreFits es ev) :
    (x : Cedar.Spec.Expr) → (t : Term) → toTerm x = some t → TermFits req es x → (v : Value) →
      Cedar.Spec.evaluate x req es = .ok v →
      ∀ c, Denotes ι rate σ ev vis v₀ j t c ↔ c = CVal.ofValue v
  | .lit p, t, ht, _, v, hv, c => by
    simp only [Cedar.Spec.evaluate, Except.ok.injEq] at hv
    subst hv
    cases p <;> simp only [toTerm, Option.some.injEq] at ht <;> subst ht <;>
      simp [Denotes, Term.eval?, CVal.ofTVal]
  | .var .principal, t, ht, _, v, hv, c => by
    simp only [toTerm, Option.some.injEq] at ht
    simp only [Cedar.Spec.evaluate, Except.ok.injEq] at hv
    subst ht hv
    simp [Denotes, Term.eval?, Event.scopePath?, Event.scope, hpr, CVal.ofTVal]
  | .var .resource, t, ht, _, v, hv, c => by
    simp only [toTerm, Option.some.injEq] at ht
    simp only [Cedar.Spec.evaluate, Except.ok.injEq] at hv
    subst ht hv
    simp [Denotes, Term.eval?, Event.scopePath?, Event.scope, hrs, CVal.ofTVal]
  | .call xfn xs, t, ht, _, v, hv, c => by
    obtain ⟨s, rfl, rfl, rfl⟩ := toTerm_call ht
    simp [Cedar.Spec.evaluate, List.mapM₁, Cedar.Spec.call, Cedar.Spec.res] at hv
    cases hd : Cedar.Spec.Ext.Decimal.parse s with
    | none => simp [hd] at hv
    | some d =>
      simp only [hd, Except.ok.injEq] at hv
      subst hv
      simp [Denotes, Term.eval?, hd, CVal.ofTVal, CVal.ofValue]
      rfl
  | .getAttr x a, t, ht, hfit, v, hv, c => by
    cases hcx : ctxPath x with
    | some p =>
      simp only [toTerm, attrTerm, hcx, Option.some.injEq] at ht
      subst ht
      have hpath := valuePath_of_ctxPath (.getAttr x a) (p ++ [a]) (by simp [ctxPath, hcx]) hfit
        v hv
      simp [Denotes, Term.eval?, Event.contextPath?, hc,
        recordPath_eq_valuePath _ (by simp : p ++ [a] ≠ []), hpath, CVal.ofTVal]
    | none =>
      cases hsx : scopePath x with
      | none => simp [toTerm, attrTerm, hcx, hsx] at ht
      | some rp =>
        obtain ⟨r, p⟩ := rp
        simp only [toTerm, attrTerm, hcx, hsx,
          Option.some.injEq] at ht
        subst ht
        obtain ⟨uid, huid, hpath⟩ := entityAttr_of_scopePath hpr hrs hes (.getAttr x a) r
          (p ++ [a]) (by simp [scopePath, hsx]) (by simp) hfit v hv
        obtain ⟨b, q, hq⟩ := List.exists_cons_of_ne_nil (by simp : p ++ [a] ≠ [])
        rw [hq] at hpath ⊢
        simp [Denotes, Term.eval?, Event.scopePath?, huid, hpath, CVal.ofTVal]
  | .binaryApp .add x y, t, ht, hfit, v, hv, c
  | .binaryApp .sub x y, t, ht, hfit, v, hv, c
  | .binaryApp .mul x y, t, ht, hfit, v, hv, c => by
    simp only [toTerm, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at ht
    obtain ⟨tx, htx, ty, hty, rfl⟩ := ht
    simp only [TermFits] at hfit
    exact denotes_arith rfl (fun v hv => denotes_toTerm hc hpr hrs hes x tx htx hfit.1 v hv)
      (fun v hv => denotes_toTerm hc hpr hrs hes y ty hty hfit.2 v hv) hv c
  | .var .action, _, ht, _, _, _, _ | .var .context, _, ht, _, _, _, _
  | .ite .., _, ht, _, _, _, _ | .and .., _, ht, _, _, _, _ | .or .., _, ht, _, _, _, _
  | .unaryApp .., _, ht, _, _, _, _ | .binaryApp .eq .., _, ht, _, _, _, _
  | .binaryApp .mem .., _, ht, _, _, _, _ | .binaryApp .hasTag .., _, ht, _, _, _, _
  | .binaryApp .getTag .., _, ht, _, _, _, _ | .binaryApp .less .., _, ht, _, _, _, _
  | .binaryApp .lessEq .., _, ht, _, _, _, _ | .binaryApp .contains .., _, ht, _, _, _, _
  | .binaryApp .containsAll .., _, ht, _, _, _, _ | .binaryApp .containsAny .., _, ht, _, _, _, _
  | .hasAttr .., _, ht, _, _, _, _ | .extHasAttr .., _, ht, _, _, _, _ | .set .., _, ht, _, _, _, _
  | .record .., _, ht, _, _, _, _ => by simp [toTerm] at ht

end

theorem as_bool_ok {r : Cedar.Spec.Result Value} {b : Bool} :
    r.as Bool = .ok b ↔ r = .ok (.prim (.bool b)) := by
  cases r with
  | error e => simp [Cedar.Spec.Result.as]
  | ok v =>
    cases v with
    | prim p =>
      cases p <;> simp [Cedar.Spec.Result.as, Coe.coe, Cedar.Spec.Value.asBool]
    | _ => simp [Cedar.Spec.Result.as, Coe.coe, Cedar.Spec.Value.asBool]

/-! ## One expression -/

private theorem as_bool_of_pure {r : Cedar.Spec.Result Value} {b : Bool}
    (h : (do let a ← r.as Bool; pure (Value.prim (.bool a)) : Cedar.Spec.Result Value) =
      .ok (.prim (.bool b))) : r.as Bool = .ok b := by
  cases hr : r.as Bool with
  | error e => rw [hr] at h; cases h
  | ok a =>
    rw [hr] at h
    simp only [Except.bind_ok, pure, Except.pure, Except.ok.injEq, Value.prim.injEq,
      Prim.bool.injEq] at h
    rw [h]

section

variable {ι : ImplChoices} {rate : TickRate} {σ : Trace} {vis : Nat → Prop} {v₀ : Valuation}
  {j : Nat} {req : Request} {es : Entities} {ev : Event}

/-- A comparison of two translated terms holds exactly when their values compare. -/
theorem sat_cmp_toTerm (hc : ev.context = req.context) (hpr : ev.principal = some req.principal)
    (hrs : ev.resource = some req.resource) (hes : StoreFits es ev) {op : CmpOp}
    {x y : Cedar.Spec.Expr} {tx ty : Term} (htx : toTerm x = some tx) (hty : toTerm y = some ty)
    (hfx : TermFits req es x) (hfy : TermFits req es y) {vx vy : Value}
    (hx : Cedar.Spec.evaluate x req es = .ok vx) (hy : Cedar.Spec.evaluate y req es = .ok vy) :
    Sat ι rate σ ev vis v₀ j (.cmp op tx ty) ↔ op.Holds (CVal.ofValue vx) (CVal.ofValue vy) := by
  simp only [Sat, denotes_toTerm hc hpr hrs hes x tx htx hfx vx hx,
    denotes_toTerm hc hpr hrs hes y ty hty hfy vy hy]
  simp

/-- **A Cedar expression and its translation agree**: where Cedar evaluates an expression that
fits the temporal sub-language to a `Bool`, its translation holds at a decision event carrying
the request's context, principal, and resource exactly when the `Bool` is `true`, under every
reading, over every trace, at every timepoint. -/
theorem sat_toTemporal_iff (hc : ev.context = req.context)
    (hpr : ev.principal = some req.principal) (hrs : ev.resource = some req.resource)
    (hes : StoreFits es ev) :
    (e : Cedar.Spec.Expr) → (φ : Formula) → toTemporal e = some φ → Fits req es e → (b : Bool) →
      Cedar.Spec.evaluate e req es = .ok (.prim (.bool b)) →
      (Sat ι rate σ ev vis v₀ j φ ↔ b = true)
  | .binaryApp .eq x y, φ, hφ, hfit, b, he => by
    simp only [toTemporal, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hφ
    obtain ⟨tx, htx, ty, hty, rfl⟩ := hφ
    obtain ⟨vx, vy, hx, hy, ha⟩ := binary_ok he
    simp only [Cedar.Spec.apply₂, Except.ok.injEq, Value.prim.injEq, Prim.bool.injEq] at ha
    rw [sat_cmp_toTerm hc hpr hrs hes htx hty hfit.1 hfit.2 hx hy, ← ha]
    simp [CmpOp.Holds, ofValue_inj]
  | .binaryApp .less x y, φ, hφ, hfit, b, he => by
    simp only [toTemporal, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hφ
    obtain ⟨tx, htx, ty, hty, rfl⟩ := hφ
    obtain ⟨vx, vy, hx, hy, ha⟩ := binary_ok he
    obtain ⟨⟨i, rfl⟩, k, rfl⟩ := hfit.2.2 vx vy hx hy
    simp only [Cedar.Spec.apply₂, Except.ok.injEq, Value.prim.injEq, Prim.bool.injEq] at ha
    rw [sat_cmp_toTerm hc hpr hrs hes htx hty hfit.1 hfit.2.1 hx hy, ← ha]
    simp [CmpOp.Holds, CVal.ofValue, Int64.lt_iff_toInt_lt]
  | .binaryApp .lessEq x y, φ, hφ, hfit, b, he => by
    simp only [toTemporal, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hφ
    obtain ⟨tx, htx, ty, hty, rfl⟩ := hφ
    obtain ⟨vx, vy, hx, hy, ha⟩ := binary_ok he
    obtain ⟨⟨i, rfl⟩, k, rfl⟩ := hfit.2.2 vx vy hx hy
    simp only [Cedar.Spec.apply₂, Except.ok.injEq, Value.prim.injEq, Prim.bool.injEq] at ha
    rw [sat_cmp_toTerm hc hpr hrs hes htx hty hfit.1 hfit.2.1 hx hy, ← ha]
    simp [CmpOp.Holds, CVal.ofValue, Int64.le_iff_toInt_le]
  | .and x y, φ, hφ, hfit, b, he => by
    simp only [toTemporal, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hφ
    obtain ⟨φx, hφx, φy, hφy, rfl⟩ := hφ
    simp only [Cedar.Spec.evaluate] at he
    cases hx : (Cedar.Spec.evaluate x req es).as Bool with
    | error e => rw [hx] at he; cases he
    | ok bx =>
      rw [hx] at he
      have ihx := sat_toTemporal_iff hc hpr hrs hes x φx hφx hfit.1 bx (as_bool_ok.mp hx)
      simp only [Sat]
      cases bx with
      | false =>
        simp only [Bool.not_false, ↓reduceIte, Except.bind_ok, Except.ok.injEq,
          Value.prim.injEq, Prim.bool.injEq] at he
        simp only [Bool.false_eq_true, iff_false] at ihx
        subst he
        simp [ihx]
      | true =>
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, Except.bind_ok] at he
        have ihy := sat_toTemporal_iff hc hpr hrs hes y φy hφy hfit.2 b
          (as_bool_ok.mp (as_bool_of_pure he))
        simp only [iff_true] at ihx
        simp [ihx, ihy]
  | .or x y, φ, hφ, hfit, b, he => by
    simp only [toTemporal, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hφ
    obtain ⟨φx, hφx, φy, hφy, rfl⟩ := hφ
    simp only [Cedar.Spec.evaluate] at he
    cases hx : (Cedar.Spec.evaluate x req es).as Bool with
    | error e => rw [hx] at he; cases he
    | ok bx =>
      rw [hx] at he
      have ihx := sat_toTemporal_iff hc hpr hrs hes x φx hφx hfit.1 bx (as_bool_ok.mp hx)
      simp only [Sat]
      cases bx with
      | true =>
        simp only [↓reduceIte, Except.bind_ok, Except.ok.injEq, Value.prim.injEq,
          Prim.bool.injEq] at he
        simp only [iff_true] at ihx
        subst he
        simp [ihx]
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte, Except.bind_ok] at he
        have ihy := sat_toTemporal_iff hc hpr hrs hes y φy hφy hfit.2 b
          (as_bool_ok.mp (as_bool_of_pure he))
        simp only [Bool.false_eq_true, iff_false] at ihx
        simp [ihx, ihy]
  | .unaryApp .not x, φ, hφ, hfit, b, he => by
    simp only [toTemporal, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hφ
    obtain ⟨φx, hφx, rfl⟩ := hφ
    simp only [Cedar.Spec.evaluate] at he
    cases hx : Cedar.Spec.evaluate x req es with
    | error e => rw [hx] at he; cases he
    | ok vx =>
      rw [hx] at he
      simp only [Except.bind_ok] at he
      cases vx with
      | prim p =>
        cases p with
        | bool bx =>
          simp only [Cedar.Spec.apply₁, Except.ok.injEq, Value.prim.injEq,
            Prim.bool.injEq] at he
          have ihx := sat_toTemporal_iff hc hpr hrs hes x φx hφx hfit bx hx
          simp only [Sat, ihx, ← he]
          cases bx <;> simp
        | _ => simp [Cedar.Spec.apply₁] at he
      | _ => simp [Cedar.Spec.apply₁] at he
  | .lit _, _, hφ, _, _, _ | .var _, _, hφ, _, _, _ | .ite .., _, hφ, _, _, _
  | .unaryApp .neg _, _, hφ, _, _, _ | .unaryApp .isEmpty _, _, hφ, _, _, _
  | .unaryApp (.like _) _, _, hφ, _, _, _ | .unaryApp (.is _) _, _, hφ, _, _, _
  | .binaryApp .mem .., _, hφ, _, _, _ | .binaryApp .hasTag .., _, hφ, _, _, _
  | .binaryApp .getTag .., _, hφ, _, _, _ | .binaryApp .add .., _, hφ, _, _, _
  | .binaryApp .sub .., _, hφ, _, _, _ | .binaryApp .mul .., _, hφ, _, _, _
  | .binaryApp .contains .., _, hφ, _, _, _ | .binaryApp .containsAll .., _, hφ, _, _, _
  | .binaryApp .containsAny .., _, hφ, _, _, _ | .getAttr .., _, hφ, _, _, _
  | .hasAttr .., _, hφ, _, _, _ | .extHasAttr .., _, hφ, _, _, _ | .set .., _, hφ, _, _, _
  | .record .., _, hφ, _, _, _ | .call .., _, hφ, _, _, _ => by
    simp [toTemporal] at hφ

end

/-! ## Predicate arguments

A predicate `A::k{ f: t, … }` holds at a timepoint whose event is of action `A` and kind `k`
and whose logged record holds, at each field `f`, the value its term `t` resolves to at the
decision event (`Term.Matches`). A translated term in that position resolves to what Cedar
evaluates the expression to, so the match is Cedar's `==` (`matches_toTerm`), and a predicate
whose arguments are translations means: the event logged, at each field, the value Cedar
evaluates the argument's expression to at the current request (`sat_pred_toArgs_iff`). An
arithmetic term never matches (it resolves to no value), and typing excludes it (`Term.Simple`).
-/

/-- Cedar expressions as predicate arguments. -/
def toArgs (xs : List (Path × Cedar.Spec.Expr)) : Option (List (Path × Term)) :=
  xs.mapM fun fx => (toTerm fx.2).map fun t => (fx.1, t)

section

variable {req : Request} {es : Entities} {ev : Event} {v₀ : Valuation}

/-- A simple translated term resolves to what Cedar evaluates its expression to. -/
theorem eval_toTerm_simple (hc : ev.context = req.context)
    (hpr : ev.principal = some req.principal) (hrs : ev.resource = some req.resource)
    (hes : StoreFits es ev) {x : Cedar.Spec.Expr} {t : Term} (ht : toTerm x = some t)
    (hs : t.Simple) (hfit : TermFits req es x) {v : Value}
    (hx : Cedar.Spec.evaluate x req es = .ok v) :
    t.eval? ev v₀ = some (.val v) := by
  have hd := (denotes_toTerm (ι := ImplChoices.widen) (rate := TickRate.seconds) (σ := [])
    (vis := fun _ => True) (v₀ := v₀) (j := 0) hc hpr hrs hes x t ht hfit v hx
    (CVal.ofValue v)).mpr rfl
  have hw : ∃ w, t.eval? ev v₀ = some w ∧ CVal.ofValue v = CVal.ofTVal w := by
    cases t with
    | agg _ => exact absurd hs (by simp [Term.Simple])
    | arith _ _ _ => exact absurd hs (by simp [Term.Simple])
    | _ => simpa [Denotes] using hd
  obtain ⟨w, hw, hcw⟩ := hw
  cases w with
  | val v' =>
    simp only [CVal.ofTVal] at hcw
    rw [hw, ofValue_inj.mp hcw]
  | tp k =>
    exfalso
    revert hcw
    simp only [CVal.ofTVal, CVal.ofValue]
    split <;> simp

/-- **A translated predicate argument matches a logged value exactly when Cedar's `==` holds**
between the expression, at the current request, and the value. -/
theorem matches_toTerm (hc : ev.context = req.context)
    (hpr : ev.principal = some req.principal) (hrs : ev.resource = some req.resource)
    (hes : StoreFits es ev) {x : Cedar.Spec.Expr} {t : Term} (ht : toTerm x = some t)
    (hs : t.Simple) (hfit : TermFits req es x) {v : Value}
    (hx : Cedar.Spec.evaluate x req es = .ok v) (w : Value) :
    t.Matches ev v₀ w ↔ Cedar.Spec.apply₂ .eq v w es = .ok (.prim (.bool true)) := by
  have he := eval_toTerm_simple (v₀ := v₀) hc hpr hrs hes ht hs hfit hx
  have hnw : t ≠ .wildcard := by
    rintro rfl
    simp [Term.eval?] at he
  have hm : t.Matches ev v₀ w ↔ v = w := by
    unfold Term.Matches
    split
    · exact absurd rfl hnw
    · rw [he]
      simp
  rw [hm]
  simp [Cedar.Spec.apply₂]

theorem argsMatch_toArgs (hc : ev.context = req.context)
    (hpr : ev.principal = some req.principal) (hrs : ev.resource = some req.resource)
    (hes : StoreFits es ev) (e' : Event) :
    (xs : List (Path × Cedar.Spec.Expr)) → (args : List (Path × Term)) → toArgs xs = some args →
      (∀ fa ∈ args, fa.2.Simple) → (∀ fx ∈ xs, TermFits req es fx.2) →
      (∀ fx ∈ xs, ∃ v, Cedar.Spec.evaluate fx.2 req es = .ok v) →
      (ArgsMatch ev v₀ e' args ↔ ∀ fx ∈ xs, ∃ w, recordPath? e'.logged fx.1 = some w ∧
        Cedar.Spec.evaluate fx.2 req es = .ok w)
  | [], args, h, _, _, _ => by
    simp only [toArgs, List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    simp [ArgsMatch]
  | (f, x) :: xs, args, h, hs, hfit, hev => by
    simp only [toArgs, List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.map_eq_some_iff, Option.pure_def, Option.some.injEq] at h
    obtain ⟨_, ⟨t, ht, rfl⟩, rest, hrest, rfl⟩ := h
    have ih := argsMatch_toArgs hc hpr hrs hes e' xs rest hrest
      (fun fa hfa => hs fa (List.mem_cons_of_mem _ hfa))
      (fun fx hfx => hfit fx (List.mem_cons_of_mem _ hfx))
      (fun fx hfx => hev fx (List.mem_cons_of_mem _ hfx))
    unfold ArgsMatch at ih ⊢
    rw [List.forall_mem_cons, List.forall_mem_cons, ih]
    obtain ⟨v, hv⟩ := hev (f, x) (List.mem_cons_self ..)
    have hm := matches_toTerm (v₀ := v₀) hc hpr hrs hes ht (hs (f, t) (List.mem_cons_self ..))
      (hfit (f, x) (List.mem_cons_self ..)) hv
    refine and_congr_left fun _ => exists_congr fun w => and_congr_right fun _ => ?_
    rw [hm, hv]
    simp only [Cedar.Spec.apply₂, Except.ok.injEq, Value.prim.injEq, Prim.bool.injEq,
      beq_iff_eq]

/-- **A predicate whose arguments are Cedar expressions** holds at a timepoint exactly when its
event is of the predicate's action and kind and logged, at each argument's field, the value Cedar
evaluates the argument's expression to at the current request, under every reading, over every
trace. Under a temporal operator, this is the predicate's meaning at each timepoint the operator
reaches. -/
theorem sat_pred_toArgs_iff {ι : ImplChoices} {rate : TickRate} {σ : Trace} {vis : Nat → Prop}
    {j : Nat} (hc : ev.context = req.context) (hpr : ev.principal = some req.principal)
    (hrs : ev.resource = some req.resource) (hes : StoreFits es ev) {a : EntityUID} {k : String}
    {xs : List (Path × Cedar.Spec.Expr)} {args : List (Path × Term)} (hargs : toArgs xs = some args)
    (hs : ∀ fa ∈ args, fa.2.Simple) (hfit : ∀ fx ∈ xs, TermFits req es fx.2)
    (hev : ∀ fx ∈ xs, ∃ v, Cedar.Spec.evaluate fx.2 req es = .ok v) :
    Sat ι rate σ ev vis v₀ j (.pred a k args) ↔
      ∃ p, σ[j]? = some p ∧ p.event.action = a ∧ p.event.kind = k ∧
        ∀ fx ∈ xs, ∃ w, recordPath? p.event.logged fx.1 = some w ∧
          Cedar.Spec.evaluate fx.2 req es = .ok w := by
  simp only [Sat]
  refine exists_congr fun p => and_congr_right fun _ => and_congr_right fun _ =>
    and_congr_right fun _ => ?_
  exact argsMatch_toArgs hc hpr hrs hes p.event xs args hargs hs hfit hev

end

/-! ## Where the two differ

The agreement theorems need Cedar's arithmetic not to overflow. The hypothesis is needed. -/

section

variable {ι : ImplChoices} {rate : TickRate} {σ : Trace} {vis : Nat → Prop} {v₀ : Valuation}
  {j : Nat} {req : Request} {es : Entities} {ev : Event}

/-- **An overflow is where the two differ, under every reading.** Where Cedar evaluates `x` and
`y` to `Long`s whose sum is out of range, Cedar's `x + y == x + y` errs, so a rule with the
condition is skipped and reports the error. Its translation holds under a reading that reads the
sum (`widen`, `clamp`): a `when` rule with it is satisfied. It fails under a reading that reports
an error: an `unless` rule with it is satisfied. -/
theorem overflow_differs (hc : ev.context = req.context) (hpr : ev.principal = some req.principal)
    (hrs : ev.resource = some req.resource) (hes : StoreFits es ev) {x y : Cedar.Spec.Expr}
    {tx ty : Term} (htx : toTerm x = some tx) (hty : toTerm y = some ty)
    (hfx : TermFits req es x) (hfy : TermFits req es y) {i k : Int64}
    (hx : Cedar.Spec.evaluate x req es = .ok (.prim (.int i)))
    (hy : Cedar.Spec.evaluate y req es = .ok (.prim (.int k)))
    (hout : i.toInt + k.toInt < Int64.MIN ∨ i.toInt + k.toInt > Int64.MAX) :
    toTemporal (.binaryApp .eq (.binaryApp .add x y) (.binaryApp .add x y)) =
        some (.cmp .eq (.arith .add tx ty) (.arith .add tx ty)) ∧
      Cedar.Spec.evaluate (.binaryApp .eq (.binaryApp .add x y) (.binaryApp .add x y)) req es =
        .error .arithBoundsError ∧
      ((ι.arithOutOfRange (i.toInt + k.toInt)).isSome = true →
        Sat ι rate σ ev vis v₀ j (.cmp .eq (.arith .add tx ty) (.arith .add tx ty))) ∧
      (ι.arithOutOfRange (i.toInt + k.toInt) = none →
        ¬ Sat ι rate σ ev vis v₀ j (.cmp .eq (.arith .add tx ty) (.arith .add tx ty))) := by
  have hdx := denotes_toTerm (ι := ι) (rate := rate) (σ := σ) (vis := vis) (v₀ := v₀) (j := j)
    hc hpr hrs hes x tx htx hfx _ hx
  have hdy := denotes_toTerm (ι := ι) (rate := rate) (σ := σ) (vis := vis) (v₀ := v₀) (j := j)
    hc hpr hrs hes y ty hty hfy _ hy
  have hlong : ¬ (Int64.MIN ≤ i.toInt + k.toInt ∧ i.toInt + k.toInt ≤ Int64.MAX) := by omega
  -- The compound denotes the reading of the out-of-range sum, and nothing else.
  have hden : ∀ c, Denotes ι rate σ ev vis v₀ j (.arith .add tx ty) c ↔
      (ι.arithOutOfRange (i.toInt + k.toInt)).map CVal.num = some c := by
    intro c
    simp only [Denotes, hdx, hdy, CVal.ofValue, CVal.num.injEq, ImplChoices.arithValue,
      readLong, ArithOp.apply]
    simp [hlong]
  refine ⟨by simp [toTemporal, toTerm, htx, hty], ?_, fun hs => ?_, fun hn hs => ?_⟩
  · simp [Cedar.Spec.evaluate, hx, hy, Cedar.Spec.apply₂, Int64.add?,
      Int64.ofInt?_none_iff.mp hout, Cedar.Spec.intOrErr]
  · obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp hs
    exact ⟨.num m, .num m, (hden _).mpr (by simp [hm]), (hden _).mpr (by simp [hm]), rfl⟩
  · obtain ⟨a, b, ha, -, -⟩ := hs
    rw [hden, hn] at ha
    cases ha

end

/-! ## The translation as a leaf -/

theorem attrTerm_shape {x : Cedar.Spec.Expr} {a : Attr} {t : Term}
    (h : toTerm (.getAttr x a) = some t) : (∃ p, t = .context p) ∨ ∃ r p, t = .scope r p := by
  simp only [toTerm, attrTerm] at h
  split at h
  · simp only [Option.some.injEq] at h
    exact .inl ⟨_, h.symm⟩
  · simp only [Option.some.injEq] at h
    exact .inr ⟨_, _, h.symm⟩
  · cases h

theorem toTerm_injectPins {S : EventSchema} :
    (x : Cedar.Spec.Expr) → (t : Term) → toTerm x = some t → t.injectPins S = t
  | .lit p, t, h => by
    cases p <;> simp only [toTerm, Option.some.injEq] at h <;> subst h <;> rfl
  | .var v, t, h => by
    cases v <;> simp only [toTerm, Option.some.injEq, reduceCtorEq] at h <;> subst h <;> rfl
  | .getAttr x a, t, h => by
    obtain ⟨p, rfl⟩ | ⟨r, p, rfl⟩ := attrTerm_shape h <;> rfl
  | .call _ _, t, h => by
    obtain ⟨s, -, -, rfl⟩ := toTerm_call h
    rfl
  | .binaryApp .add x y, t, h | .binaryApp .sub x y, t, h | .binaryApp .mul x y, t, h => by
    simp only [toTerm, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨tx, htx, ty, hty, rfl⟩ := h
    simp [Term.injectPins, toTerm_injectPins x tx htx, toTerm_injectPins y ty hty]
  | .ite .., _, h | .and .., _, h | .or .., _, h | .unaryApp .., _, h
  | .binaryApp .eq .., _, h | .binaryApp .mem .., _, h | .binaryApp .hasTag .., _, h
  | .binaryApp .getTag .., _, h | .binaryApp .less .., _, h | .binaryApp .lessEq .., _, h
  | .binaryApp .contains .., _, h | .binaryApp .containsAll .., _, h
  | .binaryApp .containsAny .., _, h | .hasAttr .., _, h | .extHasAttr .., _, h | .set .., _, h
  | .record .., _, h => by simp [toTerm] at h

/-- A translation names no event: pin injection leaves it as it is. -/
theorem toTemporal_injectPins {S : EventSchema} :
    (e : Cedar.Spec.Expr) → (φ : Formula) → toTemporal e = some φ → φ.injectPins S = φ
  | .binaryApp .eq x y, φ, h | .binaryApp .less x y, φ, h | .binaryApp .lessEq x y, φ, h => by
    simp only [toTemporal, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨tx, htx, ty, hty, rfl⟩ := h
    simp [Formula.injectPins, toTerm_injectPins x tx htx, toTerm_injectPins y ty hty]
  | .and x y, φ, h | .or x y, φ, h => by
    simp only [toTemporal, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨φx, hφx, φy, hφy, rfl⟩ := h
    simp [Formula.injectPins, toTemporal_injectPins (S := S) x φx hφx,
      toTemporal_injectPins (S := S) y φy hφy]
  | .unaryApp .not x, φ, h => by
    simp only [toTemporal, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨φx, hφx, rfl⟩ := h
    simp [Formula.injectPins, toTemporal_injectPins (S := S) x φx hφx]
  | .lit _, _, h | .var _, _, h | .ite .., _, h
  | .unaryApp .neg _, _, h | .unaryApp .isEmpty _, _, h
  | .unaryApp (.like _) _, _, h | .unaryApp (.is _) _, _, h
  | .binaryApp .mem .., _, h | .binaryApp .hasTag .., _, h
  | .binaryApp .getTag .., _, h | .binaryApp .add .., _, h
  | .binaryApp .sub .., _, h | .binaryApp .mul .., _, h
  | .binaryApp .contains .., _, h | .binaryApp .containsAll .., _, h
  | .binaryApp .containsAny .., _, h | .getAttr .., _, h
  | .hasAttr .., _, h | .extHasAttr .., _, h | .set .., _, h
  | .record .., _, h | .call .., _, h => by simp [toTemporal] at h

/-- **The translation's leaf value is the Cedar expression's value**, at a decision event, under
every reading, over every trace. -/
theorem leaves_toTemporal {ι : ImplChoices} {P : PolicySet} {ω : Provider.Providers}
    {σ : Trace} {n : Nat} {p : TimePoint} (hp : σ[n]? = some p) {pr rs : EntityUID}
    (hpr : p.event.principal = some pr) (hrs : p.event.resource = some rs)
    {e : Cedar.Spec.Expr} {φ : Formula} (hφ : toTemporal e = some φ)
    (hfit : Fits (p.event.request pr rs) (P.decisionEntities p.event) e) {b : Bool}
    (he : Cedar.Spec.evaluate e (p.event.request pr rs) (P.decisionEntities p.event) =
      .ok (.prim (.bool b))) :
    (P.leaves ι ω σ n p.event).temporal φ = b := by
  have hsat := sat_toTemporal_iff (ι := ι) (rate := P.tickRate) (σ := σ)
    (vis := P.schema.Visible σ p.event) (v₀ := Valuation.empty) (j := n) rfl hpr hrs
    (storeFits_decisionEntities P p.event) e φ hφ hfit b he
  have hinj := toTemporal_injectPins (S := P.schema) e φ hφ
  simp only [PolicySet.leaves]
  have : P.LeafHolds ι σ n φ ↔ b = true := by
    unfold PolicySet.LeafHolds
    rw [hinj]
    constructor
    · rintro ⟨p', hp', hs⟩
      rw [hp] at hp'
      cases hp'
      exact hsat.mp hs
    · intro hb
      exact ⟨p, hp, hsat.mpr hb⟩
  cases b <;> simp_all

/-! ## Where typing puts an expression -/

/-- Cedar's store reads every entity of a declared entity type as the event supplies it: the
entity store of a decision of a valid policy set (`storeReads_decisionEntities`), where only the
schema's actions take precedence, and no action is of a declared entity type. -/
def StoreReads (es : Entities) (ev : Event) (env : Cedar.Validation.TypeEnv) : Prop :=
  ∀ uid d, env.ets.contains uid.ty = true → ev.entities.find? uid = some d → es.find? uid = some d

theorem storeReads_decisionEntities {P : PolicySet} (hv : P.Valid) {env : Cedar.Validation.TypeEnv}
    (henv : env ∈ P.actionSchema.environments) (ev : Event) :
    StoreReads (P.decisionEntities ev) ev env := by
  intro uid d hets hd
  have hwf := augmented_wf hv henv
  have hA := environments_schema henv
  have hnact : P.actionSchema.acts.find? uid = none := by
    have h3 := hwf.2.1.2.2.1 uid
    rw [augmented_contains henv, augmented_ets] at h3
    cases hf : P.actionSchema.acts.find? uid with
    | none => rfl
    | some entry =>
      exfalso
      have hc : env.acts.contains uid = true := by
        simp [hA.2, Cedar.Validation.ActionSchema.contains, hf]
      exact h3 hc hets
  rw [decisionEntities_find?, hnact, hd]
  rfl

/-- A Cedar result is a `Bool`, or the error of an arithmetic overflow. -/
def BoolOrOverflow (r : Cedar.Spec.Result Value) : Prop :=
  (∃ b, r = .ok (.prim (.bool b))) ∨ r = .error .arithBoundsError

section

variable {C : TypingCtx} {req : Request} {es : Entities} {ev : Event}

/-- A context path that resolves through records is one Cedar evaluates, to the same value, and
runs through records. -/
theorem evaluate_ctxPath :
    (x : Cedar.Spec.Expr) → (p : Path) → ctxPath x = some p → (u : Value) →
      valuePath? (.record req.context) p = some u →
      Cedar.Spec.evaluate x req es = .ok u ∧ TermFits req es x
  | .var .context, p, hp, u, hu => by
    simp only [ctxPath, Option.some.injEq] at hp
    subst hp
    simp only [valuePath?, Option.some.injEq] at hu
    subst hu
    exact ⟨by simp [Cedar.Spec.evaluate], by simp [TermFits]⟩
  | .getAttr x a, p, hp, u, hu => by
    simp only [ctxPath, Option.map_eq_some_iff] at hp
    obtain ⟨p', hp', rfl⟩ := hp
    rw [valuePath_append, Option.bind_eq_some_iff] at hu
    obtain ⟨u', hu', hu⟩ := hu
    cases u' with
    | record r =>
      simp only [valuePath?] at hu
      cases hf : r.find? a with
      | none => rw [hf] at hu; cases hu
      | some w =>
        rw [hf] at hu
        simp only [Option.bind_some, Option.some.injEq] at hu
        subst hu
        obtain ⟨hx, hfx⟩ := evaluate_ctxPath x p' hp' _ hu'
        refine ⟨?_, ?_⟩
        · rw [evaluate_getAttr_record hx]
          simp [Cedar.Data.Map.findOrErr, hf]
        · simp only [TermFits]
          refine ⟨hfx, .inr (.inr fun v hv => ⟨r, ?_⟩)⟩
          rw [hx] at hv
          cases hv
          rfl
    | _ => simp [valuePath?] at hu
  | .lit _, _, hp, _, _ | .var .principal, _, hp, _, _ | .var .action, _, hp, _, _
  | .var .resource, _, hp, _, _ | .ite .., _, hp, _, _ | .and .., _, hp, _, _
  | .or .., _, hp, _, _ | .unaryApp .., _, hp, _, _ | .binaryApp .., _, hp, _, _
  | .hasAttr .., _, hp, _, _ | .extHasAttr .., _, hp, _, _ | .set .., _, hp, _, _
  | .record .., _, hp, _, _ | .call .., _, hp, _, _ => by cases hp

/-- A scope path that resolves in the event's entity data is one Cedar evaluates, to the same
value, and runs through records, when Cedar's store reads the entity as the event supplies it. -/
theorem evaluate_scopePath (hpr : ev.principal = some req.principal)
    (hrs : ev.resource = some req.resource) {uid : EntityUID}
    (hsr : ∀ d, ev.entities.find? uid = some d → es.find? uid = some d) :
    (x : Cedar.Spec.Expr) → (r : ScopeRoot) → (p : Path) → scopePath x = some (r, p) → p ≠ [] →
      ev.scope r = some uid → (u : Value) → ev.entityAttr? uid p = some u →
      Cedar.Spec.evaluate x req es = .ok u ∧ TermFits req es x
  | .getAttr x a, r, p, hp, _, huid, u, hu => by
    simp only [scopePath, Option.map_eq_some_iff, Prod.exists] at hp
    obtain ⟨r', p', hp', hrp⟩ := hp
    simp only [Prod.mk.injEq] at hrp
    obtain ⟨rfl, rfl⟩ := hrp
    by_cases hnil : p' = []
    · subst hnil
      simp only [List.nil_append, Event.entityAttr?, valuePath?, Option.bind_eq_some_iff,
        Option.some.injEq] at hu
      obtain ⟨w, ⟨d, hd, hw⟩, rfl⟩ := hu
      have hes := hsr d hd
      have hvar : x = .var .principal ∧ req.principal = uid ∨
          x = .var .resource ∧ req.resource = uid := by
        rcases scopePath_nil hp' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · simp only [Event.scope, hpr, Option.some.injEq] at huid
          exact .inl ⟨rfl, huid⟩
        · simp only [Event.scope, hrs, Option.some.injEq] at huid
          exact .inr ⟨rfl, huid⟩
      refine ⟨?_, ?_⟩
      · rcases hvar with ⟨rfl, hu⟩ | ⟨rfl, hu⟩ <;>
          simp [Cedar.Spec.evaluate, Cedar.Spec.getAttr, Cedar.Spec.attrsOf, Entities.attrs,
            Cedar.Data.Map.findOrErr, hu, hes, hw]
      · simp only [TermFits]
        rcases hvar with ⟨rfl, -⟩ | ⟨rfl, -⟩
        · exact ⟨trivial, .inl rfl⟩
        · exact ⟨trivial, .inr (.inl rfl)⟩
    · obtain ⟨b, q, rfl⟩ := List.exists_cons_of_ne_nil hnil
      simp only [List.cons_append, Event.entityAttr?] at hu
      rw [Option.bind_congr (fun w _ => valuePath_append w q [a]), ← Option.bind_assoc,
        Option.bind_eq_some_iff] at hu
      obtain ⟨u', hu', hu⟩ := hu
      cases u' with
      | record rec =>
        simp only [valuePath?] at hu
        cases hw : rec.find? a with
        | none => rw [hw] at hu; cases hu
        | some w =>
          rw [hw] at hu
          simp only [Option.bind_some, Option.some.injEq] at hu
          subst hu
          obtain ⟨hx, hfx⟩ := evaluate_scopePath hpr hrs hsr x r' (b :: q) hp' hnil huid _
            (by simpa [Event.entityAttr?] using hu')
          refine ⟨?_, ?_⟩
          · rw [evaluate_getAttr_record hx]
            simp [Cedar.Data.Map.findOrErr, hw]
          · simp only [TermFits]
            refine ⟨hfx, .inr (.inr fun v hv => ⟨rec, ?_⟩)⟩
            rw [hx] at hv
            cases hv
            rfl
      | _ => simp [valuePath?] at hu
  | .var .principal, _, _, hp, hne, _, _, _ | .var .resource, _, _, hp, hne, _, _, _ => by
    simp only [scopePath, Option.some.injEq, Prod.mk.injEq] at hp
    exact absurd hp.2.symm hne
  | .lit _, _, _, hp, _, _, _, _ | .var .action, _, _, hp, _, _, _, _
  | .var .context, _, _, hp, _, _, _, _ | .ite .., _, _, hp, _, _, _, _
  | .and .., _, _, hp, _, _, _, _ | .or .., _, _, hp, _, _, _, _
  | .unaryApp .., _, _, hp, _, _, _, _ | .binaryApp .., _, _, hp, _, _, _, _
  | .hasAttr .., _, _, hp, _, _, _, _ | .extHasAttr .., _, _, hp, _, _, _, _
  | .set .., _, _, hp, _, _, _, _ | .record .., _, _, hp, _, _, _, _
  | .call .., _, _, hp, _, _, _, _ => by cases hp

theorem int_of_hasSort {u : Value} (h : (TVal.val u).HasSort C.env (.cedar .int)) :
    ∃ i, u = .prim (.int i) := by
  simp only [TVal.HasSort] at h
  cases h
  exact ⟨_, rfl⟩

/-- A typed path of a scope entity reads an entity type that declares attributes. -/
theorem scopeAttr_typed {C : TypingCtx} {Γ : Bindings} {t : Term} {τ : TType} {r : ScopeRoot}
    {q : Path} (hty : Term.Typed C Γ t τ) (ht : t = .scope r q)
    (hne : q ≠ []) : ∃ rty, C.env.ets.attrs? (C.scopeType r) = some rty := by
  cases hty with
  | scopeRoot => simp only [Term.scope.injEq] at ht; exact absurd ht.2.symm hne
  | scopeAttr _ h _ =>
    simp only [Term.scope.injEq] at ht
    obtain ⟨rfl, rfl⟩ := ht
    unfold TypingCtx.scopeAttrType? at h
    split at h
    · exact ⟨_, by assumption⟩
    · cases h
  | _ => cases ht

/-- A typed atomic term resolves, at an instance of the typing environment whose facts hold and
that supplies the scope entities the term reads. -/
private theorem resolves (he : ev.InstanceOf C.env) (hf : ∀ g ∈ C.facts, g.Holds ev)
    {t : Term} {τ : TType} (hty : Term.Typed C [] t τ) (hat : t.Atomic) (hfv : t.fv = [])
    (hsup : ∀ r ∈ t.scopeReads, ev.Supplies C.env r) :
    ∃ w, t.eval? ev Valuation.empty = some w ∧ w.HasSort C.env τ :=
  term_resolves (v := Valuation.empty) hty hat he hsup hf (by simp [hfv])

/-- **A typed translated term evaluates**, to a value of its type, or overflows, at a decision
event that is an instance of the typing environment, carries the request's context, principal,
and resource, supplies the scope entities the term reads, and whose facts hold, with a store that
reads declared entities as the event supplies them; and its attribute accesses run through
records. Typing excludes every error of Cedar's but an arithmetic overflow. -/
theorem evaluate_toTerm (hc : ev.context = req.context) (hpr : ev.principal = some req.principal)
    (hrs : ev.resource = some req.resource) (he : ev.InstanceOf C.env)
    (hf : ∀ g ∈ C.facts, g.Holds ev) (hst : StoreReads es ev C.env) :
    (x : Cedar.Spec.Expr) → (t : Term) → (τ : TType) → toTerm x = some t →
      Term.Typed C [] t τ → (∀ r ∈ t.scopeReads, ev.Supplies C.env r) →
      TermFits req es x ∧
        ((∃ u, Cedar.Spec.evaluate x req es = .ok u ∧ (TVal.val u).HasSort C.env τ) ∨
          Cedar.Spec.evaluate x req es = .error .arithBoundsError)
  | .lit p, t, τ, ht, hty, hsup => by
    cases p <;> simp only [toTerm, Option.some.injEq] at ht <;> subst ht <;>
      obtain ⟨w, hw, hws⟩ := resolves he hf hty trivial rfl hsup <;>
      simp only [Term.eval?, Option.some.injEq] at hw <;> subst hw <;>
      exact ⟨by simp [TermFits], .inl ⟨_, by simp [Cedar.Spec.evaluate], hws⟩⟩
  | .var .principal, t, τ, ht, hty, hsup => by
    simp only [toTerm, Option.some.injEq] at ht
    subst ht
    obtain ⟨w, hw, hws⟩ := resolves he hf hty trivial rfl hsup
    simp only [Term.eval?, Event.scopePath?, Event.scope, hpr, Option.map_some,
      Option.some.injEq] at hw
    subst hw
    exact ⟨by simp [TermFits], .inl ⟨_, by simp [Cedar.Spec.evaluate], hws⟩⟩
  | .var .resource, t, τ, ht, hty, hsup => by
    simp only [toTerm, Option.some.injEq] at ht
    subst ht
    obtain ⟨w, hw, hws⟩ := resolves he hf hty trivial rfl hsup
    simp only [Term.eval?, Event.scopePath?, Event.scope, hrs, Option.map_some,
      Option.some.injEq] at hw
    subst hw
    exact ⟨by simp [TermFits], .inl ⟨_, by simp [Cedar.Spec.evaluate], hws⟩⟩
  | .call xfn xs, t, τ, ht, hty, hsup => by
    obtain ⟨s, rfl, rfl, rfl⟩ := toTerm_call ht
    obtain ⟨w, hw, hws⟩ := resolves he hf hty trivial rfl hsup
    simp only [Term.eval?, Option.map_eq_some_iff] at hw
    obtain ⟨d, hd, rfl⟩ := hw
    refine ⟨by simp [TermFits], .inl ⟨_, ?_, hws⟩⟩
    simp [Cedar.Spec.evaluate, List.mapM₁, Cedar.Spec.call, Cedar.Spec.res, hd]
    rfl
  | .getAttr x a, t, τ, ht, hty, hsup => by
    cases hcx : ctxPath x with
    | some p =>
      simp only [toTerm, attrTerm, hcx, Option.some.injEq] at ht
      subst ht
      obtain ⟨w, hw, hws⟩ := resolves he hf hty trivial rfl hsup
      simp only [Term.eval?, Event.contextPath?, hc,
        recordPath_eq_valuePath _ (by simp : p ++ [a] ≠ []), Option.map_eq_some_iff] at hw
      obtain ⟨u, hu, rfl⟩ := hw
      obtain ⟨hx, hfx⟩ := evaluate_ctxPath (es := es) (.getAttr x a) (p ++ [a])
        (by simp [ctxPath, hcx]) u hu
      exact ⟨hfx, .inl ⟨u, hx, hws⟩⟩
    | none =>
      cases hsx : scopePath x with
      | none => simp [toTerm, attrTerm, hcx, hsx] at ht
      | some rp =>
        obtain ⟨r, p⟩ := rp
        simp only [toTerm, attrTerm, hcx, hsx,
          Option.some.injEq] at ht
        subst ht
        -- The scope entity's type declares attributes: it is not an action.
        obtain ⟨rty, hrty⟩ := scopeAttr_typed hty rfl (by simp)
        obtain ⟨uid, huid, huty⟩ : ∃ uid, ev.scope r = some uid ∧ uid.ty = C.scopeType r := by
          cases r with
          | principal =>
            obtain ⟨pr, hpr', hinst⟩ := he.principal
            exact ⟨pr, hpr', hinst.1.symm⟩
          | resource =>
            obtain ⟨rs, hrs', hinst⟩ := he.resource
            exact ⟨rs, hrs', hinst.1.symm⟩
        have hets : C.env.ets.contains uid.ty = true := by
          rw [huty]
          simp only [Cedar.Validation.EntitySchema.attrs?, Option.map_eq_some_iff] at hrty
          obtain ⟨entry, hentry, _⟩ := hrty
          simp [Cedar.Validation.EntitySchema.contains, hentry]
        obtain ⟨w, hw, hws⟩ := resolves he hf hty trivial rfl hsup
        obtain ⟨b, q, hq⟩ := List.exists_cons_of_ne_nil (by simp : p ++ [a] ≠ [])
        have hent : ∃ u, ev.entityAttr? uid (p ++ [a]) = some u ∧ w = .val u := by
          rw [hq] at hw ⊢
          simp only [Term.eval?, Event.scopePath?, huid, Option.map_eq_some_iff] at hw
          obtain ⟨u, hu, rfl⟩ := hw
          exact ⟨u, hu, rfl⟩
        obtain ⟨u, hu, rfl⟩ := hent
        obtain ⟨hx, hfx⟩ := evaluate_scopePath hpr hrs (fun d hd => hst uid d hets hd)
          (.getAttr x a) r (p ++ [a]) (by simp [scopePath, hsx]) (by simp) huid u hu
        exact ⟨hfx, .inl ⟨u, hx, hws⟩⟩
  | .binaryApp .add x y, t, τ, ht, hty, hsup
  | .binaryApp .sub x y, t, τ, ht, hty, hsup
  | .binaryApp .mul x y, t, τ, ht, hty, hsup => by
    simp only [toTerm, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at ht
    obtain ⟨tx, htx, ty, hty', rfl⟩ := ht
    cases hty with
    | arith hl hr =>
      simp only [Term.scopeReads, List.mem_append] at hsup
      obtain ⟨hfx, hx⟩ := evaluate_toTerm hc hpr hrs he hf hst x tx _ htx hl
        (fun r hr => hsup r (.inl hr))
      obtain ⟨hfy, hy⟩ := evaluate_toTerm hc hpr hrs he hf hst y ty _ hty' hr
        (fun r hr => hsup r (.inr hr))
      refine ⟨by simp only [TermFits]; exact ⟨hfx, hfy⟩, ?_⟩
      rcases hx with ⟨vx, hvx, hsx⟩ | hvx
      · obtain ⟨i, rfl⟩ := int_of_hasSort hsx
        rcases hy with ⟨vy, hvy, hsy⟩ | hvy
        · obtain ⟨k, rfl⟩ := int_of_hasSort hsy
          simp only [Cedar.Spec.evaluate, hvx, hvy, Except.bind_ok, Cedar.Spec.apply₂,
            Int64.add?, Int64.sub?, Int64.mul?]
          generalize Int64.ofInt? _ = o
          cases o with
          | none => exact .inr rfl
          | some n => exact .inl ⟨_, rfl, by simp [TVal.HasSort]; exact .instance_of_int⟩
        · exact .inr (by simp [Cedar.Spec.evaluate, hvx, hvy])
      · exact .inr (by simp [Cedar.Spec.evaluate, hvx])
  | .var .action, _, _, ht, _, _ | .var .context, _, _, ht, _, _
  | .ite .., _, _, ht, _, _ | .and .., _, _, ht, _, _ | .or .., _, _, ht, _, _
  | .unaryApp .., _, _, ht, _, _ | .binaryApp .eq .., _, _, ht, _, _
  | .binaryApp .mem .., _, _, ht, _, _ | .binaryApp .hasTag .., _, _, ht, _, _
  | .binaryApp .getTag .., _, _, ht, _, _ | .binaryApp .less .., _, _, ht, _, _
  | .binaryApp .lessEq .., _, _, ht, _, _ | .binaryApp .contains .., _, _, ht, _, _
  | .binaryApp .containsAll .., _, _, ht, _, _ | .binaryApp .containsAny .., _, _, ht, _, _
  | .hasAttr .., _, _, ht, _, _ | .extHasAttr .., _, _, ht, _, _ | .set .., _, _, ht, _, _
  | .record .., _, _, ht, _, _ => by simp [toTerm] at ht

end

section

variable {C : TypingCtx} {req : Request} {es : Entities} {ev : Event}

private theorem cmp_result {op : BinaryOp} {x y : Cedar.Spec.Expr} {P Q : Value → Prop}
    (hx : (∃ u, Cedar.Spec.evaluate x req es = .ok u ∧ P u) ∨
      Cedar.Spec.evaluate x req es = .error .arithBoundsError)
    (hy : (∃ u, Cedar.Spec.evaluate y req es = .ok u ∧ Q u) ∨
      Cedar.Spec.evaluate y req es = .error .arithBoundsError)
    (hok : ∀ vx vy, P vx → Q vy → ∃ b, Cedar.Spec.apply₂ op vx vy es = .ok (.prim (.bool b))) :
    BoolOrOverflow (Cedar.Spec.evaluate (.binaryApp op x y) req es) := by
  rcases hx with ⟨vx, hvx, hpx⟩ | hvx
  · rcases hy with ⟨vy, hvy, hqy⟩ | hvy
    · obtain ⟨b, hb⟩ := hok vx vy hpx hqy
      exact .inl ⟨b, by simp [Cedar.Spec.evaluate, hvx, hvy, hb]⟩
    · exact .inr (by simp [Cedar.Spec.evaluate, hvx, hvy])
  · exact .inr (by simp [Cedar.Spec.evaluate, hvx])

private theorem as_bool_error {r : Cedar.Spec.Result Value}
    (h : r = .error .arithBoundsError) : r.as Bool = .error .arithBoundsError := by
  subst h
  rfl

/-- **A well-typed translation fits, and Cedar evaluates its expression to a `Bool`, or
overflows**, at a decision event that is an instance of the typing environment, carries the
request's context, principal, and resource, supplies the scope entities the translation reads,
and whose facts hold, with a store that reads declared entities as the event supplies them. -/
theorem fits_of_wellTyped (hc : ev.context = req.context)
    (hpr : ev.principal = some req.principal) (hrs : ev.resource = some req.resource)
    (he : ev.InstanceOf C.env) (hf : ∀ g ∈ C.facts, g.Holds ev) (hst : StoreReads es ev C.env) :
    (e : Cedar.Spec.Expr) → (φ : Formula) → toTemporal e = some φ → φ.WellTyped C [] →
      (∀ r ∈ φ.scopeReads, ev.Supplies C.env r) →
      Fits req es e ∧ BoolOrOverflow (Cedar.Spec.evaluate e req es)
  | .binaryApp .eq x y, φ, hφ, hwt, hsup => by
    simp only [toTemporal, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hφ
    obtain ⟨tx, htx, ty, hty, rfl⟩ := hφ
    simp only [Formula.scopeReads, List.mem_append] at hsup
    cases hwt with
    | eq _ hx hy _ =>
      obtain ⟨hfx, hvx⟩ := evaluate_toTerm hc hpr hrs he hf hst x tx _ htx hx
        (fun r h => hsup r (.inl h))
      obtain ⟨hfy, hvy⟩ := evaluate_toTerm hc hpr hrs he hf hst y ty _ hty hy
        (fun r h => hsup r (.inr h))
      exact ⟨by simp only [Fits]; exact ⟨hfx, hfy⟩,
        cmp_result hvx hvy fun vx vy _ _ => ⟨vx == vy, by simp [Cedar.Spec.apply₂]⟩⟩
    | ord hord _ _ => exact absurd hord (by simp [CmpOp.IsOrder])
  | .binaryApp .less x y, φ, hφ, hwt, hsup | .binaryApp .lessEq x y, φ, hφ, hwt, hsup => by
    simp only [toTemporal, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hφ
    obtain ⟨tx, htx, ty, hty, rfl⟩ := hφ
    simp only [Formula.scopeReads, List.mem_append] at hsup
    cases hwt with
    | eq hord _ _ _ => exact absurd (by simp [CmpOp.IsOrder]) hord
    | ord _ hx hy =>
      obtain ⟨hfx, hvx⟩ := evaluate_toTerm hc hpr hrs he hf hst x tx _ htx hx
        (fun r h => hsup r (.inl h))
      obtain ⟨hfy, hvy⟩ := evaluate_toTerm hc hpr hrs he hf hst y ty _ hty hy
        (fun r h => hsup r (.inr h))
      refine ⟨?_, cmp_result hvx hvy fun vx vy hsx hsy => ?_⟩
      · simp only [Fits]
        refine ⟨hfx, hfy, fun vx' vy' hx' hy' => ⟨?_, ?_⟩⟩
        · rcases hvx with ⟨vx, hvx, hsx⟩ | hvx <;> rw [hvx] at hx' <;> cases hx'
          exact int_of_hasSort hsx
        · rcases hvy with ⟨vy, hvy, hsy⟩ | hvy <;> rw [hvy] at hy' <;> cases hy'
          exact int_of_hasSort hsy
      · obtain ⟨i, rfl⟩ := int_of_hasSort hsx
        obtain ⟨k, rfl⟩ := int_of_hasSort hsy
        simp only [Cedar.Spec.apply₂]
        exact ⟨_, rfl⟩
  | .and x y, φ, hφ, hwt, hsup => by
    simp only [toTemporal, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hφ
    obtain ⟨φx, hφx, φy, hφy, rfl⟩ := hφ
    simp only [Formula.scopeReads, List.mem_append] at hsup
    cases hwt with
    | and hx hy =>
      obtain ⟨fx, hbx⟩ := fits_of_wellTyped hc hpr hrs he hf hst x φx hφx hx
        (fun r h => hsup r (.inl h))
      obtain ⟨fy, hby⟩ := fits_of_wellTyped hc hpr hrs he hf hst y φy hφy hy
        (fun r h => hsup r (.inr h))
      refine ⟨by simp only [Fits]; exact ⟨fx, fy⟩, ?_⟩
      rcases hbx with ⟨bx, hbx⟩ | hbx
      · cases bx with
        | false => exact .inl ⟨false, by simp [Cedar.Spec.evaluate, as_bool_ok.mpr hbx]⟩
        | true =>
          rcases hby with ⟨b', hby⟩ | hby
          · exact .inl ⟨b', by simp [Cedar.Spec.evaluate, as_bool_ok.mpr hbx, as_bool_ok.mpr hby]⟩
          · exact .inr (by simp [Cedar.Spec.evaluate, as_bool_ok.mpr hbx, as_bool_error hby])
      · exact .inr (by simp [Cedar.Spec.evaluate, as_bool_error hbx])
  | .or x y, φ, hφ, hwt, hsup => by
    simp only [toTemporal, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hφ
    obtain ⟨φx, hφx, φy, hφy, rfl⟩ := hφ
    simp only [Formula.scopeReads, List.mem_append] at hsup
    cases hwt with
    | not h =>
      cases h with
      | and hx hy =>
        cases hx with
        | not hx =>
          cases hy with
          | not hy =>
            obtain ⟨fx, hbx⟩ := fits_of_wellTyped hc hpr hrs he hf hst x φx hφx hx
              (fun r h => hsup r (.inl h))
            obtain ⟨fy, hby⟩ := fits_of_wellTyped hc hpr hrs he hf hst y φy hφy hy
              (fun r h => hsup r (.inr h))
            refine ⟨by simp only [Fits]; exact ⟨fx, fy⟩, ?_⟩
            rcases hbx with ⟨bx, hbx⟩ | hbx
            · cases bx with
              | true => exact .inl ⟨true, by simp [Cedar.Spec.evaluate, as_bool_ok.mpr hbx]⟩
              | false =>
                rcases hby with ⟨b', hby⟩ | hby
                · exact .inl ⟨b', by
                    simp [Cedar.Spec.evaluate, as_bool_ok.mpr hbx, as_bool_ok.mpr hby]⟩
                · exact .inr (by
                    simp [Cedar.Spec.evaluate, as_bool_ok.mpr hbx, as_bool_error hby])
            · exact .inr (by simp [Cedar.Spec.evaluate, as_bool_error hbx])
  | .unaryApp .not x, φ, hφ, hwt, hsup => by
    simp only [toTemporal, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hφ
    obtain ⟨φx, hφx, rfl⟩ := hφ
    simp only [Formula.scopeReads] at hsup
    cases hwt with
    | not hx =>
      obtain ⟨fx, hbx⟩ := fits_of_wellTyped hc hpr hrs he hf hst x φx hφx hx hsup
      refine ⟨by simp only [Fits]; exact fx, ?_⟩
      rcases hbx with ⟨bx, hbx⟩ | hbx
      · exact .inl ⟨!bx, by simp [Cedar.Spec.evaluate, hbx, Cedar.Spec.apply₁]⟩
      · exact .inr (by simp [Cedar.Spec.evaluate, hbx])
  | .lit _, _, hφ, _, _ | .var _, _, hφ, _, _ | .ite .., _, hφ, _, _
  | .unaryApp .neg _, _, hφ, _, _ | .unaryApp .isEmpty _, _, hφ, _, _
  | .unaryApp (.like _) _, _, hφ, _, _ | .unaryApp (.is _) _, _, hφ, _, _
  | .binaryApp .mem .., _, hφ, _, _ | .binaryApp .hasTag .., _, hφ, _, _
  | .binaryApp .getTag .., _, hφ, _, _ | .binaryApp .add .., _, hφ, _, _
  | .binaryApp .sub .., _, hφ, _, _ | .binaryApp .mul .., _, hφ, _, _
  | .binaryApp .contains .., _, hφ, _, _ | .binaryApp .containsAll .., _, hφ, _, _
  | .binaryApp .containsAny .., _, hφ, _, _ | .getAttr .., _, hφ, _, _
  | .hasAttr .., _, hφ, _, _ | .extHasAttr .., _, hφ, _, _ | .set .., _, hφ, _, _
  | .record .., _, hφ, _, _ | .call .., _, hφ, _, _ => by
    simp [toTemporal] at hφ

end

/-! ## Provider arguments

A provider argument resolves against the decision event as a temporal term does
(`Provider.Arg.resolve`), and a path that does not resolve is `absent`, which the provider
receives as null. On the fragment without sets and arithmetic, a translated argument resolves to
the value Cedar evaluates the expression to (`resolve_toArg`), and to `absent` exactly where Cedar
errs (`resolve_toArg_error`): the provider runs, with a null, where Cedar's evaluation of the
same expression fails. A set argument resolves to the list of its items as written, in order
and with duplicates, where Cedar's set literal is a set. -/

/-- A temporal term as a provider argument: a literal other than an entity, a `decimal`, or a
context or scope path. -/
def termToArg : Term → Option Provider.Arg
  | .long i => some (.long i)
  | .string s => some (.string s)
  | .bool b => some (.bool b)
  | .decimal s => some (.decimal s)
  | .context p => some (.context p)
  | .scope r p => some (.scope r p)
  | _ => none

/-- A Cedar expression as a provider argument. -/
def toArg (x : Cedar.Spec.Expr) : Option Provider.Arg := (toTerm x).bind termToArg

theorem termToArg_simple {t : Term} {a : Provider.Arg} (h : termToArg t = some a) : t.Simple := by
  cases t <;> simp_all [termToArg, Term.Simple]

theorem resolve_termToArg {e : Event} {v₀ : Valuation} {t : Term} {a : Provider.Arg}
    (h : termToArg t = some a) :
    a.resolve e = ((t.eval? e v₀).bind fun w => match w with
      | .val v => some (Provider.ArgValue.value v) | .tp _ => none).getD .absent := by
  cases t <;> simp only [termToArg, Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
    simp only [Provider.Arg.resolve, Term.eval?] <;>
    first
    | rfl
    | (rename_i s; cases Cedar.Spec.Ext.Decimal.parse s <;> rfl)
    | (rename_i p; cases Event.contextPath? _ p <;> rfl)
    | (rename_i r p; cases Event.scopePath? _ r p <;> rfl)

section

variable {req : Request} {es : Entities} {ev : Event} {v₀ : Valuation}

/-- A simple translated term that resolves is one Cedar evaluates, to the same value, when
Cedar's store reads the scope entities as the event supplies them. -/
theorem evaluate_of_eval (hc : ev.context = req.context)
    (hpr : ev.principal = some req.principal) (hrs : ev.resource = some req.resource) :
    (x : Cedar.Spec.Expr) → (t : Term) → toTerm x = some t → t.Simple →
      (∀ r q uid d, t = .scope r q → q ≠ [] → ev.scope r = some uid →
        ev.entities.find? uid = some d → es.find? uid = some d) → (w : TVal) →
      t.eval? ev v₀ = some w → ∃ u, w = .val u ∧ Cedar.Spec.evaluate x req es = .ok u
  | .lit p, t, ht, _, _, w, hw => by
    cases p <;> simp only [toTerm, Option.some.injEq] at ht <;> subst ht <;>
      simp only [Term.eval?, Option.some.injEq] at hw <;> subst hw <;>
      exact ⟨_, rfl, by simp [Cedar.Spec.evaluate]⟩
  | .var .principal, t, ht, _, _, w, hw => by
    simp only [toTerm, Option.some.injEq] at ht
    subst ht
    simp [Term.eval?, Event.scopePath?, Event.scope, hpr] at hw
    subst hw
    exact ⟨_, rfl, by simp [Cedar.Spec.evaluate]⟩
  | .var .resource, t, ht, _, _, w, hw => by
    simp only [toTerm, Option.some.injEq] at ht
    subst ht
    simp [Term.eval?, Event.scopePath?, Event.scope, hrs] at hw
    subst hw
    exact ⟨_, rfl, by simp [Cedar.Spec.evaluate]⟩
  | .call xfn xs, t, ht, _, _, w, hw => by
    obtain ⟨s, rfl, rfl, rfl⟩ := toTerm_call ht
    simp only [Term.eval?, Option.map_eq_some_iff] at hw
    obtain ⟨d, hd, rfl⟩ := hw
    refine ⟨_, rfl, ?_⟩
    simp [Cedar.Spec.evaluate, List.mapM₁, Cedar.Spec.call, Cedar.Spec.res, hd]
    rfl
  | .getAttr x a, t, ht, _, hsr, w, hw => by
    cases hcx : ctxPath x with
    | some p =>
      simp only [toTerm, attrTerm, hcx, Option.some.injEq] at ht
      subst ht
      simp only [Term.eval?, Event.contextPath?, hc,
        recordPath_eq_valuePath _ (by simp : p ++ [a] ≠ []), Option.map_eq_some_iff] at hw
      obtain ⟨u, hu, rfl⟩ := hw
      exact ⟨u, rfl, (evaluate_ctxPath (es := es) (.getAttr x a) (p ++ [a])
        (by simp [ctxPath, hcx]) u hu).1⟩
    | none =>
      cases hsx : scopePath x with
      | none => simp [toTerm, attrTerm, hcx, hsx] at ht
      | some rp =>
        obtain ⟨r, p⟩ := rp
        simp only [toTerm, attrTerm, hcx, hsx,
          Option.some.injEq] at ht
        subst ht
        obtain ⟨b, q, hq⟩ := List.exists_cons_of_ne_nil (by simp : p ++ [a] ≠ [])
        cases huid : ev.scope r with
        | none =>
          rw [hq] at hw
          simp [Term.eval?, Event.scopePath?, huid] at hw
        | some uid =>
          have hent : ∃ u, ev.entityAttr? uid (p ++ [a]) = some u ∧ w = .val u := by
            rw [hq] at hw ⊢
            simp only [Term.eval?, Event.scopePath?, huid, Option.map_eq_some_iff] at hw
            obtain ⟨u, hu, rfl⟩ := hw
            exact ⟨u, hu, rfl⟩
          obtain ⟨u, hu, rfl⟩ := hent
          exact ⟨u, rfl, (evaluate_scopePath hpr hrs
            (fun d hd => hsr r (p ++ [a]) uid d rfl (by simp) huid hd)
            (.getAttr x a) r (p ++ [a]) (by simp [scopePath, hsx]) (by simp) huid u hu).1⟩
  | .binaryApp .add x y, t, ht, hs, _, _, _ | .binaryApp .sub x y, t, ht, hs, _, _, _
  | .binaryApp .mul x y, t, ht, hs, _, _, _ => by
    simp only [toTerm, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at ht
    obtain ⟨_, _, _, _, rfl⟩ := ht
    simp [Term.Simple] at hs
  | .var .action, _, ht, _, _, _, _ | .var .context, _, ht, _, _, _, _
  | .ite .., _, ht, _, _, _, _ | .and .., _, ht, _, _, _, _ | .or .., _, ht, _, _, _, _
  | .unaryApp .., _, ht, _, _, _, _ | .binaryApp .eq .., _, ht, _, _, _, _
  | .binaryApp .mem .., _, ht, _, _, _, _ | .binaryApp .hasTag .., _, ht, _, _, _, _
  | .binaryApp .getTag .., _, ht, _, _, _, _ | .binaryApp .less .., _, ht, _, _, _, _
  | .binaryApp .lessEq .., _, ht, _, _, _, _ | .binaryApp .contains .., _, ht, _, _, _, _
  | .binaryApp .containsAll .., _, ht, _, _, _, _ | .binaryApp .containsAny .., _, ht, _, _, _, _
  | .hasAttr .., _, ht, _, _, _, _ | .extHasAttr .., _, ht, _, _, _, _ | .set .., _, ht, _, _, _, _
  | .record .., _, ht, _, _, _, _ => by simp [toTerm] at ht

/-- **A translated provider argument resolves to the value Cedar evaluates the expression to**,
at a decision event that carries the request's context, principal, and resource, with a store
that reads entities as the event supplies them (`StoreFits`), where the expression's attribute
accesses run through records. -/
theorem resolve_toArg (hc : ev.context = req.context)
    (hpr : ev.principal = some req.principal) (hrs : ev.resource = some req.resource)
    (hes : StoreFits es ev) {x : Cedar.Spec.Expr} {a : Provider.Arg} (ha : toArg x = some a)
    (hfit : TermFits req es x) {v : Value} (hx : Cedar.Spec.evaluate x req es = .ok v) :
    a.resolve ev = .value v := by
  simp only [toArg, Option.bind_eq_some_iff] at ha
  obtain ⟨t, ht, hta⟩ := ha
  rw [resolve_termToArg (v₀ := Valuation.empty) hta,
    eval_toTerm_simple hc hpr hrs hes ht (termToArg_simple hta) hfit hx]
  rfl

/-- A decision's store reads the event's entities as the event supplies them when no entity the
event supplies is an action of the schema: an action's schema entry takes precedence. -/
theorem decisionEntities_reads_supplied {P : PolicySet} {ev : Event}
    (h : ∀ uid d, ev.entities.find? uid = some d → P.actionSchema.acts.find? uid = none) :
    ∀ uid d, ev.entities.find? uid = some d → (P.decisionEntities ev).find? uid = some d := by
  intro uid d hd
  rw [decisionEntities_find?, h uid d hd, hd]
  rfl

/-- **A translated provider argument is `absent` exactly where Cedar's evaluation of the
expression errs**, with a store that reads the event's entities as it supplies them: the
provider runs, and receives a null, where Cedar fails. -/
theorem resolve_toArg_error (hc : ev.context = req.context)
    (hpr : ev.principal = some req.principal) (hrs : ev.resource = some req.resource)
    (hsr : ∀ uid d, ev.entities.find? uid = some d → es.find? uid = some d)
    {x : Cedar.Spec.Expr} {a : Provider.Arg} (ha : toArg x = some a) {err : Cedar.Spec.Error}
    (hx : Cedar.Spec.evaluate x req es = .error err) :
    a.resolve ev = .absent := by
  simp only [toArg, Option.bind_eq_some_iff] at ha
  obtain ⟨t, ht, hta⟩ := ha
  rw [resolve_termToArg (v₀ := Valuation.empty) hta]
  cases hw : t.eval? ev Valuation.empty with
  | none => rfl
  | some w =>
    obtain ⟨u, -, hu⟩ := evaluate_of_eval (es := es) hc hpr hrs x t ht (termToArg_simple hta)
      (fun _ _ uid d _ _ _ hd => hsr uid d hd) w hw
    rw [hu] at hx
    cases hx

end

/-- A Cedar set literal of translated items as a provider argument. -/
def toSetArg (xs : List Cedar.Spec.Expr) : Option Provider.Arg :=
  (xs.mapM toArg).map .set

section

variable {req : Request} {es : Entities} {ev : Event}

private theorem resolveList_toArg (hc : ev.context = req.context)
    (hpr : ev.principal = some req.principal) (hrs : ev.resource = some req.resource)
    (hes : StoreFits es ev) :
    (xs : List Cedar.Spec.Expr) → (bs : List Provider.Arg) → xs.mapM toArg = some bs →
      (∀ x ∈ xs, TermFits req es x) → (vs : List Value) →
      xs.mapM (Cedar.Spec.evaluate · req es) = .ok vs →
      Provider.Arg.resolveList ev bs = vs.map .value
  | [], bs, h, _, vs, hv => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at hv
    subst h hv
    rfl
  | x :: xs, bs, h, hfit, vs, hv => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨a, ha, rest, hrest, rfl⟩ := h
    cases hx : Cedar.Spec.evaluate x req es with
    | error e => simp [List.mapM_cons, hx] at hv
    | ok v =>
      cases hxs : xs.mapM (Cedar.Spec.evaluate · req es) with
      | error e => simp [List.mapM_cons, hx, hxs] at hv
      | ok vs' =>
        simp only [List.mapM_cons, hx, hxs, Except.bind_ok, pure, Except.pure,
          Except.ok.injEq] at hv
        subst hv
        simp only [Provider.Arg.resolveList, List.map_cons,
          resolve_toArg hc hpr hrs hes ha (hfit x (List.mem_cons_self ..)) hx,
          resolveList_toArg hc hpr hrs hes xs rest hrest
            (fun y hy => hfit y (List.mem_cons_of_mem _ hy)) vs' hxs]

/-- **A set argument is a list where Cedar's is a set.** A Cedar set literal of translated items
that Cedar evaluates is the set of the items' values (`Set.make`), and as a provider argument it
resolves to the list of the same values, as written: in order, with duplicates. So two set
literals Cedar evaluates alike, such as `[a, b]` and `[b, a, a]`, can reach a provider as
different lists. -/
theorem resolve_toSetArg (hc : ev.context = req.context)
    (hpr : ev.principal = some req.principal) (hrs : ev.resource = some req.resource)
    (hes : StoreFits es ev) {xs : List Cedar.Spec.Expr} {a : Provider.Arg}
    (ha : toSetArg xs = some a) (hfit : ∀ x ∈ xs, TermFits req es x) {vs : List Value}
    (hv : xs.mapM (Cedar.Spec.evaluate · req es) = .ok vs) :
    Cedar.Spec.evaluate (.set xs) req es = .ok (.set (Cedar.Data.Set.make vs)) ∧
      a.resolve ev = .list (vs.map .value) := by
  simp only [toSetArg, Option.map_eq_some_iff] at ha
  obtain ⟨bs, has, rfl⟩ := ha
  refine ⟨?_, ?_⟩
  · simp only [Cedar.Spec.evaluate]
    rw [List.mapM₁_eq_mapM (fun x => Cedar.Spec.evaluate x req es), hv]
    rfl
  · simp only [Provider.Arg.resolve]
    rw [resolveList_toArg hc hpr hrs hes xs bs has hfit vs hv]

end

/-! ### Provider arguments of a valid policy set

A typed provider argument's path types through records (`declaredPathType?`), so at a request and
a store that are instances of the environment, every subject of an access along it that Cedar
evaluates is a record: the argument fits. A typed scope path reads an entity of a type that
declares attributes, which is no action, so the store reads it as the event supplies it. So, for a
valid policy set, an argument is exactly what Cedar evaluates its expression to, or absent where
Cedar errs (`resolve_providerArg_of_valid`). -/

/-- The Cedar variable of a scope root. -/
def scopeVar : ScopeRoot → Var
  | .principal => .principal
  | .resource => .resource

section

open Cedar.Validation (TypeEnv RecordType CedarType)
open Cedar.Thm (InstanceOfType InstanceOfSchema)

variable {env : TypeEnv}

/-- A value read along a typed path of a record instance is an instance of the path's type. -/
theorem valuePath_instance : (p : Path) → (pre : Path) → (r : Cedar.Data.Map Attr Value) →
    (rty : RecordType) → {T : CedarType} → InstanceOfType env (.record r) (.record rty) →
    pathType? (fun _ => true) rty pre p = some T → (w : Value) →
    valuePath? (.record r) p = some w → InstanceOfType env w T
  | [], _, _, _, _, _, h, _, _ => by simp [pathType?] at h
  | a :: p, pre, r, rty, T, hinst, h, w, hw => by
    unfold pathType? at h
    cases hf : rty.find? a with
    | none => rw [hf] at h; cases h
    | some qty =>
      rw [hf] at h
      simp only [Bool.or_true, ↓reduceIte] at h
      simp only [valuePath?] at hw
      cases hr : r.find? a with
      | none => rw [hr] at hw; cases hw
      | some w' =>
        rw [hr] at hw
        simp only [Option.bind_some] at hw
        cases hinst with
        | instance_of_record _ _ _ h₂ _ =>
        have hw' := h₂ a w' qty hr hf
        cases p with
        | nil =>
          simp only [valuePath?, Option.some.injEq] at hw
          subst hw
          simp only [Option.some.injEq] at h
          exact h ▸ hw'
        | cons b p =>
          cases hg : qty.getType with
          | record rty' =>
            rw [hg] at h hw'
            cases hw' with
            | instance_of_record r' _ h₁' h₂' h₃' =>
            exact valuePath_instance (b :: p) (pre ++ [a]) r' rty'
              (.instance_of_record _ _ h₁' h₂' h₃') h w hw
          | _ => rw [hg] at h; simp at h

/-- A proper prefix of a typed path types as a record. -/
theorem pathType_prefix : (q : Path) → (pre : Path) → (rty : RecordType) → (a : Attr) →
    {T : CedarType} → q ≠ [] → pathType? (fun _ => true) rty pre (q ++ [a]) = some T →
    ∃ rty', pathType? (fun _ => true) rty pre q = some (.record rty')
  | [], _, _, _, _, hq, _ => absurd rfl hq
  | b :: q, pre, rty, a, T, _, h => by
    simp only [List.cons_append] at h
    unfold pathType? at h ⊢
    cases hf : rty.find? b with
    | none => rw [hf] at h; cases h
    | some qty =>
      rw [hf] at h
      simp only [Bool.or_true, ↓reduceIte] at h ⊢
      cases hg : qty.getType with
      | record rty' =>
        rw [hg] at h
        cases q with
        | nil => exact ⟨rty', rfl⟩
        | cons c q =>
          simp only at h ⊢
          exact pathType_prefix (c :: q) (pre ++ [b]) rty' a (by simp) h
      | _ =>
        rw [hg] at h
        cases q <;> simp at h

end

section

open Cedar.Validation (TypeEnv RecordType CedarType)
open Cedar.Thm (InstanceOfType InstanceOfSchema)

variable {env : TypeEnv} {req : Request} {es : Entities}

/-- A context path typed through records fits, at a request whose context is an instance of the
record type. -/
theorem termFits_ctx {rty : RecordType}
    (hinst : InstanceOfType env (.record req.context) (.record rty)) :
    (x : Cedar.Spec.Expr) → (p : Path) → ctxPath x = some p → {T : CedarType} →
      pathType? (fun _ => true) rty [] p = some T → TermFits req es x
  | .var .context, _, _, _, _ => by simp [TermFits]
  | .getAttr x a, p, hp, T, hT => by
    simp only [ctxPath, Option.map_eq_some_iff] at hp
    obtain ⟨p', hp', rfl⟩ := hp
    simp only [TermFits]
    by_cases hnil : p' = []
    · subst hnil
      have hx : x = .var .context := by
        rcases x with _ | ⟨_ | _ | _ | _⟩ | _ | _ | _ | _ | _ | ⟨y, b⟩ | _ | _ | _ | _ | _
        all_goals simp_all [ctxPath]
      subst hx
      refine ⟨by simp [TermFits], .inr (.inr fun v hv => ⟨req.context, ?_⟩)⟩
      simp only [Cedar.Spec.evaluate, Except.ok.injEq] at hv
      exact hv.symm
    · obtain ⟨rty', hrty'⟩ := pathType_prefix p' [] rty a hnil hT
      have hfx := termFits_ctx hinst x p' hp' hrty'
      refine ⟨hfx, .inr (.inr fun v hv => ?_)⟩
      have hw := valuePath_of_ctxPath x p' hp' hfx v hv
      have := valuePath_instance p' [] req.context rty hinst hrty' v hw
      cases this with
      | instance_of_record r _ _ _ _ => exact ⟨r, rfl⟩
  | .lit _, _, hp, _, _ | .var .principal, _, hp, _, _ | .var .action, _, hp, _, _
  | .var .resource, _, hp, _, _ | .ite .., _, hp, _, _ | .and .., _, hp, _, _
  | .or .., _, hp, _, _ | .unaryApp .., _, hp, _, _ | .binaryApp .., _, hp, _, _
  | .hasAttr .., _, hp, _, _ | .extHasAttr .., _, hp, _, _ | .set .., _, hp, _, _
  | .record .., _, hp, _, _ | .call .., _, hp, _, _ => by cases hp

/-- The attribute path `p` of the entity `uid`, in Cedar's store. -/
def storePath? (es : Entities) (uid : EntityUID) : Path → Option Value
  | [] => none
  | a :: p => ((es.find? uid).bind (·.attrs.find? a)).bind (valuePath? · p)

/-- A scope path Cedar evaluates through records reads the store's data for the scope entity. -/
theorem storePath_of_scopePath {uid : EntityUID} {r : ScopeRoot}
    (hroot : Cedar.Spec.evaluate (.var (scopeVar r)) req es = .ok (.prim (.entityUID uid))) :
    (x : Cedar.Spec.Expr) → (p : Path) → scopePath x = some (r, p) → p ≠ [] →
      TermFits req es x → (v : Value) → Cedar.Spec.evaluate x req es = .ok v →
      storePath? es uid p = some v
  | .getAttr x a, p, hp, _, hfit, v, hv => by
    simp only [scopePath, Option.map_eq_some_iff, Prod.exists] at hp
    obtain ⟨r', p', hp', hrp⟩ := hp
    simp only [Prod.mk.injEq] at hrp
    obtain ⟨rfl, rfl⟩ := hrp
    simp only [TermFits] at hfit
    obtain ⟨hfit', hrec⟩ := hfit
    simp only [Cedar.Spec.evaluate] at hv
    cases hx : Cedar.Spec.evaluate x req es with
    | error e => rw [hx] at hv; cases hv
    | ok vx =>
      rw [hx] at hv
      simp only [Except.bind_ok] at hv
      by_cases hnil : p' = []
      · subst hnil
        have hvx : vx = .prim (.entityUID uid) := by
          rcases scopePath_nil hp' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · simp only [scopeVar] at hroot; rw [hroot] at hx; cases hx; rfl
          · simp only [scopeVar] at hroot; rw [hroot] at hx; cases hx; rfl
        subst hvx
        simp only [Cedar.Spec.getAttr, Cedar.Spec.attrsOf, Entities.attrs,
          Cedar.Data.Map.findOrErr] at hv
        cases hd : es.find? uid with
        | none => rw [hd] at hv; cases hv
        | some d =>
          rw [hd] at hv
          simp only [Except.bind_ok] at hv
          cases hw : d.attrs.find? a with
          | none => rw [hw] at hv; cases hv
          | some w =>
            rw [hw] at hv
            simp only [Except.ok.injEq] at hv
            subst hv
            simp [storePath?, hd, hw, valuePath?]
      · have hrec : ∃ rec, vx = .record rec := by
          rcases hrec with h | h | h
          · exact absurd h (scopePath_var hp' hnil).1
          · exact absurd h (scopePath_var hp' hnil).2
          · exact h vx hx
        obtain ⟨rec, rfl⟩ := hrec
        have ih := storePath_of_scopePath hroot x p' hp' hnil hfit' _ hx
        simp only [Cedar.Spec.getAttr, Cedar.Spec.attrsOf, Cedar.Data.Map.findOrErr,
          Except.bind_ok] at hv
        cases hw : rec.find? a with
        | none => rw [hw] at hv; cases hv
        | some w =>
          rw [hw] at hv
          simp only [Except.ok.injEq] at hv
          subst hv
          obtain ⟨b, q, rfl⟩ := List.exists_cons_of_ne_nil hnil
          simp only [storePath?, List.cons_append] at ih ⊢
          rw [Option.bind_congr (fun w _ => valuePath_append w q [a]), ← Option.bind_assoc, ih]
          simp [valuePath?, hw]
  | .var .principal, _, hp, hne, _, _, _ | .var .resource, _, hp, hne, _, _, _ => by
    simp only [scopePath, Option.some.injEq, Prod.mk.injEq] at hp
    exact absurd hp.2.symm hne
  | .lit _, _, hp, _, _, _, _ | .var .action, _, hp, _, _, _, _
  | .var .context, _, hp, _, _, _, _ | .ite .., _, hp, _, _, _, _
  | .and .., _, hp, _, _, _, _ | .or .., _, hp, _, _, _, _
  | .unaryApp .., _, hp, _, _, _, _ | .binaryApp .., _, hp, _, _, _, _
  | .hasAttr .., _, hp, _, _, _, _ | .extHasAttr .., _, hp, _, _, _, _
  | .set .., _, hp, _, _, _, _ | .record .., _, hp, _, _, _, _
  | .call .., _, hp, _, _, _, _ => by cases hp

/-- A scope path typed through the scope entity's declared attributes fits, at a store that is an
instance of the environment. -/
theorem termFits_scope {uid : EntityUID} {r : ScopeRoot}
    (hroot : Cedar.Spec.evaluate (.var (scopeVar r)) req es = .ok (.prim (.entityUID uid)))
    (hst : InstanceOfSchema es env) {rty : RecordType}
    (hrty : env.ets.attrs? uid.ty = some rty) :
    (x : Cedar.Spec.Expr) → (p : Path) → scopePath x = some (r, p) → {T : CedarType} →
      p ≠ [] → pathType? (fun _ => true) rty [] p = some T → TermFits req es x
  | .getAttr x a, p, hp, T, _, hT => by
    simp only [scopePath, Option.map_eq_some_iff, Prod.exists] at hp
    obtain ⟨r', p', hp', hrp⟩ := hp
    simp only [Prod.mk.injEq] at hrp
    obtain ⟨rfl, rfl⟩ := hrp
    simp only [TermFits]
    by_cases hnil : p' = []
    · subst hnil
      refine ⟨?_, ?_⟩
      · rcases scopePath_nil hp' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [TermFits]
      · rcases scopePath_nil hp' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact .inl rfl
        · exact .inr (.inl rfl)
    · obtain ⟨rty', hrty'⟩ := pathType_prefix p' [] rty a hnil hT
      have hfx := termFits_scope hroot hst hrty x p' hp' hnil hrty'
      refine ⟨hfx, .inr (.inr fun v hv => ?_)⟩
      have hsp := storePath_of_scopePath hroot x p' hp' hnil hfx v hv
      obtain ⟨b, q, rfl⟩ := List.exists_cons_of_ne_nil hnil
      simp only [storePath?, Option.bind_eq_some_iff] at hsp
      obtain ⟨w, ⟨d, hd, hw⟩, hq⟩ := hsp
      -- The store's entry is an instance of the entity type, or an action, which has no
      -- attributes.
      rcases hst.1 uid d hd with ⟨entry, hentry, _, hattrs, _, _⟩ | hact
      · have hre : entry.attrs = rty := by
          simp only [Cedar.Validation.EntitySchema.attrs?, hentry, Option.map_some,
            Option.some.injEq] at hrty
          exact hrty
        subst hre
        have := valuePath_instance (b :: q) [] d.attrs entry.attrs hattrs hrty' v
          (by simp [valuePath?, hw, hq])
        cases this with
        | instance_of_record r _ _ _ _ => exact ⟨r, rfl⟩
      · obtain ⟨hempty, _, _⟩ := hact
        rw [hempty] at hw
        cases hw
  | .var .principal, _, hp, _, hne, _ | .var .resource, _, hp, _, hne, _ => by
    simp only [scopePath, Option.some.injEq, Prod.mk.injEq] at hp
    exact absurd hp.2.symm hne
  | .lit _, _, hp, _, _, _ | .var .action, _, hp, _, _, _
  | .var .context, _, hp, _, _, _ | .ite .., _, hp, _, _, _
  | .and .., _, hp, _, _, _ | .or .., _, hp, _, _, _
  | .unaryApp .., _, hp, _, _, _ | .binaryApp .., _, hp, _, _, _
  | .hasAttr .., _, hp, _, _, _ | .extHasAttr .., _, hp, _, _, _
  | .set .., _, hp, _, _, _ | .record .., _, hp, _, _, _
  | .call .., _, hp, _, _, _ => by cases hp

end

section

open Cedar.Thm (InstanceOfSchema)
open Cedar.Validation (CedarType)

variable {C : TypingCtx} {req : Request} {es : Entities} {ev : Event}

theorem toArg_shape {x : Cedar.Spec.Expr} {a : Provider.Arg} (ha : toArg x = some a) :
    ∃ t, toTerm x = some t ∧ termToArg t = some a := by
  simpa [toArg, Option.bind_eq_some_iff] using ha

/-- A translated argument is not a set: its declared type is its type. -/
theorem typeIn_of_hasTypeIn {x : Cedar.Spec.Expr} {a : Provider.Arg} {ty : CedarType}
    (ha : toArg x = some a) (h : a.hasTypeIn C ty = true) : a.typeIn? C = some ty := by
  obtain ⟨t, -, hta⟩ := toArg_shape ha
  cases t <;> simp only [termToArg, Option.some.injEq, reduceCtorEq] at hta <;> subst hta <;>
    simpa [Provider.Arg.hasTypeIn] using h

/-- **A typed provider argument fits**: its path types through records, so at a request and a
store that are instances of the typing environment, every subject of an access along it that
Cedar evaluates is a record. -/
theorem termFits_of_typeIn (hc : ev.context = req.context)
    (hpr : ev.principal = some req.principal) (hrs : ev.resource = some req.resource)
    (he : ev.InstanceOf C.env) (hst : InstanceOfSchema es C.env) {x : Cedar.Spec.Expr}
    {a : Provider.Arg} (ha : toArg x = some a) {ty : CedarType} (hty : a.typeIn? C = some ty) :
    TermFits req es x := by
  obtain ⟨t, ht, hta⟩ := toArg_shape ha
  cases x with
  | getAttr x b =>
    cases hcx : ctxPath x with
    | some p =>
      simp only [toTerm, attrTerm, hcx, Option.some.injEq] at ht
      subst ht
      simp only [termToArg, Option.some.injEq] at hta
      subst hta
      have hinst := he.context
      rw [hc] at hinst
      exact termFits_ctx hinst (.getAttr x b) (p ++ [b]) (by simp [ctxPath, hcx]) hty
    | none =>
      cases hsx : scopePath x with
      | none => simp [toTerm, attrTerm, hcx, hsx] at ht
      | some rp =>
        obtain ⟨r, p⟩ := rp
        simp only [toTerm, attrTerm, hcx, hsx,
          Option.some.injEq] at ht
        subst ht
        simp only [termToArg, Option.some.injEq] at hta
        subst hta
        obtain ⟨c, q, hq⟩ := List.exists_cons_of_ne_nil (by simp : p ++ [b] ≠ [])
        have hty' := hty
        rw [hq] at hty'
        simp only [Provider.Arg.typeIn?, ← hq, Bool.false_eq_true, ↓reduceIte,
          Option.bind_eq_some_iff] at hty'
        obtain ⟨rty, hrty, hT⟩ := hty'
        -- The scope entity, of the scope's type.
        obtain ⟨uid, hroot, huty⟩ : ∃ uid, Cedar.Spec.evaluate (.var (scopeVar r)) req es =
            .ok (.prim (.entityUID uid)) ∧ uid.ty = C.scopeType r := by
          cases r with
          | principal =>
            obtain ⟨pr, hpr', hinst⟩ := he.principal
            rw [hpr] at hpr'
            cases hpr'
            exact ⟨_, by simp [scopeVar, Cedar.Spec.evaluate], hinst.1.symm⟩
          | resource =>
            obtain ⟨rs, hrs', hinst⟩ := he.resource
            rw [hrs] at hrs'
            cases hrs'
            exact ⟨_, by simp [scopeVar, Cedar.Spec.evaluate], hinst.1.symm⟩
        rw [← huty] at hrty
        exact termFits_scope hroot hst hrty (.getAttr x b) (p ++ [b])
          (by simp [scopePath, hsx]) (by simp) hT
  | binaryApp op x y =>
    cases op <;> simp only [toTerm, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq, reduceCtorEq] at ht <;>
      (try obtain ⟨_, _, _, _, rfl⟩ := ht) <;> simp_all [termToArg]
  | _ => simp [TermFits]

/-- **A typed provider argument resolves to the value Cedar evaluates its expression to**, at a
decision event that is an instance of the typing environment and carries the request's context,
principal, and resource, with a store that is an instance of the environment and reads entities
as the event supplies them. -/
theorem resolve_toArg_of_typed (hc : ev.context = req.context)
    (hpr : ev.principal = some req.principal) (hrs : ev.resource = some req.resource)
    (hes : StoreFits es ev) (he : ev.InstanceOf C.env) (hst : InstanceOfSchema es C.env)
    {x : Cedar.Spec.Expr} {a : Provider.Arg} (ha : toArg x = some a) {ty : CedarType}
    (hty : a.typeIn? C = some ty) {v : Value} (hx : Cedar.Spec.evaluate x req es = .ok v) :
    a.resolve ev = .value v :=
  resolve_toArg hc hpr hrs hes ha (termFits_of_typeIn hc hpr hrs he hst ha hty) hx

/-- **A typed provider argument is `absent` exactly where Cedar's evaluation of its expression
errs**, at a decision event that is an instance of the typing environment, with a store that
reads every entity of a declared entity type as the event supplies it (`StoreReads`, which a
valid policy set's decision store satisfies): the entity a typed scope path reads is of a type
that declares attributes, so it is not an action. -/
theorem resolve_toArg_error_of_typed (hc : ev.context = req.context)
    (hpr : ev.principal = some req.principal) (hrs : ev.resource = some req.resource)
    (he : ev.InstanceOf C.env) (hsr : StoreReads es ev C.env) {x : Cedar.Spec.Expr}
    {a : Provider.Arg} (ha : toArg x = some a) {ty : CedarType} (hty : a.typeIn? C = some ty)
    {err : Cedar.Spec.Error} (hx : Cedar.Spec.evaluate x req es = .error err) :
    a.resolve ev = .absent := by
  obtain ⟨t, ht, hta⟩ := toArg_shape ha
  rw [resolve_termToArg (v₀ := Valuation.empty) hta]
  cases hw : t.eval? ev Valuation.empty with
  | none => rfl
  | some w =>
    have hread : ∀ r q uid d, t = .scope r q → q ≠ [] → ev.scope r = some uid →
        ev.entities.find? uid = some d → es.find? uid = some d := by
      intro r q uid d htq hq huid hd
      subst htq
      simp only [termToArg, Option.some.injEq] at hta
      subst hta
      obtain ⟨c, q', rfl⟩ := List.exists_cons_of_ne_nil hq
      simp only [Provider.Arg.typeIn?, Option.bind_eq_some_iff] at hty
      obtain ⟨rty, hrty, -⟩ := hty
      have huty : uid.ty = C.scopeType r := by
        cases r with
        | principal =>
          obtain ⟨pr, hpr', hinst⟩ := he.principal
          simp only [Event.scope] at huid
          rw [huid] at hpr'
          cases hpr'
          exact hinst.1.symm
        | resource =>
          obtain ⟨rs, hrs', hinst⟩ := he.resource
          simp only [Event.scope] at huid
          rw [huid] at hrs'
          cases hrs'
          exact hinst.1.symm
      have hets : C.env.ets.contains uid.ty = true := by
        rw [huty]
        simp only [Cedar.Validation.EntitySchema.attrs?, Option.map_eq_some_iff] at hrty
        obtain ⟨entry, hentry, _⟩ := hrty
        simp [Cedar.Validation.EntitySchema.contains, hentry]
      exact hsr uid d hets hd
    obtain ⟨u, -, hu⟩ := evaluate_of_eval (es := es) hc hpr hrs x t ht (termToArg_simple hta)
      hread w hw
    rw [hu] at hx
    cases hx

end

/-- At a decision of a valid policy set every check of which passes, a provider argument of an
invocation of a rule whose scope holds is typed in an environment of which the request and the
store are instances, and whose declared entities the store reads as the event supplies them. -/
private theorem providerArg_typed {P : PolicySet} (hv : P.Valid) {rules : Policies}
    {ω : Provider.Providers} {p : TimePoint} {pr rs : EntityUID} (ha : P.Admits rules ω p pr rs)
    {q : Policy} (hq : q ∈ P.policies)
    (hs : q.ScopeHolds (p.event.request pr rs) (P.decisionEntities p.event))
    {c : Provider.Call} {F : List Guard} (hcF : (.inr c, F) ∈ q.toExpr.leafFacts [])
    {arg : Provider.Arg} (hmem : arg ∈ c.args) {x : Cedar.Spec.Expr} (harg : toArg x = some arg) :
    ∃ env, p.event.InstanceOf env ∧ Cedar.Thm.InstanceOfSchema (P.decisionEntities p.event) env ∧
      StoreReads (P.decisionEntities p.event) p.event env ∧
      ∃ ty, arg.typeIn? (P.typingCtx env F) = some ty := by
  obtain ⟨env, henv, hreq⟩ := request_instance ha.request
  have henvq := admits_of_scopeHolds henv hreq (instanceOfSchema_of_admits ha henv) hs
  obtain ⟨sig, -, ⟨hlen, hzip⟩, -⟩ := (hv.providers q hq c F hcF).2 env henvq
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hmem
  have hi' : i < sig.args.length := hlen ▸ hi
  have hz := hzip (c.args[i], sig.args[i])
    (List.mem_iff_getElem.mpr ⟨i, by simp only [List.length_zip]; omega, by simp⟩)
  exact ⟨env, instanceOf_of_admits ha hreq, instanceOfSchema_of_admits ha henv,
    storeReads_decisionEntities hv henv p.event, _, typeIn_of_hasTypeIn harg hz⟩

/-- **For a valid policy set, a provider argument written as a Cedar expression is what Cedar
evaluates the expression to, or absent where Cedar errs**, at a decision event every check of
which passes, for an invocation of a rule whose scope holds at the request: validity types the
argument, typing makes it fit and makes the entity it reads one the store reads as supplied, and
the decision's checks make the request and the store instances of an environment the rule
admits. The provider runs, with a null, exactly where Cedar's evaluation fails. -/
theorem resolve_providerArg_of_valid {P : PolicySet} (hv : P.Valid) {rules : Policies}
    {ω : Provider.Providers} {p : TimePoint} {pr rs : EntityUID} (ha : P.Admits rules ω p pr rs)
    {q : Policy} (hq : q ∈ P.policies)
    (hs : q.ScopeHolds (p.event.request pr rs) (P.decisionEntities p.event))
    {c : Provider.Call} {F : List Guard} (hcF : (.inr c, F) ∈ q.toExpr.leafFacts [])
    {arg : Provider.Arg} (hmem : arg ∈ c.args) {x : Cedar.Spec.Expr} (harg : toArg x = some arg) :
    arg.resolve p.event =
      match Cedar.Spec.evaluate x (p.event.request pr rs) (P.decisionEntities p.event) with
      | .ok v => .value v
      | .error _ => .absent := by
  obtain ⟨env, he, hst, hsr, ty, hty⟩ := providerArg_typed hv ha hq hs hcF hmem harg
  cases hx : Cedar.Spec.evaluate x (p.event.request pr rs) (P.decisionEntities p.event) with
  | ok v =>
    exact resolve_toArg_of_typed (C := P.typingCtx env F) rfl ha.principal ha.resource
      (storeFits_decisionEntities P p.event) he hst harg hty hx
  | error err =>
    exact resolve_toArg_error_of_typed (C := P.typingCtx env F) rfl ha.principal ha.resource
      he hsr harg hty hx

/-! ## Replacing a condition -/

section

variable {θ : Leaves} {req : Request} {es : Entities}

private theorem evaluate_and_congr' {a a' b b' : Expr}
    (ha : evaluate θ a req es = evaluate θ a' req es)
    (hb : evaluate θ b req es = evaluate θ b' req es) :
    evaluate θ (.and a b) req es = evaluate θ (.and a' b') req es := by
  simp only [evaluate, ha, hb]

private theorem foldl_congr : (cs cs' : List Condition) → (acc acc' : Expr) →
    List.Forall₂ (fun c c' => evaluate θ c.toExpr req es = evaluate θ c'.toExpr req es) cs cs' →
    evaluate θ acc req es = evaluate θ acc' req es →
    evaluate θ (cs.foldl (fun expr c => .and c.toExpr expr) acc) req es =
      evaluate θ (cs'.foldl (fun expr c => .and c.toExpr expr) acc') req es
  | [], [], _, _, .nil, h => h
  | c :: cs, c' :: cs', acc, acc', .cons hc hcs, h => by
    simp only [List.foldl_cons]
    exact foldl_congr cs cs' _ _ hcs (evaluate_and_congr' hc h)

theorem forall₂_append' {α β : Type} {R : α → β → Prop} :
    {l₁ l₂ : List α} → {m₁ m₂ : List β} → List.Forall₂ R l₁ m₁ → List.Forall₂ R l₂ m₂ →
      List.Forall₂ R (l₁ ++ l₂) (m₁ ++ m₂)
  | [], _, [], _, .nil, h => h
  | _ :: _, _, _ :: _, _, .cons h₁ h₁', h₂ => .cons h₁ (forall₂_append' h₁' h₂)

private theorem forall₂_reverse' {α β : Type} {R : α → β → Prop} :
    {l : List α} → {m : List β} → List.Forall₂ R l m → List.Forall₂ R l.reverse m.reverse
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons h hs => by
    simp only [List.reverse_cons]
    exact forall₂_append' (forall₂_reverse' hs) (.cons h .nil)

theorem forall₂_refl' {α : Type} {R : α → α → Prop} (h : ∀ a, R a a) :
    (l : List α) → List.Forall₂ R l l
  | [] => .nil
  | a :: l => .cons (h a) (forall₂_refl' h l)

/-- Conditions that evaluate alike, one by one, evaluate alike together. -/
theorem evaluate_conditions_congr {cs cs' : Conditions}
    (h : List.Forall₂ (fun c c' => evaluate θ c.toExpr req es = evaluate θ c'.toExpr req es)
      cs cs') :
    evaluate θ (Conditions.toExpr cs) req es = evaluate θ (Conditions.toExpr cs') req es := by
  unfold Conditions.toExpr
  have hr := forall₂_reverse' h
  generalize cs.reverse = l at hr ⊢
  generalize cs'.reverse = l' at hr ⊢
  cases hr with
  | nil => rfl
  | cons hc hcs => exact foldl_congr _ _ _ _ hcs hc

/-- A condition whose body evaluates as another's evaluates as it, whatever its kind. -/
theorem evaluate_condition_congr {k : Cedar.Spec.ConditionKind} {x x' : Expr}
    (h : evaluate θ x req es = evaluate θ x' req es) :
    evaluate θ (Condition.toExpr ⟨k, x⟩) req es = evaluate θ (Condition.toExpr ⟨k, x'⟩) req es := by
  cases k <;> simp only [Condition.toExpr, evaluate, h]

/-- **A rule with a condition replaced by one that evaluates alike evaluates alike.** -/
theorem evaluate_withCondition_congr {q : Policy} {pre post : Conditions} {c c' : Condition}
    (h : evaluate θ c.toExpr req es = evaluate θ c'.toExpr req es) :
    evaluate θ (q.withCondition pre c post).toExpr req es =
      evaluate θ (q.withCondition pre c' post).toExpr req es := by
  have hconds : List.Forall₂ (fun c c' => evaluate θ c.toExpr req es = evaluate θ c'.toExpr req es)
      (pre ++ c :: post) (pre ++ c' :: post) := by
    exact forall₂_append' (forall₂_refl' (R := fun (c c' : Condition) =>
      evaluate θ c.toExpr req es = evaluate θ c'.toExpr req es) (fun _ => rfl) _)
      (.cons h (forall₂_refl' (R := fun (c c' : Condition) => evaluate θ c.toExpr req es =
        evaluate θ c'.toExpr req es) (fun _ => rfl) _))
  simp only [Policy.withCondition, Policy.toExpr]
  exact evaluate_and_congr' rfl (evaluate_and_congr' rfl (evaluate_and_congr' rfl
    (evaluate_conditions_congr hconds)))

/-- The facts the conditions establish, in order, when each evaluates to `true`. -/
def condFacts (cs : Conditions) : List Guard := cs.flatMap (·.toExpr.facts)

/-- The facts a rule's scope establishes, when it holds. -/
def scopeFacts (q : Policy) : List Guard :=
  (Expr.ofCedar q.principalScope.toExpr).facts ++ (Expr.ofCedar q.actionScope.toExpr).facts ++
    (Expr.ofCedar q.resourceScope.toExpr).facts

theorem scopeFacts_hold (θ : Leaves) {q : Policy} (hs : q.ScopeHolds req es) :
    ∀ g ∈ scopeFacts q, g.HoldsIn req es := by
  intro g hg
  simp only [scopeFacts, List.mem_append] at hg
  rcases hg with (hg | hg) | hg
  · exact facts_hold (θ := θ) _ (by rw [evaluate_ofCedar]; exact hs.1) g hg
  · exact facts_hold (θ := θ) _ (by rw [evaluate_ofCedar]; exact hs.2.1) g hg
  · exact facts_hold (θ := θ) _ (by rw [evaluate_ofCedar]; exact hs.2.2) g hg

theorem evaluate_and_congr_right {a b b' : Expr}
    (h : evaluate θ a req es = .ok (.prim (.bool true)) →
      evaluate θ b req es = evaluate θ b' req es) :
    evaluate θ (.and a b) req es = evaluate θ (.and a b') req es := by
  simp only [evaluate]
  cases ha : (evaluate θ a req es).as Bool with
  | error e => rfl
  | ok b₁ =>
    cases b₁ with
    | false => rfl
    | true => simp [h (as_bool_true ha)]

/-- A condition is evaluated only where the conditions before it evaluate to `true`, and so
where their facts hold. -/
theorem evaluate_conditions_congr_facts {c c' : Condition} {post : Conditions} :
    (pre : Conditions) → ((∀ g ∈ condFacts pre, g.HoldsIn req es) →
      evaluate θ c.toExpr req es = evaluate θ c'.toExpr req es) →
    evaluate θ (Conditions.toExpr (pre ++ c :: post)) req es =
      evaluate θ (Conditions.toExpr (pre ++ c' :: post)) req es
  | [], h => evaluate_conditions_congr (.cons (h (by simp [condFacts]))
      (forall₂_refl' (R := fun (c c' : Condition) =>
        evaluate θ c.toExpr req es = evaluate θ c'.toExpr req es) (fun _ => rfl) _))
  | d :: pre, h => by
    simp only [List.cons_append]
    rw [conditions_toExpr_cons _ _ (by simp), conditions_toExpr_cons _ _ (by simp)]
    refine evaluate_and_congr_right fun hd => evaluate_conditions_congr_facts pre fun hF => h ?_
    intro g hg
    simp only [condFacts, List.flatMap_cons, List.mem_append] at hg
    rcases hg with hg | hg
    · exact facts_hold _ hd g hg
    · exact hF g (by simpa [condFacts] using hg)

/-- **A rule's condition is evaluated only where the rule's scope holds and the facts of the
conditions before it hold**: replacing it by one that evaluates alike there changes nothing. -/
theorem evaluate_withCondition_congr_scope {q : Policy} {pre post : Conditions}
    {c c' : Condition}
    (h : q.ScopeHolds req es → (∀ g ∈ condFacts pre, g.HoldsIn req es) →
      evaluate θ c.toExpr req es = evaluate θ c'.toExpr req es) :
    evaluate θ (q.withCondition pre c post).toExpr req es =
      evaluate θ (q.withCondition pre c' post).toExpr req es := by
  simp only [Policy.withCondition, Policy.toExpr]
  refine evaluate_and_congr_right fun h₁ => evaluate_and_congr_right fun h₂ =>
    evaluate_and_congr_right fun h₃ => evaluate_conditions_congr_facts pre (h ?_)
  rw [evaluate_ofCedar] at h₁ h₂ h₃
  exact ⟨h₁, h₂, h₃⟩

/-- Rules that evaluate alike, one by one, with the same ids and effects, authorize alike. -/
theorem isAuthorized_congr_evaluate {ps ps' : Policies}
    (h : List.Forall₂ (fun p p' => p.id = p'.id ∧ p.effect = p'.effect ∧
      evaluate θ p.toExpr req es = evaluate θ p'.toExpr req es) ps ps') :
    isAuthorized θ req es ps = isAuthorized θ req es ps' := by
  have herr : ps.filterMap (errored θ · req es) = ps'.filterMap (errored θ · req es) := by
    induction h with
    | nil => rfl
    | @cons p p' _ _ hp _ ih =>
      obtain ⟨hid, -, hev⟩ := hp
      have hone : errored θ p req es = errored θ p' req es := by
        unfold errored hasError
        rw [hev, hid]
      rw [List.filterMap_cons, List.filterMap_cons, ih, hone]
  have hsat : ∀ eff, ps.filterMap (satisfiedWithEffect θ eff · req es) =
      ps'.filterMap (satisfiedWithEffect θ eff · req es) := by
    intro eff
    clear herr
    induction h with
    | nil => rfl
    | @cons p p' _ _ hp _ ih =>
      obtain ⟨hid, heff, hev⟩ := hp
      have hone : satisfiedWithEffect θ eff p req es = satisfiedWithEffect θ eff p' req es := by
        unfold satisfiedWithEffect satisfied
        rw [hev, hid, heff]
      rw [List.filterMap_cons, List.filterMap_cons, ih, hone]
  unfold isAuthorized satisfiedPolicies errorPolicies
  rw [hsat, hsat, herr]

end

/-! ## Over a trace -/

/-- The leaves of a rule whose condition `ofCedar e` is replaced by `temporal { φ }` are the
rule's and `φ`. -/
theorem mem_leaves_replace {q : Policy} {pre post : Conditions} {k : Cedar.Spec.ConditionKind}
    {e : Cedar.Spec.Expr} {φ : Formula} {l : Leaf} :
    l ∈ (q.withCondition pre ⟨k, .temporal φ⟩ post).toExpr.leaves ↔
      l ∈ (q.withCondition pre ⟨k, Expr.ofCedar e⟩ post).toExpr.leaves ∨ l = .inl φ := by
  have h₀ : (Condition.toExpr ⟨k, Expr.ofCedar e⟩).leaves = [] := by
    cases k <;> simp [Condition.toExpr, Expr.leaves, leaves_ofCedar]
  have h₁ : (Condition.toExpr ⟨k, .temporal φ⟩).leaves = [.inl φ] := by
    cases k <;> simp [Condition.toExpr, Expr.leaves]
  simp only [mem_leaves_toExpr, Policy.withCondition, List.mem_append, List.mem_cons]
  constructor
  · rintro ⟨c, hc | rfl | hc, hl⟩
    · exact .inl ⟨c, .inl hc, hl⟩
    · rw [h₁, List.mem_singleton] at hl; exact .inr hl
    · exact .inl ⟨c, .inr (.inr hc), hl⟩
  · rintro (⟨c, hc | rfl | hc, hl⟩ | rfl)
    · exact ⟨c, .inl hc, hl⟩
    · rw [h₀] at hl; cases hl
    · exact ⟨c, .inr (.inr hc), hl⟩
    · exact ⟨_, .inr (.inl rfl), by rw [h₁]; exact List.mem_singleton_self _⟩

theorem mem_leafFacts_conditions {φ : Formula} {k : Cedar.Spec.ConditionKind} {post : Conditions} :
    (pre : Conditions) → (F : List Guard) →
      ∃ F', ((.inl φ : Leaf), F') ∈
          (Conditions.toExpr (pre ++ ⟨k, .temporal φ⟩ :: post)).leafFacts F ∧
        ∀ g ∈ F', g ∈ F ∨ g ∈ condFacts pre
  | [], F => by
    refine ⟨F, ?_, fun g hg => .inl hg⟩
    have hc : ((.inl φ : Leaf), F) ∈ (Condition.toExpr ⟨k, .temporal φ⟩).leafFacts F := by
      cases k <;> simp [Condition.toExpr, Expr.leafFacts]
    cases post with
    | nil => simpa [Conditions.toExpr] using hc
    | cons d post =>
      rw [List.nil_append, conditions_toExpr_cons _ _ (by simp)]
      simp only [Expr.leafFacts, List.mem_append]
      exact .inl hc
  | d :: pre, F => by
    rw [List.cons_append, conditions_toExpr_cons _ _ (by simp)]
    obtain ⟨F', hm, hF'⟩ := mem_leafFacts_conditions (φ := φ) (k := k) (post := post) pre
      (F ++ d.toExpr.facts)
    refine ⟨F', ?_, fun g hg => ?_⟩
    · simp only [Expr.leafFacts, List.mem_append]
      exact .inr hm
    · simp only [condFacts, List.flatMap_cons, List.mem_append] at hF' ⊢
      rcases hF' g hg with (hg | hg) | hg
      · exact .inl hg
      · exact .inr (.inl hg)
      · exact .inr (.inr hg)

/-- The temporal leaf of a rule's replaced condition sits where the facts of the rule's scope and
of the conditions before it are established. -/
theorem mem_leafFacts_withCondition {q : Policy} {pre post : Conditions}
    {k : Cedar.Spec.ConditionKind} {φ : Formula} :
    ∃ F, ((.inl φ : Leaf), F) ∈ (q.withCondition pre ⟨k, .temporal φ⟩ post).toExpr.leafFacts [] ∧
      ∀ g ∈ F, g ∈ scopeFacts q ∨ g ∈ condFacts pre := by
  obtain ⟨F, hm, hF⟩ := mem_leafFacts_conditions (φ := φ) (k := k) (post := post) pre
    ([] ++ (Expr.ofCedar q.principalScope.toExpr).facts ++
      (Expr.ofCedar q.actionScope.toExpr).facts ++ (Expr.ofCedar q.resourceScope.toExpr).facts)
  refine ⟨F, ?_, fun g hg => ?_⟩
  · simp only [Policy.withCondition, Policy.toExpr, Expr.leafFacts, List.mem_append]
    exact .inr (.inr (.inr hm))
  · rcases hF g hg with hg | hg
    · exact .inl (by simpa [scopeFacts] using hg)
    · exact .inr hg

theorem mem_providerCalls' {ps : Policies} {c : Provider.Call} :
    c ∈ Policies.providerCalls ps ↔ ∃ p ∈ ps, Sum.inr c ∈ p.toExpr.leaves := by
  simp only [Policies.providerCalls, List.mem_flatMap, List.mem_filterMap]
  constructor
  · rintro ⟨p, hp, l, hl, hlc⟩
    cases l with
    | inl _ => cases hlc
    | inr c' => simp only [Option.some.injEq] at hlc; subst hlc; exact ⟨p, hp, hl⟩
  · rintro ⟨p, hp, hl⟩
    exact ⟨p, hp, _, hl, rfl⟩

private theorem calls_mem_iff {qs₁ qs₂ : Policies} {q : Policy} {pre post : Conditions}
    {k : Cedar.Spec.ConditionKind} {e : Cedar.Spec.Expr} {φ : Formula} (c : Provider.Call) :
    c ∈ Policies.providerCalls (qs₁ ++ q.withCondition pre ⟨k, .temporal φ⟩ post :: qs₂) ↔
      c ∈ Policies.providerCalls (qs₁ ++ q.withCondition pre ⟨k, Expr.ofCedar e⟩ post :: qs₂) := by
  rw [mem_providerCalls', mem_providerCalls']
  simp only [List.mem_append, List.mem_cons]
  constructor
  · rintro ⟨p, hp | rfl | hp, hl⟩
    · exact ⟨p, .inl hp, hl⟩
    · rcases (mem_leaves_replace (e := e)).mp hl with hl | hl
      · exact ⟨_, .inr (.inl rfl), hl⟩
      · cases hl
    · exact ⟨p, .inr (.inr hp), hl⟩
  · rintro ⟨p, hp | rfl | hp, hl⟩
    · exact ⟨p, .inl hp, hl⟩
    · exact ⟨_, .inr (.inl rfl), (mem_leaves_replace (e := e)).mpr (.inl hl)⟩
    · exact ⟨p, .inr (.inr hp), hl⟩

theorem any_congr_mem {α : Type} {l₁ l₂ : List α} (f : α → Bool)
    (h : ∀ x, x ∈ l₁ ↔ x ∈ l₂) : l₁.any f = l₂.any f := by
  rw [Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
  exact ⟨fun ⟨x, hx, hf⟩ => ⟨x, (h x).mp hx, hf⟩, fun ⟨x, hx, hf⟩ => ⟨x, (h x).mpr hx, hf⟩⟩

theorem all_congr_mem {α : Type} {l₁ l₂ : List α} (f : α → Bool)
    (h : ∀ x, x ∈ l₁ ↔ x ∈ l₂) : l₁.all f = l₂.all f := by
  rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  exact ⟨fun hf x hx => hf x ((h x).mpr hx), fun hf x hx => hf x ((h x).mp hx)⟩

/-- The outcome depends on the scope entities the rules read only at the decision's event. -/
theorem decideWith_rules_congr_at {P : PolicySet} {rules₁ rules₂ : Policies}
    {ω : Provider.Providers} {σ : Trace} {n : Nat}
    {respond : Event → EntityUID → EntityUID → Option Cedar.Spec.Response}
    (h₁ : ∀ e, rules₁.providersFail ω e = rules₂.providersFail ω e)
    (h₂ : ∀ e, P.providerOutputsConform rules₁ ω e = P.providerOutputsConform rules₂ ω e)
    (h₃ : ∀ p pr rs, σ[n]? = some p → p.event.principal = some pr →
      p.event.resource = some rs →
      P.scopeEntitiesSupplied rules₁ p.event pr rs = P.scopeEntitiesSupplied rules₂ p.event pr rs) :
    P.decideWith rules₁ ω σ n respond = P.decideWith rules₂ ω σ n respond := by
  unfold PolicySet.decideWith
  cases hσ : σ[n]? with
  | none => rfl
  | some p =>
    simp only [h₁, h₂]
    cases hpr : p.event.principal with
    | none => rfl
    | some pr =>
      cases hrs : p.event.resource with
      | none => rfl
      | some rs => simp only [h₃ p pr rs hσ hpr hrs]

/-- **Writing a Cedar condition as a temporal leaf changes no decision**: replacing a condition
`ofCedar e` of a rule by `temporal { φ }`, where `φ` is `e`'s translation, gives the same outcome
at a timepoint of a trace, under every reading, where every admitted decision event at which the
condition is evaluated (the rule's scope holds, and the facts of the conditions before it) evaluates
`e` to a `Bool` within the temporal sub-language (`Fits`), and where the decision event supplies
the scope entities whose attributes the translation reads when the rule's scope holds. Without
that last hypothesis the leaf can make the decision fail closed where Cedar decides
(`authorize_toTemporal_missing`). -/
theorem authorize_toTemporal {ι : ImplChoices} {P : PolicySet} {ω : Provider.Providers}
    {σ : Trace} {n : Nat} {qs₁ qs₂ : Policies} {q : Policy} {pre post : Conditions}
    {k : Cedar.Spec.ConditionKind} {e : Cedar.Spec.Expr} {φ : Formula}
    (hφ : toTemporal e = some φ)
    (hps : P.policies = qs₁ ++ q.withCondition pre ⟨k, Expr.ofCedar e⟩ post :: qs₂)
    (hsup : ∀ p pr rs, σ[n]? = some p → p.event.principal = some pr →
      p.event.resource = some rs →
      q.ScopeHolds (p.event.request pr rs) (P.decisionEntities p.event) →
      ∀ r ∈ φ.scopeReads, p.event.supplies r = true)
    (hok : ∀ p pr rs, σ[n]? = some p → P.Admits P.policies ω p pr rs →
      q.ScopeHolds (p.event.request pr rs) (P.decisionEntities p.event) →
      (∀ g ∈ condFacts pre, g.HoldsIn (p.event.request pr rs) (P.decisionEntities p.event)) →
      Fits (p.event.request pr rs) (P.decisionEntities p.event) e ∧
        ∃ b, Cedar.Spec.evaluate e (p.event.request pr rs) (P.decisionEntities p.event) =
          .ok (.prim (.bool b))) :
    ({ P with policies := qs₁ ++ q.withCondition pre ⟨k, .temporal φ⟩ post :: qs₂ } :
      PolicySet).authorize ι ω σ n = P.authorize ι ω σ n := by
  have hinj := toTemporal_injectPins (S := P.schema) e φ hφ
  unfold PolicySet.authorize
  show P.decideWith (qs₁ ++ q.withCondition pre ⟨k, .temporal φ⟩ post :: qs₂) ω σ n _ =
    P.decideWith P.policies ω σ n _
  rw [hps]
  rw [decideWith_rules_congr_at
    (rules₂ := qs₁ ++ q.withCondition pre ⟨k, Expr.ofCedar e⟩ post :: qs₂)
    (fun ev => ?_) (fun ev => ?_) (fun p pr rs hσ hpr hrs => ?_)]
  · refine decideWith_congr rfl fun p pr rs hσ ha => ?_
    simp only [PolicySet.respond]
    refine supervaluate_congr fun ι' _ => ?_
    rw [hps]
    apply isAuthorized_congr_evaluate
    refine forall₂_append' ?_ (.cons ?_ ?_)
    · exact forall₂_refl' (fun _ => ⟨rfl, rfl, rfl⟩) _
    rotate_left
    · exact forall₂_refl' (fun _ => ⟨rfl, rfl, rfl⟩) _
    refine ⟨rfl, rfl, evaluate_withCondition_congr_scope fun hs hpre =>
      evaluate_condition_congr ?_⟩
    obtain ⟨hfit, b, he⟩ := hok p pr rs hσ (hps ▸ ha) hs hpre
    rw [evaluate_ofCedar]
    show evaluate (P.leaves ι' ω σ n p.event) (.temporal φ) (p.event.request pr rs)
        (P.decisionEntities p.event) =
      Cedar.Spec.evaluate e (p.event.request pr rs) (P.decisionEntities p.event)
    rw [he]
    simp only [evaluate]
    rw [leaves_toTemporal hσ ha.principal ha.resource hφ hfit he]
  · unfold Policies.providersFail
    exact any_congr_mem _ (calls_mem_iff (e := e))
  · unfold PolicySet.providerOutputsConform
    exact all_congr_mem _ (calls_mem_iff (e := e))
  · simp only [PolicySet.scopeEntitiesSupplied, List.all_append, List.all_cons]
    congr 2
    have hscope : (q.withCondition pre ⟨k, .temporal φ⟩ post).scopeHolds =
        (q.withCondition pre ⟨k, Expr.ofCedar e⟩ post).scopeHolds := rfl
    rw [hscope]
    cases hsh : (q.withCondition pre ⟨k, Expr.ofCedar e⟩ post).scopeHolds
      (p.event.request pr rs) (P.decisionEntities p.event) with
    | false => rfl
    | true =>
      simp only [Bool.not_true, Bool.false_or]
      rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
      constructor
      · intro h l hl
        exact h l ((mem_leaves_replace (e := e)).mpr (.inl hl))
      · intro h l hl
        rcases (mem_leaves_replace (e := e)).mp hl with hl | rfl
        · exact h l hl
        · simp only [hinj, List.all_eq_true]
          exact hsup p pr rs hσ hpr hrs (scopeHolds_iff.mp hsh)

/-- **A leaf that reads an unsupplied scope entity fails the decision closed.** At a decision event
that passes the checks before the scope-entity check, where the rule's scope holds, and that does
not supply a scope entity whose attributes the translation reads, the policy set with the leaf
fails closed (`missingScopeEntity`), whatever Cedar decides: there, Cedar's attribute read errs,
and the rule is skipped, with its error reported. -/
theorem authorize_toTemporal_missing {ι : ImplChoices} {P : PolicySet} {ω : Provider.Providers}
    {σ : Trace} {n : Nat} {qs₁ qs₂ : Policies} {q : Policy} {pre post : Conditions}
    {k : Cedar.Spec.ConditionKind} {e : Cedar.Spec.Expr} {φ : Formula}
    (hφ : toTemporal e = some φ) {p : TimePoint} {pr rs : EntityUID} (hσ : σ[n]? = some p)
    (hk : P.schema.isDecisionKind p.event.kind = true) (hpr : p.event.principal = some pr)
    (hrs : p.event.resource = some rs) (hconf : p.event.Conforms P.actionSchema P.schema)
    (hreq : succeeds (Cedar.Validation.validateRequest P.actionSchema (p.event.request pr rs)) =
      true)
    (hent : succeeds (Cedar.Validation.validateEntities P.actionSchema
      (P.decisionEntities p.event)) = true)
    (hs : q.ScopeHolds (p.event.request pr rs) (P.decisionEntities p.event)) {r : ScopeRoot}
    (hr : r ∈ φ.scopeReads) (hmiss : p.event.supplies r = false) :
    ({ P with policies := qs₁ ++ q.withCondition pre ⟨k, .temporal φ⟩ post :: qs₂ } :
      PolicySet).authorize ι ω σ n = .failClosed .missingScopeEntity := by
  have hsc : P.scopeEntitiesSupplied (qs₁ ++ q.withCondition pre ⟨k, .temporal φ⟩ post :: qs₂)
      p.event pr rs = false := by
    rw [Bool.eq_false_iff]
    intro h
    unfold PolicySet.scopeEntitiesSupplied at h
    have hq := List.all_eq_true.mp h (q.withCondition pre ⟨k, .temporal φ⟩ post)
      (List.mem_append_right _ (List.mem_cons_self ..))
    rw [show (q.withCondition pre ⟨k, .temporal φ⟩ post).scopeHolds (p.event.request pr rs)
        (P.decisionEntities p.event) = true from scopeHolds_iff.mpr hs] at hq
    simp only [Bool.not_true, Bool.false_or, List.all_eq_true] at hq
    have hl := hq (.inl φ) ((mem_leaves_replace (e := e)).mpr (.inr rfl))
    simp only [toTemporal_injectPins e φ hφ, List.all_eq_true] at hl
    rw [hl r hr] at hmiss
    cases hmiss
  unfold PolicySet.authorize
  show P.decideWith (qs₁ ++ q.withCondition pre ⟨k, .temporal φ⟩ post :: qs₂) ω σ n _ = _
  simp [PolicySet.decideWith, hσ, hk, hpr, hrs, hconf, hreq, hent, hsc]

theorem toTerm_not_varies {E : List VarName} :
    (x : Cedar.Spec.Expr) → (t : Term) → toTerm x = some t → ¬ t.Varies E
  | .lit p, t, h => by
    cases p <;> simp only [toTerm, Option.some.injEq] at h <;> subst h <;> simp [Term.Varies]
  | .var v, t, h => by
    cases v <;> simp only [toTerm, Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
      simp [Term.Varies]
  | .getAttr x a, t, h => by
    obtain ⟨p, rfl⟩ | ⟨r, p, rfl⟩ := attrTerm_shape h <;> simp [Term.Varies]
  | .call _ _, t, h => by
    obtain ⟨s, -, -, rfl⟩ := toTerm_call h
    simp [Term.Varies]
  | .binaryApp .add x y, t, h | .binaryApp .sub x y, t, h | .binaryApp .mul x y, t, h => by
    simp only [toTerm, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨tx, htx, ty, hty, rfl⟩ := h
    simp [Term.Varies, toTerm_not_varies x tx htx, toTerm_not_varies y ty hty]
  | .ite .., _, h | .and .., _, h | .or .., _, h | .unaryApp .., _, h
  | .binaryApp .eq .., _, h | .binaryApp .mem .., _, h | .binaryApp .hasTag .., _, h
  | .binaryApp .getTag .., _, h | .binaryApp .less .., _, h | .binaryApp .lessEq .., _, h
  | .binaryApp .contains .., _, h | .binaryApp .containsAll .., _, h
  | .binaryApp .containsAny .., _, h | .hasAttr .., _, h | .extHasAttr .., _, h | .set .., _, h
  | .record .., _, h => by simp [toTerm] at h

theorem toTemporal_not_varies {E : List VarName} :
    (e : Cedar.Spec.Expr) → (φ : Formula) → toTemporal e = some φ → ¬ φ.Varies E
  | .binaryApp .eq x y, φ, h | .binaryApp .less x y, φ, h | .binaryApp .lessEq x y, φ, h => by
    simp only [toTemporal, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨tx, htx, ty, hty, rfl⟩ := h
    simp [Formula.Varies, toTerm_not_varies x tx htx, toTerm_not_varies y ty hty]
  | .and x y, φ, h | .or x y, φ, h => by
    simp only [toTemporal, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨φx, hφx, φy, hφy, rfl⟩ := h
    simp [Formula.Varies, toTemporal_not_varies x φx hφx, toTemporal_not_varies y φy hφy]
  | .unaryApp .not x, φ, h => by
    simp only [toTemporal, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨φx, hφx, rfl⟩ := h
    simp [Formula.Varies, toTemporal_not_varies x φx hφx]
  | .lit _, _, h | .var _, _, h | .ite .., _, h
  | .unaryApp .neg _, _, h | .unaryApp .isEmpty _, _, h
  | .unaryApp (.like _) _, _, h | .unaryApp (.is _) _, _, h
  | .binaryApp .mem .., _, h | .binaryApp .hasTag .., _, h
  | .binaryApp .getTag .., _, h | .binaryApp .add .., _, h
  | .binaryApp .sub .., _, h | .binaryApp .mul .., _, h
  | .binaryApp .contains .., _, h | .binaryApp .containsAll .., _, h
  | .binaryApp .containsAny .., _, h | .getAttr .., _, h
  | .hasAttr .., _, h | .extHasAttr .., _, h | .set .., _, h
  | .record .., _, h | .call .., _, h => by simp [toTemporal] at h

theorem conjuncts_ne_nil : (φ : Formula) → φ.conjuncts ≠ []
  | .and φ _ => by simp [Formula.conjuncts, conjuncts_ne_nil φ]
  | .not _ | .formerly .. | .previous .. | .since .. | .pred .. | .cmp .. | .exist .. | .tp _ => by
    simp [Formula.conjuncts]

theorem not_varies_conjuncts {E : List VarName} :
    (φ : Formula) → ¬ φ.Varies E → ∀ c ∈ φ.conjuncts, ¬ c.Varies E
  | .and φ ψ, h, c, hc => by
    simp only [Formula.Varies, not_or] at h
    simp only [Formula.conjuncts, List.mem_append] at hc
    rcases hc with hc | hc
    · exact not_varies_conjuncts φ h.1 c hc
    · exact not_varies_conjuncts ψ h.2 c hc
  | .not _, h, c, hc | .formerly .., h, c, hc | .previous .., h, c, hc | .since .., h, c, hc
  | .pred .., h, c, hc | .cmp .., h, c, hc | .exist .., h, c, hc | .tp _, h, c, hc => by
    simp only [Formula.conjuncts, List.mem_singleton] at hc
    subst hc
    exact h

/-- **A translation monitors nothing**: it reads only the decision event, so no conjunct of it
varies with the timepoint, and validation rejects it as a leaf of its own
(`PolicySet.LeafValid.monitorsTime`; guide chapter 8, §5.4, "tp-dependence"). The rule has no
semantic consequence, and `authorize_toTemporal_of_valid` assumes, of the leaf, only what typing
gives. -/
theorem toTemporal_not_monitorsTime {e : Cedar.Spec.Expr} {φ : Formula}
    (h : toTemporal e = some φ) : ¬ φ.MonitorsTime := by
  intro hm
  obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil _ (conjuncts_ne_nil φ)
  exact not_varies_conjuncts φ (toTemporal_not_varies e φ h) c hc (hm c hc).1

/-- **For a valid policy set, writing a Cedar condition as a well-typed temporal leaf changes no
decision**: for a valid policy set, replacing the condition `ofCedar e` of a rule by
`temporal { φ }`, `φ` the translation of `e`, well-typed at its position in every environment
the rule admits (as validation asks of a leaf), gives the same outcome at a timepoint of a trace,
under every reading, where the decision event supplies the scope entities the translation reads
when the rule's scope holds (`authorize_toTemporal_missing`), and where Cedar's arithmetic does
not overflow. Typing excludes the other errors where the two would differ: at a decision event
that passes the checks and evaluates the condition, a typed attribute access resolves through
records, and a typed ordering compares `Long`s, so Cedar evaluates `e` to a `Bool` that fits, or
overflows (`fits_of_wellTyped`). An overflow cannot be excluded by typing, and the temporal
arithmetic of a reading other than `error` gives it a value where Cedar errs.

The policy set with the leaf is not valid: the leaf monitors nothing
(`toTemporal_not_monitorsTime`), a rule with no semantic consequence; validity is asked of the
Cedar original, and only typing of the leaf. -/
theorem authorize_toTemporal_of_valid {ι : ImplChoices} {P : PolicySet} {ω : Provider.Providers}
    {σ : Trace} {n : Nat} {qs₁ qs₂ : Policies} {q : Policy} {pre post : Conditions}
    {k : Cedar.Spec.ConditionKind} {e : Cedar.Spec.Expr} {φ : Formula}
    (hφ : toTemporal e = some φ)
    (hps : P.policies = qs₁ ++ q.withCondition pre ⟨k, Expr.ofCedar e⟩ post :: qs₂)
    (hv : P.Valid)
    (hwt : ∀ F, ((.inl φ : Leaf), F) ∈
        (q.withCondition pre ⟨k, .temporal φ⟩ post).toExpr.leafFacts [] →
      ∀ env ∈ P.envsOf q, φ.WellTyped (P.typingCtx env F) [])
    (hsup : ∀ p pr rs, σ[n]? = some p → p.event.principal = some pr →
      p.event.resource = some rs →
      q.ScopeHolds (p.event.request pr rs) (P.decisionEntities p.event) →
      ∀ r ∈ φ.scopeReads, p.event.supplies r = true)
    (hnov : ∀ p pr rs, σ[n]? = some p → P.Admits P.policies ω p pr rs →
      q.ScopeHolds (p.event.request pr rs) (P.decisionEntities p.event) →
      (∀ g ∈ condFacts pre, g.HoldsIn (p.event.request pr rs) (P.decisionEntities p.event)) →
      Cedar.Spec.evaluate e (p.event.request pr rs) (P.decisionEntities p.event) ≠
        .error .arithBoundsError) :
    ({ P with policies := qs₁ ++ q.withCondition pre ⟨k, .temporal φ⟩ post :: qs₂ } :
      PolicySet).authorize ι ω σ n = P.authorize ι ω σ n := by
  refine authorize_toTemporal hφ hps hsup fun p pr rs hσ ha hs hpre => ?_
  obtain ⟨env, henv, hreq⟩ := request_instance ha.request
  have henvq : env ∈ P.envsOf q :=
    admits_of_scopeHolds (q := q) henv hreq (instanceOfSchema_of_admits ha henv) hs
  obtain ⟨F, hmem, hF⟩ := mem_leafFacts_withCondition (q := q) (pre := pre) (post := post) (k := k)
    (φ := φ)
  have hfacts : ∀ g ∈ F, g.Holds p.event := fun g hg =>
    holds_of_holdsIn (P := P) ha.principal ha.resource (by
      rcases hF g hg with hg | hg
      · exact scopeFacts_hold (P.leaves ι ω σ n p.event) hs g hg
      · exact hpre g hg)
  have hsupp : ∀ r ∈ φ.scopeReads, p.event.Supplies env r := fun r hr =>
    supplies_of_admits hv ha henv (hsup p pr rs hσ ha.principal ha.resource hs r hr)
  obtain ⟨hfit, hb⟩ := fits_of_wellTyped (C := P.typingCtx env F)
    (req := p.event.request pr rs) (es := P.decisionEntities p.event) rfl ha.principal
    ha.resource (instanceOf_of_admits ha hreq) hfacts (storeReads_decisionEntities hv henv p.event)
    e φ hφ (hwt F hmem env henvq) hsupp
  rcases hb with hb | hb
  · exact ⟨hfit, hb⟩
  · exact absurd hb (hnov p pr rs hσ ha hs hpre)

end Dogwood.Thm
