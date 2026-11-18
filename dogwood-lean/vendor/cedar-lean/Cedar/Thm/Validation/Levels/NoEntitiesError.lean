/-
 Copyright Cedar Contributors

 Licensed under the Apache License, Version 2.0 (the "License");
 you may not use this file except in compliance with the License.
 You may obtain a copy of the License at

      https://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software
 distributed under the License is distributed on an "AS IS" BASIS,
 WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 See the License for the specific language governing permissions and
 limitations under the License.
-/

import Cedar.Spec
import Cedar.Data
import Cedar.Validation
import Cedar.Thm.Data.Control
import Cedar.Thm.Validation.Typechecker
import Cedar.Thm.Validation.Typechecker.Types
import Cedar.Thm.Validation.Slice
import Cedar.Thm.Validation.Slice.Reachable
import Cedar.Thm.Validation.Levels.Basic
import Cedar.Thm.Validation.Levels.CheckLevel

/-!
# Level checking rules out `entityDoesNotExist` errors (issue #642)

`level_based_slicing_is_sound_expr` already proves that evaluating against the
full store agrees with evaluating against the level-`n` slice.  Issue #642 asks
for the *additional* guarantee that a level-checked, well-typed expression never
produces `Error.entityDoesNotExist` at all, given a store that is *closed* up to
that level.

Note this is genuinely a NEW hypothesis, not a consequence of well-formedness:
`InstanceOfSchema` (Typechecker/Types.lean) only constrains entries that are
*present* in the store; nothing forces an entity-typed attribute value to point
at a uid that is itself a key in `entities`.  So `principal.manager.name` can
type- and level-check while `principal.manager`'s uid is absent, and the second
`getAttr` errors with `entityDoesNotExist`.  That is exactly the gap #642 closes,
and the reason we introduce `EntitiesClosedAtLevel`.

Per @john-h-kastner-aws on the issue (2026-05-21), the property is stated as a
standalone validation pass, independent of slicing:

  `validatesAtLevel ∧ EntitiesClosedAtLevel → NoEntitiesErrors`

with the sliced variant following trivially from the existing
semantic-equivalence soundness theorem.

## The DNE surface

`Error.entityDoesNotExist` is produced in exactly three places, all in
`Spec/Entities.lean`: `Entities.attrs`, `Entities.tags`, `Entities.ancestors`
(each `findOrErr uid .entityDoesNotExist`).  In the evaluator these are reached
only via:

* `.getAttr` on an entity value  (`getAttr` → `attrsOf v es.attrs` → `Entities.attrs`)
* `.binaryApp .getTag`           (`getTag uid tag es` → `Entities.tags`)

Every other operator either short-circuits or uses the infallible `*OrEmpty`
lookups (`hasAttr`/`hasTag`/`mem`), so for them the result follows from the
inductive hypotheses alone.  Hence only `level_based_no_dne_get_attr` and the
`.getTag` branch of `level_based_no_dne_binary_app` carry real content.

## The crux (`checked_eval_entity_exists`)

`checked_eval_entity_reachable` (Slice/Reachable.lean) already places a
level-checked entity at `ReachableIn … (n + 1)`, and with its `entities.contains`
hypothesis dropped upstream it does so without presupposing existence.  Composing
that with `EntitiesClosedAtLevel` gives `checked_eval_entity_exists`, the single
lemma consumed by the two dereferencing cases (`getAttr` on an entity, `.getTag`).
Everything else is plumbing.
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

/--
`entities` is closed for `request` up to `level`: every entity reachable from
the request roots (`request.sliceEUIDs`) within `level` dereferences is present
in the store.  This is the closure condition #642 adds.

Phrased relative to the request because that is what `checked_eval_entity_reachable`
and friends produce (`ReachableIn entities request.sliceEUIDs euid (n + 1)`).
`Entities.closedAtLevel` (Spec/Slice.lean) is the executable algorithm that
decides this predicate, and `closedAtLevel_iff` proves the two equivalent, so the
guarantees below can be discharged by *running* the check on a concrete store.
-/
def EntitiesClosedAtLevel (entities : Entities) (request : Request) (level : Nat) : Prop :=
  ∀ euid, ReachableIn entities request.sliceEUIDs euid level → entities.contains euid

/--
`Entities.closedAtLevel` (the executable check) agrees with the
`EntitiesClosedAtLevel` predicate.  `Entities.closedAtLevel` reuses the reachable
set computed by the slicing algorithm (`Entities.sliceAtLevel.sliceAtLevel`), and
membership in that set coincides with `ReachableIn` (`reachable_then_mem_slice` /
`reachable_of_mem_slice`), so the algorithm checks `contains` on exactly the
entities the predicate quantifies over.
-/
theorem closedAtLevel_iff {entities : Entities} {request : Request} {n : Nat} :
  entities.closedAtLevel request n = true ↔ EntitiesClosedAtLevel entities request n
:= by
  simp only [Entities.closedAtLevel, Set.all_eq_true, EntitiesClosedAtLevel]
  constructor
  · intro h euid hr
    exact h euid (reachable_then_mem_slice hr)
  · intro h euid hmem
    exact h euid (reachable_of_mem_slice hmem)

/--
Per-expression inductive hypothesis, parallel to `TypedAtLevelIsSound`: a
level-checked, well-typed `e` evaluated against a store closed at its level does
not produce `entityDoesNotExist`.
-/
def TypedAtLevelHasNoDNEError (e : Expr) : Prop :=
  ∀ {n : Nat} {tx : TypedExpr} {c c₁ : Capabilities} {env : TypeEnv} {request : Request} {entities : Entities},
    CapabilitiesInvariant c request entities →
    InstanceOfWellFormedEnvironment request entities env →
    EntitiesClosedAtLevel entities request n →
    typeOf e c env = Except.ok (tx, c₁) →
    tx.AtLevel env n →
    evaluate e request entities ≠ .error .entityDoesNotExist

/-! ## The crux: a reachable, level-checked entity exists -/

/--
KEY LEMMA (the crux of #642).  If a level-checked, well-typed entity-access
expression evaluates to (a value yielding, via `path`) `euid`, and the store is
closed at level `n + 1`, then `euid` is present in the store.

`checked_eval_entity_reachable` (Slice/Reachable.lean) supplies
`ReachableIn entities request.sliceEUIDs euid (n + 1)` without assuming `euid`
exists (its `entities.contains` hypothesis was dropped upstream), and
`EntitiesClosedAtLevel` turns that reachability into membership.  This is the one
lemma the two dereferencing cases (`getAttr` on an entity, `.getTag`) consume.
-/
theorem checked_eval_entity_exists {e : Expr} {n nmax : Nat} {c c' : Capabilities} {tx : TypedExpr} {env : TypeEnv} {request : Request} {entities : Entities} {v : Value} {path : List Attr} {euid : EntityUID}
  (hc : CapabilitiesInvariant c request entities)
  (hr : InstanceOfWellFormedEnvironment request entities env)
  (ht : typeOf e c env = .ok (tx, c'))
  (hl : tx.EntityAccessAtLevel env n nmax path)
  (he : evaluate e request entities = .ok v)
  (ha : Value.EuidViaPath v path euid)
  (hcl : EntitiesClosedAtLevel entities request (n + 1)) :
  entities.contains euid
:= hcl euid (checked_eval_entity_reachable hc hr ht hl he ha)

/-! ## Per-operation "never DNE" helpers

The generic `bind_ne_error` workhorse (monadic bind preserves "not this error")
lives in `Thm/Data/Control.lean`; the lemmas below cover the individual
operators.
-/

/--
`apply₁` only ever yields a value, a `typeError`, or an `arithBoundsError` (via
`intOrErr`); it never produces `entityDoesNotExist`.
-/
theorem apply₁_ne_dne (op : UnaryOp) (v : Value) :
  apply₁ op v ≠ .error .entityDoesNotExist
:= by
  unfold apply₁
  split <;>
  first
  | (simp ; done)
  | (unfold intOrErr ; split <;> simp)

/--
`hasAttr` reads attributes via the infallible `attrsOrEmpty` lookup, so it never
produces `entityDoesNotExist` (at worst `typeError` for a non-record/entity
receiver).
-/
theorem has_attr_value_ne_dne (v : Value) (a : Attr) (es : Entities) :
  hasAttr v a es ≠ .error .entityDoesNotExist
:= by
  cases v <;>
  first
  | (simp [hasAttr, attrsOf] ; done)
  | (rename_i p ; cases p <;> simp [hasAttr, attrsOf])

private theorem has_attrs_loop_ne_dne (v : Value) (attrs : List Attr) (es : Entities) :
  hasAttrs.loop v attrs es ≠ .error .entityDoesNotExist := by
  induction attrs generalizing v with
  | nil => simp [hasAttrs.loop]
  | cons attr rest ih =>
    simp only [hasAttrs.loop]
    -- The result of attrsOf v (fun uid => .ok (es.attrsOrEmpty uid)) is either
    -- .ok m (for records/entities) or .error .typeError (for other values)
    match hattr : attrsOf v (fun uid => .ok (es.attrsOrEmpty uid)) with
    | .ok m =>
      simp only [ExceptT.stM_eq, ne_eq]
      match hfind : m.find? attr with
      | .some next => exact ih next
      | .none => simp
    | .error e => simp


theorem has_attrs_value_ne_dne (v : Value) (a : Attr) (attrs : List Attr) (es : Entities) :
  hasAttrs v a attrs es ≠ .error .entityDoesNotExist := by
  simp only [hasAttrs]
  exact has_attrs_loop_ne_dne v (a :: attrs) es

/--
Coercing a result to `Bool` (`Result.as Bool`) never introduces an
`entityDoesNotExist`: on success it runs `Value.asBool` (at worst `typeError`),
on failure it preserves the existing error.  Used for the boolean-guard
operators (`and`, `or`, `ite`).
-/
theorem as_bool_ne_dne {r : Result Value} (hr : r ≠ .error .entityDoesNotExist) :
  (Result.as Bool r) ≠ .error .entityDoesNotExist
:= by
  cases r
  case error e =>
    simp only [Result.as, ne_eq, Except.error.injEq] at hr ⊢
    exact hr
  case ok v =>
    cases v
    case prim p =>
      cases p <;> simp [Result.as, Coe.coe, Value.asBool]
    all_goals simp [Result.as, Coe.coe, Value.asBool]

/--
Inversion for the boolean coercion: if `Result.as Bool r = .ok b`, then `r` was
already `.ok (.prim (.bool b))`.  Lets the guard operators recover the underlying
value (needed to fire `GuardedCapabilitiesInvariant`).
-/
theorem as_bool_ok_inv {r : Result Value} {b : Bool} (h : Result.as Bool r = .ok b) :
  r = .ok (.prim (.bool b))
:= by
  cases r
  case error e =>
    simp only [Result.as, reduceCtorEq] at h
  case ok v =>
    cases v
    case prim p =>
      cases p <;> simp only [Result.as, Coe.coe, Value.asBool, Except.ok.injEq, reduceCtorEq] at h
      subst h
      rfl
    all_goals simp only [Result.as, Coe.coe, Value.asBool, reduceCtorEq] at h

/-! ## Per-operator lemmas

Trivial (IH plumbing only): lit, var, and, or, ite, unaryApp, hasAttr, set,
call, record, and the non-dereferencing / `*OrEmpty` branches of binaryApp.
Meaty (use `checked_eval_entity_exists`): `get_attr` (entity branch) and the
`.getTag` branch of `binary_app`.
-/

/--
The boolean-guard operators coerce their final `Result Bool` back to
`Result Value` via `(Value.prim ∘ Prim.bool) <$> ·`.  That functor map never
turns a non-`entityDoesNotExist` result into one.
-/
theorem map_bool_ne_dne {r : Result Bool} (hr : r ≠ .error .entityDoesNotExist) :
  ((fun b => Value.prim (Prim.bool b)) <$> r) ≠ .error .entityDoesNotExist
:= by
  cases r <;> simp_all

theorem level_based_no_dne_if {x₁ x₂ x₃ : Expr} {n : Nat} {c₀ c₁ : Capabilities} {env : TypeEnv} {request : Request} {entities : Entities}
  (hc : CapabilitiesInvariant c₀ request entities)
  (hr : InstanceOfWellFormedEnvironment request entities env)
  (hcl : EntitiesClosedAtLevel entities request n)
  (htx : typeOf (.ite x₁ x₂ x₃) c₀ env = Except.ok (tx, c₁))
  (hl : tx.AtLevel env n)
  (ih₁ : TypedAtLevelHasNoDNEError x₁)
  (ih₂ : TypedAtLevelHasNoDNEError x₂)
  (ih₃ : TypedAtLevelHasNoDNEError x₃) :
  evaluate (.ite x₁ x₂ x₃) request entities ≠ .error .entityDoesNotExist
:= by
  replace ⟨ tx₁, bty₁, c₁', tx₂, c₂, tx₃, c₃, htxeq, htx₁, hty₁, htx₂₃ ⟩ := type_of_ite_inversion htx
  have ⟨ hgc, v₁, he₁, hv₁ ⟩ := type_of_is_sound hc hr htx₁
  rw [hty₁] at hv₁
  rw [htxeq] at hl
  cases hl
  rename_i hl₁ hl₂ hl₃
  simp only [evaluate]
  apply bind_ne_error (as_bool_ne_dne (ih₁ (n := n) hc hr hcl htx₁ hl₁))
  intro b hb
  have he₁' := as_bool_ok_inv hb
  split at htx₂₃
  · have hbf : b = false := by
      simpa [he₁', instance_of_ff_is_false hv₁, EvaluatesTo] using he₁
    subst hbf
    simpa using ih₃ (n := n) hc hr hcl htx₂₃.left hl₃
  · have hbt : b = true := by
      simpa [he₁', instance_of_tt_is_true hv₁, EvaluatesTo] using he₁
    subst hbt
    simpa using ih₂ (n := n) (capability_union_invariant hc (hgc he₁')) hr hcl htx₂₃.left hl₂
  · replace ⟨ htx₂, htx₃, _, _ ⟩ := htx₂₃
    cases b
    · simpa using ih₃ (n := n) hc hr hcl htx₃ hl₃
    · simpa using ih₂ (n := n) (capability_union_invariant hc (hgc he₁')) hr hcl htx₂ hl₂

theorem level_based_no_dne_and {e₁ e₂ : Expr} {n : Nat} {c₀ c₁ : Capabilities} {env : TypeEnv} {request : Request} {entities : Entities}
  (hc : CapabilitiesInvariant c₀ request entities)
  (hr : InstanceOfWellFormedEnvironment request entities env)
  (hcl : EntitiesClosedAtLevel entities request n)
  (ht : typeOf (.and e₁ e₂) c₀ env = Except.ok (tx, c₁))
  (hl : tx.AtLevel env n)
  (ih₁ : TypedAtLevelHasNoDNEError e₁)
  (ih₂ : TypedAtLevelHasNoDNEError e₂) :
  evaluate (.and e₁ e₂) request entities ≠ .error .entityDoesNotExist
:= by
  replace ⟨ tx₁, bty₁, c₁', htx₁, hty₁, ht ⟩ := type_of_and_inversion ht
  have ⟨ hgc, v₁, he₁, hv₁ ⟩ := type_of_is_sound hc hr htx₁
  rw [hty₁] at hv₁
  simp only [evaluate]
  split at ht
  case isTrue hbty =>
    replace ⟨ ht, _ ⟩ := ht
    subst tx
    subst hbty
    replace hv₁ := instance_of_ff_is_false hv₁
    subst v₁
    apply bind_ne_error (as_bool_ne_dne (ih₁ (n := n) hc hr hcl htx₁ hl))
    intro b hb
    have he₁' := as_bool_ok_inv hb
    cases b
    · simp
    · exfalso
      rcases he₁ with h | h | h | h <;> rw [h] at he₁' <;> simp_all
  case isFalse hbty =>
    replace ⟨ bty, tx₂, bty₂, c₂, htx, htx₂, hty₂, _ ⟩ := ht
    subst tx
    cases hl
    rename_i hl₁ hl₂
    apply bind_ne_error (as_bool_ne_dne (ih₁ (n := n) hc hr hcl htx₁ hl₁))
    intro b hb
    have he₁' := as_bool_ok_inv hb
    cases b
    · simp
    · split
      · simp_all
      · exact map_bool_ne_dne (as_bool_ne_dne (ih₂ (n := n) (capability_union_invariant hc (hgc he₁')) hr hcl htx₂ hl₂))

theorem level_based_no_dne_or {e₁ e₂ : Expr} {n : Nat} {c₀ c₁ : Capabilities} {env : TypeEnv} {request : Request} {entities : Entities}
  (hc : CapabilitiesInvariant c₀ request entities)
  (hr : InstanceOfWellFormedEnvironment request entities env)
  (hcl : EntitiesClosedAtLevel entities request n)
  (ht : typeOf (.or e₁ e₂) c₀ env = Except.ok (tx, c₁))
  (hl : tx.AtLevel env n)
  (ih₁ : TypedAtLevelHasNoDNEError e₁)
  (ih₂ : TypedAtLevelHasNoDNEError e₂) :
  evaluate (.or e₁ e₂) request entities ≠ .error .entityDoesNotExist
:= by
  replace ⟨ tx₁, bty₁, c₁', htx₁, hty₁, ht ⟩ := type_of_or_inversion ht
  have ⟨ hgc, v₁, he₁, hv₁ ⟩ := type_of_is_sound hc hr htx₁
  rw [hty₁] at hv₁
  simp only [evaluate]
  split at ht
  case isTrue hbty =>
    replace ⟨ ht, _ ⟩ := ht
    subst tx
    subst hbty
    replace hv₁ := instance_of_tt_is_true hv₁
    subst v₁
    apply bind_ne_error (as_bool_ne_dne (ih₁ (n := n) hc hr hcl htx₁ hl))
    intro b hb
    have he₁' := as_bool_ok_inv hb
    cases b
    · exfalso
      rcases he₁ with h | h | h | h <;> rw [h] at he₁' <;> simp_all
    · simp
  case isFalse hbty =>
    replace ⟨ bty, tx₂, bty₂, c₂, htx, htx₂, hty₂, _ ⟩ := ht
    subst tx
    cases hl
    rename_i hl₁ hl₂
    apply bind_ne_error (as_bool_ne_dne (ih₁ (n := n) hc hr hcl htx₁ hl₁))
    intro b hb
    cases b
    · split
      · simp_all
      · exact map_bool_ne_dne (as_bool_ne_dne (ih₂ (n := n) hc hr hcl htx₂ hl₂))
    · simp

theorem level_based_no_dne_unary_app {op : UnaryOp} {e : Expr} {n : Nat} {c₀ c₁ : Capabilities} {env : TypeEnv} {request : Request} {entities : Entities}
  (hc : CapabilitiesInvariant c₀ request entities)
  (hr : InstanceOfWellFormedEnvironment request entities env)
  (hcl : EntitiesClosedAtLevel entities request n)
  (ht : typeOf (.unaryApp op e) c₀ env = Except.ok (tx, c₁))
  (hl : tx.AtLevel env n)
  (ihe : TypedAtLevelHasNoDNEError e) :
  evaluate (.unaryApp op e) request entities ≠ .error .entityDoesNotExist
:= by
  replace ⟨ _, tx₁, ty, c₁', htx, htx₁, ht ⟩ := type_of_unary_inversion ht
  subst tx
  cases hl
  rename_i hl₁
  simp only [evaluate]
  exact bind_ne_error (ihe hc hr hcl htx₁ hl₁) (fun v _ => apply₁_ne_dne op v)

/--
Meaty (`.getTag` branch).  For `op = .getTag` the evaluator calls
`getTag uid tag es` which dereferences `Entities.tags` and can DNE; that branch
mirrors `get_attr` below (`checked_eval_entity_exists` shows the entity is
present).  All other binary operators are non-dereferencing or use `*OrEmpty`
(`.mem`, `.hasTag`), so they follow from the inductive hypotheses.
-/

theorem apply₂_ne_dne_of_not_getTag {op : BinaryOp} (hop : op ≠ .getTag) (v₁ v₂ : Value) (es : Entities) :
  apply₂ op v₁ v₂ es ≠ .error .entityDoesNotExist
:= by
  cases op
  case getTag => exact absurd rfl hop
  all_goals
    unfold apply₂
    split <;>
    first
    | (simp ; done)
    | contradiction
    | (unfold intOrErr ; split <;> simp)
    | (unfold inₛ Set.mapOrErr ; split <;> simp)
    | (simp [hasTag] ; done)

theorem level_based_no_dne_binary_app {op : BinaryOp} {e₁ e₂ : Expr} {n : Nat} {c₀ c₁ : Capabilities} {env : TypeEnv} {request : Request} {entities : Entities}
  (hc : CapabilitiesInvariant c₀ request entities)
  (hr : InstanceOfWellFormedEnvironment request entities env)
  (hcl : EntitiesClosedAtLevel entities request n)
  (ht : typeOf (.binaryApp op e₁ e₂) c₀ env = Except.ok (tx, c₁))
  (hl : tx.AtLevel env n)
  (ihe₁ : TypedAtLevelHasNoDNEError e₁)
  (ihe₂ : TypedAtLevelHasNoDNEError e₂) :
  evaluate (.binaryApp op e₁ e₂) request entities ≠ .error .entityDoesNotExist
:= by
  replace ⟨ tx₁, c₁', tx₂, c₂', htx₁, htx₂, ty, htxeq ⟩ := type_of_binaryApp_inversion ht
  subst htxeq
  simp only [evaluate]
  cases hl
  case getTag hel hl₁ hl₂ =>
    apply bind_ne_error (ihe₁ (n := hel + 1) hc hr hcl htx₁ (entity_access_at_level_then_at_level hl₁))
    intro v₁ hv₁eq
    apply bind_ne_error (ihe₂ (n := hel + 1) hc hr hcl htx₂ hl₂)
    intro v₂ hv₂eq
    cases v₁ <;> cases v₂ <;>
    first
    | (simp [apply₂] ; done)
    | ( rename_i p₁ p₂
        cases p₁ <;> cases p₂ <;>
        first
        | (simp [apply₂] ; done)
        | ( rename_i uid tag
            have hcont := checked_eval_entity_exists hc hr htx₁ hl₁ hv₁eq (.euid uid) hcl
            obtain ⟨ ed, hed ⟩ := Map.contains_iff_some_find?.mp hcont
            simp only [apply₂, getTag, Entities.tags, Map.findOrErr, hed, Except.bind_ok]
            split <;> simp ) )
  case hasTag hel hl₁ hl₂ =>
    apply bind_ne_error (ihe₁ (n := hel + 1) hc hr hcl htx₁ (entity_access_at_level_then_at_level hl₁))
    intro v₁ hv₁eq
    apply bind_ne_error (ihe₂ (n := hel + 1) hc hr hcl htx₂ hl₂)
    intro v₂ hv₂eq
    exact apply₂_ne_dne_of_not_getTag (by decide) v₁ v₂ entities
  case mem hel hl₁ hl₂ =>
    apply bind_ne_error (ihe₁ (n := hel + 1) hc hr hcl htx₁ (entity_access_at_level_then_at_level hl₁))
    intro v₁ hv₁eq
    apply bind_ne_error (ihe₂ (n := hel + 1) hc hr hcl htx₂ hl₂)
    intro v₂ hv₂eq
    exact apply₂_ne_dne_of_not_getTag (by decide) v₁ v₂ entities
  case binaryApp hop hl₁ hl₂ =>
    apply bind_ne_error (ihe₁ (n := n) hc hr hcl htx₁ hl₁)
    intro v₁ hv₁eq
    apply bind_ne_error (ihe₂ (n := n) hc hr hcl htx₂ hl₂)
    intro v₂ hv₂eq
    exact apply₂_ne_dne_of_not_getTag (by rintro rfl; simp only [DereferencingBinaryOp, not_true_eq_false] at hop) v₁ v₂ entities

/--
Entity branch.  `getAttr (entity euid) a es = es.attrs euid >>= (·.findOrErr a attrDoesNotExist)`,
which DNEs iff `euid ∉ es`.  By soundness `e` evaluates to an entity (or errors,
in which case the IH rules out a DNE error and the remaining error kinds are not
`entityDoesNotExist`).  When it evaluates to `entity euid`, `checked_eval_entity_exists`
shows `euid` is present in the store, so the outer lookup yields at worst
`attrDoesNotExist`, never `entityDoesNotExist`.
-/
theorem level_based_no_dne_get_attr_entity {e : Expr} {tx₁ : TypedExpr} {ty : CedarType} {ety : EntityType} {a : Attr} {n : Nat} {c₀ c₁ : Capabilities} {env : TypeEnv} {request : Request} {entities : Entities}
  (hc : CapabilitiesInvariant c₀ request entities)
  (hr : InstanceOfWellFormedEnvironment request entities env)
  (hcl : EntitiesClosedAtLevel entities request n)
  (hl : (tx₁.getAttr a ty).AtLevel env n)
  (ht : typeOf e c₀ env = Except.ok (tx₁, c₁))
  (hety : tx₁.typeOf = CedarType.entity ety)
  (ihe : TypedAtLevelHasNoDNEError e) :
  evaluate (.getAttr e a) request entities ≠ .error .entityDoesNotExist
:= by
  have ⟨ hgc, v, he, hv ⟩ := type_of_is_sound hc hr ht
  rw [hety] at hv
  replace ⟨ euid, hety', hv ⟩ := instance_of_entity_type_is_entity hv
  subst hety' hv
  cases hl
  case getAttrRecord hnety _ =>
    specialize hnety euid.ty
    contradiction
  rename_i n hel₁ hl₁ _
  simp only [evaluate]
  have hl₁' := entity_access_at_level_then_at_level hl₁
  unfold EvaluatesTo at he
  rcases he with he | he | he | he
  · exact absurd he (ihe hc hr hcl ht hl₁')
  · simp [he]
  · simp [he]
  · have hcont := checked_eval_entity_exists hc hr ht hl₁ he (.euid euid) hcl
    obtain ⟨ ed, hed ⟩ := Map.contains_iff_some_find?.mp hcont
    simp only [he, Except.bind_ok, getAttr, attrsOf, Entities.attrs, Map.findOrErr, hed]
    split <;> simp

/--
Record branch.  No entity is dereferenced, so the outer lookup is a record
projection (`attrDoesNotExist` at worst).  Only the inner expression `e` could
DNE, and the IH rules that out.
-/
theorem level_based_no_dne_get_attr_record {e : Expr} {tx₁ : TypedExpr} {ty : CedarType} {rty : RecordType} {a : Attr} {n : Nat} {c₀ c₁ : Capabilities} {env : TypeEnv} {request : Request} {entities : Entities}
  (hc : CapabilitiesInvariant c₀ request entities)
  (hr : InstanceOfWellFormedEnvironment request entities env)
  (hcl : EntitiesClosedAtLevel entities request n)
  (hl : (tx₁.getAttr a ty).AtLevel env n)
  (ht : typeOf e c₀ env = Except.ok (tx₁, c₁))
  (hrty : tx₁.typeOf = CedarType.record rty)
  (ihe : TypedAtLevelHasNoDNEError e) :
  evaluate (.getAttr e a) request entities ≠ .error .entityDoesNotExist
:= by
  cases hl
  case getAttr hety =>
    simp [hety] at hrty
  rename_i hl₁
  simp only [evaluate]
  have ⟨ hgc, v, he, hi ⟩ := type_of_is_sound hc hr ht
  unfold EvaluatesTo at he
  rcases he with he | he | he | he
  · exact absurd he (ihe hc hr hcl ht hl₁)
  · simp [he]
  · simp [he]
  · rw [hrty] at hi
    obtain ⟨ attrs, hv ⟩ := instance_of_record_type_is_record hi
    subst hv
    simp only [he, Except.bind_ok, getAttr, attrsOf, Map.findOrErr]
    split <;> simp

/--
Meaty case.  Dispatches on whether the receiver has entity or record type
(`type_of_getAttr_inversion`); the entity branch is where `entityDoesNotExist`
can fire and where `EntitiesClosedAtLevel` is consumed.
-/
theorem level_based_no_dne_get_attr {e : Expr} {a : Attr} {n : Nat} {c₀ c₁ : Capabilities} {env : TypeEnv} {request : Request} {entities : Entities}
  (hc : CapabilitiesInvariant c₀ request entities)
  (hr : InstanceOfWellFormedEnvironment request entities env)
  (hcl : EntitiesClosedAtLevel entities request n)
  (ht : typeOf (e.getAttr a) c₀ env = Except.ok (tx, c₁))
  (hl : tx.AtLevel env n)
  (ihe : TypedAtLevelHasNoDNEError e) :
  evaluate (.getAttr e a) request entities ≠ .error .entityDoesNotExist
:= by
  have ⟨ _, tx₁, c₁', ht', h₅, h₆ ⟩ := type_of_getAttr_inversion ht
  rw [h₅] at hl
  cases h₆
  case inl hety =>
    obtain ⟨ ety, hety ⟩ := hety
    exact level_based_no_dne_get_attr_entity hc hr hcl hl ht' hety ihe
  case inr hrty =>
    obtain ⟨ rty, hrty ⟩ := hrty
    exact level_based_no_dne_get_attr_record hc hr hcl hl ht' hrty ihe

theorem level_based_no_dne_has_attr {e : Expr} {a : Attr} {n : Nat} {c₀ c₁ : Capabilities} {env : TypeEnv} {request : Request} {entities : Entities}
  (hc : CapabilitiesInvariant c₀ request entities)
  (hr : InstanceOfWellFormedEnvironment request entities env)
  (hcl : EntitiesClosedAtLevel entities request n)
  (ht : typeOf (e.hasAttr a) c₀ env = Except.ok (tx, c₁))
  (hl : tx.AtLevel env n)
  (ihe : TypedAtLevelHasNoDNEError e) :
  evaluate (.hasAttr e a) request entities ≠ .error .entityDoesNotExist
:= by
  have ⟨ _, tx₁, c₁', ht', h₅, _ ⟩ := type_of_hasAttr_inversion ht
  rw [h₅] at hl
  simp only [evaluate]
  refine bind_ne_error ?_ (fun v _ => has_attr_value_ne_dne v a entities)
  apply ihe hc hr hcl ht'
  cases hl
  · exact entity_access_at_level_then_at_level (by assumption)
  · assumption

theorem level_based_no_dne_ext_has_attr {e : Expr} {a : Attr} {attrs : List Attr} {n : Nat} {c₀ c₁ : Capabilities} {env : TypeEnv} {request : Request} {entities : Entities}
  (hc : CapabilitiesInvariant c₀ request entities)
  (hr : InstanceOfWellFormedEnvironment request entities env)
  (hcl : EntitiesClosedAtLevel entities request n)
  (ht : typeOf (e.extHasAttr a attrs) c₀ env = Except.ok (tx, c₁))
  (hl : tx.AtLevel env n)
  (ihe : TypedAtLevelHasNoDNEError e) :
  evaluate (.extHasAttr e a attrs) request entities ≠ .error .entityDoesNotExist
:= by
  -- Extract sub-expression typing from extHasAttr typing
  simp only [typeOf, bind, Except.bind] at ht
  generalize hte : typeOf e c₀ env = res_e at ht
  cases res_e with
  | error => simp at ht
  | ok val_e =>
    obtain ⟨ty₁, c₁'⟩ := val_e
    simp only at ht
    -- After the first bind, the remaining binds produce tx = .extHasAttr ty₁ a attrs (.bool bty)
    have htx : ∃ bty, tx = TypedExpr.extHasAttr ty₁ a attrs (.bool bty) := by
      revert ht
      generalize typeOfExtHasAttr ty₁ e (a :: attrs) c₀ env = res_ext
      intro ht
      cases res_ext with
      | error => simp only [ExceptT.stM_eq, reduceCtorEq] at ht
      | ok val_ext =>
        simp only [ok, Except.ok.injEq, Prod.mk.injEq] at ht
        exact ⟨val_ext.1, ht.1.symm⟩
    obtain ⟨bty, htx⟩ := htx
    rw [htx] at hl
    -- evaluate (.extHasAttr e a attrs) = evaluate e >>= hasAttrs · a attrs entities
    simp only [evaluate]
    refine bind_ne_error ?_ (fun v _ => has_attrs_value_ne_dne v a attrs entities)
    -- Show evaluate e ≠ .error .entityDoesNotExist using ihe
    apply ihe hc hr hcl hte
    -- Extract sub-expression level from hl
    cases hl with
    | extHasAttr _ _ _ _ _ hl₁ _ hk =>
      apply entity_access_at_level_then_at_level (path := [])
      have bump : ∀ m n nmax path, m ≤ n →
          ty₁.EntityAccessAtLevel env m nmax path → ty₁.EntityAccessAtLevel env n nmax path := by
        intro m n nmax path hmn h
        induction hmn with
        | refl => exact h
        | step _ ih => exact entity_access_at_level_succ ih
      exact bump _ _ _ _ (Nat.sub_le _ _) hl₁
    | extHasAttrRecord _ _ _ _ _ hl₁ _ _ => exact hl₁
    | extHasAttrRecordEntity _ _ _ _ _ _ _ hl₁ _ _ _ _ => exact hl₁

theorem level_based_no_dne_set {xs : List Expr} {n : Nat} {c₀ c₁ : Capabilities} {env : TypeEnv} {request : Request} {entities : Entities}
  (hc : CapabilitiesInvariant c₀ request entities)
  (hr : InstanceOfWellFormedEnvironment request entities env)
  (hcl : EntitiesClosedAtLevel entities request n)
  (ht : typeOf (.set xs) c₀ env = Except.ok (tx, c₁))
  (hl : tx.AtLevel env n)
  (ih : ∀ x ∈ xs, TypedAtLevelHasNoDNEError x) :
  evaluate (.set xs) request entities ≠ .error .entityDoesNotExist
:= by
  replace ⟨ _, txs, ty, htx, ht ⟩ := type_of_set_inversion ht
  subst tx
  cases hl
  rename_i hl
  simp only [evaluate, xs.mapM₁_eq_mapM (evaluate · request entities)]
  apply bind_ne_error _ (fun vs _ => by simp)
  intro hmapm
  obtain ⟨ x, hx, hxe ⟩ := List.mapM_error_implies_exists_error hmapm
  replace ⟨ tx', _, htxs, htxe, _ ⟩ := ht x hx
  exact (ih x hx (n := n) hc hr hcl htxe (hl tx' htxs)) hxe

theorem level_based_no_dne_call {xfn : ExtFun} {xs : List Expr} {n : Nat} {c₀ c₁ : Capabilities} {env : TypeEnv} {request : Request} {entities : Entities}
  (hc : CapabilitiesInvariant c₀ request entities)
  (hr : InstanceOfWellFormedEnvironment request entities env)
  (hcl : EntitiesClosedAtLevel entities request n)
  (ht : typeOf (.call xfn xs) c₀ env = Except.ok (tx, c₁))
  (hl : tx.AtLevel env n)
  (ih : ∀ x ∈ xs, TypedAtLevelHasNoDNEError x) :
  evaluate (.call xfn xs) request entities ≠ .error .entityDoesNotExist
:= by
  replace ⟨ txs, ⟨ ty, hty ⟩, ht ⟩ := type_of_call_inversion ht
  subst tx
  cases hl
  rename_i hl
  simp only [evaluate, xs.mapM₁_eq_mapM (evaluate · request entities)]
  apply bind_ne_error _ (fun vs _ => by
    unfold Cedar.Spec.call
    split <;> first | (simp ; done) | (unfold Cedar.Spec.res ; split <;> simp))
  intro hmapm
  obtain ⟨ x, hx, hxe ⟩ := List.mapM_error_implies_exists_error hmapm
  replace ⟨ tx', htxs, c', htxe ⟩ := List.forall₂_implies_all_left ht x hx
  exact (ih x hx (n := n) hc hr hcl htxe (hl tx' htxs)) hxe

theorem level_based_no_dne_record {rxs : List (Attr × Expr)} {n : Nat} {c₀ c₁ : Capabilities} {env : TypeEnv} {request : Request} {entities : Entities}
  (hc : CapabilitiesInvariant c₀ request entities)
  (hr : InstanceOfWellFormedEnvironment request entities env)
  (hcl : EntitiesClosedAtLevel entities request n)
  (ht : typeOf (.record rxs) c₀ env = Except.ok (tx, c₁))
  (hl : tx.AtLevel env n)
  (ih : ∀ x ∈ rxs, TypedAtLevelHasNoDNEError x.snd) :
  evaluate (.record rxs) request entities ≠ .error .entityDoesNotExist
:= by
  replace ⟨ hc₁, atxs, htx, hatxs ⟩ := type_of_record_inversion ht
  subst htx
  cases hl
  rename_i hl
  simp only [evaluate, bindAttr, pure, Except.pure]
  simp only [List.mapM₂_eq_mapM (fun x : Attr × Expr => evaluate x.snd request entities >>= fun v => Except.ok (x.fst, v))]
  apply bind_ne_error _ (fun avs _ => by simp)
  intro hmapm
  obtain ⟨ x, hx, hxe ⟩ := List.mapM_error_implies_exists_error hmapm
  replace ⟨ atx, hatx_mem, _, c', htxe ⟩ := List.forall₂_implies_all_left hatxs x hx
  have key : (evaluate x.snd request entities >>= fun v => Except.ok (x.fst, v)) ≠ .error .entityDoesNotExist :=
    bind_ne_error (ih x hx (n := n) hc hr hcl htxe (hl atx hatx_mem)) (fun v _ => by simp)
  exact key hxe

/-! ## Top-level theorem

Mirrors `level_based_slicing_is_sound_expr`: structural recursion on `e`
dispatching to the per-operator lemmas, with the same `sizeOf` bookkeeping for
the `set`/`call`/`record` inductive-hypothesis builders.
-/

theorem level_based_no_dne_expr {e : Expr} {n : Nat} {tx : TypedExpr} {c c₁ : Capabilities} {env : TypeEnv} {request : Request} {entities : Entities}
  (hc : CapabilitiesInvariant c request entities)
  (hr : InstanceOfWellFormedEnvironment request entities env)
  (hcl : EntitiesClosedAtLevel entities request n)
  (ht : typeOf e c env = Except.ok (tx, c₁))
  (hl : tx.AtLevel env n) :
  evaluate e request entities ≠ .error .entityDoesNotExist
:= by
  cases e
  case lit => simp [evaluate]
  case var v => cases v <;> simp [evaluate]
  case ite x₁ x₂ x₃ =>
    have ih₁ := @level_based_no_dne_expr x₁
    have ih₂ := @level_based_no_dne_expr x₂
    have ih₃ := @level_based_no_dne_expr x₃
    exact level_based_no_dne_if hc hr hcl ht hl ih₁ ih₂ ih₃
  case and e₁ e₂ =>
    have ih₁ := @level_based_no_dne_expr e₁
    have ih₂ := @level_based_no_dne_expr e₂
    exact level_based_no_dne_and hc hr hcl ht hl ih₁ ih₂
  case or e₁ e₂ =>
    have ih₁ := @level_based_no_dne_expr e₁
    have ih₂ := @level_based_no_dne_expr e₂
    exact level_based_no_dne_or hc hr hcl ht hl ih₁ ih₂
  case unaryApp op e =>
    have ihe := @level_based_no_dne_expr e
    exact level_based_no_dne_unary_app hc hr hcl ht hl ihe
  case binaryApp op e₁ e₂ =>
    have ih₁ := @level_based_no_dne_expr e₁
    have ih₂ := @level_based_no_dne_expr e₂
    exact level_based_no_dne_binary_app hc hr hcl ht hl ih₁ ih₂
  case getAttr e _ =>
    have ihe := @level_based_no_dne_expr e
    exact level_based_no_dne_get_attr hc hr hcl ht hl ihe
  case hasAttr e _ =>
    have ihe := @level_based_no_dne_expr e
    exact level_based_no_dne_has_attr hc hr hcl ht hl ihe
  case extHasAttr e _ _ =>
    have ihe := @level_based_no_dne_expr e
    exact level_based_no_dne_ext_has_attr hc hr hcl ht hl ihe
  case set xs =>
    have ih : ∀ x ∈ xs, TypedAtLevelHasNoDNEError x := by
      intro x hx
      have _ : sizeOf x < sizeOf (Expr.set xs) := by
        have h₁ := List.sizeOf_lt_of_mem hx
        simp only [Expr.set.sizeOf_spec]
        omega
      exact @level_based_no_dne_expr x
    exact level_based_no_dne_set hc hr hcl ht hl ih
  case call xfn xs =>
    have ih : ∀ x ∈ xs, TypedAtLevelHasNoDNEError x := by
      intro x hx
      have _ : sizeOf x < sizeOf (Expr.set xs) := by
        have h₁ := List.sizeOf_lt_of_mem hx
        simp only [Expr.set.sizeOf_spec]
        omega
      exact @level_based_no_dne_expr x
    exact level_based_no_dne_call hc hr hcl ht hl ih
  case record rxs =>
    have ih : ∀ x ∈ rxs, TypedAtLevelHasNoDNEError x.snd := by
      intro x hx
      have _ : sizeOf x.snd < sizeOf (Expr.record rxs) := by
        have h₁ := List.sizeOf_lt_of_mem hx
        rw [Prod.mk.sizeOf_spec] at h₁
        simp only [Expr.record.sizeOf_spec]
        omega
      exact @level_based_no_dne_expr x.snd
    exact level_based_no_dne_record hc hr hcl ht hl ih
termination_by e

/-! ## Policy- and validator-level wrappers

Mirror `typecheck_policy_with_level_is_sound` /
`validate_with_level_is_sound_wf`, threading `EntitiesClosedAtLevel` through to
the top-level expression theorem.  Stubbed until the expression theorem is
complete.
-/

theorem typecheck_policy_with_level_no_dne {p : Policy} {tx : TypedExpr} {n : Nat} {env : TypeEnv} {request : Request} {entities : Entities}
  (hr : InstanceOfWellFormedEnvironment request entities env)
  (hcl : EntitiesClosedAtLevel entities request n)
  (htl : typecheckPolicyWithLevel p n env = .ok tx) :
  evaluate p.toExpr request entities ≠ .error .entityDoesNotExist
:= by
  simp only [typecheckPolicyWithLevel, typecheckPolicy] at htl
  split at htl <;> try contradiction
  rename_i tx' _ htx'
  cases htl₁ : tx'.typeOf ⊑ .bool .anyBool <;> simp only [htl₁, Bool.false_eq_true, ↓reduceIte, Except.bind_err, Except.bind_ok, reduceCtorEq] at htl
  split at htl <;> simp only [reduceCtorEq, Except.ok.injEq] at htl
  subst htl
  rename_i htl'
  have subst_pres := (@substitute_action_preserves_evaluation · · entities)
  rw [←subst_pres, action_matches_env hr]
  rw [←level_spec] at htl'
  exact level_based_no_dne_expr (empty_capabilities_invariant request entities) hr hcl htx' htl'

end Cedar.Thm
