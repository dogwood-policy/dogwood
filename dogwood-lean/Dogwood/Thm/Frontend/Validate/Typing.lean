import Dogwood.Thm.Frontend.Validate.Interface
import Dogwood.Thm.TypingDecide

/-!
# The validator's temporal checks are sound for typing

`leaf_wellTyped`: a temporal leaf on which the temporal dialect of the frontend's validator
(`Dogwood.Frontend.Validate.leafFindings`) reports nothing, which passed the crate's parse-time
checks (`parseChecked`) and has no `context` term with an empty path (`noEmptyContextF`), is
well-typed (`Formula.WellTyped`) in every request environment of its rule, in a typing context
of the specification that sees the environment as the crate's validator does (`ViewAgrees`).

The crate checks a leaf in several passes, each a walk of the condition; the proof gathers what
each pass says of a sub-condition (`FOk`, and `TOk` for a comparison operand) and builds the
typing derivation by induction on the condition (`formula_wt`, `term_wt`):

* the event-name check gives each predicate a signature and each argument a declared field;
* the path checks resolve each request-side path, and the optional-read rule guards each optional
  attribute along it, with a fact that the specification's context also has
  (`pathType?_of_descend`); a scope path resolves on the environment's entity type
  (`resolveOne_of_resolveScopePath`);
* the type checks, run in the environment with the variables the specification binds and the
  action's input fields after them, type each comparison, `tp`, and predicate argument;
* the binder rules make each binder list well-formed, so the specification binds what the crate
  does (`domainSorts_of`, `binder_sort`), and the summand rule types each `sum`;
* the pin rule types each pin's request-side path, required (`pinsTyped_of`);
* the window check bounds each window.

The parse-time checks give the rest: every variable is bound, no binder is reserved, aggregates
and compounds are operands only, and each `sum` adds a binder of its own `for` list. The crate's
temporal grammar has no bare `context` term, which the specification does not type and the
crate's checks pass over; `noEmptyContextF` states that.
-/

namespace Dogwood.Thm.Frontend

open Dogwood.Frontend Dogwood.Frontend.Validate
open Dogwood.Spec (Path)
open Dogwood.Spec.Temporal
open Dogwood.Eval (acceptsB withinB)
open Cedar.Validation (CedarType Schema ActionSchemaEntry RecordType QualifiedType TypeEnv)
open Cedar.Spec (Attr EntityUID EntityType)

/-! ## Bindings -/

theorem lookup_append_of_isSome {Γ Δ : Bindings} {x : VarName} (h : (Γ.lookup x).isSome) :
    (Γ ++ Δ).lookup x = Γ.lookup x := by
  unfold Bindings.lookup at *
  rw [List.find?_append]
  cases hf : Γ.find? (·.1 == x) with
  | none => rw [hf] at h; simp at h
  | some p => rfl

theorem lookup_cons (x y : VarName) (τ : TType) (Γ : Bindings) :
    Bindings.lookup ((y, τ) :: Γ) x = if y = x then some τ else Γ.lookup x := by
  unfold Bindings.lookup
  by_cases h : y = x <;> simp [h]

/-- In a list of binders with distinct names, the reversed list finds a name where the list does. -/
theorem find?_reverse_of_nodup (x : VarName) : (dom : List Binder) → (dom.map (·.name)).Nodup →
    dom.reverse.find? (·.name == x) = dom.find? (·.name == x)
  | [], _ => rfl
  | a :: t, hnd => by
    simp only [List.map_cons, List.nodup_cons] at hnd
    rw [List.reverse_cons, List.find?_append, find?_reverse_of_nodup x t hnd.2, List.find?_cons]
    by_cases ha : a.name = x
    · have hnone : t.find? (·.name == x) = none := by
        rw [List.find?_eq_none]
        intro b hb hbx
        exact hnd.1 (ha ▸ List.mem_map.mpr ⟨b, hb, by simpa using hbx⟩)
      simp [hnone, ha]
    · have : (a.name == x) = false := by simpa using ha
      simp [this]

/-- The bindings a binder list makes, looked up. -/
theorem lookup_binderBindings (dom : List Binder) (Γ : Bindings) (x : VarName) :
    (binderBindings dom ++ Γ).lookup x =
      ((dom.find? (·.name == x)).map (annotationSort ·.ty)).or (Γ.lookup x) := by
  unfold Bindings.lookup binderBindings
  rw [List.find?_append, Option.map_or, List.find?_map, Option.map_map]
  rfl

/-- A list every element of which is missing from the prefix before it has distinct elements. -/
theorem nodup_of_take {l : List String}
    (h : ∀ i (hi : i < l.length), (l.take i).contains l[i] = false) : l.Nodup := by
  rw [List.nodup_iff_pairwise_ne, List.pairwise_iff_getElem]
  intro i j hi hj hij heq
  have hj' := h j hj
  have hmem : l[j] ∈ l.take j := List.mem_take_iff_getElem.mpr ⟨i, by omega, heq⟩
  simp at hj'
  exact hj' hmem

/-! ## Paths -/

/-- `pathType?` reads the record only at the path's head. -/
theorem pathType?_congr {present : Path → Bool} {R R' : RecordType} {pre : Path} {h : Attr}
    {rest : Path} (hf : R.find? h = R'.find? h) :
    pathType? present R pre (h :: rest) = pathType? present R' pre (h :: rest) := by
  simp only [pathType?, hf]

/-- A path that resolves, every optional attribute along which is guarded, has its type in the
specification, where every guard the crate's validator saw at a path of this head holds. -/
theorem pathType?_of_descend {present guarded : Path → Bool} {h : Attr} :
    ∀ (rest : Path) (R : RecordType) (pre : Path) (ty : CedarType),
      (pre ++ rest).head? = some h →
      (∀ q, (pre ++ q).head? = some h → guarded (pre ++ q) = true → present (pre ++ q) = true) →
      rest ≠ [] → descend (.record R) rest = .resolved ty →
      unguardedOptional guarded R pre rest = none →
      pathType? present R pre rest = some ty
  | [], _, _, _, _, _, hne, _, _ => absurd rfl hne
  | s :: rest, R, pre, ty, hh, hpg, _, hd, hu => by
    cases hq : R.find? s with
    | none => simp [descend, hq] at hd
    | some q =>
      simp only [descend, hq] at hd
      have hok : (q.isRequired || guarded (pre ++ [s])) = true := by
        cases hr : q.isRequired <;> cases hg : guarded (pre ++ [s]) <;>
          simp_all [unguardedOptional]
      have hu' : (match rest, q.getType with
          | [], _ => none
          | _ :: _, .record rty => unguardedOptional guarded rty (pre ++ [s]) rest
          | _ :: _, _ => none) = none := by
        have hnot : (!q.isRequired && !guarded (pre ++ [s])) = false := by
          cases hr : q.isRequired <;> cases hg : guarded (pre ++ [s]) <;> simp_all
        simp only [unguardedOptional, hq, hnot] at hu
        exact hu
      have hreq : (q.isRequired || present (pre ++ [s])) = true := by
        cases hr : q.isRequired
        · rw [hr, Bool.false_or] at hok
          exact hpg [s] (by cases pre <;> simp_all) hok
        · rfl
      simp only [pathType?, hq, hreq, if_true]
      cases rest with
      | nil => simp only [descend] at hd; cases hd; rfl
      | cons s' rest' =>
        cases hT : q.getType with
        | record R' =>
          rw [hT] at hd hu'
          simp only at hu' ⊢
          refine pathType?_of_descend (h := h) (s' :: rest') R' (pre ++ [s]) ty
            (by rw [List.append_assoc]; exact hh) (fun q' hq' hg => ?_) (by simp) hd hu'
          rw [List.append_assoc] at hq' hg ⊢
          exact hpg ([s] ++ q') hq' hg
        | _ => rw [hT] at hd; simp [descend] at hd

/-- A path every attribute along which is required has its type in the specification, guarded or
not. -/
theorem pathType?_of_required {present : Path → Bool} :
    ∀ (p : Path) (R : RecordType) (pre : Path) (ty : CedarType),
      requiredPathType? R p = some ty → pathType? present R pre p = some ty
  | [], _, _, _, h => by simp [requiredPathType?] at h
  | [last], R, pre, ty, h => by
    simp only [requiredPathType?] at h
    split at h
    · rename_i t hf
      cases h
      simp [pathType?, hf, Cedar.Validation.Qualified.isRequired, Cedar.Validation.Qualified.getType]
    · cases h
  | seg :: s' :: rest, R, pre, ty, h => by
    simp only [requiredPathType?] at h
    split at h
    · rename_i rty hf
      simp only [pathType?, hf, Cedar.Validation.Qualified.isRequired, Bool.true_or, if_true,
        Cedar.Validation.Qualified.getType]
      exact pathType?_of_required (s' :: rest) rty (pre ++ [seg]) ty h
    · cases h

/-- `resolve_one`'s descent is `descend`. -/
theorem resolveOne_go_eq : ∀ (T : CedarType) (rest : List String) (ty : CedarType),
    resolveOne.go T rest = .ok ty → descend T rest = .resolved ty
  | T, [], ty, h => by simp [resolveOne.go] at h; subst h; rfl
  | .record R, s :: rest, ty, h => by
    simp only [resolveOne.go] at h
    simp only [descend]
    cases hq : R.find? s with
    | none => rw [hq] at h; cases h
    | some q => rw [hq] at h; exact resolveOne_go_eq q.getType rest ty h
  | .bool _, _ :: _, _, h | .int, _ :: _, _, h | .string, _ :: _, _, h | .entity _, _ :: _, _, h
  | .set _, _ :: _, _, h | .ext _, _ :: _, _, h => by simp [resolveOne.go] at h


/-! ## No empty context path

The crate's temporal grammar has no bare `context` term: a `context.<path>` term has a non-empty
path. The specification types `context.<path>` only for a non-empty one. -/

/-! ## The walk's nodes -/

mutual

/-- The nodes the crate's walk visits. -/
def nodesF : Formula → List Formula
  | .and φ ψ => .and φ ψ :: (nodesF φ ++ nodesF ψ)
  | .since φ w ψ => .since φ w ψ :: (nodesF φ ++ nodesF ψ)
  | .not φ => .not φ :: nodesF φ
  | .formerly w φ => .formerly w φ :: nodesF φ
  | .previous w φ => .previous w φ :: nodesF φ
  | .exist x φ => .exist x φ :: nodesF φ
  | .pred a k args => [.pred a k args]
  | .cmp op l r => .cmp op l r :: (nodesT l ++ nodesT r)
  | .tp x => [.tp x]

def nodesT : Term → List Formula
  | .agg a => nodesA a
  | .arith _ l r => nodesT l ++ nodesT r
  | _ => []

def nodesA : Aggregate → List Formula
  | .count _ body | .sum _ _ body => nodesF body

end

mutual

theorem walkF_eq (f : Formula → List String) : (ψ : Formula) → walkF f ψ = (nodesF ψ).flatMap f
  | .and φ ψ => by simp [walkF, nodesF, walkF_eq f φ, walkF_eq f ψ]
  | .since φ w ψ => by simp [walkF, nodesF, walkF_eq f φ, walkF_eq f ψ]
  | .not φ => by simp [walkF, nodesF, walkF_eq f φ]
  | .formerly w φ => by simp [walkF, nodesF, walkF_eq f φ]
  | .previous w φ => by simp [walkF, nodesF, walkF_eq f φ]
  | .exist x φ => by simp [walkF, nodesF, walkF_eq f φ]
  | .pred a k args => by simp [walkF, nodesF]
  | .cmp op l r => by simp [walkF, nodesF, walkT_eq f l, walkT_eq f r]
  | .tp x => by simp [walkF, nodesF]

theorem walkT_eq (f : Formula → List String) : (t : Term) → walkT f t = (nodesT t).flatMap f
  | .agg a => by simp [walkT, nodesT, walkA_eq f a]
  | .arith _ l r => by simp [walkT, nodesT, walkT_eq f l, walkT_eq f r]
  | .entity _ | .long _ | .decimal _ | .string _ | .bool _ | .context _ | .scope _ _ | .var _
  | .wildcard => by simp [walkT, nodesT]

theorem walkA_eq (f : Formula → List String) : (a : Aggregate) → walkA f a = (nodesA a).flatMap f
  | .count _ body | .sum _ _ body => by simp [walkA, nodesA, walkF_eq f body]

end

theorem walkF_nil (f : Formula → List String) (ψ : Formula) :
    walkF f ψ = [] ↔ ∀ n ∈ nodesF ψ, f n = [] := by
  rw [walkF_eq, List.flatMap_eq_nil_iff]

/-! ## The merge of the environments' findings -/

theorem mergeEnvFindings_foldl {α : Type} (f : α → List String) :
    ∀ (envs : List α) (acc : List String),
      envs.foldl (fun acc e => acc ++ eraseEach (f e) acc) acc = [] ↔
        acc = [] ∧ ∀ e ∈ envs, f e = []
  | [], acc => by simp
  | e :: es, acc => by
    rw [List.foldl_cons, mergeEnvFindings_foldl f es]
    constructor
    · rintro ⟨h, hes⟩
      obtain ⟨rfl, hd⟩ := List.append_eq_nil_iff.mp h
      simp only [eraseEach, List.foldl_nil] at hd
      refine ⟨rfl, fun e' he' => ?_⟩
      rcases List.mem_cons.mp he' with rfl | he'
      · exact hd
      · exact hes e' he'
    · rintro ⟨rfl, hall⟩
      refine ⟨?_, fun e' he' => hall e' (List.mem_cons_of_mem _ he')⟩
      simp [eraseEach, hall e List.mem_cons_self]

/-- The merged findings are none exactly when no environment reports one. -/
theorem mergeEnvFindings_eq_nil_iff {α : Type} (envs : List α) (f : α → List String) :
    mergeEnvFindings envs f = [] ↔ ∀ e ∈ envs, f e = [] := by
  unfold mergeEnvFindings
  rw [mergeEnvFindings_foldl]
  simp

/-! ## The setting -/

/-- The term checks the walk makes, for the environment's action. -/
def termChecks (C : LeafCtx) (e : ReqEnv) (decl : List Binder) (t : Term) : List String :=
  entityAt C.schema C.declaredEnum t ++ decimalAt t ++ pathsAt C e.uid e.entry t ++ summandAt decl t

/-- The checks the walk makes at a node, for the environment's action. -/
def nodeChecks (C : LeafCtx) (e : ReqEnv) (decl : List Binder) (n : Formula) : List String :=
  windowsAt C n ++ wildcardAt n ++ (nodeTerms n).flatMap (termChecks C e decl)

/-- The specification's typing context, the leaf's checking context, and one of its request
environments, related. -/
structure Setting (C : LeafCtx) (C' : TypingCtx) (e : ReqEnv) : Prop where
  view : ViewAgrees C' C e
  act : (e.uid, e.entry) ∈ C.actions
  principal : e.principal ∈ admittedTypes C.schema e.entry .principal C.principal
  resource : e.resource ∈ admittedTypes C.schema e.entry .resource C.resource

/-- The bindings the crate's type environment has when the specification's are `Γ`. -/
abbrev portBindings (e : ReqEnv) (Γ : Bindings) : Bindings := Γ ++ inputBindings e.entry

/-- What the crate's checks and the parse-time checks say of a sub-condition, with the
specification's bindings `Γ` and the validity rules' binders `sc` in scope. -/
structure FOk (C : LeafCtx) (e : ReqEnv) (decl : List Binder) (Γ : Bindings) (sc : List Binder)
    (ψ : Formula) : Prop where
  names : eventNamesF C.events ψ = none
  nodes : ∀ n ∈ nodesF ψ, nodeChecks C e decl n = []
  types : typesF C.schema C.events e (portBindings e Γ) ψ = []
  valid : validityF C sc ψ = []
  noRes : noReservedF ψ = true
  placed : wellPlacedF ψ = true
  own : summandsOwnF ψ = true
  noEmpty : noEmptyContextF ψ = true
  closed : ∀ y ∈ ψ.fv, (Γ.lookup y).isSome
  scope : ∀ x, (sc.find? (·.name == x)).map (annotationSort ·.ty) = Γ.lookup x

/-- What they say of a comparison operand. -/
structure TOk (C : LeafCtx) (e : ReqEnv) (decl : List Binder) (Γ : Bindings) (sc : List Binder)
    (t : Term) : Prop where
  names : eventNamesT C.events t = none
  nodes : ∀ n ∈ nodesT t, nodeChecks C e decl n = []
  atoms : ∀ u ∈ termAtoms t, termChecks C e decl u = [] ∧ optionalAt C u = []
  notWild : t ≠ .wildcard
  arith : operandArith C.schema e (portBindings e Γ) t = []
  types : typesT C.schema C.events e (portBindings e Γ) t = []
  forList : forListAt t = []
  binderTys : binderTypesAt C.schema t = []
  valid : validityT C sc t = []
  noRes : noReservedT t = true
  placed : wellPlacedT t = true
  own : summandsOwnT t = true
  noEmpty : noEmptyContextT t = true
  closed : ∀ y ∈ t.fv, (Γ.lookup y).isSome
  scope : ∀ x, (sc.find? (·.name == x)).map (annotationSort ·.ty) = Γ.lookup x
  /-- The term is not a request-side path of a type temporal conditions do not support. -/
  supp : unsupportedOperand C.schema e t = none


/-! ## Decomposing the checks -/

section

variable {C : LeafCtx} {e : ReqEnv} {decl : List Binder} {Γ : Bindings} {sc : List Binder}

theorem FOk.and {φ ψ : Formula} (h : FOk C e decl Γ sc (.and φ ψ)) :
    FOk C e decl Γ sc φ ∧ FOk C e decl Γ sc ψ := by
  obtain ⟨hn, hN, hT, hV, h1, h2, h3, h4, hc, hs⟩ := h
  simp only [eventNamesF, Option.or_eq_none_iff, typesF, List.append_eq_nil_iff, validityF,
    noReservedF, wellPlacedF, summandsOwnF, noEmptyContextF, Bool.and_eq_true, Formula.fv,
    List.mem_append, nodesF, List.mem_cons] at *
  exact ⟨⟨hn.1, fun n hn' => hN n (.inr (.inl hn')), hT.1, hV.1.2, h1.1, h2.1, h3.1, h4.1,
      fun y hy => hc y (.inl hy), hs⟩,
    ⟨hn.2, fun n hn' => hN n (.inr (.inr hn')), hT.2, hV.2, h1.2, h2.2, h3.2, h4.2,
      fun y hy => hc y (.inr hy), hs⟩⟩

theorem FOk.since {φ ψ : Formula} {w : Window} (h : FOk C e decl Γ sc (.since φ w ψ)) :
    FOk C e decl Γ sc φ ∧ FOk C e decl Γ sc ψ ∧ windowProblem C w = none := by
  obtain ⟨hn, hN, hT, hV, h1, h2, h3, h4, hc, hs⟩ := h
  have hw := hN _ (List.mem_cons_self ..)
  simp only [nodeChecks, windowsAt, List.append_eq_nil_iff, Option.toList_eq_nil_iff] at hw
  simp only [eventNamesF, Option.or_eq_none_iff, typesF, List.append_eq_nil_iff, validityF,
    noReservedF, wellPlacedF, summandsOwnF, noEmptyContextF, Bool.and_eq_true, Formula.fv,
    List.mem_append, nodesF, List.mem_cons] at *
  exact ⟨⟨hn.1, fun n hn' => hN n (.inr (.inl hn')), hT.1, hV.1.2, h1.1, h2.1, h3.1, h4.1,
      fun y hy => hc y (.inl hy), hs⟩,
    ⟨hn.2, fun n hn' => hN n (.inr (.inr hn')), hT.2, hV.2, h1.2, h2.2, h3.2, h4.2,
      fun y hy => hc y (.inr hy), hs⟩, hw.1.1⟩

theorem FOk.not {φ : Formula} (h : FOk C e decl Γ sc (.not φ)) : FOk C e decl Γ sc φ := by
  obtain ⟨hn, hN, hT, hV, h1, h2, h3, h4, hc, hs⟩ := h
  simp only [eventNamesF, typesF, List.append_eq_nil_iff, validityF, noReservedF, wellPlacedF,
    summandsOwnF, noEmptyContextF, Formula.fv, nodesF, List.mem_cons] at *
  exact ⟨hn, fun n hn' => hN n (.inr hn'), hT, hV.2, h1, h2, h3, h4, hc, hs⟩

theorem FOk.formerly {φ : Formula} {w : Window} (h : FOk C e decl Γ sc (.formerly w φ)) :
    FOk C e decl Γ sc φ ∧ windowProblem C w = none := by
  obtain ⟨hn, hN, hT, hV, h1, h2, h3, h4, hc, hs⟩ := h
  have hw := hN _ (List.mem_cons_self ..)
  simp only [nodeChecks, windowsAt, List.append_eq_nil_iff, Option.toList_eq_nil_iff] at hw
  simp only [eventNamesF, typesF, List.append_eq_nil_iff, validityF, noReservedF, wellPlacedF,
    summandsOwnF, noEmptyContextF, Formula.fv, nodesF, List.mem_cons] at *
  exact ⟨⟨hn, fun n hn' => hN n (.inr hn'), hT, hV.2, h1, h2, h3, h4, hc, hs⟩, hw.1.1⟩

theorem binderTypeProblem_eq_none {S : Schema} {b : Binder} :
    binderTypeProblem S b = none ↔ binderTypeDeclared S b.ty = true := by
  unfold binderTypeProblem
  split
  · simp_all
  · split <;> simp_all

theorem comparisonProblems_eq_nil {S : Schema} {e : ReqEnv} {Γ : Bindings} {op : CmpOp}
    {l r : Term} : comparisonProblems S e Γ op l r = [] ↔
      unsupportedOperand S e l = none ∧ unsupportedOperand S e r = none ∧
        comparisonProblem S e Γ op l r = none := by
  unfold comparisonProblems
  cases unsupportedOperand S e l <;> cases unsupportedOperand S e r <;> simp

theorem FOk.previous {φ : Formula} {w : Window} (h : FOk C e decl Γ sc (.previous w φ)) :
    FOk C e decl Γ sc φ ∧ windowProblem C w = none := by
  obtain ⟨hn, hN, hT, hV, h1, h2, h3, h4, hc, hs⟩ := h
  have hw := hN _ (List.mem_cons_self ..)
  simp only [nodeChecks, windowsAt, List.append_eq_nil_iff, Option.toList_eq_nil_iff] at hw
  simp only [eventNamesF, typesF, List.append_eq_nil_iff, validityF, noReservedF, wellPlacedF,
    summandsOwnF, noEmptyContextF, Formula.fv, nodesF, List.mem_cons] at *
  exact ⟨⟨hn, fun n hn' => hN n (.inr hn'), hT, hV.2, h1, h2, h3, h4, hc, hs⟩, hw.1.1⟩

theorem FOk.exist {x : Binder} {φ : Formula} (h : FOk C e decl Γ sc (.exist x φ)) :
    binderTypeDeclared C.schema x.ty = true ∧ reservedBinderNames.contains x.name = false ∧
      FOk C e decl ((x.name, annotationSort x.ty) :: Γ) (x :: sc) φ := by
  obtain ⟨hn, hN, hT, hV, h1, h2, h3, h4, hc, hs⟩ := h
  simp only [validityF, validityAt, List.append_eq_nil_iff, Option.toList_eq_nil_iff,
    binderTypeProblem_eq_none] at hV
  have hd : binderTypeDeclared C.schema x.ty = true := by
    by_contra hd; simp [hd] at hV
  have hbt : bindersTyped C.schema [x] = true := by simp [bindersTyped, hd]
  rw [if_pos hbt] at hV
  simp only [typesF, if_pos hbt] at hT
  simp only [noReservedF, Bool.and_eq_true, Bool.not_eq_true'] at h1
  refine ⟨hd, h1.1, hn, fun n hn' => hN n (List.mem_cons_of_mem _ hn'), hT, hV.2, h1.2, h2, h3, h4,
    fun y hy => ?_, fun y => ?_⟩
  · rw [lookup_cons]
    by_cases hxy : x.name = y
    · simp [hxy]
    · rw [if_neg hxy]
      exact hc y (by simp [Formula.fv, hy, Ne.symm hxy])
  · rw [lookup_cons, List.find?_cons]
    by_cases hxy : x.name = y
    · simp [hxy]
    · have : (x.name == y) = false := by simpa using hxy
      rw [this, if_neg hxy]
      exact hs y

theorem wildcardAt_cmp {op : CmpOp} {l r : Term} (h : wildcardAt (.cmp op l r) = []) :
    l ≠ .wildcard ∧ r ≠ .wildcard := by
  constructor
  · rintro rfl; simp [wildcardAt] at h
  · rintro rfl; cases l <;> simp [wildcardAt] at h

theorem FOk.cmp {op : CmpOp} {l r : Term} (h : FOk C e decl Γ sc (.cmp op l r)) :
    TOk C e decl Γ sc l ∧ TOk C e decl Γ sc r ∧
      unsupportedOperand C.schema e l = none ∧ unsupportedOperand C.schema e r = none ∧
      comparisonProblem C.schema e (portBindings e Γ) op l r = none := by
  obtain ⟨hn, hN, hT, hV, h1, h2, h3, h4, hc, hs⟩ := h
  have hnode := hN _ (List.mem_cons_self ..)
  simp only [nodeChecks, List.append_eq_nil_iff] at hnode
  obtain ⟨⟨-, hw⟩, hatoms⟩ := hnode
  obtain ⟨hwl, hwr⟩ := wildcardAt_cmp hw
  simp only [nodeTerms, List.flatMap_append, List.append_eq_nil_iff, List.flatMap_eq_nil_iff] at hatoms
  simp only [validityF, validityAt, eraseDups_eq_nil_iff, List.append_eq_nil_iff,
    List.flatMap_append, List.flatMap_eq_nil_iff, and_assoc] at hV
  obtain ⟨hol, hor, hfl, hfr, hbl, hbr, hvl, hvr⟩ := hV
  simp only [typesF, eraseDups_eq_nil_iff, List.append_eq_nil_iff, Option.toList_eq_nil_iff,
    and_assoc] at hT
  obtain ⟨hal, har, hcp, htl, htr⟩ := hT
  simp only [eventNamesF, Option.or_eq_none_iff, noReservedF, wellPlacedF, summandsOwnF,
    noEmptyContextF, Bool.and_eq_true, Formula.fv, List.mem_append, nodesF,
    List.mem_cons] at hn h1 h2 h3 h4 hc hN
  exact ⟨⟨hn.1, fun n hn' => hN n (.inr (.inl hn')), fun u hu => ⟨hatoms.1 u hu, hol u hu⟩, hwl,
      hal, htl, hfl, hbl, hvl, h1.1, h2.1, h3.1, h4.1, fun y hy => hc y (.inl hy), hs,
      (comparisonProblems_eq_nil.mp hcp).1⟩,
    ⟨hn.2, fun n hn' => hN n (.inr (.inr hn')), fun u hu => ⟨hatoms.2 u hu, hor u hu⟩, hwr,
      har, htr, hfr, hbr, hvr, h1.2, h2.2, h3.2, h4.2, fun y hy => hc y (.inr hy), hs,
      (comparisonProblems_eq_nil.mp hcp).2.1⟩, comparisonProblems_eq_nil.mp hcp⟩

theorem operandArith_of_arithAtoms {S : Schema} {e : ReqEnv} {Γ : Bindings} {t : Term}
    (h : arithAtoms S e Γ t = []) : operandArith S e Γ t = [] := by
  cases t <;> simp_all [operandArith]

theorem ne_wildcard_of_arithAtoms {S : Schema} {e : ReqEnv} {Γ : Bindings} {t : Term}
    (h : arithAtoms S e Γ t = []) : t ≠ .wildcard := by
  rintro rfl; simp [arithAtoms] at h

/-- An atom of a compound operand the crate's checks accept is of a supported type: an unsupported
type is not `Long`, so the atom check reports it. -/
theorem supported_of_arithAtoms {S : Schema} {e : ReqEnv} {Γp : Bindings} {t : Term}
    (h : arithAtoms S e Γp t = []) : unsupportedOperand S e t = none := by
  cases hu : unsupportedOperand S e t with
  | none => rfl
  | some m =>
    exfalso
    have hτ : ∃ ty, termSort S e Γp t = some (.cedar ty) ∧ ty ≠ .int := by
      cases t with
      | context p =>
        simp only [unsupportedOperand] at hu
        split at hu
        · rename_i ty hc
          refine ⟨ty, by simp [termSort, hc], ?_⟩
          rintro rfl; simp [Cedar.Validation.CedarType.temporalSupported] at hu
        · cases hu
      | scope r p =>
        cases p with
        | nil => simp [unsupportedOperand] at hu
        | cons a p =>
          simp only [unsupportedOperand] at hu
          split at hu
          · rename_i ty hc
            refine ⟨ty, by simp [termSort, hc], ?_⟩
            rintro rfl; simp [Cedar.Validation.CedarType.temporalSupported] at hu
          · cases hu
      | _ => simp [unsupportedOperand] at hu
    obtain ⟨ty, hts, hne⟩ := hτ
    have hnw : t ≠ .wildcard := by rintro rfl; simp [unsupportedOperand] at hu
    have hna : ∀ op l r, t ≠ .arith op l r := by rintro _ _ _ rfl; simp [unsupportedOperand] at hu
    have hcase : arithAtoms S e Γp t =
        match termSort S e Γp t with
        | some (.cedar .int) | none => []
        | some τ =>
          match unsupportedOperand S e t with
          | some m => [m]
          | none => [s!"arithmetic operates only on `Long` values, but this operand has type `{renderSort τ}`"] := by
      cases t with
      | arith op l r => exact absurd rfl (hna op l r)
      | wildcard => exact absurd rfl hnw
      | _ => rfl
    rw [hcase, hts, hu] at h
    cases ty <;> first | exact hne rfl | simp at h

theorem TOk.ofArith {op : ArithOp} {l r : Term} (h : TOk C e decl Γ sc (.arith op l r)) :
    TOk C e decl Γ sc l ∧ TOk C e decl Γ sc r ∧
      arithAtoms C.schema e (portBindings e Γ) l = [] ∧
      arithAtoms C.schema e (portBindings e Γ) r = [] := by
  obtain ⟨hn, hN, hA, -, har, hT, hF, hB, hV, h1, h2, h3, h4, hc, hs⟩ := h
  simp only [operandArith, arithAtoms, List.append_eq_nil_iff] at har
  simp only [eventNamesT, Option.or_eq_none_iff, nodesT, List.mem_append, termAtoms,
    List.mem_cons, typesT, List.append_eq_nil_iff, forListAt, binderTypesAt, validityT,
    noReservedT, wellPlacedT, summandsOwnT, noEmptyContextT, Bool.and_eq_true, Term.fv] at *
  exact ⟨⟨hn.1, fun n hn' => hN n (.inl hn'), fun u hu => hA u (.inr (.inl hu)),
      ne_wildcard_of_arithAtoms har.1, operandArith_of_arithAtoms har.1, hT.1, hF.1, hB.1, hV.1,
      h1.1, h2.1, h3.1, h4.1, fun y hy => hc y (.inl hy), hs, supported_of_arithAtoms har.1⟩,
    ⟨hn.2, fun n hn' => hN n (.inr hn'), fun u hu => hA u (.inr (.inr hu)),
      ne_wildcard_of_arithAtoms har.2, operandArith_of_arithAtoms har.2, hT.2, hF.2, hB.2, hV.2,
      h1.2, h2.2, h3.2, h4.2, fun y hy => hc y (.inr hy), hs, supported_of_arithAtoms har.2⟩,
    har.1, har.2⟩

/-- A well-formed binder list's bindings: the body of an aggregate. -/
theorem FOk.ofBody {dom : List Binder} {body : Formula}
    (hnd : (dom.map (·.name)).Nodup)
    (hn : eventNamesF C.events body = none) (hN : ∀ n ∈ nodesF body, nodeChecks C e decl n = [])
    (hT : typesF C.schema C.events e (binderBindings dom ++ portBindings e Γ) body = [])
    (hV : validityF C (dom.reverse ++ sc) body = [])
    (h1 : noReservedF body = true) (h2 : wellPlacedF body = true) (h3 : summandsOwnF body = true)
    (h4 : noEmptyContextF body = true)
    (hc : ∀ y ∈ body.fv.filter (fun x => !(dom.map (·.name)).contains x), (Γ.lookup y).isSome)
    (hs : ∀ x, (sc.find? (·.name == x)).map (annotationSort ·.ty) = Γ.lookup x) :
    FOk C e decl (binderBindings dom ++ Γ) (dom.reverse ++ sc) body := by
  refine ⟨hn, hN, by simpa [portBindings, List.append_assoc] using hT, hV, h1, h2, h3, h4,
    fun y hy => ?_, fun x => ?_⟩
  · rw [lookup_binderBindings]
    cases hf : dom.find? (·.name == y) with
    | some b => simp
    | none =>
      have hy' : (dom.map (·.name)).contains y = false := by
        rw [List.find?_eq_none] at hf
        simp only [List.contains_eq_any_beq, List.any_map, List.any_eq_false]
        intro b hb hby
        exact hf b hb (by simp at hby ⊢; exact hby.symm)
      simpa using hc y (List.mem_filter.mpr ⟨hy, by rw [hy']; rfl⟩)
  · rw [lookup_binderBindings, List.find?_append, Option.map_or, find?_reverse_of_nodup x dom hnd,
      hs x]

theorem TOk.count {dom : List Binder} {body : Formula} (h : TOk C e decl Γ sc (.agg (.count dom body))) :
    bindersTyped C.schema dom = true ∧ (∀ b ∈ dom, reservedBinderNames.contains b.name = false) ∧
      FOk C e decl (binderBindings dom ++ Γ) (dom.reverse ++ sc) body := by
  obtain ⟨hn, hN, -, -, -, hT, hF, hB, hV, h1, h2, h3, h4, hc, hs⟩ := h
  have hnd : (dom.map (·.name)).Nodup := by
    apply nodup_of_take
    intro i hi
    simp only [forListAt, eraseDups_eq_nil_iff, List.filterMap_eq_nil_iff] at hF
    have := hF ((dom.map (·.name))[i], i) (List.mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_getElem hi))
    split at this
    · cases this
    · rename_i hc'; simpa using hc'
  have hdecl : ∀ b ∈ dom, binderTypeDeclared C.schema b.ty = true := by
    simp only [binderTypesAt, eraseDups_eq_nil_iff, List.filterMap_eq_nil_iff] at hB
    intro b hb
    exact binderTypeProblem_eq_none.mp (hB b hb)
  have hbt : bindersTyped C.schema dom = true := by
    simp only [bindersTyped, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
    exact ⟨hdecl, hnd⟩
  simp only [typesT, typesA, if_pos hbt] at hT
  simp only [validityT, validityA, if_pos hbt] at hV
  simp only [eventNamesT, eventNamesA, nodesT, nodesA, noReservedT, wellPlacedT, summandsOwnT,
    noEmptyContextT, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true', Term.fv,
    Aggregate.fv] at hn hN h1 h2 h3 h4 hc
  exact ⟨hbt, h1.1, FOk.ofBody hnd hn hN hT hV h1.2 h2 h3 h4 hc hs⟩

theorem TOk.sum {s : VarName} {dom : List Binder} {body : Formula}
    (h : TOk C e decl Γ sc (.agg (.sum s dom body))) :
    bindersTyped C.schema dom = true ∧ (∀ b ∈ dom, reservedBinderNames.contains b.name = false) ∧
      (dom.map (·.name)).contains s = true ∧ summandAt decl (.agg (.sum s dom body)) = [] ∧
      FOk C e decl (binderBindings dom ++ Γ) (dom.reverse ++ sc) body := by
  obtain ⟨hn, hN, hA, -, -, hT, hF, hB, hV, h1, h2, h3, h4, hc, hs⟩ := h
  have hnd : (dom.map (·.name)).Nodup := by
    apply nodup_of_take
    intro i hi
    simp only [forListAt, eraseDups_eq_nil_iff, List.filterMap_eq_nil_iff] at hF
    have := hF ((dom.map (·.name))[i], i) (List.mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_getElem hi))
    split at this
    · cases this
    · rename_i hc'; simpa using hc'
  have hdecl : ∀ b ∈ dom, binderTypeDeclared C.schema b.ty = true := by
    simp only [binderTypesAt, eraseDups_eq_nil_iff, List.filterMap_eq_nil_iff] at hB
    intro b hb
    exact binderTypeProblem_eq_none.mp (hB b hb)
  have hbt : bindersTyped C.schema dom = true := by
    simp only [bindersTyped, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
    exact ⟨hdecl, hnd⟩
  have hsum : summandAt decl (.agg (.sum s dom body)) = [] := by
    have := (hA (.agg (.sum s dom body)) (by simp [termAtoms])).1
    simp only [termChecks, List.append_eq_nil_iff] at this
    exact this.2
  simp only [typesT, typesA, if_pos hbt] at hT
  simp only [validityT, validityA, if_pos hbt] at hV
  simp only [eventNamesT, eventNamesA, nodesT, nodesA, noReservedT, wellPlacedT, summandsOwnT,
    noEmptyContextT, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true', Term.fv,
    Aggregate.fv] at hn hN h1 h2 h3 h4 hc
  exact ⟨hbt, h1.1, h3.1, hsum, FOk.ofBody hnd hn hN hT hV h1.2 h2 h3.2 h4 hc hs⟩

end

/-! ## Terms -/

section

variable {C : LeafCtx} {C' : TypingCtx} {e : ReqEnv} {decl : List Binder}

theorem Setting.scopeType (hs : Setting C C' e) (r : Dogwood.Spec.ScopeRoot) :
    C'.scopeType r = e.scopeType r := by
  cases r
  · exact hs.view.principal
  · exact hs.view.resource

theorem Setting.admitted (hs : Setting C C' e) (r : Dogwood.Spec.ScopeRoot) :
    e.scopeType r ∈ admittedTypes C.schema e.entry (Root.ofSpec r) (C.narrow (Root.ofSpec r)) := by
  cases r
  · exact hs.principal
  · exact hs.resource

theorem Setting.declaredAdmitted (hs : Setting C C' e) {ro : Root} {ety : EntityType}
    (h : ety ∈ admittedTypes C.schema e.entry ro (C.narrow ro)) :
    ∃ attrs, entityAttrs? C.schema ety = some attrs := by
  have hmem : ety ∈ appliesTo e.entry ro := (List.mem_filter.mp h).1
  have hc := hs.view.declared ro ety hmem
  simp only [Cedar.Validation.EntitySchema.contains, Option.isSome_iff_exists] at hc
  obtain ⟨entry, he⟩ := hc
  exact ⟨entry.attrs, by simp [entityAttrs?, Cedar.Validation.EntitySchema.attrs?, he]⟩

/-- A scope path the crate's validator resolves on every admitted entity type resolves on each. -/
theorem resolveOne_of_resolveScopePath {S : Schema} {entry : ActionSchemaEntry} {ro : Root}
    {narrow : ScopeConstraint} {a : String} {p : List String} {ety : EntityType}
    (h : resolveScopePath S entry ro narrow (a :: p) = .resolved ∨
      resolveScopePath S entry ro narrow (a :: p) = .unknown ∨
      ∃ ts, resolveScopePath S entry ro narrow (a :: p) = .ambiguous ts)
    (hety : ety ∈ admittedTypes S entry ro narrow)
    (hall : ∀ ety' ∈ admittedTypes S entry ro narrow, ∃ attrs, entityAttrs? S ety' = some attrs) :
    ∃ attrs ty, entityAttrs? S ety = some attrs ∧ resolveOne attrs a p = .ok ty := by
  obtain ⟨attrs, hattrs⟩ := hall ety hety
  refine ⟨attrs, ?_⟩
  have hne : (admittedTypes S entry ro narrow).isEmpty = false := by
    cases hl : admittedTypes S entry ro narrow with
    | nil => rw [hl] at hety; cases hety
    | cons _ _ => rfl
  have hany : (admittedTypes S entry ro narrow).any (fun ety => (entityAttrs? S ety).isNone) = false := by
    rw [List.any_eq_false]
    intro x hx
    obtain ⟨a', ha'⟩ := hall x hx
    simp [ha']
  cases hr : resolveOne attrs a p with
  | ok ty => exact ⟨ty, hattrs, rfl⟩
  | error f =>
    exfalso
    simp only [resolveScopePath, hne, hany, Bool.false_eq_true, if_false] at h
    generalize hfail : (List.filterMap _ _).mergeSort _ = failed at h
    have hmem : (nameText ety, f) ∈ failed := by
      rw [← hfail]
      apply List.mem_mergeSort.mpr
      rw [List.mem_filterMap]
      refine ⟨(nameText ety, resolveOne ((entityAttrs? S ety).getD Cedar.Data.Map.empty) a p), ?_, ?_⟩
      · exact List.mem_map.mpr ⟨ety, hety, rfl⟩
      · simp [hattrs, hr]
    cases failed with
    | nil => cases hmem
    | cons hd tl =>
      obtain ⟨_, f'⟩ := hd
      cases f' <;> simp at h

theorem simple_wt (hs : Setting C C' e) {Γ Γp : Bindings} (t : Term) (hsimple : t.Simple)
    (hnv : ∀ x, t ≠ .var x) (hnw : t ≠ .wildcard) (hne : t ≠ .context [])
    (hchk : termChecks C e decl t = []) (hopt : optionalAt C t = [])
    (hsup : unsupportedOperand C.schema e t = none) :
    ∃ τ, termSort C.schema e Γp t = some τ ∧ Term.Typed C' Γ t τ := by
  simp only [termChecks, List.append_eq_nil_iff] at hchk
  obtain ⟨⟨⟨hent, hdec⟩, hpath⟩, -⟩ := hchk
  have hv := hs.view
  cases t with
  | entity uid =>
    refine ⟨_, rfl, .entity ?_⟩
    simp only [entityAt, Option.toList_eq_nil_iff, entityProblem] at hent
    rw [hv.ets]
    split at hent
    · split at hent
      · rename_i hc
        rw [hv.acts uid, hc, Bool.or_true]
      · cases hent
    · split at hent
      · rename_i eids hf
        split at hent
        · rename_i hc
          simp [Cedar.Validation.EntitySchema.isValidEntityUID, hf,
            Cedar.Validation.EntitySchemaEntry.isValidEntityEID, hc]
        · cases hent
      · rename_i entry hf
        simp [Cedar.Validation.EntitySchema.isValidEntityUID, hf,
          Cedar.Validation.EntitySchemaEntry.isValidEntityEID]
      · cases hent
  | long i => exact ⟨_, rfl, .long⟩
  | decimal text =>
    refine ⟨_, rfl, .decimal ?_⟩
    simp only [decimalAt] at hdec
    split at hdec
    · assumption
    · cases hdec
  | string _ => exact ⟨_, rfl, .string⟩
  | bool _ => exact ⟨_, rfl, .bool⟩
  | context p =>
    cases p with
    | nil => exact absurd rfl hne
    | cons h rest =>
      simp only [pathsAt, Option.toList_eq_nil_iff, contextPathProblem] at hpath
      cases hres : resolveContextPath e.entry.context (h :: rest) with
      | resolved ty =>
        have hsupp : ty.temporalSupported = true := by
          simp only [unsupportedOperand, contextPathType?, hres] at hsup
          revert hsup; cases ty.temporalSupported <;> simp
        refine ⟨.cedar ty, by simp [termSort, contextPathType?, hres], .context ?_ hsupp⟩
        simp only [resolveContextPath] at hres
        have hh : isHoistedName h = false := by
          cases hh : isHoistedName h
          · rfl
          · rw [hh] at hres; simp at hres
        rw [hh] at hres
        simp only [Bool.false_eq_true, if_false] at hres
        have hdesc : descend (.record e.entry.context) (h :: rest) = .resolved ty := by
          simp only [descend]; split at hres <;> simp_all
        have hu : unguardedOptional (fun q => decide (Guard.context q ∈ C.facts)) e.entry.context
            [] (h :: rest) = none := by
          simp only [optionalAt, List.filterMap_eq_nil_iff, Option.map_eq_none_iff] at hopt
          exact hopt _ hs.act
        unfold TypingCtx.contextType?
        rw [pathType?_congr (hv.context h hh)]
        refine pathType?_of_descend (h := h) (h :: rest) e.entry.context [] ty rfl ?_ (by simp)
          hdesc hu
        intro q hq hg
        simp only [List.nil_append, decide_eq_true_eq] at hq hg ⊢
        apply hv.facts _ hg
        cases q with
        | nil => cases hq
        | cons q₁ q' => simp at hq; subst hq; simp [Guard.reservedHead, hh]
      | headMissing | nestedMissing _ | nonRecord _ => rw [hres] at hpath; cases hpath
  | scope r p =>
    cases p with
    | nil =>
      refine ⟨_, rfl, ?_⟩
      rw [← hs.scopeType r]
      exact .scopeRoot
    | cons a p' =>
      simp only [pathsAt, Option.toList_eq_nil_iff, scopePathProblem] at hpath
      have hrs : resolveScopePath C.schema e.entry (Root.ofSpec r) (C.narrow (Root.ofSpec r)) (a :: p') =
          .resolved ∨
          resolveScopePath C.schema e.entry (Root.ofSpec r) (C.narrow (Root.ofSpec r)) (a :: p') =
          .unknown ∨
          ∃ ts, resolveScopePath C.schema e.entry (Root.ofSpec r) (C.narrow (Root.ofSpec r)) (a :: p') =
          .ambiguous ts := by
        revert hpath
        cases resolveScopePath C.schema e.entry (Root.ofSpec r) (C.narrow (Root.ofSpec r)) (a :: p') <;>
          simp
      obtain ⟨attrs, ty, hattrs, hro⟩ := resolveOne_of_resolveScopePath hrs (hs.admitted r)
        (fun ety' h' => hs.declaredAdmitted h')
      have hsupp : ty.temporalSupported = true := by
        simp only [unsupportedOperand, scopeAttrTypeOf?, hattrs, hro, Except.toOption] at hsup
        revert hsup; cases ty.temporalSupported <;> simp
      refine ⟨.cedar ty, by simp [termSort, scopeAttrTypeOf?, hattrs, hro, Except.toOption], ?_⟩
      refine .scopeAttr (by simp) ?_ hsupp
      simp only [resolveOne] at hro
      have hdesc : descend (.record attrs) (a :: p') = .resolved ty := by
        simp only [descend]
        split at hro
        · cases hro
        · rename_i q hq; rw [hq]; exact resolveOne_go_eq _ _ _ hro
      have hunp : unguardedOptional (fun q => decide (Guard.scope r q ∈ C.facts)) attrs [] (a :: p') =
          none := by
        simp only [optionalAt, List.isEmpty_cons, Bool.false_eq_true, if_false,
          List.flatMap_eq_nil_iff, List.filterMap_eq_nil_iff] at hopt
        have := hopt _ hs.act _ (hs.admitted r)
        rw [hattrs] at this
        simpa using this
      unfold TypingCtx.scopeAttrType?
      rw [hv.ets, hs.scopeType r]
      have hattrs' : C.schema.ets.attrs? (e.scopeType r) = some attrs := hattrs
      rw [hattrs']
      refine pathType?_of_descend (h := a) (a :: p') attrs [] ty rfl ?_ (by simp) hdesc hunp
      intro q _ hg
      simp only [List.nil_append, decide_eq_true_eq] at hg ⊢
      exact hv.facts _ hg rfl
  | var x => exact absurd rfl (hnv x)
  | wildcard => exact absurd rfl hnw
  | agg _ => exact hsimple.elim
  | arith _ _ _ => exact hsimple.elim

/-! ## Binders -/

theorem binderValueSort?_eq {S : Schema} {ty : BinderType} {τ : TType}
    (h : binderValueSort? S ty = some τ) : annotationSort ty = τ := by
  cases ty with
  | timepoint => simp [binderValueSort?] at h
  | named path =>
    simp only [binderValueSort?, annotationSort] at *
    split at h <;> simp_all

theorem sort?_of_declared {S : Schema} {ets : Cedar.Validation.EntitySchema} (hets : ets = S.ets)
    {ty : BinderType} (h : binderTypeDeclared S ty = true) : ty.sort? ets = some (annotationSort ty) := by
  subst hets
  cases ty with
  | timepoint => rfl
  | named path =>
    simp only [binderTypeDeclared, BinderType.sort?, annotationSort] at *
    split <;> simp_all

/-! ## Monadic maps -/

theorem except_mapM_mem {α β ε : Type} {f : α → Except ε β} :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = .ok ys → ∀ y ∈ ys, ∃ x ∈ xs, f x = .ok y
  | [], ys, h, y, hy => by simp [List.mapM_nil, pure, Except.pure] at h; subst h; cases hy
  | x :: xs, ys, h, y, hy => by
    simp only [List.mapM_cons, bind, Except.bind, pure, Except.pure] at h
    cases hx : f x with
    | error _ => rw [hx] at h; cases h
    | ok y' =>
      rw [hx] at h
      cases hxs : xs.mapM f with
      | error _ => rw [hxs] at h; cases h
      | ok ys' =>
        rw [hxs] at h
        cases h
        rcases List.mem_cons.mp hy with rfl | hy
        · exact ⟨x, List.mem_cons_self .., hx⟩
        · obtain ⟨x', hx', hf⟩ := except_mapM_mem hxs y hy
          exact ⟨x', List.mem_cons_of_mem _ hx', hf⟩

theorem option_mapM_mem {α β : Type} {f : α → Option β} :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = some ys → ∀ x ∈ xs, ∃ y ∈ ys, f x = some y
  | [], _, _, x, hx => by cases hx
  | x :: xs, ys, h, z, hz => by
    simp only [List.mapM_cons, bind, Option.bind, pure] at h
    cases hx : f x with
    | none => rw [hx] at h; cases h
    | some y' =>
      rw [hx] at h
      cases hxs : xs.mapM f with
      | none => rw [hxs] at h; cases h
      | some ys' =>
        rw [hxs] at h
        simp only [Option.some.injEq] at h
        subst h
        rcases List.mem_cons.mp hz with rfl | hz
        · exact ⟨y', List.mem_cons_self .., hx⟩
        · obtain ⟨y, hy, hf⟩ := option_mapM_mem hxs z hz
          exact ⟨y, List.mem_cons_of_mem _ hy, hf⟩

/-! ## Pins -/

theorem pin_scope (hs : Setting C C' e) (r : Dogwood.Spec.ScopeRoot) (tail : Path)
    {sorts : List TType} {fty : Dogwood.Spec.FieldTy}
    (hsorts : (if tail.isEmpty then
        some ((admittedTypes C.schema e.entry (Root.ofSpec r) (C.narrow (Root.ofSpec r))).map
          fun ety => TType.cedar (.entity ety))
      else (admittedTypes C.schema e.entry (Root.ofSpec r) (C.narrow (Root.ofSpec r))).mapM
        fun ety => (entityAttrs? C.schema ety).bind fun attrs =>
          (requiredPathType? attrs tail).map TType.cedar) = some sorts)
    (hacc : ∀ τ ∈ sorts, acceptsB fty τ = true) (hsupp : ∀ τ ∈ sorts, τ.temporalSupported = true) :
    ∃ τ, (Dogwood.Spec.PinRef.scope r tail).sort? { C' with facts := [] } = some τ ∧
      fty.Accepts τ := by
  have hv := hs.view
  have hadm := hs.admitted r
  by_cases hte : tail.isEmpty = true
  · rw [if_pos hte] at hsorts
    cases hsorts
    have ht : tail = [] := List.isEmpty_iff.mp hte
    subst ht
    refine ⟨.cedar (.entity (e.scopeType r)), ?_, (acceptsB_iff _ _).mp (hacc _ ?_)⟩
    · simp only [Dogwood.Spec.PinRef.sort?]
      have := hs.scopeType r
      simp only [TypingCtx.scopeType] at this ⊢
      cases r <;> simp_all
    · exact List.mem_map.mpr ⟨_, hadm, rfl⟩
  · rw [if_neg hte] at hsorts
    have htne : tail ≠ [] := fun h => hte (by simp [h])
    obtain ⟨τ, hτ, hf⟩ := option_mapM_mem hsorts _ hadm
    obtain ⟨attrs, hattrs⟩ := hs.declaredAdmitted hadm
    rw [hattrs] at hf
    simp only [Option.bind_some, Option.map_eq_some_iff] at hf
    obtain ⟨t, ht, rfl⟩ := hf
    refine ⟨.cedar t, ?_, (acceptsB_iff _ _).mp (hacc _ hτ)⟩
    cases tail with
    | nil => exact absurd rfl htne
    | cons a rest =>
      simp only [Dogwood.Spec.PinRef.sort?, Option.map_eq_some_iff, Option.filter_eq_some_iff]
      refine ⟨t, ⟨?_, by simpa [TType.temporalSupported] using hsupp _ hτ⟩, rfl⟩
      unfold TypingCtx.scopeAttrType?
      have hsc : ({ C' with facts := [] } : TypingCtx).scopeType r = e.scopeType r := by
        rw [← hs.scopeType r]; cases r <;> rfl
      rw [hsc]
      show (match C'.env.ets.attrs? (e.scopeType r) with
        | some rty => pathType? _ rty [] (a :: rest)
        | none => none) = some t
      rw [hv.ets]
      have hattrs' : C.schema.ets.attrs? (e.scopeType r) = some attrs := hattrs
      rw [hattrs']
      exact pathType?_of_required _ _ _ _ ht

theorem pinsTyped_of (hs : Setting C C' e) {a : EntityUID} {k : String} {ev : DerivedEvent}
    {sig : Dogwood.Spec.EventSignature}
    (hev : eventOf? C.events a k = some ev) (hag : SigAgrees C.schema a ev sig)
    (hp : pinsAt C a k = []) : sig.PinsTyped C' := by
  have hv := hs.view
  intro pin hpin
  obtain ⟨cp, hcp, hto⟩ := except_mapM_mem hag.pins pin hpin
  obtain ⟨fd, hfd⟩ := Option.isSome_iff_exists.mp (hag.pinFields cp hcp)
  have hft : fieldType? C.schema ev cp.fieldPath = some (some fd.ty) := by rw [hag.fields, hfd]; rfl
  simp only [pinsAt, hev, List.flatMap_eq_nil_iff] at hp
  have h1 := hp cp hcp
  rw [hft] at h1
  simp only [List.filterMap_eq_nil_iff] at h1
  have h2 := h1 _ hs.act
  cases hsorts : pinRefSorts? C e.entry cp with
  | none => rw [hsorts] at h2; cases h2
  | some sorts =>
    rw [hsorts] at h2
    dsimp only at h2
    have hsupp : ∀ τ ∈ sorts, τ.temporalSupported = true := by
      cases hf : sorts.find? (!TType.temporalSupported ·) with
      | some τ => rw [hf] at h2; cases h2
      | none =>
        intro τ hτ
        simpa using List.find?_eq_none.mp hf τ hτ
    have hfn : sorts.find? (!TType.temporalSupported ·) = none := by
      rw [List.find?_eq_none]; intro τ hτ; simp [hsupp τ hτ]
    simp only [hfn] at h2
    have hacc : ∀ τ ∈ sorts, acceptsB fd.ty τ = true := by
      simp only [Option.map_eq_none_iff, List.find?_eq_none, Bool.not_eq_true',
        Bool.not_eq_false] at h2
      intro τ hτ
      have := h2 τ hτ
      simpa [fieldAccepts] using this
    obtain ⟨field, ctxp, root⟩ := cp
    cases root with
    | context =>
      simp only [Dogwood.Frontend.Pin.toSpec, pure, Except.pure, Except.ok.injEq] at hto
      subst hto
      simp only [pinRefSorts?] at hsorts
      cases ctxp with
      | nil => cases hsorts
      | cons head tl =>
        simp only at hsorts
        by_cases hh : isHoistedName head = true
        · rw [if_pos hh] at hsorts; cases hsorts
        · rw [if_neg hh] at hsorts
          simp only [Option.map_eq_some_iff] at hsorts
          obtain ⟨t, ht, rfl⟩ := hsorts
          refine ⟨fd, .cedar t, hfd, ?_, (acceptsB_iff _ _).mp (hacc _ (by simp))⟩
          simp only [Dogwood.Spec.PinRef.sort?, TypingCtx.contextType?, Option.map_eq_some_iff,
            Option.filter_eq_some_iff]
          refine ⟨t, ⟨?_, by simpa [TType.temporalSupported] using hsupp (.cedar t) (by simp)⟩, rfl⟩
          have hhf : isHoistedName head = false := by simpa using hh
          rw [pathType?_congr (hv.context head hhf)]
          exact pathType?_of_required _ _ _ _ ht
    | scope =>
      cases ctxp with
      | nil => simp [Dogwood.Frontend.Pin.toSpec] at hto
      | cons r0 tail =>
        by_cases hp1 : r0 = "principal"
        · subst hp1
          simp only [Dogwood.Frontend.Pin.toSpec, pure, Except.pure, Except.ok.injEq] at hto
          subst hto
          simp only [pinRefSorts?] at hsorts
          obtain ⟨τ, hτ, hacc'⟩ := pin_scope hs .principal tail hsorts hacc hsupp
          exact ⟨fd, τ, hfd, hτ, hacc'⟩
        · by_cases hp2 : r0 = "resource"
          · subst hp2
            simp only [Dogwood.Frontend.Pin.toSpec, pure, Except.pure, Except.ok.injEq] at hto
            subst hto
            simp only [pinRefSorts?] at hsorts
            obtain ⟨τ, hτ, hacc'⟩ := pin_scope hs .resource tail hsorts hacc hsupp
            exact ⟨fd, τ, hfd, hτ, hacc'⟩
          · simp [Dogwood.Frontend.Pin.toSpec, hp1, hp2] at hto

/-! ## Predicates -/

theorem self_mem_termAtoms (t : Term) : t ∈ termAtoms t := by
  cases t <;> simp [termAtoms]

theorem mem_argsAtoms {p : Path} {t : Term} : {args : List (Path × Term)} → (p, t) ∈ args →
    ∀ u ∈ termAtoms t, u ∈ argsAtoms args
  | [], h, _, _ => by cases h
  | (p', t') :: args, h, u, hu => by
    simp only [argsAtoms, List.mem_append]
    rcases List.mem_cons.mp h with h | h
    · cases h; exact .inl hu
    · exact .inr (mem_argsAtoms h u hu)

theorem fv_sub_argsFv {p : Path} {t : Term} : {args : List (Path × Term)} → (p, t) ∈ args →
    ∀ y ∈ t.fv, y ∈ Formula.argsFv args
  | [], h, _, _ => by cases h
  | (p', t') :: args, h, y, hy => by
    simp only [Formula.argsFv, List.mem_append]
    rcases List.mem_cons.mp h with h | h
    · cases h; exact .inl hy
    · exact .inr (fv_sub_argsFv h y hy)

theorem noEmpty_of_arg {p : Path} {t : Term} : {args : List (Path × Term)} →
    noEmptyContextArgs args = true → (p, t) ∈ args → noEmptyContextT t = true
  | [], _, h => by cases h
  | (p', t') :: args, hn, h => by
    simp only [noEmptyContextArgs, Bool.and_eq_true] at hn
    rcases List.mem_cons.mp h with h | h
    · cases h; exact hn.1
    · exact noEmpty_of_arg hn.2 h

/-- A predicate argument other than a variable or a wildcard is not of an unsupported type. -/
theorem predArg_supported {S : Schema} {d : DerivedEventSchema} {Γp : Bindings} {a : EntityUID}
    {k : String} {args : List (Path × Term)} {p : Path} {t : Term}
    (h : predArgsProblems S d e Γp a k args = []) (hpt : (p, t) ∈ args)
    (hnv : ∀ x, t ≠ .var x) (hnw : t ≠ .wildcard) : unsupportedOperand S e t = none := by
  simp only [predArgsProblems, List.flatMap_eq_nil_iff] at h
  have := h _ hpt
  dsimp only at this
  cases hu : argUnsupported S e t with
  | some m => rw [hu] at this; cases this
  | none =>
    cases t <;> first | exact absurd rfl (hnv _) | exact absurd rfl hnw | exact hu

/-- A spliced field's argument has the field's type, when it has one. -/
theorem predArg_spliced {S : Schema} {d : DerivedEventSchema} {Γp : Bindings} {a : EntityUID}
    {k : String} {args : List (Path × Term)} {p : Path} {t : Term}
    (h : predArgsProblems S d e Γp a k args = []) (hpt : (p, t) ∈ args)
    (hsp : isSpliced p = true) {expected : CedarType} (hst : splicedFieldType? S a p = some expected)
    {got : TType} (hgot : termSort S e Γp t = some got) : got = .cedar expected := by
  simp only [predArgsProblems, List.flatMap_eq_nil_iff] at h
  have := h _ hpt
  dsimp only at this
  cases hu : argUnsupported S e t with
  | some m => rw [hu] at this; cases this
  | none =>
  rw [hu] at this
  dsimp only at this
  simp only [hsp, if_true, hst, hgot] at this
  split at this
  · simpa using (by assumption : (got == TType.cedar expected) = true)
  · cases this

/-- Any other field's argument other than a variable or a wildcard has a type the field can hold,
when it has one. -/
theorem predArg_other {S : Schema} {d : DerivedEventSchema} {Γp : Bindings} {a : EntityUID}
    {k : String} {args : List (Path × Term)} {p : Path} {t : Term}
    (h : predArgsProblems S d e Γp a k args = []) (hpt : (p, t) ∈ args)
    (hnsp : isSpliced p = false) (hnv : ∀ x, t ≠ .var x) (hnw : t ≠ .wildcard) {ev : DerivedEvent}
    (hev : eventOf? d a k = some ev) {fty : Option Dogwood.Spec.FieldTy}
    (hft : fieldType? S ev p = some fty) {got : TType} (hgot : termSort S e Γp t = some got) :
    fieldAccepts fty got = true := by
  simp only [predArgsProblems, List.flatMap_eq_nil_iff] at h
  have := h _ hpt
  dsimp only at this
  cases hu : argUnsupported S e t with
  | some m => rw [hu] at this; cases this
  | none =>
  rw [hu] at this
  dsimp only at this
  simp only [hnsp, Bool.false_eq_true, if_false, hev, Option.bind_some, hft, hgot] at this
  cases t with
  | var x => exact absurd rfl (hnv x)
  | wildcard => exact absurd rfl hnw
  | _ =>
    split at this
    · assumption
    · cases this

/-- A predicate argument other than a variable or a wildcard is typed. -/
theorem arg_other (hs : Setting C C' e) {Γ : Bindings} {a : EntityUID} {k : String}
    {ev : DerivedEvent} {sig : Dogwood.Spec.EventSignature} {args : List (Path × Term)} {p : Path}
    {t : Term} {fd : Dogwood.Spec.FieldDecl}
    (hev : eventOf? C.events a k = some ev) (hag : SigAgrees C.schema a ev sig) (hpt : (p, t) ∈ args)
    (hfd : sig.field? p = some fd) (hft : fieldType? C.schema ev p = some (some fd.ty))
    (hT : predArgsProblems C.schema C.events e (portBindings e Γ) a k args = [])
    (hsimple : t.Simple) (hnv : ∀ x, t ≠ .var x) (hnw : t ≠ .wildcard)
    (hne : noEmptyContextT t = true) (hchk : termChecks C e decl t = [])
    (hopt : optionalAt C t = []) : Formula.ArgTyped C' Γ sig (p, t) := by
  have hne' : t ≠ .context [] := by rintro rfl; simp [noEmptyContextT] at hne
  obtain ⟨τ, hτs, hτ⟩ := simple_wt hs (Γp := portBindings e Γ) t hsimple hnv hnw hne' hchk hopt
    (predArg_supported hT hpt hnv hnw)
  refine .term hfd hsimple hnv hnw hτ ?_
  cases hsp : isSpliced p
  · exact (acceptsB_iff _ _).mp (predArg_other hT hpt hsp hnv hnw hev hft hτs)
  · obtain ⟨t', hst, hty⟩ := hag.spliced p fd hsp hfd
    have := predArg_spliced hT hpt hsp hst hτs
    rw [hty, this]
    rfl

/-- **A predicate the crate's checks accept is well-typed.** -/
theorem pred_wt (hs : Setting C C' e) {Γ : Bindings} {sc : List Binder} {a : EntityUID}
    {k : String} {args : List (Path × Term)} (h : FOk C e decl Γ sc (.pred a k args)) :
    (Formula.pred a k args).WellTyped C' Γ := by
  obtain ⟨hn, hN, hT, hV, -, hP, -, hE, hc, hsc⟩ := h
  have hv := hs.view
  simp only [eventNamesF, predEventProblem] at hn
  cases hev : eventOf? C.events a k with
  | none => rw [hev] at hn; cases hn
  | some ev =>
    rw [hev] at hn
    simp only [List.findSome?_eq_none_iff] at hn
    obtain ⟨sig, hsig, hag⟩ := hv.events a k ev hev
    simp only [validityF, validityAt, eraseDups_eq_nil_iff, List.append_eq_nil_iff,
      List.flatMap_eq_nil_iff] at hV
    obtain ⟨⟨⟨hopt, hpins⟩, hbind⟩, -⟩ := hV
    have hnode : ∀ u ∈ argsAtoms args, termChecks C e decl u = [] := by
      have := hN (.pred a k args) (by simp [nodesF])
      simpa [nodeChecks, nodeTerms, windowsAt, wildcardAt, List.flatMap_eq_nil_iff] using this
    simp only [typesF, eraseDups_eq_nil_iff] at hT
    simp only [wellPlacedF, List.all_eq_true] at hP
    simp only [noEmptyContextF] at hE
    refine .pred hsig (fun ⟨p, t⟩ hpt => ?_) (pinsTyped_of hs hev hag hpins)
    have hleaf : lookupPath ev p = .leaf := by
      have := hn _ hpt
      revert this
      cases lookupPath ev p <;> simp
    obtain ⟨fd, hfd⟩ := Option.isSome_iff_exists.mp (hag.leaf p hleaf)
    have hft : fieldType? C.schema ev p = some (some fd.ty) := by rw [hag.fields, hfd]; rfl
    have hsimple : t.Simple := (simple_iff t).mp (hP _ hpt)
    have hne := noEmpty_of_arg hE hpt
    have hclosed : ∀ y ∈ t.fv, (Γ.lookup y).isSome := fun y hy => hc y (fv_sub_argsFv hpt y hy)
    have hchk : termChecks C e decl t = [] := hnode t (mem_argsAtoms hpt t (self_mem_termAtoms t))
    have hopt' : optionalAt C t = [] := hopt t (mem_argsAtoms hpt t (self_mem_termAtoms t))
    cases t with
    | wildcard => exact .wildcard hfd
    | var x =>
      obtain ⟨τ, hτ⟩ := Option.isSome_iff_exists.mp (hclosed x (by simp [Term.fv]))
      refine .var hfd hτ ?_
      cases hsp : isSpliced p
      · simp only [bindingFieldsAt, hev, List.filterMap_eq_nil_iff] at hbind
        have hb1 := hbind _ hpt
        simp only [hsp, Bool.false_eq_true, if_false, hft] at hb1
        have hsx := hsc x
        rw [hτ] at hsx
        obtain ⟨b, hb, hbτ⟩ := Option.map_eq_some_iff.mp hsx
        rw [hb] at hb1
        cases hbv : binderValueSort? C.schema b.ty with
        | none => simp [hbv] at hb1
        | some τ' =>
          have he := binderValueSort?_eq hbv
          rw [hbτ] at he
          subst he
          have hok : fieldWithin (some fd.ty) τ = true := by
            by_contra hk
            simp [hbv, hk] at hb1
          exact (withinB_iff _ _).mp hok
      · obtain ⟨t', hst, hty⟩ := hag.spliced p fd hsp hfd
        have hgot : termSort C.schema e (portBindings e Γ) (.var x) = some τ := by
          simp only [termSort, portBindings]
          rw [lookup_append_of_isSome (by rw [hτ]; rfl), hτ]
        have := predArg_spliced hT hpt hsp hst hgot
        rw [hty, this]
        rfl
    | agg _ => exact hsimple.elim
    | arith _ _ _ => exact hsimple.elim
    | entity _ => exact arg_other hs hev hag hpt hfd hft hT hsimple (by simp) (by simp) hne hchk hopt'
    | long _ => exact arg_other hs hev hag hpt hfd hft hT hsimple (by simp) (by simp) hne hchk hopt'
    | decimal _ => exact arg_other hs hev hag hpt hfd hft hT hsimple (by simp) (by simp) hne hchk hopt'
    | string _ => exact arg_other hs hev hag hpt hfd hft hT hsimple (by simp) (by simp) hne hchk hopt'
    | bool _ => exact arg_other hs hev hag hpt hfd hft hT hsimple (by simp) (by simp) hne hchk hopt'
    | context _ => exact arg_other hs hev hag hpt hfd hft hT hsimple (by simp) (by simp) hne hchk hopt'
    | scope _ _ => exact arg_other hs hev hag hpt hfd hft hT hsimple (by simp) (by simp) hne hchk hopt'

/-! ## The other constructs -/

theorem withinCap_of (hs : Setting C C' e) {w : Window} (h : windowProblem C w = none) :
    w.withinCap C'.maxWindow = true := by
  rw [hs.view.maxWindow]
  simp only [windowProblem] at h
  simp only [Window.withinCap, Bool.and_eq_true, decide_eq_true_eq]
  split at h
  · cases h
  · rename_i h1
    split at h
    · cases h
    · rename_i h2
      split at h
      · cases h
      · rename_i h3
        omega

theorem binder_sort (hs : Setting C C' e) {x : Binder} (hd : binderTypeDeclared C.schema x.ty = true)
    (hr : reservedBinderNames.contains x.name = false) :
    Binder.sort? C'.env.ets x = some (x.name, annotationSort x.ty) := by
  have hr' : x.name ∉ reservedBinderNames := by simpa using hr
  simp [Binder.sort?, hr', sort?_of_declared hs.view.ets hd]

theorem mapM_eq_some_map {α β : Type} {f : α → Option β} {g : α → β} :
    ∀ {xs : List α}, (∀ x ∈ xs, f x = some (g x)) → xs.mapM f = some (xs.map g)
  | [], _ => rfl
  | x :: xs, h => by
    simp only [List.mapM_cons, h x (List.mem_cons_self ..),
      mapM_eq_some_map (fun y hy => h y (List.mem_cons_of_mem _ hy))]
    rfl

theorem domainSorts_of (hs : Setting C C' e) {dom : List Binder}
    (hbt : bindersTyped C.schema dom = true)
    (hres : ∀ b ∈ dom, reservedBinderNames.contains b.name = false) :
    domainSorts? C'.env.ets dom = some (binderBindings dom) := by
  simp only [bindersTyped, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hbt
  simp only [domainSorts?, if_pos hbt.2]
  exact mapM_eq_some_map fun b hb => binder_sort hs (hbt.1 b hb) (hres b hb)

theorem arith_int {S : Schema} {Γp : Bindings} {t : Term} {τ : TType}
    (h : arithAtoms S e Γp t = []) (hτ : termSort S e Γp t = some τ) : τ = .cedar .int := by
  cases t with
  | arith _ _ _ => simp [termSort] at hτ; exact hτ.symm
  | wildcard => simp [arithAtoms] at h
  | _ =>
    simp only [arithAtoms, hτ] at h
    split at h
    · rename_i h'; cases h'; rfl
    · rename_i h'; cases h'
    · split at h <;> cases h

theorem summand_mem {dom : List Binder} {s : VarName} {body : Formula}
    (hown : (dom.map (·.name)).contains s = true)
    (hsum : summandAt decl (.agg (.sum s dom body)) = []) :
    (s, TType.cedar .int) ∈ binderBindings dom := by
  obtain ⟨b, hb⟩ : ∃ b, dom.find? (·.name == s) = some b := by
    cases hf : dom.find? (·.name == s) with
    | some b => exact ⟨b, rfl⟩
    | none =>
      rw [List.find?_eq_none] at hf
      simp only [List.contains_eq_any_beq, List.any_map, List.any_eq_true] at hown
      obtain ⟨b, hbm, hbs⟩ := hown
      exact absurd (by simp at hbs ⊢; exact hbs.symm) (hf b hbm)
  have hbname : b.name = s := by simpa using List.find?_some hb
  have hbmem := List.mem_of_find?_eq_some hb
  simp only [summandAt, hb, Option.map_some, Option.some_or] at hsum
  have hlong : annotationSort b.ty = .cedar .int := by
    cases hty : b.ty with
    | timepoint => rw [hty] at hsum; simp [summandProblem] at hsum
    | named path =>
      rw [hty] at hsum
      simp only [summandProblem, Option.toList_eq_nil_iff] at hsum
      simp only [annotationSort]
      split at hsum <;> simp_all
  rw [← hbname, ← hlong]
  exact List.mem_map.mpr ⟨b, hbmem, rfl⟩

theorem tp_wt {Γ : Bindings} {sc : List Binder} {x : VarName} (h : FOk C e decl Γ sc (.tp x)) :
    (Formula.tp x).WellTyped C' Γ := by
  obtain ⟨-, -, hT, -, -, -, -, -, hc, -⟩ := h
  obtain ⟨τ, hτ⟩ := Option.isSome_iff_exists.mp (hc x (by simp [Formula.fv]))
  simp only [typesF, portBindings, lookup_append_of_isSome (by rw [hτ]; rfl), hτ] at hT
  split at hT
  · rename_i h'
    have : τ = .timepoint := by simpa using h'
    subst this
    exact .tp hτ
  · cases hT

/-! ## Typing -/

mutual

theorem formula_wt (hs : Setting C C' e) : (ψ : Formula) → (Γ : Bindings) → (sc : List Binder) →
    FOk C e decl Γ sc ψ → ψ.WellTyped C' Γ
  | .and φ ψ, Γ, sc, h =>
    .and (formula_wt hs φ Γ sc h.and.1) (formula_wt hs ψ Γ sc h.and.2)
  | .not φ, Γ, sc, h => .not (formula_wt hs φ Γ sc h.not)
  | .formerly _ φ, Γ, sc, h =>
    .formerly (withinCap_of hs h.formerly.2) (formula_wt hs φ Γ sc h.formerly.1)
  | .previous _ φ, Γ, sc, h =>
    .previous (withinCap_of hs h.previous.2) (formula_wt hs φ Γ sc h.previous.1)
  | .since φ _ ψ, Γ, sc, h =>
    .since (withinCap_of hs h.since.2.2) (formula_wt hs φ Γ sc h.since.1)
      (formula_wt hs ψ Γ sc h.since.2.1)
  | .pred _ _ _, _, _, h => pred_wt hs h
  | .tp _, _, _, h => tp_wt h
  | .exist x φ, Γ, sc, h =>
    .exist (binder_sort hs h.exist.1 h.exist.2.1) (formula_wt hs φ _ _ h.exist.2.2)
  | .cmp op l r, Γ, sc, h => by
    obtain ⟨hl, hr, hul, hur, hcp⟩ := h.cmp
    obtain ⟨τ₁, h1s, h1t⟩ := term_wt hs l Γ sc hl
    obtain ⟨τ₂, h2s, h2t⟩ := term_wt hs r Γ sc hr
    simp only [comparisonProblem, h1s, h2s] at hcp
    by_cases hord : op.isOrder = true
    · rw [if_pos hord] at hcp
      by_cases hint : (τ₁ == .cedar .int && τ₂ == .cedar .int) = true
      · simp only [Bool.and_eq_true, beq_iff_eq] at hint
        obtain ⟨rfl, rfl⟩ := hint
        exact .ord ((isOrder_iff op).mp hord) h1t h2t
      · rw [if_neg hint] at hcp; cases hcp
    · rw [if_neg hord] at hcp
      have hc : Dogwood.Eval.eqCompatibleB l r τ₁ τ₂ = true := by
        revert hcp
        unfold Dogwood.Eval.eqCompatibleB
        cases τ₁ with
        | timepoint => cases τ₂ with
          | timepoint => simp
          | cedar t₂ => simp
        | cedar t₁ => cases τ₂ with
          | timepoint => simp
          | cedar t₂ =>
            cases t₁ <;> cases t₂ <;> simp
            intro hh
            exact (Classical.em _).elim Or.inl (fun hab => Or.inr (hh hab))
      exact .eq (fun ho => hord ((isOrder_iff op).mpr ho)) h1t h2t ((eqCompatibleB_iff l r _ _).mp hc)

theorem term_wt (hs : Setting C C' e) : (t : Term) → (Γ : Bindings) → (sc : List Binder) →
    TOk C e decl Γ sc t →
      ∃ τ, termSort C.schema e (portBindings e Γ) t = some τ ∧ Term.Typed C' Γ t τ
  | .agg (.count dom body), Γ, sc, h => by
    obtain ⟨hbt, hres, hb⟩ := h.count
    exact ⟨.cedar .int, rfl, .agg (.count (domainSorts_of hs hbt hres)
      (formula_wt hs body _ _ hb))⟩
  | .agg (.sum s dom body), Γ, sc, h => by
    obtain ⟨hbt, hres, hown, hsum, hb⟩ := h.sum
    exact ⟨.cedar .int, rfl, .agg (.sum (domainSorts_of hs hbt hres) (summand_mem hown hsum)
      (formula_wt hs body _ _ hb))⟩
  | .arith op l r, Γ, sc, h => by
    obtain ⟨hl, hr, hal, har⟩ := h.ofArith
    obtain ⟨τl, hls, hlt⟩ := term_wt hs l Γ sc hl
    obtain ⟨τr, hrs, hrt⟩ := term_wt hs r Γ sc hr
    have e₁ := arith_int hal hls
    have e₂ := arith_int har hrs
    subst e₁ e₂
    exact ⟨.cedar .int, rfl, .arith hlt hrt⟩
  | .var x, Γ, sc, h => by
    obtain ⟨τ, hτ⟩ := Option.isSome_iff_exists.mp (h.closed x (by simp [Term.fv]))
    refine ⟨τ, ?_, .var hτ⟩
    simp only [termSort, portBindings]
    rw [lookup_append_of_isSome (by rw [hτ]; rfl), hτ]
  | .wildcard, _, _, h => absurd rfl h.notWild
  | .entity uid, Γ, sc, h => simple_wt hs _ (by simp [Term.Simple]) (by simp) (by simp) (by simp)
      (h.atoms _ (self_mem_termAtoms _)).1 (h.atoms _ (self_mem_termAtoms _)).2 h.supp
  | .long i, Γ, sc, h => simple_wt hs _ (by simp [Term.Simple]) (by simp) (by simp) (by simp)
      (h.atoms _ (self_mem_termAtoms _)).1 (h.atoms _ (self_mem_termAtoms _)).2 h.supp
  | .decimal d, Γ, sc, h => simple_wt hs _ (by simp [Term.Simple]) (by simp) (by simp) (by simp)
      (h.atoms _ (self_mem_termAtoms _)).1 (h.atoms _ (self_mem_termAtoms _)).2 h.supp
  | .string str, Γ, sc, h => simple_wt hs _ (by simp [Term.Simple]) (by simp) (by simp) (by simp)
      (h.atoms _ (self_mem_termAtoms _)).1 (h.atoms _ (self_mem_termAtoms _)).2 h.supp
  | .bool b, Γ, sc, h => simple_wt hs _ (by simp [Term.Simple]) (by simp) (by simp) (by simp)
      (h.atoms _ (self_mem_termAtoms _)).1 (h.atoms _ (self_mem_termAtoms _)).2 h.supp
  | .context p, Γ, sc, h =>
    simple_wt hs _ (by simp [Term.Simple]) (by simp) (by simp)
      (by intro heq; cases heq; have := h.noEmpty; simp [noEmptyContextT] at this)
      (h.atoms _ (self_mem_termAtoms _)).1 (h.atoms _ (self_mem_termAtoms _)).2 h.supp
  | .scope r p, Γ, sc, h => simple_wt hs _ (by simp [Term.Simple]) (by simp) (by simp) (by simp)
      (h.atoms _ (self_mem_termAtoms _)).1 (h.atoms _ (self_mem_termAtoms _)).2 h.supp

end

end

/-! ## The theorem -/

theorem mem_envs {C : LeafCtx} {e : ReqEnv} (he : e ∈ C.envs) :
    (e.uid, e.entry) ∈ C.targets ∧
      e.principal ∈ admittedTypes C.schema e.entry .principal C.principal ∧
      e.resource ∈ admittedTypes C.schema e.entry .resource C.resource := by
  simp only [LeafCtx.envs, List.mem_flatMap, List.mem_map] at he
  obtain ⟨⟨uid, entry⟩, hmem, p, hp, r, hr, rfl⟩ := he
  exact ⟨hmem, hp, hr⟩

/-- **The validator's temporal checks are sound for typing.** A temporal leaf on which the
crate's validator reports nothing, which passed the parse-time checks and has no `context` term
with an empty path, is well-typed in every request environment of its rule, in the
specification's typing context that sees the environment as the crate's validator does. -/
theorem leaf_wellTyped {C : LeafCtx} {φ : Formula} {C' : TypingCtx} {e : ReqEnv}
    (hf : leafFindings C φ = []) (hp : parseChecked φ = true) (hne : noEmptyContextF φ = true)
    (he : e ∈ C.envs) (hv : ViewAgrees C' C e) : φ.WellTyped C' [] := by
  obtain ⟨htgt, hpr, hrs⟩ := mem_envs he
  have hact : (e.uid, e.entry) ∈ C.actions := by
    refine List.mem_filter.mpr ⟨htgt, ?_⟩
    simp only [admitsAnyEnv, Bool.and_eq_true, List.any_eq_true]
    exact ⟨⟨e.principal, (List.mem_filter.mp hpr).1, (List.mem_filter.mp hpr).2⟩,
      ⟨e.resource, (List.mem_filter.mp hrs).1, (List.mem_filter.mp hrs).2⟩⟩
  have hs : Setting C C' e := ⟨hv, hact, hpr, hrs⟩
  simp only [leafFindings, List.append_eq_nil_iff, Option.toList_eq_nil_iff,
    List.flatMap_eq_nil_iff, mergeEnvFindings_eq_nil_iff, walkTerms] at hf
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hn, hw⟩, -⟩, hwc⟩, hent⟩, hdec⟩, hpaths⟩, -⟩, htypes⟩, hsum⟩, hval⟩ := hf
  simp only [parseChecked, Bool.and_eq_true, List.isEmpty_iff] at hp
  obtain ⟨⟨⟨⟨hfv, hres⟩, hpl⟩, hown⟩, -⟩ := hp
  have hpa := hpaths _ hact
  have hty := htypes e he
  rw [walkF_nil] at hw hwc hent hdec hsum
  rw [walkF_nil] at hpa
  refine formula_wt (decl := declaredBindersF φ) hs φ [] []
    ⟨hn, fun n hn' => ?_, hty, hval, hres, hpl, hown, hne, by simp [hfv], fun x => rfl⟩
  have h1 := hw n hn'
  have h2 := hwc n hn'
  have h3 := hent n hn'
  have h4 := hdec n hn'
  have h5 := hpa n hn'
  have h6 := hsum n hn'
  simp only [List.flatMap_eq_nil_iff] at h3 h4 h5 h6
  simp only [nodeChecks, termChecks, h1, h2, List.nil_append, List.flatMap_eq_nil_iff,
    List.append_eq_nil_iff]
  exact fun t ht => ⟨⟨⟨h3 t ht, h4 t ht⟩, h5 t ht⟩, h6 t ht⟩

end Dogwood.Thm.Frontend
