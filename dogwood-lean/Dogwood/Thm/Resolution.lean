import Dogwood.Spec.Temporal.Typing
import Dogwood.Spec.Decision
import Cedar.Thm.Validation.Typechecker.Types
import Cedar.Thm.Validation.RequestEntityValidation

/-!
# Typed terms resolve

A well-typed simple term — a literal, a request-side path, or a variable — resolves at a
decision event to a value of its type, when:

* the event is an instance of the typing environment (`Event.InstanceOf`): its request is an
  instance of the environment's request type;
* the event supplies the scope entities whose attributes the term reads (`Event.Supplies`,
  `Term.scopeReads`), with conforming attributes. A decision fails closed when a rule that
  applies to it reads an entity the event does not supply (`FailClosed.missingScopeEntity`), so
  `Dogwood.Thm.decision_sound` derives this from the decision's checks;
* the facts of the leaf's position hold of the event's data (`Guard.Holds`): every optional
  attribute the term reads along a path of records, the Cedar part of the rule has tested
  present. `Dogwood.Thm.holds_of_holdsIn` derives this from Cedar's evaluation of the tests;
* the valuation gives each variable the term reads a value of its sort (`Valuation.SortedVar`).

This is `term_resolves`. The rest of the soundness development (`Dogwood.Thm.Soundness`) builds on
it.
-/

namespace Dogwood.Thm

open Dogwood.Spec Dogwood.Spec.Temporal
open Cedar.Spec (Value EntityUID Attr)
open Cedar.Data (Map)
open Cedar.Validation (CedarType RecordType TypeEnv Qualified)
open Cedar.Thm (InstanceOfType InstanceOfEntityType InstanceOfBoolType InstanceOfExtType)

/-! ## Sorts, guards, and instances -/

/-- A variable's value has the sort `τ` in the environment. -/
def _root_.Dogwood.Spec.Temporal.TVal.HasSort (env : TypeEnv) : TVal → TType → Prop
  | .tp _, .timepoint => True
  | .val w, .cedar ty => InstanceOfType env w ty
  | _, _ => False

/-- The valuation gives the variable `y`, if it is in scope, a value of its sort. -/
def _root_.Dogwood.Spec.Temporal.Valuation.SortedVar (env : TypeEnv) (Γ : Bindings)
    (v : Valuation) (y : VarName) : Prop :=
  ∀ τ, Γ.lookup y = some τ → ∃ w, v y = some w ∧ w.HasSort env τ

/-- The valuation gives every binder in scope a value of its sort. -/
def _root_.Dogwood.Spec.Temporal.Valuation.Sorted (env : TypeEnv) (Γ : Bindings) (v : Valuation) :
    Prop :=
  ∀ y, Valuation.SortedVar env Γ v y

/-- A scope entity's attributes, in the event's entity data. -/
def _root_.Dogwood.Spec.Event.scopeAttrs? (e : Event) (r : ScopeRoot) : Option (Map Attr Value) :=
  (e.scope r).bind fun uid => (e.entities.find? uid).map (·.attrs)

/-- The path leads through records of `r`: it is empty, or it reaches a record. -/
def RecordAlong (r : Map Attr Value) (p : Path) : Prop :=
  p = [] ∨ ∃ r', recordPath? r p = some (.record r')

/-- A guard `q.a` holds at the event when, if `q` leads through records of the request context
(or of the scope entity's attributes), the record `q` reaches has the attribute `a`. This is what
a `has` test that evaluates to `true` establishes of the event's data
(`Dogwood.Thm.holds_of_holdsIn`); typing reads only paths that lead through records. -/
def _root_.Dogwood.Spec.Temporal.Guard.Holds (e : Event) : Guard → Prop
  | .context p => ∀ q a, p = q ++ [a] → RecordAlong e.context q →
      (recordPath? e.context p).isSome = true
  | .scope r p => ∀ attrs, e.scopeAttrs? r = some attrs → ∀ q a, p = q ++ [a] →
      RecordAlong attrs q → (recordPath? attrs p).isSome = true

/-- **The event is an instance of the environment**: its principal and resource are entities of
the environment's types, and its request context is an instance of the context record type. -/
structure _root_.Dogwood.Spec.Event.InstanceOf (env : TypeEnv) (e : Event) : Prop where
  principal : ∃ pr, e.principal = some pr ∧ InstanceOfEntityType pr env.reqty.principal env
  resource : ∃ rs, e.resource = some rs ∧ InstanceOfEntityType rs env.reqty.resource env
  context : InstanceOfType env (.record e.context) (.record env.reqty.context)

/-- **The event supplies its scope entity `r`** in the environment: when the entity's type
declares attributes, the entity is in the event's entity data, with attributes of those
types. -/
def _root_.Dogwood.Spec.Event.Supplies (env : TypeEnv) (e : Event) (r : ScopeRoot) : Prop :=
  ∀ uid, e.scope r = some uid → ∀ rty, env.ets.attrs? uid.ty = some rty →
    ∃ d, e.entities.find? uid = some d ∧ InstanceOfType env (.record d.attrs) (.record rty)

theorem hasSort_val {env : TypeEnv} {w : Value} {ty : CedarType} (h : InstanceOfType env w ty) :
    (TVal.val w).HasSort env (.cedar ty) := h

/-! ## Paths -/

theorem recordPath_cons_cons (r : Map Attr Value) (a b : Attr) (p : Path) (w : Value)
    (h : r.find? a = some w) : recordPath? r (a :: b :: p) = valuePath? w (b :: p) := by
  simp [recordPath?, h]

theorem valuePath_record (r : Map Attr Value) (b : Attr) (p : Path) :
    valuePath? (.record r) (b :: p) = recordPath? r (b :: p) := by
  simp [valuePath?, recordPath?]

/-- **A typed path resolves.** In a record that is an instance of the record type, a path whose
type is `ty`, every optional attribute along it present where its prefix leads through records,
holds a value of type `ty`. -/
theorem path_resolves {env : TypeEnv} {present : Path → Bool} :
    ∀ (p : Path) (rty : RecordType) (pre : Path) (r : Map Attr Value) {ty : CedarType},
      InstanceOfType env (.record r) (.record rty) →
      (∀ q a, present (pre ++ q ++ [a]) = true → RecordAlong r q →
        (recordPath? r (q ++ [a])).isSome = true) →
      pathType? present rty pre p = some ty →
      ∃ w, recordPath? r p = some w ∧ InstanceOfType env w ty
  | [], _, _, _, _, _, _, h => by simp [pathType?] at h
  | a :: p, rty, pre, r, ty, hinst, hpres, h => by
    unfold pathType? at h
    cases hf : rty.find? a with
    | none => rw [hf] at h; cases h
    | some qty =>
      rw [hf] at h
      simp only at h
      split at h
      · rename_i hreq
        cases hinst with
        | instance_of_record _ _ h₁ h₂ h₃ =>
        -- The attribute is present: it is required, or present by `present`.
        have hpresent : ∃ w, r.find? a = some w := by
          rcases Bool.or_eq_true _ _ |>.mp hreq with hr | hr
          · have := h₃ a qty hf hr
            simp only [Map.contains, Option.isSome_iff_exists] at this
            exact this
          · have := hpres [] a (by simpa using hr) (Or.inl rfl)
            simp only [List.nil_append, recordPath?, valuePath?] at this
            cases hw : r.find? a with
            | none => rw [hw] at this; simp at this
            | some w => exact ⟨w, rfl⟩
        obtain ⟨w, hw⟩ := hpresent
        have hwty := h₂ a w qty hw hf
        cases p with
        | nil =>
          have hty : qty.getType = ty := by
            revert h
            cases qty.getType <;> simp
          subst hty
          exact ⟨w, by simp [recordPath?, hw, valuePath?], hwty⟩
        | cons b p =>
          cases hg : qty.getType with
          | record rty' =>
            rw [hg] at h hwty
            simp only at h
            cases hwty with
            | instance_of_record r' _ h₁' h₂' h₃' =>
            have hpres' : ∀ q c, present (pre ++ [a] ++ q ++ [c]) = true → RecordAlong r' q →
                (recordPath? r' (q ++ [c])).isSome = true := by
              intro q c hq hra
              have hra' : RecordAlong r (a :: q) := by
                right
                rcases hra with rfl | ⟨r'', hr''⟩
                · exact ⟨r', by simp [recordPath?, hw, valuePath?]⟩
                · cases q with
                  | nil => simp [recordPath?] at hr''
                  | cons b q =>
                    exact ⟨r'', by rw [recordPath_cons_cons r a b q _ hw, valuePath_record]; exact hr''⟩
              have := hpres (a :: q) c (by simpa using hq) hra'
              cases q with
              | nil =>
                rw [show (a :: ([] : Path)) ++ [c] = [a, c] from rfl,
                  recordPath_cons_cons r a c [] _ hw, valuePath_record] at this
                simpa using this
              | cons b q =>
                rw [show (a :: b :: q) ++ [c] = a :: b :: (q ++ [c]) from rfl,
                  recordPath_cons_cons r a b (q ++ [c]) _ hw, valuePath_record] at this
                simpa using this
            obtain ⟨w', hw', hwty'⟩ := path_resolves (b :: p) rty' (pre ++ [a]) r'
              (.instance_of_record _ _ h₁' h₂' h₃') hpres' h
            refine ⟨w', ?_, hwty'⟩
            rw [recordPath_cons_cons r a b p _ hw, valuePath_record]
            exact hw'
          | _ => rw [hg] at h; simp at h
      · cases h

/-! ## Terms -/

/-- A term that reads no variable, aggregate, or compound: a literal or a request-side path. -/
def _root_.Dogwood.Spec.Temporal.Term.Atomic : Term → Prop
  | .entity _ | .long _ | .decimal _ | .string _ | .bool _ | .context _ | .scope _ _
  | .var _ => True
  | .wildcard | .agg _ | .arith _ _ _ => False

/-- **A typed simple term resolves** to a value of its type: a literal, a request-side path at an
instance of the environment that supplies the scope entities the path reads and whose facts hold,
or a variable of a sorted valuation. -/
theorem term_resolves {C : TypingCtx} {Γ : Bindings} {t : Term} {τ : TType}
    (ht : Term.Typed C Γ t τ) (hat : t.Atomic) {e : Event} (he : e.InstanceOf C.env)
    (hsup : ∀ r ∈ t.scopeReads, e.Supplies C.env r)
    (hf : ∀ g ∈ C.facts, g.Holds e) {v : Valuation}
    (hv : ∀ y ∈ t.fv, Valuation.SortedVar C.env Γ v y) :
    ∃ w, t.eval? e v = some w ∧ w.HasSort C.env τ := by
  cases ht with
  | entity h =>
    refine ⟨_, rfl, hasSort_val (.instance_of_entity _ _ ⟨rfl, ?_⟩)⟩
    simpa [Cedar.Validation.EntityUID.WellFormed] using h
  | long => exact ⟨_, rfl, hasSort_val .instance_of_int⟩
  | decimal h =>
    obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp h
    exact ⟨.val (.ext (.decimal d)), by simp [Term.eval?, hd],
      hasSort_val (.instance_of_ext _ _ (by simp [InstanceOfExtType]))⟩
  | string => exact ⟨_, rfl, hasSort_val .instance_of_string⟩
  | bool =>
    rename_i b
    exact ⟨_, rfl, hasSort_val (.instance_of_bool _ _ (by cases b <;> simp [InstanceOfBoolType]))⟩
  | context hty hsupp =>
    rename_i p ty
    have hpres : ∀ q a, (fun q => decide (Guard.context q ∈ C.facts)) ([] ++ q ++ [a]) = true →
        RecordAlong e.context q → (recordPath? e.context (q ++ [a])).isSome = true := by
      intro q a hq hra
      have h := hf (.context (q ++ [a])) (by simpa using hq)
      unfold Guard.Holds at h
      exact h q a rfl hra
    obtain ⟨w, hw, hwty⟩ := path_resolves p _ [] _ he.context hpres hty
    exact ⟨.val w, by simp [Term.eval?, Event.contextPath?, hw], hasSort_val hwty⟩
  | scopeRoot =>
    rename_i r
    cases r with
    | principal =>
      obtain ⟨pr, hpr, hinst⟩ := he.principal
      exact ⟨.val (.prim (.entityUID pr)), by simp [Term.eval?, Event.scopePath?, Event.scope, hpr],
        hasSort_val (.instance_of_entity _ _ hinst)⟩
    | resource =>
      obtain ⟨rs, hrs, hinst⟩ := he.resource
      exact ⟨.val (.prim (.entityUID rs)), by simp [Term.eval?, Event.scopePath?, Event.scope, hrs],
        hasSort_val (.instance_of_entity _ _ hinst)⟩
  | scopeAttr hne hty hsupp =>
    rename_i r p ty
    -- The scope entity, its type the environment's, and its data.
    have hroot : ∃ uid, e.scope r = some uid ∧ uid.ty = C.scopeType r := by
      cases r with
      | principal =>
        obtain ⟨pr, hpr, hinst⟩ := he.principal
        exact ⟨pr, hpr, hinst.1.symm⟩
      | resource =>
        obtain ⟨rs, hrs, hinst⟩ := he.resource
        exact ⟨rs, hrs, hinst.1.symm⟩
    obtain ⟨uid, huid, hty_uid⟩ := hroot
    simp only [TypingCtx.scopeAttrType?] at hty
    cases hrty : C.env.ets.attrs? (C.scopeType r) with
    | none => rw [hrty] at hty; cases hty
    | some rty =>
    rw [hrty] at hty
    simp only at hty
    have hread : r ∈ (Term.scope r p).scopeReads := by
      have hne' : p.isEmpty = false := by cases p <;> simp_all
      simp [Term.scopeReads, hne']
    obtain ⟨d, hd, hinst⟩ := hsup r hread uid huid rty (by rw [hty_uid]; exact hrty)
    have hpres : ∀ q a, (fun q => decide (Guard.scope r q ∈ C.facts)) ([] ++ q ++ [a]) = true →
        RecordAlong d.attrs q → (recordPath? d.attrs (q ++ [a])).isSome = true := by
      intro q a hq hra
      have h := hf (.scope r (q ++ [a])) (by simpa using hq)
      unfold Guard.Holds at h
      exact h d.attrs (by simp [Event.scopeAttrs?, huid, hd]) q a rfl hra
    obtain ⟨w, hw, hwty⟩ := path_resolves p _ [] _ hinst hpres hty
    refine ⟨.val w, ?_, hasSort_val hwty⟩
    -- The path reads the attributes.
    have hpath : e.scopePath? r p = recordPath? d.attrs p := by
      unfold Event.scopePath?
      rw [huid]
      cases p with
      | nil => exact absurd rfl hne
      | cons a q =>
        show e.entityAttr? uid (a :: q) = _
        have hea : e.entityAttr? uid (a :: q) =
            ((e.entities.find? uid).bind (·.attrs.find? a)).bind (valuePath? · q) := rfl
        rw [hea]
        simp [hd, recordPath?]
    simp [Term.eval?, hpath, hw]
  | var hx =>
    rename_i x
    obtain ⟨w, hw, hs⟩ := hv x (by simp [Term.fv]) _ hx
    exact ⟨w, hw, hs⟩
  | agg _ => exact hat.elim
  | arith _ _ => exact hat.elim

end Dogwood.Thm
