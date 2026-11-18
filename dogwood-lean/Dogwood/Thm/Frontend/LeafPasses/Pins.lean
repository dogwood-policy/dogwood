import Dogwood.Thm.Frontend.LeafPasses.Basic

/-!
# Pin injection commutes with the projection

`LeafPasses.injectPins` on the crate's AST and the specification's `Formula.injectPins` agree
through the projection `Condition.toFormula` (`injectCond_toFormula`): the crate matches a
predicate to the derived event of its namespace, action and kind, the specification to the
signature of its projected action and kind; and the argument the crate appends, the escaped text
of the pinned field's path with the pin's request-side term, projects to the specification's
`(field, ref)`. The hypotheses are what makes the two matches and the two arguments agree: the
derived schema projects to the specification's (`Agrees`, `injectCond_toFormula_of_agrees`), and
the leaf's predicate namespaces are determined by the entity types they project to
(`NamespacesFaithful`).
-/

namespace Dogwood.Thm.Frontend

open Dogwood.Frontend Dogwood.Frontend.LeafPasses Surface.Temporal
open Dogwood.Spec (EventSchema PinRef)
open Dogwood.Spec.Temporal (Formula Aggregate)

mutual

/-- The namespaces of the predicates pin injection reaches. -/
def predNamespaces : Condition → List (List String)
  | ⟨_, k⟩ => kindPredNamespaces k

def kindPredNamespaces : ConditionKind → List (List String)
  | .and l r => predNamespaces l ++ predNamespaces r
  | .or l r => predNamespaces l ++ predNamespaces r
  | .since l _ r => predNamespaces l ++ predNamespaces r
  | .not c => predNamespaces c
  | .formerly _ c => predNamespaces c
  | .previous _ c => predNamespaces c
  | .exists _ c => predNamespaces c
  | .predicate p => [p.namespace]
  | .refine b _ _ => predNamespaces b
  | .comparison _ l r => termPredNamespaces l ++ termPredNamespaces r
  | .tp _ => []
  | .call _ => []
  | .sigilRef _ _ => []

def termPredNamespaces : Surface.Temporal.Term → List (List String)
  | .agg ⟨_, k⟩ => aggPredNamespaces k
  | .arith _ l r => termPredNamespaces l ++ termPredNamespaces r
  | _ => []

def aggPredNamespaces : AggExprKind → List (List String)
  | .sum _ _ b => predNamespaces b
  | .count _ b => predNamespaces b
  | .call _ => []

end

/-- The namespace of each predicate of the leaf is determined by the entity type its action
projects to, among the derived events' namespaces: the crate matches a predicate to an event by its
namespace, the specification by the projected action. (Expected when no namespace segment
holds `::`; not yet proved.) -/
def NamespacesFaithful (d : DerivedEventSchema) (nss : List (List String)) : Prop :=
  ∀ ns ∈ nss, ∀ ev ∈ d.events, ∀ a u, entityUid ("::".intercalate ns) a = .ok u →
    u.ty = (actionUid ev.namespace ev.action).ty → ns = ev.namespace

/-- The derived event a predicate names and the specification's signature for its projected
action carry the same pins. -/
theorem pinsFor_toSpec {ns : List String} {a k : String} {uid : Cedar.Spec.EntityUID}
    (hu : entityUid ("::".intercalate ns) a = .ok uid) :
    (evs : List DerivedEvent) → {S : EventSchema} →
    evs.mapM eventToSpec = .ok S →
    (∀ ev ∈ evs, entityUid ("::".intercalate ev.namespace) ev.action =
      .ok (actionUid ev.namespace ev.action)) →
    (∀ ev ∈ evs, ∀ u, entityUid ("::".intercalate ns) a = .ok u →
      u.ty = (actionUid ev.namespace ev.action).ty → ns = ev.namespace) →
    List.mapM Pin.toSpec
      (((evs.find? fun e => e.action == a && e.kind == k && e.namespace == ns).map (·.pins)).getD []) =
      .ok (S.pinsOf uid k)
  | [], S, h, _, _ => by
    simp only [List.mapM_nil, pure_eq_ok] at h; subst h
    simp [EventSchema.pinsOf, EventSchema.signature?, pure, Except.pure]
  | ev :: evs, S, h, hn, hf => by
    simp only [List.mapM_cons, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨s, hs, S', hS', rfl⟩ := h
    simp only [eventToSpec, bind_eq_ok, pure_eq_ok] at hs
    obtain ⟨qs, hqs, rfl⟩ := hs
    have hiff : (ev.action == a && ev.kind == k && ev.namespace == ns) =
        (actionUid ev.namespace ev.action == uid && ev.kind == k) := by
      have key : (ev.action = a ∧ ev.namespace = ns) ↔ actionUid ev.namespace ev.action = uid := by
        constructor
        · rintro ⟨rfl, rfl⟩
          have := hn ev List.mem_cons_self
          rw [hu] at this
          exact (Except.ok.inj this).symm
        · intro he
          have hea : ev.action = a := by
            have h1 : (actionUid ev.namespace ev.action).eid = ev.action := rfl
            rw [← h1, he]; exact entityUid_eid hu
          exact ⟨hea, (hf ev List.mem_cons_self uid hu (by rw [he])).symm⟩
      rw [Bool.eq_iff_iff]
      simp only [Bool.and_eq_true, beq_iff_eq]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨key.mp ⟨h1, h3⟩, h2⟩
      · rintro ⟨h1, h2⟩; obtain ⟨h3, h4⟩ := key.mpr h1; exact ⟨⟨h3, h2⟩, h4⟩
    simp only [List.find?_cons, EventSchema.pinsOf, EventSchema.signature?, hiff]
    cases hc : (actionUid ev.namespace ev.action == uid && ev.kind == k)
    · have := pinsFor_toSpec (k := k) hu evs hS' (fun e he => hn e (List.mem_cons_of_mem _ he))
        (fun e he => hf e (List.mem_cons_of_mem _ he))
      simpa [EventSchema.pinsOf, EventSchema.signature?] using this
    · simpa using hqs


theorem NamespacesFaithful.mono {d : DerivedEventSchema} {A B : List (List String)}
    (h : NamespacesFaithful d B) (hsub : ∀ x ∈ A, x ∈ B) : NamespacesFaithful d A :=
  fun ns hns => h ns (hsub ns hns)

theorem pinsFor_eq (d : DerivedEventSchema) (ns : List String) (a k : String) :
    pinsFor d ns a k = ((eventOf d ns a k).map (·.pins)).getD [] := by
  unfold pinsFor; cases eventOf d ns a k <;> rfl

theorem mem_pinsFor {d : DerivedEventSchema} {ns : List String} {a k : String} {p : Pin}
    (h : p ∈ pinsFor d ns a k) : ∃ ev ∈ d.events, p ∈ ev.pins := by
  unfold pinsFor at h
  cases he : eventOf d ns a k with
  | none => simp [he] at h
  | some ev =>
    simp only [he] at h
    exact ⟨ev, List.mem_of_find?_eq_some he, h⟩

theorem injectPins_specAtom {S : EventSchema} {t : Dogwood.Spec.Temporal.Term} (ht : SpecAtom t) :
    t.injectPins S = t := by
  cases t <;> first | exact absurd ht id | rfl

section
variable {d : DerivedEventSchema} {S : EventSchema}

mutual

/-- **Pin injection commutes with the projection** to the specification's formulas, and with the
specification's own pin injection. -/
theorem injectCond_toFormula (hS : d.events.mapM eventToSpec = .ok S)
    (hnames : ∀ ev ∈ d.events,
      entityUid ("::".intercalate ev.namespace) ev.action = .ok (actionUid ev.namespace ev.action))
    (hpaths : ∀ ev ∈ d.events, ∀ p ∈ ev.pins, fieldPathSplit (fieldPathJoin p.fieldPath) = p.fieldPath) :
    (c : Condition) → NamespacesFaithful d (predNamespaces c) →
    (injectCond d c).toFormula = (c.toFormula).map (·.injectPins S)
  | ⟨sp, .and l r⟩, hf => by
    have hl := injectCond_toFormula hS hnames hpaths l (hf.mono fun x h => List.mem_append_left _ h)
    have hr := injectCond_toFormula hS hnames hpaths r (hf.mono fun x h => List.mem_append_right _ h)
    simp only [injectCond, injectKind, Condition.toFormula, ConditionKind.toFormula, hl, hr]
    cases l.toFormula <;> cases r.toFormula <;> rfl
  | ⟨sp, .or l r⟩, _ => rfl
  | ⟨sp, .since l w r⟩, hf => by
    have hl := injectCond_toFormula hS hnames hpaths l (hf.mono fun x h => List.mem_append_left _ h)
    have hr := injectCond_toFormula hS hnames hpaths r (hf.mono fun x h => List.mem_append_right _ h)
    simp only [injectCond, injectKind, Condition.toFormula, ConditionKind.toFormula, hl, hr]
    cases l.toFormula <;> cases w.toSpec <;> cases r.toFormula <;> rfl
  | ⟨sp, .not c⟩, hf => by
    have hc := injectCond_toFormula hS hnames hpaths c hf
    simp only [injectCond, injectKind, Condition.toFormula, ConditionKind.toFormula, hc]
    cases c.toFormula <;> rfl
  | ⟨sp, .formerly w c⟩, hf => by
    have hc := injectCond_toFormula hS hnames hpaths c hf
    simp only [injectCond, injectKind, Condition.toFormula, ConditionKind.toFormula, hc]
    cases w.toSpec <;> cases c.toFormula <;> rfl
  | ⟨sp, .previous w c⟩, hf => by
    have hc := injectCond_toFormula hS hnames hpaths c hf
    simp only [injectCond, injectKind, Condition.toFormula, ConditionKind.toFormula, hc]
    cases w.toSpec <;> cases c.toFormula <;> rfl
  | ⟨sp, .exists x c⟩, hf => by
    have hc := injectCond_toFormula hS hnames hpaths c hf
    simp only [injectCond, injectKind, Condition.toFormula, ConditionKind.toFormula, hc]
    cases x.toSpec <;> cases c.toFormula <;> rfl
  | ⟨sp, .comparison op l r⟩, hf => by
    have hl := injectTerm_toSpec hS hnames hpaths l (hf.mono fun x h => List.mem_append_left _ h)
    have hr := injectTerm_toSpec hS hnames hpaths r (hf.mono fun x h => List.mem_append_right _ h)
    simp only [injectCond, injectKind, Condition.toFormula, ConditionKind.toFormula, hl, hr]
    cases l.toSpec <;> cases r.toSpec <;> rfl
  | ⟨sp, .predicate ⟨psp, ns, a, k, args⟩⟩, hf => by
    simp only [injectCond, injectKind, injectPred, Condition.toFormula, ConditionKind.toFormula]
    cases hu : entityUid ("::".intercalate ns) a with
    | error _ => rfl
    | ok uid =>
      have hfaith : ∀ ev ∈ d.events, ∀ u, entityUid ("::".intercalate ns) a = .ok u →
          u.ty = (actionUid ev.namespace ev.action).ty → ns = ev.namespace :=
        fun ev hev u hu' hty => hf ns (by simp [predNamespaces, kindPredNamespaces]) ev hev a u hu' hty
      have hpins := pinsFor_toSpec (k := k) hu d.events hS hnames hfaith
      rw [← eventOf.eq_def, ← pinsFor_eq] at hpins
      have hp : ∀ p ∈ pinsFor d ns a k, fieldPathSplit (fieldPathJoin p.fieldPath) = p.fieldPath := by
        intro p hp
        obtain ⟨ev, hev, hpe⟩ := mem_pinsFor hp
        exact hpaths ev hev p hpe
      have hargs := pinArgs_toSpecList _ hpins hp
      simp only [toSpecList_append, hargs]
      cases NamedArg.toSpecList args <;> rfl
  | ⟨sp, .tp x⟩, _ => by
    simp only [injectCond, injectKind, Condition.toFormula, ConditionKind.toFormula]
    cases x.toName <;> rfl
  | ⟨sp, .call _⟩, _ => rfl
  | ⟨sp, .sigilRef _ _⟩, _ => rfl
  | ⟨sp, .refine _ _ _⟩, _ => rfl

theorem injectTerm_toSpec (hS : d.events.mapM eventToSpec = .ok S)
    (hnames : ∀ ev ∈ d.events,
      entityUid ("::".intercalate ev.namespace) ev.action = .ok (actionUid ev.namespace ev.action))
    (hpaths : ∀ ev ∈ d.events, ∀ p ∈ ev.pins, fieldPathSplit (fieldPathJoin p.fieldPath) = p.fieldPath) :
    (t : Surface.Temporal.Term) → NamespacesFaithful d (termPredNamespaces t) →
    (injectTerm d t).toSpec = (t.toSpec).map (·.injectPins S)
  | .agg ⟨sp, k⟩, hf => by
    have hk := injectAgg_toSpec hS hnames hpaths k hf
    simp only [injectTerm, injectAgg, Surface.Temporal.Term.toSpec, hk]
    cases AggExprKind.toSpec k <;> rfl
  | .arith op l r, hf => by
    have hl := injectTerm_toSpec hS hnames hpaths l (hf.mono fun x h => List.mem_append_left _ h)
    have hr := injectTerm_toSpec hS hnames hpaths r (hf.mono fun x h => List.mem_append_right _ h)
    simp only [injectTerm, Surface.Temporal.Term.toSpec, hl, hr]
    cases l.toSpec <;> cases r.toSpec <;> rfl
  | .entity ty id, _ => atom (.entity ty id) trivial
  | .integer i, _ => atom (.integer i) trivial
  | .decimal x, _ => atom (.decimal x) trivial
  | .string x, _ => atom (.string x) trivial
  | .bool x, _ => atom (.bool x) trivial
  | .contextField x, _ => atom (.contextField x) trivial
  | .scopeField x, _ => atom (.scopeField x) trivial
  | .var x, _ => atom (.var x) trivial
  | .wildcard, _ => atom .wildcard trivial
  | .array x, _ => atom (.array x) trivial
  | .paramRef x, _ => atom (.paramRef x) trivial
  | .binderRef x, _ => atom (.binderRef x) trivial
where
  atom (t : Surface.Temporal.Term) (ht : TermAtom t) :
      (injectTerm d t).toSpec = (t.toSpec).map (·.injectPins S) := by
    have hi : injectTerm d t = t := by cases t <;> first | exact absurd ht id | rfl
    rw [hi]
    cases h : t.toSpec with
    | error _ => rfl
    | ok t' => simp [Except.map, injectPins_specAtom (toSpec_atom ht h)]

theorem injectAgg_toSpec (hS : d.events.mapM eventToSpec = .ok S)
    (hnames : ∀ ev ∈ d.events,
      entityUid ("::".intercalate ev.namespace) ev.action = .ok (actionUid ev.namespace ev.action))
    (hpaths : ∀ ev ∈ d.events, ∀ p ∈ ev.pins, fieldPathSplit (fieldPathJoin p.fieldPath) = p.fieldPath) :
    (k : AggExprKind) → NamespacesFaithful d (aggPredNamespaces k) →
    (injectAggKind d k).toSpec = (k.toSpec).map (·.injectPins S)
  | .count vs b, hf => by
    have hb := injectCond_toFormula hS hnames hpaths b hf
    simp only [injectAggKind, AggExprKind.toSpec, hb]
    cases vs.mapM TypedBinder.toSpec <;> cases b.toFormula <;> rfl
  | .sum v vs b, hf => by
    have hb := injectCond_toFormula hS hnames hpaths b hf
    simp only [injectAggKind, AggExprKind.toSpec, hb]
    cases v.toName <;> cases vs.mapM TypedBinder.toSpec <;> cases b.toFormula <;> rfl
  | .call _, _ => rfl

end

end


mutual

theorem injectPins_strip (S : EventSchema) : (φ : Formula) → φ.injectPins (strip S) = φ.injectPins S
  | .and φ ψ => by simp only [Formula.injectPins, injectPins_strip S φ, injectPins_strip S ψ]
  | .not φ => by simp only [Formula.injectPins, injectPins_strip S φ]
  | .formerly _ φ => by simp only [Formula.injectPins, injectPins_strip S φ]
  | .previous _ φ => by simp only [Formula.injectPins, injectPins_strip S φ]
  | .since φ _ ψ => by simp only [Formula.injectPins, injectPins_strip S φ, injectPins_strip S ψ]
  | .pred a k args => by simp only [Formula.injectPins, pinsOf_strip]
  | .cmp _ l r => by simp only [Formula.injectPins, termInjectPins_strip S l, termInjectPins_strip S r]
  | .exist _ φ => by simp only [Formula.injectPins, injectPins_strip S φ]
  | .tp _ => rfl

theorem termInjectPins_strip (S : EventSchema) :
    (t : Dogwood.Spec.Temporal.Term) → t.injectPins (strip S) = t.injectPins S
  | .agg a => by simp only [Dogwood.Spec.Temporal.Term.injectPins, aggInjectPins_strip S a]
  | .arith _ l r => by
    simp only [Dogwood.Spec.Temporal.Term.injectPins, termInjectPins_strip S l, termInjectPins_strip S r]
  | .entity _ | .long _ | .decimal _ | .string _ | .bool _ | .context _ | .scope _ _ | .var _
  | .wildcard => rfl

theorem aggInjectPins_strip (S : EventSchema) : (a : Aggregate) → a.injectPins (strip S) = a.injectPins S
  | .count _ body => by simp only [Aggregate.injectPins, injectPins_strip S body]
  | .sum _ _ body => by simp only [Aggregate.injectPins, injectPins_strip S body]

end

/-- **Pin injection projects to the specification's**: on a leaf that projects to `φ`, over a
derived schema that agrees with the specification's `S`, the projection of the pinned leaf is
`φ.injectPins S`. -/
theorem injectCond_toFormula_of_agrees {d : DerivedEventSchema} {S : EventSchema} (h : Agrees d S)
    {c : Condition} (hf : NamespacesFaithful d (predNamespaces c)) {φ : Formula}
    (hc : c.toFormula = .ok φ) : (injectCond d c).toFormula = .ok (φ.injectPins S) := by
  have hS : d.events.mapM eventToSpec = .ok (strip S) := h.untyped
  rw [injectCond_toFormula hS h.names h.paths c hf, hc]
  simp [Except.map, injectPins_strip]

/-- The same, for the pass as the frontend runs it. -/
theorem injectPins_toFormula {d : DerivedEventSchema} {S : EventSchema} (h : Agrees d S)
    {c : Condition} (hf : NamespacesFaithful d (predNamespaces c)) {φ : Formula}
    (hc : c.toFormula = .ok φ) :
    ∃ c', LeafPasses.injectPins d c = .ok c' ∧ c'.toFormula = .ok (φ.injectPins S) :=
  ⟨_, rfl, injectCond_toFormula_of_agrees h hf hc⟩

end Dogwood.Thm.Frontend
