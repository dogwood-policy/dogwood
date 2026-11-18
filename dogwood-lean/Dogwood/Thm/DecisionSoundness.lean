import Dogwood.Thm.CedarSoundness
import Dogwood.Thm.Guards

/-!
# Soundness at the request

`Dogwood.Thm.soundness` states the soundness of the temporal part for every environment a rule
admits of which the decision event is an instance, at a position whose facts hold of the event's
data. This module discharges those hypotheses from the decision's own checks, for the leaves the
response depends on:

* a fact that Cedar's `has` test establishes at the request (`Guard.HoldsIn`) holds of the
  event's data (`holds_of_holdsIn`);
* a rule whose scope holds at the request (`Policy.ScopeHolds`) admits the request's environment
  (`admits_of_scopeHolds`);
* an admitted decision event is an instance of its request's environment
  (`instanceOf_of_admits`);
* an admitted decision event supplies, with conforming attributes, every scope entity whose
  attributes a temporal leaf of a rule whose scope holds reads (`supplied_of_admits`,
  `supplies_of_admits`): the decision fails closed otherwise (`FailClosed.missingScopeEntity`).

A response depends on a leaf only where its rule's scope and its facts hold
(`isAuthorized_congr_scope`), and every such temporal leaf is sound (`decision_sound`), with no
hypothesis beyond the decision's checks and the conformance of the trace.
-/

namespace Dogwood.Thm

open Dogwood.Spec Dogwood.Spec.Temporal
open Cedar.Spec (Value Attr Request Entities EntityUID EntityData Var Result)
open Cedar.Data (Map Set)
open Cedar.Validation (TypeEnv Schema)
open Cedar.Thm (InstanceOfType InstanceOfRequestType InstanceOfSchema)

/-! ## Attribute chains -/

theorem attrChainExpr_eq_foldl (root : Var) (p : Path) :
    attrChainExpr root p = p.foldl (fun x a => Cedar.Spec.Expr.getAttr x a) (.var root) := by
  cases p <;> rfl

theorem attrChainExpr_snoc (root : Var) (p : Path) (b : Attr) :
    attrChainExpr root (p ++ [b]) = .getAttr (attrChainExpr root p) b := by
  rw [attrChainExpr_eq_foldl, attrChainExpr_eq_foldl, List.foldl_append]
  rfl

theorem evaluate_getAttr_record {x : Cedar.Spec.Expr} {req : Request} {es : Entities}
    {r : Map Attr Value} (h : Cedar.Spec.evaluate x req es = .ok (.record r)) (a : Attr) :
    Cedar.Spec.evaluate (.getAttr x a) req es = r.findOrErr a .attrDoesNotExist := by
  simp [Cedar.Spec.evaluate, h, Cedar.Spec.getAttr, Cedar.Spec.attrsOf]

theorem evaluate_hasAttr_record {x : Cedar.Spec.Expr} {req : Request} {es : Entities}
    {r : Map Attr Value} (h : Cedar.Spec.evaluate x req es = .ok (.record r)) (a : Attr) :
    Cedar.Spec.evaluate (.hasAttr x a) req es = .ok (.prim (.bool (r.contains a))) := by
  simp [Cedar.Spec.evaluate, h, Cedar.Spec.hasAttr, Cedar.Spec.attrsOf]

/-- Along a record path, Cedar's attribute chain evaluates to the record the path reaches. -/
theorem evaluate_chain_record {root : Var} {req : Request} {es : Entities} :
    ∀ (q pre : Path) (r₀ r' : Map Attr Value),
      Cedar.Spec.evaluate (attrChainExpr root pre) req es = .ok (.record r₀) →
      recordPath? r₀ q = some (.record r') →
      Cedar.Spec.evaluate (attrChainExpr root (pre ++ q)) req es = .ok (.record r')
  | [], _, _, _, _, h => by simp [recordPath?] at h
  | a :: q, pre, r₀, r', h0, h => by
    simp only [recordPath?] at h
    cases hw : r₀.find? a with
    | none => rw [hw] at h; cases h
    | some w =>
      rw [hw] at h
      simp only [Option.bind_some] at h
      have h1 : Cedar.Spec.evaluate (attrChainExpr root (pre ++ [a])) req es = .ok w := by
        rw [attrChainExpr_snoc, evaluate_getAttr_record h0]
        simp [Map.findOrErr, hw]
      cases q with
      | nil =>
        simp only [valuePath?, Option.some.injEq] at h
        subst h
        simpa using h1
      | cons b q =>
        cases w with
        | record r₁ =>
          rw [valuePath_record] at h
          have := evaluate_chain_record (b :: q) (pre ++ [a]) r₁ r' h1 h
          simpa using this
        | _ => simp [valuePath?] at h

/-- An attribute chain that errs keeps erring. -/
theorem evaluate_chain_error {root : Var} {req : Request} {es : Entities} :
    ∀ (q pre : Path) {err : Cedar.Spec.Error},
      Cedar.Spec.evaluate (attrChainExpr root pre) req es = .error err →
      ∃ err', Cedar.Spec.evaluate (attrChainExpr root (pre ++ q)) req es = .error err'
  | [], pre, err, h => ⟨err, by simpa using h⟩
  | a :: q, pre, err, h => by
    have h1 : Cedar.Spec.evaluate (attrChainExpr root (pre ++ [a])) req es = .error err := by
      rw [attrChainExpr_snoc]
      simp [Cedar.Spec.evaluate, h]
    obtain ⟨err', h'⟩ := evaluate_chain_error q (pre ++ [a]) h1
    exact ⟨err', by simpa using h'⟩

theorem recordPath_snoc : ∀ {r : Map Attr Value} {q : Path} {r' : Map Attr Value} (a : Attr),
    recordPath? r q = some (.record r') → recordPath? r (q ++ [a]) = r'.find? a
  | _, [], _, _, h => by simp [recordPath?] at h
  | r, b :: q, r', a, h => by
    simp only [recordPath?, List.cons_append] at h ⊢
    cases hw : r.find? b with
    | none => rw [hw] at h; cases h
    | some w =>
      rw [hw] at h
      simp only [Option.bind_some] at h ⊢
      cases q with
      | nil =>
        simp only [valuePath?, Option.some.injEq] at h
        subst h
        show valuePath? (.record r') [a] = r'.find? a
        simp only [valuePath?]
        cases r'.find? a <;> rfl
      | cons c q =>
        cases w with
        | record r₁ =>
          rw [valuePath_record] at h
          rw [List.cons_append, valuePath_record]
          exact recordPath_snoc a h
        | _ => simp [valuePath?] at h

theorem contains_isSome {r : Map Attr Value} {a : Attr} (h : r.contains a = true) :
    (r.find? a).isSome = true := by
  simpa [Map.contains] using h

/-! ## The decision's entity store -/

theorem find?_make_toList_append {β : Type} (m₁ m₂ : Map EntityUID β) (k : EntityUID) :
    (Map.make (m₁.toList ++ m₂.toList)).find? k = (m₁.find? k).or (m₂.find? k) := by
  rw [Map.make_find?_eq_list_find?, List.find?_append]
  unfold Map.find?
  cases h₁ : m₁.toList.find? (fun x => x.fst == k) <;>
    cases h₂ : m₂.toList.find? (fun x => x.fst == k) <;> simp_all

/-- The decision's store finds an action of the schema as the schema declares it, and any other
entity in the supplied data. -/
theorem decisionEntities_find? (P : PolicySet) (e : Event) (uid : EntityUID) :
    (P.decisionEntities e).find? uid =
      ((P.actionSchema.acts.find? uid).map Cedar.Validation.actionSchemaEntryToEntityData).or
        (e.entities.find? uid) := by
  unfold PolicySet.decisionEntities PolicySet.actionEntities
  rw [find?_make_toList_append, Map.find?_mapOnValues]

/-! ## Facts -/

/-- **A fact Cedar establishes holds of the data.** A `has` test that evaluates to `true` at a
decision event's request and store establishes its fact of the event's data. -/
theorem holds_of_holdsIn {P : PolicySet} {e : Event} {pr rs : EntityUID}
    (hpr : e.principal = some pr) (hrs : e.resource = some rs) {g : Guard}
    (h : g.HoldsIn (e.request pr rs) (P.decisionEntities e)) : g.Holds e := by
  cases g with
  | context p =>
    unfold Guard.Holds
    intro q a hp hra
    subst hp
    simp only [Guard.HoldsIn, Guard.expr, test_append] at h
    -- The chain to `q` evaluates to the record `q` reaches.
    have hchain : ∃ r', Cedar.Spec.evaluate (attrChainExpr .context q) (e.request pr rs)
        (P.decisionEntities e) = .ok (.record r') ∧ recordPath? e.context (q ++ [a]) = r'.find? a := by
      have h0 : Cedar.Spec.evaluate (attrChainExpr .context []) (e.request pr rs)
          (P.decisionEntities e) = .ok (.record e.context) := by
        simp [attrChainExpr, Cedar.Spec.evaluate, Event.request]
      rcases hra with rfl | ⟨r', hr'⟩
      · exact ⟨e.context, h0, by simp [recordPath?, valuePath?]⟩
      · exact ⟨r', by simpa using evaluate_chain_record q [] e.context r' h0 hr',
          recordPath_snoc a hr'⟩
    obtain ⟨r', hev, hpath⟩ := hchain
    rw [evaluate_hasAttr_record hev] at h
    simp only [Except.ok.injEq, Value.prim.injEq, Cedar.Spec.Prim.bool.injEq] at h
    rw [hpath]
    exact contains_isSome h
  | scope root p =>
    unfold Guard.Holds
    intro attrs hattrs q a hp hra
    subst hp
    -- The scope entity and its supplied data.
    obtain ⟨uid, huid, hda⟩ : ∃ uid, e.scope root = some uid ∧
        (e.entities.find? uid).map (·.attrs) = some attrs := by
      unfold Event.scopeAttrs? at hattrs
      cases hs : e.scope root with
      | none => rw [hs] at hattrs; cases hattrs
      | some uid => rw [hs] at hattrs; exact ⟨uid, rfl, hattrs⟩
    obtain ⟨d, hd, rfl⟩ : ∃ d, e.entities.find? uid = some d ∧ d.attrs = attrs := by
      cases hf : e.entities.find? uid with
      | none => rw [hf] at hda; cases hda
      | some d => rw [hf] at hda; exact ⟨d, rfl, by simpa using hda⟩
    clear hda hattrs
    -- The root variable evaluates to the scope entity.
    have hvar : ∃ v : Var, Guard.expr (.scope root (q ++ [a])) =
        .hasAttr (attrChainExpr v q) a ∧
        Cedar.Spec.evaluate (.var v) (e.request pr rs) (P.decisionEntities e) =
          .ok (.prim (.entityUID uid)) := by
      cases root with
      | principal =>
        refine ⟨.principal, by simp [Guard.expr, test_append], ?_⟩
        simp only [Event.scope, hpr, Option.some.injEq] at huid
        subst huid
        simp [Cedar.Spec.evaluate, Event.request]
      | resource =>
        refine ⟨.resource, by simp [Guard.expr, test_append], ?_⟩
        simp only [Event.scope, hrs, Option.some.injEq] at huid
        subst huid
        simp [Cedar.Spec.evaluate, Event.request]
    obtain ⟨v, hexpr, hev⟩ := hvar
    simp only [Guard.HoldsIn, hexpr] at h
    -- The store's entry for the scope entity.
    obtain ⟨d', hfind, hd'⟩ : ∃ d', (P.decisionEntities e).find? uid = some d' ∧
        (d'.attrs = Map.empty ∨ d' = d) := by
      have hf := decisionEntities_find? P e uid
      cases hact : P.actionSchema.acts.find? uid with
      | some entry =>
        rw [hact] at hf
        simp only [Option.map_some, Option.some_or] at hf
        exact ⟨_, hf, .inl rfl⟩
      | none =>
        rw [hact, hd] at hf
        simp only [Option.map_none, Option.none_or] at hf
        exact ⟨d, hf, .inr rfl⟩
    have hhas : ∀ b, Cedar.Spec.evaluate (.hasAttr (.var v) b) (e.request pr rs)
        (P.decisionEntities e) = .ok (.prim (.bool (d'.attrs.contains b))) := by
      intro b
      simp [Cedar.Spec.evaluate, hev, Cedar.Spec.hasAttr, Cedar.Spec.attrsOf,
        Entities.attrsOrEmpty, hfind]
    have hget : ∀ b, Cedar.Spec.evaluate (.getAttr (.var v) b) (e.request pr rs)
        (P.decisionEntities e) = d'.attrs.findOrErr b .attrDoesNotExist := by
      intro b
      simp [Cedar.Spec.evaluate, hev, Cedar.Spec.getAttr, Cedar.Spec.attrsOf,
        Entities.attrs, Map.findOrErr, hfind]
    have hempty : ∀ b, (Map.empty : Map Attr Value).find? b = none := fun b => rfl
    cases q with
    | nil =>
      rw [show attrChainExpr v [] = .var v from rfl, hhas] at h
      simp only [Except.ok.injEq, Value.prim.injEq, Cedar.Spec.Prim.bool.injEq] at h
      have hc := contains_isSome h
      rcases hd' with he' | rfl
      · rw [he', hempty] at hc; cases hc
      · simpa [recordPath?, valuePath?] using hc
    | cons b q =>
      rcases hra with hnil | ⟨r', hr'⟩
      · cases hnil
      rcases hd' with he' | rfl
      · -- An action of the schema has no attributes: the chain errs.
        exfalso
        have h1 : Cedar.Spec.evaluate (attrChainExpr v ([] ++ [b])) (e.request pr rs)
            (P.decisionEntities e) = .error .attrDoesNotExist := by
          rw [List.nil_append, show attrChainExpr v [b] = .getAttr (.var v) b from rfl, hget, he']
          simp [Map.findOrErr, hempty]
        obtain ⟨err', h'⟩ := evaluate_chain_error q ([] ++ [b]) h1
        have : Cedar.Spec.evaluate (.hasAttr (attrChainExpr v (b :: q)) a) (e.request pr rs)
            (P.decisionEntities e) = .error err' := by
          simp only [List.nil_append, List.singleton_append] at h'
          simp [Cedar.Spec.evaluate, h']
        rw [this] at h
        cases h
      · -- The chain to `b :: q` evaluates to the record the path reaches.
        have hev' : Cedar.Spec.evaluate (attrChainExpr v (b :: q)) (e.request pr rs)
            (P.decisionEntities e) = .ok (.record r') := by
          simp only [recordPath?] at hr'
          cases hw : d'.attrs.find? b with
          | none => rw [hw] at hr'; cases hr'
          | some w =>
            rw [hw] at hr'
            simp only [Option.bind_some] at hr'
            have hb : Cedar.Spec.evaluate (attrChainExpr v ([] ++ [b])) (e.request pr rs)
                (P.decisionEntities e) = .ok w := by
              rw [List.nil_append, show attrChainExpr v [b] = .getAttr (.var v) b from rfl, hget]
              simp [Map.findOrErr, hw]
            cases q with
            | nil =>
              simp only [valuePath?, Option.some.injEq] at hr'
              subst hr'
              simpa using hb
            | cons c q =>
              cases w with
              | record r₁ =>
                rw [valuePath_record] at hr'
                simpa using evaluate_chain_record (c :: q) ([] ++ [b]) r₁ r' hb hr'
              | _ => simp [valuePath?] at hr'
        rw [evaluate_hasAttr_record hev'] at h
        simp only [Except.ok.injEq, Value.prim.injEq, Cedar.Spec.Prim.bool.injEq] at h
        rw [recordPath_snoc a hr']
        exact contains_isSome h

/-! ## Rules whose scope holds -/

theorem isTrueResult_iff {r : Cedar.Spec.Result Value} :
    isTrueResult r = true ↔ r = .ok (.prim (.bool true)) := by
  unfold isTrueResult
  split <;> simp_all

/-- `Policy.scopeHolds` decides `Policy.ScopeHolds`. -/
theorem scopeHolds_iff {p : Policy} {req : Request} {es : Entities} :
    p.scopeHolds req es = true ↔ p.ScopeHolds req es := by
  simp only [Policy.scopeHolds, Policy.ScopeHolds, Bool.and_eq_true, isTrueResult_iff, and_assoc]

theorem evaluate_and_congr {θ₁ θ₂ : Leaves} {req : Request} {es : Entities} {a b : Expr}
    (ha : evaluate θ₁ a req es = evaluate θ₂ a req es)
    (hb : evaluate θ₁ a req es = .ok (.prim (.bool true)) →
      evaluate θ₁ b req es = evaluate θ₂ b req es) :
    evaluate θ₁ (.and a b) req es = evaluate θ₂ (.and a b) req es := by
  simp only [evaluate]
  rw [← ha]
  cases hab : (evaluate θ₁ a req es).as Bool with
  | error e => rfl
  | ok b₁ =>
    cases b₁ with
    | false => rfl
    | true => simp [hb (as_bool_true hab)]

/-- **A rule's evaluation depends on a leaf only where the rule's scope and the leaf's facts
hold.** -/
theorem evaluate_toExpr_congr {θ₁ θ₂ : Leaves} {req : Request} {es : Entities} (p : Policy)
    (h : p.ScopeHolds req es → ∀ l F, (l, F) ∈ p.toExpr.leafFacts [] →
      (∀ g ∈ F, g.HoldsIn req es) → LeafAgree θ₁ θ₂ l) :
    evaluate θ₁ p.toExpr req es = evaluate θ₂ p.toExpr req es := by
  have hc : ∀ x : Cedar.Spec.Expr,
      evaluate θ₁ (Expr.ofCedar x) req es = evaluate θ₂ (Expr.ofCedar x) req es := fun x => by
    rw [evaluate_ofCedar, evaluate_ofCedar]
  unfold Policy.toExpr
  refine evaluate_and_congr (hc _) fun h₁ => evaluate_and_congr (hc _) fun h₂ =>
    evaluate_and_congr (hc _) fun h₃ => ?_
  have hs : p.ScopeHolds req es := by
    rw [evaluate_ofCedar] at h₁ h₂ h₃
    exact ⟨h₁, h₂, h₃⟩
  have hF : ∀ g ∈ [] ++ (Expr.ofCedar p.principalScope.toExpr).facts ++
      (Expr.ofCedar p.actionScope.toExpr).facts ++ (Expr.ofCedar p.resourceScope.toExpr).facts,
      g.HoldsIn req es := by
    intro g hg
    simp only [List.nil_append, List.mem_append] at hg
    rcases hg with (hg | hg) | hg
    · exact facts_hold _ h₁ g hg
    · exact facts_hold _ h₂ g hg
    · exact facts_hold _ h₃ g hg
  exact evaluate_congr_facts θ₁ θ₂ req es _ _ hF fun l F hm hF' =>
    h hs l F (by simp only [Policy.toExpr, Expr.leafFacts, List.mem_append]; exact .inr (.inr (.inr hm))) hF'

/-- **A response depends on a leaf only where its rule's scope and its facts hold.** Two leaf
valuations that agree, on every rule whose scope holds at the request, on every leaf whose facts
hold, give the same response. -/
theorem isAuthorized_congr_scope {θ₁ θ₂ : Leaves} {req : Request} {es : Entities} {ps : Policies}
    (h : ∀ p ∈ ps, p.ScopeHolds req es → ∀ l F, (l, F) ∈ p.toExpr.leafFacts [] →
      (∀ g ∈ F, g.HoldsIn req es) → LeafAgree θ₁ θ₂ l) :
    isAuthorized θ₁ req es ps = isAuthorized θ₂ req es ps := by
  have he : ∀ p ∈ ps, evaluate θ₁ p.toExpr req es = evaluate θ₂ p.toExpr req es := fun p hp =>
    evaluate_toExpr_congr p (h p hp)
  have hsat : ∀ p ∈ ps, satisfied θ₁ p req es = satisfied θ₂ p req es := fun p hp => by
    simp only [satisfied, he p hp]
  have herr : ∀ p ∈ ps, hasError θ₁ p req es = hasError θ₂ p req es := fun p hp => by
    simp only [hasError, he p hp]
  have heff : ∀ eff, satisfiedPolicies θ₁ eff ps req es = satisfiedPolicies θ₂ eff ps req es :=
    fun eff => by
      simp only [satisfiedPolicies]
      congr 1
      exact Cedar.List.filterMap_congr fun p hp => by simp only [satisfiedWithEffect, hsat p hp]
  have herrs : errorPolicies θ₁ ps req es = errorPolicies θ₂ ps req es := by
    simp only [errorPolicies]
    congr 1
    exact Cedar.List.filterMap_congr fun p hp => by simp only [errored, herr p hp]
  simp only [isAuthorized, heff, herrs]

/-! ## Scopes admit the request's environment -/

theorem cedar_and_true {a b : Cedar.Spec.Expr} {req : Request} {es : Entities}
    (h : Cedar.Spec.evaluate (.and a b) req es = .ok (.prim (.bool true))) :
    Cedar.Spec.evaluate a req es = .ok (.prim (.bool true)) ∧
      Cedar.Spec.evaluate b req es = .ok (.prim (.bool true)) := by
  simp only [Cedar.Spec.evaluate] at h
  cases ha : (Cedar.Spec.evaluate a req es).as Bool with
  | error e => simp [ha] at h
  | ok b₁ =>
    cases b₁ with
    | false => simp [ha] at h
    | true =>
      cases hb : (Cedar.Spec.evaluate b req es).as Bool with
      | error e => simp [ha, hb] at h
      | ok b₂ =>
        cases b₂ with
        | false => simp [ha, hb] at h
        | true => exact ⟨as_bool_true ha, as_bool_true hb⟩

/-- On an entity store that conforms to the schema, an entity is in another only if the schema
lets its type be in the other's. -/
theorem memberOfType_of_inₑ {A : Schema} {env : TypeEnv} {es : Entities} {u uid : EntityUID}
    (hA : env.ets = A.ets ∧ env.acts = A.acts) (hes : InstanceOfSchema es env)
    (h : Cedar.Spec.inₑ u uid es = true) : Schema.memberOfType A u.ty uid.ty = true := by
  unfold Cedar.Spec.inₑ at h
  unfold Schema.memberOfType
  rcases Bool.or_eq_true_iff.mp h with heq | hanc
  · have : u = uid := by simpa using heq
    subst this
    simp
  · unfold Cedar.Spec.Entities.ancestorsOrEmpty at hanc
    cases hd : es.find? u with
    | none => rw [hd] at hanc; simp [Set.contains, Set.empty] at hanc; cases hanc
    | some d =>
      rw [hd] at hanc
      have hmem : uid ∈ d.ancestors := Set.contains_prop_bool_equiv.mp hanc
      rcases hes.1 u d hd with ⟨entry, hf, _, _, hanc', _⟩ | ⟨_, _, entry, hf, hanc'⟩
      · have hty : uid.ty ∈ entry.ancestors := hanc' uid hmem
        rw [hA.1] at hf
        simp [hf, Set.contains_prop_bool_equiv.mpr hty]
      · rw [hA.2] at hf
        have hacts : A.acts.maybeDescendentOf u.ty uid.ty = true := by
          unfold Cedar.Validation.ActionSchema.maybeDescendentOf
          refine List.any_eq_true.mpr ⟨(u, entry), Map.find?_mem_toList hf, ?_⟩
          simp only [decide_true, Bool.true_and]
          exact Set.any_eq_true.mpr ⟨uid, hanc' ▸ hmem, by simp⟩
        simp [hacts]

/-- A scope constraint that holds of a principal or resource, on an entity store that conforms
to the schema, admits its type. -/
theorem scopeAdmitsType_of_eval {A : Schema} {env : TypeEnv} {s : Cedar.Spec.Scope} {v : Var}
    {u : EntityUID} {req : Request} {es : Entities} (hA : env.ets = A.ets ∧ env.acts = A.acts)
    (hes : InstanceOfSchema es env)
    (hv : Cedar.Spec.evaluate (.var v) req es = .ok (.prim (.entityUID u)))
    (h : Cedar.Spec.evaluate (s.toExpr v) req es = .ok (.prim (.bool true))) :
    scopeAdmitsType A s u.ty = true := by
  cases s with
  | any => rfl
  | mem uid =>
    simp [Cedar.Spec.Scope.toExpr, Cedar.Spec.Var.inEntityUID, Cedar.Spec.evaluate, hv,
      Cedar.Spec.apply₂] at h
    exact memberOfType_of_inₑ hA hes h
  | eq uid =>
    simp [Cedar.Spec.Scope.toExpr, Cedar.Spec.Var.eqEntityUID, Cedar.Spec.evaluate, hv,
      Cedar.Spec.apply₂] at h
    simp [scopeAdmitsType, h]
  | is ety =>
    simp [Cedar.Spec.Scope.toExpr, Cedar.Spec.Var.isEntityType, Cedar.Spec.evaluate, hv,
      Cedar.Spec.apply₁] at h
    simp [scopeAdmitsType, h]
  | isMem ety uid =>
    have h₁ := (cedar_and_true h).1
    simp [Cedar.Spec.Var.isEntityType, Cedar.Spec.evaluate, hv, Cedar.Spec.apply₁] at h₁
    simp [scopeAdmitsType, h₁]

theorem mapM_lit (req : Request) (es : Entities) : ∀ (ls : List EntityUID),
    (ls.map fun e => Cedar.Spec.Expr.lit (.entityUID e)).mapM
        (fun x => Cedar.Spec.evaluate x req es) =
      .ok (ls.map fun u => Value.prim (.entityUID u))
  | [] => rfl
  | u :: ls => by
    simp only [List.map_cons, List.mapM_cons, mapM_lit req es ls]
    simp [Cedar.Spec.evaluate]

theorem evaluate_mem_set (req : Request) (es : Entities) (ls : List EntityUID) :
    Cedar.Spec.evaluate (.binaryApp .mem (.var .action)
        (.set (ls.map fun e => Cedar.Spec.Expr.lit (.entityUID e)))) req es =
      Cedar.Spec.apply₂ .mem (.prim (.entityUID req.action))
        (.set (Set.make (ls.map fun u => Value.prim (.entityUID u)))) es := by
  have hset : Cedar.Spec.evaluate (.set (ls.map fun e => Cedar.Spec.Expr.lit (.entityUID e)))
      req es = .ok (.set (Set.make (ls.map fun u => Value.prim (.entityUID u)))) := by
    rw [Cedar.Spec.evaluate]
    rw [List.mapM₁_eq_mapM (fun x => Cedar.Spec.evaluate x req es), mapM_lit]
    rfl
  rw [Cedar.Spec.evaluate, hset]
  simp [Cedar.Spec.evaluate]

/-- A membership test of an action in a set of action literals holds of one of them. -/
theorem inₛ_lits {act : EntityUID} {ls : List EntityUID} {es : Entities}
    (h : Cedar.Spec.inₛ act (Set.make (ls.map fun u => Value.prim (.entityUID u))) es =
      .ok (.prim (.bool true))) :
    ∃ u ∈ ls, Cedar.Spec.inₑ act u es = true := by
  unfold Cedar.Spec.inₛ Set.mapOrErr at h
  cases hm : (Set.make (ls.map fun u => Value.prim (.entityUID u))).elts.mapM
      Value.asEntityUID with
  | error e => simp [hm] at h
  | ok elts =>
    simp only [hm] at h
    obtain ⟨u', hu', hin⟩ := List.any_eq_true.mp (by simpa [Set.any] using h)
    have hu'' : u' ∈ elts := (Set.mem_make u' elts).mp hu'
    obtain ⟨w, hw, hwu⟩ := List.mapM_ok_implies_all_from_ok hm u' hu''
    have hw' : w ∈ ls.map fun u => Value.prim (.entityUID u) := (Set.mem_make w _).mp hw
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hw'
    simp [Value.asEntityUID] at hwu
    subst hwu
    exact ⟨u, hu, hin⟩

/-- In the decision's store, an action's ancestors are the schema's. -/
theorem descendentOf_of_inₑ {P : PolicySet} {e : Event} {act uid : EntityUID}
    (hdecl : (P.actionSchema.acts.find? act).isSome = true)
    (h : Cedar.Spec.inₑ act uid (P.decisionEntities e) = true) :
    P.actionSchema.acts.descendentOf act uid = true := by
  unfold Cedar.Spec.inₑ at h
  unfold Cedar.Validation.ActionSchema.descendentOf
  obtain ⟨entry, hentry⟩ := Option.isSome_iff_exists.mp hdecl
  have hanc : (P.decisionEntities e).ancestorsOrEmpty act = entry.ancestors := by
    have hf := decisionEntities_find? P e act
    rw [hentry] at hf
    simp only [Option.map_some, Option.some_or] at hf
    simp [Entities.ancestorsOrEmpty, hf, Cedar.Validation.actionSchemaEntryToEntityData]
  by_cases heq : act = uid
  · simp [heq]
  · have hc : ((P.decisionEntities e).ancestorsOrEmpty act).contains uid = true := by
      simpa [heq] using h
    rw [hanc] at hc
    simp [heq, hentry, hc]

/-- An action scope that holds of a declared action admits it. -/
theorem actionScopeAdmits_of_eval {P : PolicySet} {e : Event} {req : Request}
    {s : Cedar.Spec.ActionScope}
    (hdecl : (P.actionSchema.acts.find? req.action).isSome = true)
    (h : Cedar.Spec.evaluate s.toExpr req (P.decisionEntities e) = .ok (.prim (.bool true))) :
    actionScopeAdmits P.actionSchema req.action s = true := by
  have hv : Cedar.Spec.evaluate (.var .action) req (P.decisionEntities e) =
      .ok (.prim (.entityUID req.action)) := by simp [Cedar.Spec.evaluate]
  cases s with
  | actionScope s =>
    cases s with
    | any => rfl
    | eq uid =>
      simp [Cedar.Spec.ActionScope.toExpr, Cedar.Spec.Scope.toExpr, Cedar.Spec.Var.eqEntityUID,
        Cedar.Spec.evaluate, Cedar.Spec.apply₂] at h
      simp [actionScopeAdmits, h]
    | mem uid =>
      simp [Cedar.Spec.ActionScope.toExpr, Cedar.Spec.Scope.toExpr, Cedar.Spec.Var.inEntityUID,
        Cedar.Spec.evaluate, Cedar.Spec.apply₂] at h
      simpa [actionScopeAdmits] using descendentOf_of_inₑ hdecl h
    | is ety =>
      simp [Cedar.Spec.ActionScope.toExpr, Cedar.Spec.Scope.toExpr, Cedar.Spec.Var.isEntityType,
        Cedar.Spec.evaluate, Cedar.Spec.apply₁] at h
      simp [actionScopeAdmits, h]
    | isMem ety uid =>
      have h' := cedar_and_true h
      obtain ⟨h₁, h₂⟩ := h'
      simp [Cedar.Spec.Var.isEntityType, Cedar.Spec.evaluate, Cedar.Spec.apply₁] at h₁
      simp [Cedar.Spec.Var.inEntityUID, Cedar.Spec.evaluate, Cedar.Spec.apply₂] at h₂
      simp [actionScopeAdmits, h₁, descendentOf_of_inₑ hdecl h₂]
  | actionInAny ls =>
    simp only [Cedar.Spec.ActionScope.toExpr] at h
    rw [evaluate_mem_set] at h
    simp only [Cedar.Spec.apply₂] at h
    obtain ⟨u, hu, hin⟩ := inₛ_lits h
    simp only [actionScopeAdmits, List.any_eq_true]
    exact ⟨u, hu, descendentOf_of_inₑ hdecl hin⟩

/-- An action of a request environment is declared. -/
theorem action_declared {A : Schema} {env : TypeEnv} (henv : env ∈ A.environments) :
    (A.acts.find? env.reqty.action).isSome = true := by
  obtain ⟨a, entry, _, _, hmem, _, _, rfl⟩ := mem_environments.mp henv
  unfold Map.find?
  cases hf : A.acts.toList.find? (fun x => x.fst == a) with
  | none =>
    have := List.find?_eq_none.mp hf (a, entry) hmem
    simp at this
  | some p => simp

theorem environments_schema {A : Schema} {env : TypeEnv} (h : env ∈ A.environments) :
    env.ets = A.ets ∧ env.acts = A.acts := by
  obtain ⟨_, _, _, _, _, _, _, rfl⟩ := mem_environments.mp h
  exact ⟨rfl, rfl⟩

/-- **A rule whose scope holds at the request admits the request's environment**, on an entity
store that conforms to the schema. -/
theorem admits_of_scopeHolds {P : PolicySet} {e : Event} {pr rs : EntityUID} {env : TypeEnv}
    (henv : env ∈ P.actionSchema.environments)
    (hreq : InstanceOfRequestType (e.request pr rs) env)
    (hes : InstanceOfSchema (P.decisionEntities e) env) {q : Policy}
    (h : q.ScopeHolds (e.request pr rs) (P.decisionEntities e)) : env ∈ P.envsOf q := by
  unfold PolicySet.envsOf
  refine List.mem_filter.mpr ⟨henv, ?_⟩
  obtain ⟨hp, ha, hr⟩ := h
  have hpr : env.reqty.principal = pr.ty := hreq.1.1
  have hact : env.reqty.action = e.action := hreq.2.1.symm
  have hrs : env.reqty.resource = rs.ty := hreq.2.2.1.1
  cases hps : q.principalScope with
  | principalScope ps =>
    cases hrsc : q.resourceScope with
    | resourceScope rsc =>
      simp only [Policy.admits, hps, hrsc, Bool.and_eq_true]
      rw [hps] at hp
      rw [hrsc] at hr
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [hpr]
        exact scopeAdmitsType_of_eval (environments_schema henv) hes
          (by simp [Cedar.Spec.evaluate, Event.request]) hp
      · have hdecl := action_declared henv
        rw [hact] at hdecl ⊢
        exact actionScopeAdmits_of_eval (req := e.request pr rs) hdecl ha
      · rw [hrs]
        exact scopeAdmitsType_of_eval (environments_schema henv) hes
          (by simp [Cedar.Spec.evaluate, Event.request]) hr

/-! ## The decision event is an instance of its request's environment -/

/-- The decision's checks make its store an instance of every environment of the schema. -/
theorem instanceOfSchema_of_admits {P : PolicySet} {rules : Policies} {ω : Provider.Providers}
    {p : TimePoint} {pr rs : EntityUID} (ha : P.Admits rules ω p pr rs) {env : TypeEnv}
    (henv : env ∈ P.actionSchema.environments) :
    InstanceOfSchema (P.decisionEntities p.event) env := by
  have := ha.entities
  unfold succeeds at this
  split at this
  · rename_i hok
    have := List.forM_ok_implies_all_ok _ _ hok env henv
    unfold Cedar.Validation.entitiesMatchEnvironment at this
    exact Cedar.Thm.instance_of_schema_refl this
  · cases this

/-- **An admitted decision event is an instance of its request's environment.** -/
theorem instanceOf_of_admits {P : PolicySet} {rules : Policies} {ω : Provider.Providers}
    {p : TimePoint} {pr rs : EntityUID} (ha : P.Admits rules ω p pr rs) {env : TypeEnv}
    (hreq : InstanceOfRequestType (p.event.request pr rs) env) :
    p.event.InstanceOf env :=
  instanceOf_of_request ha.principal ha.resource hreq

/-- **An admitted decision event supplies the scope entities the rules that apply to it read.**
At a decision every check of which passes, a temporal leaf of a rule whose scope holds at the
request reads the attributes only of scope entities the event supplies. -/
theorem supplied_of_admits {P : PolicySet} {rules : Policies} {ω : Provider.Providers}
    {p : TimePoint} {pr rs : EntityUID} (ha : P.Admits rules ω p pr rs) {q : Policy}
    (hq : q ∈ rules) (hs : q.ScopeHolds (p.event.request pr rs) (P.decisionEntities p.event))
    {φ : Formula} (hφ : Sum.inl φ ∈ q.toExpr.leaves) :
    ∀ r ∈ (φ.injectPins P.schema).scopeReads, p.event.supplies r = true := by
  have h := List.all_eq_true.mp ha.scopes q hq
  rw [← scopeHolds_iff] at hs
  simp only [hs, Bool.not_true, Bool.false_or] at h
  have := List.all_eq_true.mp h (.inl φ) hφ
  exact List.all_eq_true.mp this

/-- **A supplied scope entity conforms.** At a decision every check of which passes, a scope entity
the event supplies has attributes of the types its entity type declares, in every environment of
the action schema: the store conforms, and it holds the supplied data for the entity, because an
entity type with attributes is not an action type (`validateWellFormed`). -/
theorem supplies_of_admits {P : PolicySet} (hv : P.Valid) {rules : Policies}
    {ω : Provider.Providers} {p : TimePoint} {pr rs : EntityUID} (ha : P.Admits rules ω p pr rs)
    {env : TypeEnv} (henv : env ∈ P.actionSchema.environments) {r : ScopeRoot}
    (hsup : p.event.supplies r = true) : p.event.Supplies env r := by
  intro uid huid rty hrty
  have hwf := augmented_wf hv henv
  have hes := instanceOfSchema_of_admits ha henv
  have hA := environments_schema henv
  -- The entity type has attributes, so it is declared, and the scope entity is not an action.
  have hets : env.ets.contains uid.ty = true := by
    simp only [Cedar.Validation.EntitySchema.attrs?, Option.map_eq_some_iff] at hrty
    obtain ⟨entry, hentry, _⟩ := hrty
    simp [Cedar.Validation.EntitySchema.contains, hentry]
  obtain ⟨d, hd⟩ : ∃ d, p.event.entities.find? uid = some d := by
    unfold Event.supplies at hsup
    rw [huid] at hsup
    exact Option.isSome_iff_exists.mp hsup
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
  have hfind : (P.decisionEntities p.event).find? uid = some d := by
    rw [decisionEntities_find?, hnact, hd]
    rfl
  refine ⟨d, hd, ?_⟩
  rcases hes.1 uid d hfind with ⟨entry, hentry, _, hattrs, _, _⟩ | ⟨_, _, entry, hentry, _⟩
  · simp only [Cedar.Validation.EntitySchema.attrs?, hentry, Option.map_some,
      Option.some.injEq] at hrty
    subst hrty
    exact hattrs
  · exfalso
    rw [hA.2, hnact] at hentry
    cases hentry

/-! ## Soundness at the request -/

/-- **Soundness at the request.** For a valid policy set, at a decision every check of which
passes, over a trace whose events conform, under a total reading: the request is an instance of
an environment of the action schema, and every temporal leaf of every rule whose scope holds at
the request, at a position whose facts hold at the request, is sound in that environment — every
comparison its satisfaction reaches is two-valued, and every witness and row it uses is typed.
By `isAuthorized_congr_scope`, these are the leaves the response depends on. -/
theorem decision_sound {P : PolicySet} (hv : P.Valid) {ι : ImplChoices} (hι : ι.Total)
    {ω : Provider.Providers} {σ : Trace} {n : Nat} {p : TimePoint} {pr rs : EntityUID}
    (ha : P.Admits P.policies ω p pr rs)
    (htr : ∀ (k : Nat) (q : TimePoint), σ[k]? = some q →
      q.event.Conforms P.actionSchema P.schema) :
    ∃ env ∈ P.actionSchema.environments,
      InstanceOfRequestType (p.event.request pr rs) env ∧ p.event.InstanceOf env ∧
      ∀ q ∈ P.policies, q.ScopeHolds (p.event.request pr rs) (P.decisionEntities p.event) →
        ∀ φ F, (.inl φ, F) ∈ q.toExpr.leafFacts [] →
        (∀ g ∈ F, g.HoldsIn (p.event.request pr rs) (P.decisionEntities p.event)) →
        env ∈ P.envsOf q ∧ ∀ vis,
          (φ.injectPins P.schema).Sound ι P.tickRate σ p.event vis (P.typingCtx env F) [] Valuation.empty n := by
  obtain ⟨env, henv, hreq⟩ := request_instance ha.request
  have hinst := instanceOf_of_admits ha hreq
  refine ⟨env, henv, hreq, hinst, fun q hq hs φ F hφ hF => ?_⟩
  have henvq := admits_of_scopeHolds henv hreq (instanceOfSchema_of_admits ha henv) hs
  have hleaf : Sum.inl φ ∈ q.toExpr.leaves := by
    rw [← leafFacts_fst [] q.toExpr]
    exact List.mem_map.mpr ⟨_, hφ, rfl⟩
  have hsup : ∀ r ∈ (φ.injectPins P.schema).scopeReads, p.event.Supplies env r :=
    fun r hr => supplies_of_admits hv ha henv (supplied_of_admits ha hq hs hleaf r hr)
  exact ⟨henvq, fun vis => leaves_sound hv hι htr n hq hφ henvq hinst hsup
    (fun g hg => holds_of_holdsIn ha.principal ha.resource (hF g hg)) vis⟩

/-- **No allow is caused by an unresolved or ill-typed value.** An allowed decision of a valid
policy set, over a trace whose events conform, is the allow of every completion of the reading,
at a decision every check of which passes. Under each completion, which is total, every rule
evaluates to a `Bool` or a runtime error, and every temporal leaf the response depends on is
sound: no comparison it reaches has an operand that does not resolve. -/
theorem allow_sound_leaves {P : PolicySet} (hv : P.Valid) {ι : ImplChoices}
    {ω : Provider.Providers} {σ : Trace} {n : Nat}
    (h : (P.authorize ι ω σ n).decision? = some .allow)
    (htr : ∀ (k : Nat) (q : TimePoint), σ[k]? = some q →
      q.event.Conforms P.actionSchema P.schema) :
    ∃ p pr rs, σ[n]? = some p ∧ P.Admits P.policies ω p pr rs ∧ ∀ ι', ι'.Completes ι →
      (isAuthorized (P.leaves ι' ω σ n p.event) (p.event.request pr rs)
          (P.decisionEntities p.event) P.policies).decision = .allow ∧
      (∀ q ∈ P.policies, EvaluatesToBool (P.leaves ι' ω σ n p.event) q.toExpr
        (p.event.request pr rs) (P.decisionEntities p.event)) ∧
      ∃ env ∈ P.actionSchema.environments,
        ∀ q ∈ P.policies, q.ScopeHolds (p.event.request pr rs) (P.decisionEntities p.event) →
          ∀ φ F, (.inl φ, F) ∈ q.toExpr.leafFacts [] →
          (∀ g ∈ F, g.HoldsIn (p.event.request pr rs) (P.decisionEntities p.event)) →
          env ∈ P.envsOf q ∧ ∀ vis, (φ.injectPins P.schema).Sound ι' P.tickRate σ p.event vis
            (P.typingCtx env F) [] Valuation.empty n := by
  obtain ⟨p, pr, rs, hσ, ha, hall⟩ := allow_sound hv h
  refine ⟨p, pr, rs, hσ, ha, fun ι' hc => ⟨(hall ι' hc).1, (hall ι' hc).2, ?_⟩⟩
  obtain ⟨env, henv, _, _, hs⟩ := decision_sound hv hc.total ha htr
  exact ⟨env, henv, hs⟩

end Dogwood.Thm
