import Dogwood.Frontend.Resolve
import Dogwood.Thm.Frontend.Derive.Events
import Cedar.Thm.Data.Map
import Cedar.Thm.Data.Set

/-!
# Cedar's schema resolution: what the resolved schema names

* **No common-type reference is left unresolved.** cedar-lean's `CedarType` has no reference
  constructor, so a resolved schema has none by construction. What resolution does with a
  reference is inline it: the resolved type of a reference to a common type is the resolved type
  of its definition, in its own namespace (`convert_commonRef`), and once it resolves, a larger
  bound on reference chains gives the same type (`convert_fuel_mono`). A schema resolves only if
  every common type does, used or not (`resolve_commons`), as Cedar requires.
* **Every entity type the resolved schema names is declared** (`resolve_namesDeclared`): every
  entity type an attribute, a tag or a context names is a declared entity type or the type of a
  declared action; every `appliesTo` entity type and every ancestor of an entity type is a
  declared entity type; and every ancestor of an action is a declared action.
-/

namespace Dogwood.Thm.Frontend.Derivation

open Dogwood.Frontend Dogwood.Frontend.CedarSchema Dogwood.Frontend.CedarSchema.Resolve
open Cedar.Spec (Name EntityType EntityUID Attr)
open Cedar.Validation (CedarType QualifiedType RecordType Qualified Schema EntitySchemaEntry
  ActionSchemaEntry)
open Cedar.Data (Map Set)

/-! ## What a type names -/

/-- The entity types a Cedar type names. -/
inductive Mentions : CedarType → EntityType → Prop
  | entity (e : EntityType) : Mentions (.entity e) e
  | set {t : CedarType} {e : EntityType} : Mentions t e → Mentions (.set t) e
  | record {r : RecordType} {a : Attr} {q : QualifiedType} {e : EntityType} :
      (a, q) ∈ r.toList → Mentions q.getType e → Mentions (.record r) e

/-- An entity type the schema declares, or the type of one of its actions: what Cedar accepts
in an attribute type. -/
def KnownType (S : Schema) (e : EntityType) : Prop :=
  S.ets.contains e = true ∨ S.acts.actionType? e = true

/-- **Every entity type the schema names is declared.** -/
structure NamesDeclared (S : Schema) : Prop where
  ancestors : ∀ ety entry, (ety, entry) ∈ S.ets.toList → ∀ a ∈ entry.ancestors,
    S.ets.contains a = true
  attrs : ∀ ety entry, (ety, entry) ∈ S.ets.toList → ∀ e, Mentions (.record entry.attrs) e →
    KnownType S e
  tags : ∀ ety entry t, (ety, entry) ∈ S.ets.toList → entry.tags? = some t → ∀ e, Mentions t e →
    KnownType S e
  appliesTo : ∀ uid entry, (uid, entry) ∈ S.acts.toList → ∀ p,
    (p ∈ entry.appliesToPrincipal ∨ p ∈ entry.appliesToResource) → S.ets.contains p = true
  actionAncestors : ∀ uid entry, (uid, entry) ∈ S.acts.toList → ∀ a ∈ entry.ancestors,
    S.acts.contains a = true
  context : ∀ uid entry, (uid, entry) ∈ S.acts.toList → ∀ e, Mentions (.record entry.context) e →
    KnownType S e

/-! ## Resolved types -/

theorem qualified_getType (req : Bool) (t : CedarType) : (qualified req t).getType = t := by
  cases req <;> rfl

theorem resolveEntity_mem {D : Defs} {ns : Option Name} {n : String} {e : EntityType}
    (h : D.resolveEntity ns n = some e) : e ∈ D.entities := by
  unfold Defs.resolveEntity at h
  exact List.contains_iff_mem.mp (List.find?_some h)

theorem resolveRef_inr_mem {D : Defs} {ns : Option Name} {n : String} {e : EntityType}
    (h : D.resolveRef ns n = some (.inr e)) : e ∈ D.entities := by
  unfold Defs.resolveRef at h
  obtain ⟨p, -, hp⟩ := List.exists_of_findSome?_eq_some h
  split at hp
  · simp at hp
  · split at hp
    · rename_i hc
      simp only [Option.some.injEq, Sum.inr.injEq] at hp
      subst hp
      exact List.contains_iff_mem.mp hc
    · simp at hp

mutual

/-- The entity types a resolved type names are entity types for name resolution, given that
those of the inlined common types are. -/
theorem convertT_mentions (D : Defs) (inl : Name → Except String CedarType)
    (hinl : ∀ c r, inl c = .ok r → ∀ e, Mentions r e → e ∈ D.entities) (ns : Option Name) :
    ∀ (t : SchemaType) (r : CedarType), convertT D inl ns t = .ok r →
      ∀ e, Mentions r e → e ∈ D.entities
  | .string, r, h, e, hm => by
    simp [convertT, pure, Except.pure] at h; subst h; cases hm
  | .long, r, h, e, hm => by
    simp [convertT, pure, Except.pure] at h; subst h; cases hm
  | .boolean, r, h, e, hm => by
    simp [convertT, pure, Except.pure] at h; subst h; cases hm
  | .set t, r, h, e, hm => by
    simp only [convertT, bind, Except.bind] at h
    cases ht : convertT D inl ns t with
    | error _ => simp [ht] at h
    | ok r' =>
      simp [ht, pure, Except.pure] at h
      subst h
      cases hm with
      | set hm' => exact convertT_mentions D inl hinl ns t r' ht e hm'
  | .record attrs add, r, h, e, hm => by
    simp only [convertT] at h
    split at h
    · simp at h
    · simp only [bind, Except.bind] at h
      cases ha : convertAttrsT D inl ns attrs with
      | error _ => simp [ha] at h
      | ok l =>
        simp [ha, pure, Except.pure] at h
        subst h
        cases hm with
        | record hmem hm' =>
          exact convertAttrsT_mentions D inl hinl ns attrs l ha _ (Map.mem_make_mem_list hmem) e hm'
  | .entity n, r, h, e, hm => by
    simp only [convertT] at h
    split at h
    · rename_i e' he'
      simp [pure, Except.pure] at h
      subst h
      cases hm
      exact resolveEntity_mem he'
    · simp at h
  | .entityOrCommon n, r, h, e, hm => by
    simp only [convertT] at h
    split at h
    · exact hinl _ _ h e hm
    · rename_i e' he'
      simp [pure, Except.pure] at h
      subst h
      cases hm
      exact resolveRef_inr_mem he'
    · simp at h
  | .commonRef n, r, h, e, hm => by
    simp only [convertT] at h
    split at h
    · exact hinl _ _ h e hm
    · simp at h
  | .extension n, r, h, e, hm => by
    simp only [convertT] at h
    split at h
    · simp [pure, Except.pure] at h; subst h; cases hm
    · simp at h

theorem convertAttrsT_mentions (D : Defs) (inl : Name → Except String CedarType)
    (hinl : ∀ c r, inl c = .ok r → ∀ e, Mentions r e → e ∈ D.entities) (ns : Option Name) :
    ∀ (attrs : List (String × AttrType)) (l : List (String × QualifiedType)),
      convertAttrsT D inl ns attrs = .ok l → ∀ aq ∈ l, ∀ e, Mentions aq.2.getType e →
        e ∈ D.entities
  | [], l, h, aq, haq, _, _ => by
    simp [convertAttrsT, pure, Except.pure] at h; subst h; simp at haq
  | (k, ⟨ty, req, anns⟩) :: rest, l, h, aq, haq, e, hm => by
    simp only [convertAttrsT, bind, Except.bind] at h
    cases ht : convertT D inl ns ty with
    | error _ => simp [ht] at h
    | ok r =>
      cases hr : convertAttrsT D inl ns rest with
      | error _ => simp [ht, hr] at h
      | ok l' =>
        simp [ht, hr, pure, Except.pure] at h
        subst h
        rcases List.mem_cons.mp haq with rfl | haq
        · rw [qualified_getType] at hm
          exact convertT_mentions D inl hinl ns ty r ht e hm
        · exact convertAttrsT_mentions D inl hinl ns rest l' hr aq haq e hm

end

/-- The entity types a resolved type names are entity types for name resolution. -/
theorem convert_mentions (D : Defs) : ∀ (fuel : Nat) (ns : Option Name) (t : SchemaType)
    (r : CedarType), convert D fuel ns t = .ok r → ∀ e, Mentions r e → e ∈ D.entities
  | 0, ns, t, r, h => convertT_mentions D _ (fun _ _ h => by simp [throw, throwThe,
      MonadExceptOf.throw] at h) ns t r h
  | fuel + 1, ns, t, r, h => convertT_mentions D _ (fun c r' h' => by
      split at h'
      · exact convert_mentions D fuel _ _ _ h'
      · simp at h') ns t r h

/-! ## Inlining -/

mutual

theorem convertT_mono (D : Defs) {inl inl' : Name → Except String CedarType}
    (hinl : ∀ c r, inl c = .ok r → inl' c = .ok r) (ns : Option Name) :
    ∀ (t : SchemaType) (r : CedarType), convertT D inl ns t = .ok r → convertT D inl' ns t = .ok r
  | .string, _, h | .long, _, h | .boolean, _, h | .entity _, _, h | .extension _, _, h => by
    simpa [convertT] using h
  | .set t, r, h => by
    simp only [convertT, bind, Except.bind] at h ⊢
    cases ht : convertT D inl ns t with
    | error _ => simp [ht] at h
    | ok r' => simp [ht] at h; simp [convertT_mono D hinl ns t r' ht, h]
  | .record attrs add, r, h => by
    simp only [convertT] at h ⊢
    split at h
    · simp at h
    · rename_i hadd
      simp only [hadd, bind, Except.bind] at h ⊢
      cases ha : convertAttrsT D inl ns attrs with
      | error _ => simp [ha] at h
      | ok l => simp [ha] at h; simp [convertAttrsT_mono D hinl ns attrs l ha, h]
  | .entityOrCommon n, r, h => by
    simp only [convertT] at h ⊢
    split at h
    · simp [hinl _ _ h]
    · rename_i e' he'
      simpa [he'] using h
    · simp at h
  | .commonRef n, r, h => by
    simp only [convertT] at h ⊢
    split at h
    · simp [hinl _ _ h]
    · simp at h

theorem convertAttrsT_mono (D : Defs) {inl inl' : Name → Except String CedarType}
    (hinl : ∀ c r, inl c = .ok r → inl' c = .ok r) (ns : Option Name) :
    ∀ (attrs : List (String × AttrType)) (l : List (String × QualifiedType)),
      convertAttrsT D inl ns attrs = .ok l → convertAttrsT D inl' ns attrs = .ok l
  | [], l, h => by simpa [convertAttrsT] using h
  | (k, ⟨ty, req, anns⟩) :: rest, l, h => by
    simp only [convertAttrsT, bind, Except.bind] at h ⊢
    cases ht : convertT D inl ns ty with
    | error _ => simp [ht] at h
    | ok r =>
      cases hr : convertAttrsT D inl ns rest with
      | error _ => simp [ht, hr] at h
      | ok l' =>
        simp [ht, hr] at h
        simp [convertT_mono D hinl ns ty r ht, convertAttrsT_mono D hinl ns rest l' hr, h]

end

/-- **The result of inlining does not depend on the bound** on reference chains: more fuel gives
the same type. -/
theorem convert_fuel_mono (D : Defs) : ∀ (fuel : Nat) (ns : Option Name) (t : SchemaType)
    (r : CedarType), convert D fuel ns t = .ok r → convert D (fuel + 1) ns t = .ok r
  | 0, ns, t, r, h => convertT_mono D (fun _ _ h => by simp [throw, throwThe,
      MonadExceptOf.throw] at h) ns t r h
  | fuel + 1, ns, t, r, h => convertT_mono D (fun c r' h' => by
      split at h'
      · exact convert_fuel_mono D fuel _ _ _ h'
      · simp at h') ns t r h

/-- **A reference to a common type resolves to its definition**, resolved in the namespace that
declares it. -/
theorem convert_commonRef {D : Defs} {fuel : Nat} {ns : Option Name} {n : String} {c : Name}
    {d : CommonDef} (hc : D.resolveCommon ns n = some c)
    (hd : D.commons.find? (·.name == c) = some d) :
    convert D (fuel + 1) ns (.commonRef n) = convert D fuel d.ns d.ty := by
  simp [convert, convertT, hc, hd]

/-- The same for a reference that may name an entity type, when it names a common type. -/
theorem convert_entityOrCommon {D : Defs} {fuel : Nat} {ns : Option Name} {n : String} {c : Name}
    {d : CommonDef} (hc : D.resolveRef ns n = some (.inl c))
    (hd : D.commons.find? (·.name == c) = some d) :
    convert D (fuel + 1) ns (.entityOrCommon n) = convert D fuel d.ns d.ty := by
  simp [convert, convertT, hc, hd]

/-! ## The resolved schema -/

theorem resolveExcept_ok {f : Fragment} {S : Schema} (h : resolveExcept f = .ok S) :
    checkCommons (Defs.ofFragment f) = .ok () ∧
    ∃ ets acts, resolveEntityTypes (Defs.ofFragment f) f = .ok ets ∧
      resolveActions (Defs.ofFragment f) f = .ok acts ∧
      S = { ets := entitySchema ets, acts := actionSchema acts } := by
  unfold resolveExcept at h
  simp only [bind, Except.bind] at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · split at h
      · simp at h
      · split at h
        · simp at h
        · rename_i hcc
          split at h
          · simp at h
          · rename_i ets hets
            split at h
            · simp at h
            · rename_i acts hacts
              split at h
              · simp at h
              · split at h
                · simp at h
                · simp only [pure, Except.pure, Except.ok.injEq] at h
                  rename_i u hu
                  cases u
                  exact ⟨hcc, ets, acts, hets, hacts, h.symm⟩

/-- **A schema resolves only if every common type does**, used or not. -/
theorem resolve_commons {f : Fragment} {S : Schema} (h : resolve f = .ok S) :
    ∀ d ∈ (Defs.ofFragment f).commons,
      ∃ r, convert (Defs.ofFragment f) (Defs.ofFragment f).fuel d.ns d.ty = .ok r := by
  have hr : resolveExcept f = .ok S := by
    unfold resolve at h
    cases h' : resolveExcept f <;> simp_all [Except.mapError]
  have hcc := (resolveExcept_ok hr).1
  intro d hd
  have := List.forM_ok_implies_all_ok _ _ hcc d hd
  simp only [bind, Except.bind] at this
  split at this
  · simp at this
  · rename_i r hr'
    exact ⟨r, hr'⟩

/-! ## Declarations and their resolution -/

theorem mem_userEntities {f : Fragment} {x : EntityType} :
    x ∈ userEntities f ↔ ∃ ns d, (ns, d) ∈ f ∧ ∃ id e, (id, e) ∈ d.entityTypes ∧
      x = qualifyWith (nsName ns) ⟨id, []⟩ := by
  simp only [userEntities, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨⟨ns, d⟩, hns, ⟨id, e⟩, he, rfl⟩
    exact ⟨ns, d, hns, id, e, he, rfl⟩
  · rintro ⟨ns, d, hns, id, e, he, rfl⟩
    exact ⟨⟨ns, d⟩, hns, ⟨id, e⟩, he, rfl⟩

theorem mem_userActions {f : Fragment} {u : EntityUID} :
    u ∈ userActions f ↔ ∃ ns d, (ns, d) ∈ f ∧ ∃ id a, (id, a) ∈ d.actions ∧
      u = ⟨actionType (nsName ns), id⟩ := by
  simp only [userActions, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨⟨ns, d⟩, hns, ⟨id, a⟩, ha, rfl⟩
    exact ⟨ns, d, hns, id, a, ha, rfl⟩
  · rintro ⟨ns, d, hns, id, a, ha, rfl⟩
    exact ⟨⟨ns, d⟩, hns, ⟨id, a⟩, ha, rfl⟩

/-- An entity type for name resolution is declared, or the `Action` type of a namespace with an
action. -/
theorem mem_entities {f : Fragment} {e : EntityType} (h : e ∈ (Defs.ofFragment f).entities) :
    e ∈ userEntities f ∨ ∃ u ∈ userActions f, u.ty = e := by
  simp only [Defs.ofFragment, List.mem_append, List.mem_map, List.mem_filter] at h
  rcases h with h | ⟨⟨ns, d⟩, ⟨hns, hne⟩, rfl⟩
  · exact .inl h
  · right
    simp only [Bool.not_eq_true', List.isEmpty_eq_false_iff] at hne
    obtain ⟨⟨id, a⟩, ha⟩ := List.exists_mem_of_ne_nil _ hne
    exact ⟨⟨actionType (nsName ns), id⟩, mem_userActions.mpr ⟨ns, d, hns, id, a, ha, rfl⟩, rfl⟩

theorem resolveEntityTypes_mem {D : Defs} {f : Fragment} {ets : List EntityEntry}
    (h : resolveEntityTypes D f = .ok ets) {ee : EntityEntry} (he : ee ∈ ets) :
    ∃ ns d, (ns, d) ∈ f ∧ ∃ id e, (id, e) ∈ d.entityTypes ∧
      resolveEntityType D (nsName ns) id e = .ok ee := by
  unfold resolveEntityTypes at h
  obtain ⟨⟨ns, d⟩, hns, zs, hzs, hez⟩ := flatMapM_ok_mem h he
  obtain ⟨⟨id, e⟩, hid, hone⟩ := mapM_ok_mem hzs hez
  exact ⟨ns, d, hns, id, e, hid, hone⟩

theorem resolveEntityTypes_complete {D : Defs} {f : Fragment} {ets : List EntityEntry}
    (h : resolveEntityTypes D f = .ok ets) {ns : Option String} {d : NamespaceDef}
    (hns : (ns, d) ∈ f) {id : String} {e : EntityTypeDef} (he : (id, e) ∈ d.entityTypes) :
    ∃ ee ∈ ets, resolveEntityType D (nsName ns) id e = .ok ee := by
  unfold resolveEntityTypes at h
  obtain ⟨zs, hzs, hsub⟩ := flatMapM_ok_complete h hns
  obtain ⟨ee, hee, hone⟩ := mapM_ok_complete hzs he
  exact ⟨ee, hsub _ hee, hone⟩

theorem resolveActions_mem {D : Defs} {f : Fragment} {acts : List ActionEntry}
    (h : resolveActions D f = .ok acts) {ae : ActionEntry} (ha : ae ∈ acts) :
    ∃ ns d, (ns, d) ∈ f ∧ ∃ id a, (id, a) ∈ d.actions ∧
      resolveAction D (nsName ns) id a = .ok ae := by
  unfold resolveActions at h
  obtain ⟨⟨ns, d⟩, hns, zs, hzs, hez⟩ := flatMapM_ok_mem h ha
  obtain ⟨⟨id, a⟩, hid, hone⟩ := mapM_ok_mem hzs hez
  exact ⟨ns, d, hns, id, a, hid, hone⟩

theorem resolveActions_complete {D : Defs} {f : Fragment} {acts : List ActionEntry}
    (h : resolveActions D f = .ok acts) {ns : Option String} {d : NamespaceDef}
    (hns : (ns, d) ∈ f) {id : String} {a : ActionDef} (ha : (id, a) ∈ d.actions) :
    ∃ ae ∈ acts, resolveAction D (nsName ns) id a = .ok ae := by
  unfold resolveActions at h
  obtain ⟨zs, hzs, hsub⟩ := flatMapM_ok_complete h hns
  obtain ⟨ae, hae, hone⟩ := mapM_ok_complete hzs ha
  exact ⟨ae, hsub _ hae, hone⟩

theorem convertRecord_mentions {D : Defs} {ns : Option Name} {what : String} {ty : SchemaType}
    {r : RecordType} (h : convertRecord D ns what ty = .ok r) :
    ∀ e, Mentions (.record r) e → e ∈ D.entities := by
  unfold convertRecord at h
  simp only [bind, Except.bind] at h
  split at h
  · simp at h
  · rename_i t ht
    split at h
    · simp [pure, Except.pure] at h
      subst h
      exact convert_mentions D _ _ _ _ ht
    · simp at h

/-- A resolved entity type: its name, declared parents, and the entity types its shape and tags
name. -/
theorem resolveEntityType_ok {D : Defs} {ns : Option Name} {id : String} {d : EntityTypeDef}
    {ee : EntityEntry} (h : resolveEntityType D ns id d = .ok ee) :
    ee.name = qualifyWith ns ⟨id, []⟩ ∧ (∀ p ∈ ee.parents, p ∈ D.declared) ∧
      ∀ attrs tags, ee.kind = some (attrs, tags) →
        (∀ e, Mentions (.record attrs) e → e ∈ D.entities) ∧
        (∀ t, tags = some t → ∀ e, Mentions t e → e ∈ D.entities) := by
  unfold resolveEntityType at h
  split at h
  · simp only [bind, Except.bind, check] at h
    split at h
    · simp at h
    · simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      simp
  · rename_i memberOf shape tags hkind
    simp only [bind, Except.bind] at h
    split at h
    · simp at h
    · rename_i parents hparents
      split at h
      · simp at h
      · rename_i attrs hattrs
        split at h
        · simp at h
        · rename_i tags' htags
          simp only [pure, Except.pure, Except.ok.injEq] at h
          subst h
          refine ⟨rfl, ?_, ?_⟩
          · intro p hp
            obtain ⟨q, -, hq⟩ := mapM_ok_mem hparents hp
            split at hq
            · split at hq
              · simp [pure, Except.pure] at hq
                subst hq
                rename_i hc
                exact List.contains_iff_mem.mp hc
              · simp at hq
            · simp at hq
          · intro attrs' tags'' hk
            simp only [Option.some.injEq, Prod.mk.injEq] at hk
            obtain ⟨rfl, rfl⟩ := hk
            refine ⟨convertRecord_mentions hattrs, ?_⟩
            intro t ht e hm
            subst ht
            cases tags with
            | none => simp [pure, Except.pure] at htags
            | some t₀ =>
              simp only [Option.mapM_some] at htags
              cases hc : convert D D.fuel ns t₀ with
              | error _ => simp [hc, Functor.map, Except.map] at htags
              | ok t' =>
                simp [hc, Functor.map, Except.map] at htags
                subst htags
                exact convert_mentions D _ _ _ _ hc e hm

theorem resolveApplies_mem {D : Defs} {ns : Option Name} {raw : String} {e : EntityType}
    (h : resolveApplies D ns raw = .ok e) : e ∈ D.declared := by
  unfold resolveApplies at h
  split at h
  · split at h
    · simp [pure, Except.pure] at h
      subst h
      rename_i hc
      exact List.contains_iff_mem.mp hc
    · simp at h
  · simp at h

theorem resolveAction_mem {D : Defs} {ns : Option Name} {m : ActionUid} {u : EntityUID}
    (h : D.resolveAction ns m = some u) : u ∈ D.actions := by
  unfold Defs.resolveAction at h
  have := List.find?_some h
  simp only [Bool.and_eq_true] at this
  exact List.contains_iff_mem.mp this.2

/-- A resolved action: its uid, declared parents, declared `appliesTo` types, and the entity types
its context names. -/
theorem resolveAction_ok {D : Defs} {ns : Option Name} {id : String} {a : ActionDef}
    {ae : ActionEntry} (h : resolveAction D ns id a = .ok ae) :
    ae.uid = ⟨actionType ns, id⟩ ∧ (∀ p ∈ ae.parents, p ∈ D.actions) ∧
      (∀ p, p ∈ ae.principals ∨ p ∈ ae.resources → p ∈ D.declared) ∧
      (∀ e, Mentions (.record ae.context) e → e ∈ D.entities) := by
  unfold resolveAction at h
  simp only [bind, Except.bind] at h
  split at h
  · simp at h
  · rename_i parents hparents
    have hpar : ∀ p ∈ parents, p ∈ D.actions := by
      intro p hp
      obtain ⟨m, -, hm⟩ := mapM_ok_mem hparents hp
      split at hm
      · simp [pure, Except.pure] at hm
        subst hm
        rename_i hu
        exact resolveAction_mem hu
      · simp at hm
    split at h
    · simp [pure, Except.pure] at h
      subst h
      refine ⟨rfl, hpar, by simp, ?_⟩
      intro e hm
      cases hm with
      | record hmem _ => simp [Map.empty, Map.toList] at hmem
    · rename_i ap _
      split at h
      · simp at h
      · rename_i ps hps
        split at h
        · simp at h
        · rename_i rs hrs
          split at h
          · simp at h
          · rename_i ctx hctx
            simp only [pure, Except.pure, Except.ok.injEq] at h
            subst h
            refine ⟨rfl, hpar, ?_, convertRecord_mentions hctx⟩
            rintro p (hp | hp)
            · obtain ⟨raw, -, hr⟩ := mapM_ok_mem hps hp
              exact resolveApplies_mem hr
            · obtain ⟨raw, -, hr⟩ := mapM_ok_mem hrs hp
              exact resolveApplies_mem hr

/-! ## Hierarchies -/

theorem closure_subset {α : Type} [DecidableEq α] {parents : α → List α} {P : α → Prop}
    (hp : ∀ x, ∀ y ∈ parents x, P y) :
    ∀ (fuel : Nat) (start : List α), (∀ y ∈ start, P y) → ∀ y ∈ closure parents fuel start, P y
  | 0, start, hs => by simpa [closure] using hs
  | fuel + 1, start, hs => by
    simp only [closure]
    split
    · exact hs
    · apply closure_subset hp fuel
      intro y hy
      rw [List.mem_eraseDups, List.mem_append] at hy
      rcases hy with hy | hy
      · exact hs y hy
      · obtain ⟨x, -, hx⟩ := List.mem_flatMap.mp hy
        exact hp x y hx

theorem ancestorsOf_subset {α : Type} [DecidableEq α] {parents : α → List α} {P : α → Prop}
    (hp : ∀ x, ∀ y ∈ parents x, P y) (n : Nat) (x : α) : ∀ y ∈ ancestorsOf parents n x, P y :=
  closure_subset hp (n + 1) _ (fun y hy => hp x y (List.mem_eraseDups.mp hy))

theorem entityParents_mem {ets : List EntityEntry} {n p : EntityType}
    (h : p ∈ entityParents ets n) : ∃ ee ∈ ets, p ∈ ee.parents := by
  unfold entityParents at h
  cases hf : ets.find? (·.name == n) with
  | none => simp [hf] at h
  | some ee =>
    simp only [hf, Option.map_some, Option.getD_some] at h
    exact ⟨ee, List.mem_of_find?_eq_some hf, h⟩

theorem actionParents_mem {acts : List ActionEntry} {u p : EntityUID}
    (h : p ∈ actionParents acts u) : ∃ ae ∈ acts, p ∈ ae.parents := by
  unfold actionParents at h
  cases hf : acts.find? (·.uid == u) with
  | none => simp [hf] at h
  | some ae =>
    simp only [hf, Option.map_some, Option.getD_some] at h
    exact ⟨ae, List.mem_of_find?_eq_some hf, h⟩

/-! ## The schema's maps -/

theorem make_contains {α β : Type} [LT α] [DecidableLT α] [Cedar.Data.StrictLT α] [DecidableEq α]
    {l : List (α × β)} {k : α} {v : β} (h : (k, v) ∈ l) : (Map.make l).contains k = true := by
  rw [Map.contains_iff_some_find?, Map.make_find?_eq_list_find?]
  have : (l.find? fun x => x.fst == k).isSome := List.find?_isSome.mpr ⟨(k, v), h, by simp⟩
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp this
  exact ⟨p.2, by simp [hp]⟩

theorem entitySchema_contains {ets : List EntityEntry} {ee : EntityEntry} (h : ee ∈ ets) :
    (entitySchema ets).contains ee.name = true :=
  make_contains (List.mem_map.mpr ⟨ee, h, rfl⟩)

theorem actionSchema_contains {acts : List ActionEntry} {ae : ActionEntry} (h : ae ∈ acts) :
    (actionSchema acts).contains ae.uid = true :=
  make_contains (List.mem_map.mpr ⟨ae, h, rfl⟩)

theorem actionSchema_actionType {acts : List ActionEntry} {ae : ActionEntry} (h : ae ∈ acts) :
    (actionSchema acts).actionType? ae.uid.ty = true := by
  have hc := actionSchema_contains h
  simp only [Cedar.Validation.ActionSchema.contains, Option.isSome_iff_exists] at hc
  obtain ⟨v, hv⟩ := hc
  have hmem := Map.find?_mem_toList hv
  unfold Cedar.Validation.ActionSchema.actionType? Map.keys Set.any
  simp only [List.any_eq_true]
  exact ⟨ae.uid, List.mem_map.mpr ⟨_, hmem, rfl⟩, by simp⟩

theorem entitySchema_mem {ets : List EntityEntry} {k : EntityType} {v : EntitySchemaEntry}
    (h : (k, v) ∈ (entitySchema ets).toList) :
    ∃ ee ∈ ets, k = ee.name ∧ v = entityEntryOf ets ee := by
  have := Map.mem_make_mem_list h
  obtain ⟨ee, hee, heq⟩ := List.mem_map.mp this
  simp only [Prod.mk.injEq] at heq
  exact ⟨ee, hee, heq.1.symm, heq.2.symm⟩

theorem actionSchema_mem {acts : List ActionEntry} {k : EntityUID} {v : ActionSchemaEntry}
    (h : (k, v) ∈ (actionSchema acts).toList) :
    ∃ ae ∈ acts, k = ae.uid ∧ v = actionEntryOf acts ae := by
  have := Map.mem_make_mem_list h
  obtain ⟨ae, hae, heq⟩ := List.mem_map.mp this
  simp only [Prod.mk.injEq] at heq
  exact ⟨ae, hae, heq.1.symm, heq.2.symm⟩

/-! ## Every name is declared -/

/-- **Every entity type the resolved schema names is declared**: in attribute, tag and context
types, a declared entity type or an action's type; in `appliesTo` and among an entity type's
ancestors, a declared entity type; among an action's ancestors, a declared action. -/
theorem resolve_namesDeclared {f : Fragment} {S : Schema} (h : resolve f = .ok S) :
    NamesDeclared S := by
  have hr : resolveExcept f = .ok S := by
    unfold resolve at h
    cases h' : resolveExcept f <;> simp_all [Except.mapError]
  obtain ⟨-, ets, acts, hets, hacts, rfl⟩ := resolveExcept_ok hr
  -- every declared entity type is a key of the entity schema
  have hdecl : ∀ x ∈ (Defs.ofFragment f).declared, (entitySchema ets).contains x = true := by
    intro x hx
    obtain ⟨ns, d, hns, id, e, he, rfl⟩ := mem_userEntities.mp hx
    obtain ⟨ee, hee, hone⟩ := resolveEntityTypes_complete hets hns he
    rw [← (resolveEntityType_ok hone).1]
    exact entitySchema_contains hee
  -- every declared action is a key of the action schema
  have hact : ∀ u ∈ (Defs.ofFragment f).actions, (actionSchema acts).contains u = true := by
    intro u hu
    obtain ⟨ns, d, hns, id, a, ha, rfl⟩ := mem_userActions.mp hu
    obtain ⟨ae, hae, hone⟩ := resolveActions_complete hacts hns ha
    rw [← (resolveAction_ok hone).1]
    exact actionSchema_contains hae
  -- every entity type for name resolution is known to the schema
  have hknown : ∀ e ∈ (Defs.ofFragment f).entities,
      KnownType ⟨entitySchema ets, actionSchema acts⟩ e := by
    intro e he
    rcases mem_entities he with he | ⟨u, hu, rfl⟩
    · exact .inl (hdecl e he)
    · right
      obtain ⟨ns, d, hns, id, a, ha, rfl⟩ := mem_userActions.mp hu
      obtain ⟨ae, hae, hone⟩ := resolveActions_complete hacts hns ha
      have := actionSchema_actionType hae
      rwa [(resolveAction_ok hone).1] at this
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ety entry hmem a ha
    obtain ⟨ee, -, -, rfl⟩ := entitySchema_mem hmem
    unfold entityEntryOf at ha
    split at ha
    · simp only [EntitySchemaEntry.ancestors, Set.mem_make] at ha
      refine ancestorsOf_subset (P := fun y => (entitySchema ets).contains y = true) ?_ _ _ a ha
      intro x y hy
      obtain ⟨ee', hee', hy'⟩ := entityParents_mem hy
      obtain ⟨ns, d, -, id, e, -, hone⟩ := resolveEntityTypes_mem hets hee'
      exact hdecl y ((resolveEntityType_ok hone).2.1 y hy')
    · simp only [EntitySchemaEntry.ancestors, Set.empty] at ha
      exact absurd ha List.not_mem_nil
  · intro ety entry hmem e hm
    obtain ⟨ee, hee, -, rfl⟩ := entitySchema_mem hmem
    obtain ⟨ns, d, -, id, edef, -, hone⟩ := resolveEntityTypes_mem hets hee
    unfold entityEntryOf at hm
    split at hm
    · rename_i attrs tags hk
      exact hknown e (((resolveEntityType_ok hone).2.2 attrs tags hk).1 e hm)
    · cases hm with
      | record hmem' _ => simp [EntitySchemaEntry.attrs, Map.empty, Map.toList] at hmem'
  · intro ety entry t hmem ht e hm
    obtain ⟨ee, hee, -, rfl⟩ := entitySchema_mem hmem
    obtain ⟨ns, d, -, id, edef, -, hone⟩ := resolveEntityTypes_mem hets hee
    unfold entityEntryOf at ht
    split at ht
    · rename_i attrs tags hk
      exact hknown e (((resolveEntityType_ok hone).2.2 attrs tags hk).2 t ht e hm)
    · simp [EntitySchemaEntry.tags?] at ht
  · intro uid entry hmem p hp
    obtain ⟨ae, hae, -, rfl⟩ := actionSchema_mem hmem
    obtain ⟨ns, d, -, id, a, -, hone⟩ := resolveActions_mem hacts hae
    simp only [actionEntryOf, Set.mem_make] at hp
    exact hdecl p ((resolveAction_ok hone).2.2.1 p hp)
  · intro uid entry hmem u hu
    obtain ⟨ae, hae, -, rfl⟩ := actionSchema_mem hmem
    simp only [actionEntryOf, actionAncestors, Set.mem_make] at hu
    refine ancestorsOf_subset (P := fun y => (actionSchema acts).contains y = true) ?_ _ _ u hu
    intro x y hy
    obtain ⟨ae', hae', hy'⟩ := actionParents_mem hy
    obtain ⟨ns, d, -, id, a, -, hone⟩ := resolveActions_mem hacts hae'
    exact hact y ((resolveAction_ok hone).2.1 y hy')
  · intro uid entry hmem e hm
    obtain ⟨ae, hae, -, rfl⟩ := actionSchema_mem hmem
    obtain ⟨ns, d, -, id, a, -, hone⟩ := resolveActions_mem hacts hae
    exact hknown e ((resolveAction_ok hone).2.2.2 e hm)

/-! ## The derived events name actions of the resolved schema -/

theorem splitOnAux_ne_nil (s sep : String) (b i j : String.Pos.Raw) (r : List String) :
    String.splitOnAux s sep b i j r ≠ [] := by
  fun_induction String.splitOnAux s sep b i j r with
  | case1 => simp
  | _ => assumption

theorem splitOn_ne_nil (s sep : String) : s.splitOn sep ≠ [] := by
  unfold String.splitOn
  split
  · simp
  · exact splitOnAux_ne_nil _ _ _ _ _ _

theorem dropLast_append_getLastD {l : List String} (h : l ≠ []) :
    l.dropLast ++ [l.getLast?.getD ""] = l := by
  rw [List.getLast?_eq_getLast h]
  exact List.dropLast_concat_getLast h

/-- The action an event of namespace `ns` and action `id` names is the resolved action. -/
theorem actionUid_nsPath (ns : Option String) (id : String) :
    actionUid (Derive.nsPath ns ++ ["Action"]) id = ⟨actionType (nsName ns), id⟩ := by
  cases ns with
  | none => rfl
  | some n =>
    have hne := splitOn_ne_nil n "::"
    simp only [actionUid, Derive.nsPath, actionType, nsName, qualifyWith, parseName,
      Option.map_some, List.isEmpty_nil, if_true]
    rw [dropLast_append_getLastD hne]
    simp

/-- **Every derived event names an action of the resolved schema.** -/
theorem derive_actions_resolved {dsl : EventSchemaDsl.EventSchema} {f : Fragment}
    {d : DerivedEventSchema} {S : Schema} (h : Derive.derive dsl f = .ok d) (hS : resolve f = .ok S)
    {e : DerivedEvent} (he : e ∈ d.events) :
    S.acts.contains (actionUid e.namespace e.action) = true := by
  have hr : resolveExcept f = .ok S := by
    unfold resolve at hS
    cases h' : resolveExcept f <;> simp_all [Except.mapError]
  obtain ⟨-, ets, acts, -, hacts, rfl⟩ := resolveExcept_ok hr
  obtain ⟨ns, nd, hns, hn, ⟨a, ha⟩, -⟩ := derive_event_declared h he
  obtain ⟨ae, hae, hone⟩ := resolveActions_complete hacts hns ha
  rw [hn, actionUid_nsPath, ← (resolveAction_ok hone).1]
  exact actionSchema_contains hae

end Dogwood.Thm.Frontend.Derivation
