import Dogwood.Thm.Frontend.Augment.Context
import Dogwood.Spec.Validity

/-!
# The crate's augmentation and the specification's `Schema.augment`

`Dogwood.Spec.Schema.augment` adds every hoisted attribute to every action's context (keeping a
declared attribute over a hoisted one of the same name), which validates as the specification's
action-selective `PolicySet.augmentedSchema` does (`Dogwood.Thm.valid_iff_validAll`);
the crate adds a temporal field's attribute only to the actions its rule can apply to, and refuses
an action schema whose context declares a temporal field's name (`rejectDeclaredLeafNames`). This
module states what follows, at the level of an action's context record:

* **declared attributes**: augmentation keeps every attribute the action schema declares, except
  one that has the name of a temporal field targeting the action (which would become `Bool`) and
  `providers` on an action a provider field targets (`augment_keeps_declared`,
  `augment_changes_declared_only`, `augment_never_removes`);
* **hoisted attributes**: each temporal field's `Bool` is on every action it targets
  (`augment_hoists_on_targets`) and on no other action that does not declare it
  (`augment_omits_untargeted`);
* **agreement with `Schema.augment`**: for any attribute-wise compilation of record types
  (`compileAttrs`), on every attribute the action declares or a field targeting it hoists, the
  crate's compiled context agrees with the specification's augmented one, provided no declared
  attribute has a hoisted name (`augment_agrees_with_spec`). Without that proviso the two would
  differ, and augmentation refuses the schema (`CollisionExample`); that a successful
  augmentation meets the proviso is not yet proved. On the attributes of rules that cannot apply
  to the action, the crate's context has none and the specification's has them
  (`augment_selective`).

The provider fields: the specification adds each provider leaf as an attribute of its own; the
crate gathers them in the record `providers`, a reference to the shared provider type
(`augmentSchema_context`), so the two agree up to the renaming of `context.providers.<id>` as the
leaf's attribute, which the conformance bridge performs.
-/

namespace Dogwood.Frontend.Augment

open CedarSchema
open Cedar.Validation (QualifiedType Qualified CedarType BoolType)
open Cedar.Data (Map)
open Cedar.Spec (Attr)

/-! ## Declared and hoisted attributes -/

section
variable {F F' : Fragment} {decls : Option ProviderDecls.Declarations} {enums : List String}
  {CF : List ContextField} {PF : List ProviderField} {nsName id : String} {k : Option String}
  {attrs attrs' : List (String × AttrType)} {add add' : Bool}

/-- The augmented context at a key other than `providers`, or at any key of an action no provider
field targets: the hoisted `Bool` where a temporal field targeting the action has that name, the
declared attribute elsewhere. -/
theorem augment_lookup (h : augmentSchema F decls enums CF PF = .ok F') (hk : nsKey nsName = .ok k)
    (hc : contextAt F k id = some (.record attrs add))
    (hc' : contextAt F' k id = some (.record attrs' add')) (key : String)
    (hp : key ≠ "providers" ∨ (nsName, id) ∉ providerTargets PF) :
    add' = add ∧
      attrs'.lookup key = if hoistedAt CF nsName id key then some boolAttr else attrs.lookup key := by
  obtain ⟨attrs'', hc'', hP⟩ := augmentSchema_context h hk hc
  rw [hc'] at hc''
  simp only [Option.some.injEq, SchemaType.record.injEq] at hc''
  obtain ⟨rfl, rfl⟩ := hc''
  refine ⟨rfl, ?_⟩
  split at hP
  · rename_i hmem
    obtain ⟨attrsT, S, _, hext, _, hwith, _⟩ := hP
    have hkey : key ≠ "providers" := hp.resolve_right (fun h => h hmem)
    rw [hwith.1 key hkey, hext key]
  · exact hP key

/-- **Hoisted attributes are on their targets.** -/
theorem augment_hoists_on_targets (h : augmentSchema F decls enums CF PF = .ok F')
    (hk : nsKey nsName = .ok k) (hc : contextAt F k id = some (.record attrs add))
    (hc' : contextAt F' k id = some (.record attrs' add')) {fl : ContextField} (hf : fl ∈ CF)
    (ht : (nsName, id) ∈ fl.targetActions)
    (hp : fl.fieldName ≠ "providers" ∨ (nsName, id) ∉ providerTargets PF) :
    attrs'.lookup fl.fieldName = some boolAttr := by
  rw [(augment_lookup h hk hc hc' fl.fieldName hp).2]
  have : hoistedAt CF nsName id fl.fieldName = true := by
    simp only [hoistedAt, List.any_eq_true, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem]
    exact ⟨fl, hf, rfl, ht⟩
  simp [this]

/-- **Declared attributes are kept** unless a temporal field targeting the action has their name
(or, on an action a provider field targets, the name is `providers`). -/
theorem augment_keeps_declared (h : augmentSchema F decls enums CF PF = .ok F')
    (hk : nsKey nsName = .ok k) (hc : contextAt F k id = some (.record attrs add))
    (hc' : contextAt F' k id = some (.record attrs' add')) {key : String}
    (hkey : hoistedAt CF nsName id key = false)
    (hp : key ≠ "providers" ∨ (nsName, id) ∉ providerTargets PF) :
    attrs'.lookup key = attrs.lookup key := by
  rw [(augment_lookup h hk hc hc' key hp).2, hkey]; rfl

/-- **Exactly when a declared attribute changes**: a declared attribute other than `providers`
is changed exactly when a temporal field targeting the action has its name and it is not already
a required `Bool`; it then becomes one. -/
theorem augment_changes_declared_only (h : augmentSchema F decls enums CF PF = .ok F')
    (hk : nsKey nsName = .ok k) (hc : contextAt F k id = some (.record attrs add))
    (hc' : contextAt F' k id = some (.record attrs' add')) {key : String} {t : AttrType}
    (ht : attrs.lookup key = some t) (hp : key ≠ "providers") :
    (attrs'.lookup key = some t ↔ (hoistedAt CF nsName id key = true → t = boolAttr)) ∧
      (hoistedAt CF nsName id key = true → attrs'.lookup key = some boolAttr) := by
  rw [(augment_lookup h hk hc hc' key (.inl hp)).2]
  by_cases hh : hoistedAt CF nsName id key = true
  · simp only [hh, if_true, Option.some.injEq, true_implies]
    exact ⟨⟨fun e => e.symm, fun e => e.symm⟩, trivial⟩
  · simp only [Bool.not_eq_true] at hh
    simp [hh, ht]

/-- **No declared attribute is removed.** -/
theorem augment_never_removes (h : augmentSchema F decls enums CF PF = .ok F')
    (hk : nsKey nsName = .ok k) (hc : contextAt F k id = some (.record attrs add))
    (hc' : contextAt F' k id = some (.record attrs' add')) {key : String}
    (ht : (attrs.lookup key).isSome) : (attrs'.lookup key).isSome := by
  by_cases hp : key = "providers" ∧ (nsName, id) ∈ providerTargets PF
  · obtain ⟨rfl, hmem⟩ := hp
    obtain ⟨attrs'', hc'', hP⟩ := augmentSchema_context h hk hc
    rw [hc'] at hc''
    simp only [Option.some.injEq, SchemaType.record.injEq] at hc''
    obtain ⟨rfl, rfl⟩ := hc''
    rw [if_pos hmem] at hP
    obtain ⟨_, _, _, _, _, ⟨_, pa, hpa, _⟩, _⟩ := hP
    simp [hpa]
  · have hp' : key ≠ "providers" ∨ (nsName, id) ∉ providerTargets PF := by
      by_cases h1 : key = "providers"
      · exact .inr fun h2 => hp ⟨h1, h2⟩
      · exact .inl h1
    rw [(augment_lookup h hk hc hc' key hp').2]
    split <;> simp_all

/-- **Hoisted attributes are on no other action**: an attribute the action does not declare,
and no temporal field targeting it hoists, is absent from its augmented context (`providers`
aside). In particular the attribute of a temporal field whose rule cannot apply to the action. -/
theorem augment_omits_untargeted (h : augmentSchema F decls enums CF PF = .ok F')
    (hk : nsKey nsName = .ok k) (hc : contextAt F k id = some (.record attrs add))
    (hc' : contextAt F' k id = some (.record attrs' add')) {key : String}
    (hkey : hoistedAt CF nsName id key = false) (hnd : attrs.lookup key = none)
    (hp : key ≠ "providers") : attrs'.lookup key = none := by
  rw [augment_keeps_declared h hk hc hc' hkey (.inl hp), hnd]

end

/-! ## Agreement with `Schema.augment` -/

/-- An attribute-wise compilation of a record's attributes into the specification's attribute
types, `cmp` compiling one attribute; `none` when one does not compile. -/
def compileAttrs (cmp : AttrType → Option QualifiedType) (attrs : List (String × AttrType)) :
    Option (List (Attr × QualifiedType)) :=
  attrs.mapM fun (k, t) => (cmp t).map (k, ·)

theorem compileAttrs_lookup {cmp : AttrType → Option QualifiedType} :
    ∀ {attrs : List (String × AttrType)} {L : List (Attr × QualifiedType)},
      compileAttrs cmp attrs = some L → ∀ key, L.lookup key = (attrs.lookup key).bind cmp
  | [], L, h, key => by
    simp only [compileAttrs, List.mapM_nil, pure, Option.some.injEq] at h; subst h; rfl
  | (k, t) :: rest, L, h, key => by
    simp only [compileAttrs, List.mapM_cons, bind, Option.bind] at h
    cases hct : cmp t with
    | none => simp [hct] at h
    | some q =>
      simp only [hct, Option.map_some] at h
      cases hrest : List.mapM (fun x => Option.map (fun y => (x.1, y)) (cmp x.2)) rest with
      | none => simp [hrest] at h
      | some L' =>
        simp only [hrest, pure, Option.some.injEq] at h
        subst h
        have ih := compileAttrs_lookup (cmp := cmp) (attrs := rest) (L := L') hrest key
        rw [lookup_cons_ite, lookup_cons_ite, ih]
        by_cases hk : key = k <;> simp [hk, hct]

theorem compileAttrs_isSome {cmp : AttrType → Option QualifiedType} :
    ∀ {attrs : List (String × AttrType)} {L : List (Attr × QualifiedType)},
      compileAttrs cmp attrs = some L → ∀ key t, (key, t) ∈ attrs → (cmp t).isSome
  | [], _, _, _, _, hmem => by simp at hmem
  | (k, t) :: rest, L, h, key, t', hmem => by
    simp only [compileAttrs, List.mapM_cons, bind, Option.bind] at h
    cases hct : cmp t with
    | none => simp [hct] at h
    | some q =>
      simp only [hct, Option.map_some] at h
      cases hrest : List.mapM (fun x => Option.map (fun y => (x.1, y)) (cmp x.2)) rest with
      | none => simp [hrest] at h
      | some L' =>
        rcases List.mem_cons.mp hmem with heq | hmem'
        · simp only [Prod.mk.injEq] at heq; obtain ⟨rfl, rfl⟩ := heq; simp [hct]
        · exact compileAttrs_isSome (attrs := rest) hrest key t' hmem'

theorem find?_eq_lookup_toList {β : Type} (m : Map String β) (key : String) :
    m.find? key = m.toList.lookup key := by
  simp only [Map.find?]
  generalize m.toList = l
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨k, v⟩ := hd
    rw [lookup_cons_ite]
    by_cases hk : key = k
    · subst hk; simp [List.find?]
    · have : (k == key) = false := by simp [Ne.symm hk]
      simp only [List.find?, this, if_neg hk]
      exact ih

theorem find?_make {β : Type} (l : List (String × β)) (key : String) :
    (Map.make l).find? key = l.lookup key := by
  rw [Map.make_find?_eq_list_find?]
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨k, v⟩ := hd
    rw [lookup_cons_ite]
    by_cases hk : key = k
    · subst hk; simp [List.find?]
    · have : (k == key) = false := by simp [Ne.symm hk]
      simp only [List.find?, this, if_neg hk]
      exact ih

/-- The attributes the specification hoists for the temporal fields, each a required `Bool`
(with the crate's names). -/
def hoistedTypes (CF : List ContextField) : List (Attr × QualifiedType) :=
  CF.map fun f => (f.fieldName, .required (.bool .anyBool))

theorem lookup_hoistedTypes {CF : List ContextField} {key : String} :
    (hoistedTypes CF).lookup key =
      if CF.any (·.fieldName == key) then some (.required (.bool .anyBool)) else none := by
  induction CF with
  | nil => rfl
  | cons f rest ih =>
    simp only [hoistedTypes, List.map_cons, List.any_cons] at ih ⊢
    rw [lookup_cons_ite, ih]
    by_cases hk : key = f.fieldName
    · subst hk; simp
    · have : (f.fieldName == key) = false := by simp [Ne.symm hk]
      simp [hk, this]

/-- The specification's augmented schema at one action: the action's context extended with `H`,
a declared attribute kept over a hoisted one. -/
theorem find?_schemaAugment (A : Cedar.Validation.Schema) (H : List (Attr × QualifiedType))
    (uid : Cedar.Spec.EntityUID) :
    (Dogwood.Spec.Schema.augment A H).acts.find? uid =
      (A.acts.find? uid).map fun e => { e with context := Map.make (e.context.toList ++ H) } := by
  simp [Dogwood.Spec.Schema.augment]

theorem find?_augmentedContext (M : Map Attr QualifiedType) (H : List (Attr × QualifiedType))
    (key : String) : (Map.make (M.toList ++ H)).find? key = (M.find? key).or (H.lookup key) := by
  rw [find?_make, List.lookup_append, find?_eq_lookup_toList]

/-- **Agreement with `Schema.augment` on the targets.** Let `cmp` compile record attributes one by
one, with `Bool` compiled to `Bool`, and let the action's declared context `attrs` and its
augmented context `attrs'` compile to `L` and `L'`. If no declared attribute has the name of a
temporal field, then at every attribute the action declares and at every attribute a temporal
field targeting it hoists, the crate's compiled context `Map.make L'` agrees with the
specification's augmentation of `Map.make L` by every temporal field (`providers` aside, on an
action a provider field targets). -/
theorem augment_agrees_with_spec {F F' : Fragment} {decls : Option ProviderDecls.Declarations}
    {enums : List String} {CF : List ContextField} {PF : List ProviderField} {nsName id : String}
    {k : Option String} {attrs attrs' : List (String × AttrType)} {add add' : Bool}
    {cmp : AttrType → Option QualifiedType} {L L' : List (Attr × QualifiedType)}
    (hb : cmp boolAttr = some (.required (.bool .anyBool)))
    (h : augmentSchema F decls enums CF PF = .ok F') (hk : nsKey nsName = .ok k)
    (hc : contextAt F k id = some (.record attrs add))
    (hc' : contextAt F' k id = some (.record attrs' add'))
    (hL : compileAttrs cmp attrs = some L) (hL' : compileAttrs cmp attrs' = some L')
    (hnc : ∀ f ∈ CF, attrs.lookup f.fieldName = none) {key : String}
    (hkey : (attrs.lookup key).isSome ∨ hoistedAt CF nsName id key = true)
    (hp : key ≠ "providers" ∨ (nsName, id) ∉ providerTargets PF) :
    (Map.make L').find? key = (Map.make ((Map.make L).toList ++ hoistedTypes CF)).find? key := by
  rw [find?_augmentedContext, find?_make, find?_make, compileAttrs_lookup hL' key,
    compileAttrs_lookup hL key, (augment_lookup h hk hc hc' key hp).2, lookup_hoistedTypes]
  by_cases hh : hoistedAt CF nsName id key = true
  · obtain ⟨fl, hf, hname⟩ : ∃ fl ∈ CF, fl.fieldName = key := by
      simp only [hoistedAt, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at hh
      obtain ⟨fl, hf, hn, _⟩ := hh
      exact ⟨fl, hf, hn⟩
    have hnone : attrs.lookup key = none := hname ▸ hnc fl hf
    have hany : CF.any (·.fieldName == key) = true :=
      List.any_eq_true.mpr ⟨fl, hf, by simp [hname]⟩
    simp [hh, hnone, hany, hb]
  · simp only [Bool.not_eq_true] at hh
    have hdecl : (attrs.lookup key).isSome := hkey.resolve_right (by simp [hh])
    obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp hdecl
    have hmem : (key, t) ∈ attrs := by
      obtain ⟨l₁, l₂, heq, _⟩ := List.lookup_eq_some_iff.mp ht
      rw [heq]; simp
    obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp (compileAttrs_isSome hL key t hmem)
    simp [hh, ht, hq]

/-- **Agreement with `Schema.augment`**, stated on the specification's schema: if the action
schema's compiled entry for the action has the compiled declared context, then the entry of
`Schema.augment A (hoistedTypes CF)` agrees with the crate's compiled context at every attribute
the action declares or a temporal field targeting it hoists. -/
theorem augment_agrees_with_schemaAugment {F F' : Fragment}
    {decls : Option ProviderDecls.Declarations} {enums : List String} {CF : List ContextField}
    {PF : List ProviderField} {nsName id : String} {k : Option String}
    {attrs attrs' : List (String × AttrType)} {add add' : Bool}
    {cmp : AttrType → Option QualifiedType} {L L' : List (Attr × QualifiedType)}
    {A : Cedar.Validation.Schema} {uid : Cedar.Spec.EntityUID}
    {e : Cedar.Validation.ActionSchemaEntry}
    (hb : cmp boolAttr = some (.required (.bool .anyBool)))
    (h : augmentSchema F decls enums CF PF = .ok F') (hk : nsKey nsName = .ok k)
    (hc : contextAt F k id = some (.record attrs add))
    (hc' : contextAt F' k id = some (.record attrs' add'))
    (hL : compileAttrs cmp attrs = some L) (hL' : compileAttrs cmp attrs' = some L')
    (hA : A.acts.find? uid = some e) (he : e.context = Map.make L)
    (hnc : ∀ f ∈ CF, attrs.lookup f.fieldName = none) {key : String}
    (hkey : (attrs.lookup key).isSome ∨ hoistedAt CF nsName id key = true)
    (hp : key ≠ "providers" ∨ (nsName, id) ∉ providerTargets PF) :
    ∃ e', (Dogwood.Spec.Schema.augment A (hoistedTypes CF)).acts.find? uid = some e' ∧
      e'.context.find? key = (Map.make L').find? key := by
  refine ⟨_, by rw [find?_schemaAugment, hA]; rfl, ?_⟩
  simp only [he]
  exact (augment_agrees_with_spec hb h hk hc hc' hL hL' hnc hkey hp).symm

/-- **The crate's augmentation is selective.** The attribute of a temporal field that does not
target the action, and that the action does not declare, is absent from the crate's compiled
context, while the specification's augmented context has it, as a required `Bool`. -/
theorem augment_selective {F F' : Fragment} {decls : Option ProviderDecls.Declarations}
    {enums : List String} {CF : List ContextField} {PF : List ProviderField} {nsName id : String}
    {k : Option String} {attrs attrs' : List (String × AttrType)} {add add' : Bool}
    {cmp : AttrType → Option QualifiedType} {L L' : List (Attr × QualifiedType)}
    (h : augmentSchema F decls enums CF PF = .ok F') (hk : nsKey nsName = .ok k)
    (hc : contextAt F k id = some (.record attrs add))
    (hc' : contextAt F' k id = some (.record attrs' add'))
    (hL : compileAttrs cmp attrs = some L) (hL' : compileAttrs cmp attrs' = some L')
    {fl : ContextField} (hf : fl ∈ CF) (hnt : hoistedAt CF nsName id fl.fieldName = false)
    (hnd : attrs.lookup fl.fieldName = none) (hp : fl.fieldName ≠ "providers") :
    (Map.make L').find? fl.fieldName = none ∧
      (Map.make ((Map.make L).toList ++ hoistedTypes CF)).find? fl.fieldName =
        some (.required (.bool .anyBool)) := by
  constructor
  · rw [find?_make, compileAttrs_lookup hL', augment_omits_untargeted h hk hc hc' hnt hnd hp]; rfl
  · rw [find?_augmentedContext, find?_make, compileAttrs_lookup hL, hnd, lookup_hoistedTypes]
    have : CF.any (·.fieldName == fl.fieldName) = true := List.any_eq_true.mpr ⟨fl, hf, by simp⟩
    simp [this]

/-! ## A declared attribute with a hoisted name -/

namespace CollisionExample

/-- The hoisted name, declared by the action schema too. -/
def name : String := "policy_0__temporal_0"

/-- The context of `read` with an attribute `name` of type `ty`. -/
def context (ty : AttrType) : SchemaType := .record [(name, ty)] false

/-- An action `read` whose context declares `name` with the type `ty`. -/
def read (ty : AttrType) : ActionDef :=
  { attributes := none
    memberOf := none
    annotations := []
    appliesTo := some { principalTypes := ["User"], resourceTypes := ["Doc"], context := context ty } }

/-- A schema, in the root namespace, of the one action `read`, whose context declares `name`
with the type `ty`. -/
def schema (ty : AttrType) : Fragment :=
  [(none, { commonTypes := [], entityTypes := [], annotations := [], actions := [("read", read ty)] })]

/-- `Long`, required. -/
def longAttr : AttrType := ⟨.long, true, []⟩

/-- A temporal field of that name targeting `read`. -/
def field : ContextField :=
  { action := .concrete "" "read", fieldName := name, temporal := default,
    targetActions := [("", "read")], principal := .any, resource := .any }

/-- A compilation of the two attribute types involved. -/
def cmp : AttrType → Option QualifiedType
  | ⟨.long, true, _⟩ => some (.required .int)
  | ⟨.boolean, true, _⟩ => some (.required (.bool .anyBool))
  | _ => none

end CollisionExample

open CollisionExample in
/-- **A declared attribute with a hoisted name is refused.** The action schema declares
`policy_0__temporal_0: Long` on `read`, and a temporal field of that name targets `read`.
Replacing the attribute by the leaf's `Bool` would disagree with `Schema.augment`, which keeps
`Long` (as the last two conjuncts compute); augmentation refuses the action schema instead (the
crate's `reject_declared_leaf_names`), as `PolicySet.Valid.namesFresh` does. -/
example :
    (augmentSchema (schema longAttr) none [] [field] []).toBool = false ∧
    contextAt (schema longAttr) none "read" = some (.record [(name, longAttr)] false) ∧
    compileAttrs cmp [(name, longAttr)] = some [(name, .required .int)] ∧
    (Map.make ((Map.make [(name, (.required .int : QualifiedType))]).toList ++ hoistedTypes [field])).find? name =
      some (.required .int) :=
  ⟨rfl, rfl, rfl, by decide +kernel⟩

end Dogwood.Frontend.Augment
