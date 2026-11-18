import Dogwood.Thm.Frontend.Augment.Basic

/-!
# What augmentation does to an action's context

For an action whose context the action schema declares as an inline record, the crate's
augmentation (`augmentSchema`) adds exactly:

* the attribute `<name>: Bool`, required, of each temporal field that targets the action
  (`hoistedAt`); an action schema whose context declares that name is refused
  (`rejectDeclaredLeafNames`);
* the attribute `providers`, a reference to the namespace's shared provider type, when a
  provider field targets the action; the shared type is a record holding every provider field,
  with the type the crate's parse of the field's Cedar type gives it, builtin names pinned to
  `__cedar::` (`SharedTypeHolds`).

Every other attribute is the declared one (`augmentSchema_context`). The provider enums are
entity types, and inlining touches only contexts that are type references, so neither changes
an inline context.
-/

namespace Dogwood.Frontend.Augment

open CedarSchema

/-! ## Namespace keys -/

theorem nsKey_eq_ok {a : String} {k : Option String} (h : nsKey a = .ok k) :
    k = if a.isEmpty then none else some a := by
  unfold nsKey at h
  by_cases hea : a.isEmpty
  · simp only [hea, if_true, Except.ok.injEq] at h; simp [hea, h]
  · by_cases hn : isName a
    · simp only [hea, hn, if_true, Bool.false_eq_true, if_false, Except.ok.injEq] at h; simp [hea, h]
    · simp [hea, hn] at h

theorem nsKey_inj {a b : String} {k : Option String} (ha : nsKey a = .ok k) (hb : nsKey b = .ok k) :
    a = b := by
  have h1 := nsKey_eq_ok ha
  have h2 := nsKey_eq_ok hb
  rw [h1] at h2
  by_cases hea : a.isEmpty <;> by_cases heb : b.isEmpty <;> simp only [hea, heb] at h2
  · simp only [String.isEmpty_iff] at hea heb; rw [hea, heb]
  · simp at h2
  · simp at h2
  · simpa using h2

theorem getNs_of_actionAt {f : Fragment} {k : Option String} {id : String} {a : ActionDef}
    (h : actionAt f k id = some a) : ∃ nd, getNs f k = some nd ∧ nd.actions.lookup id = some a := by
  unfold actionAt at h
  cases hg : getNs f k with
  | none => simp [hg] at h
  | some nd => exact ⟨nd, rfl, by simpa [hg] using h⟩

/-! ## Inlining keeps inline contexts -/

theorem inlineStep_contextAt_record {D : Defs} {defs : List (String × SchemaType)}
    {sel : Option String → String → Bool} {acc acc' : Fragment} {key : Option String × String}
    {k : Option String} {id : String} {attrs : List (String × AttrType)} {add : Bool}
    (hc : contextAt acc k id = some (.record attrs add))
    (h : inlineStep D defs sel acc key = .ok acc') :
    contextAt acc' k id = some (.record attrs add) := by
  obtain ⟨ns, id2⟩ := key
  unfold inlineStep at h
  simp only at h
  split at h
  · split at h
    · rename_i a ha
      split at h
      · rename_i ap hap
        split at h
        · rename_i href
          split at h
          · rename_i t ht
            simp only [Except.ok.injEq] at h
            subst h
            obtain ⟨nd, hnd, _⟩ := getNs_of_actionAt ha
            rw [contextAt_setAction hnd]
            split
            · rename_i hsame
              obtain ⟨rfl, rfl⟩ := hsame
              simp [contextAt, ha, hap] at hc
              simp [hc, contextReferenceName] at href
            · exact hc
          · simp only [Except.ok.injEq] at h; subst h; exact hc
          · exact absurd h (by simp)
        · simp only [Except.ok.injEq] at h; subst h; exact hc
      · simp only [Except.ok.injEq] at h; subst h; exact hc
    · simp only [Except.ok.injEq] at h; subst h; exact hc
  · simp only [Except.ok.injEq] at h; subst h; exact hc

/-- Inlining leaves every inline context record as it is. -/
theorem inlineSelectedContexts_contextAt_record {f f' : Fragment}
    {sel : Option String → String → Bool} {k : Option String} {id : String}
    {attrs : List (String × AttrType)} {add : Bool}
    (h : inlineSelectedContexts f sel = .ok f') (hc : contextAt f k id = some (.record attrs add)) :
    contextAt f' k id = some (.record attrs add) := by
  unfold inlineSelectedContexts at h
  split at h
  · simp only [Except.ok.injEq] at h; subst h; exact hc
  · split at h
    · exact absurd h (by simp)
    · exact foldlM_ok_invariant (P := fun acc => contextAt acc k id = some (.record attrs add)) _ hc
        (fun _ _ _ _ hP hs => inlineStep_contextAt_record hP hs) h

/-! ## Temporal fields -/

/-- Some temporal field of `fields` named `key` targets the action `id` of the namespace
`nsName`. -/
def hoistedAt (fields : List ContextField) (nsName id key : String) : Bool :=
  fields.any fun f => f.fieldName == key && f.targetActions.contains (nsName, id)

theorem string_beq_comm (a b : String) : (a == b) = (b == a) := by
  by_cases h : a = b
  · subst h; rfl
  · have h' : ¬ b = a := fun e => h e.symm
    rw [show (a == b) = false from by simp [h], show (b == a) = false from by simp [h']]

/-- `attrs'` is `attrs` with the attribute `boolAttr` at every key `S` admits. -/
def ExtendsBy (attrs attrs' : List (String × AttrType)) (S : String → Bool) : Prop :=
  ∀ key, attrs'.lookup key = if S key then some boolAttr else attrs.lookup key

theorem extendsBy_refl (attrs : List (String × AttrType)) : ExtendsBy attrs attrs fun _ => false := by
  intro key; simp

theorem extendsBy_insert {attrs attrs' : List (String × AttrType)} {S : String → Bool}
    (h : ExtendsBy attrs attrs' S) (name : String) :
    ExtendsBy attrs (insertKey name boolAttr attrs') fun key => key == name || S key := by
  intro key
  rw [lookup_insertKey, h key]
  by_cases hk : key = name <;> simp [hk]

theorem extendsBy_congr {attrs attrs' : List (String × AttrType)} {S T : String → Bool}
    (h : ExtendsBy attrs attrs' S) (hST : ∀ key, S key = T key) : ExtendsBy attrs attrs' T := by
  intro key; rw [h key, hST key]

/-- A successful `addBoolToAction`, unfolded. -/
theorem addBoolToAction_ok {f f' : Fragment} {name nsName id : String}
    (h : addBoolToAction f name nsName id = .ok f') :
    ∃ k nd a ap attrs add, nsKey nsName = .ok k ∧ getNs f k = some nd ∧
      nd.actions.lookup id = some a ∧ a.appliesTo = some ap ∧ ap.context = .record attrs add ∧
      f' = setAction f k id { a with appliesTo := some { ap with
        context := .record (insertKey name boolAttr attrs) add } } := by
  unfold addBoolToAction at h
  split at h
  · exact absurd h (by simp)
  · rename_i k hk
    split at h
    · exact absurd h (by simp)
    · rename_i nd hnd
      split at h
      · exact absurd h (by simp)
      · rename_i a ha
        split at h
        · exact absurd h (by simp)
        · rename_i ap hap
          split at h
          · rename_i attrs add hctx
            simp only [Except.ok.injEq] at h
            exact ⟨k, nd, a, ap, attrs, add, hk, hnd, ha, hap, hctx, h.symm⟩
          · exact absurd h (by simp)
          · exact absurd h (by simp)

theorem addBoolToAction_contextAt {f f' : Fragment} {name nsName id nsName₀ id₀ : String}
    {k₀ : Option String} {attrs : List (String × AttrType)} {add : Bool}
    (h : addBoolToAction f name nsName id = .ok f') (hk₀ : nsKey nsName₀ = .ok k₀)
    (hc : contextAt f k₀ id₀ = some (.record attrs add)) :
    contextAt f' k₀ id₀ = some (.record
      (if nsName₀ = nsName ∧ id₀ = id then insertKey name boolAttr attrs else attrs) add) := by
  obtain ⟨k, nd, a, ap, attrs1, add1, hk, hnd, ha, hap, hctx, rfl⟩ := addBoolToAction_ok h
  rw [contextAt_setAction hnd]
  by_cases hsame : k₀ = k ∧ id₀ = id
  · obtain ⟨rfl, rfl⟩ := hsame
    have hns : nsName₀ = nsName := nsKey_inj hk₀ hk
    simp only [contextAt, actionAt, hnd, Option.bind_some, ha, hap, Option.map_some, hctx,
      Option.some.injEq, SchemaType.record.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    simp [hns]
  · rw [if_neg hsame]
    have : ¬ (nsName₀ = nsName ∧ id₀ = id) := by
      rintro ⟨rfl, rfl⟩
      exact hsame ⟨by rw [hk₀] at hk; simpa using hk, rfl⟩
    rw [if_neg this]; exact hc

theorem addBoolField_contextAt {f f' : Fragment} {field : ContextField} {nsName₀ id₀ : String}
    {k₀ : Option String} {attrs attrs₀ : List (String × AttrType)} {add : Bool} {S : String → Bool}
    (h : addBoolField f field = .ok f') (hk₀ : nsKey nsName₀ = .ok k₀)
    (hc : contextAt f k₀ id₀ = some (.record attrs₀ add)) (hS : ExtendsBy attrs attrs₀ S) :
    ∃ attrs', contextAt f' k₀ id₀ = some (.record attrs' add) ∧
      ExtendsBy attrs attrs' fun key =>
        (key == field.fieldName && field.targetActions.contains (nsName₀, id₀)) || S key := by
  unfold addBoolField at h
  have := foldlM_ok_induction (P := fun acc pre => ∃ attrs', contextAt acc k₀ id₀ = some (.record attrs' add) ∧
      ExtendsBy attrs attrs' fun key => (key == field.fieldName && pre.contains (nsName₀, id₀)) || S key)
    field.targetActions ⟨attrs₀, hc, extendsBy_congr hS (by simp)⟩
    (fun acc pre x acc' hP hs => by
      obtain ⟨attrs', hc', hext⟩ := hP
      obtain ⟨ns, id⟩ := x
      refine ⟨_, addBoolToAction_contextAt hs hk₀ hc', ?_⟩
      by_cases hx : nsName₀ = ns ∧ id₀ = id
      · rw [if_pos hx]
        obtain ⟨rfl, rfl⟩ := hx
        refine extendsBy_congr (extendsBy_insert hext field.fieldName) fun key => ?_
        by_cases hk : key = field.fieldName
        · simp [hk]
        · have hb : (key == field.fieldName) = false := by simpa using hk
          simp [hb]
      · rw [if_neg hx]
        refine extendsBy_congr hext fun key => ?_
        have hd : (decide (nsName₀ = ns) && decide (id₀ = id)) = false := by
          by_cases h1 : nsName₀ = ns <;> simp_all
        simp [hd]) h
  simpa using this

/-- **The temporal pass** adds, to an inline context record, the attribute `Bool` of every
temporal field that targets the action, and keeps every other attribute. -/
theorem addBoolContextFields_contextAt {f f' : Fragment} {fields : List ContextField}
    {nsName id : String} {k : Option String} {attrs : List (String × AttrType)} {add : Bool}
    (h : addBoolContextFields f fields = .ok f') (hk : nsKey nsName = .ok k)
    (hc : contextAt f k id = some (.record attrs add)) :
    ∃ attrs', contextAt f' k id = some (.record attrs' add) ∧
      ExtendsBy attrs attrs' (hoistedAt fields nsName id) := by
  unfold addBoolContextFields at h
  split at h
  · rename_i hempty
    simp only [Except.ok.injEq] at h; subst h
    refine ⟨attrs, hc, extendsBy_congr (extendsBy_refl attrs) fun key => ?_⟩
    simp [List.isEmpty_iff.mp hempty, hoistedAt]
  · obtain ⟨f1, hf1, hfold⟩ := bind_eq_ok.mp h
    obtain ⟨_, _, hfold⟩ := bind_eq_ok.mp hfold
    have hc1 := inlineSelectedContexts_contextAt_record hf1 hc
    have := foldlM_ok_induction (P := fun acc pre => ∃ attrs', contextAt acc k id = some (.record attrs' add) ∧
        ExtendsBy attrs attrs' (hoistedAt pre nsName id))
      fields ⟨attrs, hc1, extendsBy_congr (extendsBy_refl attrs) fun key => by simp [hoistedAt]⟩
      (fun acc pre x acc' hP hs => by
        obtain ⟨attrs', hc', hext⟩ := hP
        obtain ⟨attrs'', hc'', hext'⟩ := addBoolField_contextAt hs hk hc' hext
        refine ⟨attrs'', hc'', extendsBy_congr hext' fun key => ?_⟩
        simp only [hoistedAt, List.any_append, List.any_cons, List.any_nil, Bool.or_false]
        rw [Bool.or_comm, string_beq_comm key x.fieldName]) hfold
    exact this

/-! ## Provider enums -/

/-- Injecting the provider enums changes no action. -/
theorem addProviderEntityTypes_actionAt {f f' : Fragment} {d : ProviderDecls.Declarations}
    {referenced : List String} (h : addProviderEntityTypes f d referenced = .ok f')
    (k : Option String) (id : String) : actionAt f' k id = actionAt f k id := by
  unfold addProviderEntityTypes at h
  simp only at h
  split at h
  · split at h
    · exact absurd h (by simp)
    · simp only [Except.ok.injEq] at h; subst h; rfl
  · split at h
    · exact absurd h (by simp)
    · obtain ⟨⟨errors, entries⟩, _, h⟩ := bind_eq_ok.mp h
      simp only at h
      split at h
      · exact absurd h (by simp [bind, Except.bind])
      · obtain ⟨_, _, h⟩ := bind_eq_ok.mp h
        split at h
        · rename_i nd hnd
          simp only [pure, Except.pure, Except.ok.injEq] at h
          subst h
          refine actionAt_setNs_of_actions hnd ?_ k id
          rfl
        · exact absurd h (by simp [throw, throwThe, MonadExceptOf.throw])

theorem addProviderEntityTypes_contextAt {f f' : Fragment} {d : ProviderDecls.Declarations}
    {referenced : List String} (h : addProviderEntityTypes f d referenced = .ok f')
    (k : Option String) (id : String) : contextAt f' k id = contextAt f k id := by
  simp only [contextAt, addProviderEntityTypes_actionAt h]

/-! ## Provider fields -/

/-- The common type `id` of the namespace `k`. -/
def commonTypeAt (f : Fragment) (k : Option String) (id : String) : Option CommonType :=
  (getNs f k).bind (·.commonTypes.lookup id)

theorem commonTypeAt_setAction {f : Fragment} {k : Option String} {id : String} {a : ActionDef}
    {nd : NamespaceDef} (h : getNs f k = some nd) (k' : Option String) (c : String) :
    commonTypeAt (setAction f k id a) k' c = commonTypeAt f k' c := by
  simp only [setAction, h, commonTypeAt]
  by_cases hk : k' = k
  · subst hk; rw [getNs_setNs_self h, h]; rfl
  · rw [getNs_setNs_ne _ hk]

/-- A successful `writeSharedType`, unfolded. -/
theorem writeSharedType_ok {allAttrs : List (String × AttrType)} {out out' : Fragment}
    {nsName sid : String} (h : writeSharedType allAttrs out (nsName, sid) = .ok out') :
    ∃ k nd c, nsKey nsName = .ok k ∧ getNs out k = some nd ∧ c.ty = .record allAttrs false ∧
      out' = setNs out k { nd with commonTypes := insertKey sid c nd.commonTypes } := by
  unfold writeSharedType at h
  simp only at h
  split at h
  · exact absurd h (by simp)
  · rename_i k hk
    split at h
    · exact absurd h (by simp)
    · rename_i nd hnd
      simp only [Except.ok.injEq] at h
      refine ⟨k, nd, _, hk, hnd, ?_, h.symm⟩
      split <;> rfl

theorem writeSharedType_contextAt {allAttrs : List (String × AttrType)} {out out' : Fragment}
    {e : String × String} (h : writeSharedType allAttrs out e = .ok out') (k : Option String)
    (id : String) : contextAt out' k id = contextAt out k id := by
  obtain ⟨nsName, sid⟩ := e
  obtain ⟨k', nd, c, _, hnd, _, rfl⟩ := writeSharedType_ok h
  refine contextAt_setNs_of_actions hnd ?_ k id
  rfl

/-- After the shared types are written, the namespace of each has its shared type, a record of
`allAttrs`. -/
theorem writeSharedTypes_commonTypeAt {allAttrs : List (String × AttrType)} {f out : Fragment}
    {ids : List (String × String)} (h : ids.foldlM (writeSharedType allAttrs) f = .ok out) :
    ∀ nsName sid k, (nsName, sid) ∈ ids → nsKey nsName = .ok k →
      ∃ c, commonTypeAt out k sid = some c ∧ c.ty = .record allAttrs false := by
  have := foldlM_ok_induction (P := fun acc pre => ∀ nsName sid k, (nsName, sid) ∈ pre →
      nsKey nsName = .ok k → ∃ c, commonTypeAt acc k sid = some c ∧ c.ty = .record allAttrs false)
    ids (by simp)
    (fun acc pre x acc' hP hs => by
      obtain ⟨ns2, sid2⟩ := x
      obtain ⟨k2, nd, c2, hk2, hnd, hc2, rfl⟩ := writeSharedType_ok hs
      intro nsName sid k hmem hk
      simp only [commonTypeAt]
      by_cases hkk : k = k2
      · subst hkk
        rw [getNs_setNs_self hnd]
        simp only [Option.bind_some, lookup_insertKey]
        by_cases hs : sid = sid2
        · subst hs; exact ⟨c2, by simp, hc2⟩
        · simp only [hs, if_false]
          rcases List.mem_append.mp hmem with hpre | hlast
          · obtain ⟨c, hc, hcty⟩ := hP nsName sid k hpre hk
            simp only [commonTypeAt, hnd, Option.bind_some] at hc
            exact ⟨c, hc, hcty⟩
          · simp only [List.mem_singleton, Prod.mk.injEq] at hlast
            exact absurd hlast.2 hs
      · rw [getNs_setNs_ne _ hkk]
        rcases List.mem_append.mp hmem with hpre | hlast
        · exact hP nsName sid k hpre hk
        · simp only [List.mem_singleton, Prod.mk.injEq] at hlast
          obtain ⟨rfl, rfl⟩ := hlast
          rw [hk] at hk2
          exact absurd (by simpa using hk2) hkk) h
  exact this

theorem writeSharedTypes_contextAt {allAttrs : List (String × AttrType)} {f out : Fragment}
    {ids : List (String × String)} (h : ids.foldlM (writeSharedType allAttrs) f = .ok out)
    (k : Option String) (id : String) : contextAt out k id = contextAt f k id :=
  foldlM_ok_invariant (P := fun acc => contextAt acc k id = contextAt f k id) ids rfl
    (fun _ _ _ _ hP hs => (writeSharedType_contextAt hs k id).trans hP) h

/-- A successful `insertProviderReference`, unfolded. -/
theorem insertProviderReference_ok {f f' : Fragment} {nsName id sharedName : String}
    (h : insertProviderReference f nsName id sharedName = .ok f') :
    ∃ k a ap attrs add attr, nsKey nsName = .ok k ∧ actionAt f k id = some a ∧
      a.appliesTo = some ap ∧ ap.context = .record attrs add ∧
      providersAttr (attrs.lookup "providers") nsName sharedName = some attr ∧
      f' = setAction f k id { a with appliesTo := some { ap with
        context := .record (insertKey "providers" attr attrs) add } } := by
  unfold insertProviderReference at h
  split at h
  · exact absurd h (by simp)
  · rename_i k hk
    split at h
    · exact absurd h (by simp)
    · rename_i a ha
      split at h
      · exact absurd h (by simp)
      · rename_i ap hap
        split at h
        · rename_i attrs add hctx
          split at h
          · rename_i attr hattr
            simp only [Except.ok.injEq] at h
            exact ⟨k, a, ap, attrs, add, attr, hk, ha, hap, hctx, hattr, h.symm⟩
          · exact absurd h (by simp)
        · exact absurd h (by simp)
        · exact absurd h (by simp)

/-- The attribute `providersAttr` gives references the shared type. -/
theorem providersAttr_matches {existing : Option AttrType} {nsName sharedName : String}
    {attr : AttrType} (h : providersAttr existing nsName sharedName = some attr) :
    providerTypeReferenceMatches attr.ty nsName sharedName = true := by
  unfold providersAttr at h
  split at h
  · split at h
    · simp only [Option.some.injEq] at h; subst h; assumption
    · exact absurd h (by simp)
  · simp only [Option.some.injEq] at h; subst h
    simp [providerTypeReferenceMatches, contextReferenceName]

/-- `providersAttr` keeps an attribute that already references the shared type. -/
theorem providersAttr_of_matches {attr : AttrType} {nsName sharedName : String}
    (h : providerTypeReferenceMatches attr.ty nsName sharedName = true) :
    providersAttr (some attr) nsName sharedName = some attr := by
  simp [providersAttr, h]

/-- `attrs'` is `attrs` with the attribute `providers` referencing the shared type `S`. -/
def WithProviders (attrs attrs' : List (String × AttrType)) (nsName S : String) : Prop :=
  (∀ key, key ≠ "providers" → attrs'.lookup key = attrs.lookup key) ∧
    ∃ pa, attrs'.lookup "providers" = some pa ∧ providerTypeReferenceMatches pa.ty nsName S = true

/-- The fold of `insertProviderReference` over the target actions: at the action `id` of the
namespace `nsName`, `providers` references the shared type when the action is one of the targets
folded so far; every other attribute stays. -/
theorem insertProviderReferences_contextAt {f out : Fragment} {targets : List (String × String)}
    {name : String → String} {nsName id : String} {k : Option String}
    {attrs : List (String × AttrType)} {add : Bool}
    (h : targets.foldlM (fun out (ns, id) => insertProviderReference out ns id (name ns)) f = .ok out)
    (hk : nsKey nsName = .ok k) (hc : contextAt f k id = some (.record attrs add)) :
    ∃ attrs', contextAt out k id = some (.record attrs' add) ∧
      (if (nsName, id) ∈ targets then WithProviders attrs attrs' nsName (name nsName)
       else attrs' = attrs) := by
  have := foldlM_ok_induction (P := fun acc pre => ∃ attrs', contextAt acc k id = some (.record attrs' add) ∧
      (if (nsName, id) ∈ pre then WithProviders attrs attrs' nsName (name nsName) else attrs' = attrs))
    targets ⟨attrs, hc, by simp⟩
    (fun acc pre x acc' hP hs => by
      obtain ⟨attrs', hc', hinv⟩ := hP
      obtain ⟨ns2, id2⟩ := x
      obtain ⟨k2, a, ap, attrs2, add2, attr, hk2, ha, hap, hctx, hattr, rfl⟩ :=
        insertProviderReference_ok hs
      obtain ⟨nd, hnd, _⟩ := getNs_of_actionAt ha
      rw [contextAt_setAction hnd]
      by_cases hsame : k = k2 ∧ id = id2
      · obtain ⟨rfl, rfl⟩ := hsame
        have hns : nsName = ns2 := nsKey_inj hk hk2
        subst hns
        simp only [contextAt, ha, hap, Option.bind_some, Option.map_some, hctx, Option.some.injEq,
          SchemaType.record.injEq] at hc'
        obtain ⟨rfl, rfl⟩ := hc'
        refine ⟨insertKey "providers" attr attrs2, by simp, ?_⟩
        have hmem : (nsName, id) ∈ pre ++ [(nsName, id)] := by simp
        rw [if_pos hmem]
        refine ⟨fun key hkey => ?_, attr, lookup_insertKey_self _ _ _, providersAttr_matches hattr⟩
        rw [lookup_insertKey_ne _ _ hkey]
        split at hinv
        · exact hinv.1 key hkey
        · rw [hinv]
      · rw [if_neg hsame]
        refine ⟨attrs', hc', ?_⟩
        have hne : (nsName, id) ≠ (ns2, id2) := by
          rintro ⟨⟩
          exact hsame ⟨by rw [hk] at hk2; simpa using hk2, rfl⟩
        have hiff : (nsName, id) ∈ pre ++ [(ns2, id2)] ↔ (nsName, id) ∈ pre := by
          simp only [List.mem_append, List.mem_singleton]; exact ⟨fun h => h.resolve_right hne, Or.inl⟩
        simp only [hiff]; exact hinv) h
  exact this

/-- After `assignSharedId` over the target namespaces, each has a shared type name. -/
theorem assignSharedIds_lookup {f : Fragment} {nss : List String} {init ids : List (String × String)}
    (h : nss.foldlM (assignSharedId f) init = .ok ids) :
    ∀ nsName ∈ nss, ∃ sid, ids.lookup nsName = some sid := by
  have := foldlM_ok_induction (P := fun acc pre => ∀ nsName ∈ pre, ∃ sid, acc.lookup nsName = some sid)
    nss (by simp)
    (fun acc pre x acc' hP hs => by
      unfold assignSharedId at hs
      intro nsName hmem
      split at hs
      · rename_i hsome
        simp only [Except.ok.injEq] at hs; subst hs
        rcases List.mem_append.mp hmem with hpre | hlast
        · exact hP nsName hpre
        · simp only [List.mem_singleton] at hlast; subst hlast
          exact Option.isSome_iff_exists.mp hsome
      · split at hs
        · exact absurd hs (by simp)
        · split at hs
          · simp only [Except.ok.injEq] at hs; subst hs
            rw [lookup_insertKey]
            by_cases hx : nsName = x
            · simp [hx]
            · simp only [hx, if_false]
              rcases List.mem_append.mp hmem with hpre | hlast
              · exact hP nsName hpre
              · simp at hlast; exact absurd hlast hx
          · exact absurd hs (by simp)) h
  exact this

/-- Merging keeps, at every key of `source`, the value of its last occurrence there. -/
theorem mergeProviderAttributes_lookup {target source r : List (String × AttrType)}
    (h : mergeProviderAttributes target source = .ok r) :
    ∀ key, (source.lookup key).isSome → r.lookup key = source.reverse.lookup key := by
  unfold mergeProviderAttributes at h
  have := foldlM_ok_induction (P := fun acc pre => ∀ key, (pre.lookup key).isSome →
      acc.lookup key = pre.reverse.lookup key)
    source (by simp)
    (fun acc pre x acc' hP hs => by
      obtain ⟨name, attr⟩ := x
      have hacc' : acc' = insertKey name attr acc := by
        simp only at hs
        split at hs
        · split at hs
          · simp only [Except.ok.injEq] at hs; exact hs.symm
          · exact absurd hs (by simp)
        · simp only [Except.ok.injEq] at hs; exact hs.symm
      subst hacc'
      intro key hkey
      simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
        List.singleton_append, lookup_cons_eq, lookup_insertKey]
      by_cases hk : key = name
      · simp [hk]
      · simp only [hk, if_false]
        apply hP key
        simpa [List.lookup_append, lookup_cons_eq, hk] using hkey) h
  exact this

theorem mem_providerTargets {fields : List ProviderField} {t : String × String} :
    t ∈ providerTargets fields ↔ ∃ p ∈ fields, t ∈ p.targetActions := by
  simp [providerTargets, List.mem_eraseDups, List.mem_mergeSort, List.mem_flatMap]

theorem mem_targetNamespaces {targets : List (String × String)} {nsName id : String}
    (h : (nsName, id) ∈ targets) : nsName ∈ targetNamespaces targets := by
  simp only [targetNamespaces, List.mem_eraseDups, List.mem_mergeSort, List.mem_map]
  exact ⟨(nsName, id), h, rfl⟩

/-- The common type the action's `providers` attribute references, in the result of the provider
pass: a record of every provider field, each with the type of its last declaration in the text
`providerTypeText` (there is one), with the builtin names in `ds` pinned to `__cedar::`
(`pinBuiltinAttrs`), plus those of earlier lowerings. -/
def SharedTypeHolds (f' : Fragment) (k : Option String) (S : String)
    (newAttrs : List (String × AttrType)) : Prop :=
  ∃ c allAttrs ds, commonTypeAt f' k S = some c ∧ c.ty = .record allAttrs false ∧
    ∀ key, (newAttrs.lookup key).isSome →
      allAttrs.lookup key = (pinBuiltinAttrs ds newAttrs).reverse.lookup key

/-- One attribute with its builtin names pinned. -/
def pinAttr (ds : List String) (a : AttrType) : AttrType :=
  ⟨pinBuiltinNames ds a.ty, a.required, a.annotations⟩

/-- Pinning the builtin names of a record's attributes keeps their names, in order. -/
theorem pinBuiltinAttrs_eq_map (ds : List String) : (attrs : List (String × AttrType)) →
    pinBuiltinAttrs ds attrs = attrs.map fun p => (p.1, pinAttr ds p.2)
  | [] => rfl
  | (k, ⟨t, req, anns⟩) :: rest => by
    simp only [pinBuiltinAttrs, List.map_cons, pinBuiltinAttrs_eq_map ds rest, pinAttr]

theorem lookup_map_snd {α β : Type} (g : α → β) : (l : List (String × α)) → (key : String) →
    (l.map fun p => (p.1, g p.2)).lookup key = (l.lookup key).map g
  | [], _ => rfl
  | (k, a) :: rest, key => by
    simp only [List.map_cons, List.lookup_cons]
    split <;> simp_all [lookup_map_snd g rest key]

/-- A key's attribute after pinning is the pinned attribute. -/
theorem lookup_pinBuiltinAttrs (ds : List String) (attrs : List (String × AttrType))
    (key : String) : (pinBuiltinAttrs ds attrs).lookup key = (attrs.lookup key).map (pinAttr ds) := by
  rw [pinBuiltinAttrs_eq_map]
  exact lookup_map_snd (pinAttr ds) attrs key

theorem pinBuiltinAttrs_reverse (ds : List String) (attrs : List (String × AttrType)) :
    (pinBuiltinAttrs ds attrs).reverse = pinBuiltinAttrs ds attrs.reverse := by
  rw [pinBuiltinAttrs_eq_map, pinBuiltinAttrs_eq_map, List.map_reverse]

theorem lookup_isSome_pinBuiltinAttrs (ds : List String) (attrs : List (String × AttrType))
    (key : String) : ((pinBuiltinAttrs ds attrs).lookup key).isSome = (attrs.lookup key).isSome := by
  rw [lookup_pinBuiltinAttrs]; cases attrs.lookup key <;> rfl

/-- **The provider pass** gives an inline context of a target action the attribute `providers`,
a reference to the namespace's shared provider type, which holds every provider field; it keeps
every other attribute, and leaves the contexts of other actions as they are. -/
theorem addProviderContextFields_contextAt {f f' : Fragment} {fields : List ProviderField}
    {nsName id : String} {k : Option String} {attrs : List (String × AttrType)} {add : Bool}
    (h : addProviderContextFields f fields = .ok f') (hk : nsKey nsName = .ok k)
    (hc : contextAt f k id = some (.record attrs add)) :
    ∃ attrs', contextAt f' k id = some (.record attrs' add) ∧
      if (nsName, id) ∈ providerTargets fields then
        ∃ S newAttrs, synthesizedAttrs fields = .ok newAttrs ∧ WithProviders attrs attrs' nsName S ∧
          SharedTypeHolds f' k S newAttrs
      else attrs' = attrs := by
  unfold addProviderContextFields at h
  split at h
  · rename_i hempty
    simp only [Except.ok.injEq] at h; subst h
    refine ⟨attrs, hc, ?_⟩
    have : (nsName, id) ∉ providerTargets fields := by
      simp [mem_providerTargets, List.isEmpty_iff.mp hempty]
    simp [this]
  · simp only at h
    split at h
    · rename_i hempty
      simp only [Except.ok.injEq] at h; subst h
      refine ⟨attrs, hc, ?_⟩
      have : (nsName, id) ∉ providerTargets fields := by
        rw [List.isEmpty_iff.mp hempty]; simp
      simp [this]
    · obtain ⟨f1, hf1, h⟩ := bind_eq_ok.mp h
      obtain ⟨newAttrs, hnew, h⟩ := bind_eq_ok.mp h
      obtain ⟨⟨existingIds, existingAttrs⟩, _, h⟩ := bind_eq_ok.mp h
      simp only at h
      obtain ⟨_, _, h⟩ := bind_eq_ok.mp h
      obtain ⟨sharedIds, hids, h⟩ := bind_eq_ok.mp h
      obtain ⟨allAttrs0, _, h⟩ := bind_eq_ok.mp h
      obtain ⟨allAttrs, hmerge, h⟩ := bind_eq_ok.mp h
      obtain ⟨out, hout, hrefs⟩ := bind_eq_ok.mp h
      have hc1 := inlineSelectedContexts_contextAt_record hf1 hc
      have hcout : contextAt out k id = some (.record attrs add) := by
        rw [writeSharedTypes_contextAt hout]; exact hc1
      obtain ⟨attrs', hc', hinv⟩ := insertProviderReferences_contextAt hrefs hk hcout
      refine ⟨attrs', hc', ?_⟩
      split
      · rename_i hmem
        rw [if_pos hmem] at hinv
        obtain ⟨sid, hsid⟩ := assignSharedIds_lookup hids nsName (mem_targetNamespaces hmem)
        have hS : sharedNameOf sharedIds nsName = sid := by simp [sharedNameOf, hsid]
        rw [hS] at hinv
        refine ⟨sid, newAttrs, hnew, hinv, ?_⟩
        have hmemIds : (nsName, sid) ∈ sharedIds := by
          obtain ⟨l₁, l₂, rfl, _⟩ := List.lookup_eq_some_iff.mp hsid
          simp
        obtain ⟨c, hc, hcty⟩ := writeSharedTypes_commonTypeAt hout nsName sid k hmemIds hk
        refine ⟨c, allAttrs, declaredTypeNames f1, ?_, hcty, fun key hkey => ?_⟩
        rotate_left
        · rw [← lookup_isSome_pinBuiltinAttrs (declaredTypeNames f1)] at hkey
          exact mergeProviderAttributes_lookup hmerge key hkey
        rw [← hc]
        -- the references leave the common types as they are
        exact foldlM_ok_invariant (P := fun acc => commonTypeAt acc k sid = commonTypeAt out k sid)
          (providerTargets fields) rfl
          (fun acc x acc' _ hP hs => by
            obtain ⟨ns2, id2⟩ := x
            obtain ⟨k2, a, _, _, _, _, _, ha, _, _, _, rfl⟩ := insertProviderReference_ok hs
            obtain ⟨nd, hnd, _⟩ := getNs_of_actionAt ha
            rw [commonTypeAt_setAction hnd]; exact hP) hrefs
      · rename_i hmem
        rw [if_neg hmem] at hinv; exact hinv

/-! ## The three passes together -/

theorem withPrefix_ok {α : Type} {pre : String} {r : Except String α} {a : α}
    (h : withPrefix pre r = .ok a) : r = .ok a := by
  unfold withPrefix at h
  split at h
  · simpa using h
  · exact absurd h (by simp)

/-- **What augmentation does to an inline context.** For an action whose context the action
schema declares as an inline record `attrs`, the augmented context is a record `attrs'` such
that: when no provider field targets the action, `attrs'` is `attrs` with the `Bool` of each
temporal field targeting the action; when one does, it is that record with, besides, the
attribute `providers` referencing the namespace's shared provider type, which holds every
provider field. -/
theorem augmentSchema_context {F F' : Fragment} {decls : Option ProviderDecls.Declarations}
    {enums : List String} {CF : List ContextField} {PF : List ProviderField}
    {nsName id : String} {k : Option String} {attrs : List (String × AttrType)} {add : Bool}
    (h : augmentSchema F decls enums CF PF = .ok F') (hk : nsKey nsName = .ok k)
    (hc : contextAt F k id = some (.record attrs add)) :
    ∃ attrs', contextAt F' k id = some (.record attrs' add) ∧
      if (nsName, id) ∈ providerTargets PF then
        ∃ attrsT S newAttrs, ExtendsBy attrs attrsT (hoistedAt CF nsName id) ∧
          synthesizedAttrs PF = .ok newAttrs ∧ WithProviders attrsT attrs' nsName S ∧
          SharedTypeHolds F' k S newAttrs
      else ExtendsBy attrs attrs' (hoistedAt CF nsName id) := by
  unfold augmentSchema at h
  split at h
  · exact absurd h (by simp)
  · obtain ⟨F1, hF1, h⟩ := bind_eq_ok.mp h
    have hc1 : contextAt F1 k id = some (.record attrs add) := by
      unfold enumPass at hF1
      split at hF1
      · rw [addProviderEntityTypes_contextAt (withPrefix_ok hF1)]; exact hc
      · simp only [Except.ok.injEq] at hF1; subst hF1; exact hc
    obtain ⟨F2, hF2, h⟩ := bind_eq_ok.mp h
    obtain ⟨attrsT, hc2, hext⟩ := addBoolContextFields_contextAt (withPrefix_ok hF2) hk hc1
    obtain ⟨attrs', hc', hP⟩ := addProviderContextFields_contextAt (withPrefix_ok h) hk hc2
    refine ⟨attrs', hc', ?_⟩
    split
    · rename_i hmem
      rw [if_pos hmem] at hP
      obtain ⟨S, newAttrs, hnew, hwith, hshared⟩ := hP
      exact ⟨attrsT, S, newAttrs, hext, hnew, hwith, hshared⟩
    · rename_i hmem
      rw [if_neg hmem] at hP
      subst hP; exact hext

end Dogwood.Frontend.Augment
