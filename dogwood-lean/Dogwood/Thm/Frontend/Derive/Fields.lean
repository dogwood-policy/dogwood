import Dogwood.Thm.Frontend.Derive.Events

/-!
# The field trees and pins derivation produces

* **Field trees are maps** (`derive_fields_ordered`): at every level of a derived event's field
  tree the names strictly increase, as in the crate's `BTreeMap`s; so **each signature's fields
  are distinct** (`derive_leafFields_nodup`).
* **An event's pins are its declaration's** (`derive_pins`): the pins of the declaration's field
  specs, with their full paths (`specsPins`), the same on every action.
* **Every pin names a declared field of its signature** (`derive_pin_declared`), provided no
  record field is pinned, which the DSL's parser guarantees (`PinsOnLeaves`). Without that
  proviso a pin can name a group (`derive_pin_on_record`).
-/

namespace Dogwood.Thm.Frontend.Derivation

open Dogwood.Frontend Dogwood.Frontend.Derive Dogwood.Frontend.CedarSchema
open Dogwood.Frontend.EventSchemaDsl

/-! ## Field maps -/

mutual

/-- A field forest is ordered: its names strictly increase, and each group is ordered. -/
def Ordered : List (String × DerivedFieldNode) → Prop
  | [] => True
  | (k, v) :: rest => (∀ p ∈ rest, k < p.1) ∧ NodeOrdered v ∧ Ordered rest

/-- A field node is ordered: a leaf, or an ordered group. -/
def NodeOrdered : DerivedFieldNode → Prop
  | .leaf _ => True
  | .group ms => Ordered ms

end

/-- The node at a path under a field node. -/
def nodeAt : DerivedFieldNode → List String → Option DerivedFieldNode
  | n, [] => some n
  | .leaf _, _ :: _ => none
  | .group ms, k :: rest =>
    match ms.lookup k with
    | some n => nodeAt n rest
    | none => none

theorem mem_insertKey {α : Type} {k : String} {v : α} {ms : List (String × α)}
    {p : String × α} (h : p ∈ insertKey k v ms) : p = (k, v) ∨ p ∈ ms := by
  induction ms with
  | nil => simp [insertKey] at h; exact .inl h
  | cons q rest ih =>
    obtain ⟨k', v'⟩ := q
    simp only [insertKey] at h
    split at h
    · simp only [List.mem_cons] at h
      rcases h with h | h | h
      · exact .inl h
      · exact .inr (by simp [h])
      · exact .inr (by simp [h])
    · split at h
      · simp only [List.mem_cons] at h
        rcases h with h | h
        · exact .inl h
        · exact .inr (by simp [h])
      · simp only [List.mem_cons] at h
        rcases h with h | h
        · exact .inr (by simp [h])
        · rcases ih h with h | h
          · exact .inl h
          · exact .inr (by simp [h])

theorem lookup_insertKey_self {α : Type} (k : String) (v : α) (ms : List (String × α)) :
    (insertKey k v ms).lookup k = some v := by
  induction ms with
  | nil => simp [insertKey]
  | cons q rest ih =>
    obtain ⟨k', v'⟩ := q
    simp only [insertKey]
    split
    · simp
    · split
      · simp
      · rename_i _ hne
        simp [List.lookup_cons, beq_false_of_ne hne, ih]

theorem lookup_insertKey_ne {α : Type} {k k' : String} (v : α) (ms : List (String × α))
    (hne : k' ≠ k) : (insertKey k v ms).lookup k' = ms.lookup k' := by
  have hb : (k' == k) = false := beq_false_of_ne hne
  induction ms with
  | nil => simp [insertKey, List.lookup_cons, hb]
  | cons q rest ih =>
    obtain ⟨k'', v''⟩ := q
    simp only [insertKey]
    split
    · simp [List.lookup_cons, hb]
    · split
      · rename_i _ heq
        subst heq
        simp [List.lookup_cons, hb]
      · simp only [List.lookup_cons]
        split <;> simp_all

theorem lookup_of_hasKey_false {α : Type} {k : String} {ms : List (String × α)}
    (h : hasKey k ms = false) : ms.lookup k = none := by
  simp only [hasKey, List.any_eq_false, beq_iff_eq] at h
  simp only [List.lookup_eq_none_iff, bne_iff_ne, ne_eq]
  intro p hp heq
  exact h p hp heq.symm

theorem lookup_mem {α : Type} {k : String} {v : α} {ms : List (String × α)}
    (h : ms.lookup k = some v) : (k, v) ∈ ms := by
  obtain ⟨l₁, l₂, rfl, -⟩ := List.lookup_eq_some_iff.mp h
  simp

/-- Inserting a name keeps a forest ordered. -/
theorem insertKey_ordered {k : String} {v : DerivedFieldNode}
    {ms : List (String × DerivedFieldNode)}
    (hms : Ordered ms) (hv : NodeOrdered v) : Ordered (insertKey k v ms) := by
  induction ms with
  | nil => simp [insertKey, Ordered, hv]
  | cons q rest ih =>
    obtain ⟨k', v'⟩ := q
    simp only [Ordered] at hms
    obtain ⟨hlt, hv', hrest⟩ := hms
    simp only [insertKey]
    split
    · rename_i hk
      simp only [Ordered, List.mem_cons, forall_eq_or_imp]
      refine ⟨⟨hk, fun p hp => Cedar.Data.StrictLT.transitive _ _ _ hk (hlt p hp)⟩, hv, hlt, hv',
        hrest⟩
    · split
      · rename_i heq
        subst heq
        exact ⟨hlt, hv, hrest⟩
      · rename_i hk hne
        refine ⟨?_, hv', ih hrest⟩
        intro p hp
        rcases mem_insertKey hp with rfl | hp
        · rcases Cedar.Data.StrictLT.connected k k' hne with h | h
          · exact absurd h hk
          · exact h
        · exact hlt p hp

/-- An ordered forest's names are distinct. -/
theorem Ordered.nodup : ∀ {ms : List (String × DerivedFieldNode)}, Ordered ms →
    (ms.map (·.1)).Nodup
  | [], _ => by simp
  | (k, v) :: rest, h => by
    simp only [Ordered] at h
    obtain ⟨hlt, -, hrest⟩ := h
    simp only [List.map_cons, List.nodup_cons, List.mem_map]
    refine ⟨?_, Ordered.nodup hrest⟩
    rintro ⟨p, hp, heq⟩
    exact Cedar.Data.StrictLT.irreflexive k (heq ▸ hlt p hp)

/-! ## Leaves -/

theorem leaves_nil (pfx : List String) : DerivedFieldNode.leaves pfx [] = [] := by
  simp [DerivedFieldNode.leaves]

theorem leaves_leaf (pfx : List String) (n : String) (t : FieldType)
    (rest : List (String × DerivedFieldNode)) :
    DerivedFieldNode.leaves pfx ((n, .leaf t) :: rest) =
      (pfx ++ [n], t) :: DerivedFieldNode.leaves pfx rest := by
  simp [DerivedFieldNode.leaves]

theorem leaves_group (pfx : List String) (n : String) (ms rest : List (String × DerivedFieldNode)) :
    DerivedFieldNode.leaves pfx ((n, .group ms) :: rest) =
      DerivedFieldNode.leaves (pfx ++ [n]) ms ++ DerivedFieldNode.leaves pfx rest := by
  simp [DerivedFieldNode.leaves]

/-- Every leaf path under a forest starts with the prefix and one of the forest's names. -/
theorem leaves_prefix : ∀ (pfx : List String) (ms : List (String × DerivedFieldNode))
    (q : List String × FieldType), q ∈ DerivedFieldNode.leaves pfx ms →
    ∃ n r, n ∈ ms.map (·.1) ∧ q.1 = pfx ++ n :: r
  | _, [], q, h => by simp [leaves_nil] at h
  | pfx, (n, .leaf t) :: rest, q, h => by
    rw [leaves_leaf] at h
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨n, [], by simp, by simp⟩
    · obtain ⟨n', r, hn', hq⟩ := leaves_prefix pfx rest q h
      exact ⟨n', r, by simp [hn'], hq⟩
  | pfx, (n, .group ms) :: rest, q, h => by
    rw [leaves_group] at h
    rcases List.mem_append.mp h with h | h
    · obtain ⟨n', r, -, hq⟩ := leaves_prefix (pfx ++ [n]) ms q h
      exact ⟨n, n' :: r, by simp, by simp [hq]⟩
    · obtain ⟨n', r, hn', hq⟩ := leaves_prefix pfx rest q h
      exact ⟨n', r, by simp [hn'], hq⟩

/-- The leaf paths under an ordered forest are distinct. -/
theorem leaves_nodup : ∀ (pfx : List String) (ms : List (String × DerivedFieldNode)),
    Ordered ms → ((DerivedFieldNode.leaves pfx ms).map (·.1)).Nodup
  | _, [], _ => by simp [leaves_nil]
  | pfx, (n, .leaf t) :: rest, h => by
    simp only [Ordered] at h
    obtain ⟨hlt, -, hrest⟩ := h
    rw [leaves_leaf]
    simp only [List.map_cons, List.nodup_cons, List.mem_map]
    refine ⟨?_, leaves_nodup pfx rest hrest⟩
    rintro ⟨q, hq, heq⟩
    obtain ⟨n', r, hn', hq'⟩ := leaves_prefix pfx rest q hq
    rw [hq'] at heq
    simp only [List.append_cancel_left_eq, List.cons.injEq] at heq
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hn'
    exact Cedar.Data.StrictLT.irreflexive n (heq.1 ▸ hlt p hp)
  | pfx, (n, .group ms) :: rest, h => by
    simp only [Ordered, NodeOrdered] at h
    obtain ⟨hlt, hms, hrest⟩ := h
    rw [leaves_group, List.map_append, List.nodup_append]
    refine ⟨leaves_nodup (pfx ++ [n]) ms hms, leaves_nodup pfx rest hrest, ?_⟩
    intro a ha b hb heq
    obtain ⟨qa, hqa, rfl⟩ := List.mem_map.mp ha
    obtain ⟨qb, hqb, rfl⟩ := List.mem_map.mp hb
    obtain ⟨_, ra, -, hra⟩ := leaves_prefix (pfx ++ [n]) ms qa hqa
    obtain ⟨n', rb, hn', hrb⟩ := leaves_prefix pfx rest qb hqb
    rw [hra, hrb] at heq
    simp only [List.append_assoc, List.singleton_append, List.append_cancel_left_eq,
      List.cons.injEq] at heq
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hn'
    exact Cedar.Data.StrictLT.irreflexive n (heq.1 ▸ hlt p hp)

/-- A member's leaves are among the forest's. -/
theorem leaves_mem_leaf {pfx : List String} {ms : List (String × DerivedFieldNode)} {n : String}
    {t : FieldType} (h : (n, .leaf t) ∈ ms) : (pfx ++ [n], t) ∈ DerivedFieldNode.leaves pfx ms := by
  induction ms with
  | nil => simp at h
  | cons q rest ih =>
    obtain ⟨k, v⟩ := q
    rcases List.mem_cons.mp h with h' | h'
    · simp only [Prod.mk.injEq] at h'
      obtain ⟨rfl, rfl⟩ := h'
      rw [leaves_leaf]; simp
    · cases v with
      | leaf t' => rw [leaves_leaf]; exact List.mem_cons_of_mem _ (ih h')
      | group ms' => rw [leaves_group]; exact List.mem_append_right _ (ih h')

theorem leaves_mem_group {pfx : List String} {ms : List (String × DerivedFieldNode)} {n : String}
    {ms' : List (String × DerivedFieldNode)} (h : (n, .group ms') ∈ ms) {q}
    (hq : q ∈ DerivedFieldNode.leaves (pfx ++ [n]) ms') : q ∈ DerivedFieldNode.leaves pfx ms := by
  induction ms with
  | nil => simp at h
  | cons p rest ih =>
    obtain ⟨k, v⟩ := p
    rcases List.mem_cons.mp h with h' | h'
    · simp only [Prod.mk.injEq] at h'
      obtain ⟨rfl, rfl⟩ := h'
      rw [leaves_group]; exact List.mem_append_left _ hq
    · cases v with
      | leaf t' => rw [leaves_leaf]; exact List.mem_cons_of_mem _ (ih h')
      | group ms'' => rw [leaves_group]; exact List.mem_append_right _ (ih h')

/-- A leaf at a path under a forest is one of its leaves. -/
theorem nodeAt_leaf_mem : ∀ (rel : List String) (pfx : List String)
    (ms : List (String × DerivedFieldNode)) (t : FieldType),
    nodeAt (.group ms) rel = some (.leaf t) → (pfx ++ rel, t) ∈ DerivedFieldNode.leaves pfx ms
  | [], _, _, _, h => by simp [nodeAt] at h
  | k :: rest, pfx, ms, t, h => by
    simp only [nodeAt] at h
    split at h
    · rename_i n hn
      have hmem := lookup_mem hn
      cases rest with
      | nil =>
        simp only [nodeAt, Option.some.injEq] at h
        subst h
        exact leaves_mem_leaf hmem
      | cons k' rest' =>
        cases n with
        | leaf _ => simp [nodeAt] at h
        | group ms' =>
          have := nodeAt_leaf_mem (k' :: rest') (pfx ++ [k]) ms' t h
          simp only [List.append_assoc, List.singleton_append] at this
          exact leaves_mem_group hmem this
    · simp at h

/-- A leaf at a path is a leaf field of the event. -/
theorem leafFields_of_nodeAt {e : DerivedEvent} {rel : List String} {t : FieldType}
    (h : nodeAt (.group e.fields) rel = some (.leaf t)) : (rel, t) ∈ e.leafFields := by
  unfold DerivedEvent.leafFields
  rw [List.mem_mergeSort]
  simpa using nodeAt_leaf_mem rel [] e.fields t h

/-! ## Spliced groups -/

theorem attrsToNodes_ordered {node : SchemaType → Nat → Except String (DerivedFieldNode × Nat)}
    (hnode : ∀ t n r, node t n = .ok r → NodeOrdered r.1) :
    ∀ (attrs : List (String × AttrType)) (n : Nat) (acc : List (String × DerivedFieldNode)) r,
      Ordered acc → attrsToNodes node attrs n acc = .ok r → Ordered r.1
  | [], _, acc, r, hacc, h => by
    simp [attrsToNodes, pure, Except.pure] at h; subst h; exact hacc
  | (k, a) :: rest, n, acc, r, hacc, h => by
    simp only [attrsToNodes, bind, Except.bind] at h
    cases hn : node a.ty n with
    | error _ => simp [hn] at h
    | ok p =>
      simp only [hn] at h
      exact attrsToNodes_ordered hnode rest p.2 _ r (insertKey_ordered hacc (hnode _ _ _ hn)) h

theorem typeToNodeF_ordered {f : Fragment} : ∀ (fuel : Nat) (ty : SchemaType)
    (home : Option String) (n : Nat) r, typeToNodeF f fuel ty home n = .ok r → NodeOrdered r.1
  | 0, _, _, _, _, h => by simp [typeToNodeF] at h
  | fuel + 1, ty, home, n, r, h => by
    simp only [typeToNodeF] at h
    split at h
    · simp at h
    · simp only [bind, Except.bind] at h
      cases hr : resolveToRecordF f (fuel + 1) ty home with
      | error _ => simp [hr] at h
      | ok o =>
        simp only [hr] at h
        cases o with
        | none => simp [pure, Except.pure] at h; subst h; simp [NodeOrdered]
        | some ar =>
          obtain ⟨attrs, recNs⟩ := ar
          simp only at h
          cases ha : attrsToNodes (fun t n => typeToNodeF f fuel t recNs n) attrs (n + 1) [] with
          | error _ => simp [ha] at h
          | ok p =>
            simp [ha, pure, Except.pure] at h
            subst h
            exact attrsToNodes_ordered (fun t n r h => typeToNodeF_ordered fuel t recNs n r h)
              attrs (n + 1) [] p (by simp [Ordered]) ha

theorem contextSubrecord_ordered {f : Fragment} {a : ActionDef} {home : Option String}
    {attr : String} {ms : List (String × DerivedFieldNode)}
    (h : contextSubrecord f a home attr = .ok ms) : Ordered ms := by
  unfold contextSubrecord at h
  split at h
  · simp [pure, Except.pure] at h; subst h; simp [Ordered]
  · simp only [bind, Except.bind] at h
    split at h
    · simp at h
    · split at h
      · simp [pure, Except.pure] at h; subst h; simp [Ordered]
      · split at h
        · simp [pure, Except.pure] at h; subst h; simp [Ordered]
        · split at h
          · simp at h
          · rename_i r hr
            split at h
            · rename_i members hm
              simp [pure, Except.pure] at h; subst h
              have := typeToNodeF_ordered _ _ _ _ _ hr
              simpa [hm, NodeOrdered] using this
            · simp [pure, Except.pure] at h; subst h; simp [Ordered]

/-! ## Deriving field specs -/

/-- The pin a named field at `path` declares, if any. -/
def ownPin (path : List String) : Option PinValue → List Pin
  | some pv => [{ fieldPath := path, contextPath := pv.contextPath, root := pv.root }]
  | none => []

mutual

/-- The pins of field specs at `pfx`, with their full paths, in declaration order (a record
field's own pin after those of its members). -/
def specsPins (pfx : List String) : List FieldSpec → List Pin
  | [] => []
  | s :: rest => specPins pfx s ++ specsPins pfx rest

/-- The pins of one field spec at `pfx`. -/
def specPins (pfx : List String) : FieldSpec → List Pin
  | .spread _ _ => []
  | .named name ty pin _ =>
    typePins (pfx ++ [name]) ty ++ ownPin (pfx ++ [name]) pin

/-- The pins of a field type at `path`: a record's members'. -/
def typePins (path : List String) : TypeExpr → List Pin
  | .record inner => specsPins path inner
  | _ => []

end

/-- Whether a field type is a record. -/
def isRecordType : TypeExpr → Bool
  | .record _ => true
  | _ => false

mutual

/-- No field spec pins a record. -/
def specsPinLeaves : List FieldSpec → Bool
  | [] => true
  | s :: rest => specPinLeaves s && specsPinLeaves rest

def specPinLeaves : FieldSpec → Bool
  | .spread _ _ => true
  | .named _ ty pin _ => (pin.isNone || !isRecordType ty) && typePinLeaves ty

def typePinLeaves : TypeExpr → Bool
  | .record inner => specsPinLeaves inner
  | _ => true

end

/-- No declaration pins a record field: the DSL parser's guarantee. -/
def PinsOnLeaves (dsl : EventSchemaDsl.EventSchema) : Prop :=
  ∀ d ∈ dsl.decls, specsPinLeaves d.fields = true

/-- What deriving field specs at `pfx` does to the accumulator, `new` being the specs' pins and
`leaves` whether none of them pins a record: it appends the pins, keeps the field map ordered,
keeps every name it had, and each new pin names a leaf of the result. -/
def StepInv (pfx : List String) (new : List Pin) (leaves : Bool) (acc acc' : Acc) : Prop :=
  acc'.pins = acc.pins ++ new ∧ (Ordered acc.fields → Ordered acc'.fields) ∧
  (∀ k v, acc.fields.lookup k = some v → acc'.fields.lookup k = some v) ∧
  (leaves = true → ∀ p ∈ new, ∃ rel t, p.fieldPath = pfx ++ rel ∧
    nodeAt (.group acc'.fields) rel = some (.leaf t))

/-- What deriving a field's type at `path` produces: the pins appended, an ordered node, a leaf
for each new pin, and a leaf unless the type is a record. -/
def TypeInv (path : List String) (ty : TypeExpr) (pins pins' : List Pin) (node : DerivedFieldNode) :
    Prop :=
  pins' = pins ++ typePins path ty ∧ NodeOrdered node ∧
  (typePinLeaves ty = true → ∀ p ∈ typePins path ty, ∃ rel t, p.fieldPath = path ++ rel ∧
    nodeAt node rel = some (.leaf t)) ∧
  (isRecordType ty = false → ∃ t, node = .leaf t)

theorem nodeAt_group_mono {ms ms' : List (String × DerivedFieldNode)}
    (h : ∀ k v, ms.lookup k = some v → ms'.lookup k = some v) {rel : List String} {t : FieldType}
    (hn : nodeAt (.group ms) rel = some (.leaf t)) : nodeAt (.group ms') rel = some (.leaf t) := by
  cases rel with
  | nil => simp [nodeAt] at hn
  | cons k rest =>
    simp only [nodeAt] at hn ⊢
    split at hn
    · rename_i n hl
      rw [h k n hl]
      exact hn
    · simp at hn

theorem deriveSpec_spread_ok {c : Ctx} {pfx : List String} {sel : Selector} {sp : Span}
    {acc acc' : Acc} (h : deriveSpec c pfx (.spread sel sp) acc = .ok acc') :
    ∃ group members, contextSubrecord c.fragment c.action c.home group = .ok members ∧
      hasKey group acc.fields = false ∧
      acc' = { acc with fields := insertKey group (.group members) acc.fields,
                        spreadNames := acc.spreadNames ++ [group] } := by
  cases sel <;> simp only [deriveSpec, bind, Except.bind, pure, Except.pure] at h
  · cases hc : contextSubrecord c.fragment c.action c.home "input" with
    | error _ => simp [hc] at h
    | ok ms =>
      simp only [hc] at h
      split at h
      · simp at h
      · rename_i hk
        simp only [Except.ok.injEq] at h
        exact ⟨"input", ms, hc, by simpa using hk, h.symm⟩
  · cases hc : contextSubrecord c.fragment c.action c.home "output" with
    | error _ => simp [hc] at h
    | ok ms =>
      simp only [hc] at h
      split at h
      · simp at h
      · rename_i hk
        simp only [Except.ok.injEq] at h
        exact ⟨"output", ms, hc, by simpa using hk, h.symm⟩
  · simp at h
  · simp at h

theorem deriveSpec_named_ok {c : Ctx} {pfx : List String} {name : String} {ty : TypeExpr}
    {pin : Option PinValue} {sp : Span} {acc acc' : Acc}
    (h : deriveSpec c pfx (.named name ty pin sp) acc = .ok acc') :
    ∃ node pins, deriveType c (pfx ++ [name]) ty acc.pins = .ok (node, pins) ∧
      hasKey name acc.fields = false ∧
      acc' = { acc with fields := insertKey name node acc.fields,
                        pins := pins ++ ownPin (pfx ++ [name]) pin } := by
  simp only [deriveSpec, bind, Except.bind, pure, Except.pure] at h
  cases ht : deriveType c (pfx ++ [name]) ty acc.pins with
  | error _ => simp [ht] at h
  | ok r =>
    obtain ⟨node, pins⟩ := r
    simp only [ht] at h
    split at h
    · split at h <;> simp at h
    · rename_i hk
      simp only [Except.ok.injEq] at h
      refine ⟨node, pins, rfl, by simpa using hk, ?_⟩
      rw [← h]
      cases pin <;> simp [ownPin]

mutual

theorem deriveSpecs_inv : ∀ (c : Ctx) (pfx : List String) (specs : List FieldSpec) (acc acc' : Acc),
    deriveSpecs c pfx specs acc = .ok acc' →
      StepInv pfx (specsPins pfx specs) (specsPinLeaves specs) acc acc'
  | c, pfx, [], acc, acc', h => by
    simp only [deriveSpecs, pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp [StepInv, specsPins]
  | c, pfx, s :: rest, acc, acc', h => by
    simp only [deriveSpecs, bind, Except.bind] at h
    cases h1 : deriveSpec c pfx s acc with
    | error _ => simp [h1] at h
    | ok acc1 =>
      simp only [h1] at h
      obtain ⟨p1, o1, l1, n1⟩ := deriveSpec_inv c pfx s acc acc1 h1
      obtain ⟨p2, o2, l2, n2⟩ := deriveSpecs_inv c pfx rest acc1 acc' h
      refine ⟨by rw [p2, p1, specsPins, List.append_assoc], fun ho => o2 (o1 ho),
        fun k v hk => l2 k v (l1 k v hk), ?_⟩
      intro hl p hp
      simp only [specsPinLeaves, Bool.and_eq_true] at hl
      simp only [specsPins, List.mem_append] at hp
      rcases hp with hp | hp
      · obtain ⟨rel, t, hpath, hnode⟩ := n1 hl.1 p hp
        exact ⟨rel, t, hpath, nodeAt_group_mono l2 hnode⟩
      · exact n2 hl.2 p hp

theorem deriveSpec_inv : ∀ (c : Ctx) (pfx : List String) (s : FieldSpec) (acc acc' : Acc),
    deriveSpec c pfx s acc = .ok acc' → StepInv pfx (specPins pfx s) (specPinLeaves s) acc acc'
  | c, pfx, .spread sel sp, acc, acc', h => by
    obtain ⟨group, members, hc, hk, rfl⟩ := deriveSpec_spread_ok h
    refine ⟨by simp [specPins], fun ho => insertKey_ordered ho (contextSubrecord_ordered hc),
      fun k v hkv => ?_, fun _ p hp => by simp [specPins] at hp⟩
    have hne : k ≠ group := by
      rintro rfl
      rw [lookup_of_hasKey_false hk] at hkv
      cases hkv
    simpa [lookup_insertKey_ne _ _ hne] using hkv
  | c, pfx, .named name ty pin sp, acc, acc', h => by
    obtain ⟨node, pins, ht, hk, rfl⟩ := deriveSpec_named_ok h
    obtain ⟨tp, to, tl, tleaf⟩ := deriveType_inv c (pfx ++ [name]) ty acc.pins (node, pins) ht
    simp only at tp to tl tleaf
    refine ⟨?_, fun ho => insertKey_ordered ho to, fun k v hkv => ?_, ?_⟩
    · simp only [specPins, tp, List.append_assoc]
    · have hne : k ≠ name := by
        rintro rfl
        rw [lookup_of_hasKey_false hk] at hkv
        cases hkv
      simpa [lookup_insertKey_ne _ _ hne] using hkv
    · intro hl p hp
      simp only [specPinLeaves, Bool.and_eq_true, Bool.or_eq_true, Option.isNone_iff_eq_none,
        Bool.not_eq_true'] at hl
      obtain ⟨hpin, htl⟩ := hl
      have hat : ∀ rel t, nodeAt node rel = some (.leaf t) →
          nodeAt (.group (insertKey name node acc.fields)) (name :: rel) = some (.leaf t) := by
        intro rel t hn
        simp only [nodeAt, lookup_insertKey_self]
        exact hn
      simp only [specPins, List.mem_append] at hp
      rcases hp with hp | hp
      · obtain ⟨rel, t, hpath, hn⟩ := tl htl p hp
        exact ⟨name :: rel, t, by simp [hpath], hat rel t hn⟩
      · cases pin with
        | none => simp [ownPin] at hp
        | some pv =>
          simp only [ownPin, List.mem_singleton] at hp
          subst hp
          rcases hpin with h' | h'
          · cases h'
          · obtain ⟨t, rfl⟩ := tleaf h'
            exact ⟨[name], t, by simp, by simp [nodeAt, lookup_insertKey_self]⟩

theorem deriveType_inv : ∀ (c : Ctx) (path : List String) (ty : TypeExpr) (pins : List Pin)
    (r : DerivedFieldNode × List Pin), deriveType c path ty pins = .ok r →
      TypeInv path ty pins r.2 r.1
  | c, path, .selector .principalType, pins, r, h => by
    simp only [deriveType, pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp [TypeInv, typePins, NodeOrdered]
  | c, path, .selector .resourceType, pins, r, h => by
    simp only [deriveType, pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp [TypeInv, typePins, NodeOrdered]
  | c, path, .selector .inputs, pins, r, h => by simp [deriveType] at h
  | c, path, .selector .outputs, pins, r, h => by simp [deriveType] at h
  | c, path, .concrete p, pins, r, h => by
    simp only [deriveType, pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp [TypeInv, typePins, NodeOrdered]
  | c, path, .record inner, pins, r, h => by
    simp only [deriveType, bind, Except.bind] at h
    cases hs : deriveSpecs c path inner ⟨[], [], pins⟩ with
    | error _ => simp [hs] at h
    | ok acc =>
      simp only [hs, pure, Except.pure, Except.ok.injEq] at h
      subst h
      obtain ⟨sp, so, -, sn⟩ := deriveSpecs_inv c path inner ⟨[], [], pins⟩ acc hs
      exact ⟨by simpa [typePins] using sp, so (by simp [Ordered]),
        fun hl p hp => sn (by simpa [typePinLeaves] using hl) p (by simpa [typePins] using hp),
        fun hr => by simp [isRecordType] at hr⟩

end

/-! ## The derived events -/

variable {dsl : EventSchemaDsl.EventSchema} {f : Fragment} {d : DerivedEventSchema}
  {e : DerivedEvent}

/-- **Field trees are maps**: at every level the names strictly increase. -/
theorem derive_fields_ordered (h : derive dsl f = .ok d) (he : e ∈ d.events) :
    Ordered e.fields := by
  obtain ⟨_, _, -, _, _, -, _, -, hone⟩ := derive_event_mem h he
  obtain ⟨-, -, -, -, acc, hs, hf, -⟩ := deriveOne_ok hone
  rw [hf]
  exact (deriveSpecs_inv _ _ _ _ _ hs).2.1 (by simp [Ordered])

/-- **Each signature's fields are distinct.** -/
theorem derive_leafFields_nodup (h : derive dsl f = .ok d) (he : e ∈ d.events) :
    (e.leafFields.map (·.1)).Nodup := by
  have := leaves_nodup [] e.fields (derive_fields_ordered h he)
  unfold DerivedEvent.leafFields
  exact ((List.mergeSort_perm _ _).map _).nodup_iff.mpr this

/-- **An event's pins are its declaration's**, with their full paths, whatever the action. -/
theorem derive_pins (h : derive dsl f = .ok d) (he : e ∈ d.events) :
    ∃ decl ∈ dsl.decls, e.kind = decl.kind ∧ e.pins = specsPins [] decl.fields := by
  obtain ⟨_, _, -, _, _, -, decl, hdecl, hone⟩ := derive_event_mem h he
  obtain ⟨-, -, hk, -, acc, hs, -, hp⟩ := deriveOne_ok hone
  refine ⟨decl, hdecl, hk, ?_⟩
  rw [hp, (deriveSpecs_inv _ _ _ _ _ hs).1]
  rfl

/-- **Every pin names a declared field of its signature** (a leaf field), when no record field
is pinned. -/
theorem derive_pin_declared (h : derive dsl f = .ok d) (hpins : PinsOnLeaves dsl)
    (he : e ∈ d.events) : ∀ p ∈ e.pins, ∃ t, (p.fieldPath, t) ∈ e.leafFields := by
  obtain ⟨_, _, -, _, _, -, decl, hdecl, hone⟩ := derive_event_mem h he
  obtain ⟨-, -, -, -, acc, hs, hf, hp⟩ := deriveOne_ok hone
  obtain ⟨hpe, -, -, hn⟩ := deriveSpecs_inv _ _ _ _ _ hs
  intro p hpm
  rw [hp, hpe] at hpm
  obtain ⟨rel, t, hpath, hnode⟩ := hn (hpins decl hdecl) p (by simpa using hpm)
  refine ⟨t, ?_⟩
  rw [hpath, List.nil_append]
  rw [← hf] at hnode
  exact leafFields_of_nodeAt hnode

/-- A DSL that pins a record field, which the parser rejects. -/
def pinnedRecordDsl : EventSchemaDsl.EventSchema where
  maxWindow := none
  decls := [{ span := default, decision := true, binder := "A", kind := "k",
              fields := [.named "r" (.record [.named "x" (.concrete ["String"]) none default])
                (some { contextPath := ["principal"], root := .scope, span := default }) default] }]

/-- **Counterexample**: without `PinsOnLeaves`, a pin can name a group, not a field. -/
theorem derive_pin_on_record :
    ∃ d, derive pinnedRecordDsl oneActionFragment = .ok d ∧ ∃ e ∈ d.events, ∃ p ∈ e.pins,
      ∃ ms, nodeAt (.group e.fields) p.fieldPath = some (.group ms) := by
  refine ⟨_, rfl, _, List.mem_cons_self .., _, List.mem_cons_self ..,
    [("x", .leaf (.cedar "String"))], ?_⟩
  rfl

end Dogwood.Thm.Frontend.Derivation
