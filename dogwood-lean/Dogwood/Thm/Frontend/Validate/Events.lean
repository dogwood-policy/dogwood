import Dogwood.Thm.Frontend.Validate.Interface
import Cedar.Thm.Data.List

namespace Dogwood.Thm.Frontend

open Dogwood.Frontend Dogwood.Frontend.Validate
open Cedar.Validation (CedarType Schema RecordType)

/-! ## Leaf fields -/

mutual

theorem mem_leaves_of_leaf {pre : List String} {t : FieldType} :
    (ms : List (String × DerivedFieldNode)) → {seg : String} → (seg, .leaf t) ∈ ms →
      (pre ++ [seg], t) ∈ DerivedFieldNode.leaves pre ms
  | [], _, h => by cases h
  | (n, node) :: ms, seg, h => by
    rcases List.mem_cons.mp h with h1 | h2
    · simp only [Prod.mk.injEq] at h1; obtain ⟨rfl, rfl⟩ := h1
      simp [DerivedFieldNode.leaves]
    · have ih := mem_leaves_of_leaf (pre := pre) ms h2
      cases node with
      | leaf t' => simp only [DerivedFieldNode.leaves]; exact List.mem_cons_of_mem _ ih
      | group ms' => simp only [DerivedFieldNode.leaves]; exact List.mem_append_right _ ih

end

theorem leaves_sub_of_group {pre : List String} {ms' : List (String × DerivedFieldNode)} :
    (ms : List (String × DerivedFieldNode)) → {seg : String} → (seg, .group ms') ∈ ms →
      ∀ x ∈ DerivedFieldNode.leaves (pre ++ [seg]) ms', x ∈ DerivedFieldNode.leaves pre ms
  | [], _, h => by cases h
  | (n, node) :: ms, seg, h => by
    intro x hx
    rcases List.mem_cons.mp h with h1 | h2
    · simp only [Prod.mk.injEq] at h1; obtain ⟨rfl, rfl⟩ := h1
      simp only [DerivedFieldNode.leaves]; exact List.mem_append_left _ hx
    · have ih := leaves_sub_of_group (pre := pre) ms h2 x hx
      cases node with
      | leaf t' => simp only [DerivedFieldNode.leaves]; exact List.mem_cons_of_mem _ ih
      | group ms'' => simp only [DerivedFieldNode.leaves]; exact List.mem_append_right _ ih

theorem mem_of_lookup_node {L : List (String × DerivedFieldNode)} {a : String} {v : DerivedFieldNode}
    (h : L.lookup a = some v) : (a, v) ∈ L := by
  induction L with
  | nil => simp [List.lookup] at h
  | cons p L ih =>
    obtain ⟨k, w⟩ := p
    by_cases hk : a = k
    · subst hk; simp [List.lookup] at h; subst h; simp
    · have : (a == k) = false := by simpa using hk
      simp only [List.lookup, this] at h
      exact List.mem_cons_of_mem _ (ih h)

theorem lookupBelow_leaf {pre : List String} :
    (rest : List String) → (ms : List (String × DerivedFieldNode)) → (seg : String) →
    (n : DerivedFieldNode) → (seg, n) ∈ ms → lookupBelow n rest = .leaf →
      ∃ t, (pre ++ seg :: rest, t) ∈ DerivedFieldNode.leaves pre ms
  | [], ms, seg, n, hm, h => by
    cases n with
    | leaf t => exact ⟨t, by simpa using mem_leaves_of_leaf (pre := pre) ms hm⟩
    | group _ => simp [lookupBelow] at h
  | s :: rest, ms, seg, n, hm, h => by
    cases n with
    | leaf _ => simp [lookupBelow] at h
    | group ms' =>
      simp only [lookupBelow] at h
      cases hl : ms'.lookup s with
      | none => rw [hl] at h; cases h
      | some n' =>
        rw [hl] at h
        obtain ⟨t, ht⟩ := lookupBelow_leaf (pre := pre ++ [seg]) rest ms' s n' (mem_of_lookup_node hl) h
        exact ⟨t, leaves_sub_of_group ms hm _ (by simpa using ht)⟩

/-- A path that names a leaf is a leaf field's. -/
theorem mem_leafFields_of_lookupPath {ev : DerivedEvent} {p : List String} (h : lookupPath ev p = .leaf) :
    ∃ t, (p, t) ∈ ev.leafFields := by
  cases p with
  | nil => simp [lookupPath] at h
  | cons head rest =>
    simp only [lookupPath] at h
    cases hl : ev.fields.lookup head with
    | none => rw [hl] at h; cases h
    | some n =>
      rw [hl] at h
      obtain ⟨t, ht⟩ := lookupBelow_leaf (pre := []) rest ev.fields head n (mem_of_lookup_node hl) h
      exact ⟨t, by unfold DerivedEvent.leafFields; rw [List.mem_mergeSort]; simpa using ht⟩

/-! ## The projection's signatures -/

/-- What the projection makes of one derived field (`EventSignature.toSpec`): a spliced field that
resolves in its action's context the type there, any other its event-schema type. -/
def FieldOk (S : Schema) (ns : List String) (ctx : Option RecordType) (x : List String × FieldType)
    (ty : Dogwood.Spec.FieldTy) : Prop :=
  match isSpliced x.1, ctx.bind (pathType · x.1) with
  | true, some (t, _) => ty = .cedar t
  | _, _ =>
    match x.2 with
    | .entityTypes names => ∃ etys, names.mapM (resolveEntityType S ns) = .ok etys ∧ ty = .entities etys
    | .cedar text => ∃ t, textType S text = .ok t ∧ ty = .cedar t

/-- The projection's translation of one derived field (`EventSignature.toSpec`). -/
def specField (S : Schema) (ns : List String) (ctx : Option RecordType) :
    List String × FieldType → Except String Dogwood.Spec.FieldDecl
  | (path, fty) =>
    match isSpliced path, ctx.bind (pathType · path) with
    | true, some (t, req) => pure { path, ty := .cedar t, required := req }
    | _, _ =>
      match fty with
      | .entityTypes names => do
        pure { path, ty := .entities (← names.mapM (resolveEntityType S ns)), required := false }
      | .cedar text => do pure { path, ty := .cedar (← textType S text), required := false }

theorem specField_ok {S : Schema} {ns : List String} {ctx : Option RecordType}
    {x : List String × FieldType} {fd : Dogwood.Spec.FieldDecl} (h : specField S ns ctx x = .ok fd) :
    fd.path = x.1 ∧ FieldOk S ns ctx x fd.ty := by
  obtain ⟨path, fty⟩ := x
  unfold specField at h
  unfold FieldOk
  simp only at h ⊢
  cases hsp : isSpliced path <;> cases hc : ctx.bind (pathType · path) <;> rw [hsp, hc] at h <;>
    simp only
  all_goals first
    | (rename_i tr; obtain ⟨t, req⟩ := tr
       simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; exact ⟨rfl, rfl⟩)
    | skip
  all_goals
    cases fty with
    | entityTypes names =>
      simp only [bind, Except.bind] at h ⊢
      cases hm : names.mapM (resolveEntityType S ns) with
      | error e => rw [hm] at h; cases h
      | ok etys =>
        rw [hm] at h; simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
        exact ⟨rfl, etys, rfl, rfl⟩
    | cedar text =>
      simp only [bind, Except.bind] at h ⊢
      cases ht : textType S text with
      | error e => rw [ht] at h; cases h
      | ok t =>
        rw [ht] at h; simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
        exact ⟨rfl, t, rfl, rfl⟩

theorem toSpec_ok {S : Schema} {s : EventSignature} {sig : Dogwood.Spec.EventSignature}
    (h : EventSignature.toSpec S s = .ok sig) :
    sig.action = actionUid s.namespace s.action ∧ sig.kind = s.kind ∧
      s.pins.mapM Dogwood.Frontend.Pin.toSpec = .ok sig.pins ∧
      List.Forall₂ (fun x fd => fd.path = x.1 ∧
        FieldOk S s.namespace ((S.acts.find? (actionUid s.namespace s.action)).map (·.context)) x fd.ty)
        s.fields sig.fields := by
  unfold EventSignature.toSpec at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · rename_i pins hpins
    split at h
    · cases h
    · rename_i fields hfields
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      refine ⟨rfl, rfl, hpins, ?_⟩
      have hf : s.fields.mapM (specField S s.namespace
          ((S.acts.find? (actionUid s.namespace s.action)).map (·.context))) = .ok fields := hfields
      exact Cedar.List.Forall₂.imp (fun _ _ hx => specField_ok hx) (List.mapM_ok_iff_forall₂.mp hf)

/-! ## The projection's signatures agree with the crate's lookups -/

theorem filterMap_toOption_of_mapM {α β ε : Type} {f : α → Except ε β} :
    {xs : List α} → {ys : List β} → xs.mapM f = .ok ys → xs.filterMap (fun x => (f x).toOption) = ys
  | xs, ys, h => by
    have := List.mapM_ok_iff_forall₂.mp h
    clear h
    induction this with
    | nil => rfl
    | cons hxy _ ih =>
      simp only [List.filterMap_cons, hxy]
      simp only [Except.toOption] at ih ⊢
      rw [ih]

theorem descend_of_pathType : {rty : RecordType} → {p : List String} → {t : CedarType} → {r : Bool} →
    pathType rty p = some (t, r) → ∃ seg rest q, p = seg :: rest ∧ rty.find? seg = some q ∧
      descend q.getType rest = .resolved t
  | _, [], _, _, h => by simp [pathType] at h
  | rty, [last], t, r, h => by
    simp only [pathType] at h
    cases hf : rty.find? last with
    | none => rw [hf] at h; cases h
    | some q =>
      rw [hf] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      exact ⟨last, [], q, rfl, hf, by rw [← h.1]; rfl⟩
  | rty, seg :: s2 :: rest, t, r, h => by
    simp only [pathType] at h
    cases hf : rty.find? seg with
    | none => rw [hf] at h; cases h
    | some q =>
      rw [hf] at h
      cases q with
      | required ty =>
        cases ty with
        | record inner =>
          simp only at h
          obtain ⟨seg', rest', q', heq, hf', hd⟩ := descend_of_pathType h
          simp only [List.cons.injEq] at heq; obtain ⟨rfl, rfl⟩ := heq
          exact ⟨seg, s2 :: rest, _, rfl, hf, by
            show descend (CedarType.record inner) (s2 :: rest) = _
            simp only [descend, hf']; exact hd⟩
        | _ => simp at h
      | optional ty =>
        cases ty with
        | record inner =>
          simp only at h
          cases hp : pathType inner (s2 :: rest) with
          | none => rw [hp] at h; cases h
          | some tr =>
            obtain ⟨t', r'⟩ := tr
            rw [hp] at h
            simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, -⟩ := h
            obtain ⟨seg', rest', q', heq, hf', hd⟩ := descend_of_pathType hp
            simp only [List.cons.injEq] at heq; obtain ⟨rfl, rfl⟩ := heq
            exact ⟨seg, s2 :: rest, _, rfl, hf, by
              show descend (CedarType.record inner) (s2 :: rest) = _
              simp only [descend, hf']; exact hd⟩
        | _ => simp at h

/-- A path the projection types in a context resolves there, to the same type, when its head is
not reserved. -/
theorem contextPathType?_of_pathType {ctx : RecordType} {p : List String} {t : CedarType} {r : Bool}
    (h : pathType ctx p = some (t, r)) (hh : ∀ a tl, p = a :: tl → isHoistedName a = false) :
    contextPathType? ctx p = some t := by
  obtain ⟨seg, rest, q, rfl, hf, hd⟩ := descend_of_pathType h
  simp [contextPathType?, resolveContextPath, hh seg rest rfl, hf, hd]

theorem isHoistedName_input : isHoistedName "input" = false := by decide
theorem isHoistedName_output : isHoistedName "output" = false := by decide

theorem isSpliced_head {p : List String} (h : isSpliced p = true) :
    ∀ a tl, p = a :: tl → isHoistedName a = false := by
  intro a tl hp
  subst hp
  unfold isSpliced at h
  split at h
  · rename_i heq; simp only [List.cons.injEq] at heq; rw [heq.1]; exact isHoistedName_input
  · rename_i heq; simp only [List.cons.injEq] at heq; rw [heq.1]; exact isHoistedName_output
  · cases h

/-- The crate's typing of a derived field, from the projection's. -/
theorem eventField_of_fieldOk {S : Schema} {ns : List String} {ctx : Option RecordType}
    {x : List String × FieldType} {ty : Dogwood.Spec.FieldTy} (h : FieldOk S ns ctx x ty) :
    (match isSpliced x.1, ctx.bind (pathType · x.1) with
      | true, some (t, req) => (x.1, some (Dogwood.Spec.FieldTy.cedar t), req)
      | _, _ =>
        match x.2 with
        | .entityTypes names =>
          (x.1, some (Dogwood.Spec.FieldTy.entities (names.filterMap fun n => (resolveEntityType S ns n).toOption)), false)
        | .cedar text => (x.1, ((textType S text).toOption.map .cedar), false)).2.1 = some ty := by
  unfold FieldOk at h
  split
  · rename_i t req _ hc
    simp only [*] at h; subst h; rfl
  · rename_i hne
    have h' : (match x.2 with
        | .entityTypes names => ∃ etys, names.mapM (resolveEntityType S ns) = .ok etys ∧ ty = .entities etys
        | .cedar text => ∃ t, textType S text = .ok t ∧ ty = .cedar t) := by
      split at h
      · rename_i t req hs hc; exact absurd hc (hne t req hs)
      · exact h
    obtain ⟨path, fty⟩ := x
    cases fty with
    | entityTypes names =>
      obtain ⟨etys, hm, rfl⟩ := h'
      simp [filterMap_toOption_of_mapM hm]
    | cedar text =>
      obtain ⟨t, ht, rfl⟩ := h'
      simp [ht, Except.toOption]

/-- The crate's typing of one derived field (`eventFields`). -/
def ef (S : Schema) (ns : List String) (ctx : Option RecordType) :
    List String × FieldType → List String × Option Dogwood.Spec.FieldTy × Bool
  | (path, fty) =>
    match isSpliced path, ctx.bind (pathType · path) with
    | true, some (t, req) => (path, some (.cedar t), req)
    | _, _ =>
      match fty with
      | .entityTypes names =>
        (path, some (.entities (names.filterMap fun n => (resolveEntityType S ns n).toOption)), false)
      | .cedar text => (path, ((textType S text).toOption.map .cedar), false)

theorem eventFields_eq (S : Schema) (e : DerivedEvent) :
    eventFields S e =
      e.leafFields.map (ef S e.namespace ((S.acts.find? (actionUid e.namespace e.action)).map (·.context))) :=
  rfl

theorem ef_fst (S : Schema) (ns : List String) (ctx : Option RecordType) (x : List String × FieldType) :
    (ef S ns ctx x).1 = x.1 := by
  obtain ⟨path, fty⟩ := x
  simp only [ef]
  split
  · rfl
  · cases fty <;> rfl

theorem ef_ty {S : Schema} {ns : List String} {ctx : Option RecordType} {x : List String × FieldType}
    {ty : Dogwood.Spec.FieldTy} (h : FieldOk S ns ctx x ty) : (ef S ns ctx x).2.1 = some ty := by
  obtain ⟨path, fty⟩ := x
  exact eventField_of_fieldOk h

theorem find?_forall₂ {α β : Type} {R : α → β → Prop} {p : α → Bool} {q : β → Bool} :
    {xs : List α} → {ys : List β} → List.Forall₂ R xs ys → (∀ x y, R x y → p x = q y) →
      {x : α} → xs.find? p = some x → ∃ y, ys.find? q = some y ∧ R x y
  | _, _, .nil, _, _, h => by simp at h
  | x' :: xs, y' :: ys, .cons hxy hr, hpq, x, h => by
    rw [List.find?_cons] at h ⊢
    rw [← hpq x' y' hxy]
    cases hp : p x'
    · rw [hp] at h; exact find?_forall₂ hr hpq h
    · rw [hp] at h; simp only [Option.some.injEq] at h; subst h; exact ⟨y', rfl, hxy⟩

theorem forall₂_mem_left {α β : Type} {R : α → β → Prop} :
    {xs : List α} → {ys : List β} → List.Forall₂ R xs ys → {x : α} → x ∈ xs → ∃ y ∈ ys, R x y
  | _, _, .nil, _, h => by cases h
  | _, _, .cons hxy hr, _, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨_, List.mem_cons_self, hxy⟩
    · obtain ⟨y, hy, hR⟩ := forall₂_mem_left hr h
      exact ⟨y, List.mem_cons_of_mem _ hy, hR⟩

theorem forall₂_mem_right {α β : Type} {R : α → β → Prop} :
    {xs : List α} → {ys : List β} → List.Forall₂ R xs ys → {y : β} → y ∈ ys → ∃ x ∈ xs, R x y
  | _, _, .nil, _, h => by cases h
  | _, _, .cons hxy hr, _, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨_, List.mem_cons_self, hxy⟩
    · obtain ⟨x, hx, hR⟩ := forall₂_mem_right hr h
      exact ⟨x, List.mem_cons_of_mem _ hx, hR⟩

/-- **The projection's signature of a derived event agrees with the crate's lookups in it.** -/
theorem sigAgrees_of_toSpec {S : Schema} {ev : DerivedEvent} {sig : Dogwood.Spec.EventSignature}
    (h : EventSignature.toSpec S ev.signature = .ok sig)
    (hspl : ∀ x ∈ ev.leafFields, isSpliced x.1 = true →
      (((S.acts.find? (actionUid ev.namespace ev.action)).map (·.context)).bind (pathType · x.1)).isSome)
    (hpin : ∀ pin ∈ ev.pins, ev.leafFields.any (·.1 == pin.fieldPath) = true) :
    SigAgrees S (actionUid ev.namespace ev.action) ev sig := by
  obtain ⟨-, -, hpins, hf⟩ := toSpec_ok h
  simp only [DerivedEvent.signature] at hpins hf
  -- The crate's field lookup is the projection's, field by field.
  have hfields : ∀ p, fieldType? S ev p = (sig.field? p).map (some ·.ty) := by
    intro p
    unfold fieldType? Dogwood.Spec.EventSignature.field?
    rw [eventFields_eq]
    clear hspl hpin hpins h
    generalize ev.leafFields = L at hf ⊢
    generalize sig.fields = M at hf ⊢
    induction hf with
    | nil => rfl
    | @cons x fd L M hxy _ ih =>
      rw [List.map_cons, List.find?_cons, List.find?_cons, ef_fst, hxy.1]
      cases hb : x.1 == p
      · exact ih
      · simp only [Option.map_some]; rw [ef_ty hxy.2]
  -- A field of the derived event is a field of the signature.
  have hdecl : ∀ x ∈ ev.leafFields, (sig.field? x.1).isSome := by
    intro x hx
    obtain ⟨fd, hfd, hR⟩ := forall₂_mem_left hf hx
    unfold Dogwood.Spec.EventSignature.field?
    rw [List.find?_isSome]
    exact ⟨fd, hfd, by simp [hR.1]⟩
  refine ⟨hfields, ?_, ?_, hpins, ?_⟩
  · intro p hp
    obtain ⟨t, ht⟩ := mem_leafFields_of_lookupPath hp
    exact hdecl (p, t) ht
  · intro p fd hsp hfd
    have hmem := List.mem_of_find?_eq_some hfd
    have hp := List.find?_some hfd
    simp only [beq_iff_eq] at hp
    obtain ⟨x, hx, hR⟩ := forall₂_mem_right hf hmem
    have hx1 : x.1 = p := by rw [← hR.1, hp]
    have hs := hspl x hx (by rw [hx1]; exact hsp)
    obtain ⟨⟨t, req⟩, hc⟩ := Option.isSome_iff_exists.mp hs
    have hok := hR.2
    unfold FieldOk at hok
    rw [hx1] at hc hok
    rw [hsp, hc] at hok
    refine ⟨t, ?_, hok⟩
    unfold splicedFieldType?
    cases hact : S.acts.find? (actionUid ev.namespace ev.action) with
    | none => rw [hact] at hc; cases hc
    | some entry =>
      rw [hact] at hc
      simp only [Option.map_some, Option.bind_some] at hc
      exact contextPathType?_of_pathType hc (isSpliced_head hsp)
  · intro pin hp
    have := hpin pin hp
    rw [List.any_eq_true] at this
    obtain ⟨x, hx, hxe⟩ := this
    simp only [beq_iff_eq] at hxe
    rw [← hxe]
    exact hdecl x hx

theorem forall₂_map_left {α γ β : Type} {f : α → γ} {R : γ → β → Prop} :
    {xs : List α} → {ys : List β} → List.Forall₂ R (xs.map f) ys → List.Forall₂ (fun x y => R (f x) y) xs ys
  | [], [], _ => .nil
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | x :: xs, y :: ys, h => by
    cases h with
    | cons hxy hr => exact .cons hxy (forall₂_map_left hr)

/-- **The projection's event schema agrees with the crate's lookups in the derived one**: the
signature a predicate names is the projection of the event the crate finds for it. -/
theorem events_agree {d : DerivedEventSchema} {S : Schema} {sigs : Dogwood.Spec.EventSchema}
    (h : typedSignatures d S = .ok sigs)
    (hdf : ∀ ev ∈ d.events,
      (∀ x ∈ ev.leafFields, isSpliced x.1 = true →
        (((S.acts.find? (actionUid ev.namespace ev.action)).map (·.context)).bind (pathType · x.1)).isSome) ∧
      (∀ pin ∈ ev.pins, ev.leafFields.any (·.1 == pin.fieldPath) = true))
    {a : Cedar.Spec.EntityUID} {k : String} {ev : DerivedEvent} (hev : eventOf? d a k = some ev) :
    ∃ sig, Dogwood.Spec.EventSchema.signature? sigs a k = some sig ∧ SigAgrees S a ev sig := by
  unfold typedSignatures at h
  have hf := List.mapM_ok_iff_forall₂.mp h
  replace hf : List.Forall₂ (fun e y => EventSignature.toSpec S e.signature = .ok y) d.events sigs :=
    forall₂_map_left hf
  unfold eventOf? at hev
  have hmem := List.mem_of_find?_eq_some hev
  have hp := List.find?_some hev
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  obtain ⟨sig, hsig, hR⟩ := find?_forall₂ (q := fun s : Dogwood.Spec.EventSignature => s.action == a && s.kind == k)
    hf (fun e s hes => by
      obtain ⟨h1, h2, -, -⟩ := toSpec_ok hes
      simp only [DerivedEvent.signature] at h1 h2
      simp [h1, h2]) hev
  refine ⟨sig, hsig, ?_⟩
  rw [← hp.1]
  exact sigAgrees_of_toSpec hR (hdf ev hmem).1 (hdf ev hmem).2

end Dogwood.Thm.Frontend
