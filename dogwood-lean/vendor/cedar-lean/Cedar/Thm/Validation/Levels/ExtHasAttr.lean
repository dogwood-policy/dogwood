import Cedar.Spec
import Cedar.Data
import Cedar.Validation
import Cedar.Thm.Validation.Typechecker
import Cedar.Thm.Validation.Typechecker.Basic
import Cedar.Thm.Validation.Typechecker.IfThenElse
import Cedar.Thm.Validation.Typechecker.Types
import Cedar.Thm.Validation.Slice
import Cedar.Thm.Validation.Levels.Basic
import Cedar.Thm.Validation.Levels.CheckLevel
import Cedar.Thm.Validation.Levels.ReachableChild
import Cedar.Thm.Validation.Levels.SliceHelpers
import Cedar.Thm.WellTyped.Expr.Typechecking

/-!
This file proves that level checking for `.extHasAttr` expressions is sound.
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

set_option maxHeartbeats 800000

/-! ## Core helper lemmas -/

/--
If `uid` is reachable at level `n+1`, then its `find?` agrees between
entities and the slice at level `n+1`.
-/
theorem reachable_implies_find_agree
  (entities : Entities) (request : Request) (uid : EntityUID) (n : Nat)
  (hr : ReachableIn entities request.sliceEUIDs uid (n + 1)) :
  (entities.sliceAtLevel request (n + 1)).find? uid = entities.find? uid := by
  cases hf : entities.find? uid with
  | none => exact not_entities_then_not_slice hf
  | some ed =>
    simp only [Entities.sliceAtLevel]
    have hi := slice_contains_reachable hr
    let eids := Entities.sliceAtLevel.sliceAtLevel entities request.sliceEUIDs (n + 1)
    let eds := eids.elts.filterMap (λ e => do some (e, ← Map.find? entities e))
    have hmake : Map.mk eds = Map.make eds := by
      have hsorted := eids.wf_iff_sorted.mp slice_at_level_inner_well_formed
      have hsbfst : eds.SortedBy Prod.fst := List.filterMap_key_id_sortedBy_key hsorted
      have hwf : (Map.mk eds).WellFormed := by
        simpa [Map.wf_iff_sorted] using hsbfst
      simpa [Map.WellFormed] using hwf
    rw [←hmake]
    exact (Map.find?_filterMap_key_id hi).symm ▸ hf

private theorem find?_slice_eq
  {entities : Entities} {request : Request} {uid : EntityUID}
  {level sliceLevel : Nat}
  (hr : ReachableIn entities request.sliceEUIDs uid level)
  (hle : level ≤ sliceLevel) (hpos : 0 < sliceLevel) :
  (entities.sliceAtLevel request sliceLevel).find? uid = entities.find? uid := by
  have hr' := reachable_of_le hr hle
  have heq : sliceLevel - 1 + 1 = sliceLevel := by omega
  rw [← heq] at hr' ⊢
  exact reachable_implies_find_agree entities request uid (sliceLevel - 1) hr'

private theorem instance_of_found_attribute
  {env : TypeEnv} {r : Map Attr Value} {rty : RecordType}
  {a : Attr} {v : Value}
  (hinst : InstanceOfType env (.record r) (.record rty))
  (hfind : r.find? a = .some v) :
  ∃ qty, rty.find? a = .some qty ∧ InstanceOfType env v qty.getType := by
  cases hqty : rty.find? a with
  | none =>
    have h := absent_attribute_is_absent hinst hqty
    simp [hfind] at h
  | some qty =>
    exact ⟨qty, rfl, instance_of_attribute_type hinst hqty rfl hfind⟩

private theorem reachable_child_succ
  {entities : Entities} {start : Set EntityUID} {uid uid' : EntityUID}
  {ed : EntityData} {level : Nat}
  (hr : ReachableIn entities start uid level)
  (hpos : 0 < level)
  (hfind : entities.find? uid = .some ed)
  (hmem : uid' ∈ ed.sliceEUIDs) :
  ReachableIn entities start uid' (level + 1) := by
  have heq : level = level - 1 + 1 := by omega
  have hr' := reachable_child (heq ▸ hr) hfind hmem
  have heq' : level - 1 + 2 = level + 1 := by omega
  exact heq' ▸ hr'

/-! ## The main soundness theorem -/

mutual
/--
Core lemma: `hasAttrs.loop` on an entity uid agrees between full and sliced
stores when the uid is reachable and the chain cost budget is sufficient.
-/
theorem hasAttrs_loop_entity_sound
  {uid : EntityUID} {ety : EntityType} {attrs : List Attr} {sliceLevel : Nat}
  {entities : Entities} {request : Request} {env : TypeEnv}
  (hwf : InstanceOfWellFormedEnvironment request entities env)
  (huidty : InstanceOfEntityType uid ety env)
  (hcost : extHasAttrChainCost env (.entity ety) attrs < sliceLevel)
  (hreach : ReachableIn entities request.sliceEUIDs uid
    (sliceLevel - extHasAttrChainCost env (.entity ety) attrs)) :
  hasAttrs.loop (.prim (.entityUID uid)) attrs entities =
    hasAttrs.loop (.prim (.entityUID uid)) attrs (entities.sliceAtLevel request sliceLevel) := by
  cases attrs with
  | nil => simp [hasAttrs.loop]
  | cons a rest =>
    simp only [hasAttrs.loop, attrsOf, Entities.attrsOrEmpty]
    have hfind_agree := find?_slice_eq hreach (Nat.sub_le _ _) (by omega)
    rw [hfind_agree]
    cases h₁ : entities.find? uid with
    | none => simp
    | some ed =>
      simp only []
      cases h₂ : ed.attrs.find? a with
      | none => simp
      | some next =>
        simp only []
        cases rest with
        | nil => simp only [ExceptT.stM_eq]; unfold hasAttrs.loop; simp
        | cons b bs =>
          -- Derive schema info from InstanceOfWellFormedEnvironment + entities.find? uid = some ed
          have h₃ := hwf.2.2.1 uid ed h₁
          have h₄ : ∃ rty, env.ets.attrs? ety = .some rty ∧
              InstanceOfType env ed.attrs (.record rty) := by
            cases h₃ with
            | inl h =>
              obtain ⟨x, h₅, _, h₆, _⟩ := h
              exact ⟨x.attrs, by simp [EntitySchema.attrs?, ← huidty.1.symm, h₅], h₆⟩
            | inr h =>
              -- Action entity: data.attrs = .empty, contradicts hfinda
              obtain ⟨h₅, _⟩ := h
              rw [h₅] at h₂
              simp [Map.find?, Map.empty] at h₂
          obtain ⟨x, h₅, h₆⟩ := h₄
          obtain ⟨x₁, h₈, h₉⟩ := instance_of_found_attribute h₆ h₂
          cases hqty : x₁.getType with
          | entity nextEty =>
            -- next is an entity uid
            rw [hqty] at h₉
            cases h₉ with
            | instance_of_entity uid2 _ huid2ty =>
            -- Recurse on the tail: uid2 is reachable
            apply hasAttrs_loop_entity_sound hwf huid2ty
            · -- cost: extHasAttrChainCostTy env (.entity nextEty) (b :: bs) < sliceLevel
              simp [extHasAttrChainCost, h₅, h₈, hqty] at hcost
              omega
            · -- reach: uid2 is reachable at (sliceLevel - cost)
              have hmem : uid2 ∈ ed.sliceEUIDs :=
                sliceEUIDs_entity_attr h₂ uid2 (by simp [Value.sliceEUIDs, Set.mem_singleton])
              have hcost_eq : extHasAttrChainCost env (.entity ety) (a :: b :: bs) =
                  1 + extHasAttrChainCost env (.entity nextEty) (b :: bs) := by
                simp [extHasAttrChainCost, h₅, h₈, hqty]
              rw [hcost_eq] at hreach hcost
              have hreach_child := reachable_child_succ hreach (by omega) h₁ hmem
              have heq :
                  sliceLevel - (1 + extHasAttrChainCost env (.entity nextEty) (b :: bs)) + 1 =
                    sliceLevel - extHasAttrChainCost env (.entity nextEty) (b :: bs) := by
                omega
              exact heq ▸ hreach_child
          | record nextRty =>
            rw [hqty] at h₉
            obtain ⟨nextRecord, rfl⟩ := instance_of_record_type_is_record h₉
            apply hasAttrs_loop_record_sound hwf h₉
            · exact Nat.le_of_lt (by
                simpa [extHasAttrChainCost, h₅, h₈, hqty] using hcost)
            · intro path _ uid₂ hpath
              have hmem := in_val_then_val_slice hpath
              have hcost_eq :
                  extHasAttrChainCost env (.entity ety) (a :: b :: bs) =
                    extHasAttrChainCost env (.record nextRty) (b :: bs) := by
                simp [extHasAttrChainCost, h₅, h₈, hqty]
              rw [hcost_eq] at hreach hcost
              exact reachable_child_succ hreach (by omega) h₁
                (sliceEUIDs_entity_attr h₂ uid₂ hmem)
          | _ =>
            rw [hqty] at h₉
            cases h₉ ; simp [hasAttrs.loop, attrsOf]
termination_by attrs.length
decreasing_by
  all_goals simp_all

theorem hasAttrs_loop_record_sound
  {r : Map Attr Value} {rty : RecordType} {attrs : List Attr} {sliceLevel : Nat}
  {entities : Entities} {request : Request} {env : TypeEnv}
  (hwf : InstanceOfWellFormedEnvironment request entities env)
  (hinst : InstanceOfType env (.record r) (.record rty))
  (hcost : extHasAttrChainCost env (.record rty) attrs <= sliceLevel)
  (hreach : ∀ path,
    extHasAttrFirstEntityPath? env (.record rty) attrs = some path →
    ∀ uid, Value.EuidViaPath (.record r) path uid →
      ReachableIn entities request.sliceEUIDs uid
        (sliceLevel - extHasAttrChainCost env (.record rty) attrs + 1)) :
  hasAttrs.loop (.record r) attrs entities =
    hasAttrs.loop (.record r) attrs (entities.sliceAtLevel request sliceLevel) := by
  cases attrs with
  | nil => simp [hasAttrs.loop]
  | cons a rest =>
    simp only [hasAttrs.loop, attrsOf]
    cases hfind : r.find? a with
    | none => simp
    | some next =>
      cases rest with
      | nil => simp only [ExceptT.stM_eq]; unfold hasAttrs.loop; simp
      | cons b bs =>
        obtain ⟨qty, hfindq, hnext_inst⟩ := instance_of_found_attribute hinst hfind
        cases hqty : qty.getType with
        | entity nextEty =>
          rw [hqty] at hnext_inst
          cases hnext_inst with
          | instance_of_entity uid _ huidty =>
            apply hasAttrs_loop_entity_sound hwf huidty
            · simp [extHasAttrChainCost, hfindq, hqty] at hcost
              omega
            · have hr := hreach [a]
                (by simp [extHasAttrFirstEntityPath?, hfindq, hqty]) uid
                (.record hfind (.euid uid))
              have hcost_eq : extHasAttrChainCost env (.record rty) (a :: b :: bs) =
                    extHasAttrChainCost env (.entity nextEty) (b :: bs) + 1 := by
                    simp [extHasAttrChainCost, hfindq, hqty]
                    omega
              rw [hcost_eq] at hr hcost
              have heq :
                  sliceLevel - (extHasAttrChainCost env (.entity nextEty) (b :: bs) + 1) + 1 =
                    sliceLevel - extHasAttrChainCost env (.entity nextEty) (b :: bs) := by
                omega
              exact heq ▸ hr
        | record nextRty =>
          rw [hqty] at hnext_inst
          obtain ⟨nextRecord, rfl⟩ :=
            instance_of_record_type_is_record hnext_inst
          apply hasAttrs_loop_record_sound hwf hnext_inst
          · simpa [extHasAttrChainCost, hfindq, hqty] using hcost
          · intro path hpath uid hvia
            have hr := hreach (a :: path)
              (by simp [extHasAttrFirstEntityPath?, hfindq, hqty, hpath]) uid
              (.record hfind hvia)
            have hcost_eq :
                extHasAttrChainCost env (.record rty) (a :: b :: bs) =
                  extHasAttrChainCost env (.record nextRty) (b :: bs) := by
              simp [extHasAttrChainCost, hfindq, hqty]
            rw [hcost_eq] at hr
            exact hr
        | _ =>
          rw [hqty] at hnext_inst
          cases hnext_inst ; simp [hasAttrs.loop, attrsOf]
termination_by attrs.length
decreasing_by
  all_goals simp_all
end

private theorem evaluate_extHasAttr_eq_of_loop_eq
  {e : Expr} {a : Attr} {attrs : List Attr} {request : Request}
  {entities entities' : Entities} {v : Value}
  (he : EvaluatesTo e request entities v)
  (hie : evaluate e request entities = evaluate e request entities')
  (hloop : evaluate e request entities = .ok v →
    hasAttrs.loop v (a :: attrs) entities =
      hasAttrs.loop v (a :: attrs) entities') :
  evaluate (.extHasAttr e a attrs) request entities =
    evaluate (.extHasAttr e a attrs) request entities' := by
  simp only [evaluate, ← hie]
  rcases he with he | he | he | he <;> simp only [he, Except.bind_err]
  simpa only [Except.bind_ok, hasAttrs] using hloop he

theorem level_based_slicing_is_sound_ext_has_attr
  {e : Expr} {tx : TypedExpr} {a : Attr} {attrs : List Attr}
  {n : Nat} {c₀ c₁: Capabilities} {env : TypeEnv} {request : Request} {entities : Entities}
  (hc : CapabilitiesInvariant c₀ request entities)
  (hr : InstanceOfWellFormedEnvironment request entities env)
  (ht : typeOf (e.extHasAttr a attrs) c₀ env = Except.ok (tx, c₁))
  (hl : tx.AtLevel env n)
  (ihe : TypedAtLevelIsSound e) :
  evaluate (.extHasAttr e a attrs) request entities =
    evaluate (.extHasAttr e a attrs) request (entities.sliceAtLevel request n)
:= by
  simp only [typeOf] at ht
  simp_do_let (typeOf e c₀ env) as hte at ht
  rename_i baseResult
  obtain ⟨tx₁, c₁'⟩ := baseResult
  simp only [] at ht
  simp_do_let (typeOfExtHasAttr tx₁ e (a :: attrs) c₀ env) as htchain at ht
  rename_i chainResult
  obtain ⟨bty, c'⟩ := chainResult
  simp only [ok, Except.ok.injEq, Prod.mk.injEq] at ht
  have ⟨_, v, he, hv⟩ := type_of_is_sound hc hr hte
  rw [← ht.1] at hl
  cases hl
  case extHasAttr =>
    rename_i ety level hty hk hl₁
    rw [hty] at hv
    cases hv with
    | instance_of_entity uid _ huidty =>
      have hlbase : tx₁.AtLevel env (level + 1) := by
        apply entity_access_at_level_then_at_level (path := [])
        have bump : ∀ m n nmax path, m ≤ n →
            tx₁.EntityAccessAtLevel env m nmax path →
              tx₁.EntityAccessAtLevel env n nmax path := by
          intro m n nmax path hmn h
          induction hmn with
          | refl => exact h
          | step _ ih => exact entity_access_at_level_succ ih
        exact bump _ _ _ _ (Nat.sub_le _ _) hl₁
      apply evaluate_extHasAttr_eq_of_loop_eq he (ihe hc hr hte hlbase)
      intro he
      apply hasAttrs_loop_entity_sound hr huidty
      · simpa [extHasAttrChainCost] using Nat.lt_succ_of_le hk
      · have hreach := checked_eval_entity_reachable hc hr hte hl₁ he (.euid uid)
        change extHasAttrChainCost env (.entity ety) (a :: attrs) ≤ level at hk
        change ReachableIn entities request.sliceEUIDs uid
          (level - extHasAttrChainCost env (.entity ety) (a :: attrs) + 1) at hreach
        have heq :
            level - extHasAttrChainCost env (.entity ety) (a :: attrs) + 1 =
              level + 1 - extHasAttrChainCost env (.entity ety) (a :: attrs) := by
          omega
        exact heq ▸ hreach
  case extHasAttrRecord =>
    rename_i hnety hlbase hchain
    have hrty : ∃ rty, tx₁.typeOf = .record rty := by
      cases hty : tx₁.typeOf with
      | record rty => exact ⟨rty, rfl⟩
      | entity ety => exact absurd hty (hnety ety)
      | _ => cases attrs <;> simp [typeOfExtHasAttr, typeOfHasAttr, hty, err] at htchain
    obtain ⟨rty, hrty⟩ := hrty
    rw [hrty] at hv
    obtain ⟨record, rfl⟩ := instance_of_record_type_is_record hv
    obtain ⟨hk, hpathnone⟩ := hchain rty hrty
    apply evaluate_extHasAttr_eq_of_loop_eq he (ihe hc hr hte hlbase)
    intro _
    apply hasAttrs_loop_record_sound hr hv hk
    intro path hpath
    rw [hpathnone] at hpath
    contradiction
  case extHasAttrRecordEntity =>
    rename_i rty path hty hpath hl₁ hk haccess
    rw [hty] at hv
    obtain ⟨record, rfl⟩ := instance_of_record_type_is_record hv
    apply evaluate_extHasAttr_eq_of_loop_eq he (ihe hc hr hte hl₁)
    intro he
    apply hasAttrs_loop_record_sound hr hv hk
    intro path' hpath' uid hvia
    have hpath_eq : path = path' := Option.some.inj (hpath.symm.trans hpath')
    subst path'
    exact checked_eval_entity_reachable hc hr hte haccess he hvia

end Cedar.Thm
