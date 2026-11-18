/-
 Copyright Cedar Contributors

 Licensed under the Apache License, Version 2.0 (the "License");
 you may not use this file except in compliance with the License.
 You may obtain a copy of the License at

      https://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software
 distributed under the License is distributed on an "AS IS" BASIS,
 WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 See the License for the specific language governing permissions and
 limitations under the License.
-/

import Cedar.Thm.WellTyped.Expr.Definition
import Cedar.Thm.WellTyped.Expr.Typechecking
import Cedar.Thm.WellTyped.Expr.TypeLifting
import Cedar.Thm.Validation.Typechecker.WF

/-!
This file contains the theorems that `TypedExpr.WellTyped` implies `CedarType.WellFormed`.
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Validation
open Cedar.Spec

/--
`TypedExpr.WellTyped` implies well-formedness of the type (`CedarType.WellFormed`).
-/
theorem well_typed_implies_wf_type
  {env : TypeEnv} {tx : TypedExpr}
  (hwf_env : env.WellFormed)
  (hwt : TypedExpr.WellTyped env tx) :
  CedarType.WellFormed env tx.typeOf
:= by
  cases hwt with
  | lit hwt_prim =>
    cases hwt_prim
    any_goals
      simp only [TypedExpr.typeOf]
      constructor
    rename_i hwt_uid
    simp only [EntityType.WellFormed, ActionSchema.IsActionEntityType]
    simp only [EntitySchema.isValidEntityUID] at hwt_uid
    rcases hwt_uid with hets | hacts
    · split at hets
      · rename_i hsome
        simp only [EntitySchema.contains, Option.isSome, hsome, true_or]
      · contradiction
    · rename_i uid
      apply Or.inr
      exists uid
  | var hwt_var =>
    have ⟨hwf_principal, hwf_action, hwf_resource, hwf_context⟩
    := wf_env_implies_wf_request hwf_env
    cases hwt_var
    all_goals simp only [TypedExpr.typeOf]
    case principal =>
      constructor
      assumption
    case action =>
      constructor
      simp only [EntityType.WellFormed, ActionSchema.IsActionEntityType]
      apply Or.inr
      exists env.reqty.action
    case resource =>
      constructor
      assumption
    case context =>
      apply wf_type_iff_wf_liftBoolTypes.mp
      assumption
  | ite _ hwf2 =>
    simp only [TypedExpr.typeOf]
    exact well_typed_implies_wf_type hwf_env hwf2
  | and _ => constructor
  | or _ => constructor
  | unaryApp _ hwt_op =>
    simp only [TypedExpr.typeOf]
    cases hwt_op
    all_goals constructor
  | binaryApp _ _ hwt_op =>
    simp only [TypedExpr.typeOf]
    cases hwt_op with
    | getTag =>
      apply wf_type_iff_wf_liftBoolTypes.mp
      apply wf_env_implies_wf_tag_type
      assumption
      assumption
    | _ => constructor
  | hasAttr_entity => constructor
  | hasAttr_record => constructor
  | extHasAttr_entity => constructor
  | extHasAttr_record => constructor
  | extHasAttr_ff => constructor
  | getAttr_entity _ _ hattrs hattr =>
    simp only [TypedExpr.typeOf]
    simp only [Option.map_eq_some_iff] at hattrs hattr
    have ⟨attrs, hattrs, hattrs_lift⟩ := hattrs
    have ⟨attr, hattr, hattr_ty⟩ := hattr
    simp only [← hattr_ty]
    have hwf_attrs := wf_env_implies_wf_attrs hwf_env hattrs
    have hwf_attrs_lift := wf_type_iff_wf_liftBoolTypes.mp hwf_attrs
    simp only [CedarType.liftBoolTypes, hattrs_lift] at hwf_attrs_lift
    have hwf_attr := wf_record_implies_wf_attr hwf_attrs_lift hattr
    apply qty_wf_implies_type_of_wf
    exact hwf_attr
  | getAttr_record hwt1 hwt_rec hattr =>
    simp only [TypedExpr.typeOf]
    simp only [Option.map_eq_some_iff] at hattr
    have hwf1 := well_typed_implies_wf_type hwf_env hwt1
    simp only [hwt_rec] at hwf1
    have ⟨attr, hattr, hattr_ty⟩ := hattr
    simp only [← hattr_ty]
    apply qty_wf_implies_type_of_wf
    apply wf_record_implies_wf_attr
    assumption
    assumption
  | set hwt_elem hty_elem hnon_empty =>
    rename_i elems elem_ty
    simp only [TypedExpr.typeOf]
    constructor
    cases elems with
    | nil => contradiction
    | cons hd _ =>
      have := hwt_elem hd
      simp only [List.mem_cons, true_or, forall_const] at this
      have hwf_hd := well_typed_implies_wf_type hwf_env this
      have := hty_elem hd
      simp only [List.mem_cons, true_or, forall_const] at this
      simp only [this] at hwf_hd
      assumption
  | record hwt_attrs hrty =>
    simp only [TypedExpr.typeOf]
    rename_i rty attrs_ls
    have hwf_rty : Map.WellFormed rty := by
      simp only [hrty]
      apply Map.make_wf
    constructor
    · exact hwf_rty
    · intros attr qty hattr
      have := (Map.in_list_iff_find?_some hwf_rty).mpr hattr
      simp only [hrty] at this
      have := Map.mem_make_mem_list this
      simp only [List.mem_map, Prod.mk.injEq, Prod.exists] at this
      have ⟨attr, tx, htx, heq_attr, hqty⟩ := this
      have := hwt_attrs attr tx htx
      -- For termination
      have _ : sizeOf tx < 1 + sizeOf attrs_ls + (1 + sizeOf rty) := by
        simp [*]
        have h := List.sizeOf_snd_lt_sizeOf_list htx
        simp at h
        omega
      have := well_typed_implies_wf_type hwf_env this
      simp only [← hqty]
      constructor
      assumption
  | call _ hwt_xfn =>
    cases hwt_xfn
    all_goals
      simp only [TypedExpr.typeOf]
      constructor

/--
The result of `typeOf` has a well-formed type.
-/
theorem typechecked_has_well_formed_type
  {e : Expr}
  {c₁ c₂ : Capabilities}
  {env : TypeEnv}
  {tx : TypedExpr}
  (hwf : env.WellFormed)
  (hty : typeOf e c₁ env = .ok (tx, c₂)) :
  tx.typeOf.WellFormed env
:= by
  have : CedarType.WellFormed env tx.liftBoolTypes.typeOf := by
    apply well_typed_implies_wf_type hwf
    apply typechecked_is_well_typed_after_lifting
    assumption
  cases tx
  all_goals
    simp only [TypedExpr.liftBoolTypes, TypedExpr.typeOf] at this
    simp only [TypedExpr.typeOf]
    apply wf_type_iff_wf_liftBoolTypes.mpr
    assumption

end Cedar.Thm
