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

import Cedar.Thm.Data.LT
import Cedar.Thm.Validation.Typechecker.Basic

/-!
This file proves that typechecking of `.record` expressions is sound.
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

def AttrValueHasAttrType {env : TypeEnv} (av : Attr × Value) (aqty : Attr × QualifiedType) : Prop :=
  av.fst = aqty.fst ∧ InstanceOfType env av.snd aqty.snd.getType

def AttrExprHasAttrType (c : Capabilities) (env : TypeEnv) (ax : Attr × Expr) (atx : Attr × TypedExpr) : Prop :=
  ax.fst = atx.fst ∧
  ∃ c', (typeOf ax.snd c env) = Except.ok (atx.snd, c')

theorem type_of_record_inversion_forall {axs : List (Attr × Expr)} {c : Capabilities} {env : TypeEnv} {rtx : List (Attr × TypedExpr)}
  (h₁ : axs.mapM (λ x => (typeOf x.snd c env).map (λ (ty, _) => (x.fst, ty))) = Except.ok rtx) :
  List.Forall₂ (AttrExprHasAttrType c env) axs rtx
:= by
  cases axs
  case nil =>
    simp [pure, Except.pure] at h₁ ; subst h₁ ; apply List.Forall₂.nil
  case cons hd tl =>
    cases rtx
    case nil =>
      simp [←List.mapM'_eq_mapM] at h₁
      cases h₂ : Except.map (fun x => (hd.fst, x.fst)) (typeOf hd.snd c env) <;> simp [h₂] at h₁
      cases h₃ : List.mapM' (fun x => Except.map (fun x_1 => (x.fst, x_1.fst)) (typeOf x.snd c env)) tl <;> simp [h₃] at h₁
    case cons hd' tl' =>
      apply List.Forall₂.cons
      {
        simp [←List.mapM'_eq_mapM] at h₁
        cases h₂ : Except.map (fun x => (hd.fst, x.fst)) (typeOf hd.snd c env) <;> simp [h₂] at h₁
        cases h₃ : List.mapM' (fun x => Except.map (fun x_1 => (x.fst, x_1.fst)) (typeOf x.snd c env)) tl <;> simp [h₃] at h₁
        have ⟨hl₁, hr₁⟩ := h₁
        rw [eq_comm] at hl₁ hr₁ ; subst hl₁ hr₁
        simp [Except.map] at h₂
        split at h₂ <;> simp at h₂
        subst h₂
        rename_i _ r _
        simp [AttrExprHasAttrType]
        exists r.snd
      }
      {
        apply type_of_record_inversion_forall
        simp [←List.mapM'_eq_mapM] at *
        cases h₂ : Except.map (fun x => (hd.fst, x.fst)) (typeOf hd.snd c env) <;> simp [h₂] at h₁
        cases h₃ : List.mapM' (fun x => Except.map (fun x_1 => (x.fst, x_1.fst)) (typeOf x.snd c env)) tl <;> simp [h₃] at h₁
        simp only [h₁]
      }

theorem type_of_record_inversion {axs : List (Attr × Expr)} {c c' : Capabilities} {env : TypeEnv} {tx : TypedExpr}
  (h₁ : typeOf (Expr.record axs) c env = Except.ok (tx, c')) :
  c' = ∅ ∧
  ∃ (atxs : List (Attr × TypedExpr)),
    tx = .record atxs (.record (Map.make (atxs.map λ (a, tx) => (a, .required tx.typeOf)))) ∧
    List.Forall₂ (AttrExprHasAttrType c env) axs atxs
:= by
  simp [typeOf, ok] at h₁
  cases h₂ : axs.mapM₂ fun x => Except.map (fun x_1 => (x.1.fst, x_1.fst)) (typeOf x.1.snd c env) <;> simp [h₂] at h₁
  rename_i rty
  simp [h₁]
  exists rty
  simp [←h₁]
  simp [List.mapM₂_eq_mapM λ (x : Attr × Expr) => Except.map (fun x₁ : (TypedExpr × Capabilities) => (x.fst, x₁.fst)) (typeOf x.snd c env)] at h₂
  exact type_of_record_inversion_forall h₂

theorem mk_vals_instance_of_mk_types₁ {env : TypeEnv} {a : Attr} {avs : List (Attr × Value)} {rty : List (Attr × QualifiedType)}
  (h₁ : List.Forall₂ (AttrValueHasAttrType (env := env)) avs rty)
  (h₂ : Map.contains (Map.mk avs) a = true) :
  Map.contains (Map.mk rty) a = true
:= by
  cases avs <;> cases rty <;> cases h₁
  case nil =>
    simp [Map.contains, Map.find?] at h₂
  case cons ahd atl rhd rtl h₃ h₄ =>
    simp [Map.contains, Map.find?, List.find?] at *
    simp [AttrValueHasAttrType] at h₃
    have ⟨h₃, _⟩ := h₃ ; simp [h₃] at *
    cases h₅ : rhd.fst == a <;> simp [h₅] at *
    cases h₆ : List.find? (fun x => x.fst == a) atl <;> simp [h₆] at h₂
    have h₇ := @mk_vals_instance_of_mk_types₁ env a atl rtl h₄
    simp [Map.contains, Map.find?, Map.toList, h₆] at h₇
    exact h₇

theorem mk_vals_instance_of_mk_types₂ {env : TypeEnv} {a : Attr} {v : Value} {qty : QualifiedType} {avs : List (Attr × Value)} {rtx : List (Attr × QualifiedType)}
  (h₁ : List.Forall₂ (AttrValueHasAttrType (env := env)) avs rtx)
  (h₂ : Map.find? (Map.mk avs) a = some v)
  (h₃ : (Map.mk rtx).find? a = some qty) :
  InstanceOfType env v (Qualified.getType qty)
:= by
  cases avs <;> cases rtx <;> cases h₁
  case nil => simp [Map.find?] at h₂
  case cons ahd atl rhd rtl h₄ h₅ =>
    simp [Map.find?, List.find?] at h₂ h₃
    simp [AttrValueHasAttrType] at h₄
    have ⟨hl₄, hr₄⟩ := h₄ ; simp [hl₄] at *
    cases h₆ : rhd.fst == a <;> simp [h₆] at h₂ h₃
    case true =>
      rw [←h₂, ←h₃]
      exact hr₄
    case false =>
      apply @mk_vals_instance_of_mk_types₂ env a v qty atl rtl h₅ <;>
      simp [Map.find?, Map.toList, h₂, h₃]

theorem mk_vals_instance_of_mk_types₃ {env : TypeEnv} {a : Attr} {qty : QualifiedType} {avs : List (Attr × Value)} {rtx : List (Attr × QualifiedType)}
  (h₁ : List.Forall₂ (AttrValueHasAttrType (env := env)) avs rtx)
  (h₂ : (Map.mk rtx).find? a = some qty) :
  Map.contains (Map.mk avs) a = true
:= by
  cases avs <;> cases rtx <;> cases h₁
  case nil => simp [Map.find?] at h₂
  case cons ahd atl rhd rtl h₄ h₅ =>
    simp [Map.contains, Map.find?, List.find?]
    simp [Map.find?, List.find?] at h₂
    simp [AttrValueHasAttrType] at h₄
    have ⟨h₄, _⟩ := h₄ ; simp [h₄]
    cases h₆ : rhd.fst == a <;> simp [h₆] at h₂ ⊢
    cases h₇ : rtl.find? λ (a', _) => a' == a <;> simp [h₇] at h₂
    have h₈ := @mk_vals_instance_of_mk_types₃ env a qty atl rtl h₅
    simp [Map.find?, Map.toList, h₇, h₂, Map.contains] at h₈
    exact h₈

theorem mk_vals_instance_of_mk_types {env : TypeEnv} {avs : List (Attr × Value)} {rty : List (Attr × QualifiedType)}
  (h₁ : List.Forall₂ (AttrValueHasAttrType (env := env)) avs rty) :
  InstanceOfType env (Value.record (Map.mk avs)) (CedarType.record (Map.mk rty))
:= by
  apply InstanceOfType.instance_of_record
  case h₁ =>
    intro a h₂
    exact mk_vals_instance_of_mk_types₁ h₁ h₂
  case h₂ =>
    intro a v qty h₂ h₃
    exact mk_vals_instance_of_mk_types₂ h₁ h₂ h₃
  case h₃ =>
    intro a qty h₂ _
    exact mk_vals_instance_of_mk_types₃ h₁ h₂

theorem find_mk_xs_find_mk_txs {axs : List (Attr × Expr)} {atxs : List (Attr × TypedExpr)}
  (h₁ : List.Forall₂ (AttrExprHasAttrType c env) axs atxs)
  (h₂ : (Map.mk axs).find? a = some x) :
  ∃ tx c', (Map.mk atxs).find? a = some tx ∧ typeOf x c env = .ok (tx, c')
:= by
  cases axs <;> cases atxs <;> cases h₁
  case nil => simp [Map.find?] at h₂
  case cons axh axt atxh athl h₄ h₅ =>
    simp [Map.find?, List.find?]
    simp [Map.find?, List.find?] at h₂
    simp [AttrExprHasAttrType] at h₄
    replace ⟨h₄, _, h₆⟩ := h₄ ; rw [←h₄]
    cases h₇ : axh.fst == a <;> simp [h₇] at h₂ ⊢
    · cases h₈ : axt.find? λ (a', _) => a' == a <;> simp [h₈] at h₂
      subst h₂
      rename_i ax
      have h₉ := @find_mk_xs_find_mk_txs c env a ax.snd axt athl h₅
      simp [h₈, Map.find?, Map.toList] at h₉
      exact h₉
    · subst h₂
      simp [h₆]

theorem find_make_xs_find_make_txs {axs : List (Attr × Expr)} {atxs : List (Attr × TypedExpr)}
  (h₁ : List.Forall₂ (AttrExprHasAttrType c env) axs atxs)
  (h₂ : (Map.make axs).find? a = some x) :
  ∃ tx c', (Map.make atxs).find? a = some tx ∧ typeOf x c env = .ok (tx, c')
:= by
  apply @find_mk_xs_find_mk_txs _ _ _ _ (List.canonicalize Prod.fst axs)
  · let p := fun (x :  Expr) (tx : TypedExpr) =>
      ∃ c', (typeOf x c env) = Except.ok (tx, c')
    have h₆ := List.canonicalize_preserves_forallᵥ p axs atxs
    simp [p, List.Forallᵥ] at h₆
    apply h₆ h₁
  · simp only [Map.make] at h₂
    exact h₂

theorem head_of_vals_instance_of_head_of_types {xhd : Attr × Expr} {c₁ : Capabilities} {env : TypeEnv} {request : Request} {entities : Entities} {rhd : Attr × TypedExpr} {vhd : Attr × Value}
  (h₁ : TypeOfIsSound xhd.snd)
  (h₂ : CapabilitiesInvariant c₁ request entities)
  (h₃ : InstanceOfWellFormedEnvironment request entities env)
  (h₄ : AttrExprHasAttrType c₁ env xhd rhd)
  (h₅ : bindAttr xhd.fst (evaluate xhd.snd request entities) = Except.ok vhd) :
  AttrValueHasAttrType (env := env) vhd (rhd.fst, .required rhd.snd.typeOf)
:= by
  simp [TypeOfIsSound] at h₁
  replace ⟨h₄, _, h₆⟩ := h₄ ; rw [←h₄]
  specialize h₁ h₂ h₃ h₆
  have ⟨_, v, h₁, h₇⟩ := h₁
  simp [bindAttr] at h₅
  cases h₈ : evaluate xhd.snd request entities <;> simp [h₈] at h₅
  simp [EvaluatesTo, h₈] at h₁ ; subst h₁ h₅
  simp [AttrValueHasAttrType, Qualified.getType, h₇]

theorem vals_instance_of_types {axs : List (Attr × Expr)} {c₁ : Capabilities} {env : TypeEnv} {request : Request} {entities : Entities} {rtx : List (Attr × TypedExpr)} {avs : List (Attr × Value)}
  (ih : ∀ (axᵢ : Attr × Expr), axᵢ ∈ axs → TypeOfIsSound axᵢ.snd)
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : InstanceOfWellFormedEnvironment request entities env)
  (h₃ : List.Forall₂ (AttrExprHasAttrType c₁ env) axs rtx)
  (h₄ : (axs.mapM fun x => bindAttr x.fst (evaluate x.snd request entities)) = Except.ok avs) :
  List.Forall₂ (AttrValueHasAttrType (env := env)) avs (rtx.map λ (a, tx) => (a, .required tx.typeOf))
:= by
  cases h₃
  case nil =>
    simp [←List.mapM'_eq_mapM, pure, Except.pure] at h₄
    subst h₄
    simp [List.map_nil]
  case cons xhd rhd xtl rtl h₅ h₆ =>
    simp [pure, Except.pure] at h₄
    cases h₇ : bindAttr xhd.fst (evaluate xhd.snd request entities) <;> simp [h₇] at h₄
    cases h₈ : List.mapM (fun x => bindAttr x.fst (evaluate x.snd request entities)) xtl <;> simp [h₈] at h₄
    subst h₄
    rename_i vhd vtl
    apply List.Forall₂.cons
    {
      apply head_of_vals_instance_of_head_of_types _ h₁ h₂ h₅ h₇
      apply ih ; simp only [List.mem_cons, true_or]
    }
    {
      apply @vals_instance_of_types xtl c₁ env request entities rtl vtl _ h₁ h₂ h₆ h₈
      intro ax h₉ ; apply ih ; simp [h₉]
    }

theorem type_of_record_is_sound_ok {axs : List (Attr × Expr)} {c₁ : Capabilities} {env : TypeEnv} {request : Request} {entities : Entities} {rtx : List (Attr × TypedExpr)} {avs : List (Attr × Value)}
  (ih : ∀ (axᵢ : Attr × Expr), axᵢ ∈ axs → TypeOfIsSound axᵢ.snd)
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : InstanceOfWellFormedEnvironment request entities env)
  (h₃ : List.Forall₂ (AttrExprHasAttrType c₁ env) axs rtx)
  (h₄ : (axs.mapM fun x => bindAttr x.fst (evaluate x.snd request entities)) = Except.ok avs) :
  InstanceOfType env (Value.record (Map.make avs)) (CedarType.record (Map.make (rtx.map λ (a, tx) => (a, .required tx.typeOf))))
:= by
  apply mk_vals_instance_of_mk_types
  let p := fun (v : Value) (qty : QualifiedType) => InstanceOfType env v qty.getType
  have h₅ := vals_instance_of_types ih h₁ h₂ h₃ h₄
  have h₆ := List.canonicalize_preserves_forallᵥ p avs (rtx.map λ (a, tx) => (a, .required tx.typeOf))
  simp [List.Forallᵥ] at h₆
  exact h₆ h₅

theorem type_of_record_is_sound_err {axs : List (Attr × Expr)} {c₁ : Capabilities} {env : TypeEnv} {request : Request} {entities : Entities} {rtx : List (Attr × TypedExpr)} {err : Error}
  (ih : ∀ (axᵢ : Attr × Expr), axᵢ ∈ axs → TypeOfIsSound axᵢ.snd)
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : InstanceOfWellFormedEnvironment request entities env)
  (h₃ : List.Forall₂ (AttrExprHasAttrType c₁ env) axs rtx)
  (h₄ : (axs.mapM fun x => bindAttr x.fst (evaluate x.snd request entities)) = Except.error err) :
  err = Error.entityDoesNotExist ∨ err = Error.extensionError ∨ err = Error.arithBoundsError
:= by
  cases axs
  case nil =>
    simp only [List.mapM_nil, pure, Except.pure, reduceCtorEq] at h₄
  case cons hd tl =>
    cases h₃ ; rename_i hd' tl' hh₃ ht₃
    simp only [List.mapM_cons] at h₄
    cases h₅ : bindAttr hd.fst (evaluate hd.snd request entities) <;> simp only [h₅] at h₄
    case error e =>
      simp only [bindAttr] at h₅
      simp only [bind_pure_comp, Except.bind_err, Except.error.injEq] at h₄
      cases h₆ : evaluate hd.snd request entities <;> simp [h₆] at h₅
      subst h₄ h₅
      specialize ih hd
      simp only [List.mem_cons, true_or, TypeOfIsSound, forall_const] at ih
      replace ⟨h₄, c', hh₃⟩ := hh₃
      specialize ih h₁ h₂ hh₃
      have ⟨_, v, ih, _⟩ := ih
      simp [EvaluatesTo, h₆] at ih
      exact ih
    case ok vhd =>
      cases h₅ : tl.mapM λ x => bindAttr x.fst (evaluate x.snd request entities) <;> simp [h₅, pure, Except.pure] at h₄
      rw [eq_comm] at h₄ ; subst h₄
      exact @type_of_record_is_sound_err
        tl c₁ env request entities tl' err
        (by intro axᵢ h ; apply ih ; simp [h])
        h₁ h₂ ht₃
        (by simp [h₅])


theorem type_of_record_is_sound {axs : List (Attr × Expr)} {c₁ c₂ : Capabilities} {env : TypeEnv} {tx : TypedExpr} {request : Request} {entities : Entities}
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : InstanceOfWellFormedEnvironment request entities env)
  (h₃ : typeOf (Expr.record axs) c₁ env = Except.ok (tx, c₂))
  (ih : ∀ (axᵢ : Attr × Expr), axᵢ ∈ axs → TypeOfIsSound axᵢ.snd) :
  GuardedCapabilitiesInvariant (Expr.record axs) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.record axs) request entities v ∧ InstanceOfType env v tx.typeOf
:= by
  have ⟨h₆, rty, h₄, h₅⟩ := type_of_record_inversion h₃
  subst h₆ h₄
  apply And.intro empty_guarded_capabilities_invariant
  simp only [EvaluatesTo, evaluate]
  simp only [do_ok_eq_ok, do_error]
  let f := fun (x : Attr × Expr) => bindAttr x.fst (evaluate x.snd request entities)
  rw [List.mapM₂_eq_mapM f]
  cases h₅ : (axs.mapM f) <;> simp
  case error err =>
    rename_i h₄
    simp [type_of_is_inhabited h₂.wf_env h₃]
    exact type_of_record_is_sound_err ih h₁ h₂ h₄ h₅
  case ok avs =>
    rename_i h₄
    exact type_of_record_is_sound_ok ih h₁ h₂ h₄ h₅

/- Used by `type_of_preserves_evaluation_results` -/
theorem type_of_ok_list {c₁ env xs ys request entities} :
  List.Forall₂ (fun x y => justType (typeOf x c₁ env) = Except.ok y) xs ys →
  (∀ (x₁ : Expr),
    x₁ ∈ xs →
      ∀ {c₂ : Capabilities} {ty : TypedExpr},
        typeOf x₁ c₁ env = Except.ok (ty, c₂) → evaluate x₁ request entities = evaluate ty.toExpr request entities) →
  List.Forall₂ (fun x y => evaluate x request entities = evaluate y.toExpr request entities) xs ys
:= by
  intro h₁ h₂
  cases h₁
  case nil => simp only [List.Forall₂.nil]
  case cons x y xs ys h₃ h₄ =>
    constructor
    · simp [justType, Except.map] at h₃
      split at h₃ <;> cases h₃
      rename_i heq
      have : x ∈ x :: xs := by simp only [List.mem_cons, true_or]
      specialize h₂ x this heq
      exact h₂
    · have : ∀ (x₁ : Expr),
        x₁ ∈ xs →
          ∀ {c₂ : Capabilities} {ty : TypedExpr},
            typeOf x₁ c₁ env = Except.ok (ty, c₂) → evaluate x₁ request entities = evaluate ty.toExpr request entities := by
        intro x₁ hᵢ c₂ ty
        have : x₁ ∈ x :: xs := by simp only [List.mem_cons, hᵢ, or_true]
        exact h₂ x₁ this
      exact type_of_ok_list h₄ this

end Cedar.Thm
