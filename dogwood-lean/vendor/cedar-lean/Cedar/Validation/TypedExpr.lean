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

module

public import Cedar.Spec
public import Cedar.Validation.Types

/-!
This file defines a type annotated version of the Cedar AST
-/

namespace Cedar.Validation

open Cedar.Data
open Cedar.Spec

/--
A type annotated Cedar AST. This should have exactly the same variants as the
unannotated `Expr` data type, but each variant carries an additional `ty` that
stores the type of the expression.
-/
public inductive TypedExpr where
  | lit (p : Prim) (ty : CedarType)
  | var (v : Var) (ty : CedarType)
  | ite (cond : TypedExpr) (thenExpr : TypedExpr) (elseExpr : TypedExpr) (ty : CedarType)
  | and (a : TypedExpr) (b : TypedExpr) (ty : CedarType)
  | or (a : TypedExpr) (b : TypedExpr) (ty : CedarType)
  | unaryApp (op : UnaryOp) (expr : TypedExpr) (ty : CedarType)
  | binaryApp (op : BinaryOp) (a : TypedExpr) (b : TypedExpr) (ty : CedarType)
  | getAttr (expr : TypedExpr) (attr : Attr) (ty : CedarType)
  | hasAttr (expr : TypedExpr) (attr : Attr) (ty : CedarType)
  | extHasAttr (expr : TypedExpr) (attr : Attr) (attrs : List Attr) (ty : CedarType)
  | set (ls : List TypedExpr) (ty : CedarType)
  | record (map : List (Attr × TypedExpr)) (ty : CedarType)
  | call (xfn : ExtFun) (args : List TypedExpr) (ty : CedarType)


deriving instance Repr, Inhabited for TypedExpr

mutual

public def decTypedExpr (x y : TypedExpr) : Decidable (x = y) := by
  cases x <;> cases y <;>
  try { apply isFalse ; intro h ; injection h }
  case lit.lit x₁ tx  y₁ ty  | var.var x₁ tx y₁ ty =>
    exact match decEq x₁ y₁, decEq tx ty with
    | isTrue h₁, isTrue h₂ => isTrue (by rw [h₁, h₂])
    | isFalse _, _  | _, isFalse _ => isFalse (by intro h; injection h; contradiction)
  case ite.ite x₁ x₂ x₃ tx y₁ y₂ y₃ ty =>
    exact match decTypedExpr x₁ y₁, decTypedExpr x₂ y₂, decTypedExpr x₃ y₃, decEq tx ty with
    | isTrue h₁, isTrue h₂, isTrue h₃, isTrue h₄ => isTrue (by rw [h₁, h₂, h₃, h₄])
    | isFalse _, _, _, _ | _, isFalse _, _, _ | _, _, isFalse _, _ | _, _, _, isFalse _ => isFalse (by intro h; injection h; contradiction)
  case and.and x₁ x₂ tx y₁ y₂ ty | or.or x₁ x₂ tx y₁ y₂ ty =>
    exact match decTypedExpr x₁ y₁, decTypedExpr x₂ y₂, decEq tx ty with
    | isTrue h₁, isTrue h₂, isTrue h₃ => isTrue (by rw [h₁, h₂, h₃])
    | isFalse _, _, _ | _, isFalse _, _ | _, _, isFalse _ => isFalse (by intro h; injection h; contradiction)
  case unaryApp.unaryApp o x₁ tx o' y₁ ty =>
    exact match decEq o o', decTypedExpr x₁ y₁, decEq tx ty with
    | isTrue h₁, isTrue h₂, isTrue h₃ => isTrue (by rw [h₁, h₂, h₃])
    | isFalse _, _, _ | _, isFalse _, _ | _, _, isFalse _ => isFalse (by intro h; injection h; contradiction)
  case binaryApp.binaryApp o x₁ x₂ tx o' y₁ y₂ ty =>
    exact match decEq o o', decTypedExpr x₁ y₁, decTypedExpr x₂ y₂, decEq tx ty with
    | isTrue h₁, isTrue h₂, isTrue h₃, isTrue h₄ => isTrue (by rw [h₁, h₂, h₃, h₄])
    | isFalse _, _, _, _ | _, isFalse _, _, _ | _, _, isFalse _, _ | _, _, _, isFalse _ => isFalse (by intro h; injection h; contradiction)
  case getAttr.getAttr x₁ a tx y₁ a' ty | hasAttr.hasAttr x₁ a tx y₁ a' ty =>
    exact match decTypedExpr x₁ y₁, decEq a a', decEq tx ty with
    | isTrue h₁, isTrue h₂, isTrue h₃ => isTrue (by rw [h₁, h₂, h₃])
    | isFalse _, _, _ | _, isFalse _, _ | _, _, isFalse _ => isFalse (by intro h; injection h; contradiction)
  case extHasAttr.extHasAttr x₁ a as tx y₁ a' as' ty =>
    exact match decTypedExpr x₁ y₁, decEq a a', decEq as as', decEq tx ty with
    | isTrue h₁, isTrue h₂, isTrue h₃, isTrue h₄ => isTrue (by rw [h₁, h₂, h₃, h₄])
    | isFalse _, _, _, _ | _, isFalse _, _, _ | _, _, isFalse _, _ | _, _, _, isFalse _ => isFalse (by intro h; injection h; contradiction)
  case set.set xs tx ys ty =>
    exact match decExprList xs ys, decEq tx ty with
    | isTrue h₁, isTrue h₂ => isTrue (by rw [h₁, h₂])
    | isFalse _, _ | _, isFalse _ => isFalse (by intro h; injection h; contradiction)
  case record.record axs tx ays ty =>
    exact match decProdAttrExprList axs ays, decEq tx ty with
    | isTrue h₁, isTrue h₂ => isTrue (by rw [h₁, h₂])
    | isFalse _, _ | _, isFalse _ => isFalse (by intro h; injection h; contradiction)
  case call.call f xs tx f' ys ty =>
    exact match decEq f f', decExprList xs ys, decEq tx ty with
    | isTrue h₁, isTrue h₂, isTrue h₃ => isTrue (by rw [h₁, h₂, h₃])
    | isFalse _, _, _ | _, isFalse _, _ | _, _, isFalse _ => isFalse (by intro h; injection h; contradiction)

def decProdAttrExprList (axs ays : List (Prod Attr TypedExpr)) : Decidable (axs = ays) :=
  match axs, ays with
  | [], [] => isTrue rfl
  | _::_, [] | [], _::_ => isFalse (by intro; contradiction)
  | (a, x)::axs, (a', y)::ays =>
    match decEq a a', decTypedExpr x y, decProdAttrExprList axs ays with
    | isTrue h₁, isTrue h₂, isTrue h₃ => isTrue (by rw [h₁, h₂, h₃])
    | isFalse _, _, _ | _, isFalse _, _ | _, _, isFalse _ =>
      isFalse (by simp; intros; first | contradiction | assumption)

def decExprList (xs ys : List TypedExpr) : Decidable (xs = ys) :=
  match xs, ys with
  | [], [] => isTrue rfl
  | _::_, [] | [], _::_ => isFalse (by intro; contradiction)
  | x::xs, y::ys =>
    match decTypedExpr x y, decExprList xs ys with
    | isTrue h₁, isTrue h₂ => isTrue (by rw [h₁, h₂])
    | isFalse _, _ | _, isFalse _ => isFalse (by intro h; injection h; contradiction)
end

public instance : DecidableEq TypedExpr := decTypedExpr

public def TypedExpr.typeOf : TypedExpr → CedarType
  | lit _ ty
  | var _ ty
  | ite _ _ _ ty
  | and _ _ ty
  | or _ _ ty
  | unaryApp _ _ ty
  | binaryApp _ _ _ ty
  | getAttr _ _ ty
  | hasAttr _ _ ty
  | extHasAttr _ _ _ ty
  | set _ ty
  | record _ ty
  | call _ _ ty => ty

public def TypedExpr.toExpr : TypedExpr → Expr
  | lit p _ => Expr.lit p
  | var v _ => Expr.var v
  | ite cond thenExpr elseExpr _ => Expr.ite cond.toExpr thenExpr.toExpr elseExpr.toExpr
  | and a b _ => Expr.and a.toExpr b.toExpr
  | or a b _ => Expr.or a.toExpr b.toExpr
  | unaryApp op expr _ => Expr.unaryApp op expr.toExpr
  | binaryApp op a b _ => Expr.binaryApp op a.toExpr b.toExpr
  | getAttr expr attr _ => Expr.getAttr expr.toExpr attr
  | hasAttr expr attr _ => Expr.hasAttr expr.toExpr attr
  | extHasAttr expr attr attrs _ => Expr.extHasAttr expr.toExpr attr attrs
  | set ls _ => Expr.set $ ls.map₁ (λ ⟨e, _⟩  => e.toExpr)
  | record ls _ => Expr.record $ ls.map₂ (λ ⟨(a, e), _⟩  => (a, e.toExpr))
  | call xfn args _ => Expr.call xfn $ args.map₁ (λ ⟨e, _⟩ => e.toExpr)
decreasing_by
  all_goals (simp_wf ; try omega)
  all_goals
    rename_i h
    try simp at h
    try replace h := List.sizeOf_lt_of_mem h
    omega

public def TypedExpr.liftBoolTypes : TypedExpr → TypedExpr
  | .lit p ty => .lit p ty.liftBoolTypes
  | .var v ty =>  .var v ty.liftBoolTypes
  | .ite cond thenExpr elseExpr ty => .ite cond.liftBoolTypes thenExpr.liftBoolTypes elseExpr.liftBoolTypes ty.liftBoolTypes
  | .and a b ty => .and a.liftBoolTypes b.liftBoolTypes ty.liftBoolTypes
  | .or a b ty => .or a.liftBoolTypes b.liftBoolTypes ty.liftBoolTypes
  | .unaryApp op expr ty => .unaryApp op expr.liftBoolTypes ty.liftBoolTypes
  | .binaryApp op a b ty => .binaryApp op a.liftBoolTypes b.liftBoolTypes ty.liftBoolTypes
  | .getAttr expr attr ty => .getAttr expr.liftBoolTypes attr ty.liftBoolTypes
  | .hasAttr expr attr ty => .hasAttr expr.liftBoolTypes attr ty.liftBoolTypes
  | .extHasAttr expr attr attrs ty => .extHasAttr expr.liftBoolTypes attr attrs ty.liftBoolTypes
  | .set ls ty => .set (ls.map₁ (λ ⟨e, _⟩ => e.liftBoolTypes)) ty.liftBoolTypes
  | .record ls ty => .record (ls.map₂ (λ ⟨(a, e), _⟩ => (a, e.liftBoolTypes))) ty.liftBoolTypes
  | .call xfn args ty => .call xfn (args.map₁ (λ ⟨e, _⟩ => e.liftBoolTypes)) ty.liftBoolTypes
decreasing_by
  all_goals (simp_wf ; try omega)
  all_goals
    rename_i h
    try simp at h
    try replace h := List.sizeOf_lt_of_mem h
    omega

end Cedar.Validation
