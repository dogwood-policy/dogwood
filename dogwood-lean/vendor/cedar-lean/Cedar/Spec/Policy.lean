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

public import Cedar.Spec.Expr

/-! This file defines abstract syntax for Cedar policies. -/

namespace Cedar.Spec

----- Definitions -----

public inductive Effect where
  | permit
  | forbid

public inductive Scope where
  | any
  | eq (entity : EntityUID)
  | mem (entity : EntityUID)
  | is (ety : EntityType)
  | isMem (ety : EntityType) (entity : EntityUID)

public inductive PrincipalScope where
  | principalScope (scope : Scope)

public inductive ResourceScope where
  | resourceScope (scope : Scope)

/--
This definition of the ActionScope is more liberal than what is allowed by
Cedar's concrete grammar. In particular, the concrete grammar doesn't allow `is`
constraints in action scopes (e.g., `action is ety`), while our abstract grammar
does. Restricting action scopes in this way is not necessary for proving any
properties of Cedar; it is done in the concrete grammar for usability (since
`is` constraints on actions can be expressed using groups instead). We're
choosing the more liberal modeling here for uniformity and simplicity.
-/
public inductive ActionScope where
  | actionScope (scope : Scope)
  | actionInAny (ls : List EntityUID)

public abbrev PolicyID := String

public inductive ConditionKind where
  | when
  | unless

public structure Condition where
  kind : ConditionKind
  body : Expr

public abbrev Conditions := List Condition

public structure Policy where
  id : PolicyID
  effect : Effect
  principalScope : PrincipalScope
  actionScope : ActionScope
  resourceScope : ResourceScope
  condition : Conditions

public abbrev Policies := List Policy

public def PrincipalScope.scope : PrincipalScope → Scope
  | .principalScope s => s

public def ResourceScope.scope : ResourceScope → Scope
  | .resourceScope s => s

public def Var.eqEntityUID (v : Var) (uid : EntityUID) : Expr :=
  .binaryApp .eq (.var v) (.lit (.entityUID uid))

public def Var.inEntityUID (v : Var) (uid : EntityUID) : Expr :=
  .binaryApp .mem (.var v) (.lit (.entityUID uid))

public def Var.isEntityType (v : Var) (ety : EntityType) : Expr :=
  .unaryApp (.is ety) (.var v)

public def Scope.toExpr (s : Scope) (v : Var) : Expr :=
  match s with
  | .any           => .lit (.bool true)
  | .eq uid        => v.eqEntityUID uid
  | .mem uid       => v.inEntityUID uid
  | .is ety        => v.isEntityType ety
  | .isMem ety uid => .and (v.isEntityType ety) (v.inEntityUID uid)

public def PrincipalScope.toExpr : PrincipalScope → Expr
  | .principalScope s => s.toExpr .principal

public def ResourceScope.toExpr : ResourceScope → Expr
  | .resourceScope s => s.toExpr .resource

public def ActionScope.toExpr : ActionScope → Expr
  | .actionScope s => s.toExpr .action
  | .actionInAny es =>
    let exprs := es.map (fun e => .lit (.entityUID e))
    .binaryApp (.mem) (.var .action) (.set exprs)

public def Condition.toExpr (c : Condition) : Expr :=
  match c.kind with
  | .when => c.body
  | .unless => Expr.unaryApp .not c.body

-- Conditions are evaluated top to bottom, and short circuit
public def Conditions.toExpr (cs : Conditions) : Expr :=
  match cs.reverse with
  | [] => Expr.lit (Prim.bool true)
  | c :: cs => cs.foldl (λ expr c => .and (c.toExpr) expr) c.toExpr

@[expose]
public def Policy.toExpr (p : Policy) : Expr :=
  .and
    p.principalScope.toExpr
    (.and
      p.actionScope.toExpr
      (.and
        p.resourceScope.toExpr
        p.condition.toExpr))

public def Scope.bound : Scope → Option EntityUID
  | .eq uid      => .some uid
  | .mem uid     => .some uid
  | .isMem _ uid => .some uid
  | _            => .none

/-- The trivial allow-all policy -/
public def Policy.allowAll : Policy := {
    id             := "allowAll",
    effect         := .permit,
    principalScope := .principalScope .any,
    actionScope    := .actionScope .any,
    resourceScope  := .resourceScope .any,
    condition      := []
}

----- Derivations -----

deriving instance Repr, DecidableEq, Inhabited for Effect
deriving instance Repr, DecidableEq, Inhabited for ConditionKind
deriving instance Repr, DecidableEq, Inhabited for Condition
deriving instance Repr, DecidableEq, Inhabited for Scope
deriving instance Repr, DecidableEq, Inhabited for PrincipalScope
deriving instance Repr, DecidableEq, Inhabited for ResourceScope
deriving instance Repr, DecidableEq, Inhabited for ActionScope
deriving instance Repr, DecidableEq, Inhabited for Policy

deriving instance Lean.ToJson for PolicyID

end Cedar.Spec
