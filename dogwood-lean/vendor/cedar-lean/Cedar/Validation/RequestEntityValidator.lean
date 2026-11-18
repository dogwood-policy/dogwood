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

import Cedar.Data.SizeOf
import Cedar.Thm.Data.Map -- `Map.toList_mk_id` needed in a termination proof
import Cedar.Validation.Validator
public import Cedar.Validation.Typechecker
public import Lean.Data.Json.Basic
public import Lean.Data.Json.FromToJson.Basic

/-! This file includes boolean definitions for the propositions declared in `Cedar/Thm/Validation/Typechecker/Types.lean`. -/

namespace Cedar.Validation

open Cedar.Spec
open Cedar.Data

public inductive RequestValidationError where
| typeError (msg : String)

public abbrev RequestValidationResult := Except RequestValidationError Unit

public inductive EntityValidationError where
| typeError (msg : String)

public abbrev EntityValidationResult := Except EntityValidationError Unit

public def instanceOfBoolType (b : Bool) (bty : BoolType) : Bool :=
  match b, bty with
  | true, .tt => true
  | false, .ff => true
  | _, .anyBool => true
  | _, _ => false

public def instanceOfEntityType (e : EntityUID) (ety : EntityType) (schema : Schema) : Bool :=
  ety == e.ty &&
  (schema.ets.isValidEntityUID e || schema.acts.contains e)

public def instanceOfExtType (ext : Ext) (extty: ExtType) : Bool :=
match ext, extty with
  | .decimal _, .decimal => true
  | .ipaddr _, .ipAddr => true
  | .datetime _, .datetime => true
  | .duration _, .duration => true
  | _, _ => false

public def requiredAttributePresent (r : Map Attr Value) (rty : Map Attr (Qualified CedarType)) (k : Attr) :=
match rty.find? k with
    | .some qty => if qty.isRequired then r.contains k else true
    | _ => true

public def instanceOfType (v : Value) (ty : CedarType) (schema : Schema) : Bool :=
  match v, ty with
  | .prim (.bool b), .bool bty => instanceOfBoolType b bty
  | .prim (.int _), .int => true
  | .prim (.string _), .string => true
  | .prim (.entityUID e), .entity ety => instanceOfEntityType e ety schema
  | .set s, .set ty => s.all₁ (λ ⟨v, _⟩ => instanceOfType v ty schema)
  | .record r, .record rty =>
    r.toList.all (λ (k, _) => rty.contains k) &&
    (r.toList.attach₂.all (λ ⟨(k, v), _⟩ => (match rty.find? k with
        | .some qty => instanceOfType v qty.getType schema
        | _ => true))) &&
    rty.toList.all (λ (k, _) => requiredAttributePresent r rty k)
  | .ext x, .ext xty => instanceOfExtType x xty
  | _, _ => false
    termination_by v
    decreasing_by
      all_goals simp_wf
      case _ h₁ =>
        have := Set.sizeOf_lt_of_mem h₁
        omega
      case _ h₁ =>
        cases r
        simp only [Map.toList_mk_id, Map.mk.sizeOf_spec] at *
        omega

public def instanceOfRequestType (request : Request) (env : TypeEnv) : Bool :=
  instanceOfEntityType request.principal env.reqty.principal env.schema &&
  request.action == env.reqty.action &&
  instanceOfEntityType request.resource env.reqty.resource env.schema &&
  instanceOfType request.context (.record env.reqty.context) env.schema

/--
For every entity in the store,
1. The entity's type is defined in the type store (either `ets` or `as` for action entities).
2. The entity's attributes match the attribute types indicated in the type store.
3. The entity's ancestors' types are consistent with the ancestor information
   in the type store.
4. The entity's tags' types are consistent with the tags information in the type store.

For every action in the entity store, the action's ancestors are consistent
with the ancestor information in the action store.
-/
@[expose]
public def instanceOfSchema (entities : Entities) (env : TypeEnv) : EntityValidationResult :=
  do
    entities.toList.forM λ (uid, data) => instanceOfSchemaEntry uid data
    env.acts.toList.forM λ (uid, _) => actionExists uid
where
  instanceOfEntityTags (data : EntityData) (entry : EntitySchemaEntry) : Bool :=
    match entry.tags? with
    | .some tty => data.tags.values.all (instanceOfType · tty env.schema)
    | .none     => data.tags == Map.empty
  instanceOfEntitySchemaEntry uid data entry :=
    if entry.isValidEntityEID uid.eid then
      if instanceOfType data.attrs (.record entry.attrs) env.schema then
        if data.ancestors.all (λ ancestor =>
          entry.ancestors.contains ancestor.ty &&
          instanceOfEntityType ancestor ancestor.ty env.schema) then
          if instanceOfEntityTags data entry then .ok ()
          else .error (.typeError s!"entity tags inconsistent with type store")
        else .error (.typeError s!"entity ancestors inconsistent with type store")
      else .error (.typeError "entity attributes do not match type store")
    else .error (.typeError s!"invalid entity uid: {uid}")
  instanceOfActionSchemaEntry uid data :=
    if data.attrs == Map.empty then
      if data.tags == Map.empty then
        match env.acts.find? uid with
        | .some entry =>
          if data.ancestors == entry.ancestors then .ok ()
          else .error (.typeError s!"action entity {uid} ancestors inconsistent with schema")
        | _ => .error (.typeError "entity type not defined in type store")
      else .error (.typeError s!"action entitiy {uid} cannot have tags")
    else .error (.typeError s!"action entitiy {uid} cannot have attributes")
  instanceOfSchemaEntry uid data :=
    match env.ets.find? uid.ty with
    |  .some entry => instanceOfEntitySchemaEntry uid data entry
    | _ => instanceOfActionSchemaEntry uid data
  actionExists uid :=
    if entities.contains uid then .ok ()
    else .error (.typeError s!"action entity {uid} does not exist")

public def requestMatchesEnvironment (env : TypeEnv) (request : Request) : Bool := instanceOfRequestType request env

public def validateRequest (schema : Schema) (request : Request) : RequestValidationResult :=
  if ((schema.environments.any (requestMatchesEnvironment · request)))
  then .ok ()
  else .error (.typeError "request could not be validated in any environment")

public def entitiesMatchEnvironment (env : TypeEnv) (entities : Entities) : EntityValidationResult :=
  instanceOfSchema entities env

public def actionSchemaEntryToEntityData (ase : ActionSchemaEntry) : EntityData := {
  ancestors := ase.ancestors,
  attrs := Map.empty,
  tags := Map.empty
}

public def validateEntities (schema : Schema) (entities : Entities) : EntityValidationResult :=
  schema.environments.forM (entitiesMatchEnvironment · entities)

-- json

public def entityValidationErrorToJson : EntityValidationError → Lean.Json
  | .typeError x => x

public instance : Lean.ToJson EntityValidationError where
  toJson := entityValidationErrorToJson

public def requestValidationErrorToJson : RequestValidationError → Lean.Json
  | .typeError x => x

public instance : Lean.ToJson RequestValidationError where
  toJson := requestValidationErrorToJson


end Cedar.Validation
