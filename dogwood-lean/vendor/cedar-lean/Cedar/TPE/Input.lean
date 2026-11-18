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

import Cedar.Spec.Expr
import Cedar.Spec.Request
import Cedar.Spec.Value
import Cedar.Validation.RequestEntityValidator
import Cedar.Validation.EnvironmentValidator
import Cedar.Validation.TypedExpr

namespace Cedar.TPE

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

structure PartialEntityUID where
  ty : EntityType
  id : Option String
deriving Inhabited

def PartialEntityUID.asEntityUID (self : PartialEntityUID) : Option EntityUID :=
  self.id.map (⟨self.ty, ·⟩)

structure PartialRequest where
  principal : PartialEntityUID
  action    : EntityUID
  resource  : PartialEntityUID
  -- We don't need type annotation here because the value of `context` can only
  -- be accessed via evaluating a `TypedExpr`, which allows us to obtain a
  -- (typed) `Residual`
  context   : Option (Map Attr Value)
deriving Inhabited


-- We don't need type annotations here following the rationale above
structure PartialEntityData where
  attrs     : Option (Map Attr Value)
  ancestors : Option (Set EntityUID)
  tags      : Option (Map Attr Value)
deriving Inhabited

abbrev MaybeEntityData := Option EntityData

abbrev PartialEntities := Map EntityUID PartialEntityData

deriving instance Inhabited for PartialEntities

/--
A subset of an Entities store.
When a `MaybeEntityData` is `none`, it means that the entity is not present in
the backing store.
-/
abbrev SlicedEntities := Map EntityUID MaybeEntityData



def PartialEntities.get (es : PartialEntities) (uid : EntityUID) (f : PartialEntityData → Option α) : Option α :=
  (es.find? uid).bind f

def PartialEntities.ancestors (es : PartialEntities) (uid : EntityUID) : Option (Set EntityUID) := es.get uid PartialEntityData.ancestors

def PartialEntities.tags (es : PartialEntities) (uid : EntityUID) : Option (Map Tag Value) := es.get uid PartialEntityData.tags

def PartialEntities.attrs (es : PartialEntities) (uid : EntityUID) : Option (Map Tag Value) := es.get uid PartialEntityData.attrs



def partialIsValid {α} (o : Option α) (f : α → Bool) : Bool :=
  (o.map f).getD true

def requestIsValid (env : TypeEnv) (req : PartialRequest) : Bool :=
  (partialIsValid req.principal.asEntityUID λ principal =>
    instanceOfEntityType principal env.reqty.principal env.schema) &&
  req.action == env.reqty.action &&
  (partialIsValid req.resource.asEntityUID λ resource =>
    instanceOfEntityType resource env.reqty.resource env.schema) &&
  (partialIsValid req.context λ m =>
    instanceOfType (.record m) (.record env.reqty.context) env.schema)

def validatePartialRequest (schema : Schema) (req : PartialRequest) : Except RequestValidationError TypeEnv :=
  match schema.environment? req.principal.ty req.resource.ty req.action with
  | .some env =>
    if requestIsValid env req
    then .ok env
    else .error (.typeError "partial request is inconsistent with the type store")
  | .none => .error (.typeError "partial request does not match any environment")

def entitiesIsValid (schema : Schema) (es : PartialEntities) : Bool :=
  (es.toList.all entityIsValid) && (schema.acts.toList.all instanceOfActionSchema)
where
  actionEntityIsValid uid entityData : Bool :=
    match schema.acts.find? uid with
    | .some actionEntry =>
      (partialIsValid entityData.ancestors (actionEntry.ancestors == ·)) &&
      (partialIsValid entityData.attrs (instanceOfType · (.record Map.empty) schema)) &&
      (partialIsValid entityData.tags (· == Map.empty))
    | .none             => false
  entityIsValid p :=
    let (uid, entityData) := p
    let (attrs, ancestors, tags) := (entityData.attrs, entityData.ancestors, entityData.tags)
    match schema.ets.find? uid.ty with
    | .some entry =>
      entry.isValidEntityEID uid.eid &&
      (partialIsValid ancestors λ ancestors =>
        ancestors.all (λ ancestor =>
        entry.ancestors.contains ancestor.ty &&
        instanceOfEntityType ancestor ancestor.ty schema)) &&
      (partialIsValid attrs (instanceOfType · (.record entry.attrs) schema)) &&
      (partialIsValid tags λ tags =>
        match entry.tags? with
        | .some tty => tags.values.all (instanceOfType · tty schema)
        | .none     => tags == Map.empty)
    | .none => actionEntityIsValid uid entityData
  instanceOfActionSchema p :=
    let (uid, _) := p
    match es.find? uid with
    | .some entry₁ => actionEntityIsValid uid entry₁
    | _            => true

/-- Every known component of `req₂` agrees with `req₁`. -/
def requestIsConsistent (req₁ : Request) (req₂ : PartialRequest) : Bool :=
  let ⟨p₁, a₁, r₁, c₁⟩ := req₁
  let ⟨p₂, a₂, r₂, c₂⟩ := req₂
  p₂.ty = p₁.ty &&
  r₂.ty = r₁.ty &&
  partialIsValid p₂.asEntityUID (· = p₁) &&
  a₁ = a₂ &&
  partialIsValid r₂.asEntityUID (· = r₁) &&
  partialIsValid c₂ (· = c₁)

/-- Every entity of `es₂` is in `es₁`, and every known component of it agrees with `es₁`. -/
def entitiesIsConsistent (es₁ : Entities) (es₂ : PartialEntities) : Bool :=
  es₂.toList.all λ (a₂, e₂) => match es₁.find? a₂ with
    | .some e₁ =>
      let ⟨attrs₁, ancestors₁, tags₁⟩ := e₁
      partialIsValid e₂.attrs (· = attrs₁) &&
      partialIsValid e₂.ancestors (· = ancestors₁) &&
      partialIsValid e₂.tags (· = tags₁)
    | .none => false

inductive ConcretizationError
  | typeError
  | requestsDoNotMatch
  | entitiesDoNotMatch
  | invalidEnvironment

def isValidAndConsistent (schema : Schema) (req₁ : Request) (es₁ : Entities) (req₂ : PartialRequest) (es₂ : PartialEntities) : Except ConcretizationError Unit :=
  match validatePartialRequest schema req₂ with
  | .ok env => do requestIsValidAndConsistent env; entitiesIsValidAndConsistent env; envIsWellFormed env
  | .error _ => .error .invalidEnvironment
where
  requestIsValidAndConsistent env :=
  if !requestMatchesEnvironment env req₁
  then
    .error .typeError
  else
    if requestIsConsistent req₁ req₂
    then
      .ok ()
    else
      .error .requestsDoNotMatch
  entitiesIsValidAndConsistent env : Except ConcretizationError Unit :=
    if !entitiesIsValid env.schema es₂ || !(entitiesMatchEnvironment env es₁).isOk
    then
      .error .typeError
    else
      if entitiesIsConsistent es₁ es₂ then
        .ok ()
      else
        .error .entitiesDoNotMatch
  envIsWellFormed env : Except ConcretizationError Unit :=
    if !env.validateWellFormed.isOk
    then
      .error .typeError
    else
      .ok ()


end Cedar.TPE

namespace Cedar.Spec

open Cedar.Data
open Cedar.Spec
open Cedar.Validation
open Cedar.TPE

def Request.asPartialRequest (req : Request) : PartialRequest :=
  { principal := { ty := req.principal.ty, id := .some req.principal.eid }
  , action    := req.action
  , resource  := { ty := req.resource.ty, id := .some req.resource.eid }
  , context   := req.context }

open Cedar.TPE

def EntityData.asPartial (data : EntityData) : PartialEntityData :=
  { attrs := (.some data.attrs)
  , ancestors := (.some data.ancestors)
  , tags := (.some data.tags)}

def Entities.asPartial (entities: Entities) : PartialEntities :=
  entities.mapOnValues EntityData.asPartial


end Cedar.Spec


namespace Cedar.TPE
open Cedar.Data

/-- subtle: a missing entity bahaves the same way as a concrete entity
with empty attrs, ancestors, and tags.
This is because
1. Cedar doesn't have a way to check for a presence of a particular entity id in the database.
2. Each of the cedar operations behave the same way when encountering a missing entity compared to a empty one.

This is a necessary condition for the soundness of batched entity loading.
-/
def MaybeEntityData.asPartial :
  MaybeEntityData → PartialEntityData
| none =>
  { attrs :=  (.some Map.empty)
  , ancestors := (.some Set.empty)
  , tags := (.some Map.empty)}
| some d =>
  d.asPartial

def EntitiesWithMissing.asPartial (store: SlicedEntities) : PartialEntities :=
  store.mapOnValues MaybeEntityData.asPartial

end Cedar.TPE
