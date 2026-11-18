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

public import Cedar.Validation.TypedExpr
public import Cedar.Spec.Ext

/-!
This file contains well-typedness definitions of `TypedExpr`
-/

namespace Cedar.Spec

open Cedar.Validation
open Cedar.Spec.Ext

public inductive Prim.WellTyped (env : TypeEnv) : Prim → CedarType → Prop
  | bool (b : Bool) :
    WellTyped env (.bool b) (.bool .anyBool)
  | int (i : Int64) :
    WellTyped env (.int i) .int
  | string (s : String) :
    WellTyped env (.string s) .string
  | entityUID (uid : EntityUID)
    (h₁ : env.ets.isValidEntityUID uid ∨ env.acts.contains uid) :
    WellTyped env (.entityUID uid) (.entity uid.ty)

public inductive Var.WellTyped (env : TypeEnv) : Var → CedarType → Prop
  | principal :
    WellTyped env .principal (.entity env.reqty.principal)
  | resource :
    WellTyped env .resource (.entity env.reqty.resource)
  | action :
    WellTyped env .action (.entity env.reqty.action.ty)
  | context:
    WellTyped env .context (CedarType.liftBoolTypes (.record env.reqty.context))

public inductive UnaryOp.WellTyped : UnaryOp → TypedExpr → CedarType → Prop
  | not {x₁ : TypedExpr}
    (h₁ : x₁.typeOf = .bool .anyBool) :
    WellTyped .not x₁ (.bool .anyBool)
  | neg {x₁ : TypedExpr}
    (h₁ : x₁.typeOf = .int) :
    WellTyped .neg x₁ .int
  | isEmpty {x₁ : TypedExpr} {eltTy : CedarType}
    (h₁ : x₁.typeOf = .set eltTy) :
    WellTyped .isEmpty x₁ (.bool .anyBool)
  | like {x₁ : TypedExpr} {p : Pattern}
    (h₁ : x₁.typeOf = .string) :
    WellTyped (.like p) x₁ (.bool .anyBool)
  | is {ety₁ ety₂ : EntityType}
    (h₁ : x₁.typeOf = .entity ety₂) :
    WellTyped (.is ety₁) x₁ (.bool .anyBool)

public inductive BinaryOp.WellTyped (env : TypeEnv) : BinaryOp → TypedExpr → TypedExpr → CedarType → Prop
  | eq_lit {p₁ p₂ : Prim} {ty₁ ty₂ : CedarType} :
    -- do we need hypothesis like `InstanceOfType (.prim p₁) ty₁`?
    WellTyped env .eq (.lit p₁ ty₁) (.lit p₂ ty₂) (.bool .anyBool)
  | eq_entity {ety₁ ety₂ : EntityType} {x₁ x₂ : TypedExpr}
    (h₁ : x₁.typeOf = .entity ety₁)
    (h₂ : x₂.typeOf = .entity ety₂) :
    WellTyped env .eq x₁ x₂ (.bool .anyBool)
  | eq {x₁ x₂ : TypedExpr}
    (h₁ : x₁.typeOf = x₂.typeOf) :
    WellTyped env .eq x₁ x₂ (.bool .anyBool)
  | memₑ {x₁ x₂ : TypedExpr} {ety₁ ety₂ : EntityType}
    (h₁ : x₁.typeOf = .entity ety₁)
    (h₂ : x₂.typeOf = .entity ety₂) :
    WellTyped env .mem x₁ x₂ (.bool .anyBool)
  | memₛ {x₁ x₂ : TypedExpr} {ety₁ ety₂ : EntityType}
    (h₁ : x₁.typeOf = .entity ety₁)
    (h₂ : x₂.typeOf = .set (.entity ety₂)) :
    WellTyped env .mem x₁ x₂ (.bool .anyBool)
  | less_int {x₁ x₂ : TypedExpr}
    (h₁ : x₁.typeOf = .int)
    (h₂ : x₂.typeOf = .int) :
    WellTyped env .less x₁ x₂ (.bool .anyBool)
  | less_datetime {x₁ x₂ : TypedExpr}
    (h₁ : x₁.typeOf = .ext .datetime)
    (h₂ : x₂.typeOf = .ext .datetime) :
    WellTyped env .less x₁ x₂ (.bool .anyBool)
  | less_duration {x₁ x₂ : TypedExpr}
    (h₁ : x₁.typeOf = .ext .duration)
    (h₂ : x₂.typeOf = .ext .duration) :
    WellTyped env .less x₁ x₂ (.bool .anyBool)
  | lessEq_int {x₁ x₂ : TypedExpr}
    (h₁ : x₁.typeOf = .int)
    (h₂ : x₂.typeOf = .int) :
    WellTyped env .lessEq x₁ x₂ (.bool .anyBool)
  | lessEq_datetime {x₁ x₂ : TypedExpr}
    (h₁ : x₁.typeOf = .ext .datetime)
    (h₂ : x₂.typeOf = .ext .datetime) :
    WellTyped env .lessEq x₁ x₂ (.bool .anyBool)
  | lessEq_duration {x₁ x₂ : TypedExpr}
    (h₁ : x₁.typeOf = .ext .duration)
    (h₂ : x₂.typeOf = .ext .duration) :
    WellTyped env .lessEq x₁ x₂ (.bool .anyBool)
  | add {x₁ x₂ : TypedExpr}
    (h₁ : x₁.typeOf = .int)
    (h₂ : x₂.typeOf = .int) :
    WellTyped env .add x₁ x₂ .int
  | sub {x₁ x₂ : TypedExpr}
    (h₁ : x₁.typeOf = .int)
    (h₂ : x₂.typeOf = .int) :
    WellTyped env .sub x₁ x₂ .int
  | mul {x₁ x₂ : TypedExpr}
    (h₁ : x₁.typeOf = .int)
    (h₂ : x₂.typeOf = .int) :
    WellTyped env .mul x₁ x₂ .int
  | contains {x₁ x₂ : TypedExpr}
    (h₁ : x₁.typeOf = .set x₂.typeOf) :
    WellTyped env .contains x₁ x₂ (.bool .anyBool)
  | containsAll {x₁ x₂ : TypedExpr} {ty : CedarType}
    (h₁ : x₁.typeOf = .set ty)
    (h₂ : x₂.typeOf = .set ty) :
    WellTyped env .containsAll x₁ x₂ (.bool .anyBool)
  | containsAny {x₁ x₂ : TypedExpr} {ty : CedarType}
    (h₁ : x₁.typeOf = .set ty)
    (h₂ : x₂.typeOf = .set ty) :
    WellTyped env .containsAny x₁ x₂ (.bool .anyBool)
  | hasTag {x₁ x₂ : TypedExpr} {ety : EntityType}
    (h₁ : x₁.typeOf = .entity ety)
    (h₂ : x₂.typeOf = .string) :
    WellTyped env .hasTag x₁ x₂ (.bool .anyBool)
  | getTag {x₁ x₂ : TypedExpr} {ety : EntityType} {ty : CedarType}
    (h₁ : x₁.typeOf = .entity ety)
    (h₂ : x₂.typeOf = .string)
    (h₃ : env.ets.tags? ety = .some (.some ty)) :
    WellTyped env .getTag x₁ x₂ ty.liftBoolTypes

public inductive ExtFun.WellTyped : ExtFun → List TypedExpr → CedarType → Prop
  | decimal {s₁ : String} {d₁ : Decimal}
    (h₁ : d₁ = Decimal.decimal s₁) :
    WellTyped .decimal [.lit (.string s₁) .string] (.ext .decimal)
  | lessThan {x₁ x₂ : TypedExpr}
    (h₁ : x₁.typeOf = .ext .decimal)
    (h₂ : x₂.typeOf = .ext .decimal) :
    WellTyped .lessThan [x₁, x₂] (.bool .anyBool)
  | lessThanOrEqual {x₁ x₂ : TypedExpr}
    (h₁ : x₁.typeOf = .ext .decimal)
    (h₂ : x₂.typeOf = .ext .decimal) :
    WellTyped .lessThanOrEqual [x₁, x₂] (.bool .anyBool)
  | greaterThan {x₁ x₂ : TypedExpr}
    (h₁ : x₁.typeOf = .ext .decimal)
    (h₂ : x₂.typeOf = .ext .decimal) :
    WellTyped .greaterThan [x₁, x₂] (.bool .anyBool)
  | greaterThanOrEqual {x₁ x₂ : TypedExpr}
    (h₁ : x₁.typeOf = .ext .decimal)
    (h₂ : x₂.typeOf = .ext .decimal) :
    WellTyped .greaterThanOrEqual [x₁, x₂] (.bool .anyBool)
  | ip {s₁ : String} {ip₁ : IPAddr}
    (h₁ : ip₁ =  IPAddr.ip s₁) :
    WellTyped .ip [.lit (.string s₁) .string] (.ext .ipAddr)
  | isIpv4 {x₁ : TypedExpr}
    (h₁ : x₁.typeOf = .ext .ipAddr) :
    WellTyped .isIpv4 [x₁] (.bool .anyBool)
  | isIpv6 {x₁ : TypedExpr}
    (h₁ : x₁.typeOf = .ext .ipAddr) :
    WellTyped .isIpv6 [x₁] (.bool .anyBool)
  | isLoopback {x₁ : TypedExpr}
    (h₁ : x₁.typeOf = .ext .ipAddr) :
    WellTyped .isLoopback [x₁] (.bool .anyBool)
  | isMulticast {x₁ : TypedExpr}
    (h₁ : x₁.typeOf = .ext .ipAddr) :
    WellTyped .isMulticast [x₁] (.bool .anyBool)
  | isInRange {x₁ x₂ : TypedExpr}
    (h₁ : x₁.typeOf = .ext .ipAddr)
    (h₂ : x₂.typeOf = .ext .ipAddr):
    WellTyped .isInRange [x₁, x₂] (.bool .anyBool)
  | datetime {s₁ : String} {d₁ : Datetime}
    (h₁ : d₁ =  Datetime.parse s₁) :
    WellTyped .datetime [.lit (.string s₁) .string] (.ext .datetime)
  | duration {s₁ : String} {d₁ : Duration}
    (h₁ : d₁ =  Datetime.Duration.parse s₁) :
    WellTyped .duration [.lit (.string s₁) .string] (.ext .duration)
  | offset {x₁ x₂ : TypedExpr}
    (h₁ : x₁.typeOf = .ext .datetime)
    (h₂ : x₂.typeOf = .ext .duration):
    WellTyped .offset [x₁, x₂] (.ext .datetime)
  | durationSince {x₁ x₂ : TypedExpr}
    (h₁ : x₁.typeOf = .ext .datetime)
    (h₂ : x₂.typeOf = .ext .datetime):
    WellTyped .durationSince [x₁, x₂] (.ext .duration)
  | toDate {x₁ : TypedExpr}
    (h₁ : x₁.typeOf = .ext .datetime) :
    WellTyped .toDate [x₁] (.ext .datetime)
  | toTime {x₁ : TypedExpr}
    (h₁ : x₁.typeOf = .ext .datetime) :
    WellTyped .toTime [x₁] (.ext .duration)
  | toMilliseconds {x₁ : TypedExpr}
    (h₁ : x₁.typeOf = .ext .duration) :
    WellTyped .toMilliseconds [x₁] .int
  | toSeconds {x₁ : TypedExpr}
    (h₁ : x₁.typeOf = .ext .duration) :
    WellTyped .toSeconds [x₁] .int
  | toMinutes {x₁ : TypedExpr}
    (h₁ : x₁.typeOf = .ext .duration) :
    WellTyped .toMinutes [x₁] .int
  | toHours {x₁ : TypedExpr}
    (h₁ : x₁.typeOf = .ext .duration) :
    WellTyped .toHours [x₁] .int
  | toDays {x₁ : TypedExpr}
    (h₁ : x₁.typeOf = .ext .duration) :
    WellTyped .toDays [x₁] .int

end Cedar.Spec

namespace Cedar.Thm

open Cedar.Validation
open Cedar.Spec
open Cedar.Data

/--
Chain validity for extended `has` attribute checks.
Starting from a Cedar type, each intermediate attribute access in the chain
must either:
- yield an entity or record type (so that `attrsOf` succeeds on the next value),
- not be present in the schema (absent attribute is valid).
The LAST attribute in the chain doesn't need this constraint (we just check existence).
In other words, a valid chain doesn't have intermediate accesses to attributes that are
neither entitiy nor records.
-/
public inductive ExtHasAttrChainValid (ets : EntitySchema) : CedarType → List Attr → Prop where
  /-- A single-attribute chain is always valid (just a `has` check, no deeper traversal) -/
  | last {ty : CedarType} {attr : Attr} :
    ExtHasAttrChainValid ets ty [attr]
  /-- Intermediate attribute has entity type in the schema -/
  | cons_entity {ety nextEty : EntityType} {attr : Attr} {rest : List Attr}
    {rty : RecordType} {qty : QualifiedType}
    (h₁ : ets.attrs? ety = .some rty)
    (h₂ : rty.find? attr = .some qty)
    (h₃ : qty.getType = .entity nextEty)
    (h₄ : ExtHasAttrChainValid ets (.entity nextEty) rest) :
    ExtHasAttrChainValid ets (.entity ety) (attr :: rest)
  /-- Intermediate attribute has record type in the schema -/
  | cons_record_from_entity {ety : EntityType} {attr : Attr} {rest : List Attr}
    {rty : RecordType} {qty : QualifiedType} {recRty : RecordType}
    (h₁ : ets.attrs? ety = .some rty)
    (h₂ : rty.find? attr = .some qty)
    (h₃ : qty.getType = .record recRty)
    (h₄ : ExtHasAttrChainValid ets (.record recRty) rest) :
    ExtHasAttrChainValid ets (.entity ety) (attr :: rest)
  /-- Attribute not found in schema for entity — chain is vacuously valid
      (at runtime, `find?` will return `.none` → `.ok false`) -/
  | cons_not_in_schema_entity {ety : EntityType} {attr : Attr} {rest : List Attr}
    (h₁ : ets.attrs? ety = .none ∨ ∀ rty, ets.attrs? ety = .some rty → rty.find? attr = .none) :
    ExtHasAttrChainValid ets (.entity ety) (attr :: rest)
  /-- Record type: intermediate attribute has entity type -/
  | cons_entity_from_record {recRty : RecordType} {attr : Attr} {rest : List Attr}
    {qty : QualifiedType} {nextEty : EntityType}
    (h₁ : recRty.find? attr = .some qty)
    (h₂ : qty.getType = .entity nextEty)
    (h₃ : ExtHasAttrChainValid ets (.entity nextEty) rest) :
    ExtHasAttrChainValid ets (.record recRty) (attr :: rest)
  /-- Record type: intermediate attribute has record type -/
  | cons_record_from_record {recRty : RecordType} {attr : Attr} {rest : List Attr}
    {qty : QualifiedType} {nextRecRty : RecordType}
    (h₁ : recRty.find? attr = .some qty)
    (h₂ : qty.getType = .record nextRecRty)
    (h₃ : ExtHasAttrChainValid ets (.record nextRecRty) rest) :
    ExtHasAttrChainValid ets (.record recRty) (attr :: rest)
  /-- Record type: attribute not in record type — vacuously valid -/
  | cons_not_in_record {recRty : RecordType} {attr : Attr} {rest : List Attr}
    (h₁ : recRty.find? attr = .none) :
    ExtHasAttrChainValid ets (.record recRty) (attr :: rest)


public inductive TypedExpr.WellTyped (env : TypeEnv) : TypedExpr → Prop
| lit {p : Prim} {ty : CedarType}
  (h₁ : p.WellTyped env ty) :
  WellTyped env (.lit p ty)
| var {v : Var} {ty : CedarType}
  (h₁ : v.WellTyped env ty) :
  WellTyped env (.var v ty)
| ite {x₁ x₂ x₃ : TypedExpr}
  (h₁ : WellTyped env x₁)
  (h₂ : WellTyped env x₂)
  (h₃ : WellTyped env x₃)
  (h₄ : x₁.typeOf = .bool .anyBool)
  (h₅ : x₂.typeOf = x₃.typeOf) :
  WellTyped env (.ite x₁ x₂ x₃ x₂.typeOf)
| and {x₁ x₂ : TypedExpr}
  (h₁ : WellTyped env x₁)
  (h₂ : WellTyped env x₂)
  (h₃ : x₁.typeOf = .bool .anyBool)
  (h₄ : x₂.typeOf = .bool .anyBool) :
  WellTyped env (.and x₁ x₂ (.bool .anyBool))
| or {x₁ x₂ : TypedExpr}
  (h₁ : WellTyped env x₁)
  (h₂ : WellTyped env x₂)
  (h₃ : x₁.typeOf = .bool .anyBool)
  (h₄ : x₂.typeOf = .bool .anyBool) :
  WellTyped env (.or x₁ x₂ (.bool .anyBool))
| unaryApp {op₁ : UnaryOp} {x₁ : TypedExpr}  {ty : CedarType}
  (h₁ : WellTyped env x₁)
  (h₂ : op₁.WellTyped x₁ ty) :
  WellTyped env (.unaryApp op₁ x₁ ty)
| binaryApp {op₂ : BinaryOp} {x₁ x₂: TypedExpr}  {ty : CedarType}
  (h₁ : WellTyped env x₁)
  (h₂ : WellTyped env x₂)
  (h₃ : op₂.WellTyped env x₁ x₂ ty) :
  WellTyped env (.binaryApp op₂ x₁ x₂ ty)
| hasAttr_entity {ety : EntityType} {x₁ : TypedExpr} {attr : Attr}
  (h₁ : WellTyped env x₁)
  (h₂ : x₁.typeOf = .entity ety) :
  WellTyped env (.hasAttr x₁ attr (.bool .anyBool))
| hasAttr_record {rty : RecordType} {x₁ : TypedExpr} {attr : Attr}
  (h₁ : WellTyped env x₁)
  (h₂ : x₁.typeOf = .record rty) :
  WellTyped env (.hasAttr x₁ attr (.bool .anyBool))
| extHasAttr_entity {ety : EntityType} {x₁ : TypedExpr} {attr : Attr} {attrs : List Attr}
  (h₁ : WellTyped env x₁)
  (h₂ : x₁.typeOf = .entity ety)
  (h₃ : Cedar.Thm.ExtHasAttrChainValid env.ets (.entity ety) (attr :: attrs)) :
  WellTyped env (.extHasAttr x₁ attr attrs (.bool .anyBool))
| extHasAttr_record {rty : RecordType} {x₁ : TypedExpr} {attr : Attr} {attrs : List Attr}
  (h₁ : WellTyped env x₁)
  (h₂ : x₁.typeOf = .record rty)
  (h₃ : Cedar.Thm.ExtHasAttrChainValid env.ets (.record rty) (attr :: attrs)) :
  WellTyped env (.extHasAttr x₁ attr attrs (.bool .anyBool))
| extHasAttr_ff {x₁ : TypedExpr} {attr : Attr} {attrs : List Attr}
  (h₁ : WellTyped env x₁)
  (h₂ : (∃ ety, x₁.typeOf = .entity ety) ∨ (∃ rty, x₁.typeOf = .record rty))
  (h₃ : Cedar.Thm.ExtHasAttrChainValid env.ets x₁.typeOf (attr :: attrs)) :
  WellTyped env (.extHasAttr x₁ attr attrs (.bool .anyBool))
| getAttr_entity {ety : EntityType} {rty : RecordType} {x₁ : TypedExpr} {attr : Attr} {ty : CedarType}
  (h₁ : WellTyped env x₁)
  (h₂ : x₁.typeOf = .entity ety)
  (h₃ : (env.ets.attrs? ety).map RecordType.liftBoolTypes = .some rty)
  (h₄ : (rty.find? attr).map Qualified.getType = .some ty) :
  WellTyped env (.getAttr x₁ attr ty)
| getAttr_record {rty : RecordType} {x₁ : TypedExpr} {attr : Attr} {ty : CedarType}
  (h₁ : WellTyped env x₁)
  (h₂ : x₁.typeOf = .record rty)
  (h₃ : (rty.find? attr).map Qualified.getType = .some ty) :
  WellTyped env (.getAttr x₁ attr ty)
| set {ls : List TypedExpr} {ty : CedarType}
  (h₁ : ∀ x, x ∈ ls → WellTyped env x)
  (h₂ : ∀ x, x ∈ ls → x.typeOf = ty)
  (h₃ : ls != []) :
  WellTyped env (.set ls (.set ty))
| record {rty : RecordType} {m : List (Attr × TypedExpr)}
  (h₁ : ∀ k v, (k,v) ∈ m → WellTyped env v)
  (h₂ : rty = Map.make (m.map (λ (a, ty) => (a, .required ty.typeOf)))) :
  WellTyped env (.record m (.record rty))
| call {xfn : ExtFun} {args : List TypedExpr} {ty : CedarType}
  (h₁ : ∀ x, x ∈ args → WellTyped env x)
  (h₂ : xfn.WellTyped args ty) :
  WellTyped env (.call xfn args ty)

end Cedar.Thm
