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

public import Cedar.Spec.Entities
public import Cedar.Spec.Expr
public import Cedar.Spec.ExtFun
public import Cedar.Spec.Request

/-! This file defines the semantics of Cedar operators and expressions. -/

namespace Cedar.Spec

open Cedar.Data
open Error

-- remainder of the file is all `@[expose]`d
@[expose] public section

public def intOrErr : Option Int64 → Result Value
  | .some i => .ok (.prim (.int i))
  | .none   => .error .arithBoundsError

public def apply₁ : UnaryOp → Value → Result Value
  | .not,     .prim (.bool b)        => .ok !b
  | .neg,     .prim (.int i)         => intOrErr i.neg?
  | .isEmpty, .set s                 => .ok s.isEmpty
  | .like p,  .prim (.string s)      => .ok (wildcardMatch s p)
  | .is ety,  .prim (.entityUID uid) => .ok (ety == uid.ty)
  | _, _                             => .error .typeError

public def inₑ (uid₁ uid₂ : EntityUID) (es : Entities) : Bool :=
  uid₁ == uid₂ || (es.ancestorsOrEmpty uid₁).contains uid₂

public def inₛ (uid : EntityUID) (vs : Set Value) (es : Entities) : Result Value := do
  let uids ← vs.mapOrErr Value.asEntityUID .typeError
  .ok (uids.any (inₑ uid · es))

public def hasTag (uid : EntityUID) (tag : String) (es : Entities) : Result Value :=
  .ok ((es.tagsOrEmpty uid).contains tag)

public def getTag (uid : EntityUID) (tag : String) (es : Entities) : Result Value := do
  (← es.tags uid).findOrErr tag .tagDoesNotExist

public def apply₂ (op₂ : BinaryOp) (v₁ v₂ : Value) (es : Entities) : Result Value :=
  match op₂, v₁, v₂ with
  | .eq, _, _                                              => .ok (v₁ == v₂)
  | .less,   .prim (.int i), .prim (.int j)                => .ok ((i < j): Bool)
  | .less,   .ext (.datetime d₁), .ext (.datetime d₂)      => .ok ((d₁ < d₂): Bool)
  | .less,   .ext (.duration d₁), .ext (.duration d₂)      => .ok ((d₁ < d₂): Bool)
  | .lessEq, .prim (.int i), .prim (.int j)                => .ok ((i ≤ j): Bool)
  | .lessEq, .ext (.datetime d₁), .ext (.datetime d₂)      => .ok ((d₁ ≤ d₂): Bool)
  | .lessEq, .ext (.duration d₁), .ext (.duration d₂)      => .ok ((d₁ ≤ d₂): Bool)
  | .add,    .prim (.int i), .prim (.int j)                => intOrErr (i.add? j)
  | .sub,    .prim (.int i), .prim (.int j)                => intOrErr (i.sub? j)
  | .mul,    .prim (.int i), .prim (.int j)                => intOrErr (i.mul? j)
  | .contains,    .set vs₁, _                              => .ok (vs₁.contains v₂)
  | .containsAll, .set vs₁, .set vs₂                       => .ok (vs₂.subset vs₁)
  | .containsAny, .set vs₁, .set vs₂                       => .ok (vs₁.intersects vs₂)
  | .mem, .prim (.entityUID uid₁), .prim (.entityUID uid₂) => .ok (inₑ uid₁ uid₂ es)
  | .mem, .prim (.entityUID uid₁), .set (vs)               => inₛ uid₁ vs es
  | .hasTag, .prim (.entityUID uid₁), .prim (.string tag)  => hasTag uid₁ tag es
  | .getTag, .prim (.entityUID uid₁), .prim (.string tag)  => getTag uid₁ tag es
  | _, _, _                                                => .error .typeError

public def attrsOf (v : Value) (lookup : EntityUID → Result (Map Attr Value)) : Result (Map Attr Value) :=
  match v with
  | .record r              => .ok r
  | .prim (.entityUID uid) => lookup uid
  | _                      => .error typeError

public def hasAttr (v : Value) (a : Attr) (es : Entities) : Result Value := do
  let r ← attrsOf v (fun uid => .ok (es.attrsOrEmpty uid))
  .ok (r.contains a)

public def getAttr (v : Value) (a : Attr) (es : Entities) : Result Value := do
  let r ← attrsOf v es.attrs
  r.findOrErr a attrDoesNotExist

public def hasAttrs (v : Value) (a : Attr) (as : List Attr) (es : Entities) : Result Value :=
  hasAttrs.loop v (a :: as) es
where
  loop (v : Value) (attrs : List Attr) (es : Entities) : Result Value :=
    match attrs with
    | []      => .ok true
    | a :: as =>
      match attrsOf v (fun uid => .ok (es.attrsOrEmpty uid)) with
      | .ok r =>
        match r.find? a with
        | .some v₁ => loop v₁ as es
        | .none => .ok false
      | .error _ => .error .typeError

public def bindAttr [Monad m] (a : Attr) (res : m α) : m (Attr × α) := do
  let v ← res
  pure (a, v)

public def evaluate (x : Expr) (req : Request) (es : Entities) : Result Value :=
  match x with
  | .lit l           => .ok l
  | .var v           => match v with
    | .principal     => .ok req.principal
    | .action        => .ok req.action
    | .resource      => .ok req.resource
    | .context       => .ok req.context
  | .ite x₁ x₂ x₃    => do
    let b ← (evaluate x₁ req es).as Bool
    if b then evaluate x₂ req es else evaluate x₃ req es
  | .and x₁ x₂       => do
    let b ← (evaluate x₁ req es).as Bool
    if !b then .ok b else (evaluate x₂ req es).as Bool
  | .or x₁ x₂        => do
    let b ← (evaluate x₁ req es).as Bool
    if b then .ok b else (evaluate x₂ req es).as Bool
  | .unaryApp op₁ x₁ => do
    let v₁ ← evaluate x₁ req es
    apply₁ op₁ v₁
  | .binaryApp op₂ x₁ x₂ => do
    let v₁ ← evaluate x₁ req es
    let v₂ ← evaluate x₂ req es
    apply₂ op₂ v₁ v₂ es
  | .hasAttr x₁ a    => do
    let v₁ ← evaluate x₁ req es
    hasAttr v₁ a es
  | .extHasAttr x₁ a l  => do
    let v₁ ← evaluate x₁ req es
    hasAttrs v₁ a l es
  | .getAttr x₁ a    => do
    let v₁ ← evaluate x₁ req es
    getAttr v₁ a es
  | .set xs          => do
    let vs ← xs.mapM₁ (fun ⟨x₁, _⟩ => evaluate x₁ req es)
    .ok (Set.make vs)
  | .record axs      => do
    let avs ← axs.mapM₂ (fun ⟨(a₁, x₁), _⟩ => bindAttr a₁ (evaluate x₁ req es))
    .ok (Map.make avs)
  | .call xfn xs     => do
    let vs ← xs.mapM₁ (fun ⟨x₁, _⟩ => evaluate x₁ req es)
    call xfn vs

end

end Cedar.Spec
