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

public import Cedar.Validation.Types
public import Cedar.Spec

namespace Cedar.Validation

open Cedar.Data
open Cedar.Spec

public def lubBool (b₁ b₂ : BoolType) : BoolType :=
  if b₁ = b₂ then b₁ else .anyBool

mutual
  public def lubQualifiedType (q₁ q₂ : QualifiedType) : Option QualifiedType :=
    match q₁, q₂ with
    | .optional ty₁, .optional ty₂ => do let ty ← lub? ty₁ ty₂; .some (.optional ty)
    | .required ty₁, .required ty₂ => do let ty ← lub? ty₁ ty₂; .some (.required ty)
    | _, _ => .none

  public def lubRecordType (ty₁ ty₂ : List (Attr × QualifiedType)) : Option (List (Attr × QualifiedType)) :=
    match ty₁, ty₂ with
    | [], [] => .some []
    | (k₁, v₁)::r₁, (k₂, v₂)::r₂ =>
      if k₁ != k₂
      then .none
      else do
        let ty  ← lubQualifiedType v₁ v₂
        let tys ← lubRecordType r₁ r₂
        .some ((k₁, ty) :: tys)
    | _, _ => .none


  public def lub? (ty₁ ty₂ : CedarType) : Option CedarType :=
    match ty₁, ty₂ with
    | .bool b₁, .bool b₂ => .some (.bool (lubBool b₁ b₂))
    | .set s₁, .set s₂ => do
      let lub ← lub? s₁ s₂
      .some (.set lub)
    | .record (.mk r₁), .record (.mk r₂) => do
      let lub ← lubRecordType r₁ r₂
      .some (.record (Map.mk lub))
    | _, _ => if ty₁ = ty₂ then .some ty₁ else  .none
end

public def subty (ty₁ ty₂ : CedarType) : Bool :=
  match lub? ty₁ ty₂ with
  | .some ty => ty = ty₂
  | .none    => false

infix:50 " ⊔ " => lub?
infix:50 " ⊑ " => subty

end Cedar.Validation
