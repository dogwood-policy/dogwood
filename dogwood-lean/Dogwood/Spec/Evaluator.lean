import Dogwood.Spec.Expr

/-!
# Evaluating condition expressions

`evaluate θ x req es` is Cedar's `Cedar.Spec.evaluate`, case for case, with
the two Dogwood leaves read off a leaf valuation `θ`: a temporal condition
evaluates to the `Bool` `θ.temporal φ`, a provider invocation to the value
`θ.provider c`. Every Cedar operator is delegated to Cedar's own definition
(`apply₁`, `apply₂`, `getAttr`, `hasAttr`, `hasAttrs`, `call`).

Because a leaf's value is supplied rather than computed, a leaf never
errors: whatever Cedar does with the `Bool` or the provider output — compare
it, project a field from it, combine it — happens under Cedar's semantics.
-/

namespace Dogwood.Spec

open Cedar.Spec (Value Result Request Entities apply₁ apply₂ hasAttr hasAttrs getAttr bindAttr call)
open Cedar.Data (Set Map)

/-- The values of the leaves of a policy set, at one decision. -/
structure Leaves where
  /-- Whether a temporal condition holds at the decision timepoint. -/
  temporal : Temporal.Formula → Bool
  /-- A provider invocation's output on the decision event. -/
  provider : Provider.Call → Value

def evaluate (θ : Leaves) (x : Expr) (req : Request) (es : Entities) : Result Value :=
  match x with
  | .lit l           => .ok l
  | .var v           => match v with
    | .principal     => .ok req.principal
    | .action        => .ok req.action
    | .resource      => .ok req.resource
    | .context       => .ok req.context
  | .ite x₁ x₂ x₃    => do
    let b ← (evaluate θ x₁ req es).as Bool
    if b then evaluate θ x₂ req es else evaluate θ x₃ req es
  | .and x₁ x₂       => do
    let b ← (evaluate θ x₁ req es).as Bool
    if !b then .ok b else (evaluate θ x₂ req es).as Bool
  | .or x₁ x₂        => do
    let b ← (evaluate θ x₁ req es).as Bool
    if b then .ok b else (evaluate θ x₂ req es).as Bool
  | .unaryApp op₁ x₁ => do
    let v₁ ← evaluate θ x₁ req es
    apply₁ op₁ v₁
  | .binaryApp op₂ x₁ x₂ => do
    let v₁ ← evaluate θ x₁ req es
    let v₂ ← evaluate θ x₂ req es
    apply₂ op₂ v₁ v₂ es
  | .hasAttr x₁ a    => do
    let v₁ ← evaluate θ x₁ req es
    hasAttr v₁ a es
  | .extHasAttr x₁ a l => do
    let v₁ ← evaluate θ x₁ req es
    hasAttrs v₁ a l es
  | .getAttr x₁ a    => do
    let v₁ ← evaluate θ x₁ req es
    getAttr v₁ a es
  | .set xs          => do
    let vs ← xs.mapM₁ (fun ⟨x₁, _⟩ => evaluate θ x₁ req es)
    .ok (Set.make vs)
  | .record axs      => do
    let avs ← axs.mapM₂ (fun ⟨(a₁, x₁), _⟩ => bindAttr a₁ (evaluate θ x₁ req es))
    .ok (Map.make avs)
  | .call xfn xs     => do
    let vs ← xs.mapM₁ (fun ⟨x₁, _⟩ => evaluate θ x₁ req es)
    call xfn vs
  | .temporal φ      => .ok (.prim (.bool (θ.temporal φ)))
  | .provider c      => .ok (θ.provider c)

end Dogwood.Spec
