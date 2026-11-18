import Dogwood.Thm.Frontend.Validate.Interface

/-!
# The validator's completeness: the definitions it is stated with

The converse of soundness, `PolicySet.Valid` implies that the frontend's validator reports no
error, holds except where the crate's validator is stricter than the specification. Each such
rule is stated here as a decidable property of a leaf or a lowered set, whose failure is the
exception:

* `noReservedHeadReadsF`: no `context.<path>` term starts with a name lowering reserves (the
  crate resolves no such path; the specification resolves one the action schema declares);
* `providerExceptionsOk`: the entity types a provider call references are enums, and no
  method of its chain is named like a Cedar extension method; no `context.<path>` argument
  starts with a reserved name, and no scope-attribute argument is ambiguous.

`ViewExact` is `ViewAgrees` with the facts the other way round, and the event signatures matching
the derived events both ways.
-/

namespace Dogwood.Thm.Frontend

open Dogwood.Frontend Dogwood.Frontend.Validate
open Dogwood.Spec (Path)
open Dogwood.Spec.Temporal
open Cedar.Validation (CedarType Schema ActionSchemaEntry RecordType QualifiedType TypeEnv)
open Cedar.Spec (Attr EntityUID)

/-- The specification's typing context sees the environment exactly as the crate's validator: as
`ViewAgrees`, with the specification's facts among the crate's, a declared field a leaf of its
event, and a signature only for a derived event. -/
structure ViewExact (C' : TypingCtx) (C : LeafCtx) (e : ReqEnv) : Prop extends ViewAgrees C' C e where
  factsExact : ∀ g ∈ C'.facts, g ∈ C.facts
  leafIff : ∀ a k ev, eventOf? C.events a k = some ev → ∀ sig, C'.events.signature? a k = some sig →
    ∀ p, (sig.field? p).isSome → lookupPath ev p = .leaf
  sigOnly : ∀ a k, (C'.events.signature? a k).isSome → (eventOf? C.events a k).isSome

mutual

/-- No `context.<path>` term of the condition starts with a name lowering reserves. -/
def noReservedHeadReadsF : Formula → Bool
  | .and φ ψ | .since φ _ ψ => noReservedHeadReadsF φ && noReservedHeadReadsF ψ
  | .not φ | .formerly _ φ | .previous _ φ | .exist _ φ => noReservedHeadReadsF φ
  | .pred _ _ args => noReservedHeadReadsArgs args
  | .cmp _ l r => noReservedHeadReadsT l && noReservedHeadReadsT r
  | .tp _ => true

def noReservedHeadReadsT : Term → Bool
  | .context (h :: _) => !isHoistedName h
  | .agg (.count _ body) | .agg (.sum _ _ body) => noReservedHeadReadsF body
  | .arith _ l r => noReservedHeadReadsT l && noReservedHeadReadsT r
  | _ => true

def noReservedHeadReadsArgs : List (Path × Term) → Bool
  | [] => true
  | (_, t) :: args => noReservedHeadReadsT t && noReservedHeadReadsArgs args

end

mutual

/-- The path arguments of a provider call: none starts with a reserved context name, and none
reads a scope attribute ambiguously. -/
def providerArgsOk (C : ProviderCtx) : List Provider.Arg → Bool
  | [] => true
  | .set items :: rest => providerArgsOk C items && providerArgsOk C rest
  | .field ("context" :: h :: _) :: rest => !isHoistedName h && providerArgsOk C rest
  | .field (root :: p@(_ :: _)) :: rest =>
    (C.envs.all fun e =>
      let r? : Option Root := if root == "principal" then some .principal
        else if root == "resource" then some .resource else none
      match r? with
      | some r =>
        match resolveScopePath C.schema e.entry r (C.narrow r) p with
        | .ambiguous _ => false
        | _ => true
      | none => true) && providerArgsOk C rest
  | _ :: rest => providerArgsOk C rest

end

/-- A provider leaf avoids the crate's stricter provider rules: the entity types its call
references are enums, no method of its chain is named like a Cedar extension method, and its
path arguments are as `providerArgsOk` requires. -/
def providerExceptionsOk (S : Schema) (g : LoweredProviderField) (d : ProviderDecls.ProviderDecl) : Bool :=
  (d.referencedEntityTypes (g.methods.map (·.name))).all (fun name =>
    match S.ets.find? (parseEntityType ((g.entityTypeNames.lookup name).getD name)) with
    | some (.enum _) => true
    | _ => false) &&
  g.methods.all (fun m => !cedarExtensionMethods.contains m.name) &&
  providerArgsOk (providerCtx S g) g.invocation.args &&
  g.methods.all (fun m => providerArgsOk (providerCtx S g) m.args)

end Dogwood.Thm.Frontend
