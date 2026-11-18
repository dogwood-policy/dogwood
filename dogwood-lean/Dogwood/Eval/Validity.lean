import Dogwood.Spec.Validity
import Dogwood.Eval.Safety
import Dogwood.Eval.Typing
import Dogwood.Eval.Scopes

/-!
# Deciding validity

`PolicySet.validationFindings P` lists the categories of the problems validation finds in a
policy set: none exactly when the policy set is valid
(`Dogwood.Thm.validationFindings_eq_nil_iff`). It is not part of the specification: the
conformance harness runs it, and compares its categories with the crate's findings.
-/

namespace Dogwood.Spec

open Dogwood.Eval Temporal

mutual

/-- `Expr.ReadsContext`, decided. -/
def Expr.readsContextB (reserved : List Cedar.Spec.Attr) : Expr → Bool
  | .lit _ => true
  | .var v => v != .context
  | .getAttr x a | .hasAttr x a | .extHasAttr x a _ =>
    if x.isContext then !reserved.contains a else Expr.readsContextB reserved x
  | .unaryApp _ x => Expr.readsContextB reserved x
  | .ite a b c => Expr.readsContextB reserved a && Expr.readsContextB reserved b &&
      Expr.readsContextB reserved c
  | .and a b | .or a b | .binaryApp _ a b =>
    Expr.readsContextB reserved a && Expr.readsContextB reserved b
  | .set xs | .call _ xs => Expr.readsContextListB reserved xs
  | .record axs => Expr.readsContextRecordB reserved axs
  | .temporal _ | .provider _ => true

def Expr.readsContextListB (reserved : List Cedar.Spec.Attr) : List Expr → Bool
  | [] => true
  | x :: xs => Expr.readsContextB reserved x && Expr.readsContextListB reserved xs

def Expr.readsContextRecordB (reserved : List Cedar.Spec.Attr) : List (Cedar.Spec.Attr × Expr) → Bool
  | [] => true
  | (_, x) :: axs => Expr.readsContextB reserved x && Expr.readsContextRecordB reserved axs

end

/-- `Provider.argsMatchDecl`, decided. -/
def Provider.argsMatchDeclB (args : List Provider.Arg) (tys : List Cedar.Validation.CedarType) : Bool :=
  args.length == tys.length &&
    (args.zip tys).all fun p => p.1.literalType? == none || p.1.literalType? == some p.2

/-- `Provider.Signature.Chains`, decided. -/
def Provider.Signature.chainsB (sig : Provider.Signature) :
    Cedar.Validation.CedarType → List Provider.MethodCall → Bool
  | _, [] => true
  | s, m :: ms =>
    match sig.methods.find? (·.name == m.name) with
    | some msig => (msig.input.isNone || msig.input == some s) && sig.chainsB msig.output ms
    | none => false

/-- `Provider.Call.Declared`, decided. -/
def Provider.Call.declaredB (D : Provider.Declarations) (c : Provider.Call) : Bool :=
  match D.find? c.function with
  | none => false
  | some sig =>
    Provider.argsMatchDeclB c.args sig.args &&
      (c.methods.all fun m =>
        sig.methods.any fun ms => ms.name == m.name && Provider.argsMatchDeclB m.args ms.args) &&
      sig.chainsB sig.output c.methods

/-- `Provider.ArgsTypedIn`, decided. -/
def Provider.argsTypedInB (C : TypingCtx) (args : List Provider.Arg)
    (tys : List Cedar.Validation.CedarType) : Bool :=
  args.length == tys.length && (args.zip tys).all fun p => p.1.hasTypeIn C p.2

/-- `Provider.Call.TypedIn`, decided. -/
def Provider.Call.typedInB (C : TypingCtx) (D : Provider.Declarations) (c : Provider.Call) :
    Bool :=
  match D.find? c.function with
  | none => false
  | some sig =>
    Provider.argsTypedInB C c.args sig.args &&
      c.methods.all fun m =>
        sig.methods.any fun ms => ms.name == m.name && Provider.argsTypedInB C m.args ms.args

namespace PolicySet

variable (P : PolicySet)

/-- The problems found in one temporal leaf of the rule `p`, at a position with the facts `F`. -/
def leafFindings (p : Policy) (F : List Guard) (φ : Formula) : List Finding :=
  (P.envsOf p).flatMap (fun env => φ.check (P.typingCtx env F) []) ++
    (if isSafeB φ then [] else [.safety]) ++
    (if φ.monitorsTimeB then [] else [.timeDependence])

/-- The problems found in the leaves of the rule `p`. -/
def ruleFindings (p : Policy) : List Finding :=
  (p.toExpr.leafFacts []).flatMap fun
    | (.inl φ, F) => P.leafFindings p F φ
    | (.inr c, F) =>
      if c.declaredB P.providerDecls &&
          (P.envsOf p).all (fun env => c.typedInB (P.typingCtx env F) P.providerDecls) then []
      else [.provider]

/-- Whether no action's context declares a leaf's attribute. -/
def namesFreshB : Bool :=
  P.actionSchema.acts.toList.all fun (_, entry) =>
    P.hoistedNames.all fun a => (entry.context.find? a).isNone

/-- The problems validation finds in the policy set. -/
def validationFindings : List Finding :=
  (if P.hoistedTypes?.isSome then [] else [.provider]) ++
  (if P.hoistedNames.Nodup ∧ P.namesFreshB = true then [] else [.contextRead]) ++
  (if P.leafList.isEmpty || P.policies.all (·.toExpr.readsContextB P.hoistedNames) then []
   else [.contextRead]) ++
  (match P.augmentedSchema.validateWellFormed with
    | .ok () => []
    | .error _ => [.schema]) ++
  (if P.augmentedSchema.standardAncestors then [] else [.schema]) ++
  (if P.policies.isEmpty || (P.externalTypes.isEmpty && P.externalActions.isEmpty) then []
   else [.cedar]) ++
  -- Without a type for every leaf's attribute, the augmented schema lacks some, and Cedar's
  -- verdict would only repeat the provider finding.
  (if P.hoistedTypes?.isSome then
    match Cedar.Validation.validate P.lowered P.augmentedSchema with
    | .ok () => []
    | .error _ => [.cedar]
   else []) ++
  P.policies.flatMap P.ruleFindings ++
  (match P.maxHorizon with
    | none => []
    | some H =>
      if P.temporalLeaves.all (fun φ => decide (φ.horizon .seconds ≤ H)) then [] else [.horizon])

end PolicySet

end Dogwood.Spec
