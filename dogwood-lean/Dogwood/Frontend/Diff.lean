import Dogwood.Frontend.Export
import Dogwood.Frontend.Conformance
import Dogwood.Frontend.Validate

/-!
# The differential harness

For each bundle of the crate's frontend export, each check runs one stage of the Lean frontend
on the crate's own inputs to that stage (the parsers' outputs, or the crate's observables of the
stages before it) and compares the result with the crate's observable of the stage. A stage is
thus tested on its own, whatever the state of the others. Two checks are end to end:
`conformance` (`Lowered.toConformance` of the crate's lowered set against the bridge's
conformance record) and `pipeline` (`Frontend.lower` on the parsed inputs against the crate's
lowered set, or against the first stage at which the crate failed). `export` checks the export
itself: its stages reproduce the crate's public pipeline.

A check's verdict on a bundle is one of: the two agree; they agree once the variables bound in
temporal blocks are renamed in binding order (macro expansion names fresh binders after source
spans); they disagree (with the first difference); the Lean stage is not implemented; the check
is skipped (the crate did not run the stage, or a parser rejected an input); or the record does
not decode. Results are compared by their JSON encodings, without source spans unless asked;
errors by category and, for the crate's own messages, by message.
-/

namespace Dogwood.Frontend.Diff

open Lean (Json FromJson ToJson fromJson? toJson)
open Dogwood.Conformance (sizeOf_lt_of_mem_arr sizeOf_lt_of_mem_toList)

/-! ## Comparing JSON -/

/-- The value without the keys `ks`, at any depth. -/
def stripKeys (ks : List String) (j : Json) : Json :=
  match j with
  | .arr a => .arr (a.attach.map fun ⟨x, _⟩ => stripKeys ks x)
  | .obj kvs => Json.mkObj (kvs.toList.attach.filterMap fun ⟨(k, v), _⟩ =>
      if ks.contains k then none else some (k, stripKeys ks v))
  | j => j
termination_by sizeOf j
decreasing_by
  · exact sizeOf_lt_of_mem_arr ‹_›
  · exact sizeOf_lt_of_mem_toList ‹_›

/-- A value's compact text, cut at `n` characters. -/
def shorten (j : Json) (n : Nat := 240) : String :=
  let s := j.compress
  if s.length ≤ n then s else (s.take n).toString ++ "…"

/-- The first place where two values differ, as a path and the two values there. -/
def firstDiff (path : String) (a b : Json) : Option String :=
  match a, b with
  | .arr xs, .arr ys =>
    if xs.size != ys.size then
      some s!"{path}: {xs.size} elements ≠ {ys.size}: {shorten a} ≠ {shorten b}"
    else
      (xs.attach.zipIdx.toList.zip ys.toList).findSome? fun ((⟨x, _⟩, i), y) =>
        firstDiff s!"{path}[{i}]" x y
  | .obj ka, .obj kb =>
    let keys := ((ka.toList.map (·.1)) ++ (kb.toList.map (·.1))).eraseDups
    keys.findSome? fun k =>
      match (ka.toList.attach.find? fun ⟨p, _⟩ => p.1 == k), kb.toList.lookup k with
      | some ⟨(_, x), _⟩, some y => firstDiff s!"{path}.{k}" x y
      | some ⟨(_, x), _⟩, none => some s!"{path}.{k}: {shorten x} ≠ (absent)"
      | none, some y => some s!"{path}.{k}: (absent) ≠ {shorten y}"
      | none, none => none
  | a, b => if a == b then none else some s!"{path}: {shorten a} ≠ {shorten b}"
termination_by sizeOf a
decreasing_by
  · exact sizeOf_lt_of_mem_arr ‹_›
  · exact sizeOf_lt_of_mem_toList ‹_›

/-! ## Renaming bound variables -/

namespace Alpha

open Surface.Temporal

/-- A fresh name, which no source can write. -/
def fresh : StateM Nat String := do
  let n ← get
  set (n + 1)
  return s!"#{n}"

/-- A use of a variable, renamed. -/
def slot (env : List (String × String)) : BinderSlot → BinderSlot
  | .name x => .name ((env.lookup x).getD x)
  | s => s

/-- Bind a `for` list, renaming each binder. -/
def bindAll (env : List (String × String)) :
    List TypedBinder → StateM Nat (List (String × String) × List TypedBinder)
  | [] => pure (env, [])
  | ⟨.name x, ty⟩ :: rest => do
    let n ← fresh
    let (env', rest') ← bindAll ((x, n) :: env) rest
    return (env', ⟨.name n, ty⟩ :: rest')
  | b :: rest => do
    let (env', rest') ← bindAll env rest
    return (env', b :: rest')

mutual

def cond (env : List (String × String)) : Condition → StateM Nat Condition
  | ⟨sp, k⟩ => return ⟨sp, ← kind env k⟩

def kind (env : List (String × String)) : ConditionKind → StateM Nat ConditionKind
  | .and l r => return .and (← cond env l) (← cond env r)
  | .or l r => return .or (← cond env l) (← cond env r)
  | .not c => return .not (← cond env c)
  | .formerly w c => return .formerly w (← cond env c)
  | .previous w c => return .previous w (← cond env c)
  | .since l w r => return .since (← cond env l) w (← cond env r)
  | .predicate ⟨sp, ns, a, k, args⟩ => return .predicate ⟨sp, ns, a, k, ← namedArgs env args⟩
  | .comparison op l r => return .comparison op (← term env l) (← term env r)
  | .exists ⟨.name x, ty⟩ c => do
    let n ← fresh
    return .exists ⟨.name n, ty⟩ (← cond ((x, n) :: env) c)
  | .exists b c => return .exists b (← cond env c)
  | .tp s => pure (.tp (slot env s))
  | .call c => return .call (← call env c)
  | .sigilRef s n => pure (.sigilRef s n)
  | .refine b fs sp => return .refine (← cond env b) (← namedArgs env fs) sp

def namedArgs (env : List (String × String)) : List NamedArg → StateM Nat (List NamedArg)
  | [] => pure []
  | ⟨n, t⟩ :: rest => return ⟨n, ← term env t⟩ :: (← namedArgs env rest)

def term (env : List (String × String)) : Term → StateM Nat Term
  | .var x => pure (.var ((env.lookup x).getD x))
  | .array xs => return .array (← terms env xs)
  | .agg ⟨sp, k⟩ => return .agg ⟨sp, ← agg env k⟩
  | .arith op l r => return .arith op (← term env l) (← term env r)
  | t => pure t

def terms (env : List (String × String)) : List Term → StateM Nat (List Term)
  | [] => pure []
  | t :: rest => return (← term env t) :: (← terms env rest)

def agg (env : List (String × String)) : AggExprKind → StateM Nat AggExprKind
  | .sum v vs b => do
    let (env', vs') ← bindAll env vs
    return .sum (slot env' v) vs' (← cond env' b)
  | .count vs b => do
    let (env', vs') ← bindAll env vs
    return .count vs' (← cond env' b)
  | .call c => return .call (← call env c)

def call (env : List (String × String)) : Call → StateM Nat Call
  | ⟨sp, n, args⟩ => return ⟨sp, n, ← callArgs env args⟩

def callArgs (env : List (String × String)) : List CallArg → StateM Nat (List CallArg)
  | [] => pure []
  | .condition c :: rest => return .condition (← cond env c) :: (← callArgs env rest)
  | .within i :: rest => return .within i :: (← callArgs env rest)
  | .term t :: rest => return .term (← term env t) :: (← callArgs env rest)

end

/-- The condition with its bound variables renamed `#0`, `#1`, … in binding order. -/
def normalize (c : Condition) : Condition := (cond [] c).run' 0

/-- The block with its bound variables renamed. -/
def block (b : Block) : Block := { b with condition := normalize b.condition }

open Surface in
mutual

/-- The expression with every temporal block's bound variables renamed. -/
def expr : Expr → Expr
  | ⟨k, sp⟩ => ⟨exprKind k, sp⟩

def exprKind : ExprKind → ExprKind
  | .extension t => .extension (block t)
  | .unaryApp op e => .unaryApp op (expr e)
  | .binaryApp op l r => .binaryApp op (expr l) (expr r)
  | .getAttr e a => .getAttr (expr e) a
  | .hasAttr e a => .hasAttr (expr e) a
  | .like e p => .like (expr e) p
  | .is e t none => .is (expr e) t none
  | .is e t (some x) => .is (expr e) t (some (expr x))
  | .ite c t e => .ite (expr c) (expr t) (expr e)
  | .set xs => .set (exprs xs)
  | .record m => .record (entries m)
  | .call n args => .call n (exprs args)
  | .methodCall r m args => .methodCall (expr r) m (exprs args)
  | k => k

def exprs : List Expr → List Expr
  | [] => []
  | e :: rest => expr e :: exprs rest

def entries : List (String × Expr) → List (String × Expr)
  | [] => []
  | (k, e) :: rest => (k, expr e) :: entries rest

end

/-- The policy set with every temporal block's bound variables renamed. -/
def policySet (ps : Surface.PolicySet) : Surface.PolicySet :=
  { ps with policies := ps.policies.map fun p =>
      { p with conditions := p.conditions.map fun c => { c with body := expr c.body } } }

/-- Cedarify's result with every hoisted block's bound variables renamed. -/
def cedarified (c : Cedarified) : Cedarified :=
  { c with contextFields := c.contextFields.map fun f => { f with temporal := block f.temporal } }

end Alpha

/-! ## Verdicts -/

/-- A check's verdict on one bundle. -/
inductive Verdict where
  | agree
  | agreeUpToRenaming
  | disagree (diff : String)
  | notImplemented (what : String)
  | skipped (why : String)
  | undecodable (why : String)

/-- How results are compared. -/
structure Options where
  /-- Compare source spans too. -/
  spans : Bool := false
  /-- How many disagreements to print per check. -/
  diffs : Nat := 5

/-- The span keys a comparison drops: spans, and the provider body base, a source offset. -/
def spanKeys : List String := ["span", "bodyBase"]

def prep (o : Options) (j : Json) : Json := if o.spans then j else stripKeys spanKeys j

/-- An error, for a diff. -/
def _root_.Dogwood.Frontend.Error.render (e : Error) : String := s!"[{e.stage} {repr e.category}] {e.message}"

local instance : ToJson Unit := ⟨fun _ => Json.null⟩

/-- Compare the Lean frontend's result with the crate's. `normalize` renames bound variables;
`messages` compares error messages too (false for Cedar's own errors, which the port does not
reproduce word for word). -/
def compare {α : Type} [ToJson α] (o : Options) (lean crate : Result α)
    (normalize : α → α := id) (messages : Bool := true) : Verdict :=
  match lean, crate with
  | .error e, _ =>
    if e.category == .notImplemented then .notImplemented e.message
    else match crate with
      | .error e' =>
        if e.category == e'.category && (!messages || e.message == e'.message) then .agree
        else .disagree s!"Lean {e.render} ≠ crate {e'.render}"
      | .ok v => .disagree s!"Lean {e.render} ≠ crate ok: {shorten (toJson v)}"
  | .ok v, .error e' => .disagree s!"Lean ok: {shorten (toJson v)} ≠ crate {e'.render}"
  | .ok v, .ok v' =>
    let a := prep o (toJson v)
    let b := prep o (toJson v')
    if a == b then .agree
    else if prep o (toJson (normalize v)) == prep o (toJson (normalize v')) then .agreeUpToRenaming
    else .disagree ((firstDiff "" a b).getD "the encodings differ")

/-- A check of a pass over each temporal leaf: skipped when the set has none, since the pass is
then not run. -/
def perLeaf {α : Type} (leaves : List α) (k : Unit → Verdict) : Verdict :=
  if leaves.isEmpty then .skipped "no temporal leaves" else k ()

/-- Run a check whose inputs come from the record. -/
def withInputs {α : Type} (x : Except Missing α) (k : α → Verdict) : Verdict :=
  match x with
  | .ok v => k v
  | .error (.notRun w) => .skipped w
  | .error (.undecodable w why) => .undecodable s!"{w}: {why}"

/-! ## Canonical encodings of compiled schemas and lowered sets -/

/-- A compiled schema, canonically (its maps are sorted). -/
def schemaToJson (S : Cedar.Validation.Schema) : Json :=
  let rec' := fun (r : Cedar.Validation.RecordType) => toJson (Cedar.Validation.CedarType.record r)
  Json.mkObj [
    ("ets", toJson (S.ets.toList.map fun (n, e) => (toJson n, match e with
      | .standard ⟨anc, attrs, tags⟩ =>
        Json.mkObj [("ancestors", toJson anc.toList), ("attrs", rec' attrs), ("tags", toJson tags)]
      | .enum eids => Json.mkObj [("enum", toJson eids.toList)]))),
    ("acts", toJson (S.acts.toList.map fun (a, e) => (toJson a, Json.mkObj [
      ("principals", toJson e.appliesToPrincipal.toList),
      ("resources", toJson e.appliesToResource.toList),
      ("ancestors", toJson e.ancestors.toList), ("context", rec' e.context)])))]

/-- A compiled schema, as a value the comparison encodes canonically. -/
structure CompiledSchema where
  schema : Cedar.Validation.Schema

instance : ToJson CompiledSchema := ⟨fun s => schemaToJson s.schema⟩

instance : ToJson Lowered where
  toJson l := Json.mkObj [
    ("policies", toJson l.policies), ("augmentedSchema", toJson l.augmentedSchema),
    ("schema", schemaToJson l.schema), ("temporal", toJson l.temporal),
    ("temporalExecutable", toJson l.temporalExecutable),
    ("temporalRewritten", toJson l.temporalRewritten), ("partitionKeys", toJson l.partitionKeys),
    ("providers", toJson l.providers), ("ruleIds", toJson l.ruleIds),
    ("temporalRules", toJson l.temporalRules), ("providerRules", toJson l.providerRules),
    ("eventSchema", toJson l.eventSchema), ("decisionKinds", toJson l.decisionKinds),
    ("enumNames", toJson l.enumNames), ("declarations", toJson l.declarations)]

deriving instance ToJson for Dogwood.Spec.FieldTy, Dogwood.Spec.FieldDecl,
  Dogwood.Spec.EventSignature, Dogwood.Spec.Provider.MethodSig, Dogwood.Spec.Provider.Signature

/-- The fields of a conformance record the frontend produces, each encoded. -/
def conformanceFields (l : Conformance.Lowered) : List (String × Json) :=
  [("schema", toJson l.schema), ("maxWindow", toJson l.maxWindow),
   ("maxHorizon", toJson l.maxHorizon), ("leaves", toJson l.leaves),
   ("actionSchema", schemaToJson l.actionSchema.toSchema),
   ("providerDecls", toJson l.providerDecls),
   ("providerDeclsSkipped", toJson l.providerDeclsSkipped), ("policies", toJson l.policies),
   ("providers", toJson l.providers)]

/-! ## The checks -/

/-- A check: its name, the work package that owns the Lean side, and how it runs. -/
structure Check where
  name : String
  owner : String
  run : Options → BundleExport → Verdict

open Surface.Temporal (Condition)

/-- A recorded `{"ok": null}` or error, as a unit result. -/
def unitStage (b : BundleExport) (s : Stage) : Except Missing (Result Unit) :=
  (b.stage (α := Json) s).map (·.map fun _ => ())

/-- A compiled schema the bridge recorded, as a stage result. -/
def compiledResult (stage : Stage) (r : Except String Cedar.Validation.Schema) : Result CompiledSchema :=
  match r with
  | .ok s => .ok ⟨s⟩
  | .error m => .error { stage, category := .cedarSchema, message := m }

/-- The stages of the pipeline that can fail, in the crate's order. -/
def failingStages : List Stage :=
  [.providerCheck, .mergeLibrary, .expand, .derive, .rejectArrays, .cedarify, .augment,
   .compileSchema]

/-- The error a parser rejected the input `key` with, if it rejected it. -/
def _root_.Dogwood.Frontend.BundleExport.inputError? (b : BundleExport) (key : String) :
    Option Error :=
  match decodePiece? (α := Json) key ((b.inputs.getObjVal? key).toOption.getD Json.null) with
  | .ok (some (.error e)) => some e
  | _ => none

/-- The first stage at which the crate failed, with its error. -/
def _root_.Dogwood.Frontend.BundleExport.firstError (b : BundleExport) : Option Error :=
  failingStages.findSome? fun s =>
    match b.stage (α := Json) s with
    | .ok (.error e) => some e
    | _ => none

/-- The first failure of the crate's public pipeline, from the export: the parsers' rejections
in the order the pipeline runs them, among the stages' failures. The pipeline reads the
provider declarations, then builds the service schema (the event schema, then the provider
check), parses the policy and the macro library, expands, and lowers, which derives the event
signatures from the action schema first: an action schema that does not parse fails there, in
the event-schema category, and the stages that need it do not run. -/
def _root_.Dogwood.Frontend.BundleExport.firstFailure (b : BundleExport) : Option Error :=
  let st := fun (s : Stage) => match b.stage (α := Json) s with
    | .ok (.error e) => some e
    | _ => none
  let derive := match st .derive with
    | some e => some e
    | none => (b.inputError? "actionSchema").map fun e =>
        { e with stage := .derive, category := .eventSchema }
  (b.inputError? "providers") <|> (b.inputError? "eventSchema") <|> st .providerCheck <|>
    (b.inputError? "policy") <|> (b.inputError? "library") <|> st .mergeLibrary <|>
    st .expand <|> derive <|> st .rejectArrays <|> st .cedarify <|> st .augment <|>
    st .compileSchema

def checks : List Check := [
  { name := "providerCheck", owner := "WP4", run := fun o b => withInputs (do
      let d ← b.input (α := ProviderDecls.Declarations) "providers"
      return (d, ← unitStage b .providerCheck)) fun (d, crate) =>
      compare o (Augment.checkDeclarations d) crate },
  { name := "mergeLibrary", owner := "WP1", run := fun o b => withInputs (do
      let p ← b.input (α := Surface.PolicySet) "policy"
      let lib ← b.input? (α := Library) "library"
      return (p, lib, ← b.stage (α := Merged) .mergeLibrary)) fun (p, lib, crate) =>
      compare o ((Macros.mergeLibrary p ((lib.map (·.defs)).getD [])).map (·.defs))
        (crate.map (·.defs)) },
  { name := "expand", owner := "WP1", run := fun o b => withInputs (do
      let p ← b.input (α := Surface.PolicySet) "policy"
      let m ← b.stageOk (α := Merged) .mergeLibrary
      return ({ p with defs := m.defs }, ← b.stage (α := Surface.PolicySet) .expand))
      fun (merged, crate) => compare o (Macros.expand merged) crate Alpha.policySet },
  { name := "rejectArrays", owner := "WP1", run := fun o b => withInputs (do
      return (← b.stageOk (α := Surface.PolicySet) .expand, ← unitStage b .rejectArrays))
      fun (e, crate) => compare o (Macros.rejectArrays e) crate },
  { name := "derive", owner := "WP2", run := fun o b => withInputs (do
      let dsl ← b.input (α := EventSchemaDsl.EventSchema) "eventSchema"
      let frag ← b.input (α := CedarSchema.Fragment) "actionSchema"
      return (dsl, frag, ← b.stage (α := DerivedEventSchema) .derive)) fun (dsl, frag, crate) =>
      compare o (Derive.derive dsl frag) crate },
  { name := "signatures", owner := "WP0", run := fun o b => withInputs (do
      return (← b.stageOk (α := DerivedEventSchema) .derive,
        ← b.stage (α := List EventSignature) .signatures)) fun (d, crate) =>
      compare o d.signatures crate },
  { name := "universalPins", owner := "WP0", run := fun o b => withInputs (do
      return (← b.stageOk (α := DerivedEventSchema) .derive,
        ← b.stage (α := List Pin) .universalPins)) fun (d, crate) =>
      compare o (universalPins d) crate },
  { name := "decisionKinds", owner := "WP0", run := fun o b => withInputs (do
      return (← b.stageOk (α := DerivedEventSchema) .derive,
        ← b.stage (α := List String) .decisionKinds)) fun (d, crate) =>
      compare o (decisionKinds d) crate },
  { name := "providerEnums", owner := "WP0", run := fun o b => withInputs (do
      let frag ← b.input (α := CedarSchema.Fragment) "actionSchema"
      let decls ← b.input? (α := ProviderDecls.Declarations) "providers"
      return (frag, decls, ← b.stageOk (α := Cedarified) .cedarify)) fun (frag, decls, c) =>
      if c.providerFields.isEmpty then .skipped "no provider fields" else
      let calls := c.providerFields.map fun f => (f.invocation.key, f.methods.map (·.name))
      let referenced := ProviderDecls.referencedEnums decls calls
      let names := match decls with
        | some d => ProviderDecls.providerEnumNames frag d referenced
        | none => []
      let types := c.providerFields.map fun f =>
        ProviderDecls.cedarTypeOf decls names f.invocation.key (f.methods.map (·.name))
      compare o (.ok (referenced, names, types) : Result _)
        (.ok (c.referencedEnums, c.enumNames, c.providerFields.map (·.cedarType))) },
  { name := "resolveSchema", owner := "WP2", run := fun o b => withInputs (do
      return (← b.input (α := CedarSchema.Fragment) "actionSchema",
        ← decodeValidatorSchema b.baseValidatorSchema)) fun (frag, crate) =>
      compare o ((CedarSchema.resolve frag).map (CompiledSchema.mk ·)) (compiledResult .resolveSchema crate)
        (messages := false) },
  { name := "cedarify", owner := "WP3", run := fun o b => withInputs (do
      let e ← b.stageOk (α := Surface.PolicySet) .expand
      let frag ← b.input (α := CedarSchema.Fragment) "actionSchema"
      let decls ← b.input? (α := ProviderDecls.Declarations) "providers"
      return (e, frag, decls, ← b.stage (α := Cedarified) .cedarify))
      fun (e, frag, decls, crate) =>
      compare o (Cedarify.cedarify e frag decls) crate Alpha.cedarified },
  { name := "injectPins", owner := "WP5", run := fun o b => withInputs (do
      return (← b.stageOk (α := DerivedEventSchema) .derive, ← b.stageOk (α := Cedarified) .cedarify,
        ← b.stage (α := List Condition) .injectPins)) fun (d, c, crate) => perLeaf c.contextFields fun _ =>
      compare o (c.contextFields.mapM fun f => LeafPasses.injectPins d f.temporal.condition) crate
        (List.map Alpha.normalize) },
  { name := "identity", owner := "WP5", run := fun o b => withInputs (do
      return (← b.stageOk (α := Cedarified) .cedarify, ← b.stageOk (α := List Condition) .injectPins,
        ← b.stage (α := Identity) .identity)) fun (c, pinned, crate) =>
      compare o (RuleIdentity.leaves c (withConditions c.contextFields pinned)) (crate.map (·.leaves)) },
  { name := "augment", owner := "WP4", run := fun o b => withInputs (do
      let frag ← b.input (α := CedarSchema.Fragment) "actionSchema"
      let decls ← b.input? (α := ProviderDecls.Declarations) "providers"
      return (frag, decls, ← b.stageOk (α := Cedarified) .cedarify,
        ← b.stageOk (α := List Condition) .injectPins, ← b.stage (α := CedarSchema.Fragment) .augment))
      fun (frag, decls, c, pinned, crate) =>
      compare o (Augment.augment frag decls c.referencedEnums (withConditions c.contextFields pinned)
        c.providerFields) crate },
  { name := "resolveProviders", owner := "WP4", run := fun o b => withInputs (do
      let decls ← b.input? (α := ProviderDecls.Declarations) "providers"
      return (decls, ← b.stageOk (α := Cedarified) .cedarify,
        ← b.stage (α := List ResolvedProvider) .resolveProviders)) fun (decls, c, crate) =>
      compare o (Augment.resolveProviders decls c.enumNames c.providerFields) crate },
  { name := "compileSchema", owner := "WP2", run := fun o b => withInputs (do
      let aug ← b.stageOk (α := CedarSchema.Fragment) .augment
      let crate ← match ← unitStage b .compileSchema with
        | .error e => pure (.error e)
        | .ok () => pure (compiledResult .compileSchema (← decodeValidatorSchema b.validatorSchema))
      return (aug, crate)) fun (aug, crate) =>
      compare o (Result.atStage .compileSchema ((CedarSchema.resolve aug).map (CompiledSchema.mk ·))) crate
        (messages := false) },
  { name := "unorder", owner := "WP5", run := fun o b => withInputs (do
      return (← b.stageOk (α := List Condition) .injectPins, ← b.stage (α := List Condition) .unorder))
      fun (pinned, crate) => perLeaf pinned fun _ =>
      compare o (pinned.mapM LeafPasses.unorderTimepoints) crate (List.map Alpha.normalize) },
  { name := "relativize", owner := "WP5", run := fun o b => withInputs (do
      return (← b.stageOk (α := DerivedEventSchema) .derive, ← b.stageOk (α := List Pin) .universalPins,
        ← b.stageOk (α := List Condition) .unorder, ← b.stage (α := List Condition) .relativize))
      fun (d, pins, ex, crate) => perLeaf ex fun _ =>
      compare o (ex.mapM (LeafPasses.relativize d pins)) crate (List.map Alpha.normalize) },
  { name := "validate", owner := "WP6", run := fun _ b => withInputs (do
      let l ← b.crateLowered
      match ← b.conformanceOutcome with
      | .lowered c => return (l, c.crateFindings)
      | .rejected st m => throw (.notRun s!"conformance record (rejected at {st}: {m.take 80})"))
      fun (l, crate) =>
      match Validate.validate l with
      | .error e =>
        if e.category == .notImplemented then .notImplemented e.message
        else .disagree s!"Lean {Error.render e}; the crate's validator reports {crate.length} findings"
      | .ok lean =>
        let cats := fun (fs : List Conformance.CrateFinding) =>
          ((fs.filterMap Conformance.crateCategory).map (·.name)).eraseDups.mergeSort
            (fun a b => decide (a ≤ b))
        if cats lean == cats crate then .agree
        else .disagree s!"categories: Lean {cats lean} ≠ crate {cats crate}" },
  { name := "conformance", owner := "WP0", run := fun o b => withInputs (do
      let l ← b.crateLowered
      match ← b.conformanceOutcome with
      | .lowered c => return (l, c)
      | .rejected st m => throw (.notRun s!"conformance record (rejected at {st}: {m.take 80})"))
      fun (l, crate) =>
      match l.toConformance with
      | .error e => .disagree s!"toConformance: {e}"
      | .ok lean =>
        let diffs := (conformanceFields lean).zip (conformanceFields crate) |>.filterMap
          fun ((k, a), (_, b')) =>
            let a := prep o a
            let b' := prep o b'
            if a == b' then none else some s!"{k}{(firstDiff "" a b').getD ""}"
        if diffs.isEmpty then .agree else .disagree ("; ".intercalate diffs) },
  { name := "pipeline", owner := "all", run := fun o b => withInputs (do
      let i ← b.parsedInputs
      let crate ← match ← b.crateOutcome with
        | .rejected e =>
          match b.firstError with
          | some e' => pure (Except.error e')
          | none => throw (.notRun s!"the failing stage (the crate rejects at no recorded stage: {e.message.take 80})")
        | .lowered _ => Except.ok <$> b.crateLowered
      return (i, crate)) fun (i, crate) =>
      -- Cedar's own errors are compared by category, as the stage checks compare them.
      let messages := match crate with
        | .error e => e.category != .cedarSchema
        | .ok _ => true
      compare o (Frontend.lower i) crate (messages := messages) },
  { name := "export", owner := "WP0", run := fun _ b =>
      if b.many != Json.null then .skipped "several policy sets lowered together" else
      if (b.inputs.getObjVal? "ids").toOption.getD .null != .null ||
          (b.inputs.getObjVal? "distincter").toOption.getD .null != .null then
        .skipped "lowered with stable ids or a distincter, the stages without"
      else
      withInputs b.crateOutcome fun
      | .lowered r =>
        if r.mismatches.isEmpty then .agree
        else .disagree s!"the stages disagree with the pipeline on {r.mismatches}"
      | .rejected e =>
        match b.firstFailure with
        | some e' => if e'.category == e.category then .agree
          else .disagree s!"the pipeline rejects with {Error.render e}, the stages first with {Error.render e'}"
        | none =>
          -- A parser rejected an input: no stage ran.
          if e.category == .parse || e.category == .eventSchema || e.category == .providers ||
              e.category == .cedarify then .agree
          else .disagree s!"the pipeline rejects with {Error.render e}, and no stage failed" }
]

/-! ## Reports -/

/-- What a check found over a group's bundles. -/
structure Tally where
  agree : Nat := 0
  renamed : Nat := 0
  disagree : List (String × String) := []
  expected : List (String × String) := []
  notImplemented : Nat := 0
  skipped : Nat := 0
  undecodable : List (String × String) := []

/-- A baseline: the disagreements that are expected, as `<group> | <bundle> | <check>`. -/
abbrev Baseline := List (String × String × String)

def parseBaseline (text : String) : Baseline :=
  (text.splitOn "\n").filterMap fun line =>
    let line := line.trimAscii.toString
    if line.isEmpty || line.startsWith "#" then none
    else match line.splitOn " | " with
      | [g, b, c] => some (g.trimAscii.toString, b.trimAscii.toString, c.trimAscii.toString)
      | _ => none

def Tally.add (t : Tally) (expected : Bool) (bundle : String) : Verdict → Tally
  | .agree => { t with agree := t.agree + 1 }
  | .agreeUpToRenaming => { t with renamed := t.renamed + 1 }
  | .disagree d => if expected then { t with expected := t.expected ++ [(bundle, d)] }
    else { t with disagree := t.disagree ++ [(bundle, d)] }
  | .notImplemented _ => { t with notImplemented := t.notImplemented + 1 }
  | .skipped _ => { t with skipped := t.skipped + 1 }
  | .undecodable why => { t with undecodable := t.undecodable ++ [(bundle, why)] }

/-- Pad `s` to `n` characters. -/
def pad (s : String) (n : Nat) : String := s ++ String.ofList (List.replicate (n - s.length) ' ')

def padLeft (s : String) (n : Nat) : String := String.ofList (List.replicate (n - s.length) ' ') ++ s

/-- One group's report, and whether it has no unexpected disagreement and nothing undecodable. -/
def report (o : Options) (baseline : Baseline) (group : String) (selected : List Check)
    (bundles : List BundleExport) : String × Bool :=
  let tallies := selected.map fun c =>
    (c, bundles.foldl (init := ({} : Tally)) fun t b =>
      t.add (baseline.contains (group, b.name, c.name)) b.name (c.run o b))
  let header := s!"== {group}: {bundles.length} bundles\n" ++
    "  " ++ pad "check" 18 ++ pad "owner" 6 ++ padLeft "agree" 7 ++ padLeft "renamed" 9 ++
    padLeft "disagree" 10 ++ padLeft "expected" 10 ++ padLeft "not impl" 10 ++ padLeft "skipped" 9 ++
    padLeft "undecodable" 13
  let rows := tallies.map fun (c, t) =>
    "  " ++ pad c.name 18 ++ pad c.owner 6 ++ padLeft (toString t.agree) 7 ++
      padLeft (toString t.renamed) 9 ++ padLeft (toString t.disagree.length) 10 ++
      padLeft (toString t.expected.length) 10 ++ padLeft (toString t.notImplemented) 10 ++
      padLeft (toString t.skipped) 9 ++ padLeft (toString t.undecodable.length) 13
  let details := tallies.flatMap fun (c, t) =>
    (t.disagree.take o.diffs).map (fun (b, d) => s!"  {c.name} disagrees on {b}: {d}") ++
    (if t.disagree.length > o.diffs then [s!"  {c.name}: {t.disagree.length - o.diffs} more disagreements"] else []) ++
    (t.undecodable.take o.diffs).map fun (b, d) => s!"  {c.name} cannot decode {b}: {d}"
  let ok := tallies.all fun (_, t) => t.disagree.isEmpty && t.undecodable.isEmpty
  ("\n".intercalate (header :: rows ++ details), ok)

end Dogwood.Frontend.Diff
