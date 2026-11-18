import Dogwood.Frontend.Validate.Temporal

/-!
# The provider dialect's checks

The crate's validator checks each hoisted provider leaf (`ProviderDialect::validate`,
`extension/provider/validate.rs`), in this order:

1. the provider is declared;
2. every entity type its types name, by its exported name when it is a used provider enum, is a
   declared enum entity type;
3. it has the declared number of arguments, and each literal argument the declared kind;
4. every path argument, of the invocation and of each method, exists on every target action that
   admits a request environment, and on every entity type the rule admits; a bare `context` is
   not an argument;
5. every argument has its declared Cedar type exactly (`ParamType::to_cedar_type_with`), in every
   request environment, a set's elements the element type;
6. each method of the chain does not shadow a Cedar extension method, is declared, takes the
   Cedar type the stage before it produces when it declares one, and has the declared number of
   arguments of the declared kinds.

Every finding is an error of the `provider` code. After the first check, a call warns once per
unknown `paramType` in the types it uses (`ProviderDecl::collect_fallback_warnings`): the type
falls back to `String`. The warnings are `providerFallbacks`; the validator reports each once
per run of leaves of one source (`Validate.providerWarnings`).
-/

namespace Dogwood.Frontend.Validate

open Cedar.Spec (EntityType EntityUID Attr)
open Cedar.Validation (CedarType RecordType QualifiedType Schema ActionSchemaEntry)
open ProviderDecls (ParamType ProviderDecl MethodDecl)
open Provider (Arg)

mutual

/-- The Cedar type a declared parameter type gives its value (crate `CType::from_param`): a used
provider enum by its exported name; an unknown kind and an entity without a type `String`, a set
without items `Set<String>`. -/
def paramCType (names : List (String × String)) : ParamType → CedarType
  | ⟨kind, fields, items, required, et⟩ =>
    match kind with
    | "string" => .string
    | "integer" | "long" => .int
    | "bool" | "boolean" => .bool .anyBool
    | "decimal" => .ext .decimal
    | "set" => .set (paramCTypeOpt names items)
    | "record" => .record (Cedar.Data.Map.make (paramCTypeFields names required fields))
    | "entity" =>
      match et with
      | some d => .entity (parseEntityType ((names.lookup d).getD d))
      | none => .string
    | _ => .string

def paramCTypeOpt (names : List (String × String)) : Option ParamType → CedarType
  | none => .string
  | some p => paramCType names p

def paramCTypeFields (names : List (String × String)) (required : List String) :
    List (String × ParamType) → List (Attr × QualifiedType)
  | [] => []
  | (n, p) :: rest =>
    (n, if required.contains n then .required (paramCType names p) else .optional (paramCType names p)) ::
      paramCTypeFields names required rest

end

/-- The declared kind a literal argument satisfies (crate `arg_kind`). -/
def argKind : Arg → Option String
  | .string _ => some "string"
  | .integer _ => some "integer"
  | .decimal _ => some "decimal"
  | .bool _ => some "bool"
  | .set _ => some "set"
  | .field _ => none

/-- Whether a declared kind accepts an argument of a kind (crate `param_type_accepts`). -/
def paramTypeAccepts (declared actual : String) : Bool :=
  match actual with
  | "string" => declared == "string"
  | "integer" => declared == "integer" || declared == "long"
  | "decimal" => declared == "decimal"
  | "bool" => declared == "bool" || declared == "boolean"
  | "set" => declared == "set"
  | _ => false

/-- The Cedar extension methods a provider method may not shadow (crate
`is_cedar_extension_method`). -/
def cedarExtensionMethods : List String :=
  ["lessThan", "lessThanOrEqual", "greaterThan", "greaterThanOrEqual", "contains", "containsAll",
   "containsAny", "isEmpty", "hasTag", "getTag", "isIpv4", "isIpv6", "isLoopback", "isMulticast",
   "isInRange", "offset", "durationSince", "toDate", "toTime", "toMilliseconds", "toSeconds",
   "toMinutes", "toHours", "toDays"]

/-- A declared type as a diagnostic shows it (crate `display_param`). -/
def displayParam (p : ParamType) : String :=
  match p.paramType, p.entityType with
  | "entity", some n => n
  | kind, _ => kind

mutual

/-- An argument as written, for a diagnostic (crate `render_arg`): a string and a decimal's text
as Rust's `Debug` writes them, a set with its elements. -/
def renderArg : Arg → String
  | .field p => fieldPathJoin p
  | .string s => Escape.strDebug s
  | .integer i => toString i.toInt
  | .decimal d => "decimal(" ++ Escape.strDebug d ++ ")"
  | .bool b => toString b
  | .set items => "[" ++ ", ".intercalate (renderArgs items) ++ "]"

def renderArgs : List Arg → List String
  | [] => []
  | a :: rest => renderArg a :: renderArgs rest

end

/-- A Cedar type in Cedar-familiar form, for a provider diagnostic (crate `display_ctype`): an
entity type as `entity:Ns::T`, a set by its element, a record as `record`. -/
def displayCType : CedarType → String
  | .entity ety => "entity:" ++ nameText ety
  | .set t => "Set<" ++ displayCType t ++ ">"
  | .record _ => "record"
  | t => renderCType t

/-! ## Fallback warnings -/

/-- The kinds of `paramType` the crate knows (crate `KNOWN_PARAM_TYPES`). -/
def knownParamTypes : List String :=
  ["string", "integer", "long", "bool", "boolean", "decimal", "set", "record", "entity"]

mutual

/-- A warning for this type, or for the first type nested in it on each path, whose kind is
unknown and so falls back to `String` (crate `ParamType::collect_fallback_warnings`). -/
def paramFallbacks (at_ : String) : ParamType → List String
  | ⟨kind, fields, items, _, _⟩ =>
    if !knownParamTypes.contains kind then
      [s!"{at_}: unknown paramType `{kind}` does not match a known paramType; falling back to String (deprecated: an unknown paramType becomes an error in the next major version)"]
    else paramFallbacksOpt (at_ ++ ".items") items ++ paramFallbacksFields at_ fields

def paramFallbacksOpt (at_ : String) : Option ParamType → List String
  | none => []
  | some p => paramFallbacks at_ p

def paramFallbacksFields (at_ : String) : List (String × ParamType) → List String
  | [] => []
  | (n, p) :: rest => paramFallbacks (at_ ++ "." ++ n) p ++ paramFallbacksFields at_ rest

end

/-- The fallback warnings of a call of the provider `key` with the chained `methods` (crate
`ProviderDecl::collect_fallback_warnings`): its argument and output types, then those of each
declared method of the chain. -/
def providerFallbacks (key : String) (decl : ProviderDecl) (methods : List String) : List String :=
  let at_ := s!"provider `{key}`"
  decl.argumentTypes.zipIdx.flatMap (fun (p, i) => paramFallbacks s!"{at_} argumentTypes[{i}]" p) ++
    paramFallbacks s!"{at_} outputType" decl.outputType ++
    methods.flatMap fun m =>
      match decl.methods.lookup m with
      | none => []
      | some md =>
        let at_ := s!"{at_} method `{m}`"
        md.argumentTypes.zipIdx.flatMap (fun (p, i) => paramFallbacks s!"{at_} argumentTypes[{i}]" p) ++
          (md.inputType.map (paramFallbacks s!"{at_} inputType")).getD [] ++
          paramFallbacks s!"{at_} outputType" md.outputType

/-- The fallback warnings of a provider leaf (none for an undeclared provider). -/
def leafFallbacks (f : LoweredProviderField) : List String :=
  match f.declaration with
  | none => []
  | some decl => providerFallbacks f.invocation.key decl (f.methods.map (·.name))

/-- What checking one provider leaf reads. -/
structure ProviderCtx where
  schema : Schema
  key : String
  names : List (String × String)
  /-- The target actions the schema declares. -/
  targets : List (EntityUID × ActionSchemaEntry)
  principal : ScopeConstraint
  resource : ScopeConstraint

namespace ProviderCtx

variable (C : ProviderCtx)

def narrow : Root → ScopeConstraint
  | .principal => C.principal
  | .resource => C.resource

/-- The request environments of the leaf's rule (crate `request_envs`). -/
def envs : List ReqEnv :=
  C.targets.flatMap fun (uid, entry) =>
    (admittedTypes C.schema entry .principal C.principal).flatMap fun p =>
      (admittedTypes C.schema entry .resource C.resource).map fun r => ⟨uid, entry, p, r⟩

/-- The existence problem of one path argument (crate `check_one_field_path`): the first target
action, admitting a request environment, on which it is missing. -/
def pathProblem (path : List String) : Option String :=
  match path with
  | [] => none
  | [root] =>
    if root == "context" then
      some s!"provider `{C.key}`: argument `context` is the whole request context, which is not an argument; pass one of its attributes"
    else none
  | root :: rest@(_ :: _) =>
    C.targets.findSome? fun (uid, entry) =>
      if !admitsAnyEnv C.schema entry C.principal C.resource then none
      else if root == "context" then
        match resolveContextPath entry.context rest with
        | .resolved _ => none
        | _ => some s!"provider `{C.key}`: argument `{pathUnder "context" rest}` is not present in the context of action `{actionText uid}`"
      else
        let r? : Option Root := if root == "principal" then some .principal
          else if root == "resource" then some .resource else none
        match r? with
        | none => none
        | some r =>
          match resolveScopePath C.schema entry r (C.narrow r) rest with
          | .missing _ seg | .nonRecord seg =>
            some s!"provider `{C.key}`: argument `{fieldPathJoin path}` is not present on the `{root}` of action `{actionText uid}` (no attribute `{seg}`)"
          | _ => none

/-- The existence problems of a list of arguments, recursing into sets (crate
`check_field_path_args`). -/
def pathProblems : List Arg → List String
  | [] => []
  | .set items :: rest => pathProblems items ++ pathProblems rest
  | .field p :: rest => (C.pathProblem p).toList ++ pathProblems rest
  | _ :: rest => pathProblems rest

/-- The Cedar type an argument other than a set has in a request environment (crate
`arg_type`). -/
def argType? (e : ReqEnv) : Arg → Option CedarType
  | .string _ => some .string
  | .integer _ => some .int
  | .decimal _ => some (.ext .decimal)
  | .bool _ => some (.bool .anyBool)
  | .set _ => none
  | .field [] => none
  | .field (root :: rest) =>
    if root == "context" then contextPathType? e.entry.context rest
    else
      let ety? : Option EntityType := if root == "principal" then some e.principal
        else if root == "resource" then some e.resource else none
      match ety?, rest with
      | none, _ => none
      | some ety, [] => some (.entity ety)
      | some ety, _ => scopeAttrCedarType? C.schema ety rest

/-- A type problem found in an environment (crate `ArgTyping::report`): the type the argument
has, `shown`, and the declared one, a set by its element type; when the two read alike, both in
full. A path into the principal or the resource names the entity type of the environment. -/
def typeProblem (arg : Arg) (shown : String) (declared : ParamType) (e : ReqEnv) : String :=
  let declaredTy := paramCType C.names declared
  let wanted := match declaredTy with
    | .set _ => displayCType declaredTy
    | _ => displayParam declared
  let (shown, wanted) :=
    if shown == wanted then (((C.argType? e arg).map renderCType).getD shown, renderCType declaredTy)
    else (shown, wanted)
  let scope := match arg with
    | .field ("principal" :: _) => s!" when the principal is a `{nameText e.principal}`"
    | .field ("resource" :: _) => s!" when the resource is a `{nameText e.resource}`"
    | _ => ""
  s!"provider `{C.key}`: argument `{renderArg arg}` has type `{shown}` on action `{actionText e.uid}`{scope} but the provider declares argument type `{wanted}`"

/-- Whether a scope attribute argument has a different type on the entity types the rule admits,
and the problem then (crate `ArgTyping::ambiguous`). -/
def ambiguity (arg : Arg) (declared : ParamType) : Option String :=
  match arg with
  | .field (root :: rest@(_ :: _)) =>
    let r? : Option Root := if root == "principal" then some .principal
      else if root == "resource" then some .resource else none
    match r? with
    | none => none
    | some r =>
      C.envs.findSome? fun e =>
        match resolveScopePath C.schema e.entry r (C.narrow r) rest with
        | .ambiguous types =>
          some s!"provider `{C.key}`: argument `{renderArg arg}` has a different type on each `{root}` type the rule admits (`{"`, `".intercalate types}`), so it cannot match the declared argument type `{displayParam declared}`"
        | _ => none
  | _ => none

/-- The type problem of an argument other than a set, in the first environment where its type
is not the declared one. -/
def argTypeProblemsScalar (arg : Arg) (declared : ParamType) (declaredTy : CedarType) :
    List String :=
  match C.ambiguity arg declared with
  | some m => [m]
  | none =>
    (C.envs.findSome? fun e =>
      match C.argType? e arg with
      | some ty => if ty == declaredTy then none else some (C.typeProblem arg (displayCType ty) declared e)
      | none => none).toList

mutual

/-- The type problems of one argument against its declared type (crate `ArgTyping::check`). At
the top level a literal, and a set where no set is declared, are the literal check's; a set's
elements are each checked against the element type. -/
def argTypeProblems (top : Bool) : Arg → ParamType → List String
  | .set items, declared =>
    match paramCType C.names declared with
    | .set _ => setItemProblems items (declared.items.getD { paramType := "string" })
    | _ =>
      if top then []
      else match C.envs.head? with
        | some e => [C.typeProblem (.set items) "Set" declared e]
        | none => []
  | .string s, declared =>
    if top then [] else C.argTypeProblemsScalar (.string s) declared (paramCType C.names declared)
  | .integer i, declared =>
    if top then [] else C.argTypeProblemsScalar (.integer i) declared (paramCType C.names declared)
  | .decimal d, declared =>
    if top then [] else C.argTypeProblemsScalar (.decimal d) declared (paramCType C.names declared)
  | .bool b, declared =>
    if top then [] else C.argTypeProblemsScalar (.bool b) declared (paramCType C.names declared)
  | .field p, declared =>
    if p.length < 2 && p.head? == some "context" then []
    else C.argTypeProblemsScalar (.field p) declared (paramCType C.names declared)

/-- The type problems of a set's elements, each against the element type. -/
def setItemProblems : List Arg → ParamType → List String
  | [], _ => []
  | item :: rest, element => argTypeProblems false item element ++ setItemProblems rest element

end

end ProviderCtx

/-- The literal-kind problems of arguments against declared types. -/
def literalProblems (key : String) (what : String) (args : List Arg) (params : List ParamType) :
    List String :=
  (args.zip params).filterMap fun (arg, param) =>
    match argKind arg with
    | some actual =>
      if paramTypeAccepts param.paramType actual then none
      else some s!"provider `{key}`: {what}argument of type `{actual}` does not match the declared `{displayParam param}`"
    | none => none

/-- The problems of the method chain (crate `ProviderDialect::validate`, the method chain). -/
def chainProblems (C : ProviderCtx) (decl : ProviderDecl) : ParamType → List Provider.MethodCall →
    List String
  | _, [] => []
  | pipeline, m :: ms =>
    if cedarExtensionMethods.contains m.name then
      s!"provider `{C.key}`: method `{m.name}` collides with a built-in Cedar extension method; rename the declared method" ::
        chainProblems C decl pipeline ms
    else
      match decl.methods.lookup m.name with
      | none =>
        let available := if decl.methods.isEmpty then s!"provider `{C.key}` declares no methods"
          else s!"declared methods on `{C.key}` are: " ++ ", ".intercalate (decl.methods.map (·.1))
        [s!"provider `{C.key}`: method `{m.name}` is not declared ({available})"]
      | some md =>
        (match md.inputType with
          | some input =>
            if paramCType C.names input == paramCType C.names pipeline then []
            else [s!"provider `{C.key}`: method `{m.name}` expects an input of type `{displayParam input}` but the preceding stage produces `{displayParam pipeline}`"]
          | none => []) ++
        (if md.argumentTypes.length != m.args.length then
          [s!"provider `{C.key}`: method `{m.name}` expects {md.argumentTypes.length} argument(s) but got {m.args.length}"]
        else literalProblems C.key s!"method `{m.name}` " m.args md.argumentTypes) ++
        chainProblems C decl md.outputType ms

/-- The checking context of a provider leaf. -/
def providerCtx (S : Schema) (f : LoweredProviderField) : ProviderCtx where
  schema := S
  key := f.invocation.key
  names := f.entityTypeNames
  targets := f.targetActions.filterMap fun (ns, id) => action? S ns id
  principal := f.principal
  resource := f.resource

/-- Every finding of the provider dialect on one leaf. -/
def providerLeafFindings (S : Schema) (f : LoweredProviderField) : List String :=
  let key := f.invocation.key
  match f.declaration with
  | none => [s!"provider `{key}` is not present in the provider declarations"]
  | some decl =>
    let C := providerCtx S f
    let entityTypes := (decl.referencedEntityTypes (f.methods.map (·.name))).filterMap fun name =>
      let inSchema := (f.entityTypeNames.lookup name).getD name
      match S.ets.find? (parseEntityType inSchema) with
      | none => some s!"provider `{key}`: entityType `{name}` is not declared in the policy schema or the provider declarations' `entityTypes`"
      | some (.standard _) => some s!"provider `{key}`: entityType `{name}` is not an enum entity type; provider values may only be enum entities"
      | some (.enum _) => none
    if decl.argumentTypes.length != f.invocation.args.length then
      entityTypes ++ [s!"provider `{key}` expects {decl.argumentTypes.length} argument(s) but got {f.invocation.args.length}"]
    else
      entityTypes ++
      literalProblems key "" f.invocation.args decl.argumentTypes ++
      C.pathProblems f.invocation.args ++
      f.methods.flatMap (fun m => C.pathProblems m.args) ++
      ((f.invocation.args.zip decl.argumentTypes).flatMap fun (a, p) => C.argTypeProblems true a p) ++
      f.methods.flatMap (fun m =>
        match decl.methods.lookup m.name with
        | some md => (m.args.zip md.argumentTypes).flatMap fun (a, p) => C.argTypeProblems true a p
        | none => []) ++
      chainProblems C decl decl.outputType f.methods

/-! ## Where the findings are

The crate reports a provider leaf's findings at the invocation's span, and those about a method of
the chain (its arguments' paths and types, and the chain's checks) at the method's span, each
rebased from the block's body to the rule's source (`ProviderField::body_base`). These functions
are `chainProblems` and `providerLeafFindings` with each finding's span; they find the same
messages (`Thm.Frontend.providerLeafLocated_messages`). -/

/-- A span inside a `provider { … }` block's body, in the rule's source (crate `Span::rebased`). -/
def rebaseBody (base : Nat) (sp : Span) : Span := ⟨base + sp.start, base + sp.end⟩

/-- `chainProblems`, each finding at its method's span. -/
def chainLocated (C : ProviderCtx) (decl : ProviderDecl) (base : Nat) :
    ParamType → List Provider.MethodCall → List (String × Span)
  | _, [] => []
  | pipeline, m :: ms =>
    if cedarExtensionMethods.contains m.name then
      (s!"provider `{C.key}`: method `{m.name}` collides with a built-in Cedar extension method; rename the declared method", rebaseBody base m.span) ::
        chainLocated C decl base pipeline ms
    else
      match decl.methods.lookup m.name with
      | none =>
        let available := if decl.methods.isEmpty then s!"provider `{C.key}` declares no methods"
          else s!"declared methods on `{C.key}` are: " ++ ", ".intercalate (decl.methods.map (·.1))
        [(s!"provider `{C.key}`: method `{m.name}` is not declared ({available})", rebaseBody base m.span)]
      | some md =>
        ((match md.inputType with
          | some input =>
            if paramCType C.names input == paramCType C.names pipeline then []
            else [s!"provider `{C.key}`: method `{m.name}` expects an input of type `{displayParam input}` but the preceding stage produces `{displayParam pipeline}`"]
          | none => []) ++
        (if md.argumentTypes.length != m.args.length then
          [s!"provider `{C.key}`: method `{m.name}` expects {md.argumentTypes.length} argument(s) but got {m.args.length}"]
        else literalProblems C.key s!"method `{m.name}` " m.args md.argumentTypes)).map
          (·, rebaseBody base m.span) ++
        chainLocated C decl base md.outputType ms

/-- `providerLeafFindings`, each finding with its span in the source of the leaf's rule. -/
def providerLeafLocated (S : Schema) (f : LoweredProviderField) : List (String × Span) :=
  let key := f.invocation.key
  let inv := rebaseBody f.bodyBase f.invocation.span
  let at_ := fun (sp : Span) (ms : List String) => ms.map (·, sp)
  match f.declaration with
  | none => [(s!"provider `{key}` is not present in the provider declarations", inv)]
  | some decl =>
    let C := providerCtx S f
    let entityTypes := (decl.referencedEntityTypes (f.methods.map (·.name))).filterMap fun name =>
      let inSchema := (f.entityTypeNames.lookup name).getD name
      match S.ets.find? (parseEntityType inSchema) with
      | none => some s!"provider `{key}`: entityType `{name}` is not declared in the policy schema or the provider declarations' `entityTypes`"
      | some (.standard _) => some s!"provider `{key}`: entityType `{name}` is not an enum entity type; provider values may only be enum entities"
      | some (.enum _) => none
    if decl.argumentTypes.length != f.invocation.args.length then
      at_ inv (entityTypes ++ [s!"provider `{key}` expects {decl.argumentTypes.length} argument(s) but got {f.invocation.args.length}"])
    else
      at_ inv entityTypes ++
      at_ inv (literalProblems key "" f.invocation.args decl.argumentTypes) ++
      at_ inv (C.pathProblems f.invocation.args) ++
      f.methods.flatMap (fun m => at_ (rebaseBody f.bodyBase m.span) (C.pathProblems m.args)) ++
      at_ inv ((f.invocation.args.zip decl.argumentTypes).flatMap fun (a, p) => C.argTypeProblems true a p) ++
      f.methods.flatMap (fun m => at_ (rebaseBody f.bodyBase m.span)
        (match decl.methods.lookup m.name with
        | some md => (m.args.zip md.argumentTypes).flatMap fun (a, p) => C.argTypeProblems true a p
        | none => [])) ++
      chainLocated C decl f.bodyBase decl.outputType f.methods

end Dogwood.Frontend.Validate
