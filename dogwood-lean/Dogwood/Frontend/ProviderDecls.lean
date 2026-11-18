import Dogwood.Frontend.CedarSchema

/-!
# Provider declarations, as parsed

The information-provider declarations (`providers.json`) as the crate deserializes them
(`extension/provider/declarations.rs`), before their consistency check
(`ProviderDeclarations::check`, which is frontend work). Maps are lists of `(key, value)` pairs
in key order, as the crate's `BTreeMap`s iterate.

The pure helpers of the crate that several stages use are defined here:
`exportedEnumBasename`, `ParamType.toCedarTypeWith` (the Cedar type text of a hoisted provider
field), `ProviderDecl.referencedEntityTypes` (the enums a call references), and
`providerEnumHome` and `providerEnumNames` (where and under which names the used enums are
exported). Cedarify and schema augmentation both read them.
-/

namespace Dogwood.Frontend.ProviderDecls

/-- A provider parameter or output type (crate `ParamType`). `paramType` is the kind as written;
an unknown kind falls back to `String`. -/
structure ParamType where
  paramType : String
  /-- For `record`: the field types, in name order. -/
  fields : List (String × ParamType) := []
  /-- For `set`: the element type. -/
  items : Option ParamType := none
  required : List String := []
  /-- For `entity`: the qualified enum entity type. -/
  entityType : Option String := none
deriving Repr, BEq, Inhabited

/-- A method callable on a provider's output (crate `MethodDecl`). -/
structure MethodDecl where
  argumentTypes : List ParamType
  outputType : ParamType
  inputType : Option ParamType
deriving Repr, BEq, Inhabited

/-- How a provider is evaluated (crate `Implementation`); the frontend carries it unread. -/
inductive Implementation where
  | rhai (script : Option String) (scriptFile : Option String)
deriving Repr, BEq, Inhabited

/-- One declared provider (crate `ProviderDecl`). -/
structure ProviderDecl where
  argumentTypes : List ParamType
  outputType : ParamType
  methods : List (String × MethodDecl)
  implementation : Option Implementation
deriving Repr, BEq, Inhabited

/-- A declared enum entity type (crate `EntityTypeDecl`). -/
structure EntityTypeDecl where
  values : List String
  annotations : List (String × String)
deriving Repr, BEq, Inhabited

/-- The declarations file (crate `ProviderDeclarations`), keyed by qualified name. -/
structure Declarations where
  available : List (String × ProviderDecl)
  entityTypeDecls : List (String × EntityTypeDecl)
deriving Repr, BEq, Inhabited

/-- The declaration of the provider `key` (`Ns::Fn`). -/
def Declarations.get (d : Declarations) (key : String) : Option ProviderDecl :=
  d.available.lookup key

/-- The basename a provider enum is exported under in the action schema's namespace: its
declared name with each `::` replaced by `_` (crate `exported_enum_basename`). -/
def exportedEnumBasename (declared : String) : String :=
  "_".intercalate (declared.splitOn "::")

mutual

/-- Every `entityType` named in the type, at any depth, in the order the crate's traversal
meets them (crate `ParamType::collect_entity_types`, before its set collects them). -/
def ParamType.entityTypes : ParamType → List String
  | ⟨_, fields, items, _, et⟩ => et.toList ++ ParamType.entityTypesOpt items ++
      ParamType.entityTypesFields fields

def ParamType.entityTypesOpt : Option ParamType → List String
  | none => []
  | some p => ParamType.entityTypes p

def ParamType.entityTypesFields : List (String × ParamType) → List String
  | [] => []
  | (_, p) :: rest => ParamType.entityTypes p ++ ParamType.entityTypesFields rest

end

/-- `xs` sorted and without duplicates, as a `BTreeSet<String>` iterates. -/
def sortedSet (xs : List String) : List String :=
  (xs.mergeSort (fun a b => decide (a ≤ b))).eraseDups

/-- The entity types a call to this provider references: its argument and output types, and
those of the chained methods named in `methods` (crate
`ProviderDecl::referenced_entity_types`), as a sorted set. -/
def ProviderDecl.referencedEntityTypes (d : ProviderDecl) (methods : List String) : List String :=
  let base := (d.argumentTypes ++ [d.outputType]).flatMap ParamType.entityTypes
  let ofMethods := methods.flatMap fun m =>
    match d.methods.lookup m with
    | some md => (md.argumentTypes ++ md.inputType.toList ++ [md.outputType]).flatMap
        ParamType.entityTypes
    | none => []
  sortedSet (base ++ ofMethods)

mutual

/-- The words Cedar reserves (`RESERVED_IDS`). -/
def cedarReservedIds : List String :=
  ["true", "false", "if", "then", "else", "in", "is", "like", "has", "__cedar"]

/-- A character that may start a Cedar identifier. -/
def bareHead (c : Char) : Bool := c == '_' || ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z')

/-- A character that may continue a Cedar identifier. -/
def bareTail (c : Char) : Bool := bareHead c || ('0' ≤ c && c ≤ '9')

/-- A record attribute name Cedar's schema printer writes bare (Cedar `is_normalized_ident`):
`[_a-zA-Z][_a-zA-Z0-9]*`, and not a reserved word. -/
def isBareAttrName (s : String) : Bool :=
  (match s.toList with
    | [] => false
    | c :: cs => bareHead c && cs.all bareTail) && !cedarReservedIds.contains s

/-- A character as Rust's `char::escape_debug` writes it: the usual backslash escapes, and
`\u{…}` for a control character (Rust also escapes the other non-printable characters of
Unicode, which this port writes as they are). -/
def debugEscapeChar (c : Char) : String :=
  if c == '\x00' then "\\0"
  else if c == '\t' then "\\t"
  else if c == '\r' then "\\r"
  else if c == '\n' then "\\n"
  else if c == '\\' then "\\\\"
  else if c == '"' then "\\\""
  else if c == '\'' then "\\'"
  else if c.toNat < 0x20 || (0x7f ≤ c.toNat && c.toNat < 0xa0) then
    "\\u{" ++ String.ofList (Nat.toDigits 16 c.toNat) ++ "}"
  else String.singleton c

/-- A record attribute name as Cedar's schema printer writes it: bare when it is an identifier
Cedar does not reserve (`isBareAttrName`), else a string literal, escaped as Rust's
`str::escape_debug` escapes it. -/
def attrNameText (n : String) : String :=
  if isBareAttrName n then n else "\"" ++ String.join (n.toList.map debugEscapeChar) ++ "\""

/-- The type as Cedar schema text (crate `ParamType::to_cedar_type_with`): `names` maps a
declared provider enum to its exported name; any other entity type keeps its name, and an
unknown kind, a set without items and an entity without a type are `String`. A record's field
names are written as Cedar's schema printer writes them (`attrNameText`). -/
def ParamType.toCedarTypeWith (names : List (String × String)) : ParamType → String
  | ⟨kind, fields, items, required, et⟩ =>
    match kind with
    | "string" => "String"
    | "integer" | "long" => "Long"
    | "bool" | "boolean" => "Bool"
    | "decimal" => "decimal"
    | "set" => s!"Set<{ParamType.toCedarTypeWithOpt names items}>"
    | "record" => "{ " ++ ", ".intercalate (ParamType.toCedarTypeWithFields names required fields) ++ " }"
    | "entity" =>
      match et with
      | some n => (names.lookup n).getD n
      | none => "String"
    | _ => "String"

def ParamType.toCedarTypeWithOpt (names : List (String × String)) : Option ParamType → String
  | none => "String"
  | some p => ParamType.toCedarTypeWith names p

def ParamType.toCedarTypeWithFields (names : List (String × String)) (required : List String) :
    List (String × ParamType) → List String
  | [] => []
  | (n, p) :: rest =>
    (attrNameText n ++ (if required.contains n then "" else "?") ++ ": " ++
      ParamType.toCedarTypeWith names p) :: ParamType.toCedarTypeWithFields names required rest

end

/-- The cedar type text of a hoisted provider field (crate `to_ast.rs`, the provider chain's
`cedar_type`): the last method's output type, or the provider's when there is no method, with the
used enums by their exported names; `String` when the provider or the method is undeclared. -/
def cedarTypeOf (decls : Option Declarations) (enumNames : List (String × String))
    (key : String) (methods : List String) : String :=
  let decl := decls.bind (·.get key)
  match methods.getLast? with
  | some last =>
    match decl.bind (·.methods.lookup last) with
    | some m => m.outputType.toCedarTypeWith enumNames
    | none => "String"
  | none =>
    match decl with
    | some d => d.outputType.toCedarTypeWith enumNames
    | none => "String"

/-- The declared provider enums the calls `calls` reference, each call a provider key and its
method names, as a sorted set (crate `cedarify_with_providers`, `referenced_enums`): undeclared
providers reference none. -/
def referencedEnums (decls : Option Declarations) (calls : List (String × List String)) :
    List String :=
  match decls with
  | none => []
  | some d => sortedSet (calls.flatMap fun (key, methods) =>
      match d.get key with
      | some decl => decl.referencedEntityTypes methods
      | none => [])

/-- The namespace provider enums are exported into (crate `provider_enum_home`): of the
namespaces that declare actions, the least by the **text** of its name (the root namespace
first); `none` when no namespace declares actions. -/
def providerEnumHome (f : CedarSchema.Fragment) : Option (Option String) :=
  let homes := (f.filter fun (_, ns) => !ns.actions.isEmpty).map (·.1)
  homes.foldl (init := none) fun best n =>
    match best with
    | none => some n
    | some b =>
      let lt := match n, b with
        | none, some _ => true
        | some x, some y => decide (x < y)
        | _, none => false
      if lt then some n else best

/-- The exported name of each declared provider enum in `referenced` (crate
`provider_enum_names`): `<home>::<exportedEnumBasename declared>`, or the basename alone in the
root namespace. Names the declarations do not declare are left out; empty when no namespace
declares actions. -/
def providerEnumNames (f : CedarSchema.Fragment) (decls : Declarations) (referenced : List String) :
    List (String × String) :=
  match providerEnumHome f with
  | none => []
  | some home =>
    (referenced.filter fun n => (decls.entityTypeDecls.lookup n).isSome).map fun declared =>
      let base := exportedEnumBasename declared
      (declared, match home with
        | some ns => ns ++ "::" ++ base
        | none => base)

end Dogwood.Frontend.ProviderDecls
