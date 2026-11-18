import Dogwood.Frontend.Augment.Util

/-!
# The provider declarations' consistency check

The crate's `ProviderDeclarations::check` (`extension/provider/declarations.rs`): independent of
any action schema, every `paramType` is known (or, unknown, falls back to `String` without
mentioning an entity), an `entity` type names a valid, fully qualified `entityType`, every output
entity type is declared in `entityTypes`, and every `entityTypes` entry is a well-formed enum in
one of the file's provider namespaces, with an exported name of its own. Every problem is
reported, one per line, in the crate's order.
-/

namespace Dogwood.Frontend.Augment

open ProviderDecls

/-- The `paramType`s a declaration may use. -/
def knownParamTypes : List String :=
  ["string", "integer", "long", "bool", "boolean", "decimal", "set", "record", "entity"]

/-- An enum's declared name is a valid, fully qualified Cedar name outside `__cedar`; its
namespace (the crate's `check_entity_type_name`). -/
def checkEntityTypeName (name : String) : Except String String :=
  if (name.splitOn "::").any (· == "__cedar") then
    .error s!"`{name}` uses the reserved `__cedar` namespace"
  else if !isName name then
    .error s!"`{name}` is not a valid Cedar entity type name"
  else match rsplitOnce name with
    | some (ns, _) => .ok ns
    | none => .error s!"`{name}` must be fully qualified (`Ns::Type`)"

mutual

/-- The type, or one nested in it, uses `paramType: "entity"` or carries an `entityType` (crate
`ParamType::mentions_entity`). -/
def paramMentionsEntity : ParamType → Bool
  | ⟨kind, fields, items, _, et⟩ =>
    kind == "entity" || et.isSome || paramMentionsEntityOpt items ||
      paramMentionsEntityFields fields

def paramMentionsEntityOpt : Option ParamType → Bool
  | none => false
  | some p => paramMentionsEntity p

def paramMentionsEntityFields : List (String × ParamType) → Bool
  | [] => false
  | (_, p) :: rest => paramMentionsEntity p || paramMentionsEntityFields rest

end

mutual

/-- The structural problems of a type and of every type nested in it, at the JSON path `at`
(crate `ParamType::check`). `declared` is `some` in output positions, where an entity type must
be declared in `entityTypes`. -/
def checkParam (at_ : String) (declared : Option (String → Bool)) : ParamType → List String
  | p@⟨kind, fields, items, required, et⟩ =>
    if !knownParamTypes.contains kind then
      if paramMentionsEntity p then [s!"{at_}: unknown paramType `{kind}`"] else []
    else if kind == "entity" then
      let extra := [(!fields.isEmpty, "fields"), (items.isSome, "items"), (!required.isEmpty, "required")]
        |>.filterMap fun (present, key) =>
          if present then some s!"{at_}: `entity` paramType does not take `{key}`" else none
      let typed := match et with
        | none => [s!"{at_}: `entity` paramType requires `entityType`"]
        | some name => match checkEntityTypeName name with
          | .error e => [s!"{at_}: entityType {e}"]
          | .ok _ => match declared with
            | some isDeclared =>
              if isDeclared name then [] else [s!"{at_}: `{name}` is not declared in `entityTypes`"]
            | none => []
      extra ++ typed
    else
      (if et.isSome then [s!"{at_}: `entityType` is only valid with `paramType: \"entity\"`"] else []) ++
        checkParamOpt (at_ ++ ".items") declared items ++
        checkParamFields at_ declared fields

def checkParamOpt (at_ : String) (declared : Option (String → Bool)) :
    Option ParamType → List String
  | none => []
  | some p => checkParam at_ declared p

def checkParamFields (at_ : String) (declared : Option (String → Bool)) :
    List (String × ParamType) → List String
  | [] => []
  | (name, p) :: rest =>
    checkParam (at_ ++ "." ++ name) declared p ++ checkParamFields at_ declared rest

end

/-- The problems of each type in `tys`, at `<at> argumentTypes[i]`. -/
def checkArgs (at_ : String) (tys : List ParamType) : List String :=
  tys.zipIdx.flatMap fun (t, i) => checkParam s!"{at_} argumentTypes[{i}]" none t

/-- The problems of the `entityTypes` entry `name` (the first loop of `check`). -/
def checkEnumDecl (providerNamespaces : List String) (name : String) (decl : EntityTypeDecl) :
    List String :=
  let named := match checkEntityTypeName name with
    | .error e => [s!"entityTypes: {e}"]
    | .ok ns =>
      if providerNamespaces.contains ns then []
      else [s!"entityTypes: entity type `{name}` is not in a provider namespace declared by this file"]
  let empty := if decl.values.isEmpty then [s!"entityTypes: enum `{name}` has no values"] else []
  let dups := (decl.values.zipIdx.filter fun (v, i) => (decl.values.take i).contains v).map
    fun (v, _) => s!"entityTypes: enum `{name}` lists `{v}` more than once"
  named ++ empty ++ dups

/-- Every exported basename that two or more declared enums share, with those enums in key
order (the crate's `by_export`), in basename order. -/
def exportClashes (names : List String) : List (String × List String) :=
  let byExport := names.foldl (init := ([] : List (String × List String))) fun m n =>
    let e := exportedEnumBasename n
    insertKey e (((m.lookup e).getD []) ++ [n]) m
  byExport.filter fun (_, ns) => ns.length > 1

/-- The problems of one provider's declaration (the last loop of `check`). -/
def checkProvider (declared : String → Bool) (key : String) (d : ProviderDecl) : List String :=
  let at_ := s!"provider `{key}`"
  checkArgs at_ d.argumentTypes ++ checkParam (at_ ++ " outputType") (some declared) d.outputType ++
    d.methods.flatMap fun (m, md) =>
      let at' := at_ ++ s!" method `{m}`"
      checkArgs at' md.argumentTypes ++
        (match md.inputType with
          | some t => checkParam (at' ++ " inputType") none t
          | none => []) ++
        checkParam (at' ++ " outputType") (some declared) md.outputType

/-- Every problem of the declarations, in the crate's order (crate
`ProviderDeclarations::check`). -/
def declarationProblems (d : Declarations) : List String :=
  let providerNamespaces := d.available.filterMap fun (k, _) => (rsplitOnce k).map (·.1)
  let enums := d.entityTypeDecls.flatMap fun (name, decl) => checkEnumDecl providerNamespaces name decl
  let clashes := (exportClashes (d.entityTypeDecls.map (·.1))).map fun (e, ns) =>
    s!"entityTypes: `{"`, `".intercalate ns}` are all exported as `{e}`; rename all but one"
  let declared := fun (n : String) => (d.entityTypeDecls.lookup n).isSome
  enums ++ clashes ++ d.available.flatMap fun (key, decl) => checkProvider declared key decl

/-- The declarations' consistency check (crate `ProviderDeclarations::check`): every problem,
one per line. An error has category `providers`. -/
def checkDeclarations (d : Declarations) : Result Unit :=
  match declarationProblems d with
  | [] => .ok ()
  | ps => .error { stage := .providerCheck, category := .providers, message := "\n".intercalate ps }

end Dogwood.Frontend.Augment
