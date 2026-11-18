import Dogwood.Frontend.Types
import Dogwood.Frontend.Cedarify
import Dogwood.Frontend.Escape

/-!
# Cedar's printing of a lowered rule

The crate emits each lowered rule as a `cedar_policy_core::ast::StaticPolicy` (`emit_policy`,
`cedarify/mod.rs`), and three of Cedar's printings of it are observable:

* its **policy JSON** (`cedar_policy::Policy::to_json`, the EST): the AST converted to the EST
  (`est::Builder`, `From<ast::Policy> for est::Policy`) and serialized (`policyEst`);
* its **text** (`Display` of `cedar_policy::Policy`): a policy built from an AST prints its EST,
  on one line (`est::Policy`'s `Display`, `policyText`);
* its **canonical text**, the input to its revision: the rule lowered again under the rule key
  `dw`, without annotations, printed by `Display` of the AST's `StaticPolicy`, on several lines
  (`ruleCanonical`).

The three share the EST's printer of expressions (`est/expr.rs`: `display_cedarvaluejson`, the
`BoundedDisplay` of `ExprNoExt` and `ExtFuncCall`, `maybe_with_parens`), since the AST's `Display`
of an expression converts it to the EST first. The rules are the crate's Cedar policies with the
crate's names (`Cedarify.WithSpec.cedar`), whose expressions are Cedar's AST: Cedar's
desugarings (`!=`, `>`, `>=`, `is … in`, `has a.b`) are already applied, so the EST has none of
the EST-only operators.

**Escaping.** Strings, entity ids, attribute names and annotation values are printed with
Rust's `str::escape_debug`, and pattern characters with `char::escape_debug`: `Escape`, which
reads the Unicode tables of the Rust release the crate builds with, so that every character,
ASCII or not, is escaped exactly as the crate escapes it.
-/

namespace Dogwood.Frontend.CedarPrint

open Lean (Json)
open Cedar.Spec (Expr Prim Var UnaryOp BinaryOp ExtFun Scope ActionScope EntityUID Name)

/-! ## Escaping -/

/-- One character as Rust's `char::escape_debug_ext` writes it, with every escape but that of a
grapheme extender, which is written escaped when `escapeExtend` (`Escape.escapeDebugExt`). -/
def escapeChar (escapeExtend : Bool) (c : Char) : String :=
  Escape.escapeDebugExt escapeExtend true true c

/-- A string as Rust's `str::escape_debug` writes it (`Escape.strEscapeDebug`). -/
def escapeDebug (s : String) : String := Escape.strEscapeDebug s

/-! ## Names -/

/-- Cedar's text of a name, `A::B::C` (`InternalName`'s `Display`). -/
def nameStr (n : Name) : String := String.join (n.path.map (· ++ "::")) ++ n.id

/-- Cedar's text of an entity: `A::B::"id"`, the id escaped (`EntityUID`'s `Display`). -/
def euidText (u : EntityUID) : String := nameStr u.ty ++ "::\"" ++ escapeDebug u.eid ++ "\""

/-! Cedar's identifiers (`Cedarify.isNormalizedIdent`, which lowering also reads) -/

open Dogwood.Frontend.Cedarify (reservedIds isAnyIdent isNormalizedIdent)

/-! ## Extension functions -/

/-- An extension function's name in Cedar. -/
def extName : ExtFun → String
  | .decimal => "decimal" | .lessThan => "lessThan" | .lessThanOrEqual => "lessThanOrEqual"
  | .greaterThan => "greaterThan" | .greaterThanOrEqual => "greaterThanOrEqual"
  | .ip => "ip" | .isIpv4 => "isIpv4" | .isIpv6 => "isIpv6" | .isLoopback => "isLoopback"
  | .isMulticast => "isMulticast" | .isInRange => "isInRange"
  | .datetime => "datetime" | .duration => "duration" | .offset => "offset"
  | .durationSince => "durationSince" | .toDate => "toDate" | .toTime => "toTime"
  | .toMilliseconds => "toMilliseconds" | .toSeconds => "toSeconds" | .toMinutes => "toMinutes"
  | .toHours => "toHours" | .toDays => "toDays"

/-- Whether Cedar calls the function as a method of its first argument (`CallStyle`): the
constructors `decimal`, `ip`, `datetime` and `duration` are functions, the others methods. -/
def isMethodStyle : ExtFun → Bool
  | .decimal | .ip | .datetime | .duration => false
  | _ => true

/-! ## Values and patterns -/

/-- A variable's name. -/
def varName : Var → String
  | .principal => "principal" | .action => "action" | .resource => "resource"
  | .context => "context"

/-- An entity as the EST writes it in a value or a scope: `{"type", "id"}`. -/
def euidJson (u : EntityUID) : Json :=
  Json.mkObj [("type", Json.str (nameStr u.ty)), ("id", Json.str u.eid)]

/-- A literal as the EST writes it (`CedarValueJson::from_lit`). -/
def primJson : Prim → Json
  | .bool b => Json.bool b
  | .int i => Json.num (Lean.JsonNumber.fromInt i.toInt)
  | .string s => Json.str s
  | .entityUID u => Json.mkObj [("__entity", euidJson u)]

/-- A literal as the EST prints it (`display_cedarvaluejson`): a negative number in parentheses,
a string quoted and escaped, an entity as Cedar's text of it. -/
def primText : Prim → String
  | .bool b => toString b
  | .int i => if i.toInt < 0 then "(" ++ toString i.toInt ++ ")" else toString i.toInt
  | .string s => "\"" ++ escapeDebug s ++ "\""
  | .entityUID u => euidText u

/-- A pattern as the EST writes it: one literal per character, and the wildcards. -/
def patternJson (p : Cedar.Spec.Pattern) : Json :=
  Json.arr (p.map fun
    | .star => Json.str "Wildcard"
    | .justChar c => Json.mkObj [("Literal", Json.str (String.singleton c))]).toArray

/-- A pattern as Cedar prints it inside its quotes (`Pattern`'s `Display`): a literal `*` as
`\*`, the wildcard as `*`, any other character escaped by `char::escape_debug`. -/
def patternText (p : Cedar.Spec.Pattern) : String :=
  String.join (p.map fun
    | .star => "*"
    | .justChar c => if c == '*' then "\\*" else escapeChar true c)

/-! ## Expressions -/

/-- A one-key object `{k: v}`. -/
def tag (k : String) (v : Json) : Json := Json.mkObj [(k, v)]

/-- A binary node of the EST, `{op: {"left", "right"}}`. -/
def binJson (op : String) (l r : Json) : Json := tag op (Json.mkObj [("left", l), ("right", r)])

/-- The EST's key of a binary operator. -/
def binOpKey : BinaryOp → String
  | .eq => "==" | .mem => "in" | .hasTag => "hasTag" | .getTag => "getTag" | .less => "<"
  | .lessEq => "<=" | .add => "+" | .sub => "-" | .mul => "*" | .contains => "contains"
  | .containsAll => "containsAll" | .containsAny => "containsAny"

mutual

/-- An expression as the EST writes it (the AST converted by `est::Builder`, serialized). -/
def exprJson : Expr → Json
  | .lit p => tag "Value" (primJson p)
  | .var v => tag "Var" (Json.str (varName v))
  | .ite c t e => tag "if-then-else"
      (Json.mkObj [("if", exprJson c), ("then", exprJson t), ("else", exprJson e)])
  | .and a b => binJson "&&" (exprJson a) (exprJson b)
  | .or a b => binJson "||" (exprJson a) (exprJson b)
  | .unaryApp .not e => tag "!" (Json.mkObj [("arg", exprJson e)])
  | .unaryApp .neg e => tag "neg" (Json.mkObj [("arg", exprJson e)])
  | .unaryApp .isEmpty e => tag "isEmpty" (Json.mkObj [("arg", exprJson e)])
  | .unaryApp (.like p) e => tag "like" (Json.mkObj [("left", exprJson e), ("pattern", patternJson p)])
  | .unaryApp (.is t) e =>
    tag "is" (Json.mkObj [("left", exprJson e), ("entity_type", Json.str (nameStr t))])
  | .binaryApp op a b => binJson (binOpKey op) (exprJson a) (exprJson b)
  | .getAttr e a => tag "." (Json.mkObj [("left", exprJson e), ("attr", Json.str a)])
  | .hasAttr e a => tag "has" (Json.mkObj [("left", exprJson e), ("attr", Json.str a)])
  -- `est::Builder::extended_has_attr_arc`: a path of one attribute is the simple form.
  | .extHasAttr e a [] => tag "has" (Json.mkObj [("left", exprJson e), ("attr", Json.str a)])
  | .extHasAttr e a as => tag "has" (Json.mkObj [("left", exprJson e),
      ("attr", Json.arr ((a :: as).map Json.str).toArray)])
  | .set xs => tag "Set" (Json.arr (exprsJson xs).toArray)
  | .record m => tag "Record" (Json.mkObj (entriesJson m))
  | .call f args => tag (extName f) (Json.arr (exprsJson args).toArray)

def exprsJson : List Expr → List Json
  | [] => []
  | x :: xs => exprJson x :: exprsJson xs

def entriesJson : List (String × Expr) → List (String × Json)
  | [] => []
  | (k, x) :: xs => (k, exprJson x) :: entriesJson xs

end

/-- Whether the EST's printer puts the expression in parentheses where it is an operand
(`maybe_with_parens`, Cedar 4.14): every expression except a literal, a variable, a set, a record,
and the expressions the grammar's `Member` level prints (an attribute access, `contains`,
`containsAll`, `containsAny`, `isEmpty`, `getTag`, `hasTag`, an extension call). -/
def needsParens : Expr → Bool
  | .lit _ | .var _ | .set _ | .record _ | .getAttr _ _ | .call _ _ => false
  | .unaryApp .isEmpty _ => false
  | .binaryApp .contains _ _ | .binaryApp .containsAll _ _ | .binaryApp .containsAny _ _
  | .binaryApp .getTag _ _ | .binaryApp .hasTag _ _ => false
  | _ => true

/-- Whether `e` is an application of the left-associative operator `op` (`+`, `-` or `*`), whose
left operand Cedar 4.14 prints without parentheses when it is the same operator. -/
def isBinary (op : BinaryOp) : Expr → Bool
  | .binaryApp op' _ _ => op' == op
  | _ => false

/-- Whether `e` is a conjunction. -/
def isAnd : Expr → Bool
  | .and _ _ => true
  | _ => false

/-- Whether `e` is a disjunction. -/
def isOr : Expr → Bool
  | .or _ _ => true
  | _ => false

/-- `s`, the text of `e`, in parentheses when `e` needs them as an operand. -/
def wrap (e : Expr) (s : String) : String := if needsParens e then "(" ++ s ++ ")" else s

/-- The text of a binary operator written between its operands. -/
def infixText : BinaryOp → Option String
  | .eq => some " == " | .mem => some " in " | .less => some " < " | .lessEq => some " <= "
  | .add => some " + " | .sub => some " - " | .mul => some " * "
  | _ => none

/-- The method name of a binary operator written as a method of its left operand. -/
def methodText : BinaryOp → String
  | .contains => "contains" | .containsAll => "containsAll" | .containsAny => "containsAny"
  | .getTag => "getTag" | .hasTag => "hasTag"
  | _ => ""

/-- An attribute after `.`: bare when it is an identifier, `["…"]` otherwise. -/
def attrAccess (a : String) : String :=
  if isNormalizedIdent a then "." ++ a else "[\"" ++ escapeDebug a ++ "\"]"

/-- An attribute after `has`: bare when it is an identifier, quoted otherwise. -/
def attrTest (a : String) : String :=
  if isNormalizedIdent a then " has " ++ a else " has \"" ++ escapeDebug a ++ "\""

/-- An attribute after the first of an extended `has` path: `.a` when it is an identifier,
`."…"` otherwise (`HasAttrRepr::Extended`'s `Display`). -/
def attrStep (a : String) : String :=
  if isNormalizedIdent a then "." ++ a else ".\"" ++ escapeDebug a ++ "\""

/-- A record key: bare when it is an identifier, quoted otherwise. -/
def recordKey (k : String) : String :=
  if isNormalizedIdent k then k else "\"" ++ escapeDebug k ++ "\""

mutual

/-- An expression as the EST prints it (`BoundedDisplay` of `est::Expr`, unbounded). A record
prints its entries in key order, as the AST's map holds them. -/
def exprText : Expr → String
  | .lit p => primText p
  | .var v => varName v
  -- The three operands are `Expr` in the grammar, so they print without parentheses.
  | .ite c t e => "if " ++ exprText c ++ " then " ++ exprText t ++ " else " ++ exprText e
  -- `&&`, `||`, `+`, `-` and `*` are left-associative: a left operand of the same operator prints
  -- without parentheses.
  | .and a b =>
    (if isAnd a then exprText a else wrap a (exprText a)) ++ " && " ++ wrap b (exprText b)
  | .or a b =>
    (if isOr a then exprText a else wrap a (exprText a)) ++ " || " ++ wrap b (exprText b)
  | .unaryApp .not e => "!" ++ wrap e (exprText e)
  | .unaryApp .neg e => "-(" ++ exprText e ++ ")"
  | .unaryApp .isEmpty e => wrap e (exprText e) ++ ".isEmpty()"
  | .unaryApp (.like p) e => wrap e (exprText e) ++ " like \"" ++ patternText p ++ "\""
  | .unaryApp (.is t) e => wrap e (exprText e) ++ " is " ++ nameStr t
  | .binaryApp op a b =>
    match infixText op with
    | some s =>
      let left := match op with
        | .add | .sub | .mul => if isBinary op a then exprText a else wrap a (exprText a)
        | _ => wrap a (exprText a)
      left ++ s ++ wrap b (exprText b)
    | none => wrap a (exprText a) ++ "." ++ methodText op ++ "(" ++ exprText b ++ ")"
  | .getAttr e a => wrap e (exprText e) ++ attrAccess a
  | .hasAttr e a => wrap e (exprText e) ++ attrTest a
  | .extHasAttr e a as => wrap e (exprText e) ++ attrTest a ++ String.join (as.map attrStep)
  | .set xs => "[" ++ ", ".intercalate (exprsText xs) ++ "]"
  | .record m =>
    let entries := (entriesText m).mergeSort fun a b => decide (a.1 ≤ b.1)
    "{" ++ ", ".intercalate (entries.map fun (k, v) => recordKey k ++ ": " ++ v) ++ "}"
  | .call f args =>
    let texts := exprsText args
    match isMethodStyle f, args, texts with
    | true, r :: _, t :: rest => wrap r t ++ "." ++ extName f ++ "(" ++ ", ".intercalate rest ++ ")"
    | _, _, _ => extName f ++ "(" ++ ", ".intercalate texts ++ ")"

def exprsText : List Expr → List String
  | [] => []
  | x :: xs => exprText x :: exprsText xs

def entriesText : List (String × Expr) → List (String × String)
  | [] => []
  | (k, x) :: xs => (k, exprText x) :: entriesText xs

end

/-! ## Policies -/

/-- A policy's condition as the AST holds it, one expression (`TemplateBody`'s
`non_scope_constraints`): the clauses folded left to right with `&&`, an `unless` body negated,
`true` when there is none. The crate's rules have one `when` clause, its body. -/
def conditionExpr : Cedar.Spec.Conditions → Expr
  | [] => .lit (.bool true)
  | c :: cs => cs.foldl (init := clause c) fun acc c => .and acc (clause c)
where
  clause (c : Cedar.Spec.Condition) : Expr :=
    match c.kind with
    | .when => c.body
    | .unless => .unaryApp .not c.body

/-- The annotations the crate puts on a rule (`emit_policy`): those whose key is an identifier
(`AnyId`), in key order, a later one with a key replacing an earlier one, and the value `""` for
an annotation written without one. -/
def annotationMap (anns : List Surface.Annotation) : List (String × String) :=
  let valid := anns.filter fun a => isAnyIdent a.key
  let dedup := valid.foldl (init := ([] : List (String × String))) fun acc a =>
    (acc.filter (·.1 != a.key)) ++ [(a.key, a.value.getD "")]
  dedup.mergeSort fun a b => decide (a.1 ≤ b.1)

/-- An effect's name. -/
def effectText : Cedar.Spec.Effect → String
  | .permit => "permit"
  | .forbid => "forbid"

/-- A principal or resource scope as the EST writes it. -/
def scopeJson : Scope → Json
  | .any => Json.mkObj [("op", "All")]
  | .eq u => Json.mkObj [("op", "=="), ("entity", euidJson u)]
  | .mem u => Json.mkObj [("op", "in"), ("entity", euidJson u)]
  | .is t => Json.mkObj [("op", "is"), ("entity_type", Json.str (nameStr t))]
  | .isMem t u => Json.mkObj [("op", "is"), ("entity_type", Json.str (nameStr t)),
      ("in", Json.mkObj [("entity", euidJson u)])]

/-- The action scope as the AST holds it: any action, one, or a list (`ActionConstraint`). An
`in` of one action and a list of one action are the same list. -/
inductive ActionTarget where
  | any
  | eq (u : EntityUID)
  | list (us : List EntityUID)

/-- The action scope of a lowered rule as Cedar's AST holds it. The `is` forms, which no rule has,
read as any action. -/
def actionTarget : ActionScope → ActionTarget
  | .actionScope .any => .any
  | .actionScope (.eq u) => .eq u
  | .actionScope (.mem u) => .list [u]
  | .actionInAny us => .list us
  | .actionScope (.is _) | .actionScope (.isMem _ _) => .any

/-- The action scope as the EST writes it: a list of one action is a single `in`. -/
def actionJson (a : ActionScope) : Json :=
  match actionTarget a with
  | .any => Json.mkObj [("op", "All")]
  | .eq u => Json.mkObj [("op", "=="), ("entity", euidJson u)]
  | .list [u] => Json.mkObj [("op", "in"), ("entity", euidJson u)]
  | .list us => Json.mkObj [("op", "in"), ("entities", Json.arr (us.map euidJson).toArray)]

/-- A principal or resource scope as Cedar prints it, the same in the EST's and the AST's
printings. -/
def scopeText (v : String) : Scope → String
  | .any => v
  | .eq u => v ++ " == " ++ euidText u
  | .mem u => v ++ " in " ++ euidText u
  | .is t => v ++ " is " ++ nameStr t
  | .isMem t u => v ++ " is " ++ nameStr t ++ " in " ++ euidText u

/-- The action scope as the EST prints it: a single `in`, or a list separated by `, `. -/
def actionTextEst (a : ActionScope) : String :=
  match actionTarget a with
  | .any => "action"
  | .eq u => "action == " ++ euidText u
  | .list [u] => "action in " ++ euidText u
  | .list us => "action in [" ++ ", ".intercalate (us.map euidText) ++ "]"

/-- The action scope as the AST prints it (`ActionConstraint`'s `Display`): a list always in
brackets, separated by `,`. -/
def actionTextAst (a : ActionScope) : String :=
  match actionTarget a with
  | .any => "action"
  | .eq u => "action == " ++ euidText u
  | .list us => "action in [" ++ ",".intercalate (us.map euidText) ++ "]"

/-- The policy JSON of a lowered rule with its annotations, as `cedar_policy::Policy::to_json`
writes the crate's policy: its effect, scopes, one `when` clause with the condition, and the
annotations, absent when there are none. -/
def policyEst (p : Cedar.Spec.Policy) (annotations : List Surface.Annotation) : Json :=
  let anns := annotationMap annotations
  let base : List (String × Json) := [
    ("effect", Json.str (effectText p.effect)),
    ("principal", scopeJson p.principalScope.scope),
    ("action", actionJson p.actionScope),
    ("resource", scopeJson p.resourceScope.scope),
    ("conditions", Json.arr #[Json.mkObj [("kind", "when"),
      ("body", exprJson (conditionExpr p.condition))]])]
  Json.mkObj (if anns.isEmpty then base
    else base ++ [("annotations", Json.mkObj (anns.map fun (k, v) => (k, Json.str v)))])

/-- The annotations as Cedar prints them, one line each: `@key("value")`. -/
def annotationsText (annotations : List Surface.Annotation) : String :=
  String.join ((annotationMap annotations).map fun (k, v) => "@" ++ k ++ "(\"" ++ escapeDebug v ++ "\")\n")

/-- The text of a lowered rule with its annotations, as `Display` of `cedar_policy::Policy`
prints the crate's policy (the EST's printing, on one line). -/
def policyText (p : Cedar.Spec.Policy) (annotations : List Surface.Annotation) : String :=
  annotationsText annotations ++ effectText p.effect ++ "(" ++
    scopeText "principal" p.principalScope.scope ++ ", " ++ actionTextEst p.actionScope ++ ", " ++
    scopeText "resource" p.resourceScope.scope ++ ") when { " ++
    exprText (conditionExpr p.condition) ++ " };"

/-- The text of a lowered rule as `Display` of the AST's `StaticPolicy` prints it, on several
lines, with its annotations first. -/
def staticPolicyText (p : Cedar.Spec.Policy) (annotations : List Surface.Annotation) : String :=
  annotationsText annotations ++ effectText p.effect ++ "(\n  " ++
    scopeText "principal" p.principalScope.scope ++ ",\n  " ++ actionTextAst p.actionScope ++
    ",\n  " ++ scopeText "resource" p.resourceScope.scope ++ "\n) when {\n  " ++
    exprText (conditionExpr p.condition) ++ "\n};"

/-! ## Canonical texts -/

/-- The key under which a rule is lowered again for its canonical text (crate
`CANONICAL_RULE_KEY`). -/
def canonicalRuleKey : String := "dw"

/-- The canonical text of one rule: the rule lowered under the canonical key, with the id `_`
and the set's enum names, printed without annotations by the AST's `Display`. -/
def ruleCanonicalOf (decls : Option ProviderDecls.Declarations) (enumNames : List (String × String))
    (p : Surface.Policy) : Result String := do
  let (r, _) ← Cedarify.lowerPolicy decls enumNames canonicalRuleKey "_" p
    ⟨"", 0, [], [], []⟩
  pure (staticPolicyText r.cedar [])

/-- The canonical text of each rule of an expanded set, in rule order (crate `rule_canonical`,
`cedarify::lower_policies`): each rule lowered again under the rule key `dw`, with no
annotations and the id `_`, with the exported names of the provider enums the set uses, and
printed by `Display` of the AST's `StaticPolicy`. A rule's hoisted names are then
`dw__temporal_<n>` and `dw_p_<n>`, free of its position. -/
def ruleCanonical (ps : Surface.PolicySet) (decls : Option ProviderDecls.Declarations)
    (enumNames : List (String × String)) : Result (List String) :=
  ps.policies.mapM (ruleCanonicalOf decls enumNames)

/-- The policy JSON of each rule of a cedarified set, in rule order: rule `i` with the
annotations of the `i`-th rule of the expanded set. -/
def policiesEst (ps : Surface.PolicySet) (rules : List Cedar.Spec.Policy) : List Json :=
  (rules.zip ps.policies).map fun (r, p) => policyEst r p.annotations

/-- The text of each rule of a cedarified set, in rule order. -/
def policiesText (ps : Surface.PolicySet) (rules : List Cedar.Spec.Policy) : List String :=
  (rules.zip ps.policies).map fun (r, p) => policyText r p.annotations

end Dogwood.Frontend.CedarPrint
