import Dogwood.Frontend.Types
import Dogwood.Frontend.Macros.Check

/-!
# Macro-library merge, macro expansion, and the temporal static checks (WP1)

The crate's `api::merge_macro_library`, `macros/mod.rs` (`check_defs`, `expand`),
`extension/temporal/check.rs` (`Dogwood.Frontend.Macros.Check`), and
`api::reject_temporal_arrays`.

* `mergeLibrary` checks the library's definitions alone (reserved and duplicate names, each
  body's well-formedness), then appends each one whose name the policy set does not define, so
  that a policy's own `def` takes precedence over a library macro of the same name.
* `expand` checks the definitions again, then replaces every macro call: a Cedar macro by its
  body with each `?p` replaced by the argument, a temporal macro by its condition or value body
  with each `?p` replaced by the argument, each `?w` window by the interval, and each `$t`
  binder by the fresh name `<t>$<start>`, `start` being the call's offset in its block. A
  field refinement `P{…}{…}` folds into the predicate. Every expanded block must then hold no
  macro syntax (`noResidue`) and pass the static checks (`checkLeaf`). The definitions are
  dropped.
* `rejectArrays` rejects an array constant anywhere in an expanded temporal block.

Errors carry the crate's raw messages and spans, which are positions in the source: the walk
of a temporal block computes spans relative to the block's body, and `expandBlock` rebases them;
an error in a macro body found while substituting a call points at the call; a definition's
body has positions in its source (the parser shifts them); a stray sigil in a comparison operand
points at the comparison, and one in a value body at the definition.

`rejectArrays` looks into arithmetic operands too, as the crate's `reject_temporal_arrays` does:
an array in the `where` body of an aggregate that is an operand of `+`, `-` or `*` is rejected.
-/

namespace Dogwood.Frontend.Macros

open Surface (PolicySet MacroDef MacroBody Expr ExprKind Policy Cond)
open Surface.Temporal

/-! ## Errors -/

/-- A macro error (crate `RawMacroError`): the message and the span. -/
structure RawError where
  message : String
  span : Span
deriving Repr, BEq, Inhabited

/-- The result of a macro pass. -/
abbrev MacroResult (α : Type) := Except RawError α

def err {α : Type} (message : String) (span : Span) : MacroResult α :=
  throw { message, span }

/-- A macro error as a stage's error, of category `macro`. -/
def RawError.toError (stage : Stage) (e : RawError) : Error :=
  { stage, category := .macro, message := e.message, span := some e.span }

def MacroResult.atStage {α : Type} (stage : Stage) : MacroResult α → Result α
  | .ok a => .ok a
  | .error e => .error (e.toError stage)

/-- A span inside a temporal block's body, as a position in the source: `base` is the body's
start (crate `Span::rebased`). -/
def rebaseSpan (base : Nat) (sp : Span) : Span := ⟨base + sp.start, base + sp.end⟩

/-- A result whose error's span is rebased by `base`. -/
def rebaseErr {α : Type} (base : Nat) : MacroResult α → MacroResult α
  | .ok a => .ok a
  | .error e => .error { e with span := rebaseSpan base e.span }

/-! ## The registry -/

/-- Names no macro may take (crate `RESERVED_MACRO_NAMES`). -/
def reservedMacroNames : List String :=
  ["decimal", "datetime", "duration", "ip", "let", "in", "where", "for", "sum", "count", "tp",
   "formerly", "previous", "since", "true", "false"]

/-- The definition of a name. Once `checkNames` has accepted the definitions, names are unique,
so this is the crate's registry lookup. -/
def lookup (defs : List MacroDef) (name : String) : Option MacroDef :=
  defs.find? (·.name == name)

/-- Reject a reserved name, or a name defined twice (crate `Registry::build`). -/
def checkNames (defs : List MacroDef) : MacroResult Unit :=
  go [] defs
where
  go (seen : List MacroDef) : List MacroDef → MacroResult Unit
    | [] => pure ()
    | d :: ds =>
      if reservedMacroNames.contains d.name then
        err s!"macro name `{d.name}` is reserved (built-in or keyword); pick a different name"
          d.span
      else match lookup seen d.name with
        | some prev =>
          err s!"duplicate macro definition `{d.name}` (previously defined at byte \
            {prev.span.start})" d.span
        | none => go (seen ++ [d]) ds

/-! ## A definition's well-formedness (crate `check_def`) -/

/-- The declared parameters, as the crate lists them: sorted, each once (crate
`fmt_params`). -/
def fmtParams (declared : List String) : String :=
  let sorted := declared.mergeSort fun a b => decide (a ≤ b)
  ", ".intercalate ((sorted.eraseDups).map fun p => s!"?{p}")

def undeclaredMsg (kind name : String) (declared : List String) : String :=
  s!"in `def {kind}` body: `?{name}` does not name a declared parameter (declared: \
    {fmtParams declared})"

mutual

/-- A Cedar body: every `?p` declared, no call, no temporal block. -/
def checkCedarBody (declared : List String) : Expr → MacroResult Unit
  | ⟨.lit _, _⟩ => pure ()
  | ⟨.var _, _⟩ => pure ()
  | ⟨.slot _, _⟩ => pure ()
  | ⟨.extension t, _⟩ =>
    err "in `def cedar` body: a `temporal { … }` block is not allowed inside a cedar macro \
      (cedar macro bodies must be pure cedar expressions; lift the block to the call site \
      instead)" t.span
  | ⟨.paramRef name, sp⟩ =>
    if declared.contains name then pure () else err (undeclaredMsg "cedar" name declared) sp
  | ⟨.call name _, sp⟩ =>
    err s!"in `def cedar` body: macro-in-macro is not supported (call to `{name}` inside a \
      macro body)" sp
  | ⟨.methodCall r _ args, _⟩ => do checkCedarBody declared r; checkCedarBodies declared args
  | ⟨.unaryApp _ e, _⟩ => checkCedarBody declared e
  | ⟨.binaryApp _ l r, _⟩ => do checkCedarBody declared l; checkCedarBody declared r
  | ⟨.getAttr e _, _⟩ => checkCedarBody declared e
  | ⟨.hasAttr e _, _⟩ => checkCedarBody declared e
  | ⟨.like e _, _⟩ => checkCedarBody declared e
  | ⟨.is e _ none, _⟩ => checkCedarBody declared e
  | ⟨.is e _ (some x), _⟩ => do checkCedarBody declared e; checkCedarBody declared x
  | ⟨.ite c t e, _⟩ => do
    checkCedarBody declared c; checkCedarBody declared t; checkCedarBody declared e
  | ⟨.set xs, _⟩ => checkCedarBodies declared xs
  | ⟨.record m, _⟩ => checkCedarEntries declared m

def checkCedarBodies (declared : List String) : List Expr → MacroResult Unit
  | [] => pure ()
  | e :: rest => do checkCedarBody declared e; checkCedarBodies declared rest

def checkCedarEntries (declared : List String) : List (String × Expr) → MacroResult Unit
  | [] => pure ()
  | (_, e) :: rest => do checkCedarBody declared e; checkCedarEntries declared rest

end

/-- The error for a plain identifier in a `def temporal` body, as a binder or a term (crate
`plain_ident_in_body`). Expansion renames only `$t` binders, so a plain binder would capture a
same-named variable of a spliced argument, and a plain free variable would bind to the call
site's. -/
def plainIdentMsg (name : String) : String :=
  s!"in `def temporal` body: plain identifier `{name}` is not allowed, because expansion does \
    not rename it and it can capture or bind a call-site variable; write `${name}` for a \
    variable the macro binds itself, or declare a `?{name}` parameter for a variable the caller \
    names"

/-- A binder slot of a temporal body (crate `check_binder_slot`): a `?p` must be declared, and a
plain name is refused. -/
def checkSlotBody (declared : List String) (sp : Span) : BinderSlot → MacroResult Unit
  | .name n => err (plainIdentMsg n) sp
  | .paramRef name =>
    if declared.contains name then pure () else err (undeclaredMsg "temporal" name declared) sp
  | .binderRef _ => pure ()

def checkWithinBody (declared : List String) (sp : Span) : WithinSpec → MacroResult Unit
  | .paramRef name =>
    if declared.contains name then pure () else err (undeclaredMsg "temporal" name declared) sp
  | .concrete _ => pure ()

def macroInMacroMsg : String := "in `def temporal` body: macro-in-macro is not supported"

mutual

/-- A temporal condition body: every `?p` declared, no plain identifier as a binder or a term,
no call (crate `check_temporal_condition_body`). -/
def checkCondBody (declared : List String) : Condition → MacroResult Unit
  | ⟨_, .and l r⟩ => do checkCondBody declared l; checkCondBody declared r
  | ⟨_, .or l r⟩ => do checkCondBody declared l; checkCondBody declared r
  | ⟨_, .not c⟩ => checkCondBody declared c
  | ⟨sp, .formerly w b⟩ => do checkWithinBody declared sp w; checkCondBody declared b
  | ⟨sp, .previous w b⟩ => do checkWithinBody declared sp w; checkCondBody declared b
  | ⟨sp, .since l w r⟩ => do
    checkWithinBody declared sp w; checkCondBody declared l; checkCondBody declared r
  | ⟨sp, .predicate ⟨_, _, _, _, args⟩⟩ => checkArgsBody declared sp args
  | ⟨sp, .comparison _ l r⟩ => do checkTermBody declared sp l; checkTermBody declared sp r
  | ⟨sp, .tp v⟩ => checkSlotBody declared sp v
  | ⟨sp, .exists v b⟩ => do checkSlotBody declared sp v.slot; checkCondBody declared b
  | ⟨sp, .sigilRef s name⟩ => match s with
    | .param =>
      if declared.contains name then pure () else err (undeclaredMsg "temporal" name declared) sp
    | .binder => pure ()
  | ⟨sp, .refine b fs _⟩ => do checkCondBody declared b; checkArgsBody declared sp fs
  | ⟨sp, .call _⟩ => err macroInMacroMsg sp

def checkArgsBody (declared : List String) (sp : Span) : List NamedArg → MacroResult Unit
  | [] => pure ()
  | ⟨_, t⟩ :: rest => do checkTermBody declared sp t; checkArgsBody declared sp rest

/-- An aggregation body (crate `check_temporal_agg_body`). -/
def checkAggBody (declared : List String) (asp : Span) : AggExprKind → MacroResult Unit
  | .sum bv vs b => do
    checkSlotBody declared asp bv
    vs.forM fun v => checkSlotBody declared asp v.slot
    checkCondBody declared b
  | .count vs b => do
    vs.forM fun v => checkSlotBody declared asp v.slot
    checkCondBody declared b
  | .call _ => err macroInMacroMsg asp

/-- A term of a temporal body (crate `check_temporal_term`). -/
def checkTermBody (declared : List String) (sp : Span) : Term → MacroResult Unit
  | .paramRef name =>
    if declared.contains name then pure () else err (undeclaredMsg "temporal" name declared) sp
  | .array items => checkTermsBody declared sp items
  | .agg ⟨asp, k⟩ => checkAggBody declared asp k
  | .arith _ l r => do checkTermBody declared sp l; checkTermBody declared sp r
  | .var n => err (plainIdentMsg n) sp
  | _ => pure ()

def checkTermsBody (declared : List String) (sp : Span) : List Term → MacroResult Unit
  | [] => pure ()
  | t :: rest => do checkTermBody declared sp t; checkTermsBody declared sp rest

end

/-- A value body: an aggregation or arithmetic over aggregations (crate
`check_temporal_value_body`). A term has no span of its own: an error there points at the
definition, `dsp`. -/
def checkValueBody (declared : List String) (dsp : Span) : Term → MacroResult Unit
  | .arith _ l r => do checkValueBody declared dsp l; checkValueBody declared dsp r
  | .agg ⟨asp, k⟩ => checkAggBody declared asp k
  | t => checkTermBody declared dsp t

/-- One definition's body (crate `check_def`). -/
def checkDef (d : MacroDef) : MacroResult Unit :=
  let declared := d.params.map (·.name)
  match d.body with
  | .cedar e => checkCedarBody declared e
  | .condition c => checkCondBody declared c
  | .value t => checkValueBody declared d.span t

/-- The definitions alone: their names, then each body (crate `check_defs`). -/
def checkDefs (defs : List MacroDef) : MacroResult Unit := do
  checkNames defs
  defs.forM checkDef

/-! ## The library merge (crate `api::merge_macro_library`) -/

/-- The definitions of the policy set, then those of the library whose names the policy set does
not define. -/
def mergeDefs (own library : List MacroDef) : List MacroDef :=
  own ++ library.filter fun d => !(own.map (·.name)).contains d.name

/-- Merge the macro library's definitions into the policy set's own (crate
`api::merge_macro_library`): `check_defs` on the library alone, then each library definition
whose name the policy set does not define, appended after the policy set's. -/
def mergeLibrary (ps : PolicySet) (library : List MacroDef) : Result PolicySet :=
  MacroResult.atStage .mergeLibrary do
    checkDefs library
    return { ps with defs := mergeDefs ps.defs library }

/-! ## Arity and the residue check -/

def checkArity (d : MacroDef) (got : Nat) (sp : Span) : MacroResult Unit :=
  if d.params.length != got then
    err s!"macro `{d.name}` expects {d.params.length} argument(s), got {got}" sp
  else pure ()

def residue {α : Type} (what : String) (sp : Span) : MacroResult α :=
  err s!"macro residue survived expansion: {what}" sp

def noResidueSlot (sp : Span) : BinderSlot → MacroResult Unit
  | .name _ => pure ()
  | .paramRef n => residue s!"unsubstituted reference `?{n}` in a binder position" sp
  | .binderRef n => residue s!"unsubstituted reference `${n}` in a binder position" sp

def noResidueWithin (sp : Span) : WithinSpec → MacroResult Unit
  | .concrete _ => pure ()
  | .paramRef n => residue s!"unsubstituted reference `?{n}` in a `within` position" sp

mutual

/-- No macro syntax is left in an expanded block (crate `check_no_residue`). -/
def noResidue : Condition → MacroResult Unit
  | ⟨_, .and l r⟩ => do noResidue l; noResidue r
  | ⟨_, .or l r⟩ => do noResidue l; noResidue r
  | ⟨_, .not c⟩ => noResidue c
  | ⟨sp, .formerly w b⟩ => do noResidueWithin sp w; noResidue b
  | ⟨sp, .previous w b⟩ => do noResidueWithin sp w; noResidue b
  | ⟨sp, .since l w r⟩ => do noResidueWithin sp w; noResidue l; noResidue r
  | ⟨sp, .predicate ⟨_, _, _, _, args⟩⟩ => noResidueArgs sp args
  | ⟨sp, .comparison _ l r⟩ => do noResidueTerm sp l; noResidueTerm sp r
  | ⟨sp, .tp v⟩ => noResidueSlot sp v
  | ⟨sp, .exists v b⟩ => do noResidueSlot sp v.slot; noResidue b
  | ⟨sp, .call c⟩ => residue s!"unexpanded macro call `{c.name}`" sp
  | ⟨sp, .sigilRef s n⟩ => match s with
    | .param => residue s!"unsubstituted reference `?{n}`" sp
    | .binder => residue s!"unsubstituted reference `${n}`" sp
  | ⟨sp, .refine _ _ _⟩ => residue "an unfolded field-injection refinement" sp

def noResidueArgs (sp : Span) : List NamedArg → MacroResult Unit
  | [] => pure ()
  | ⟨_, t⟩ :: rest => do noResidueTerm sp t; noResidueArgs sp rest

def noResidueTerm (sp : Span) : Term → MacroResult Unit
  | .paramRef n => residue s!"unsubstituted reference `?{n}`" sp
  | .binderRef n => residue s!"unsubstituted reference `${n}`" sp
  | .array items => noResidueTerms sp items
  | .agg ⟨asp, k⟩ => noResidueAgg asp k
  | .arith _ l r => do noResidueTerm sp l; noResidueTerm sp r
  | _ => pure ()

def noResidueTerms (sp : Span) : List Term → MacroResult Unit
  | [] => pure ()
  | t :: rest => do noResidueTerm sp t; noResidueTerms sp rest

def noResidueAgg (asp : Span) : AggExprKind → MacroResult Unit
  | .sum bv vs b => do
    noResidueSlot asp bv
    vs.forM fun v => noResidueSlot asp v.slot
    noResidue b
  | .count vs b => do
    vs.forM fun v => noResidueSlot asp v.slot
    noResidue b
  | .call c => residue s!"unexpanded macro call `{c.name}`" asp

end

/-! ## Field refinements -/

/-- A condition's shape, for the message of a refinement of a non-predicate (crate
`condition_shape`). -/
def conditionShape : ConditionKind → String
  | .and _ _ => "a conjunction (`&&`)"
  | .or _ _ => "a disjunction (internal)"
  | .not _ => "a negation (`!`)"
  | .formerly _ _ => "a `formerly` operator"
  | .previous _ _ => "a `previous` operator"
  | .since _ _ _ => "a `since` operator"
  | .comparison _ _ _ => "a comparison"
  | .exists _ _ => "an `exists` binder"
  | .tp _ => "a `tp(…)`"
  | .predicate _ => "a predicate"
  | .call _ => "an unexpanded macro call"
  | .sigilRef _ _ => "an unresolved macro parameter"
  | .refine _ _ _ => "a refinement"

/-- Fold a refinement into its resolved base, which must be a predicate: its arguments gain the
fields (crate `fold_refine`). -/
def foldRefine (base : Condition) (fields : List NamedArg) (sp : Span) : MacroResult Condition :=
  match base with
  | ⟨bsp, .predicate ⟨psp, ns, a, k, args⟩⟩ => pure ⟨bsp, .predicate ⟨psp, ns, a, k, args ++ fields⟩⟩
  | ⟨_, k⟩ => err s!"a `\{ … }` field-injection applies only to a single predicate, but the \
      refined term is {conditionShape k}" sp

/-! ## Temporal substitution -/

/-- The last value a key maps to (the crate collects the parameters into a map, so a repeated
parameter name maps to its last argument). -/
def lookupLast {β : Type} (m : List (String × β)) (k : String) : Option β :=
  m.foldl (fun acc (k', v) => if k' == k then some v else acc) none

/-- A macro call's substitution: each parameter's argument, the call's span (the fresh names
of its `$t` binders), and the macro's name (crate `SubstMaps`). -/
structure Subst where
  params : List (String × CallArg)
  callSpan : Span
  macroName : String

def Subst.ofCall (d : MacroDef) (c : Call) : Subst :=
  { params := (d.params.map (·.name)).zip c.args, callSpan := c.span, macroName := d.name }

/-- The argument of `?name` (crate `arg_for`). An error found while substituting points at the
call. -/
def Subst.argFor (m : Subst) (name : String) : MacroResult CallArg :=
  match lookupLast m.params name with
  | some a => pure a
  | none => err s!"unbound macro parameter `?{name}` in body of `{m.macroName}`" m.callSpan

/-- The fresh name of `$name` at this call (crate `gensym_for`). -/
def Subst.gensym (m : Subst) (name : String) : String := s!"{name}${m.callSpan.start}"

def substSlot (m : Subst) : BinderSlot → MacroResult BinderSlot
  | .name n => pure (.name n)
  | .paramRef name => do
    match ← m.argFor name with
    | .term (.var x) => pure (.name x)
    | _ => err s!"macro `{m.macroName}` parameter `?{name}` is used in a binder position, so \
        the call-site argument must be a single identifier" m.callSpan
  | .binderRef name => pure (.name (m.gensym name))

def substWithin (m : Subst) : WithinSpec → MacroResult WithinSpec
  | .concrete i => pure (.concrete i)
  | .paramRef name => do
    match ← m.argFor name with
    | .within i => pure (.concrete i)
    | _ => err s!"macro `{m.macroName}` parameter `?{name}` is used in a `within` position; \
        the call-site argument must be an interval literal `<n><unit>` (e.g. `1h`)" m.callSpan

def substBinders (m : Subst) (vs : List TypedBinder) : MacroResult (List TypedBinder) :=
  vs.mapM fun v => return { v with slot := ← substSlot m v.slot }

mutual

/-- Substitute a condition body (crate `subst_temporal_condition`). -/
def substCond (m : Subst) : Condition → MacroResult Condition
  | ⟨_, .sigilRef s name⟩ => match s with
    | .param => do
      match ← m.argFor name with
      | .condition c => pure c
      | _ => m.callSpan |> err s!"macro `{m.macroName}` parameter `?{name}` is used in a \
          condition position, so the call-site argument must be a temporal condition (got a \
          different shape)"
    | .binder => m.callSpan |> err s!"macro binder `${name}` used as a whole condition has no \
        meaning"
  | ⟨sp, .and l r⟩ => return ⟨sp, .and (← substCond m l) (← substCond m r)⟩
  | ⟨sp, .or l r⟩ => return ⟨sp, .or (← substCond m l) (← substCond m r)⟩
  | ⟨sp, .not c⟩ => return ⟨sp, .not (← substCond m c)⟩
  | ⟨sp, .formerly w b⟩ => do
    let w ← substWithin m w
    return ⟨sp, .formerly w (← substCond m b)⟩
  | ⟨sp, .previous w b⟩ => do
    let w ← substWithin m w
    return ⟨sp, .previous w (← substCond m b)⟩
  | ⟨sp, .since l w r⟩ => do
    let w ← substWithin m w
    let l ← substCond m l
    return ⟨sp, .since l w (← substCond m r)⟩
  | ⟨sp, .predicate ⟨psp, ns, a, k, args⟩⟩ =>
    return ⟨sp, .predicate ⟨psp, ns, a, k, ← substArgs m args⟩⟩
  | ⟨sp, .comparison op l r⟩ => do
    let l ← substTerm m l
    return ⟨sp, .comparison op l (← substTerm m r)⟩
  | ⟨sp, .tp v⟩ => return ⟨sp, .tp (← substSlot m v)⟩
  | ⟨sp, .exists ⟨s, ty⟩ b⟩ => do
    let s ← substSlot m s
    return ⟨sp, .exists ⟨s, ty⟩ (← substCond m b)⟩
  | ⟨_, .refine b fs _⟩ => do
    let b ← substCond m b
    let fs ← substArgs m fs
    foldRefine b fs m.callSpan
  -- A body holds no call (`checkDef`); left for the residue check.
  | ⟨sp, .call c⟩ => pure ⟨sp, .call c⟩

def substArgs (m : Subst) : List NamedArg → MacroResult (List NamedArg)
  | [] => pure []
  | ⟨n, t⟩ :: rest => do
    let t ← substTerm m t
    return ⟨n, t⟩ :: (← substArgs m rest)

/-- Substitute a term of a body (crate `subst_temporal_term`). -/
def substTerm (m : Subst) : Term → MacroResult Term
  | .paramRef name => do
    match ← m.argFor name with
    | .term t => pure t
    | _ => err s!"macro `{m.macroName}` parameter `?{name}` used in a term position; the \
        call-site argument has the wrong shape" m.callSpan
  | .binderRef name => pure (.var (m.gensym name))
  | .array items => return .array (← substTerms m items)
  | .agg ⟨asp, k⟩ => return .agg ⟨asp, ← substAgg m k⟩
  | .arith op l r => do
    let l ← substTerm m l
    return .arith op l (← substTerm m r)
  | t => pure t

def substTerms (m : Subst) : List Term → MacroResult (List Term)
  | [] => pure []
  | t :: rest => do
    let t ← substTerm m t
    return t :: (← substTerms m rest)

def substAgg (m : Subst) : AggExprKind → MacroResult AggExprKind
  | .sum bv vs b => do
    let bv ← substSlot m bv
    let vs ← substBinders m vs
    return .sum bv vs (← substCond m b)
  | .count vs b => do
    let vs ← substBinders m vs
    return .count vs (← substCond m b)
  -- A body holds no call (`checkDef`); left for the residue check.
  | .call c => pure (.call c)

end

/-! ## Temporal expansion -/

def checkConcreteWithin (sp : Span) : WithinSpec → MacroResult Unit
  | .concrete _ => pure ()
  | .paramRef p => err s!"stray macro parameter reference `?{p}` in a `within` position outside \
      a macro body" sp

def checkConcreteSlot (sp : Span) : BinderSlot → MacroResult Unit
  | .name _ => pure ()
  | .paramRef p => err s!"stray macro parameter reference `?{p}` in a binder position outside a \
      macro body" sp
  | .binderRef b => err s!"stray macro binder reference `${b}` in a binder position outside a \
      macro body" sp

mutual

/-- A predicate argument holds no stray sigil, also inside an array (crate
`check_concrete_term`). -/
def checkConcreteTerm (sp : Span) : Term → MacroResult Unit
  | .paramRef p => err s!"stray macro parameter reference `?{p}` in a predicate-argument \
      position outside a macro body" sp
  | .binderRef b => err s!"stray macro binder reference `${b}` in a predicate-argument position \
      outside a macro body" sp
  | .array items => checkConcreteTerms sp items
  | _ => pure ()

def checkConcreteTerms (sp : Span) : List Term → MacroResult Unit
  | [] => pure ()
  | t :: rest => do checkConcreteTerm sp t; checkConcreteTerms sp rest

end

/-- Whether a name is a value macro's. -/
def isValueMacro (defs : List MacroDef) (name : String) : Bool :=
  match lookup defs name with
  | some ⟨_, _, _, .value _⟩ => true
  | _ => false

mutual

/-- Expand the macro calls of a temporal condition (crate `expand_temporal_condition`). -/
def expandCond (defs : List MacroDef) : Condition → MacroResult Condition
  | ⟨sp, .and l r⟩ => do
    let l ← expandCond defs l
    return ⟨sp, .and l (← expandCond defs r)⟩
  | ⟨sp, .or l r⟩ => do
    let l ← expandCond defs l
    return ⟨sp, .or l (← expandCond defs r)⟩
  | ⟨sp, .not c⟩ => return ⟨sp, .not (← expandCond defs c)⟩
  | ⟨sp, .formerly w b⟩ => do
    checkConcreteWithin sp w
    return ⟨sp, .formerly w (← expandCond defs b)⟩
  | ⟨sp, .previous w b⟩ => do
    checkConcreteWithin sp w
    return ⟨sp, .previous w (← expandCond defs b)⟩
  | ⟨sp, .since l w r⟩ => do
    checkConcreteWithin sp w
    let l ← expandCond defs l
    return ⟨sp, .since l w (← expandCond defs r)⟩
  | ⟨sp, .predicate p⟩ => do
    p.args.forM fun a => checkConcreteTerm sp a.value
    return ⟨sp, .predicate p⟩
  | ⟨sp, .tp v⟩ => do
    checkConcreteSlot sp v
    return ⟨sp, .tp v⟩
  | ⟨sp, .comparison op l r⟩ => do
    let l ← expandOperand defs sp l
    return ⟨sp, .comparison op l (← expandOperand defs sp r)⟩
  | ⟨sp, .exists v b⟩ => do
    checkConcreteSlot sp v.slot
    return ⟨sp, .exists v (← expandCond defs b)⟩
  | ⟨_, .call c⟩ => callToCondition defs c
  | ⟨sp, .sigilRef s name⟩ => match s with
    | .param => err s!"stray macro parameter reference `?{name}` outside a macro body" sp
    | .binder => err s!"stray macro binder reference `${name}` outside a macro body" sp
  | ⟨_, .refine b fs rsp⟩ => do
    let b ← expandCond defs b
    foldRefine b fs rsp

/-- Expand a comparison operand (crate `expand_temporal_operand`): a value-macro call is
replaced by the value body, which may be arithmetic. A term has no span of its own: an error
points at the comparison, or the call whose argument it is, `sp`. -/
def expandOperand (defs : List MacroDef) (sp : Span) : Term → MacroResult Term
  | .agg ⟨_, .call c⟩ => callToValue defs c
  | .agg ⟨asp, .sum bv vs b⟩ => do
    checkConcreteSlot asp bv
    vs.forM fun v => checkConcreteSlot asp v.slot
    return .agg ⟨asp, .sum bv vs (← expandCond defs b)⟩
  | .agg ⟨asp, .count vs b⟩ => do
    vs.forM fun v => checkConcreteSlot asp v.slot
    return .agg ⟨asp, .count vs (← expandCond defs b)⟩
  | .arith op l r => do
    let l ← expandOperand defs sp l
    return .arith op l (← expandOperand defs sp r)
  | .paramRef p => err s!"stray macro parameter reference `?{p}` in a comparison-operand \
      position outside a macro body" sp
  | .binderRef b => err s!"stray macro binder reference `${b}` in a comparison-operand position \
      outside a macro body" sp
  | t => pure t

/-- Replace a condition-position call by its macro's body (crate
`expand_temporal_call_to_condition`). -/
def callToCondition (defs : List MacroDef) : Call → MacroResult Condition
  | ⟨csp, name, args⟩ => do
    let some d := lookup defs name
      | err s!"unknown macro `{name}` (no declared `def temporal`)" csp
    match d.body with
    | .condition body => do
      checkArity d args.length csp
      let args ← expandCallArgs defs csp args
      substCond (Subst.ofCall d ⟨csp, name, args⟩) body
    | .cedar _ => err s!"macro `{name}` is a cedar macro and cannot be called in a temporal \
        condition position" csp
    | .value _ => err s!"macro `{name}` is a value macro (an aggregation or arithmetic over \
        aggregations); it must appear as a comparison operand (e.g. `{name}(…) <= n`), not as \
        a standalone condition" csp

/-- Replace an operand-position call by its macro's value body (crate
`expand_temporal_call_to_value`). -/
def callToValue (defs : List MacroDef) : Call → MacroResult Term
  | ⟨csp, name, args⟩ => do
    let some d := lookup defs name
      | err s!"unknown macro `{name}` (no declared `def temporal`)" csp
    match d.body with
    | .value body => do
      checkArity d args.length csp
      let args ← expandCallArgs defs csp args
      let m := Subst.ofCall d ⟨csp, name, args⟩
      substTerm m body
    | .cedar _ =>
      err s!"macro `{name}` is a cedar macro and cannot be called in a value position" csp
    | .condition _ => err s!"macro `{name}` is a condition macro and cannot be used as a value \
        (a comparison operand); use it in a condition position instead" csp

/-- Expand a call's arguments (crate `expand_temporal_call_args`): a bare call to a value macro
in condition position is re-tagged as a term. `csp` is the call's span. -/
def expandCallArgs (defs : List MacroDef) (csp : Span) : List CallArg → MacroResult (List CallArg)
  | [] => pure []
  | .term t :: rest => do
    let t ← expandOperand defs csp t
    return .term t :: (← expandCallArgs defs csp rest)
  | .within i :: rest => return .within i :: (← expandCallArgs defs csp rest)
  | .condition ⟨sp, .call inner⟩ :: rest => do
    let a ← if isValueMacro defs inner.name then CallArg.term <$> callToValue defs inner
      else CallArg.condition <$> expandCond defs ⟨sp, .call inner⟩
    return a :: (← expandCallArgs defs csp rest)
  | .condition c :: rest => do
    let c ← expandCond defs c
    return .condition c :: (← expandCallArgs defs csp rest)

end

/-- Expand a temporal block, then check it: no macro residue, then the static checks (crate
`expand_extension`). The walk's spans are relative to the block's body, and are rebased. -/
def expandBlock (defs : List MacroDef) (b : Block) : MacroResult Block := do
  let c ← rebaseErr b.span.start (expandCond defs b.condition)
  rebaseErr b.span.start (noResidue c)
  match checkLeaf c with
  | .ok () => pure ⟨c, b.span⟩
  | .error e => err s!"temporal binding check failed after expansion: {e}" b.span

/-! ## Cedar expansion -/

/-- Whether a call's name is namespace-qualified, a provider invocation's. -/
def isQualified (name : String) : Bool :=
  go name.toList
where
  go : List Char → Bool
    | ':' :: ':' :: _ => true
    | _ :: rest => go rest
    | [] => false

mutual

/-- Substitute a Cedar body (crate `subst_cedar_expr`): each `?p` becomes its argument. -/
def substCedar (m : List (String × Expr)) : Expr → MacroResult Expr
  | ⟨.paramRef name, sp⟩ => match lookupLast m name with
    | some a => pure a
    | none => err s!"unbound macro parameter `?{name}` in macro body" sp
  | ⟨.call n args, sp⟩ => return ⟨.call n (← substCedars m args), sp⟩
  | ⟨.methodCall r n args, sp⟩ => do
    let r ← substCedar m r
    return ⟨.methodCall r n (← substCedars m args), sp⟩
  | ⟨.unaryApp op e, sp⟩ => return ⟨.unaryApp op (← substCedar m e), sp⟩
  | ⟨.binaryApp op l r, sp⟩ => do
    let l ← substCedar m l
    return ⟨.binaryApp op l (← substCedar m r), sp⟩
  | ⟨.getAttr e a, sp⟩ => return ⟨.getAttr (← substCedar m e) a, sp⟩
  | ⟨.hasAttr e a, sp⟩ => return ⟨.hasAttr (← substCedar m e) a, sp⟩
  | ⟨.like e p, sp⟩ => return ⟨.like (← substCedar m e) p, sp⟩
  | ⟨.is e t none, sp⟩ => return ⟨.is (← substCedar m e) t none, sp⟩
  | ⟨.is e t (some x), sp⟩ => do
    let e ← substCedar m e
    return ⟨.is e t (some (← substCedar m x)), sp⟩
  | ⟨.ite c t e, sp⟩ => do
    let c ← substCedar m c
    let t ← substCedar m t
    return ⟨.ite c t (← substCedar m e), sp⟩
  | ⟨.set xs, sp⟩ => return ⟨.set (← substCedars m xs), sp⟩
  | ⟨.record es, sp⟩ => return ⟨.record (← substCedarEntries m es), sp⟩
  | e => pure e

def substCedars (m : List (String × Expr)) : List Expr → MacroResult (List Expr)
  | [] => pure []
  | e :: rest => do
    let e ← substCedar m e
    return e :: (← substCedars m rest)

def substCedarEntries (m : List (String × Expr)) :
    List (String × Expr) → MacroResult (List (String × Expr))
  | [] => pure []
  | (k, e) :: rest => do
    let e ← substCedar m e
    return (k, e) :: (← substCedarEntries m rest)

end

mutual

/-- Expand the macro calls of a Cedar expression (crate `expand_cedar_expr`): the arguments
first; a namespace-qualified call is a provider's and stays. -/
def expandExpr (defs : List MacroDef) : Expr → MacroResult Expr
  | ⟨.call name args, sp⟩ => do
    let args ← expandExprs defs args
    if isQualified name then pure ⟨.call name args, sp⟩
    else match lookup defs name with
      | none => err s!"unknown function or macro `{name}` (not a Cedar built-in and not a \
          declared macro)" sp
      | some d => match d.body with
        | .cedar body => do
          checkArity d args.length sp
          substCedar ((d.params.map (·.name)).zip args) body
        | _ => err s!"macro `{name}` is a temporal macro and cannot be called in a cedar \
            expression position" sp
  | ⟨.methodCall r n args, sp⟩ => do
    let r ← expandExpr defs r
    return ⟨.methodCall r n (← expandExprs defs args), sp⟩
  | ⟨.paramRef name, sp⟩ =>
    err s!"stray macro parameter reference `?{name}` outside a macro body" sp
  | ⟨.extension t, sp⟩ => return ⟨.extension (← expandBlock defs t), sp⟩
  | ⟨.unaryApp op e, sp⟩ => return ⟨.unaryApp op (← expandExpr defs e), sp⟩
  | ⟨.binaryApp op l r, sp⟩ => do
    let l ← expandExpr defs l
    return ⟨.binaryApp op l (← expandExpr defs r), sp⟩
  | ⟨.getAttr e a, sp⟩ => return ⟨.getAttr (← expandExpr defs e) a, sp⟩
  | ⟨.hasAttr e a, sp⟩ => return ⟨.hasAttr (← expandExpr defs e) a, sp⟩
  | ⟨.like e p, sp⟩ => return ⟨.like (← expandExpr defs e) p, sp⟩
  | ⟨.is e t none, sp⟩ => return ⟨.is (← expandExpr defs e) t none, sp⟩
  | ⟨.is e t (some x), sp⟩ => do
    let e ← expandExpr defs e
    return ⟨.is e t (some (← expandExpr defs x)), sp⟩
  | ⟨.ite c t e, sp⟩ => do
    let c ← expandExpr defs c
    let t ← expandExpr defs t
    return ⟨.ite c t (← expandExpr defs e), sp⟩
  | ⟨.set xs, sp⟩ => return ⟨.set (← expandExprs defs xs), sp⟩
  | ⟨.record es, sp⟩ => return ⟨.record (← expandEntries defs es), sp⟩
  | e => pure e

def expandExprs (defs : List MacroDef) : List Expr → MacroResult (List Expr)
  | [] => pure []
  | e :: rest => do
    let e ← expandExpr defs e
    return e :: (← expandExprs defs rest)

def expandEntries (defs : List MacroDef) :
    List (String × Expr) → MacroResult (List (String × Expr))
  | [] => pure []
  | (k, e) :: rest => do
    let e ← expandExpr defs e
    return (k, e) :: (← expandEntries defs rest)

end

/-- Expand one rule's conditions. -/
def expandPolicy (defs : List MacroDef) (p : Policy) : MacroResult Policy := do
  let conditions ← p.conditions.mapM fun c => return { c with body := ← expandExpr defs c.body }
  return { p with conditions }

/-- Expand every macro call and clear `defs` (crate `macros::expand`), checking each expanded
temporal block again. -/
def expand (ps : PolicySet) : Result PolicySet :=
  MacroResult.atStage .expand do
    checkDefs ps.defs
    let policies ← ps.policies.mapM (expandPolicy ps.defs)
    return { policies, defs := [] }

/-! ## Array constants (crate `api::reject_temporal_arrays`) -/

mutual

/-- The temporal blocks of an expression, with the span of each block's expression, in the
crate's pre-order (`Expr::for_each_node`). -/
def exprBlocks : Expr → List (Span × Block)
  | ⟨.extension t, sp⟩ => [(sp, t)]
  | ⟨.unaryApp _ e, _⟩ => exprBlocks e
  | ⟨.binaryApp _ l r, _⟩ => exprBlocks l ++ exprBlocks r
  | ⟨.getAttr e _, _⟩ => exprBlocks e
  | ⟨.hasAttr e _, _⟩ => exprBlocks e
  | ⟨.like e _, _⟩ => exprBlocks e
  | ⟨.is e _ none, _⟩ => exprBlocks e
  | ⟨.is e _ (some x), _⟩ => exprBlocks e ++ exprBlocks x
  | ⟨.ite c t e, _⟩ => exprBlocks c ++ exprBlocks t ++ exprBlocks e
  | ⟨.set xs, _⟩ => exprsBlocks xs
  | ⟨.record es, _⟩ => entriesBlocks es
  | ⟨.call _ args, _⟩ => exprsBlocks args
  | ⟨.methodCall r _ args, _⟩ => exprBlocks r ++ exprsBlocks args
  | _ => []

def exprsBlocks : List Expr → List (Span × Block)
  | [] => []
  | e :: rest => exprBlocks e ++ exprsBlocks rest

def entriesBlocks : List (String × Expr) → List (Span × Block)
  | [] => []
  | (_, e) :: rest => exprBlocks e ++ entriesBlocks rest

end

/-- The temporal blocks of a rule, in the crate's order (`Policy::temporal_conditions`). -/
def policyBlocks (p : Policy) : List (Span × Block) :=
  p.conditions.flatMap fun c => exprBlocks c.body

mutual

/-- A condition holds an array constant: in a predicate argument or a comparison operand, also
inside an aggregate's body or an arithmetic operand (crate `condition_has_array`). -/
def condHasArray : Condition → Bool
  | ⟨_, .and l r⟩ => condHasArray l || condHasArray r
  | ⟨_, .or l r⟩ => condHasArray l || condHasArray r
  | ⟨_, .since l _ r⟩ => condHasArray l || condHasArray r
  | ⟨_, .not c⟩ => condHasArray c
  | ⟨_, .formerly _ c⟩ => condHasArray c
  | ⟨_, .previous _ c⟩ => condHasArray c
  | ⟨_, .exists _ c⟩ => condHasArray c
  | ⟨_, .predicate ⟨_, _, _, _, args⟩⟩ => argsHaveArray args
  | ⟨_, .comparison _ l r⟩ => termHasArray l || termHasArray r
  | ⟨_, .refine b fs _⟩ => condHasArray b || argsHaveArray fs
  | ⟨_, .tp _⟩ => false
  | ⟨_, .call _⟩ => false
  | ⟨_, .sigilRef _ _⟩ => false

def argsHaveArray : List NamedArg → Bool
  | [] => false
  | ⟨_, t⟩ :: rest => termHasArray t || argsHaveArray rest

def termHasArray : Term → Bool
  | .array _ => true
  | .agg ⟨_, .sum _ _ b⟩ => condHasArray b
  | .agg ⟨_, .count _ b⟩ => condHasArray b
  | .arith _ l r => termHasArray l || termHasArray r
  | _ => false

end

def arrayMsg : String :=
  "temporal predicate arguments cannot contain array constants (e.g. `field: [\"a\", \"b\"]`); \
  use scalar values or `context` field references instead"

/-- Reject the first block holding an array constant, anywhere in an expanded temporal block (a
predicate argument or a comparison operand, also inside an aggregate's body and an arithmetic
operand), with the span of the block's expression (crate `api::reject_temporal_arrays`). -/
def rejectArrays (ps : PolicySet) : Result Unit :=
  match (ps.policies.flatMap policyBlocks).find? (fun (_, b) => condHasArray b.condition) with
  | none => pure ()
  | some (sp, _) =>
    throw { stage := .rejectArrays, category := .cedarify, message := arrayMsg, span := some sp }

end Dogwood.Frontend.Macros
