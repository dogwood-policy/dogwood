import Dogwood.Frontend.Validate.Schema

/-!
# The reads of the request context the authored rules make

While it lowers an authored rule's Cedar part, the crate records each read of the request context
that lowering does not preserve (`cedarify::to_ast::note_context_read`): `context` read whole,
and `context.<a>` or `context has <a>` where `a` is a name lowering reserves for a leaf's value
(`isHoistedName`: `providers`, or `<key>__temporal_<n>`). Its validator reports them. The
lowered rules cannot tell such a read from lowering's own reference to a leaf when the author
reads a leaf's own name, so the reads are taken from the authored (expanded) rules, as the crate
takes them: the walk follows `to_ast::lower_expr`, which lowers the base of an attribute access
or test on `context` without reading `context` whole, does not look inside a temporal block, and
resolves a provider invocation's arguments without lowering them.
-/

namespace Dogwood.Frontend.Cedarify

open Surface (Expr ExprKind)

mutual

/-- The reads an authored expression makes that lowering does not preserve: whole (`true`), or
of a reserved name (`false`, with the name). -/
def readsExpr : Expr → List (Bool × String)
  | ⟨k, _⟩ => readsKind k

def readsKind : ExprKind → List (Bool × String)
  | .var v => if v == .context then [(true, "")] else []
  -- The base of an attribute access or test (crate `lower_attribute_base`): `context` itself is
  -- not a whole read there, and the attribute is a read of a reserved name when it is one.
  | .getAttr e a =>
    match e with
    | ⟨.var .context, _⟩ => if Validate.isHoistedName a then [(false, a)] else []
    | e => readsExpr e
  | .hasAttr e attrs =>
    match e, attrs with
    | ⟨.var .context, _⟩, a :: _ => if Validate.isHoistedName a then [(false, a)] else []
    | ⟨.var .context, _⟩, [] => []
    | e, _ => readsExpr e
  | .lit _ | .slot _ | .extension _ | .paramRef _ => []
  | .unaryApp _ e => readsExpr e
  | .binaryApp _ l r => readsExpr l ++ readsExpr r
  | .like e _ => readsExpr e
  | .is e _ none => readsExpr e
  | .is e _ (some x) => readsExpr e ++ readsExpr x
  | .ite c t e => readsExpr c ++ readsExpr t ++ readsExpr e
  | .set xs => readsList xs
  | .record m => readsRecord m
  -- A provider invocation's arguments, and an output method's, are resolved, not lowered.
  | .call _ _ | .methodCall _ _ _ => []

def readsList : List Expr → List (Bool × String)
  | [] => []
  | x :: xs => readsExpr x ++ readsList xs

def readsRecord : List (String × Expr) → List (Bool × String)
  | [] => []
  | (_, x) :: xs => readsExpr x ++ readsRecord xs

end

/-- The reads the rules of an expanded set make, in rule and clause order. -/
def authoredReads (ps : Surface.PolicySet) : List (Bool × String) :=
  ps.policies.flatMap fun p => p.conditions.flatMap fun c => readsExpr c.body

/-! ## The reads, located -/

mutual

/-- The reads an authored expression makes that lowering does not preserve, as `readsExpr` finds
them, each with the span of its `context` and the reserved name it reads (none for a whole
read), as `to_ast::note_context_read` records them. -/
def readsAtExpr : Expr → List (Span × Option String)
  | ⟨k, sp⟩ => readsAtKind sp k

def readsAtKind (sp : Span) : ExprKind → List (Span × Option String)
  | .var v => if v == .context then [(sp, none)] else []
  | .getAttr e a =>
    match e with
    | ⟨.var .context, bsp⟩ => if Validate.isHoistedName a then [(bsp, some a)] else []
    | e => readsAtExpr e
  | .hasAttr e attrs =>
    match e, attrs with
    | ⟨.var .context, bsp⟩, a :: _ => if Validate.isHoistedName a then [(bsp, some a)] else []
    | ⟨.var .context, _⟩, [] => []
    | e, _ => readsAtExpr e
  | .lit _ | .slot _ | .extension _ | .paramRef _ => []
  | .unaryApp _ e => readsAtExpr e
  | .binaryApp _ l r => readsAtExpr l ++ readsAtExpr r
  | .like e _ => readsAtExpr e
  | .is e _ none => readsAtExpr e
  | .is e _ (some x) => readsAtExpr e ++ readsAtExpr x
  | .ite c t e => readsAtExpr c ++ readsAtExpr t ++ readsAtExpr e
  | .set xs => readsAtList xs
  | .record m => readsAtRecord m
  | .call _ _ | .methodCall _ _ _ => []

def readsAtList : List Expr → List (Span × Option String)
  | [] => []
  | x :: xs => readsAtExpr x ++ readsAtList xs

def readsAtRecord : List (String × Expr) → List (Span × Option String)
  | [] => []
  | (_, x) :: xs => readsAtExpr x ++ readsAtRecord xs

end

/-- The validator's message for a read (crate `to_ast::note_context_read`). -/
def readMessage : Option String → String
  | none => "the rule reads the request context whole, not through one of its attributes; " ++
      "lowering adds the values of the policy set's temporal and provider leaves to the " ++
      "context, so read the attributes the rule needs (`context.<attr>`) instead"
  | some attr => s!"the rule reads the request context attribute `{attr}`, a name lowering " ++
      "reserves for the value of a temporal or provider leaf; a request cannot supply it, so " ++
      "rename the attribute"

/-- The reads the rules of an expanded set make, in rule and clause order, as the crate records
them (crate `Cedarified::context_reads`): each with its rule, its span and its message. -/
def contextReads (ps : Surface.PolicySet) : List ContextRead :=
  ps.policies.zipIdx.flatMap fun (p, k) => p.conditions.flatMap fun c =>
    (readsAtExpr c.body).map fun (sp, a) =>
      { rule := k, span := sp, message := readMessage a, whole := a.isNone }

end Dogwood.Frontend.Cedarify
