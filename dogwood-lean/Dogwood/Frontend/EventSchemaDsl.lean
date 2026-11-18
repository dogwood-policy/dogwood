import Dogwood.Frontend.Syntax

/-!
# The event-schema DSL, as parsed

What the crate's event-schema parser produces (`event_schema/ast.rs`), before derivation binds it
to an action schema: an optional `max_window` cap and an ordered list of event declarations, each
a template over an action binder `<A>`.

The parser guarantees that `pin` and `= ref` occur together, that no record field is pinned, that
every selector names the declaration's binder, that `max_window` and `max_horizon` are not zero,
that the resolved `max_window` is at most the resolved `max_horizon` (`Derive.limits`), and that
no event kind is declared twice.
-/

namespace Dogwood.Frontend.EventSchemaDsl

open Surface.Temporal (Interval)

/-- A reader over the bound action (crate `Selector`): `inputs(A)`, `outputs(A)`,
`principalType(A)`, `resourceType(A)`. -/
inductive Selector where
  | inputs
  | outputs
  | principalType
  | resourceType
deriving Repr, DecidableEq, BEq, Inhabited

/-- The request root a pin's path is anchored to (crate `PinRoot`). -/
inductive PinRoot where
  /-- `principal` or `resource`, with an optional attribute path. -/
  | scope
  /-- `context.<path>`. -/
  | context
deriving Repr, DecidableEq, BEq, Inhabited

/-- The request-side value a pinned field must match (crate `PinValue`). For a `scope` root the
path keeps `principal` or `resource` as its head; for a `context` root it drops `context`. -/
structure PinValue where
  contextPath : List String
  root : PinRoot
  span : Span
deriving Repr, DecidableEq, BEq, Inhabited

mutual

/-- A field of an event declaration (crate `FieldSpec`). -/
inductive FieldSpec where
  /-- `...selector(A)`. -/
  | spread (selector : Selector) (span : Span)
  /-- `[pin] name: type [= ref]`. -/
  | named (name : String) (ty : TypeExpr) (pin : Option PinValue) (span : Span)

/-- The type of a named field (crate `TypeExpr`). -/
inductive TypeExpr where
  | selector (s : Selector)
  /-- A Cedar type name, as its `::` segments. -/
  | concrete (path : List String)
  /-- A nested record of fields. -/
  | record (fields : List FieldSpec)

end

deriving instance Repr, BEq for FieldSpec, TypeExpr

instance : Inhabited TypeExpr := ⟨.concrete []⟩

/-- `[decision] event <binder>::kind { fields }` (crate `EventDecl`). -/
structure EventDecl where
  span : Span
  decision : Bool
  binder : String
  kind : String
  fields : List FieldSpec
deriving Repr, BEq, Inhabited

/-- A parsed event schema (crate `event_schema::ast::EventSchema`). -/
structure EventSchema where
  maxWindow : Option Interval
  maxHorizon : Option Interval := none
  decls : List EventDecl
deriving Repr, BEq, Inhabited

end Dogwood.Frontend.EventSchemaDsl
