import Dogwood.Frontend.Types

/-!
# The actions a rule's action scope reaches

The crate's `scope_target_actions` (`cedarify/schema_augment.rs`): the concrete actions a hoisted
field attaches to, resolved against the action schema as Cedar parsed it (the fragment, before
compilation).

* `action == A` gives `A` alone, without its members;
* `action in A` and `action in [A, …]` give each listed action and every action that is,
  transitively, a member of it (`memberOf`); a member's parent written `Action::"G"` (or with no
  type) lives in the member's own namespace, a parent written `Ns::Action::"G"` in `Ns`;
* a bare `action` gives every action the schema declares.

An action the schema declares but that cannot receive a request (a pure group: no principal or no
resource type) is then dropped; an action it does not declare is kept, so that augmentation
reports it. The result is sorted and free of duplicates.

The crate computes the descendants with a worklist; here they are the closure of the listed
actions under "is a member of", computed by expanding the set once per declared action (plus one),
which reaches the fixpoint (`Dogwood.Thm.Frontend.Cedarify.mem_closure`).
-/

namespace Dogwood.Frontend.Cedarify

open CedarSchema

/-- An action as `(namespace, id)`: the namespace as text, `""` at the root. -/
abbrev ActionKey := String × String

/-- The text of a fragment's namespace key, `""` for the root namespace. -/
def nsText : Option String → String
  | none => ""
  | some n => n

/-- The fragment key of a namespace written as text (crate `ns_key`). -/
def nsKey (ns : String) : Option String := if ns.isEmpty then none else some ns

/-- Every action the fragment declares, with its declaration, in the fragment's order. -/
def actionDefs (f : Fragment) : List (ActionKey × ActionDef) :=
  f.flatMap fun (k, ns) => ns.actions.map fun (id, a) => ((nsText k, id), a)

/-- The declaration of an action: its namespace's, then its own (crate `action_is_declared`). -/
def findAction? (f : Fragment) (a : ActionKey) : Option ActionDef :=
  (f.lookup (nsKey a.1)).bind fun ns => ns.actions.lookup a.2

/-- The schema declares the action. -/
def isDeclared (f : Fragment) (a : ActionKey) : Bool := (findAction? f a).isSome

/-- The action can receive a request: it applies to at least one principal type and one resource
type (crate `action_is_appliable`). -/
def isAppliable (f : Fragment) (a : ActionKey) : Bool :=
  match findAction? f a with
  | some d => match d.appliesTo with
    | some s => !s.principalTypes.isEmpty && !s.resourceTypes.isEmpty
    | none => false
  | none => false

/-- The namespace of the parent a `memberOf` entry names, for a member declared in namespace
`ns`: the namespace of the entry's entity type when that is qualified, `ns` otherwise. -/
def parentNamespace (ns : String) (m : ActionUid) : String :=
  match m.ty with
  | some ty =>
    let q := "::".intercalate (ty.splitOn "::").dropLast
    if q.isEmpty then ns else q
  | none => ns

/-- The action `child`, declared as `d`, is a member of `parent`. -/
def isMemberOf (child : ActionKey) (d : ActionDef) (parent : ActionKey) : Bool :=
  (d.memberOf.getD []).any fun m => parentNamespace child.1 m == parent.1 && m.id == parent.2

/-- One expansion: the actions of `S`, and each declared action outside `S` that is a member of
one in `S`. -/
def expandOnce (f : Fragment) (S : List ActionKey) : List ActionKey :=
  S ++ ((actionDefs f).filter fun (c, d) => !S.contains c && S.any (isMemberOf c d ·)).map (·.1)

/-- `n` expansions. -/
def expandN (f : Fragment) : Nat → List ActionKey → List ActionKey
  | 0, S => S
  | n + 1, S => expandN f n (expandOnce f S)

/-- The actions `starts`, and every action that is, transitively, a member of one of them. -/
def closure (f : Fragment) (starts : List ActionKey) : List ActionKey :=
  expandN f ((actionDefs f).length + 1) starts

/-- The order the crate sorts actions in: by namespace, then id. -/
def actionLe (a b : ActionKey) : Bool :=
  decide (a.1 < b.1) || (a.1 == b.1 && decide (a.2 ≤ b.2))

/-- The actions an action scope reaches (crate `scope_target_actions`), sorted and free of
duplicates. -/
def scopeTargetActions (a : ScopedAction) (f : Fragment) : List ActionKey :=
  let out := match a with
    | .concrete ns id => [(ns, id)]
    | .list l => closure f l
    | .unconstrained => (actionDefs f).map (fun (x : ActionKey × ActionDef) => x.1)
  ((out.filter fun x => !isDeclared f x || isAppliable f x).mergeSort actionLe).eraseDups

end Dogwood.Frontend.Cedarify
