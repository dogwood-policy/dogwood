import Dogwood.Thm.Frontend.Augment.Basic
import Dogwood.Thm.Frontend.Augment.Context
import Dogwood.Thm.Frontend.Augment.Spec
import Dogwood.Thm.Frontend.Augment.Providers
import Dogwood.Thm.Frontend.Augment.Typecheck
import Dogwood.Thm.Frontend.Augment.Selective
import Dogwood.Thm.Frontend.Augment.TypeText
import Dogwood.Thm.Frontend.Augment.Defects

/-!
# Theorems about the frontend: schema augmentation and the providers of a lowered set (WP4)

About `Dogwood.Frontend.Augment`, the Lean form of the crate's `augment_schema` and of the
provider resolution of `api::merge`:

* `Augment/Context.lean`: what augmentation does to an action's inline context record
  (`augmentSchema_context`), pass by pass: the provider enums change no action, inlining leaves
  inline contexts as they are, the temporal pass adds the `Bool` of each temporal field targeting
  the action, the provider pass the reference `providers` to the namespace's shared provider type,
  a record of every provider field.
* `Augment/Spec.lean`: the consequences, and the comparison with the specification's
  `Schema.augment`: declared attributes are kept except those with a hoisted name, hoisted
  attributes are on their targets and on no other action, and on every attribute an action
  declares or a field targeting it hoists, the crate's context agrees with `Schema.augment` when
  no declared attribute has a hoisted name; a counterexample shows the proviso is needed, and
  that augmentation refuses such a schema.
* `Augment/Providers.lean`: provider resolution gives each provider leaf its declaration, and
  the leaf's declared output type is the type of its hoisted field and the type the specification
  gives its call.
* `Augment/Typecheck.lean`: Cedar's typechecker sees only the context attributes an expression
  reads (`typeOf_agree`), so a rule gets the same validation verdict against two schemas that
  differ only in their actions' contexts, when at each action it reads only attributes on which
  they agree or its action scope excludes the action
  (`typecheckPolicyWithEnvironments_agree`).
* `Augment/Selective.lean`: the crate's augmentation compiles, action by action, to the
  selective augmentation of the compiled schema (`augment_compiles_to_selective`), which gives a
  rule the verdict `Schema.augment` gives it when, at each action, the rule reads only attributes
  the action declares or the two augmentations hoist alike, or its action scope excludes the
  action (`validate_selective_agrees`); the specification's own augmentation is selective too
  (`PolicySet.augmentedSchema`, `Dogwood.Thm.SelectiveAugment`).
* `Augment/TypeText.lean`: the provider pass's synthesized type text parses back to the declared
  types (`synthesizedAttrs_eq`), so the shared provider type holds each provider field, required,
  with the structure of its declared output type (`augment_provider_declared_types`).
* `Augment/Defects.lean`: two ways the crate's re-parsed provider types could depart from the
  declarations, each on its minimal example: a namespace's common type `decimal` does not capture
  a provider's `decimal`, and a record field name that is not a Cedar identifier is quoted.
-/
