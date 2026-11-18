import Dogwood.Frontend.Derive
import Dogwood.Frontend.Resolve
import Dogwood.Thm.Frontend.Derive.Events
import Dogwood.Thm.Frontend.Derive.Fields
import Dogwood.Thm.Frontend.Derive.Projection
import Dogwood.Thm.Frontend.Derive.Default
import Dogwood.Thm.Frontend.Derive.Resolve

/-!
# Theorems about the frontend: event-schema derivation and Cedar's schema resolution (WP2)

**The derived event schema is well-formed** (`Derive/Events.lean`, `Derive/Fields.lean`,
`Derive/Projection.lean`):

* every derived event names a declared action (`derive_event_declared`), and every declaration
  yields an event on every action (`derive_event_complete`);
* field trees are maps, so each signature's fields are distinct (`derive_leafFields_nodup`,
  `typed_fields_nodup`);
* an event's pins are its declaration's (`derive_pins`), and every pin names a declared field of
  its signature when no record field is pinned, the parser's guarantee
  (`derive_pin_declared`, `typed_pin_declared`; without it, `derive_pin_on_record`);
* the decision flag is the declaration's (`derive_decision`), a flag of the kind across actions
  when the DSL gives each kind one flag, the parser's guarantee (`derive_decision_uniform`;
  without it, `derive_decision_not_uniform`).

**What is read off the derived schema is what the specification reads off its projection**
(`Derive/Projection.lean`): the universal symmetric pins (`universalPins_toSpec`) and the
decision kinds (`decisionKinds_toSpec`, `derive_decisionKinds`).

**The default event schema** derives to the schema the crate's
`configuration/event-schemas/pinned.dwschema` declares
(`Derive/Default.lean`: `default_event`, `default_complete`, `default_typed_universalPins`,
`default_universalPins`, `default_decisionKinds`).

**Cedar's schema resolution** (`Derive/Resolve.lean`): a reference to a common type resolves to
its definition (`convert_commonRef`, `convert_entityOrCommon`), a larger bound on reference
chains gives the same type (`convert_fuel_mono`), and a schema resolves only if every common type
does (`resolve_commons`); every entity type the resolved schema names is declared
(`resolve_namesDeclared`); and every derived event names an action of the resolved schema
(`derive_actions_resolved`).
-/
