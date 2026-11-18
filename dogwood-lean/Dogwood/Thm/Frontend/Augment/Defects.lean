import Dogwood.Thm.Frontend.Augment.TypeText

/-!
# Two ways re-parsed provider types could depart from the declarations

The provider pass types the hoisted provider fields by re-parsing their Cedar type text, which is
then resolved in the namespace of the shared provider type (`add_provider_context_fields`). Two
consequences of that could depart from the declarations; each is shown here, on its minimal
example, with what the pass does about it:

* **A namespace's own type could capture a builtin name.** A provider output declared `decimal`
  is written `decimal` and parsed as a reference to `decimal`; Cedar resolves it in the namespace
  first, so in a namespace that declares a common type `decimal` (which Cedar allows) the
  provider field would get that type instead of the extension type. The pass pins such a name to
  `__cedar::decimal`, which only the extension type answers to.
* **A field name that is not a Cedar identifier could break the synthesized text.** A record field
  of a provider output may be any JSON key. Written unquoted, a key such as `content-type` (or a
  reserved word such as `in`) would make the synthesized type text unparsable. The pass writes it
  as a string, as Cedar's schema printer writes it.
-/

namespace Dogwood.Frontend.Augment

open CedarSchema ProviderDecls TypeText

namespace DecimalCapture

/-- The provider output `{ score: decimal }`, `score` required. -/
def output : ParamType :=
  { paramType := "record", fields := [("score", { paramType := "decimal" })], required := ["score"] }

/-- A namespace `Drupe` declaring the common type `decimal = { foo: Long }`. -/
def schema : Fragment :=
  [(some "Drupe", { commonTypes := [("decimal", ⟨.record [("foo", ⟨.entityOrCommon "Long", true, []⟩)] false, []⟩)],
                    entityTypes := [], actions := [], annotations := [] })]

end DecimalCapture

open DecimalCapture in
/-- **A namespace's common type `decimal` does not capture a provider's `decimal`.** The parse of
the provider output `{ score: decimal }` refers to `decimal`, which Cedar's resolution in `Drupe`
takes to `Drupe::decimal`, a record; since `Drupe` declares `decimal`, the provider pass pins the
reference to `__cedar::decimal`, the extension type, which is the specification's type of the
field (through the bridge's conversion). -/
example (S : Cedar.Validation.Schema) :
    schemaOf [] output = .record [("score", ⟨.entityOrCommon "decimal", true, []⟩)] false ∧
    (Defs.ofFragment schema).resolveName (some "Drupe") .commonOrEntity "decimal" = .ok "Drupe::decimal" ∧
    pinBuiltinNames (declaredTypeNames schema) (schemaOf [] output) =
      .record [("score", ⟨.entityOrCommon "__cedar::decimal", true, []⟩)] false ∧
    (Defs.ofFragment schema).resolveName (some "Drupe") .commonOrEntity "__cedar::decimal" =
      .ok "__cedar::decimal" ∧
    paramTypeToCedar S { paramType := "decimal" } = .ok (.ext .decimal) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

namespace QuotedField

/-- The provider output `{ "content-type"?: String }`. -/
def output : ParamType :=
  { paramType := "record", fields := [("content-type", { paramType := "string" })] }

/-- Its hoisted field, as cedarify types it. -/
def field : ProviderField :=
  { (default : ProviderField) with fieldName := "policy_0_p_0", cedarType := output.toCedarTypeWith [] }

end QuotedField

open QuotedField in
/-- **A provider record field that is not a Cedar identifier is quoted.** The output
`{ "content-type"?: String }` is written `{ "content-type"?: String }`, which Cedar's schema
syntax admits (an attribute name is an identifier or a string; the conformance probe
`runtime_provider_quoted_field` lowers it end to end). -/
example : output.toCedarTypeWith [] = "{ \"content-type\"?: String }" := by decide

end Dogwood.Frontend.Augment
