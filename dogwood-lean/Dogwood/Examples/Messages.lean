import Dogwood.Frontend.Validate

/-!
# Examples: the validator's wording of Cedar's errors

How the Lean frontend words the errors of cedar-lean's validator as Cedar's Rust validator
words them (`Validate.cedarMessage`), and renames a provider enum's exported name to its declared
one in a message (`Validate.declaredEnumNames`, crate `declared_enum_names`), checked by
evaluation.
-/

namespace Dogwood.Examples.Messages

open Dogwood.Frontend.Validate

#guard joinWithAnd ["Long", "String"] = "Long and String"
#guard joinWithAnd ["Bool", "Long", "String"] = "Bool, Long, and String"
-- Cedar orders the types by kind: `Long` before an entity type.
#guard incompatibleText [.entity ⟨"Mode", ["Drupe"]⟩, .int] =
  "the types Long and Drupe::Mode are not compatible"
#guard cedarTypeText (.set (.record (Cedar.Data.Map.make [("a", .required .int), ("b", .optional .string)]))) =
  "Set<{a: Long,b?: String,}>"
-- An exported enum name is renamed where it is a whole name, `::` after it allowed.
#guard declaredEnumNames [("Vendor::Severity", "Drupe::Vendor_Severity")]
    "`Drupe::Vendor_Severity::\"HIGH\"` is not a `Drupe::Vendor_SeverityX`" =
  "`Vendor::Severity::\"HIGH\"` is not a `Drupe::Vendor_SeverityX`"
-- The longest exported name first.
#guard declaredEnumNames [("S", "Drupe::S"), ("V::S", "Drupe::V_S")] "Drupe::V_S, Drupe::S" =
  "V::S, S"

end Dogwood.Examples.Messages
