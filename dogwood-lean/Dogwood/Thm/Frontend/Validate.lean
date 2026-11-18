import Dogwood.Thm.Frontend.Validate.Sound
import Dogwood.Thm.Frontend.Validate.Complete
import Dogwood.Thm.Frontend.Validate.Counterexamples
import Dogwood.Thm.Frontend.Validate.Located

/-!
# Theorems about the frontend's validator

The frontend's validator (`Dogwood.Frontend.Validate.validate`) is a port of the crate's
`Validator::validate`. It is sound and, up to the crate's stricter rules, complete with respect to
the specification's validity (`Dogwood.Spec.PolicySet.Valid`) of the conformance projection of the
lowered set (`Lowered.toConformance`):

* `validate_sound` (`Validate/Sound.lean`): when the validator reports no error on a lowered set
  that meets the guarantees of the earlier stages (`Assumptions`), and Cedar's schema construction
  accepted its augmented schema, the projection is valid;
* `validate_complete` (`Validate/Complete.lean`): when the projection of such a lowered set, which
  also meets `ConverseAssumptions`, is valid, the validator reports no error, unless the lowered
  set breaks one of the crate's stricter rules (`StrictRules`);
* `accepts_iff_valid`: under both, the validator accepts exactly the valid projections.

`Validate/Counterexamples.lean` and the end of `Validate/ProviderComplete.lean` show that the
crate's stricter rules are needed: each gives a leaf the specification accepts and the crate
rejects, meeting every other premise of `leaf_complete` or `provider_complete`.

The two trusted links are that cedar-lean's validator, which the port runs for Cedar's, agrees
with the crate's Cedar validator, and that Cedar's schema construction accepted the augmented
schema only if cedar-lean's well-formedness check does (`l.schema.validateWellFormed = .ok ()`).
Every assumption is a decidable property of the lowered set (`Validate.assumptions`,
`Validate.converseAssumptions`).
-/
