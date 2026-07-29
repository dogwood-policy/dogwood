//! [`Validator`] — schema-aware validation of a [`LoweredPolicySet`], the Dogwood
//! analog of `cedar_policy::Validator`.
//!
//! Usage: `Validator::new().validate(&policy_set)`, returning a
//! [`ValidationResult`] with the same query methods as Cedar's
//! (`validation_passed`, `validation_errors`, `validation_warnings`). Under
//! the hood it runs Cedar's own validator on the lowered policies plus each
//! Dogwood dialect's checks (temporal, provider) and the event-schema names
//! check, rebasing every finding to the originating `.dw` source span.
//!
//! ## Why no schema argument (unlike `cedar_policy::Validator::new(schema)`)
//!
//! Cedar's `Validator` owns a `Schema` because a Cedar schema is
//! *policy-independent*: you build one validator and reuse it to validate many
//! different policy sets (build-once-validate-many). `Validator::new` there
//! merely stores the already-compiled schema; it does no preprocessing.
//!
//! Dogwood cannot offer that reuse. Lowering *augments* the schema with the
//! `context.<id>` fields hoisted from a policy set's own temporal / provider
//! clauses (see [`ParsedPolicySet::lower`](crate::policy_set::ParsedPolicySet::lower)), so the
//! schema validation actually runs against is a *function of the policies* —
//! different policy sets yield different augmented schemas. That augmented
//! schema already travels inside the [`LoweredPolicySet`], which is why validation
//! reads it from there. A schema argument on `Validator::new` would be either
//! redundant (the same schema already on the policy set) or wrong (the
//! un-augmented base). So `Validator` carries no state; it exists to mirror
//! Cedar's `Validator::new().validate(..)` call shape.

use crate::policy_set::LoweredPolicySet;

pub use crate::error::{ValidationError, ValidationResult, ValidationWarning};

/// Validates Dogwood [`LoweredPolicySet`]s. Dogwood's analog of
/// `cedar_policy::Validator`.
///
/// Unlike Cedar's, it holds no schema: the schema a `PolicySet` was lowered
/// against (augmented with its hoisted `context.<id>` fields) already travels
/// on the `PolicySet`, and that is what validation runs against. See the
/// module docs for why.
#[derive(Debug, Default, Clone, Copy)]
pub struct Validator;

impl Validator {
    /// Construct a validator. Takes no schema — see the module docs for why
    /// (Dogwood's effective validation schema is per-policy-set and already
    /// carried on the [`LoweredPolicySet`]).
    pub fn new() -> Self {
        Validator
    }

    /// Validate `policies`, returning every finding — Cedar schema-aware
    /// errors/warnings over the lowered policies plus Dogwood's own dialect
    /// (temporal, provider) checks, each rebased to its `.dw` source span.
    ///
    /// Validation uses Cedar's default (strict) mode. Cedar's `validate` takes
    /// a `ValidationMode`; Dogwood omits it because the non-strict modes are
    /// not meaningful for the lowered dialects (a hoisted `context.<id>` field
    /// must typecheck), so there is no mode to choose.
    pub fn validate(&self, policies: &LoweredPolicySet) -> ValidationResult {
        crate::validate::validate_impl(policies.lowered())
    }
}
