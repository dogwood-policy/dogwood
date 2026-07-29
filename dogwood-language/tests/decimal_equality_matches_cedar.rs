//! Decimal equality must agree with Cedar's, because it IS Cedar's type.
//!
//! Dogwood's `decimal` is Cedar's extension type, so two decimals are equal
//! exactly when Cedar says they are. Cedar represents a decimal as an `i64` scaled
//! by `10^4` and DERIVES equality on that integer, so equality is numeric — not a
//! property of how the value was spelled.
//!
//! Rather than transcribe Cedar's rules into expectations (which would only test
//! that this file agrees with itself), each case asks CEDAR directly, by calling
//! the very extension function a policy's `decimal(…)` constructor calls, and
//! compares its answer to Dogwood's. The two verdicts sit side by side, so a
//! divergence names itself.

use cedar_policy_core::ast::{Name, Value as CedarValue};
use cedar_policy_core::extensions::decimal;
use dogwood_language::Value;

/// Cedar's own verdict: is `decimal(a) == decimal(b)`?
///
/// `None` when Cedar REJECTS either spelling as a decimal — its parser requires
/// digits on both sides of the point and at most four fractional digits, so a value
/// it will not construct has no equality to compare.
fn cedar_says_equal(a: &str, b: &str) -> Option<bool> {
    let ext = decimal::extension();
    let name: Name = "decimal"
        .parse()
        .expect("the constructor is named `decimal`");
    let ctor = ext
        .get_func(&name)
        .expect("the decimal extension exposes its constructor");

    let make = |s: &str| -> Option<CedarValue> {
        match ctor.call(&[CedarValue::from(s)]) {
            Ok(cedar_policy_core::ast::PartialValue::Value(v)) => Some(v),
            _ => None,
        }
    };
    Some(make(a)? == make(b)?)
}

/// Dogwood's verdict for the same pair.
fn dogwood_says_equal(a: &str, b: &str) -> bool {
    Value::Decimal(a.to_string()).dom_eq(&Value::Decimal(b.to_string()))
}

/// Spellings Cedar accepts: wherever Cedar has an opinion, Dogwood must match it.
///
/// The pairs deliberately span the ways one value can be written — trailing zeros,
/// leading zeros, both at once — and include unequal pairs so agreement cannot be
/// reached by calling everything equal.
#[test]
fn decimal_equality_agrees_with_cedar() {
    let pairs = [
        // Same value, differing only in trailing zeros.
        ("1.5", "1.50"),
        ("1.5", "1.5000"),
        ("0.1", "0.1000"),
        ("-2.5", "-2.500"),
        // Same value, differing only in LEADING zeros.
        ("2.5", "02.5"),
        ("2.5", "0002.5"),
        ("-2.5", "-02.5"),
        // Same value, differing in BOTH.
        ("2.5", "02.50"),
        ("2.5", "000002.500"),
        ("-2.5", "-02.5000"),
        // Genuinely different values, so agreement cannot come from always
        // answering "equal".
        ("1.5", "1.6"),
        ("1.5", "-1.5"),
        ("0.0001", "0.0002"),
        ("1.5", "15.0"),
        ("0.0", "0.0001"),
        // Signed zero is one value.
        ("0.0", "-0.0"),
        ("0.0000", "-0.0"),
        // The extremes of Cedar's range against themselves and each other.
        ("922337203685477.5807", "922337203685477.5807"),
        ("-922337203685477.5808", "-922337203685477.5808"),
        ("922337203685477.5807", "-922337203685477.5808"),
    ];

    let mut disagreements = Vec::new();
    for (a, b) in pairs {
        let Some(cedar) = cedar_says_equal(a, b) else {
            panic!("Cedar rejected `{a}` or `{b}`; this table is for accepted spellings");
        };
        let dogwood = dogwood_says_equal(a, b);
        if cedar != dogwood {
            disagreements.push(format!(
                "`{a}` vs `{b}`: cedar says {cedar}, dogwood says {dogwood}"
            ));
        }
    }

    assert!(
        disagreements.is_empty(),
        "decimal equality must be Cedar's, and these pairs disagree:\n  {}",
        disagreements.join("\n  ")
    );
}

/// The equality must be an equivalence relation over spellings of one value:
/// reflexive, symmetric, and transitive. A string-based canonicalization can
/// satisfy some of these and not others, so they are checked separately.
#[test]
fn decimal_equality_is_an_equivalence_over_spellings() {
    // Every spelling of two and a half.
    let same = ["2.5", "2.50", "02.5", "02.50", "0002.5000"];

    for a in same {
        assert!(dogwood_says_equal(a, a), "`{a}` must equal itself");
        for b in same {
            assert!(
                dogwood_says_equal(a, b),
                "`{a}` and `{b}` are one value and must compare equal"
            );
            assert_eq!(
                dogwood_says_equal(a, b),
                dogwood_says_equal(b, a),
                "equality must be symmetric for `{a}` and `{b}`"
            );
        }
    }
}

/// A spelling Cedar REJECTS is not a decimal, so there is no Cedar answer to match.
///
/// Such text can still reach the interpreter — a trace or a programmatic caller can
/// supply it — so the behaviour is pinned rather than left to chance: only
/// identical text compares equal. That is the conservative choice, and it keeps the
/// relation reflexive without inventing an equality Cedar does not define.
#[test]
fn spellings_cedar_rejects_compare_only_to_themselves() {
    // No decimal point; more than four fractional digits; not a number at all.
    for bad in ["1", "0", "1.00001", "abc", ""] {
        assert!(
            cedar_says_equal(bad, bad).is_none(),
            "`{bad}` is expected to be a spelling Cedar rejects"
        );
        assert!(
            dogwood_says_equal(bad, bad),
            "`{bad}` must still equal itself"
        );
    }

    // Two rejected spellings that would be numerically equal are NOT treated as
    // equal, since Cedar defines no equality between values it will not construct.
    assert!(
        !dogwood_says_equal("1", "1.0"),
        "`1` is not a decimal Cedar accepts, so it must not be equated with `1.0`"
    );
}
