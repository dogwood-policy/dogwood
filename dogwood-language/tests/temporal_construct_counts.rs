//! Measuring a [`ParsedPolicy`]'s temporal complexity before lowering with
//! its temporal construct counts.
//!
//! [`ParsedPolicy`]: dogwood_language::ParsedPolicy

use dogwood_language::{ParsedPolicySet, ServiceSchema};

#[derive(Debug, Default, PartialEq)]
struct Counts {
    formerly: usize,
    previous: usize,
    since: usize,
    count: usize,
    sum: usize,
    exists: usize,
}

/// The counts of a single policy with a `temporal { … }` block per entry of
/// `blocks`.
fn counts(blocks: &[&str]) -> Counts {
    let conditions = blocks
        .iter()
        .map(|block| format!("when temporal {{\n{block}\n}}"))
        .collect::<Vec<_>>()
        .join("\n");
    let src =
        format!(r#"permit (principal, action == Drupe::Action::"Read", resource) {conditions};"#);
    let parsed = ParsedPolicySet::parse(&src, &ServiceSchema::defaults()).expect("parses");
    let policy = parsed.policies().next().expect("one policy");
    let counts = policy.temporal_construct_counts();
    Counts {
        formerly: counts.formerly(),
        previous: counts.previous(),
        since: counts.since(),
        count: counts.count(),
        sum: counts.sum(),
        exists: counts.exists(),
    }
}

const FORMERLY_AND_SINCE: &str = r#"
formerly within 1h Drupe::Action::"Transfer"::request{}
&& (Drupe::Action::"Login"::request{} since within 2h Drupe::Action::"Logout"::request{})"#;

const COUNT_WITHIN: &str = r#"count_within(1h, Drupe::Action::"Transfer"::request{}) > 5"#;

const BIND_SUM_WITHIN: &str = r#"
bind(prior, sum_within(a, 1h, Drupe::Action::"Transfer"::request{ input.amount: a }),
     context.input.amount > prior)"#;

/// A `count` whose `where` body holds another `count`; each wraps one
/// `formerly`.
const COUNT_INSIDE_COUNT: &str = r#"
exists (n: Long). ((count for (t: Timepoint).
  where ((formerly within 1h (Drupe::Action::"Transfer"::request{} && tp(t)))
         && exists (m: Long). ((count for (u: Timepoint).
              where (formerly within 1h (Drupe::Action::"Login"::request{} && tp(u)))) == m
            && m > 0))) == n
  && n > 0)"#;

const COUNT_INSIDE_FORMERLY: &str = r#"
formerly within 1h (Drupe::Action::"Transfer"::request{}
  && count_within(1h, Drupe::Action::"Login"::request{}) > 5)"#;

const NEGATED: &str = r#"
(formerly within 1h Drupe::Action::"Transfer"::request{})
&& !(previous within 1h Drupe::Action::"Login"::request{})"#;

const AGGREGATE_ON_THE_RIGHT: &str = r#"5 < count_within(1h, Drupe::Action::"Login"::request{})"#;

#[test]
fn counts_are_zero_without_temporal_blocks() {
    assert_eq!(counts(&[]), Counts::default());
}

#[test]
fn temporal_operators_are_counted() {
    assert_eq!(
        counts(&[FORMERLY_AND_SINCE]),
        Counts {
            formerly: 1,
            since: 1,
            ..Counts::default()
        }
    );
}

#[test]
fn macro_calls_count_what_they_expand_to() {
    assert_eq!(
        counts(&[COUNT_WITHIN]),
        Counts {
            formerly: 1,
            count: 1,
            ..Counts::default()
        }
    );
    assert_eq!(
        counts(&[BIND_SUM_WITHIN]),
        Counts {
            formerly: 1,
            sum: 1,
            exists: 1,
            ..Counts::default()
        }
    );
}

#[test]
fn an_aggregation_inside_another_aggregation_is_counted() {
    assert_eq!(
        counts(&[COUNT_INSIDE_COUNT]),
        Counts {
            formerly: 2,
            count: 2,
            exists: 2,
            ..Counts::default()
        }
    );
}

#[test]
fn an_aggregation_inside_a_temporal_operator_is_counted() {
    assert_eq!(
        counts(&[COUNT_INSIDE_FORMERLY]),
        Counts {
            formerly: 2,
            count: 1,
            ..Counts::default()
        }
    );
}

#[test]
fn operators_under_negation_are_counted() {
    assert_eq!(
        counts(&[NEGATED]),
        Counts {
            formerly: 1,
            previous: 1,
            ..Counts::default()
        }
    );
}

#[test]
fn an_aggregate_on_the_right_of_a_comparison_is_counted() {
    assert_eq!(
        counts(&[AGGREGATE_ON_THE_RIGHT]),
        Counts {
            formerly: 1,
            count: 1,
            ..Counts::default()
        }
    );
}

#[test]
fn counts_add_across_blocks() {
    assert_eq!(
        counts(&[COUNT_INSIDE_COUNT, COUNT_WITHIN]),
        Counts {
            formerly: 3,
            count: 3,
            exists: 2,
            ..Counts::default()
        }
    );
}
