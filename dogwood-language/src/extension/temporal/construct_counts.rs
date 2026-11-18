use super::ast::{AggExpr, AggExprKind, Condition, ConditionKind};

/// How many times each temporal operator, aggregation and `exists` appears in
/// a policy, as returned by
/// [`ParsedPolicy::temporal_construct_counts`](crate::policy_set::ParsedPolicy::temporal_construct_counts).
/// Each method is named after the keyword it counts.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct TemporalConstructCounts {
    formerly: usize,
    previous: usize,
    since: usize,
    count: usize,
    sum: usize,
    exists: usize,
}

impl TemporalConstructCounts {
    pub fn formerly(&self) -> usize {
        self.formerly
    }

    pub fn previous(&self) -> usize {
        self.previous
    }

    pub fn since(&self) -> usize {
        self.since
    }

    pub fn count(&self) -> usize {
        self.count
    }

    pub fn sum(&self) -> usize {
        self.sum
    }

    pub fn exists(&self) -> usize {
        self.exists
    }

    pub(crate) fn tally(&mut self, condition: &Condition) {
        match &condition.kind {
            ConditionKind::Formerly { body, .. } => {
                self.formerly += 1;
                self.tally(body);
            }
            ConditionKind::Previous { body, .. } => {
                self.previous += 1;
                self.tally(body);
            }
            ConditionKind::Since { left, right, .. } => {
                self.since += 1;
                self.tally(left);
                self.tally(right);
            }
            ConditionKind::Exists { body, .. } => {
                self.exists += 1;
                self.tally(body);
            }
            ConditionKind::And { left, right } | ConditionKind::Or { left, right } => {
                self.tally(left);
                self.tally(right);
            }
            ConditionKind::Not { inner } => self.tally(inner),
            // check_condition only allows aggregates as comparison operands.
            ConditionKind::Comparison { left, right, .. } => {
                left.for_each_operand_agg(&mut |agg| self.tally_aggregate(agg));
                right.for_each_operand_agg(&mut |agg| self.tally_aggregate(agg));
            }
            ConditionKind::Predicate(_) | ConditionKind::Tp { .. } => {}
            // Macro expansion replaces these before a ParsedPolicy exists.
            ConditionKind::Call(_)
            | ConditionKind::SigilRef { .. }
            | ConditionKind::Refine { .. } => {}
        }
    }

    fn tally_aggregate(&mut self, agg: &AggExpr) {
        match &agg.kind {
            AggExprKind::Count { body, .. } => {
                self.count += 1;
                self.tally(body);
            }
            AggExprKind::Sum { body, .. } => {
                self.sum += 1;
                self.tally(body);
            }
            // Macro expansion replaces this before a ParsedPolicy exists.
            AggExprKind::Call(_) => {}
        }
    }
}
