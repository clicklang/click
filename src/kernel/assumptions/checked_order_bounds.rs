//! Direct extrema and witnesses for checked order queries. Each admitted fact
//! changes only its two endpoint keys; queries never enumerate those buckets.
use super::*;
use crate::kernel::MachineOperandView;
use crate::kernel::equality_graph::MachineAtom;
use crate::persistent::{PersistentMap, PersistentSet};

type Bound = (i64, ConditionTerm, bool);

#[derive(Clone, Debug, Default)]
struct EndpointBounds {
    symbolic_lower: PersistentSet<(ConditionTerm, bool)>,
    symbolic_upper: PersistentSet<(ConditionTerm, bool)>,
    strict_lower: usize,
    strict_upper: usize,
    lower: PersistentSet<Bound>,
    upper: PersistentSet<Bound>,
}

#[derive(Clone, Debug, Default)]
pub(in crate::kernel) struct CheckedOrderBounds {
    signed_wide: PersistentMap<MachineAtom, EndpointBounds>,
    endpoints: [PersistentMap<MachineAtom, EndpointBounds>; 2],
    strict_upper: PersistentMap<MachineAtom, PersistentSet<(ConditionTerm, bool)>>,
}

impl CheckedOrderBounds {
    pub(super) fn adjust(&mut self, condition: &ConditionTerm, value: bool, insert: bool) {
        if self.adjust_signed_wide(condition, value, insert) {
            return;
        }
        use crate::kernel::machine_integer::{Relation, comparison::comparison_view};
        if let Some(view) = comparison_view(condition, value) {
            let kind = match view.format {
                MachineIntegerType::Int32 => 0,
                MachineIntegerType::UInt32 => 1,
                _ => return,
            };
            let strict = match view.relation {
                Relation::Less => true,
                Relation::LessEqual => false,
                Relation::Equal | Relation::NotEqual => return,
            };
            self.adjust_word_endpoints(
                kind,
                view.operands[0].operand_view(),
                view.operands[1].operand_view(),
                strict,
                condition,
                value,
                insert,
            );
        }
    }

    fn word_key(term: MachineOperandView<'_>) -> MachineAtom {
        MachineAtom::from_operand(MachineIntegerType::Int32, term)
    }

    fn adjust_word_endpoints(
        &mut self,
        kind: usize,
        left: MachineOperandView<'_>,
        right: MachineOperandView<'_>,
        strict: bool,
        condition: &ConditionTerm,
        value: bool,
        insert: bool,
    ) {
        if kind == 0 && strict {
            let left = Self::word_key(left);
            let mut sources = self.strict_upper.get(&left).cloned().unwrap_or_default();
            let source = (condition.clone(), value);
            sources = if insert {
                sources.with_value(source)
            } else {
                sources.without_value(&source)
            };
            self.strict_upper = if sources.is_empty() {
                self.strict_upper.without_key(&left)
            } else {
                self.strict_upper.with_inserted(left.clone(), sources)
            };
        }
        for (endpoint, other, upper) in [(left, right, true), (right, left, false)] {
            let number = other.word32_constant().map(|bits| {
                if kind == 0 {
                    i64::from(bits as i32)
                } else {
                    i64::from(bits)
                }
            });
            let number = number.map(|number| {
                number
                    + if strict {
                        if upper { -1 } else { 1 }
                    } else {
                        0
                    }
            });
            let key = Self::word_key(endpoint);
            let alias = match endpoint {
                MachineOperandView::Shared(_) => None,
                MachineOperandView::Legacy(term) => {
                    let canonical = crate::kernel::eval::canonical_term(term);
                    (canonical != *term)
                        .then(|| Self::word_key(MachineOperandView::Legacy(&canonical)))
                }
            };
            for key in std::iter::once(key).chain(alias) {
                crate::instrumentation::record_deterministic_work(1);
                let mut bounds = self.endpoints[kind].get(&key).cloned().unwrap_or_default();
                if number.is_none() {
                    let sources = if upper {
                        &mut bounds.symbolic_upper
                    } else {
                        &mut bounds.symbolic_lower
                    };
                    let source = (condition.clone(), value);
                    *sources = if insert {
                        sources.with_value(source)
                    } else {
                        sources.without_value(&source)
                    };
                }
                if strict {
                    let count = if upper {
                        &mut bounds.strict_upper
                    } else {
                        &mut bounds.strict_lower
                    };
                    if insert {
                        *count += 1;
                    } else {
                        *count -= 1;
                    }
                }
                if let Some(number) = number {
                    let sources = if upper {
                        &mut bounds.upper
                    } else {
                        &mut bounds.lower
                    };
                    let source = (number, condition.clone(), value);
                    *sources = if insert {
                        sources.with_value(source)
                    } else {
                        sources.without_value(&source)
                    };
                }
                self.endpoints[kind] = if bounds.lower.is_empty()
                    && bounds.upper.is_empty()
                    && bounds.symbolic_lower.is_empty()
                    && bounds.symbolic_upper.is_empty()
                    && bounds.strict_lower == 0
                    && bounds.strict_upper == 0
                {
                    self.endpoints[kind].without_key(&key)
                } else {
                    self.endpoints[kind].with_inserted(key.clone(), bounds)
                };
            }
        }
    }

    fn adjust_signed_wide(&mut self, condition: &ConditionTerm, value: bool, insert: bool) -> bool {
        use crate::kernel::machine_integer::{Relation, comparison::comparison_view};
        if let Some(view) = comparison_view(condition, value)
            && view.format == MachineIntegerType::Int64
        {
            let strict = match view.relation {
                Relation::Less => true,
                Relation::LessEqual => false,
                Relation::Equal | Relation::NotEqual => return true,
            };
            let [left, right] = &view.operands;
            for (endpoint, other, upper) in [(left, right, true), (right, left, false)] {
                let Some(number) = other
                    .operand_view()
                    .int64_constant()
                    .and_then(|n| Self::wide_endpoint(n, strict, upper))
                else {
                    continue;
                };
                let key =
                    MachineAtom::from_operand(MachineIntegerType::UInt64, endpoint.operand_view());
                self.adjust_wide_endpoint(key, number, upper, condition, value, insert);
                // Shared arithmetic has no atomic load/cast payload to
                // canonicalize; legacy inputs retain their exact alias key.
                if let crate::kernel::MachineOperandView::Legacy(term) = endpoint.operand_view() {
                    let canonical = crate::kernel::eval::canonical_term(term);
                    if canonical != *term {
                        self.adjust_wide_endpoint(
                            MachineAtom::uint64(canonical),
                            number,
                            upper,
                            condition,
                            value,
                            insert,
                        );
                    }
                }
            }
            return true;
        }
        false
    }

    fn wide_endpoint(number: i64, strict: bool, upper: bool) -> Option<i64> {
        if !strict {
            Some(number)
        } else if upper {
            number.checked_sub(1)
        } else {
            number.checked_add(1)
        }
    }

    fn adjust_wide_endpoint(
        &mut self,
        key: MachineAtom,
        number: i64,
        upper: bool,
        condition: &ConditionTerm,
        value: bool,
        insert: bool,
    ) {
        crate::instrumentation::record_deterministic_work(1);
        let mut bounds = self.signed_wide.get(&key).cloned().unwrap_or_default();
        let sources = if upper {
            &mut bounds.upper
        } else {
            &mut bounds.lower
        };
        let source = (number, condition.clone(), value);
        *sources = if insert {
            sources.with_value(source)
        } else {
            sources.without_value(&source)
        };
        if bounds.lower.is_empty() && bounds.upper.is_empty() {
            self.signed_wide.remove(&key);
        } else {
            self.signed_wide.insert(key, bounds);
        }
    }

    pub(super) fn signed_wide_interval(&self, term: &Bitvector32Term) -> Option<(i64, i64)> {
        self.signed_wide_interval_view(crate::kernel::MachineOperandView::Legacy(term))
    }

    pub(super) fn signed_wide_interval_view(
        &self,
        term: crate::kernel::MachineOperandView<'_>,
    ) -> Option<(i64, i64)> {
        let _checking =
            crate::instrumentation::CheckingWorkScope::new("read indexed signed wide bounds", 1);
        crate::instrumentation::record_deterministic_work(1);
        let key = MachineAtom::from_operand(MachineIntegerType::UInt64, term);
        let bounds = self.signed_wide.get(&key)?;
        Some((
            bounds
                .lower
                .iter()
                .next_back()
                .map_or(i64::MIN, |bound| bound.0),
            bounds.upper.iter().next().map_or(i64::MAX, |bound| bound.0),
        ))
    }

    pub(super) fn interval(&self, term: &Bitvector32Term, unsigned: bool) -> Option<(i64, i64)> {
        self.interval_view(MachineOperandView::Legacy(term), unsigned)
    }

    pub(super) fn interval_view(
        &self,
        term: MachineOperandView<'_>,
        unsigned: bool,
    ) -> Option<(i64, i64)> {
        let _checking =
            crate::instrumentation::CheckingWorkScope::new("read indexed order bounds", 1);
        crate::instrumentation::record_deterministic_work(1);
        let bounds = self.endpoints[usize::from(unsigned)].get(&Self::word_key(term))?;
        if bounds.lower.is_empty() && bounds.upper.is_empty() {
            return None;
        }
        let (min, max) = if unsigned {
            (0, i64::from(u32::MAX))
        } else {
            (i64::from(i32::MIN), i64::from(i32::MAX))
        };
        Some((
            bounds
                .lower
                .iter()
                .next_back()
                .map_or(min, |bound| min.max(bound.0)),
            bounds
                .upper
                .iter()
                .next()
                .map_or(max, |bound| max.min(bound.0)),
        ))
    }

    /// The two numeric extrema used by `interval_view`, with their exact
    /// admitted sources. Selection is fixed-size even when one endpoint has
    /// many weaker bounds; it does not enumerate that endpoint's bucket.
    pub(super) fn interval_sources_view(
        &self,
        term: MachineOperandView<'_>,
        unsigned: bool,
    ) -> [Option<Proposition>; 2] {
        let _checking =
            crate::instrumentation::CheckingWorkScope::new("select indexed interval bounds", 1);
        crate::instrumentation::record_deterministic_work(1);
        let Some(bounds) = self.endpoints[usize::from(unsigned)].get(&Self::word_key(term)) else {
            return [None, None];
        };
        let source =
            |(_, condition, value): &Bound| Proposition::ConditionIs(condition.clone(), *value);
        [
            bounds.lower.iter().next_back().map(source),
            bounds.upper.iter().next().map(source),
        ]
    }

    /// At most one numeric extremum and one unambiguous symbolic source per
    /// direction. The fixed four slots are selected, never a bucket iterator.
    pub(super) fn constant_evidence_sources(
        &self,
        term: &Bitvector32Term,
    ) -> [Option<Proposition>; 4] {
        let _checking =
            crate::instrumentation::CheckingWorkScope::new("select constant bound evidence", 1);
        crate::instrumentation::record_deterministic_work(1);
        let Some(bounds) = self.endpoints[0].get(&Self::word_key(MachineOperandView::Legacy(term)))
        else {
            return [None, None, None, None];
        };
        let proposition =
            |(_, condition, value): &Bound| Proposition::ConditionIs(condition.clone(), *value);
        let singleton = |sources: &PersistentSet<(ConditionTerm, bool)>| {
            if sources.len() != 1 {
                return None;
            }
            let (condition, value) = sources.iter().next()?;
            Some(Proposition::ConditionIs(condition.clone(), *value))
        };
        [
            bounds.lower.iter().next_back().map(proposition),
            bounds.upper.iter().next().map(proposition),
            singleton(&bounds.symbolic_lower),
            singleton(&bounds.symbolic_upper),
        ]
    }

    /// Numeric extrema and carrier limits implied by a direct strict edge.
    pub(super) fn interval_with_strict(&self, term: &Bitvector32Term) -> Option<(i64, i64)> {
        let _checking =
            crate::instrumentation::CheckingWorkScope::new("read direct signed interval", 1);
        crate::instrumentation::record_deterministic_work(1);
        let bounds = self.endpoints[0].get(&Self::word_key(MachineOperandView::Legacy(term)))?;
        let (lower, upper) = self
            .interval(term, false)
            .unwrap_or((i64::from(i32::MIN), i64::from(i32::MAX)));
        Some((
            lower.max(i64::from(i32::MIN) + i64::from(bounds.strict_lower > 0)),
            upper.min(i64::from(i32::MAX) - i64::from(bounds.strict_upper > 0)),
        ))
    }

    pub(super) fn strict_upper(&self, term: &Bitvector32Term) -> Option<Proposition> {
        let _checking =
            crate::instrumentation::CheckingWorkScope::new("select indexed order witness", 1);
        crate::instrumentation::record_deterministic_work(1);
        let (condition, value) = self
            .strict_upper
            .get(&Self::word_key(MachineOperandView::Legacy(term)))?
            .iter()
            .next()?;
        Some(Proposition::ConditionIs(condition.clone(), *value))
    }

    pub(super) fn upper_below_max(&self, term: &Bitvector32Term) -> Option<Proposition> {
        let _checking =
            crate::instrumentation::CheckingWorkScope::new("select indexed order witness", 1);
        crate::instrumentation::record_deterministic_work(1);
        let (number, condition, value) = self.endpoints[0]
            .get(&Self::word_key(MachineOperandView::Legacy(term)))?
            .upper
            .iter()
            .next()?;
        (*number < i64::from(i32::MAX)).then(|| Proposition::ConditionIs(condition.clone(), *value))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn shared_bounds_keep_closed_arithmetic_and_signedness() {
        use crate::kernel::{IntegerTerm, KernelTermImport, SharedMachineIntegerTerm};
        let _session = crate::kernel::VerificationSession::enter();
        for format in [
            MachineIntegerType::Int32,
            MachineIntegerType::UInt32,
            MachineIntegerType::Int64,
        ] {
            let x = Bitvector32Term::Variable(Variable(982003));
            let literal = |n| {
                if format == MachineIntegerType::Int64 {
                    Bitvector32Term::Int64Constant(n)
                } else {
                    Bitvector32Term::Constant(n as u32)
                }
            };
            let bound = Bitvector32Term::Binary {
                format,
                op: MachineBinaryOp::Add,
                left: Box::new(literal(1)),
                right: Box::new(literal(2)),
            };
            let observe = |word: &Bitvector32Term| {
                SharedMachineIntegerTerm::from_shared(
                    format,
                    KernelTermImport::default().machine(format, word),
                )
                .unwrap()
            };
            let left = observe(&x);
            let right = observe(&bound);
            let condition = ConditionTerm::integer_less_equal(
                IntegerTerm::Machine(left.clone()),
                IntegerTerm::Machine(right.clone()),
            );
            let mut index = CheckedOrderBounds::default();
            index.adjust(&condition, true, true);
            let read = |index: &CheckedOrderBounds| {
                if format == MachineIntegerType::Int64 {
                    index.signed_wide_interval_view(left.operand_view())
                } else {
                    index.interval_view(left.operand_view(), format == MachineIntegerType::UInt32)
                }
            };
            assert_eq!(read(&index).unwrap().1, 3);
            let mut branch = index.clone();
            branch.adjust(&condition, true, false);
            assert_eq!(read(&branch), None);
            assert_eq!(read(&index).unwrap().1, 3);
            assert!(!left.has_boxed_operand());
            assert!(!right.has_boxed_operand());
        }
    }

    #[test]
    fn signed_wide_extrema_keep_strictness_withdrawal_and_branches() {
        let _session = crate::kernel::VerificationSession::enter();
        let x = Bitvector32Term::Variable(Variable(982000));
        let less =
            |n| ConditionTerm::int64_signed_less_than(x.clone(), Bitvector32Term::Int64Constant(n));
        let mut index = CheckedOrderBounds::default();
        index.adjust(&less(10), true, true);
        index.adjust(&less(0), false, true);
        assert_eq!(index.signed_wide_interval(&x), Some((0, 9)));
        let mut branch = index.clone();
        branch.adjust(&less(5), true, true);
        assert_eq!(branch.signed_wide_interval(&x), Some((0, 4)));
        assert_eq!(index.signed_wide_interval(&x), Some((0, 9)));
        branch.adjust(&less(5), true, false);
        assert_eq!(branch.signed_wide_interval(&x), Some((0, 9)));
        branch.adjust(&less(10), true, false);
        assert_eq!(branch.signed_wide_interval(&x), Some((0, i64::MAX)));
        branch.adjust(&less(0), false, false);
        assert_eq!(branch.signed_wide_interval(&x), None);
        // Preserve the old interval reader's refusal to wrap an impossible
        // strict endpoint. Contradiction handling remains a separate rule.
        branch.adjust(&less(i64::MIN), true, true);
        assert_eq!(branch.signed_wide_interval(&x), None);
    }

    #[cfg(test)]
    mod scaling_tests {
        include!("../../scaling_tests/kernel/assumptions/checked_order_bounds/tests.rs");
    }
}
