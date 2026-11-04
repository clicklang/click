//! Atomic observation aliases retain their original source, not a second fact.
//! Keys inspect the selected operands only; shared arithmetic is never exported.
use super::checked_scalar_facts::ScalarOperandKey;
use super::*;
use crate::kernel::machine_integer::{
    Relation,
    comparison::{NativeComparisonView, comparison_view, native_comparison_view},
};
use crate::persistent::{PersistentMap, PersistentSet};

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub(in crate::kernel) enum OperandKey {
    Constant(u128),
    Term(ScalarOperandKey),
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub(in crate::kernel) enum Key {
    Truth(bool),
    Comparison(MachineIntegerType, u8, [OperandKey; 2]),
    Overflow(
        MachineIntegerType,
        OverflowOperation,
        [ScalarOperandKey; 2],
        bool,
    ),
}

/// Comparison identity for compound and quantified facts. Numeric leaves use
/// shared operand identities; all other leaves keep their exact proposition.
#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub(in crate::kernel) enum PropositionKey {
    Comparison(Key),
    Exact(Proposition),
    Not(Box<Self>),
    And(Box<Self>, Box<Self>),
    Or(Box<Self>, Box<Self>),
    Implies(Box<Self>, Box<Self>),
    ForAll(Variable, Sort, Box<Self>),
    Exists(Variable, Sort, Box<Self>),
}
impl PropositionKey {
    pub(in crate::kernel) fn observes_machine(proposition: &Proposition) -> bool {
        let mut pending = vec![proposition];
        while let Some(proposition) = pending.pop() {
            crate::instrumentation::record_deterministic_work(1);
            match proposition {
                Proposition::ConditionIs(condition, truth)
                    if native_comparison_view(condition, *truth).is_some() =>
                {
                    return true;
                }
                Proposition::And(a, b) | Proposition::Or(a, b) | Proposition::Implies(a, b) => {
                    pending.push(a);
                    pending.push(b);
                }
                Proposition::Not(body)
                | Proposition::ForAll { body, .. }
                | Proposition::Exists { body, .. } => pending.push(body),
                _ => {}
            }
        }
        false
    }

    pub(in crate::kernel) fn new(proposition: &Proposition) -> Self {
        crate::instrumentation::record_deterministic_work(1);
        match proposition {
            Proposition::ConditionIs(condition, truth) => {
                if let Some(view) = comparison_view(condition, *truth) {
                    let view = view.widened().unwrap_or(view);
                    Self::Comparison(key(&view))
                } else {
                    Self::Exact(proposition.clone())
                }
            }
            Proposition::Not(body) => Self::Not(Box::new(Self::new(body))),
            Proposition::And(a, b) => Self::And(Box::new(Self::new(a)), Box::new(Self::new(b))),
            Proposition::Or(a, b) => Self::Or(Box::new(Self::new(a)), Box::new(Self::new(b))),
            Proposition::Implies(a, b) => {
                Self::Implies(Box::new(Self::new(a)), Box::new(Self::new(b)))
            }
            Proposition::ForAll {
                var, sort, body, ..
            } => Self::ForAll(*var, sort.clone(), Box::new(Self::new(body))),
            Proposition::Exists {
                var, sort, body, ..
            } => Self::Exists(*var, sort.clone(), Box::new(Self::new(body))),
            _ => Self::Exact(proposition.clone()),
        }
    }
}

fn key(view: &NativeComparisonView<'_>) -> Key {
    let equality = matches!(view.relation, Relation::Equal | Relation::NotEqual);
    let format = if equality {
        match view.format {
            MachineIntegerType::UInt8 => MachineIntegerType::Int8,
            MachineIntegerType::UInt16 => MachineIntegerType::Int16,
            MachineIntegerType::UInt32 => MachineIntegerType::Int32,
            MachineIntegerType::UInt64 => MachineIntegerType::Int64,
            other => other,
        }
    } else {
        view.format
    };
    let mut operands = view.operands.each_ref().map(|operand| {
        let operand = operand.operand_view();
        if let Some(value) = operand
            .literal()
            .and_then(|literal| view.format.constant_from_term(&literal))
        {
            OperandKey::Constant(value.bits())
        } else {
            OperandKey::Term(ScalarOperandKey::for_format(format, operand))
        }
    });
    if equality && operands[1] < operands[0] {
        operands.swap(0, 1);
    }
    let relation = match view.relation {
        Relation::Equal => 0,
        Relation::NotEqual => 1,
        Relation::Less => 2,
        Relation::LessEqual => 3,
    };
    Key::Comparison(format, relation, operands)
}

/// Exact comparison identity for an already selected source. This is not a
/// search and does not decide a stronger or weaker bound.
pub(in crate::kernel) fn same_comparison(
    condition: &ConditionTerm,
    truth: bool,
    source: &Proposition,
) -> bool {
    let Proposition::ConditionIs(other, value) = source else {
        return false;
    };
    match (
        crate::kernel::machine_integer::comparison::structural_native_comparison_view(
            condition, truth,
        ),
        comparison_view(other, *value),
    ) {
        (Some(left), Some(right)) => key(&left) == key(&right),
        _ => false,
    }
}

/// The intrinsic rules formerly reached through the native comparison
/// constructors. Read shared roots and exact format ranges, never export.
pub(super) fn constant_observation_value(condition: &ConditionTerm) -> Option<bool> {
    let view = native_comparison_view(condition, true)?;
    constant_reading(&view, &key(&view))
}

// A constant comparison view is still supported by its source. In particular,
// `to_integer(count) <= UINT64_MAX` used to file `true`; retain that authority
// without adding a tautology to the proof-state fact collection.
fn constant_reading(view: &NativeComparisonView<'_>, key: &Key) -> Option<bool> {
    let Key::Comparison(_, _, [left, right]) = key else {
        return None;
    };
    if left == right {
        return Some(matches!(
            view.relation,
            Relation::Equal | Relation::LessEqual
        ));
    }
    let values = view.operands.each_ref().map(|operand| {
        operand
            .operand_view()
            .literal()
            .and_then(|literal| view.format.constant_from_term(&literal))
            .map(|value| value.to_integer())
    });
    let [left, right] = &values;
    if let (Some(left), Some(right)) = (left, right) {
        return Some(match view.relation {
            Relation::Equal => left == right,
            Relation::NotEqual => left != right,
            Relation::Less => left < right,
            Relation::LessEqual => left <= right,
        });
    }
    if view.format == MachineIntegerType::Int64 {
        let [left, right] = view.operands.each_ref().map(|operand| {
            operand
                .operand_view()
                .int64_width_interval()
                .unwrap_or((i64::MIN, i64::MAX))
        });
        match view.relation {
            Relation::Less if left.1 < right.0 => return Some(true),
            Relation::Less if left.0 >= right.1 => return Some(false),
            Relation::LessEqual if left.1 <= right.0 => return Some(true),
            Relation::LessEqual if left.0 > right.1 => return Some(false),
            _ => {}
        }
    }
    if view.format == MachineIntegerType::UInt32 {
        let [left, right] = view
            .operands
            .each_ref()
            .map(|operand| operand.operand_view());
        if let Some(bound) = right.word32_constant() {
            let upper = left
                .word32_constant()
                .or_else(|| {
                    let (format, operation, [a, b]) = left.binary()?;
                    (format.format().bits() == 32
                        && operation == crate::kernel::MachineBinaryOp::BitwiseAnd)
                        .then(|| a.word32_constant().or_else(|| b.word32_constant()))
                        .flatten()
                })
                .unwrap_or(u32::MAX);
            if (view.relation == Relation::Less && upper < bound)
                || (view.relation == Relation::LessEqual && upper <= bound)
            {
                return Some(true);
            }
        }
    }
    // The unsigned 64-bit folding constructors recognize these endpoint rules.
    if view.format == MachineIntegerType::UInt64 {
        let (min, max) = view.format.format().bounds();
        match view.relation {
            Relation::LessEqual if left.as_ref() == Some(&min) || right.as_ref() == Some(&max) => {
                return Some(true);
            }
            Relation::Less if left.as_ref() == Some(&max) || right.as_ref() == Some(&min) => {
                return Some(false);
            }
            _ => {}
        }
    }
    None
}

#[derive(Clone, Debug, Default)]
pub(in crate::kernel) struct ObservationComparisons {
    keys_by_source: PersistentMap<Proposition, Vec<Key>>,
    sources: PersistentMap<Key, PersistentSet<Proposition>>,
    // The existing four-byte offset rule, indexed separately so admission
    // does not alter unrelated observation/constant-query work.
    scaled_words: PersistentMap<Key, PersistentSet<Proposition>>,
}

impl ObservationComparisons {
    pub(super) fn adjust(&mut self, condition: &ConditionTerm, truth: bool, insert: bool) {
        let source = Proposition::ConditionIs(condition.clone(), truth);
        if let ConditionTerm::PointerOffsetEqual(left, right) = condition {
            use crate::kernel::machine_integer::comparison::ComparisonOperand;
            fn operand(offset: &PointerOffsetTerm) -> Option<ComparisonOperand<'_>> {
                match offset {
                    PointerOffsetTerm::Int32Scaled {
                        value,
                        byte_width: 4,
                    } => Some(ComparisonOperand::Written(value)),
                    PointerOffsetTerm::Constant(bytes) if bytes % 4 == 0 => {
                        i32::try_from(bytes / 4).ok().map(|value| {
                            ComparisonOperand::Constant(Bitvector32Term::constant(value as u32))
                        })
                    }
                    _ => None,
                }
            }
            if let (Some(left), Some(right)) = (operand(left), operand(right)) {
                let key = key(&NativeComparisonView {
                    format: MachineIntegerType::Int32,
                    relation: if truth {
                        Relation::Equal
                    } else {
                        Relation::NotEqual
                    },
                    operands: [left, right],
                });
                let sources = self.scaled_words.get(&key).cloned().unwrap_or_default();
                let sources = if insert {
                    sources.with_value(source.clone())
                } else {
                    sources.without_value(&source)
                };
                self.scaled_words = if sources.is_empty() {
                    self.scaled_words.without_key(&key)
                } else {
                    self.scaled_words.with_inserted(key, sources)
                };
            }
            return;
        }
        let keys = if insert {
            let keys = if let ConditionTerm::Overflows {
                format,
                op,
                left,
                right,
            } = condition
            {
                vec![Self::overflow_key(
                    *format,
                    *op,
                    [
                        MachineOperandView::Legacy(left),
                        MachineOperandView::Legacy(right),
                    ],
                    truth,
                )]
            } else {
                let Some(view) = native_comparison_view(condition, truth) else {
                    return;
                };
                let comparison = key(&view);
                let mut keys = vec![comparison.clone()];
                let cancelled_view = view.clone().cancelled_form();
                let cancelled = key(&cancelled_view);
                if cancelled != comparison {
                    keys.push(cancelled.clone());
                }
                if let Some(widened) = view.widened() {
                    keys.push(key(&widened));
                }
                if let Some(value) = constant_reading(&view, &comparison)
                    .or_else(|| constant_reading(&cancelled_view, &cancelled))
                {
                    keys.push(Key::Truth(value));
                }
                keys
            };
            self.keys_by_source = self
                .keys_by_source
                .with_inserted(source.clone(), keys.clone());
            keys
        } else {
            let Some(keys) = self.keys_by_source.get(&source).cloned() else {
                return;
            };
            self.keys_by_source = self.keys_by_source.without_key(&source);
            keys
        };
        for key in keys {
            crate::instrumentation::record_deterministic_work(1);
            let sources = self.sources.get(&key).cloned().unwrap_or_default();
            let sources = if insert {
                sources.with_value(source.clone())
            } else {
                sources.without_value(&source)
            };
            self.sources = if sources.is_empty() {
                self.sources.without_key(&key)
            } else {
                self.sources.with_inserted(key, sources)
            };
        }
    }

    fn overflow_key(
        format: MachineIntegerType,
        op: OverflowOperation,
        operands: [MachineOperandView<'_>; 2],
        truth: bool,
    ) -> Key {
        Key::Overflow(
            format,
            op,
            operands.map(|operand| ScalarOperandKey::for_format(format, operand)),
            truth,
        )
    }

    pub(super) fn overflow_source(
        &self,
        format: MachineIntegerType,
        op: OverflowOperation,
        operands: [MachineOperandView<'_>; 2],
        truth: bool,
    ) -> Option<&Proposition> {
        crate::instrumentation::record_deterministic_work(1);
        self.sources
            .get(&Self::overflow_key(format, op, operands, truth))?
            .iter()
            .next()
    }

    pub(super) fn scaled_source(
        &self,
        format: MachineIntegerType,
        operands: [MachineOperandView<'_>; 2],
        truth: bool,
    ) -> Option<&Proposition> {
        use crate::kernel::machine_integer::comparison::ComparisonOperand;
        crate::instrumentation::record_deterministic_work(1);
        if self.scaled_words.is_empty() {
            return None;
        }
        let view = NativeComparisonView {
            format,
            relation: if truth {
                Relation::Equal
            } else {
                Relation::NotEqual
            },
            operands: operands.map(|operand| match operand {
                MachineOperandView::Legacy(term) => ComparisonOperand::Written(term),
                MachineOperandView::Shared(_) => {
                    ComparisonOperand::Observation(operand.retain(format))
                }
            }),
        };
        self.scaled_words.get(&key(&view))?.iter().next()
    }

    pub(super) fn false_source(&self) -> Option<&Proposition> {
        self.sources.get(&Key::Truth(false))?.iter().next()
    }

    pub(in crate::kernel) fn source(
        &self,
        condition: &ConditionTerm,
        truth: bool,
    ) -> Option<&Proposition> {
        if self.sources.is_empty() {
            return None;
        }
        let _checking =
            crate::instrumentation::CheckingWorkScope::new("read observation comparison source", 1);
        crate::instrumentation::record_deterministic_work(1);
        let key = if let ConditionTerm::Constant(value) = condition {
            Key::Truth(*value == truth)
        } else {
            key(&comparison_view(condition, truth)?)
        };
        self.sources.get(&key)?.iter().next()
    }
}
