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
    /// Build an admitted comparison key in one walk, retaining it only when
    /// some leaf has a machine comparison reading. Detection must not walk
    /// the proposition again before constructing the same key.
    pub(in crate::kernel) fn for_source(proposition: &Proposition) -> Option<Self> {
        let (key, observes) = Self::with_presence(proposition);
        observes.then_some(key)
    }

    pub(in crate::kernel) fn new(proposition: &Proposition) -> Self {
        Self::with_presence(proposition).0
    }

    fn with_presence(proposition: &Proposition) -> (Self, bool) {
        crate::instrumentation::record_deterministic_work(1);
        match proposition {
            Proposition::ConditionIs(condition, truth) => {
                if let Some(view) = comparison_view(condition, *truth) {
                    let view = view.widened().unwrap_or(view);
                    (Self::Comparison(key(&view)), true)
                } else {
                    (Self::Exact(proposition.clone()), false)
                }
            }
            Proposition::Not(body) => {
                let (key, observes) = Self::with_presence(body);
                (Self::Not(Box::new(key)), observes)
            }
            Proposition::And(a, b) | Proposition::Or(a, b) | Proposition::Implies(a, b) => {
                let (a, left) = Self::with_presence(a);
                let (b, right) = Self::with_presence(b);
                let (a, b) = (Box::new(a), Box::new(b));
                let key = match proposition {
                    Proposition::And(..) => Self::And(a, b),
                    Proposition::Or(..) => Self::Or(a, b),
                    _ => Self::Implies(a, b),
                };
                (key, left || right)
            }
            Proposition::ForAll {
                var, sort, body, ..
            } => {
                let (key, observes) = Self::with_presence(body);
                (Self::ForAll(*var, sort.clone(), Box::new(key)), observes)
            }
            Proposition::Exists {
                var, sort, body, ..
            } => {
                let (key, observes) = Self::with_presence(body);
                (Self::Exists(*var, sort.clone(), Box::new(key)), observes)
            }
            _ => (Self::Exact(proposition.clone()), false),
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
pub(in crate::kernel) fn constant_observation_value(condition: &ConditionTerm) -> Option<bool> {
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
    // Exact native equality endpoints for explicitly selected guards. Keep
    // these out of general observation lookup, like native order sources.
    selected_native_equalities: PersistentMap<Key, PersistentSet<Proposition>>,
    sources: PersistentMap<Key, PersistentSet<Proposition>>,
    // The existing four-byte offset rule, indexed separately so admission
    // does not alter unrelated observation/constant-query work.
    scaled_words: PersistentMap<Key, PersistentSet<Proposition>>,
}

impl ObservationComparisons {
    pub(super) fn adjust_native_equality(
        &mut self,
        condition: &ConditionTerm,
        truth: bool,
        insert: bool,
    ) {
        if !matches!(
            condition,
            ConditionTerm::Compare {
                relation: CompareRelation::Equal,
                ..
            }
        ) {
            return;
        }
        let view = comparison_view(condition, truth).expect("native equality");
        let key = key(&view);
        let source = Proposition::ConditionIs(condition.clone(), truth);
        let sources = self
            .selected_native_equalities
            .get(&key)
            .cloned()
            .unwrap_or_default();
        let sources = if insert {
            sources.with_value(source)
        } else {
            sources.without_value(&source)
        };
        self.selected_native_equalities = if sources.is_empty() {
            self.selected_native_equalities.without_key(&key)
        } else {
            self.selected_native_equalities.with_inserted(key, sources)
        };
    }

    fn selected_native_equality_source(
        &self,
        condition: &ConditionTerm,
        truth: bool,
    ) -> Option<&Proposition> {
        if self.selected_native_equalities.is_empty() {
            return None;
        }
        let view = match condition {
            ConditionTerm::Compare {
                relation: CompareRelation::Equal,
                ..
            } => comparison_view(condition, truth)?,
            ConditionTerm::IntegerEqual(..) | ConditionTerm::IntegerNotEqual(..) => {
                crate::kernel::machine_integer::comparison::structural_native_comparison_view(
                    condition, truth,
                )?
            }
            _ => return None,
        };
        self.selected_native_equalities
            .get(&key(&view))?
            .iter()
            .next()
    }

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
                            ComparisonOperand::Constant(MachineTerm::constant(value as u32))
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

#[cfg(test)]
mod compound_observation_lookup_tests {
    use super::*;
    use crate::kernel::{KernelTerm, KernelTermExport, KernelType, MachineBinaryOp};

    #[test]
    fn native_order_sources_retain_polarity_scope_and_withdrawal() {
        use crate::kernel::machine_integer::comparison::condition_for_operand_views;
        use crate::kernel::{KernelTermImport, MachineOperandView as V};
        for format in [
            MachineIntegerType::Int32,
            MachineIntegerType::UInt32,
            MachineIntegerType::Int64,
            MachineIntegerType::UInt64,
        ] {
            for truth in [false, true] {
                let _session = crate::kernel::VerificationSession::enter();
                let operand = MachineTerm::Binary {
                    format,
                    op: MachineBinaryOp::Add,
                    left: MachineTerm::Variable(Variable(989101)).into(),
                    right: MachineTerm::Variable(Variable(989102)).into(),
                };
                let bound = crate::kernel::machine_integer::range::constant_word(
                    format,
                    &num_bigint::BigInt::from(5),
                )
                .unwrap();
                let native = ConditionTerm::machine_compare(
                    format,
                    CompareRelation::LessThan,
                    operand.clone(),
                    bound.clone(),
                );
                let root = KernelTermImport::default()
                    .machine_arithmetic(format, &operand)
                    .unwrap();
                let query = condition_for_operand_views(
                    format,
                    CompareRelation::LessThan,
                    [V::Shared(&root), V::Legacy(&bound)],
                );
                let parent = PureFactContext::new();
                let mut child = parent.clone();
                child.adjust_signed_order_bound(&native, truth, true);
                let exports = KernelTermExport::machine_export_count();
                let raw = comparison_view(&native, truth).unwrap();
                let observed =
                    crate::kernel::machine_integer::comparison::structural_native_comparison_view(
                        &query, truth,
                    )
                    .unwrap();
                let keys = |view: &NativeComparisonView<'_>| {
                    view.operands.each_ref().map(|operand| {
                        ScalarOperandKey::for_format(view.format, operand.operand_view())
                    })
                };
                assert_eq!(
                    keys(&raw),
                    keys(&observed),
                    "format={format:?} truth={truth}, raw literals={:?}, observed literals={:?}",
                    raw.operands
                        .each_ref()
                        .map(|operand| operand.operand_view().literal()),
                    observed
                        .operands
                        .each_ref()
                        .map(|operand| operand.operand_view().literal())
                );
                assert_eq!(
                    child.selected_comparison_source(&query, truth),
                    Some(&Proposition::ConditionIs(native.clone(), truth))
                );
                assert!(child.selected_comparison_source(&query, !truth).is_none());
                assert!(parent.selected_comparison_source(&query, truth).is_none());
                child.adjust_signed_order_bound(&native, truth, false);
                assert!(child.selected_comparison_source(&query, truth).is_none());
                assert_eq!(KernelTermExport::machine_export_count(), exports);
            }
        }
    }

    #[test]
    fn compound_comparison_lookup_is_bidirectional_and_tracks_source_withdrawal() {
        let _session = crate::kernel::VerificationSession::enter();
        let ty = MachineIntegerType::Int32;
        let root = KernelTerm::machine_binary_shared(
            ty,
            MachineBinaryOp::Multiply,
            [
                KernelTerm::variable(KernelType::C(ty.c_type()), Variable(989001)),
                KernelTerm::variable(KernelType::C(ty.c_type()), Variable(989002)),
            ],
        );
        let retained = SharedMachineIntegerTerm::from_shared(ty, root).unwrap();
        let shared = ConditionTerm::integer_not_equal(
            IntegerTerm::Machine(retained.clone()),
            IntegerTerm::constant_i64(-1),
        );
        let other = Proposition::ConditionIs(ConditionTerm::Variable(Variable(989003)), true);
        let guard = |condition, truth| {
            Proposition::Or(
                Box::new(Proposition::ConditionIs(condition, truth)),
                Box::new(other.clone()),
            )
        };
        let shared_guard = guard(shared, true);
        let exports = KernelTermExport::machine_export_count();
        assert!(!retained.has_boxed_operand());
        let shared_context = PureFactContext::new().assume_proposition(shared_guard.clone());
        assert!(shared_context.proves_exact(&shared_guard));
        assert!(!retained.has_boxed_operand());
        assert_eq!(KernelTermExport::machine_export_count(), exports);

        let native = ConditionTerm::equal(
            MachineTerm::logical_machine_binary(
                ty,
                MachineBinaryOp::Multiply,
                MachineTerm::Variable(Variable(989001)),
                MachineTerm::Variable(Variable(989002)),
            ),
            MachineTerm::constant(u32::MAX),
        );
        let native_guard = guard(native.clone(), false);
        let native_context = PureFactContext::new().assume_proposition(native_guard.clone());
        let (proved, sources) = collect_reasoning_provenance(|| {
            capture_implicit_reasoning_provenance(|| native_context.proves_exact(&shared_guard))
        });
        assert!(proved);
        assert_eq!(sources, vec![native_guard.clone()]);
        assert!(!native_context.contains_assumed_exact(&shared_guard));
        assert!(shared_context.proves_exact(&native_guard));
        assert!(!native_context.proves_exact(&guard(native, true)));
        let both = native_context.assume_proposition(shared_guard.clone());
        let one = both.without_exact_fact(&native_guard);
        assert!(one.proves_exact(&native_guard));
        let none = one.without_exact_fact(&shared_guard);
        assert!(!none.proves_exact(&native_guard));
        assert!(!none.proves_exact(&shared_guard));
        assert!(both.proves_exact(&shared_guard));
    }
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/assumptions/observation_comparisons.rs");
}

impl PureFactContext {
    /// Read the selected guard of a conditional rewrite, retaining its exact
    /// supporting premise. General condition decision keeps its own lookup.
    pub(in crate::kernel) fn rewrite_guard_value(&self, condition: &ConditionTerm) -> Option<bool> {
        for truth in [true, false] {
            if let Some(source) = self.selected_comparison_source(condition, truth) {
                record_implicit_reasoning_provenance(self, source);
                return Some(truth);
            }
        }
        self.exact_condition_value(condition)
    }

    /// Select an exact comparison premise from indexes already maintained by
    /// admission. Shared order queries reuse the retained endpoint index;
    /// native equalities use their selected endpoint pairs. Neither enters
    /// the general observation source index. This is for an
    /// explicitly selected rewrite guard, not general condition decision:
    /// exposing these aliases globally changes unrelated automatic search.
    pub(in crate::kernel) fn selected_comparison_source(
        &self,
        condition: &ConditionTerm,
        truth: bool,
    ) -> Option<&Proposition> {
        use crate::kernel::machine_integer::comparison::structural_native_comparison_view;
        let order = matches!(
            condition,
            ConditionTerm::IntegerLessThan(..)
                | ConditionTerm::IntegerLessEqual(..)
                | ConditionTerm::IntegerGreaterThan(..)
                | ConditionTerm::IntegerGreaterEqual(..)
        );
        let exact = |view: &NativeComparisonView<'_>| {
            let index = match view.format {
                MachineIntegerType::Int32 => &self.signed_order_bounds,
                MachineIntegerType::UInt32 => &self.uint32_order_bounds,
                MachineIntegerType::Int64 => &self.int64_signed_order_bounds,
                MachineIntegerType::UInt64 => &self.uint64_order_bounds,
                _ => return None,
            };
            let [left, right] = view
                .operands
                .each_ref()
                .map(|operand| operand.operand_view());
            index.exact_source(left, right, view.relation == Relation::Less)
        };
        // Retain the written carrier's source before a value reading through
        // casts can select a different, derived bound.
        if order
            && let Some(view) = structural_native_comparison_view(condition, truth)
            && let Some(source) = exact(&view)
        {
            return Some(source);
        }
        self.observation_comparisons
            .source(condition, truth)
            .or_else(|| {
                if !order {
                    return self
                        .observation_comparisons
                        .selected_native_equality_source(condition, truth);
                }
                let view = native_comparison_view(condition, truth)?;
                exact(&view).or_else(|| view.widened().and_then(|view| exact(&view)))
            })
    }
}
