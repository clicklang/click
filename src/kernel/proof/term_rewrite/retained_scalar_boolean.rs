//! Scalar predicate reconstruction preserves the native raw/checking boundary.
use super::*;

impl TermRewrite<'_> {
    pub(super) fn shared_boolean_scalar_leaf(&mut self, root: &KernelTerm) -> Option<KernelTerm> {
        if let KernelTermNode::BoolLiteral(_) | KernelTermNode::Variable(_) = root.node() {
            let native = match root.node() {
                KernelTermNode::BoolLiteral(value) => ConditionTerm::Constant(*value),
                KernelTermNode::Variable(variable) => ConditionTerm::Variable(*variable),
                _ => unreachable!(),
            };
            let result = self.condition(&native);
            if self.checked_work_exhausted() {
                return None;
            }
            if result == native {
                return Some(root.clone());
            }
            // Native variable replacement is simultaneous: import this already
            // produced value once, without rewriting the replacement's children.
            if !scalar_boolean_profile(&result) {
                return None;
            }
            return Some(KernelTermImport::for_exact_field_inputs().condition(&result));
        }
        if self.condition_exact.is_some()
            || self.conditions.is_some()
            || self.cited_conditions.is_some()
            || self.collected_conditions.is_some()
            || self.equality_graph.is_some()
            || self.comparison_reads.is_some()
        {
            // Selected native predicate lookup/evidence policies are integrated
            // separately; a common predicate is not exported to perform them.
            return None;
        }
        self.visit();
        if self.checked_work_exhausted() {
            return None;
        }
        match root.node() {
            KernelTermNode::BoolCompare {
                format,
                relation,
                arguments,
            } => {
                let mut arguments = [
                    self.shared_machine_operand(&arguments[0])?,
                    self.shared_machine_operand(&arguments[1])?,
                ];
                // rebuild_machine_comparison reads UInt32 literal operands as
                // words; it does not normalize a nested arithmetic prefix.
                if matches!(
                    format,
                    MachineIntegerType::Int32 | MachineIntegerType::UInt32
                ) {
                    for operand in &mut arguments {
                        if let Some(value) = MachineOperandView::Shared(operand).literal() {
                            if matches!(
                                value,
                                MachineTerm::Constant {
                                    format: MachineIntegerType::UInt32,
                                    ..
                                }
                            ) {
                                *operand = KernelTermImport::for_exact_field_inputs()
                                    .machine(*format, &value.into_word32());
                            }
                        }
                    }
                }
                if *format == MachineIntegerType::Int64 && *relation == CompareRelation::Equal {
                    let views = arguments.each_ref().map(MachineOperandView::Shared);
                    if [(views[0], views[1]), (views[1], views[0])].into_iter().any(|(address, zero)| {
                        zero.uint64_constant() == Some(0)
                            && matches!(address, MachineOperandView::Shared(root)
                                if matches!(root.machine_conversion_leaf(), Some(MachineTerm::IntegerAddress(..))))
                    }) {
                        self.changed = true;
                        return Some(KernelTerm::boolean_comparison(*format, *relation, arguments));
                    }
                }
                Some(KernelTerm::boolean_comparison_raw(
                    *format, *relation, arguments,
                ))
            }
            KernelTermNode::BoolOverflow {
                format,
                operation,
                arguments,
            } => Some(KernelTerm::boolean_overflow_raw(
                *format,
                *operation,
                [
                    self.shared_machine_operand(&arguments[0])?,
                    self.shared_machine_operand(&arguments[1])?,
                ],
            )),
            KernelTermNode::IntegerCompare {
                operator,
                arguments,
            } => Some(
                KernelTerm::integer_comparison(
                    *operator,
                    [
                        self.shared_integer_operand(&arguments[0])?,
                        self.shared_integer_operand(&arguments[1])?,
                    ],
                )
                .ok()?,
            ),
            _ => None,
        }
    }
}

fn scalar_boolean_profile(root: &ConditionTerm) -> bool {
    let mut pending = vec![root];
    while let Some(value) = pending.pop() {
        match value {
            ConditionTerm::Constant(_)
            | ConditionTerm::Variable(_)
            | ConditionTerm::Compare { .. }
            | ConditionTerm::Overflows { .. }
            | ConditionTerm::IntegerLessThan(..)
            | ConditionTerm::IntegerLessEqual(..)
            | ConditionTerm::IntegerGreaterThan(..)
            | ConditionTerm::IntegerGreaterEqual(..)
            | ConditionTerm::IntegerEqual(..)
            | ConditionTerm::IntegerNotEqual(..) => {}
            ConditionTerm::BoolEqual(left, right) => {
                pending.extend([left.as_ref(), right.as_ref()])
            }
            ConditionTerm::BoolIf {
                condition,
                then_condition,
                else_condition,
            } => pending.extend([
                condition.as_ref(),
                then_condition.as_ref(),
                else_condition.as_ref(),
            ]),
            _ => return false,
        }
    }
    true
}

#[cfg(test)]
mod tests {
    use super::*;

    fn assert_output(
        root: &KernelTerm,
        result: &KernelTerm,
        expected: &ConditionTerm,
        exports: usize,
    ) {
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        assert!(!root.has_cached_native_argument());
        assert!(!result.has_cached_native_argument());
        let actual = KernelTermExport::condition(result).unwrap();
        assert_eq!(&actual, expected);
        assert_eq!(format!("{actual:?}"), format!("{expected:?}"));
        let expected_root = KernelTermImport::for_exact_field_inputs().condition(expected);
        assert_eq!(
            result.condition_storage_key(),
            expected_root.condition_storage_key()
        );
    }

    #[test]
    fn scalar_machine_predicates_preserve_native_raw_formats_scopes_and_warm_queries() {
        let _session = VerificationSession::enter();
        let from = Variable(998100);
        let source = MachineTerm::Variable(from);
        for format in crate::kernel::machine_integer::FORMATS {
            let literal = |n| {
                MachineTerm::machine_constant(
                    MachineIntegerConstant::from_signed(format.format(), n).unwrap(),
                )
            };
            let mut inputs = Vec::new();
            for relation in [
                CompareRelation::Equal,
                CompareRelation::LessThan,
                CompareRelation::LessEqual,
                CompareRelation::GreaterThan,
                CompareRelation::GreaterEqual,
            ] {
                inputs.push(ConditionTerm::Compare {
                    format,
                    relation,
                    left: Box::new(source.clone()),
                    right: Box::new(literal(1)),
                });
            }
            for op in [
                OverflowOperation::Add,
                OverflowOperation::Subtract,
                OverflowOperation::Multiply,
            ] {
                inputs.push(ConditionTerm::Overflows {
                    format,
                    op,
                    left: Box::new(source.clone()),
                    right: Box::new(literal(0)),
                });
            }
            for input in inputs {
                let root = KernelTermImport::for_exact_field_inputs().condition(&input);
                for replacement in [
                    literal(0),
                    literal(1),
                    MachineTerm::Variable(Variable(998101)),
                ] {
                    let mut baseline = TermRewrite::for_bits_checked(&source, &replacement);
                    let mut rewrite = TermRewrite::for_bits_checked(&source, &replacement);
                    for scoped in [false, true, false, false] {
                        let a = scoped.then(|| {
                            baseline.push_program_substitution_scope(from, Variable(998102))
                        });
                        let b = scoped.then(|| {
                            rewrite.push_program_substitution_scope(from, Variable(998102))
                        });
                        let expected = baseline.condition(&input);
                        let exports = KernelTermExport::machine_export_count();
                        let actual = rewrite.shared_boolean_operand(&root).unwrap();
                        assert_eq!(rewrite.changed, baseline.changed);
                        assert_eq!(rewrite.refusal(), baseline.refusal());
                        assert_output(&root, &actual, &expected, exports);
                        if let Some(scope) = b {
                            rewrite.pop_program_substitution_scope(scope);
                        }
                        if let Some(scope) = a {
                            baseline.pop_program_substitution_scope(scope);
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn scalar_integer_predicates_preserve_native_raw_operators_and_active_scope() {
        let _session = VerificationSession::enter();
        let from = Variable(998120);
        let left: SharedIntegerTerm = IntegerTerm::Add(
            IntegerTerm::Variable(from).into(),
            IntegerTerm::constant_i64(1).into(),
        )
        .into();
        for operator in [
            IntegerComparisonOperator::LessThan,
            IntegerComparisonOperator::LessEqual,
            IntegerComparisonOperator::GreaterThan,
            IntegerComparisonOperator::GreaterEqual,
            IntegerComparisonOperator::Equal,
            IntegerComparisonOperator::NotEqual,
        ] {
            let right = IntegerTerm::constant_i64(3).into();
            let input = match operator {
                IntegerComparisonOperator::LessThan => {
                    ConditionTerm::IntegerLessThan(left.clone(), right)
                }
                IntegerComparisonOperator::LessEqual => {
                    ConditionTerm::IntegerLessEqual(left.clone(), right)
                }
                IntegerComparisonOperator::GreaterThan => {
                    ConditionTerm::IntegerGreaterThan(left.clone(), right)
                }
                IntegerComparisonOperator::GreaterEqual => {
                    ConditionTerm::IntegerGreaterEqual(left.clone(), right)
                }
                IntegerComparisonOperator::Equal => {
                    ConditionTerm::IntegerEqual(left.clone(), right)
                }
                IntegerComparisonOperator::NotEqual => {
                    ConditionTerm::IntegerNotEqual(left.clone(), right)
                }
            };
            let root = KernelTermImport::for_exact_field_inputs().condition(&input);
            for replacement in [
                IntegerTerm::constant_i64(2),
                IntegerTerm::Variable(Variable(998121)),
            ] {
                let renamings = BTreeMap::new();
                let mut baseline =
                    TermRewrite::for_integer_variables(from, &replacement, false, &renamings);
                let mut rewrite =
                    TermRewrite::for_integer_variables(from, &replacement, false, &renamings);
                for scoped in [false, true, false] {
                    let a = scoped.then(|| {
                        baseline.push_integer_substitution_scope(from, Variable(998122), false)
                    });
                    let b = scoped.then(|| {
                        rewrite.push_integer_substitution_scope(from, Variable(998122), false)
                    });
                    let expected = baseline.condition(&input);
                    let exports = KernelTermExport::machine_export_count();
                    let actual = rewrite.shared_boolean_operand(&root).unwrap();
                    assert_eq!(rewrite.changed, baseline.changed);
                    assert_eq!(rewrite.refusal(), baseline.refusal());
                    assert_output(&root, &actual, &expected, exports);
                    if let Some(scope) = b {
                        rewrite.pop_integer_substitution_scope(scope);
                    }
                    if let Some(scope) = a {
                        baseline.pop_integer_substitution_scope(scope);
                    }
                }
            }
        }
    }

    #[test]
    fn raw_predicate_and_conditional_guard_warm_queries_do_not_poison_each_other() {
        let _session = VerificationSession::enter();
        let from = Variable(998140);
        for format in crate::kernel::machine_integer::FORMATS {
            let zero = MachineTerm::machine_constant(
                MachineIntegerConstant::from_signed(format.format(), 0).unwrap(),
            );
            let predicate = ConditionTerm::Compare {
                format,
                relation: CompareRelation::Equal,
                left: Box::new(MachineTerm::Variable(from)),
                right: Box::new(zero.clone()),
            };
            let conditional = IntegerTerm::If {
                condition: Box::new(predicate.clone()),
                then_term: IntegerTerm::constant_i64(3).into(),
                else_term: IntegerTerm::constant_i64(4).into(),
            };
            let predicate_root = KernelTermImport::for_exact_field_inputs().condition(&predicate);
            let conditional_root =
                KernelTermImport::for_exact_field_inputs().integer(&conditional.clone().into());
            let source = MachineTerm::Variable(from);
            for raw_first in [false, true] {
                let mut baseline = TermRewrite::for_bits_checked(&source, &zero);
                let mut rewrite = TermRewrite::for_bits_checked(&source, &zero);
                for raw in if raw_first {
                    [true, false, true]
                } else {
                    [false, true, false]
                } {
                    let exports = KernelTermExport::machine_export_count();
                    if raw {
                        let expected = baseline.condition(&predicate);
                        let actual = rewrite.shared_boolean_operand(&predicate_root).unwrap();
                        assert_output(&predicate_root, &actual, &expected, exports);
                    } else {
                        let expected = baseline.integer(&conditional);
                        let actual = rewrite.shared_integer_operand(&conditional_root).unwrap();
                        assert_eq!(KernelTermExport::machine_export_count(), exports);
                        assert!(!conditional_root.has_cached_native_argument());
                        assert_eq!(
                            KernelTermExport::default()
                                .integer(&actual)
                                .unwrap()
                                .as_ref(),
                            &expected
                        );
                    }
                    assert_eq!(rewrite.changed, baseline.changed);
                    assert_eq!(rewrite.refusal(), baseline.refusal());
                }
            }
        }
    }

    #[test]
    fn scalar_guard_selection_preserves_native_literal_work_and_nonfolding() {
        let _session = VerificationSession::enter();
        let from = Variable(998160);
        let word = MachineTerm::Variable(from);
        let integer_from = Variable(998161);
        let large = IntegerTerm::Constant(num_bigint::BigInt::from(1) << 1024usize);
        let predicates = [
            (
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::Equal,
                    left: Box::new(word.clone()),
                    right: Box::new(MachineTerm::constant(0)),
                },
                true,
            ),
            (
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int64,
                    relation: CompareRelation::Equal,
                    left: Box::new(word.clone()),
                    right: Box::new(MachineTerm::int64_constant(0)),
                },
                false,
            ),
            (
                ConditionTerm::Overflows {
                    format: MachineIntegerType::Int32,
                    op: OverflowOperation::Add,
                    left: Box::new(word),
                    right: Box::new(MachineTerm::constant(0)),
                },
                false,
            ),
            (
                ConditionTerm::IntegerEqual(
                    IntegerTerm::Variable(integer_from).into(),
                    IntegerTerm::constant_i64(0).into(),
                ),
                false,
            ),
        ];
        for (predicate, folds) in predicates {
            let input = IntegerTerm::If {
                condition: Box::new(predicate.clone()),
                then_term: IntegerTerm::constant_i64(3).into(),
                else_term: large.clone().into(),
            };
            let root = KernelTermImport::for_exact_field_inputs().integer(&input.clone().into());
            let replacement = if matches!(
                predicate,
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int64,
                    ..
                }
            ) {
                MachineTerm::int64_constant(0)
            } else {
                MachineTerm::constant(0)
            };
            let program =
                BTreeMap::from([(from, TypedProgramValueReplacement::Bitvector(replacement))]);
            let integers = BTreeMap::from([(integer_from, IntegerTerm::constant_i64(0))]);
            let algebraic = BTreeMap::new();
            let (expected, native_refusal) =
                crate::instrumentation::with_run_work_limit(128, || {
                    let mut rewrite =
                        TermRewrite::for_typed_variables(&program, &integers, &algebraic);
                    let result = rewrite.integer(&input);
                    (result, rewrite.refusal())
                });
            let exports = KernelTermExport::machine_export_count();
            let (result, refusal) = crate::instrumentation::with_run_work_limit(128, || {
                let mut rewrite = TermRewrite::for_typed_variables(&program, &integers, &algebraic);
                let result = rewrite.shared_integer_operand(&root);
                (result, rewrite.refusal())
            });
            assert_eq!(refusal, native_refusal);
            assert_eq!(refusal, (!folds).then_some(RewriteRefusal::WorkExhausted));
            assert_eq!(KernelTermExport::machine_export_count(), exports);
            assert!(!root.has_cached_native_argument());
            if folds {
                assert_eq!(
                    KernelTermExport::default()
                        .integer(&result.unwrap())
                        .unwrap()
                        .as_ref(),
                    &expected
                );
            } else {
                assert!(result.is_none());
            }
        }
    }

    #[test]
    fn scalar_predicates_keep_contextual_lookup_and_other_leaf_boundaries_explicit() {
        let _session = VerificationSession::enter();
        let input = ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::Equal,
            left: Box::new(MachineTerm::Variable(Variable(998180))),
            right: Box::new(MachineTerm::constant(0)),
        };
        let root = KernelTermImport::for_exact_field_inputs().condition(&input);
        let facts = HashMap::from([(input.clone(), true)]);
        let mut rewrite = TermRewrite::for_conditions(&facts);
        assert!(rewrite.shared_boolean_operand(&root).is_none());
        assert!(rewrite.refusal().is_none());
        for unsupported in [
            ConditionTerm::BoolLoad(
                ProgramPoint::at(&intern_memory(SymbolicMemory::new())),
                Box::new(Address::symbolic(Variable(998181))),
            ),
            ConditionTerm::bool_application("unsupported_scalar_application", Vec::new()),
            ConditionTerm::AddressEqual(
                Box::new(Address::symbolic(Variable(998182))),
                Box::new(Address::null()),
            ),
        ] {
            let root = KernelTermImport::for_exact_field_inputs().condition(&unsupported);
            let mut rewrite = TermRewrite::empty();
            assert!(rewrite.shared_boolean_operand(&root).is_none());
            assert!(rewrite.refusal().is_none());
            assert!(!root.has_cached_native_argument());
            let atom = KernelTerm::variable(KernelType::Bool, Variable(998183));
            let program = BTreeMap::from([(
                Variable(998183),
                TypedProgramValueReplacement::Bitvector(MachineTerm::bool_cast(
                    MachineIntegerType::UInt8,
                    unsupported,
                )),
            )]);
            let integer = BTreeMap::new();
            let algebraic = BTreeMap::new();
            let mut rewrite = TermRewrite::for_typed_variables(&program, &integer, &algebraic);
            assert!(rewrite.shared_boolean_operand(&atom).is_none());
            assert!(rewrite.refusal().is_none());
            assert!(!atom.has_cached_native_argument());
        }
    }
}

#[cfg(test)]
mod scaling_tests {
    include!("../../../scaling_tests/kernel/proof/term_rewrite/retained_scalar_boolean.rs");
}
