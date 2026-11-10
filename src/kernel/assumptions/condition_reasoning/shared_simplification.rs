//! Checking-only simplification of retained machine operands. No lowering
//! path uses these fact-dependent readings.
use super::*;
use crate::kernel::machine_integer::comparison::condition_for_operand_views;
use crate::kernel::{
    KernelTerm, KernelTermNode, MachineOperandView as V, SharedMachineIntegerTerm as S,
};

impl PureFactContext {
    /// The native simplifier's rules on a shared DAG. A query memo ensures that
    /// common children are inspected once under this fixed fact context.
    pub(in crate::kernel) fn simplify_machine_operand_under_assumptions(
        &self,
        operand: V<'_>,
        format: MachineIntegerType,
    ) -> S {
        fn walk(
            facts: &PureFactContext,
            operand: V<'_>,
            format: MachineIntegerType,
            memo: &mut BTreeMap<(u64, MachineIntegerType), S>,
        ) -> S {
            let V::Shared(root) = operand else {
                let V::Legacy(term) = operand else {
                    unreachable!()
                };
                return S::intern(format, facts.simplify_bitvector_under_assumptions(term));
            };
            let key = (root.id(), format);
            if let Some(value) = memo.get(&key) {
                return value.clone();
            }
            crate::instrumentation::record_deterministic_work(1);
            let retain = |root: KernelTerm| V::Shared(&root).retain(format);
            let node =
                |value: &S| KernelTerm::retained_machine_operand(value.ty(), value.operand_view());
            let result =
                if let Some(bits) = facts.equality_graph.direct_scalar_constant_view(operand) {
                    S::intern(format, MachineTerm::constant(bits))
                } else if let Some(native) = root.machine_conversion_leaf() {
                    S::intern(format, facts.simplify_bitvector_under_assumptions(native))
                } else if let Some(carrier) = facts.narrowed_cast_carrier_view(operand) {
                    walk(facts, carrier.operand_view(), format, memo)
                } else {
                    match root.node() {
                        KernelTermNode::MachineBinary {
                            format: op_format,
                            operator,
                            arguments: [a, b],
                        } => {
                            let a = walk(facts, V::Shared(a), *op_format, memo);
                            let b = walk(facts, V::Shared(b), *op_format, memo);
                            retain(
                            crate::kernel::proof::term_rewrite::TermRewrite::machine_binary_reading(
                                *op_format,
                                *operator,
                                node(&a),
                                node(&b),
                            ),
                        )
                        }
                        KernelTermNode::MachineUnary {
                            format: op_format,
                            operator,
                            operand: child,
                        } => {
                            let child = walk(facts, V::Shared(child), *op_format, memo);
                            if let Some(literal) = child.operand_view().literal() {
                                S::intern(
                                    format,
                                    MachineTerm::machine_unary(*op_format, *operator, literal),
                                )
                            } else {
                                retain(KernelTerm::machine_unary_shared(
                                    *op_format,
                                    *operator,
                                    node(&child),
                                ))
                            }
                        }
                        KernelTermNode::MachineCast {
                            encoding,
                            source,
                            destination,
                            operand: child,
                        } => {
                            if *encoding == MachineCastSpelling::UInt32From64
                                && let Some(bits) =
                                    facts.wide_constant_from_equalities_view(V::Shared(child))
                            {
                                S::intern(format, MachineTerm::constant(bits as u32))
                            } else {
                                let child = walk(facts, V::Shared(child), *source, memo);
                                let child = node(&child);
                                retain(if *encoding == MachineCastSpelling::Generic {
                                    child.checking_machine_cast(*source, *destination)
                                } else {
                                    child.checking_legacy_machine_conversion(*source, *destination)
                                })
                            }
                        }
                        _ => operand.retain(format),
                    }
                };
            memo.insert(key, result.clone());
            result
        }
        walk(self, operand, format, &mut BTreeMap::new())
    }

    /// The same widened-narrowing rule as `narrowed_cast_carrier`, retaining
    /// the selected carrier and expressing its existing bounds as views.
    fn narrowed_cast_carrier_view(&self, term: V<'_>) -> Option<S> {
        let (_, narrowed) = term.narrow_widening32_operand()?;
        let (MachineCastSpelling::Generic, source, destination, value) = narrowed.cast()? else {
            return None;
        };
        let bits = destination.format().bits();
        let source_bits = source.format().bits();
        if !matches!(bits, 8 | 16)
            || destination.format().contains(source.format())
            || source_bits > 64
        {
            return None;
        }
        let (lo, hi) = if destination.format().is_signed() {
            (-(1i64 << (bits - 1)), (1i64 << (bits - 1)) - 1)
        } else {
            (0, (1i64 << bits) - 1)
        };
        let source_signed = source.format().is_signed();
        let needs_lower = source_signed && -(1i128 << (source_bits - 1)) < i128::from(lo);
        let source_max = if source_signed {
            (1i128 << (source_bits - 1)) - 1
        } else {
            (1i128 << source_bits) - 1
        };
        let needs_upper = source_max > i128::from(hi);
        let original = KernelTerm::retained_machine_operand(source, value);
        let carrier = if source_bits < 32 {
            original.checking_machine_cast(source, MachineIntegerType::Int32)
        } else {
            original
        };
        let bound = |format: MachineIntegerType, relation, n: i64| {
            let literal = if format == MachineIntegerType::Int64 {
                MachineTerm::int64_constant(n)
            } else if format == MachineIntegerType::UInt64 {
                MachineTerm::uint64_constant(n as u64)
            } else {
                MachineTerm::constant(n as u32)
            };
            self.decide(&condition_for_operand_views(
                format,
                relation,
                [V::Shared(&carrier), V::Legacy(&literal)],
            )) == Some(true)
        };
        let format = if source_bits < 32 {
            MachineIntegerType::Int32
        } else {
            source
        };
        if needs_lower && !bound(format, CompareRelation::GreaterEqual, lo) {
            return None;
        }
        if needs_upper
            && !(bound(format, CompareRelation::LessEqual, hi)
                || (matches!(
                    source,
                    MachineIntegerType::UInt8 | MachineIntegerType::UInt16
                ) && bound(MachineIntegerType::UInt32, CompareRelation::LessEqual, hi)))
        {
            return None;
        }
        let carrier = if source_bits == 64 {
            carrier.checking_legacy_machine_conversion(source, MachineIntegerType::UInt32)
        } else {
            carrier
        };
        Some(V::Shared(&carrier).retain(MachineIntegerType::Int32))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::{
        KernelTermExport, MachineBinaryOp as B, MachineIntegerType as T, Variable,
    };

    #[test]
    fn shared_checking_simplification_matches_native_rules_and_sources() {
        let _session = crate::kernel::VerificationSession::enter();
        let x = MachineTerm::Variable(Variable(1017101));
        let y = MachineTerm::Variable(Variable(1017102));
        let narrow = MachineTerm::machine_integer_cast(
            T::Int8,
            T::Int32,
            MachineTerm::machine_integer_cast(T::Int32, T::Int8, x.clone()),
        );
        let cases = vec![
            MachineTerm::add(x.clone(), MachineTerm::constant(0)),
            MachineTerm::add(x.clone(), y.clone()),
            MachineTerm::multiply(
                MachineTerm::add(x.clone(), MachineTerm::constant(2)),
                y.clone(),
            ),
            MachineTerm::machine_binary(T::UInt32, B::Divide, x.clone(), y.clone()),
            MachineTerm::machine_binary(
                T::Int32,
                B::ShiftLeft,
                x.clone(),
                MachineTerm::constant(1),
            ),
            MachineTerm::machine_unary(
                T::Int32,
                crate::kernel::MachineUnaryOp::BitwiseNot,
                x.clone(),
            ),
            narrow,
        ];
        let empty = PureFactContext::new();
        let exact = empty
            .clone()
            .assume_condition(
                ConditionTerm::equal(x.clone(), MachineTerm::constant(5)),
                true,
            )
            .assume_condition(
                ConditionTerm::equal(y.clone(), MachineTerm::constant(3)),
                true,
            );
        let bounded = empty
            .clone()
            .assume_condition(
                ConditionTerm::signed_greater_equal(
                    x.clone(),
                    MachineTerm::constant((-128i32) as u32),
                ),
                true,
            )
            .assume_condition(
                ConditionTerm::signed_less_equal(x, MachineTerm::constant(127)),
                true,
            );
        let compound = cases[1].clone();
        let compound_fact = ConditionTerm::equal(compound, MachineTerm::constant(9));
        let compound_context = empty.clone().assume_condition(compound_fact.clone(), true);
        let withdrawn =
            compound_context.without_exact_fact(&Proposition::ConditionIs(compound_fact, true));
        for facts in [empty, exact, bounded, compound_context, withdrawn] {
            for term in &cases {
                let expected = facts.simplify_bitvector_under_assumptions(term);
                let input = S::index(T::Int32, term.clone());
                let exports = KernelTermExport::machine_export_count();
                let actual = facts
                    .simplify_machine_operand_under_assumptions(input.operand_view(), T::Int32);
                assert_eq!(KernelTermExport::machine_export_count(), exports);
                assert_eq!(actual.structural_value(), &expected, "{term:?}");
            }
        }
    }

    #[cfg(test)]
    mod scaling_tests {
        use super::*;
        include!(
            "../../../scaling_tests/kernel/assumptions/condition_reasoning/shared_simplification.rs"
        );
    }
}
