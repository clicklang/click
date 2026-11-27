//! Reconstruct the existing native comparison constructors over retained words.
use super::*;

impl KernelTerm {
    pub(crate) fn boolean_comparison_raw(
        format: MachineIntegerType,
        relation: CompareRelation,
        arguments: [Self; 2],
    ) -> Self {
        Self::intern(
            KernelType::Bool,
            KernelTermNode::BoolCompare {
                format,
                relation,
                arguments,
            },
        )
    }

    pub(crate) fn boolean_comparison(
        format: MachineIntegerType,
        relation: CompareRelation,
        mut arguments: [Self; 2],
    ) -> Self {
        use CompareRelation as R;
        use MachineIntegerType as T;
        let boolean = |value| Self::intern(KernelType::Bool, KernelTermNode::BoolLiteral(value));
        let native = |value: OldConditionTerm| KernelTermImport::default().condition(&value);
        let stored_format = match (relation, format) {
            (R::Equal, T::UInt64) => T::Int64,
            (R::Equal, T::UInt128) => T::Int128,
            _ => format,
        };
        if let [
            KernelTermNode::MachineLiteral(left),
            KernelTermNode::MachineLiteral(right),
        ] = arguments.each_ref().map(Self::node)
        {
            if let (Some(a), Some(b)) = (left.constant_at(format), right.constant_at(format)) {
                return Self::boolean_literal(a.compare(relation, b));
            }
            // Equality reads any pair of 64-bit patterns at either signedness.
            if relation == R::Equal
                && format.format().bits() == 64
                && let (Some(a), Some(b)) = (left.signed64(), right.signed64())
            {
                return Self::boolean_literal(a == b);
            }
            // Keep the written carriers when a typed read fails. The raw
            // comparison observes both operands at its stored format.
            arguments = [
                left.guard_operand(stored_format),
                right.guard_operand(stored_format),
            ];
        } else if let [Some(left), Some(right)] = arguments
            .each_ref()
            .map(|term| MachineOperandView::Shared(term).literal())
        {
            return native(OldConditionTerm::machine_compare(
                format, relation, left, right,
            ));
        } else if format.format().bits() == 32 {
            for argument in &mut arguments {
                if let KernelTermNode::MachineLiteral(value) = argument.node() {
                    *argument = value.guard_operand(format);
                } else if let Some(value) = MachineOperandView::Shared(argument).literal() {
                    *argument = KernelTermImport::default().machine(format, &value.into_word32());
                }
            }
        }
        let views = arguments.each_ref().map(MachineOperandView::Shared);
        if format == T::UInt32
            && relation != R::Equal
            && let Some(bound) = views[1].word32_constant()
        {
            let upper = views[0].unsigned32_upper_bound();
            let folded = match relation {
                R::LessThan if upper < bound => Some(true),
                R::LessEqual if upper <= bound => Some(true),
                R::GreaterThan if upper <= bound => Some(false),
                R::GreaterEqual if upper < bound => Some(false),
                _ => None,
            };
            if let Some(value) = folded {
                return boolean(value);
            }
        }
        if format == T::Int64
            && relation != R::Equal
            && let Some(value) = crate::kernel::primitives::int64_signed_order_by_width_views(
                views[0],
                views[1],
                |a, b| relation.holds(a, b),
            )
        {
            return boolean(value);
        }
        if format == T::UInt64 && relation != R::Equal {
            let [left, right] = views.map(|view| view.uint64_constant());
            if relation == R::LessThan
                && let Some(bound) = right
                && let Some((T::UInt64, MachineBinaryOp::BitwiseAnd, operands)) = views[0].binary()
                && let Some(mask) = operands[0]
                    .uint64_constant()
                    .or_else(|| operands[1].uint64_constant())
                && mask < bound
            {
                return boolean(true);
            }
            let folded = match relation {
                R::LessThan if right == Some(0) || left == Some(u64::MAX) => Some(false),
                R::LessEqual if left == Some(0) || right == Some(u64::MAX) => Some(true),
                R::GreaterThan if left == Some(0) || right == Some(u64::MAX) => Some(false),
                R::GreaterEqual if right == Some(0) || left == Some(u64::MAX) => Some(true),
                _ => None,
            };
            if let Some(value) = folded {
                return boolean(value);
            }
        }
        if relation == R::Equal && format.format().bits() >= 64 {
            if crate::kernel::machine_operand_syntax_cmp(views[0], views[1]).is_eq() {
                return boolean(true);
            }
            if format.format().bits() == 64 {
                for (address, other) in [(views[0], views[1]), (views[1], views[0])] {
                    if other.uint64_constant() == Some(0)
                        && let MachineOperandView::Shared(root) = address
                        && let Some(OldMachineTerm::IntegerAddress(pointer, _)) =
                            root.machine_conversion_leaf()
                    {
                        return native(OldConditionTerm::address_equal(
                            pointer.as_ref().clone(),
                            Address::null(),
                        ));
                    }
                }
                // Reuse the existing bounded alignment classifier. Observing
                // the selected operand retains it; it does not export it.
                for (word, zero) in [(views[0], views[1]), (views[1], views[0])] {
                    if zero.literal().and_then(|v| v.bitvector64_as_const()) != Some(0) {
                        continue;
                    }
                    let observed = OldConditionTerm::IntegerEqual(
                        IntegerTerm::Machine(word.retain(format)).into(),
                        IntegerTerm::constant_i64(0).into(),
                    );
                    if let Some((pointer, alignment)) = observed.as_pointer_alignment() {
                        return native(OldConditionTerm::Compare {
                            format: T::Int64,
                            relation,
                            left: Box::new(OldMachineTerm::Binary {
                                format: T::UInt64,
                                op: MachineBinaryOp::BitwiseAnd,
                                left: Box::new(OldMachineTerm::IntegerAddress(
                                    Box::new(pointer.clone()),
                                    crate::kernel::AddressObjectClass::NONE,
                                )),
                                right: Box::new(OldMachineTerm::uint64_constant(alignment - 1)),
                            }),
                            right: Box::new(OldMachineTerm::uint64_constant(0)),
                        });
                    }
                }
            }
        }
        Self::boolean_comparison_raw(stored_format, relation, arguments)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn retained_comparison_constructors_match_native_reductions() {
        let _session = crate::kernel::VerificationSession::enter();
        for format in crate::kernel::machine_integer::FORMATS {
            let variable = OldMachineTerm::Variable(Variable(971_100));
            let constant = |value| {
                OldMachineTerm::machine_constant(
                    MachineIntegerConstant::from_signed(format.format(), value).unwrap(),
                )
            };
            let values = [
                variable.clone(),
                constant(0),
                constant(1),
                OldMachineTerm::machine_constant(MachineIntegerConstant::from_term_bits(
                    format.format(),
                    format.format().mask(),
                )),
                // A differently tagged word may still be readable at this format.
                OldMachineTerm::int64_constant(-1),
                OldMachineTerm::int64_constant(i64::MIN),
                OldMachineTerm::uint32_constant(u32::MAX),
                OldMachineTerm::uint64_constant(u64::MAX),
                OldMachineTerm::Binary {
                    format,
                    op: MachineBinaryOp::BitwiseAnd,
                    left: Box::new(variable),
                    right: Box::new(constant(1)),
                },
            ];
            for relation in [
                CompareRelation::Equal,
                CompareRelation::LessThan,
                CompareRelation::LessEqual,
                CompareRelation::GreaterThan,
                CompareRelation::GreaterEqual,
            ] {
                for left in &values {
                    for right in &values {
                        let expected = OldConditionTerm::machine_compare(
                            format,
                            relation,
                            left.clone(),
                            right.clone(),
                        );
                        let mut import = KernelTermImport::default();
                        let arguments =
                            [import.machine(format, left), import.machine(format, right)];
                        let actual = KernelTerm::boolean_comparison(format, relation, arguments);
                        if matches!(left, OldMachineTerm::Constant { .. })
                            && matches!(right, OldMachineTerm::Constant { .. })
                        {
                            assert_eq!(
                                actual,
                                import.condition(&expected),
                                "{format:?} {relation:?} {left:?} {right:?}"
                            );
                        }
                        let restored = KernelTermExport::condition(&actual).unwrap();
                        assert_eq!(
                            format!("{restored:?}"),
                            format!("{expected:?}"),
                            "{format:?} {relation:?}"
                        );
                    }
                }
            }
        }
    }

    #[test]
    fn retained_comparison_constructors_preserve_address_and_mask_rules() {
        let _session = crate::kernel::VerificationSession::enter();
        let address = OldMachineTerm::IntegerAddress(
            Box::new(Address::symbolic(Variable(971_103))),
            crate::kernel::AddressObjectClass::NONE,
        );
        let values = [
            address.clone(),
            OldMachineTerm::uint64_constant(0),
            OldMachineTerm::uint64_constant(u64::MAX),
            OldMachineTerm::Binary {
                format: MachineIntegerType::UInt64,
                op: MachineBinaryOp::BitwiseAnd,
                left: Box::new(address),
                right: Box::new(OldMachineTerm::uint64_constant(7)),
            },
        ];
        for format in [MachineIntegerType::Int64, MachineIntegerType::UInt64] {
            for relation in [
                CompareRelation::Equal,
                CompareRelation::LessThan,
                CompareRelation::LessEqual,
                CompareRelation::GreaterThan,
                CompareRelation::GreaterEqual,
            ] {
                for left in &values {
                    for right in &values {
                        let expected = OldConditionTerm::machine_compare(
                            format,
                            relation,
                            left.clone(),
                            right.clone(),
                        );
                        let mut import = KernelTermImport::default();
                        let arguments =
                            [import.machine(format, left), import.machine(format, right)];
                        let result = KernelTerm::boolean_comparison(format, relation, arguments);
                        let actual = KernelTermExport::condition(&result).unwrap();
                        assert_eq!(
                            format!("{actual:?}"),
                            format!("{expected:?}"),
                            "{format:?} {relation:?}"
                        );
                    }
                }
            }
        }
    }

    #[test]
    fn retained_boolean_bit_substitution_matches_native_reductions() {
        let _session = crate::kernel::VerificationSession::enter();
        let variable = Variable(971_101);
        for format in crate::kernel::machine_integer::FORMATS {
            let zero = OldMachineTerm::machine_constant(
                MachineIntegerConstant::from_signed(format.format(), 0).unwrap(),
            );
            let one = OldMachineTerm::machine_constant(
                MachineIntegerConstant::from_signed(format.format(), 1).unwrap(),
            );
            let term = if format.format().bits() == 128 {
                OldMachineTerm::Variable(variable)
            } else {
                OldMachineTerm::Binary {
                    format,
                    op: MachineBinaryOp::Add,
                    left: Box::new(OldMachineTerm::Variable(variable)),
                    right: Box::new(zero.clone()),
                }
            };
            for relation in [
                CompareRelation::Equal,
                CompareRelation::LessThan,
                CompareRelation::GreaterEqual,
            ] {
                let source = OldConditionTerm::Compare {
                    format,
                    relation,
                    left: Box::new(term.clone()),
                    right: Box::new(one.clone()),
                };
                let root = KernelTermImport::default().condition(&source);
                let expected = crate::kernel::reasoning::substitute_bitvector_variable_in_condition(
                    &source, variable, &one,
                );
                let actual =
                    crate::kernel::reasoning::substitute_bitvector_variable_in_common_condition(
                        &root, variable, &one,
                    )
                    .unwrap();
                let actual = KernelTermExport::condition(&actual).unwrap();
                assert_eq!(
                    format!("{actual:?}"),
                    format!("{expected:?}"),
                    "{format:?} {relation:?}"
                );
            }
        }
    }
}
