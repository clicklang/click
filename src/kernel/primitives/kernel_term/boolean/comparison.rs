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
        let stored_format = match (relation, format) {
            (R::Equal, T::UInt64) => T::Int64,
            (R::Equal, T::UInt128) => T::Int128,
            _ => format,
        };
        let literals = arguments.each_ref().map(Self::guard_literal);
        if let [Some(left), Some(right)] = &literals {
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
        } else if format.format().bits() == 32 {
            for (argument, literal) in arguments.iter_mut().zip(literals) {
                if let Some(value) = literal {
                    *argument = value.guard_operand(format);
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
                        && let Some(pointer) = address.integer_address()
                    {
                        return Self::address_equal([
                            pointer.clone(),
                            Address::null().into_shared(),
                        ]);
                    }
                }
                for (word, zero) in [(views[0], &arguments[1]), (views[1], &arguments[0])] {
                    if zero.guard_literal().and_then(|literal| literal.signed64()) != Some(0) {
                        continue;
                    }
                    if let Some((pointer, alignment)) =
                        word.pointer_alignment(MachineOperandView::integer_address)
                    {
                        let pointer = Self::numeric_address_term(
                            T::UInt64,
                            &pointer.export().expect("written alignment address"),
                            AddressObjectClass::NONE,
                        );
                        let literal = |result: T, bits: u64| {
                            KernelMachineLiteral::UInt64(bits).guard_operand(result)
                        };
                        let masked = Self::machine_binary_shared_as(
                            T::Int64,
                            T::UInt64,
                            MachineBinaryOp::BitwiseAnd,
                            [pointer, literal(T::UInt64, alignment - 1)],
                        );
                        return Self::boolean_comparison_raw(
                            T::Int64,
                            R::Equal,
                            [masked, literal(T::Int64, 0)],
                        );
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
    fn alignment_mask_borrows_its_address_in_either_order() {
        let _session = crate::kernel::VerificationSession::enter();
        let address = Address::symbolic(Variable(971_104)).into_shared();
        let format = MachineIntegerType::UInt64;
        let numeric = KernelTerm::shared_pointer_address_observation(
            format,
            address.clone(),
            AddressObjectClass::NONE,
        );
        let mask = KernelMachineLiteral::UInt64(7).guard_operand(format);
        for args in [[numeric.clone(), mask.clone()], [mask, numeric.clone()]] {
            let masked =
                KernelTerm::machine_binary_shared(format, MachineBinaryOp::BitwiseAnd, args);
            let (pointer, alignment) = MachineOperandView::Shared(&masked)
                .pointer_alignment(MachineOperandView::integer_address)
                .unwrap();
            assert!(pointer.same_handle(&address));
            assert_eq!(alignment, 8);
            assert!(numeric.0.machine_leaf.0.get().is_none());
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
                        if expected.as_pointer_alignment().is_some() {
                            assert_eq!(result, import.condition(&expected));
                        }
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
