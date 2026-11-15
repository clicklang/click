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
        mut format: MachineIntegerType,
        relation: CompareRelation,
        mut arguments: [Self; 2],
    ) -> Self {
        use CompareRelation as R;
        use MachineIntegerType as T;
        let boolean = |value| Self::intern(KernelType::Bool, KernelTermNode::BoolLiteral(value));
        let native = |value: ConditionTerm| KernelTermImport::default().condition(&value);
        let views = arguments.each_ref().map(MachineOperandView::Shared);
        if let [Some(left), Some(right)] = views.map(|view| view.literal()) {
            return native(ConditionTerm::machine_compare(
                format, relation, left, right,
            ));
        }
        if format.format().bits() == 32 {
            for argument in &mut arguments {
                if let Some(value) = MachineOperandView::Shared(argument).literal() {
                    *argument = KernelTermImport::default().machine(format, &value.into_word32());
                }
            }
        }
        let views = arguments.each_ref().map(MachineOperandView::Shared);
        if format == T::UInt32 && relation != R::Equal {
            if let Some(bound) = views[1].word32_constant() {
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
        }
        if format == T::Int64 && relation != R::Equal {
            if let Some(value) = crate::kernel::primitives::int64_signed_order_by_width_views(
                views[0],
                views[1],
                |a, b| match relation {
                    R::LessThan => a < b,
                    R::LessEqual => a <= b,
                    R::GreaterThan => a > b,
                    R::GreaterEqual => a >= b,
                    R::Equal => unreachable!(),
                },
            ) {
                return boolean(value);
            }
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
                        && let Some(MachineTerm::PointerAddress(pointer, _)) =
                            root.machine_conversion_leaf()
                    {
                        return native(ConditionTerm::pointer_equal(
                            pointer.as_ref().clone(),
                            Pointer::null(),
                        ));
                    }
                }
                // Reuse the existing bounded alignment classifier. Observing
                // the selected operand retains it; it does not export it.
                for (word, zero) in [(views[0], views[1]), (views[1], views[0])] {
                    if zero.literal().and_then(|v| v.bitvector64_as_const()) != Some(0) {
                        continue;
                    }
                    let observed = ConditionTerm::IntegerEqual(
                        IntegerTerm::Machine(word.retain(format)).into(),
                        IntegerTerm::constant_i64(0).into(),
                    );
                    if let Some((pointer, alignment)) = observed.as_pointer_alignment() {
                        return native(ConditionTerm::Compare {
                            format: T::Int64,
                            relation,
                            left: Box::new(MachineTerm::Binary {
                                format: T::UInt64,
                                op: MachineBinaryOp::BitwiseAnd,
                                left: Box::new(MachineTerm::PointerAddress(
                                    Box::new(pointer.clone()),
                                    crate::kernel::AddressObjectClass::NONE,
                                )),
                                right: Box::new(MachineTerm::uint64_constant(alignment - 1)),
                            }),
                            right: Box::new(MachineTerm::uint64_constant(0)),
                        });
                    }
                }
            }
        }
        if relation == R::Equal {
            format = match format {
                T::UInt64 => T::Int64,
                T::UInt128 => T::Int128,
                _ => format,
            };
        }
        Self::boolean_comparison_raw(format, relation, arguments)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn retained_comparison_constructors_match_native_reductions() {
        let _session = crate::kernel::VerificationSession::enter();
        for format in crate::kernel::machine_integer::FORMATS {
            let variable = MachineTerm::Variable(Variable(971_100));
            let constant = |value| {
                MachineTerm::machine_constant(
                    MachineIntegerConstant::from_signed(format.format(), value).unwrap(),
                )
            };
            let values = [
                variable.clone(),
                constant(0),
                constant(1),
                MachineTerm::Binary {
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
                        let expected = ConditionTerm::machine_compare(
                            format,
                            relation,
                            left.clone(),
                            right.clone(),
                        );
                        let mut import = KernelTermImport::default();
                        let arguments =
                            [import.machine(format, left), import.machine(format, right)];
                        let actual = KernelTerm::boolean_comparison(format, relation, arguments);
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
        let address = MachineTerm::PointerAddress(
            Box::new(Pointer::symbolic(Variable(971_103))),
            crate::kernel::AddressObjectClass::NONE,
        );
        let values = [
            address.clone(),
            MachineTerm::uint64_constant(0),
            MachineTerm::uint64_constant(u64::MAX),
            MachineTerm::Binary {
                format: MachineIntegerType::UInt64,
                op: MachineBinaryOp::BitwiseAnd,
                left: Box::new(address),
                right: Box::new(MachineTerm::uint64_constant(7)),
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
                        let expected = ConditionTerm::machine_compare(
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
            let zero = MachineTerm::machine_constant(
                MachineIntegerConstant::from_signed(format.format(), 0).unwrap(),
            );
            let one = MachineTerm::machine_constant(
                MachineIntegerConstant::from_signed(format.format(), 1).unwrap(),
            );
            let term = if format.format().bits() == 128 {
                MachineTerm::Variable(variable)
            } else {
                MachineTerm::Binary {
                    format,
                    op: MachineBinaryOp::Add,
                    left: Box::new(MachineTerm::Variable(variable)),
                    right: Box::new(zero.clone()),
                }
            };
            for relation in [
                CompareRelation::Equal,
                CompareRelation::LessThan,
                CompareRelation::GreaterEqual,
            ] {
                let source = ConditionTerm::Compare {
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
