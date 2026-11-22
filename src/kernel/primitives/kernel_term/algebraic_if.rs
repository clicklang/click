//! Algebraic conditionals retain their guard and branches. Raw import preserves
//! written structure; production applies the existing literal/equal-arm rules.
use super::*;

impl KernelTerm {
    pub(crate) fn algebraic_if_raw(ty: AlgebraicType, arguments: [Self; 3]) -> Self {
        Self::intern(
            KernelType::Algebraic(ty),
            KernelTermNode::AlgebraicIf { arguments },
        )
    }

    pub(crate) fn algebraic_if(arguments: [Self; 3]) -> Self {
        let [condition, then_term, else_term] = arguments;
        match BooleanOperandView::Shared(&condition).constant() {
            Some(true) => then_term,
            Some(false) => else_term,
            None if then_term.algebraic_syntax_equal(&else_term) => then_term,
            None => {
                let KernelType::Algebraic(ty) = then_term.ty() else {
                    unreachable!("algebraic branch")
                };
                Self::algebraic_if_raw(ty.clone(), [condition, then_term, else_term])
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn algebraic_conditionals_preserve_raw_structure_and_native_reductions() {
        let _session = crate::kernel::VerificationSession::enter();
        let left = KernelMatch::test_scrutinee(vec![]);
        let mut right = left.clone();
        right.node = AlgebraicTermNode::Variable(Variable(999721));
        let guard = ConditionTerm::integer_equal(
            IntegerTerm::var(Variable(999722)),
            IntegerTerm::constant_i64(0),
        );
        for (condition, right) in [
            (guard.clone(), right),
            (guard, left.clone()),
            (ConditionTerm::Constant(true), left.clone()),
        ] {
            let raw = AlgebraicTerm {
                algebraic_type: left.algebraic_type.clone(),
                node: AlgebraicTermNode::If {
                    condition: Box::new(condition.clone()),
                    then_term: Box::new(left.clone()),
                    else_term: Box::new(right.clone()),
                },
            };
            let root = KernelTermImport::default().algebraic(&raw);
            assert!(matches!(root.node(), KernelTermNode::AlgebraicIf { .. }));
            assert_eq!(KernelTermExport::default().algebraic(&root).unwrap(), raw);
            let arguments = [
                KernelTermImport::default().condition(&condition),
                KernelTermImport::default().algebraic(&left),
                KernelTermImport::default().algebraic(&right),
            ];
            let exports = KernelTermExport::algebraic_export_count();
            let produced = KernelTerm::algebraic_if(arguments);
            assert_eq!(KernelTermExport::algebraic_export_count(), exports);
            assert_eq!(
                KernelTermExport::default().algebraic(&produced).unwrap(),
                AlgebraicTerm::if_then_else(condition, left.clone(), right)
            );
        }
    }
    #[test]
    fn algebraic_conditionals_preserve_opaque_branch_observation_keys() {
        let _session = crate::kernel::VerificationSession::enter();
        let mut source = KernelMatch::test_scrutinee(vec![AlgebraicValueType::Program(
            ProgramType::Int32Pointer,
        )]);
        let variable = source.clone();
        source.node = AlgebraicTermNode::Constructor {
            variant: "Arm".into(),
            fields: vec![AlgebraicValue::Program(ProgramValue::Pointer(
                Pointer::new(
                    Address::symbolic(Variable(999728)),
                    ProgramType::Int32Pointer,
                ),
            ))],
        };
        let native = AlgebraicTerm {
            algebraic_type: source.algebraic_type.clone(),
            node: AlgebraicTermNode::If {
                condition: Box::new(ConditionTerm::Variable(Variable(999729))),
                then_term: Box::new(source),
                else_term: Box::new(variable.clone()),
            },
        };
        let root = KernelTermImport::default().algebraic(&native);
        assert_eq!(
            format!(
                "{:?}",
                KernelTermExport::default().algebraic(&root).unwrap()
            ),
            format!("{native:?}")
        );
        let condition = KernelTerm::algebraic_equal_raw([
            root,
            KernelTermImport::default().algebraic(&variable),
        ]);
        let format = MachineIntegerType::Int32;
        let native_condition = ConditionTerm::AlgebraicEqual(Box::new(native), Box::new(variable));
        let a = MachineTerm::constant(1);
        let b = MachineTerm::constant(2);
        let common = KernelTerm::machine_if_shared(
            format,
            [
                condition,
                KernelTermImport::default().machine(format, &a),
                KernelTermImport::default().machine(format, &b),
            ],
        );
        let exports = KernelTermExport::machine_export_count();
        let observed = SharedMachineIntegerTerm::observe_shared(format, common).unwrap();
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        let expected = SharedMachineIntegerTerm::intern(
            format,
            MachineTerm::If {
                condition: Box::new(native_condition),
                then_term: Box::new(a),
                else_term: Box::new(b),
            },
        );
        assert_eq!(observed, expected);
    }
    #[test]
    fn algebraic_conditional_call_carriers_keep_native_identity() {
        let _session = crate::kernel::VerificationSession::enter();
        let ty = KernelMatch::test_scrutinee(vec![]).algebraic_type;
        let format = MachineIntegerType::Int32;
        let argument = SharedMachineIntegerTerm::intern(
            format,
            MachineTerm::ClickFunctionApplication {
                name: "word_result".into(),
                arguments: vec![],
            },
        );
        let source = AlgebraicTerm {
            algebraic_type: ty,
            node: AlgebraicTermNode::PureFunctionApplication {
                name: "wrap_word".into(),
                arguments: vec![PureFunctionArgument::SharedMachine(argument)],
            },
        };
        let root = KernelTermImport::default().algebraic(&source);
        assert_eq!(
            KernelTermExport::default().algebraic(&root).unwrap(),
            source,
            "a retained numeric call keeps its original carrier identity"
        );
        for exact in [false, true] {
            let sources = [false, true].map(|qualified| {
                let pointer = Pointer::new(
                    Address::symbolic(Variable(999730)),
                    ProgramType::Int32Pointer,
                );
                let application = SharedPureApplication::intern(
                    "carrier_pointer".into(),
                    vec![PureFunctionArgument::Value(ProgramValue::Pointer(
                        pointer.with_declared_object_class(qualified.then(|| {
                            crate::kernel::effective_type::CAccessClass::Scalar(
                                crate::kernel::effective_type::CScalarClass::Int,
                            )
                        })),
                    ))],
                );
                let carrier = if exact {
                    SharedMachineIntegerTerm::from_shared(
                        format,
                        KernelTermImport::default().machine_call(format, &application),
                    )
                    .unwrap()
                } else {
                    SharedMachineIntegerTerm::intern(format, application.native_call().clone())
                };
                AlgebraicTerm {
                    algebraic_type: source.algebraic_type.clone(),
                    node: AlgebraicTermNode::PureFunctionApplication {
                        name: "wrap_word".into(),
                        arguments: vec![PureFunctionArgument::SharedMachine(carrier)],
                    },
                }
            });
            assert_eq!(sources[0] == sources[1], !exact);
            let roots = sources
                .each_ref()
                .map(|source| KernelTermImport::default().algebraic(source));
            assert_eq!(roots[0].algebraic_syntax_equal(&roots[1]), !exact);
            for (root, source) in roots.iter().zip(&sources) {
                assert_eq!(
                    KernelTermExport::default().algebraic(root).unwrap(),
                    *source
                );
            }
            let condition = ConditionTerm::Variable(Variable(999731));
            let reduced = KernelTerm::algebraic_if([
                KernelTermImport::default().condition(&condition),
                roots[0].clone(),
                roots[1].clone(),
            ]);
            assert_eq!(
                KernelTermExport::default().algebraic(&reduced).unwrap(),
                AlgebraicTerm::if_then_else(condition, sources[0].clone(), sources[1].clone())
            );
        }
    }
}
