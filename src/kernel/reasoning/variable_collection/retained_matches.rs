//! Prepared match readers. Preserve the separate native meanings of free
//! Integer variables, expression connections, capture reservations and binders.
use super::retained_folds::{FoldVariableRead, common_variables, union};
use super::*;
use crate::kernel::{KernelMatch, KernelTermNode, KernelType};

type Variables = crate::persistent::PersistentSet<Variable>;

pub(crate) fn collect_match_variables(
    matched: &KernelMatch,
    mode: FoldVariableRead,
    variables: &mut BTreeSet<Variable>,
) {
    let mut summaries = std::collections::HashMap::new();
    let result = match_variables(matched, mode, &mut summaries);
    variables.extend(result.iter().copied());
}

pub(super) fn match_variables(
    matched: &KernelMatch,
    mode: FoldVariableRead,
    summaries: &mut std::collections::HashMap<u64, Variables>,
) -> Variables {
    let integer_result = matched.result_type == KernelType::Integer;
    let machine_result = matches!(matched.result_type, KernelType::C(_));
    let scrutinee = &matched.arguments[0];
    let mut result = if mode == FoldVariableRead::ExpressionFree
        && machine_result
        && !collecting_connection_variables()
    {
        Variables::default()
    } else if mode == FoldVariableRead::IntegerFree && integer_result {
        // The native Integer match uses the algebraic *free* Integer reader;
        // ordinary argument collection deliberately has a different meaning.
        if let KernelTermNode::Legacy(value) = scrutinee.node() {
            let PureFunctionArgument::Algebraic(value) = value.value() else {
                unreachable!("typed algebraic scrutinee");
            };
            let mut free = BTreeSet::new();
            collect_algebraic_free_integer_variables(value, &mut free, &mut SeenTerms::default());
            let mut result = Variables::default();
            for variable in free {
                result = result.with_value(variable);
            }
            result
        } else {
            common_variables(scrutinee, mode, summaries)
        }
    } else {
        common_variables(scrutinee, mode, summaries)
    };
    for (arm, body) in matched.arms.iter().zip(&matched.arguments[1..]) {
        if checked_collection_checkpoint() {
            break;
        }
        let mut body = common_variables(body, mode, summaries);
        if mode == FoldVariableRead::IntegerFree && integer_result {
            for binding in &arm.bindings {
                if checked_collection_checkpoint() {
                    break;
                }
                if binding.ty() == &KernelType::Integer
                    && let KernelTermNode::Variable(variable) = binding.node()
                {
                    body = body.without_value(variable);
                }
            }
        } else if mode != FoldVariableRead::ExpressionFree || (!integer_result && !machine_result) {
            // Capture/binder readers visit declarations too. Expression
            // connections include them only for the algebraic result family.
            for binding in &arm.bindings {
                if checked_collection_checkpoint() {
                    break;
                }
                let binding = common_variables(binding, mode, summaries);
                body = union(&body, &binding);
            }
        }
        result = union(&result, &body);
    }
    result
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::{AlgebraicIntegerMatchArm, KernelMatch, KernelTermImport};

    #[test]
    fn retained_match_readers_preserve_each_native_collection_mode() {
        let native = IntegerTerm::AlgebraicMatch {
            scrutinee: Box::new(KernelMatch::test_scrutinee(vec![
                AlgebraicValueType::Integer,
            ])),
            arms: vec![AlgebraicIntegerMatchArm {
                variant: "Arm".into(),
                bindings: vec![AlgebraicValue::Integer(IntegerTerm::Variable(Variable(2)))],
                binding_names: Default::default(),
                body: IntegerTerm::Add(
                    IntegerTerm::Variable(Variable(2)).into(),
                    IntegerTerm::RangeFold {
                        index: IntegerRangeFoldIndex::Integer {
                            start: IntegerTerm::constant_i64(0).into(),
                            end: IntegerTerm::Variable(Variable(3)).into(),
                        },
                        initial: IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
                            MachineIntegerType::Int32,
                            MachineTerm::Variable(Variable(2)),
                        ))
                        .into(),
                        accumulator: Variable(4),
                        item: Variable(5),
                        body: IntegerTerm::Add(
                            IntegerTerm::Variable(Variable(4)).into(),
                            IntegerTerm::Variable(Variable(6)).into(),
                        )
                        .into(),
                    }
                    .into(),
                )
                .into(),
            }],
        };
        let common =
            KernelMatch::import_integer(&mut KernelTermImport::default(), &native).unwrap();
        for mode in [
            FoldVariableRead::IntegerFree,
            FoldVariableRead::ExpressionFree,
            FoldVariableRead::MachineCapture,
            FoldVariableRead::IntegerBinders,
            FoldVariableRead::MachineBinders,
        ] {
            let mut expected = BTreeSet::new();
            match mode {
                FoldVariableRead::IntegerFree => {
                    collect_integer_free_variables(&native, &mut expected)
                }
                FoldVariableRead::ExpressionFree => {
                    collect_integer_variables(&native, &mut expected)
                }
                FoldVariableRead::MachineCapture => {
                    collect_integer_capture_bitvector_variables(&native, &mut expected)
                }
                _ => {
                    let mut integer = BTreeSet::new();
                    let mut machine = BTreeSet::new();
                    collect_integer_binder_variables(&native, &mut integer, &mut machine);
                    expected = if mode == FoldVariableRead::IntegerBinders {
                        integer
                    } else {
                        machine
                    };
                }
            }
            let mut actual = BTreeSet::new();
            collect_match_variables(&common, mode, &mut actual);
            assert_eq!(actual, expected, "mode={mode:?}");
        }
    }

    #[test]
    fn retained_machine_match_readers_preserve_declaration_and_connection_rules() {
        let native = MachineTerm::AlgebraicMatch {
            scrutinee: Box::new(KernelMatch::test_scrutinee(vec![AlgebraicValueType::C(
                CType::Int32,
            )])),
            arms: vec![AlgebraicBitvectorMatchArm {
                variant: "Arm".into(),
                bindings: vec![AlgebraicValue::C(CValue::Int32(MachineTerm::Variable(
                    Variable(2),
                )))],
                binding_names: Default::default(),
                body: MachineTerm::Binary {
                    format: MachineIntegerType::Int32,
                    op: MachineBinaryOp::Add,
                    left: Box::new(MachineTerm::Variable(Variable(2))),
                    right: Box::new(MachineTerm::Variable(Variable(3))),
                },
            }],
        };
        let common = KernelMatch::import_machine(
            &mut KernelTermImport::default(),
            MachineIntegerType::Int32,
            &native,
        )
        .unwrap();
        for mode in [
            FoldVariableRead::IntegerFree,
            FoldVariableRead::ExpressionFree,
            FoldVariableRead::MachineCapture,
            FoldVariableRead::IntegerBinders,
            FoldVariableRead::MachineBinders,
        ] {
            let mut expected = BTreeSet::new();
            super::super::retained_folds::collect_machine_leaf(
                &native,
                mode,
                &mut expected,
                &mut SeenTerms::default(),
            );
            let mut actual = BTreeSet::new();
            collect_match_variables(&common, mode, &mut actual);
            assert_eq!(actual, expected, "mode={mode:?}");
        }
    }
}

#[cfg(test)]
mod scaling_tests {
    include!("../../../scaling_tests/kernel/reasoning/variable_collection/retained_matches.rs");
}
