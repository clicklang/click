use super::*;
use crate::kernel::VerificationSession;

fn singleton(value: u32) -> SequenceTerm {
    SequenceTerm {
        element_type: Some(ProgramType::Int32),
        node: std::sync::Arc::new(SequenceTermNode::Literal(vec![int32(value)].into())),
    }
}

#[test]
fn integer_sequence_equality_has_linear_size_and_logarithmic_depth() {
    for size in [8usize, 32, 128, 512] {
        let mut left = singleton(0);
        for value in 1..size {
            left = concatenate_sequence_terms(left, singleton(value as u32));
        }
        let right = SequenceTerm {
            element_type: Some(ProgramType::Int32),
            node: std::sync::Arc::new(SequenceTermNode::Literal(
                (0..size)
                    .map(|n| int32(n as u32))
                    .collect::<Vec<_>>()
                    .into(),
            )),
        };
        let equality = finite_sequence_equality(&left, &right);
        let mut pending = vec![(&equality, 0)];
        let mut nodes = 0;
        let mut depth = 0;
        while let Some((proposition, current_depth)) = pending.pop() {
            nodes += 1;
            depth = depth.max(current_depth);
            if let Proposition::And(left, right) = proposition {
                pending.push((left, current_depth + 1));
                pending.push((right, current_depth + 1));
            }
        }
        assert_eq!(nodes, 2 * size - 1);
        assert_eq!(depth, size.ilog2());
    }
}

#[test]
fn repeated_concatenation_shares_the_existing_root() {
    for size in [8usize, 64, 512] {
        let mut sequence = singleton(0);
        for value in 1..size {
            let previous_root = sequence.node.clone();
            sequence = concatenate_sequence_terms(sequence, singleton(value as u32));
            let SequenceTermNode::Concat(left, _) = sequence.node.as_ref() else {
                panic!("nonempty concatenation should retain a rope node");
            };
            assert!(
                std::sync::Arc::ptr_eq(&left.node, &previous_root),
                "concatenating size {value} copied the existing sequence"
            );
        }
    }
}

#[test]
fn empty_concatenation_reuses_the_nonempty_root() {
    let empty = SequenceTerm {
        element_type: None,
        node: std::sync::Arc::new(SequenceTermNode::Literal(Vec::new().into())),
    };
    let value = singleton(7);
    let root = value.node.clone();

    assert!(std::sync::Arc::ptr_eq(
        &concatenate_sequence_terms(empty.clone(), value.clone()).node,
        &root,
    ));
    assert!(std::sync::Arc::ptr_eq(
        &concatenate_sequence_terms(value, empty).node,
        &root,
    ));
}

#[test]
fn evaluated_sequence_keeps_the_existing_program_producer() {
    let _session = crate::kernel::VerificationSession::enter();
    let atom = KernelTerm::variable(KernelType::Program(ProgramType::UInt32), Variable(10993401));
    let root = KernelTerm::machine_binary_shared(
        MachineIntegerType::UInt32,
        MachineBinaryOp::Add,
        [atom.clone(), atom],
    );
    let state =
        ExecutionState::new().with_retained_local("word", ExecutionValue::Shared(root.clone()));
    let expression = SpecSequenceExpression::Literal(vec![SpecExpression::ProgramExpression(
        ProgramExpression::Variable("word".into()),
    )]);
    let mut execution = ExecutionBudget::default();
    let exports = KernelTermExport::machine_export_count();
    let paths = evaluate_spec_sequence_at_state_in(
        SpecScope::new(&state, None, &NO_ALGEBRAIC_BINDINGS),
        &expression,
        &PureFactContext::new(),
        &mut SpecEvaluation::logical(&mut execution),
        false,
    )
    .unwrap();
    assert_eq!(paths.len(), 1);
    let SequenceTermNode::Literal(values) = paths[0].value.node.as_ref() else {
        panic!("literal sequence")
    };
    assert_eq!(values.retained_value(0).unwrap().shared(), Some(&root));
    assert_eq!(KernelTermExport::machine_export_count(), exports);
    assert!(!root.has_cached_native_argument());
}

#[test]
fn sequence_native_identity_order_hash_and_debug_are_unchanged() {
    use std::hash::{Hash, Hasher};
    let _session = VerificationSession::enter();
    let word = OldMachineTerm::Variable(Variable(10993402));
    let call = |argument| {
        ProgramValue::UInt32(OldMachineTerm::ClickFunctionApplication {
            name: "sequence_input".into(),
            arguments: vec![argument],
        })
    };
    let inputs = vec![
        call(PureFunctionArgument::Value(ProgramValue::UInt32(
            word.clone(),
        ))),
        call(PureFunctionArgument::SharedMachine(
            SharedMachineIntegerTerm::intern(MachineIntegerType::UInt32, word),
        )),
        ProgramValue::Bool(OldMachineTerm::constant(2)),
        ProgramValue::Float32(OldMachineTerm::uint32_constant(0x7fc00123)),
        ProgramValue::Float64(OldMachineTerm::uint64_constant(0x8000000000000000)),
        ProgramValue::typed_pointer(
            OldAddress::symbolic(Variable(10993403)),
            ProgramType::Int32Pointer,
        ),
    ];
    fn hash(value: &impl Hash) -> u64 {
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        value.hash(&mut hasher);
        hasher.finish()
    }
    for value in &inputs {
        let native: std::sync::Arc<[ProgramValue]> = vec![value.clone()].into();
        let stored = SequenceValues::from(native.clone());
        assert_eq!(hash(&native), hash(&stored));
        assert_eq!(format!("{stored:?}"), format!("{native:?}"));
        assert_eq!(stored.get(0), Some(value));
        for other in &inputs {
            let other_native: std::sync::Arc<[ProgramValue]> = vec![other.clone()].into();
            let other_stored = SequenceValues::from(other_native.clone());
            assert_eq!(stored == other_stored, native == other_native);
            assert_eq!(stored.cmp(&other_stored), native.cmp(&other_native));
        }
    }
    let native: std::sync::Arc<[ProgramValue]> = inputs.into();
    let retained = SequenceValues::from_values(native.iter().cloned().map(ExecutionValue::Native));
    assert_eq!(retained, SequenceValues::from(native.clone()));
    assert_eq!(hash(&retained), hash(&native));
}

#[test]
fn sequence_substitution_and_collection_keep_shared_producers() {
    let _session = VerificationSession::enter();
    let variable = Variable(10993404);
    let root = KernelTerm::variable(KernelType::Program(ProgramType::UInt32), variable);
    let value = Term::Sequence(SequenceTerm {
        element_type: Some(ProgramType::UInt32),
        node: std::sync::Arc::new(SequenceTermNode::Literal(SequenceValues::from_values([
            ExecutionValue::Shared(root.clone()),
        ]))),
    });
    let exports = KernelTermExport::machine_export_count();
    let mut variables = BTreeSet::new();
    crate::kernel::reasoning::collect_term_bitvector_variables(&value, &mut variables);
    assert_eq!(variables, BTreeSet::from([variable]));
    let unchanged = crate::kernel::reasoning::substitute_bitvector_variable_in_term(
        &value,
        Variable(10993405),
        &OldMachineTerm::constant(7),
    );
    let Term::Sequence(sequence) = unchanged else {
        panic!("sequence")
    };
    let SequenceTermNode::Literal(values) = sequence.node.as_ref() else {
        panic!("literal")
    };
    assert_eq!(values.retained_value(0).unwrap().shared(), Some(&root));
    let changed = crate::kernel::reasoning::substitute_bitvector_variable_in_term(
        &value,
        variable,
        &OldMachineTerm::constant(7),
    );
    let Term::Sequence(sequence) = &changed else {
        panic!("sequence")
    };
    let SequenceTermNode::Literal(values) = sequence.node.as_ref() else {
        panic!("literal")
    };
    assert!(values.retained_value(0).unwrap().shared().is_some());
    assert_eq!(KernelTermExport::machine_export_count(), exports);
    let native = Term::Sequence(SequenceTerm {
        element_type: Some(ProgramType::UInt32),
        node: std::sync::Arc::new(SequenceTermNode::Literal(
            vec![ProgramValue::UInt32(OldMachineTerm::Variable(variable))].into(),
        )),
    });
    assert_eq!(
        changed,
        crate::kernel::reasoning::substitute_bitvector_variable_in_term(
            &native,
            variable,
            &OldMachineTerm::constant(7)
        )
    );
}

mod scaling_tests {
    use super::*;
    include!("../../scaling_tests/kernel/spec/sequence_term_tests.rs");
}
