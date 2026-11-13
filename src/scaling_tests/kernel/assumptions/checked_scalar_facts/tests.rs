use super::*;
use crate::kernel::{
    IntegerTerm, KernelTerm, KernelType, MachineBinaryOp, SharedMachineIntegerTerm,
};

// Isolate this index: full PureFactContext admission still exports a native
// compatibility condition for consumers not migrated yet.
#[test]
fn shared_scalar_sources_keep_identity_and_branch_locality() {
    let mut previous = None;
    let mut query_work = None;
    for size in [8, 32, 96] {
        let mut root = KernelTerm::variable(
            KernelType::C(MachineIntegerType::Int32.c_type()),
            Variable(991701),
        );
        for _ in 0..size {
            root = KernelTerm::machine_binary_shared(
                MachineIntegerType::Int32,
                MachineBinaryOp::Add,
                [root.clone(), root.clone()],
            );
        }
        let operand =
            SharedMachineIntegerTerm::from_shared(MachineIntegerType::Int32, root).unwrap();
        let observed = IntegerTerm::Machine(operand.clone());
        let source = ConditionTerm::IntegerNotEqual(
            observed.clone().into(),
            IntegerTerm::constant(7.into()).into(),
        );
        let mut index = CheckedScalarFacts::default();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            index.adjust(&source, false);
            let (fact, truth) = index.literal_equality(operand.operand_view()).unwrap();
            assert_eq!((fact, *truth), (&source, false));
            assert_eq!(
                SignedConstantEvidence::exact_equality_value_view(
                    operand.operand_view(),
                    &Proposition::ConditionIs(fact.clone(), *truth)
                ),
                Some(7)
            );
        });
        assert!(!operand.has_boxed_operand());
        if let Some((old_size, old_work)) = previous {
            assert!(work <= old_work * size / old_size + 32);
        }
        previous = Some((size, work));
        let parent = index.clone();
        for value in 1..=size {
            let excluded = ConditionTerm::IntegerEqual(
                observed.clone().into(),
                IntegerTerm::constant(value.into()).into(),
            );
            index.adjust(&excluded, false);
        }
        let (range, work) = crate::instrumentation::measure_deterministic_work(|| {
            index.past_exclusions(operand.operand_view(), 1, size as i64 + 1)
        });
        assert_eq!(range, (size as i64 + 1, size as i64 + 1));
        if let Some(expected) = query_work {
            assert_eq!(work, expected);
        }
        query_work = Some(work);
        assert_eq!(
            parent.past_exclusions(operand.operand_view(), 1, size as i64 + 1),
            (1, size as i64 + 1)
        );
        assert!(!operand.has_boxed_operand());
    }
}

#[test]
fn scalar_sources_preserve_truth_and_format() {
    let term = MachineTerm::Variable(Variable(991702));
    let view = MachineOperandView::Legacy(&term);
    let observed = IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
        MachineIntegerType::Int32,
        term.clone(),
    ));
    let ordinary =
        ConditionTerm::IntegerNotEqual(observed.into(), IntegerTerm::constant(7.into()).into());
    let mut index = CheckedScalarFacts::default();
    index.adjust(&ordinary, false);
    assert_eq!(
        index.literal_equality(view),
        Some(&(ordinary.clone(), false))
    );
    let wide = ConditionTerm::int64_equal(term, MachineTerm::int64_constant(7));
    let mut index = CheckedScalarFacts::default();
    index.adjust(&wide, true);
    assert!(index.literals.is_empty());
}

#[test]
fn shared_scalar_premise_selection_keeps_written_truth() {
    let x = MachineTerm::Variable(Variable(991703));
    let observed = IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
        MachineIntegerType::Int32,
        x,
    ));
    let source = Proposition::ConditionIs(
        ConditionTerm::IntegerNotEqual(
            observed.clone().into(),
            IntegerTerm::constant(7.into()).into(),
        ),
        false,
    );
    let goal = Proposition::ConditionIs(
        ConditionTerm::IntegerEqual(observed.into(), IntegerTerm::constant(7.into()).into()),
        true,
    );
    let facts = PureFactContext::new().assume_proposition(source);
    let selected = facts.indexed_constant_equality_premises(&goal).unwrap();
    assert_eq!(selected.len(), 1);
    assert!(facts.contains_assumed_exact(&selected[0]));
    let selected_facts = PureFactContext::new().assume_proposition(selected[0].clone());
    assert!(PureFactContext::settles_exactly(&selected_facts, &goal));
    assert!(!PureFactContext::settles_exactly(
        &PureFactContext::new(),
        &goal
    ));
}

#[test]
fn promoted_call_endpoint_keys_preserve_typed_argument_identity() {
    use crate::kernel::{CValue, KernelTermExport, PureFunctionArgument, VerificationSession};
    let _session = VerificationSession::enter();
    let argument = MachineTerm::uint64_constant(7);
    let shared = SharedMachineIntegerTerm::intern(MachineIntegerType::UInt64, argument.clone());
    let call = |argument| MachineTerm::ClickFunctionApplication {
        name: "promoted_digit".into(),
        arguments: vec![argument],
    };
    let native = call(PureFunctionArgument::Value(CValue::UInt64(argument)));
    let retained = call(PureFunctionArgument::SharedMachine(shared));
    let promote = |value| {
        MachineTerm::machine_integer_cast(
            MachineIntegerType::UInt8,
            MachineIntegerType::Int32,
            value,
        )
    };
    let native = promote(native);
    let retained = promote(retained);
    let exports = KernelTermExport::machine_export_count();
    let key = |term: &MachineTerm| ScalarOperandKey::new(MachineOperandView::Legacy(term));
    assert_eq!(key(&native), key(&retained));
    let root = KernelTerm::retained_native_machine_operand(MachineIntegerType::Int32, &retained);
    assert_eq!(
        key(&native),
        ScalarOperandKey::new(MachineOperandView::Shared(&root))
    );
    assert_eq!(KernelTermExport::machine_export_count(), exports);
    let different = promote(call(PureFunctionArgument::Value(CValue::UInt64(
        MachineTerm::uint64_constant(8),
    ))));
    assert_ne!(key(&native), key(&different));
    let different_sort = promote(call(PureFunctionArgument::Value(CValue::Int64(
        MachineTerm::int64_constant(7),
    ))));
    assert_ne!(key(&native), key(&different_sort));
    let different_cast = MachineTerm::machine_integer_cast(
        MachineIntegerType::Int8,
        MachineIntegerType::Int32,
        call(PureFunctionArgument::Value(CValue::UInt64(
            MachineTerm::uint64_constant(7),
        ))),
    );
    assert_ne!(key(&native), key(&different_cast));
}

#[test]
fn arithmetic_call_endpoint_keys_preserve_argument_identity_and_opaque_refusal() {
    use crate::kernel::{CValue, KernelTermExport, PureFunctionArgument, VerificationSession};
    let _session = VerificationSession::enter();
    let call = |shared| MachineTerm::ClickFunctionApplication {
        name: "arithmetic_digit".into(),
        arguments: vec![if shared {
            PureFunctionArgument::SharedMachine(SharedMachineIntegerTerm::intern(
                MachineIntegerType::UInt64,
                MachineTerm::uint64_constant(7),
            ))
        } else {
            PureFunctionArgument::Value(CValue::UInt64(MachineTerm::uint64_constant(7)))
        }],
    };
    let promote = |value| {
        MachineTerm::machine_integer_cast(
            MachineIntegerType::UInt8,
            MachineIntegerType::Int32,
            value,
        )
    };
    let add = |left, right| MachineTerm::Binary {
        format: MachineIntegerType::Int32,
        op: MachineBinaryOp::Add,
        left: Box::new(left),
        right: Box::new(right),
    };
    let invert = |operand| MachineTerm::Unary {
        format: MachineIntegerType::Int32,
        op: crate::kernel::MachineUnaryOp::BitwiseNot,
        operand: Box::new(operand),
    };
    let key = |term: &MachineTerm| ScalarOperandKey::new(MachineOperandView::Legacy(term));
    let exports = KernelTermExport::machine_export_count();
    for (native, retained) in [
        (
            add(promote(call(false)), MachineTerm::constant(1)),
            add(promote(call(true)), MachineTerm::constant(1)),
        ),
        (invert(promote(call(false))), invert(promote(call(true)))),
    ] {
        assert_eq!(key(&native), key(&retained));
        let root =
            KernelTerm::retained_native_machine_operand(MachineIntegerType::Int32, &retained);
        assert_eq!(
            key(&native),
            ScalarOperandKey::new(MachineOperandView::Shared(&root))
        );
    }
    assert_eq!(KernelTermExport::machine_export_count(), exports);
    let read = MachineTerm::MemoryLoad(
        crate::kernel::intern_c_memory_ref(&CMemory::new()),
        Box::new(Pointer::null()),
        LoadKind::Int32,
    );
    let mixed = add(call(false), read);
    assert!(!selected_call_expression(MachineOperandView::Legacy(
        &mixed
    )));
    assert!(matches!(key(&mixed), ScalarOperandKey::Written(_)));
    assert_ne!(
        key(&add(call(false), MachineTerm::constant(1))),
        key(&add(call(true), MachineTerm::constant(2)))
    );
}

#[test]
fn opaque_call_endpoint_observation_is_linear_cold_and_constant_warm() {
    use crate::kernel::{KernelTermExport, PureFunctionArgument};
    let mut samples = Vec::new();
    for depth in [8, 32, 96] {
        let _session = crate::kernel::VerificationSession::enter();
        let call = MachineTerm::ClickFunctionApplication {
            name: "shared_endpoint_leaf".into(),
            arguments: vec![PureFunctionArgument::Value(CValue::Int32(
                MachineTerm::constant(7),
            ))],
        };
        let mut root =
            KernelTerm::retained_native_machine_operand(MachineIntegerType::Int32, &call);
        for _ in 0..depth {
            root = KernelTerm::machine_binary_shared(
                MachineIntegerType::Int32,
                MachineBinaryOp::Add,
                [root.clone(), root],
            );
        }
        let exports = KernelTermExport::machine_export_count();
        let (key, cold) = crate::instrumentation::measure_deterministic_work(|| {
            ScalarOperandKey::new(MachineOperandView::Shared(&root))
        });
        let (_, warm) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..8 {
                assert_eq!(
                    ScalarOperandKey::new(MachineOperandView::Shared(&root)),
                    key
                );
            }
        });
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        samples.push((depth, cold, warm));
    }
    for pair in samples.windows(2) {
        let [
            (small, cold_small, warm_small),
            (large, cold_large, warm_large),
        ] = pair
        else {
            unreachable!()
        };
        assert!(cold_large * small <= cold_small * large * 2, "{samples:?}");
        assert!(*warm_large <= warm_small + 8, "{samples:?}");
    }
}
