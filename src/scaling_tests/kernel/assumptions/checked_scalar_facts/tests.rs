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
            index.adjust(&source, false, true);
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
        index.adjust(&source, false, false);
        assert!(index.literal_equality(operand.operand_view()).is_none());
        assert!(parent.literal_equality(operand.operand_view()).is_some());
        for value in 1..=size {
            let excluded = ConditionTerm::IntegerEqual(
                observed.clone().into(),
                IntegerTerm::constant(value.into()).into(),
            );
            index.adjust(&excluded, false, true);
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
fn scalar_sources_preserve_truth_format_and_removal() {
    let term = Bitvector32Term::Variable(Variable(991702));
    let view = MachineOperandView::Legacy(&term);
    let native = ConditionTerm::equal(term.clone(), Bitvector32Term::Constant(7));
    let observed = IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
        MachineIntegerType::Int32,
        term.clone(),
    ));
    let ordinary =
        ConditionTerm::IntegerNotEqual(observed.into(), IntegerTerm::constant(7.into()).into());
    let mut index = CheckedScalarFacts::default();
    index.adjust(&ordinary, false, true);
    index.adjust(&native, true, true);
    index.adjust(&native, true, false);
    assert_eq!(
        index.literal_equality(view),
        Some(&(ordinary.clone(), false))
    );
    index.adjust(&ordinary, false, false);
    assert!(index.literal_equality(view).is_none());
    let wide = ConditionTerm::int64_equal(term, Bitvector32Term::Int64Constant(7));
    index.adjust(&wide, true, true);
    assert!(index.literals.is_empty());
}

#[test]
fn shared_scalar_premise_selection_keeps_written_truth() {
    let x = Bitvector32Term::Variable(Variable(991703));
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
