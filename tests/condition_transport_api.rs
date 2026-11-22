use click::kernel::*;
use click::kernel::{CompareRelation, MachineIntegerType};

fn true_source() -> Proposition {
    Proposition::condition_is(ConditionTerm::Constant(true), true)
}

#[test]
fn inconsistent_context_retains_its_false_premise() {
    let source = true_source();
    let target = Proposition::condition_is(ConditionTerm::Constant(false), true);
    let context = PureFactContext::new().assume_proposition(target.clone());

    let theorem = prove_program_condition_fact_target_transport(&source, &target, &context)
        .expect("supplied contextual assumption gets accepted");
    let closed = Proposition::Implies(Box::new(source.clone()), Box::new(target.clone()));
    assert_ne!(theorem.proposition(), &closed);
    assert_eq!(
        theorem.proposition(),
        &Proposition::Implies(Box::new(target), Box::new(closed)),
    );
}

#[test]
fn consistent_context_retains_its_symbolic_premise() {
    let source = true_source();
    let target = Proposition::condition_is(
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::Equal,
            left: Box::new(MachineTerm::Variable(Variable(777))),
            right: Box::new(MachineTerm::constant(0)),
        },
        true,
    );
    assert!(
        prove_program_condition_fact_target_transport(&source, &target, &PureFactContext::new())
            .is_none()
    );
    let context = PureFactContext::new().assume_proposition(target.clone());

    let theorem = prove_program_condition_fact_target_transport(&source, &target, &context)
        .expect("supplied contextual assumption gets accepted");
    let closed = Proposition::Implies(Box::new(source.clone()), Box::new(target.clone()));
    assert_ne!(theorem.proposition(), &closed);
    assert_eq!(
        theorem.proposition(),
        &Proposition::Implies(Box::new(target), Box::new(closed)),
    );
}

#[test]
fn context_free_disjoint_store_transport_stays_closed() {
    let before = SymbolicMemory::new();
    let written = Address {
        base: "arg-memory".into(),
        offset: AddressOffset::Constant(0),
    };
    let preserved = Address {
        base: "arg-memory".into(),
        offset: AddressOffset::Constant(4),
    };
    let after = before.clone().store(written, int32(7));
    let old_load = MachineTerm::MemoryLoad(
        ProgramPoint::at(&click::kernel::intern_memory(before)),
        Box::new(preserved.clone()),
        LoadKind::Int32,
    );
    let new_load = MachineTerm::MemoryLoad(
        ProgramPoint::at(&click::kernel::intern_memory(after)),
        Box::new(preserved),
        LoadKind::Int32,
    );
    let source = Proposition::condition_is(
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::Equal,
            left: Box::new(old_load.clone()),
            right: Box::new(old_load.clone()),
        },
        true,
    );
    let target = Proposition::condition_is(
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::Equal,
            left: Box::new(new_load),
            right: Box::new(old_load),
        },
        true,
    );

    let theorem =
        prove_program_condition_fact_target_transport(&source, &target, &PureFactContext::new())
            .expect("a structurally disjoint store needs no contextual premise");
    assert_eq!(
        theorem.proposition(),
        &Proposition::Implies(Box::new(source), Box::new(target)),
    );
}

#[test]
fn retained_premises_ignore_unrelated_ambient_context_at_scale() {
    let source = true_source();
    let target = Proposition::condition_is(
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::Equal,
            left: Box::new(MachineTerm::Variable(Variable(777))),
            right: Box::new(MachineTerm::constant(0)),
        },
        true,
    );
    let expected = Proposition::Implies(
        Box::new(target.clone()),
        Box::new(Proposition::Implies(
            Box::new(source.clone()),
            Box::new(target.clone()),
        )),
    );
    let mut samples = Vec::new();
    for size in [8, 64, 512, 4096] {
        let mut context = PureFactContext::new().assume_proposition(target.clone());
        for index in 0..size {
            context = context.assume_proposition(Proposition::condition_is(
                ConditionTerm::Variable(Variable(10_000 + index)),
                true,
            ));
        }
        let (theorem, work) = click::instrumentation::measure_deterministic_work(|| {
            prove_program_condition_fact_target_transport(&source, &target, &context)
                .expect("the exact target premise is indexed")
        });
        assert_eq!(theorem.proposition(), &expected);
        samples.push((size, work));
    }
    assert!(
        samples.windows(2).all(|pair| pair[1].1 <= pair[0].1 + 8),
        "retaining one exact premise must not scan or wrap unrelated facts: {samples:?}"
    );
}
