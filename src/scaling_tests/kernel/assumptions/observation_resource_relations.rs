use super::*;

#[test]
fn resource_relation_comparison_keys_visit_only_selected_arguments() {
    let _session = crate::kernel::VerificationSession::enter();
    let mut work = Vec::new();
    for size in [8usize, 16, 32, 64] {
        let resource = Resource::Composite {
            name: "selected".into(),
            arguments: (0..size)
                .map(|i| {
                    AlgebraicValue::C(ProgramValue::Int32(MachineTerm::Variable(Variable(
                        3_219_400 + i as u64,
                    ))))
                })
                .collect(),
        };
        let goal = Proposition::CResourceContains {
            parent: Box::new(resource),
            child: Box::new(Resource::Emp),
        };
        let (_, cost) =
            crate::instrumentation::measure_deterministic_work(|| PropositionKey::new(&goal));
        work.push(cost);
    }
    assert!(work[0] > 0);
    for pair in work.windows(2) {
        assert!(pair[1] > pair[0]);
        assert!(pair[1] <= pair[0] * 3, "selected arguments: {work:?}");
    }
}

#[test]
fn resource_relation_comparison_lookup_ignores_unrelated_facts() {
    let mut work = Vec::new();
    for size in [64u64, 128, 512] {
        let _session = crate::kernel::VerificationSession::enter();
        let memory = crate::kernel::intern_c_memory(Memory::new());
        let address = Pointer::symbolic(Variable(3_219_500));
        let name = crate::kernel::eval::load_variable_for_exact_cell(
            &memory,
            &address,
            LoadKind::Int32,
            4,
        );
        let pointer = PointerValue::new(address.clone(), ProgramType::Int32Pointer);
        let source = relation(MachineTerm::Variable(name), pointer.clone(), false);
        let goal = relation(
            MachineTerm::MemoryLoad(memory, Box::new(address), LoadKind::Int32),
            pointer,
            false,
        );
        let mut facts = PureFactContext::new().assume_proposition(source.clone());
        for i in 0..size {
            facts = facts.assume_proposition(Proposition::Predicate {
                name: format!("unrelated_{i}"),
                arguments: Vec::new(),
            });
        }
        let (proved, cost) =
            crate::instrumentation::measure_deterministic_work(|| facts.proves_exact(&goal));
        assert!(proved);
        work.push(cost);
    }
    assert!(
        work.windows(2).all(|p| p[0] == p[1]),
        "unrelated facts: {work:?}"
    );
}

#[test]
fn deep_logical_comparison_keys_visit_each_selected_node_once() {
    let _session = crate::kernel::VerificationSession::enter();
    let mut costs = Vec::new();
    for depth in [32, 64, 128, 256, 512] {
        let mut proposition = Proposition::CResourceContains {
            parent: Box::new(Resource::Emp),
            child: Box::new(Resource::Emp),
        };
        for _ in 0..depth {
            proposition = Proposition::Implies(
                Box::new(Proposition::ConditionIs(
                    ConditionTerm::Constant(true),
                    true,
                )),
                Box::new(proposition),
            );
        }
        let (key, cost) = crate::instrumentation::measure_deterministic_work(|| {
            PropositionKey::for_source(&proposition).expect("resource leaf is admitted")
        });
        assert_eq!(key, PropositionKey::new(&proposition));
        costs.push(cost);
    }
    assert!(costs[0] > 0);
    for pair in costs.windows(2) {
        assert!(
            pair[1] > pair[0] && pair[1] <= 2 * pair[0],
            "selected nodes: {costs:?}"
        );
    }
}
