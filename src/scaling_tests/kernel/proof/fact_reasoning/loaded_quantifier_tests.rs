use super::*;

#[test]
fn loaded_quantifier_matching_ignores_ambient_facts_and_retained_memory_size() {
    for format in [
        MachineIntegerType::Int32,
        MachineIntegerType::UInt32,
        MachineIntegerType::Int64,
        MachineIntegerType::UInt64,
    ] {
        let mut costs = Vec::new();
        for size in [8, 16, 32, 64] {
            let _session = crate::kernel::VerificationSession::enter();
            let mut memory = Memory::new().with_block("loaded-quantifier", 64);
            for index in 0..size {
                let block = format!("unrelated-{index}");
                memory = memory.with_block(block.clone(), 8).store(
                    Pointer {
                        block: block.into(),
                        offset: PointerOffsetTerm::Constant(0),
                    },
                    ProgramValue::Int32(MachineTerm::constant(index as u32)),
                );
            }
            let memory = intern_memory(memory);
            let native = loaded_fact_of_format(&memory, Variable(920_001), false, format);
            let shared = loaded_fact_of_format(&memory, Variable(920_002), true, format);
            let mut facts = ProofFacts::from_ordered(std::slice::from_ref(&native));
            for index in 0..size {
                facts = facts.with_fact(Proposition::ConditionIs(
                    ConditionTerm::equal(
                        MachineTerm::Variable(Variable(930_000 + index)),
                        MachineTerm::constant(3),
                    ),
                    true,
                ));
            }
            let (found, work) = crate::instrumentation::measure_deterministic_work(|| {
                facts.matching_quantified_fact(&shared)
            });
            assert!(found.is_some());
            let changed = intern_memory(memory.as_ref().clone().store(
                Pointer {
                    block: "loaded-quantifier".into(),
                    offset: PointerOffsetTerm::Constant(0),
                },
                ProgramValue::Int32(MachineTerm::constant(7)),
            ));
            let missing = loaded_fact_of_format(&changed, Variable(920_002), true, format);
            let (refused, miss_work) = crate::instrumentation::measure_deterministic_work(|| {
                facts.matching_quantified_fact(&missing)
            });
            assert!(refused.is_none());
            costs.push((work, miss_work));
        }
        assert!(
            costs[0].0 > 0 && costs[0].1 > 0 && costs.iter().all(|work| *work == costs[0]),
            "{costs:?}"
        );
    }
}

#[test]
fn loaded_quantifier_matching_scales_with_selected_body() {
    let mut costs = Vec::new();
    for size in [8, 16, 32, 64] {
        let _session = crate::kernel::VerificationSession::enter();
        let memory = intern_memory(Memory::new().with_block("loaded-quantifier", 64));
        let grow = |binder, shared| {
            let mut proposition = loaded_fact(&memory, binder, shared);
            let Proposition::ForAll { body, .. } = &mut proposition else {
                unreachable!()
            };
            let leaf = body.clone();
            for _ in 1..size {
                *body = Box::new(Proposition::And(body.clone(), leaf.clone()));
            }
            proposition
        };
        let native = grow(Variable(920_001), false);
        let shared = grow(Variable(920_002), true);
        let (matched, work) = crate::instrumentation::measure_deterministic_work(|| {
            quantified_binder_equivalent(&native, &shared)
        });
        assert!(matched);
        costs.push(work);
    }
    assert!(
        costs[0] > 0 && costs.windows(2).all(|p| p[1] <= 3 * p[0]),
        "{costs:?}"
    );
}

#[test]
fn substituted_retained_comparison_body_scales_with_selected_input() {
    let mut costs = Vec::new();
    for size in [8, 16, 32, 64] {
        let _session = crate::kernel::VerificationSession::enter();
        let memory = intern_memory(Memory::new().with_block("loaded-quantifier", 64));
        let body = |shared| {
            let Proposition::ForAll { body, .. } = loaded_fact(&memory, Variable(960_001), shared)
            else {
                unreachable!()
            };
            let leaf = *body;
            let mut result = leaf.clone();
            for _ in 1..size {
                result = Proposition::And(Box::new(result), Box::new(leaf.clone()));
            }
            result
        };
        let native = body(false);
        let shared = body(true);
        let (matched, work) = crate::instrumentation::measure_deterministic_work(|| {
            substituted_body_retained_order_equivalent(&native, &shared)
        });
        assert!(matched);
        costs.push(work);
    }
    assert!(
        costs[0] > 0 && costs.windows(2).all(|p| p[1] <= 3 * p[0]),
        "{costs:?}"
    );
}
