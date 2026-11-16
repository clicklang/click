use super::*;
use crate::kernel::proof::ProofFacts;
use crate::kernel::{LoadKind, Memory, Pointer, PointerOffsetTerm, ProgramValue, intern_memory};

fn loaded_fact(memory: &SharedMemory, binder: Variable, shared: bool) -> Proposition {
    crate::kernel::reasoning::prepare_memory_variable_index(memory.as_ref());
    let left = MachineTerm::Variable(binder);
    let right = MachineTerm::Binary {
        format: MachineIntegerType::Int32,
        op: MachineBinaryOp::Subtract,
        left: Box::new(MachineTerm::Variable(Variable(910_001))),
        right: Box::new(MachineTerm::Variable(Variable(910_002))),
    };
    let guard = if shared {
        ConditionTerm::IntegerLessThan(
            IntegerTerm::from_machine(MachineIntegerType::Int32, left)
                .unwrap()
                .into(),
            IntegerTerm::from_machine(MachineIntegerType::Int32, right)
                .unwrap()
                .into(),
        )
    } else {
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::LessThan,
            left: Box::new(left),
            right: Box::new(right),
        }
    };
    let read = MachineTerm::MemoryLoad(
        ProgramPoint::at(memory),
        Box::new(Pointer {
            block: "loaded-quantifier".into(),
            offset: PointerOffsetTerm::scaled_int32_node(MachineTerm::Variable(binder), 4),
        }),
        LoadKind::Int32,
    );
    Proposition::ForAll {
        name: Default::default(),
        var: binder,
        sort: Sort::ProgramInt32,
        body: Box::new(Proposition::Implies(
            Box::new(Proposition::ConditionIs(guard, true)),
            Box::new(Proposition::ConditionIs(
                ConditionTerm::equal(read, MachineTerm::constant(0)),
                true,
            )),
        )),
    }
}

#[test]
fn loaded_quantifier_matches_shared_guard_but_keeps_exact_read_and_binder() {
    let _session = crate::kernel::VerificationSession::enter();
    let memory = intern_memory(Memory::new().with_block("loaded-quantifier", 64));
    let native = loaded_fact(&memory, Variable(920_001), false);
    let shared = loaded_fact(&memory, Variable(920_002), true);
    for (source, requested) in [(&native, &shared), (&shared, &native)] {
        let facts = ProofFacts::from_ordered(std::slice::from_ref(source));
        assert_eq!(
            facts.matching_quantified_fact(requested),
            Some(source.clone())
        );
        assert!(quantified_binder_equivalent(source, requested));
    }
    let changed_memory = intern_memory(memory.as_ref().clone().store(
        Pointer {
            block: "loaded-quantifier".into(),
            offset: PointerOffsetTerm::Constant(0),
        },
        ProgramValue::Int32(MachineTerm::constant(7)),
    ));
    assert!(!quantified_binder_equivalent(
        &native,
        &loaded_fact(&changed_memory, Variable(920_002), true)
    ));
    for change in 0..6 {
        let mut different = shared.clone();
        let Proposition::ForAll { sort, body, .. } = &mut different else {
            unreachable!()
        };
        if change == 0 {
            *sort = Sort::ProgramInt64;
        }
        let Proposition::Implies(guard, conclusion) = body.as_mut() else {
            unreachable!()
        };
        let Proposition::ConditionIs(_, truth) = guard.as_mut() else {
            unreachable!()
        };
        if change == 1 {
            *truth = false;
        }
        let Proposition::ConditionIs(ConditionTerm::Compare { left, right, .. }, _) =
            conclusion.as_mut()
        else {
            unreachable!()
        };
        if change == 2 {
            *right = Box::new(MachineTerm::constant(1));
        }
        let MachineTerm::MemoryLoad(_, pointer, kind) = left.as_mut() else {
            unreachable!()
        };
        match change {
            3 => pointer.block = "other-block".into(),
            4 => *kind = LoadKind::UInt32,
            5 => {
                pointer.offset = PointerOffsetTerm::scaled_int32_node(
                    MachineTerm::Variable(Variable(920_003)),
                    4,
                )
            }
            _ => {}
        }
        assert!(
            !quantified_binder_equivalent(&native, &different),
            "change {change}"
        );
        let facts = ProofFacts::from_ordered(std::slice::from_ref(&native));
        assert!(
            facts.matching_quantified_fact(&different).is_none(),
            "change {change}"
        );
    }
}

#[test]
fn loaded_quantifier_shared_guard_does_not_rename_a_variable_inside_state() {
    let _session = crate::kernel::VerificationSession::enter();
    let memory = intern_memory(Memory::new().with_block("loaded-quantifier", 64).store(
        Pointer {
            block: "loaded-quantifier".into(),
            offset: PointerOffsetTerm::Constant(0),
        },
        ProgramValue::Int32(MachineTerm::Variable(Variable(920_001))),
    ));
    let native = loaded_fact(&memory, Variable(920_001), false);
    let shared = loaded_fact(&memory, Variable(920_002), true);
    for (source, requested) in [(&native, &shared), (&shared, &native)] {
        assert!(!quantified_binder_equivalent(source, requested));
        let facts = ProofFacts::from_ordered(std::slice::from_ref(source));
        assert!(facts.matching_quantified_fact(requested).is_none());
    }
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/proof/fact_reasoning/loaded_quantifier_tests.rs");
}
