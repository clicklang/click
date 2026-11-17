use super::*;
use crate::kernel::proof::PureFactStore;
use crate::kernel::{
    LoadKind, Pointer, PointerOffsetTerm, ProgramValue, SymbolicMemory, intern_memory,
};

fn loaded_fact(memory: &SharedMemory, binder: Variable, shared: bool) -> Proposition {
    loaded_fact_of_format(memory, binder, shared, MachineIntegerType::Int32)
}

fn loaded_fact_of_format(
    memory: &SharedMemory,
    binder: Variable,
    shared: bool,
    format: MachineIntegerType,
) -> Proposition {
    crate::kernel::reasoning::prepare_memory_variable_index(memory.as_ref());
    let left = MachineTerm::Variable(binder);
    let right = MachineTerm::Binary {
        format,
        op: MachineBinaryOp::Subtract,
        left: Box::new(MachineTerm::Variable(Variable(910_001))),
        right: Box::new(MachineTerm::Variable(Variable(910_002))),
    };
    let guard = if shared {
        ConditionTerm::IntegerLessThan(
            IntegerTerm::from_machine(format, left).unwrap().into(),
            IntegerTerm::from_machine(format, right).unwrap().into(),
        )
    } else {
        ConditionTerm::Compare {
            format,
            relation: CompareRelation::LessThan,
            left: Box::new(left),
            right: Box::new(right),
        }
    };
    let read = MachineTerm::MemoryLoad(
        ProgramPoint::at(memory),
        Box::new(Pointer {
            block: "loaded-quantifier".into(),
            offset: match format {
                MachineIntegerType::Int32 => {
                    PointerOffsetTerm::scaled_int32_node(MachineTerm::Variable(binder), 4)
                }
                MachineIntegerType::Int64 | MachineIntegerType::UInt64 => {
                    PointerOffsetTerm::scaled_int64_node(
                        MachineTerm::Variable(binder),
                        4,
                        format == MachineIntegerType::UInt64,
                    )
                }
                MachineIntegerType::UInt32 => PointerOffsetTerm::Constant(0),
                _ => unreachable!(),
            },
        }),
        LoadKind::Int32,
    );
    Proposition::ForAll {
        name: Default::default(),
        var: binder,
        sort: Sort::machine_integer(format),
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
    let memory = intern_memory(SymbolicMemory::new().with_block("loaded-quantifier", 64));
    let native = loaded_fact(&memory, Variable(920_001), false);
    let shared = loaded_fact(&memory, Variable(920_002), true);
    for (source, requested) in [(&native, &shared), (&shared, &native)] {
        let facts = PureFactStore::from_ordered(std::slice::from_ref(source));
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
            **right = MachineTerm::constant(1);
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
        let facts = PureFactStore::from_ordered(std::slice::from_ref(&native));
        assert!(
            facts.matching_quantified_fact(&different).is_none(),
            "change {change}"
        );
    }
}

#[test]
fn loaded_quantifier_shared_guard_does_not_rename_a_variable_inside_state() {
    let _session = crate::kernel::VerificationSession::enter();
    let memory = intern_memory(
        SymbolicMemory::new()
            .with_block("loaded-quantifier", 64)
            .store(
                Pointer {
                    block: "loaded-quantifier".into(),
                    offset: PointerOffsetTerm::Constant(0),
                },
                ProgramValue::Int32(MachineTerm::Variable(Variable(920_001))),
            ),
    );
    let native = loaded_fact(&memory, Variable(920_001), false);
    let shared = loaded_fact(&memory, Variable(920_002), true);
    for (source, requested) in [(&native, &shared), (&shared, &native)] {
        assert!(!quantified_binder_equivalent(source, requested));
        let facts = PureFactStore::from_ordered(std::slice::from_ref(source));
        assert!(facts.matching_quantified_fact(requested).is_none());
    }
}

#[test]
fn loaded_quantifier_native_guard_does_not_capture_a_variable_inside_state() {
    for existential in [false, true] {
        for shared in [false, true] {
            let _session = crate::kernel::VerificationSession::enter();
            let a = Variable(920_001);
            let b = Variable(920_002);
            let memory = intern_memory(
                SymbolicMemory::new()
                    .with_block("loaded-quantifier", 64)
                    .store(
                        Pointer {
                            block: "loaded-quantifier".into(),
                            offset: PointerOffsetTerm::Constant(0),
                        },
                        ProgramValue::Int32(MachineTerm::Variable(a)),
                    ),
            );
            let quantify = |binder| {
                let fact = loaded_fact(&memory, binder, shared);
                if existential {
                    let Proposition::ForAll {
                        var, sort, body, ..
                    } = fact
                    else {
                        unreachable!()
                    };
                    Proposition::Exists {
                        name: Default::default(),
                        var,
                        sort,
                        body,
                    }
                } else {
                    fact
                }
            };
            let first = quantify(a);
            let second = quantify(b);
            for (source, requested) in [(&first, &second), (&second, &first)] {
                assert!(!quantified_binder_equivalent(source, requested));
                let facts = PureFactStore::from_ordered(std::slice::from_ref(source));
                assert!(facts.matching_quantified_fact(requested).is_none());
            }
        }
    }
}

#[test]
fn loaded_quantifier_matching_renames_both_state_binders_without_swapping_free_variables() {
    let _session = crate::kernel::VerificationSession::enter();
    let a = Variable(970_001);
    let b = Variable(970_002);
    let fact = |binder, stored| {
        let memory = intern_memory(
            SymbolicMemory::new()
                .with_block("loaded-quantifier", 64)
                .store(
                    Pointer {
                        block: "loaded-quantifier".into(),
                        offset: PointerOffsetTerm::Constant(0),
                    },
                    ProgramValue::Int32(MachineTerm::Variable(stored)),
                ),
        );
        loaded_fact(&memory, binder, false)
    };
    let left = fact(a, a);
    let right = fact(b, b);
    assert!(quantified_binder_equivalent(&left, &right));
    assert!(quantified_binder_equivalent(&right, &left));
    // Swapping both a bound and a free name is not alpha equivalence.
    let left = fact(a, b);
    let right = fact(b, a);
    assert!(!quantified_binder_equivalent(&left, &right));
    assert!(!quantified_binder_equivalent(&right, &left));
}

#[test]
fn loaded_quantifier_guard_matching_preserves_machine_binder_width() {
    for format in [
        MachineIntegerType::Int32,
        MachineIntegerType::UInt32,
        MachineIntegerType::Int64,
        MachineIntegerType::UInt64,
    ] {
        let _session = crate::kernel::VerificationSession::enter();
        let memory = intern_memory(SymbolicMemory::new().with_block("loaded-quantifier", 64));
        let native = loaded_fact_of_format(&memory, Variable(940_001), false, format);
        let shared = loaded_fact_of_format(&memory, Variable(940_002), true, format);
        for (source, requested) in [(&native, &shared), (&shared, &native)] {
            let facts = PureFactStore::from_ordered(std::slice::from_ref(source));
            assert_eq!(
                facts.matching_quantified_fact(requested),
                Some(source.clone()),
                "{format:?}"
            );
            let mut wrong_sort = requested.clone();
            let Proposition::ForAll { sort, .. } = &mut wrong_sort else {
                unreachable!()
            };
            *sort = Sort::machine_integer(if format == MachineIntegerType::UInt64 {
                MachineIntegerType::Int32
            } else {
                MachineIntegerType::UInt64
            });
            assert!(facts.matching_quantified_fact(&wrong_sort).is_none());
        }
    }
}

#[test]
fn loaded_quantifier_without_prepared_state_matches_retained_order() {
    let _session = crate::kernel::VerificationSession::enter();
    let memory = intern_memory(SymbolicMemory::new().with_block("loaded-quantifier", 64));
    let native = loaded_fact(&memory, Variable(950_001), false);
    let shared = loaded_fact(&memory, Variable(950_002), true);
    let same_binder = loaded_fact(&memory, Variable(950_001), true);
    for (source, requested) in [
        (&native, &shared),
        (&shared, &native),
        (&native, &same_binder),
        (&same_binder, &native),
    ] {
        crate::kernel::reasoning::clear_shared_memory_variables();
        assert_eq!(
            crate::kernel::proof::fact_keys::selected_state_quantified_alpha_equivalent(
                source, requested
            ),
            None,
        );
        assert!(quantified_binder_equivalent(source, requested));
    }
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/proof/fact_reasoning/loaded_quantifier_tests.rs");
}
