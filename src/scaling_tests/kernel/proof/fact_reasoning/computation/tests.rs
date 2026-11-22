// Goal-local computational refusal must not traverse the selected states.
use super::*;

#[test]
fn selected_constructor_payload_check_scales_with_written_fields() {
    let types = [
        AlgebraicValueType::Program(ProgramType::Int32),
        AlgebraicValueType::Integer,
    ];
    let sizes = [8, 32, 128];
    for (ty, size) in types.iter().flat_map(|ty| sizes.map(|size| (ty, size))) {
        let _session = VerificationSession::enter();
        let mut scrutinee = KernelMatch::test_scrutinee(vec![ty.clone(); size]);
        let constructor = |fields| AlgebraicTermNode::Constructor {
            variant: "Arm".into(),
            fields,
        };
        let fields = (0..size)
            .map(|i| match ty {
                AlgebraicValueType::Integer => {
                    AlgebraicValue::Integer(IntegerTerm::var(Variable(992_300 + i as u64)))
                }
                _ => AlgebraicValue::Program(int32(MachineTerm::Variable(Variable(
                    992_300 + i as u64,
                )))),
            })
            .collect::<Vec<_>>();
        scrutinee.node = constructor(fields.clone());
        let bindings = (0..size)
            .map(|i| {
                let variable = Variable(992_100 + i as u64);
                match ty {
                    AlgebraicValueType::Integer => {
                        AlgebraicValue::Integer(IntegerTerm::var(variable))
                    }
                    _ => AlgebraicValue::Program(int32(MachineTerm::Variable(variable))),
                }
            })
            .collect::<Vec<_>>();
        let mut expected_fields = fields.into_iter().rev().collect::<Vec<_>>();
        let mut result_fields = bindings.iter().cloned().rev().collect::<Vec<_>>();
        if *ty == AlgebraicValueType::Integer {
            let captured = AlgebraicValue::Integer(IntegerTerm::var(Variable(992_500)));
            expected_fields[0] = captured.clone();
            result_fields[0] = captured;
        }
        let expected = AlgebraicTerm {
            algebraic_type: scrutinee.algebraic_type.clone(),
            node: constructor(expected_fields),
        };
        let body = AlgebraicTerm {
            algebraic_type: scrutinee.algebraic_type.clone(),
            node: constructor(result_fields),
        };
        let matched = AlgebraicTerm {
            algebraic_type: scrutinee.algebraic_type.clone(),
            node: AlgebraicTermNode::Match {
                scrutinee: Box::new(scrutinee),
                arms: vec![AlgebraicResultMatchArm {
                    variant: "Arm".into(),
                    binding_names: Default::default(),
                    bindings,
                    body,
                }],
            },
        };
        let goal = Proposition::Equal(
            Term::Algebraic(matched.into()),
            Term::Algebraic(expected.into()),
        );
        let (proved, work) =
            crate::instrumentation::measure_deterministic_work(|| computes_leaf(&goal));
        assert!(proved);
        assert!((2 * size..=8 * size + 48).contains(&work), "{size}: {work}");
    }
}

#[test]
fn nested_constructor_payload_check_scales_with_selected_arms() {
    for depth in [4, 8, 16] {
        let _session = VerificationSession::enter();
        let original = KernelMatch::test_scrutinee(vec![AlgebraicValueType::Integer]);
        let value =
            |index: u64| AlgebraicValue::Integer(IntegerTerm::var(Variable(993_000 + index)));
        let constructor = |index| AlgebraicTerm {
            algebraic_type: original.algebraic_type.clone(),
            node: AlgebraicTermNode::Constructor {
                variant: "Arm".into(),
                fields: vec![value(index)],
            },
        };
        let mut matched = constructor(depth);
        for index in (0..depth).rev() {
            matched = AlgebraicTerm {
                algebraic_type: original.algebraic_type.clone(),
                node: AlgebraicTermNode::Match {
                    scrutinee: Box::new(constructor(index)),
                    arms: vec![AlgebraicResultMatchArm {
                        variant: "Arm".into(),
                        binding_names: Default::default(),
                        bindings: vec![value(index + 1)],
                        body: matched,
                    }],
                },
            };
        }
        let goal = Proposition::Equal(
            Term::Algebraic(matched.into()),
            Term::Algebraic(constructor(0).into()),
        );
        let (proved, work) =
            crate::instrumentation::measure_deterministic_work(|| computes_leaf(&goal));
        assert!(proved);
        let depth = depth as usize;
        assert!(
            (3 * depth..=8 * depth + 48).contains(&work),
            "{depth}: {work}"
        );
    }
}

#[test]
fn constructor_match_computation_visits_shared_terms_once() {
    for depth in [16, 64, 256] {
        let _session = VerificationSession::enter();
        let variants: std::sync::Arc<[AlgebraicVariantType]> = vec![AlgebraicVariantType {
            name: "Wrap".into(),
            fields: vec![AlgebraicValueType::Integer],
        }]
        .into();
        let ty = AlgebraicType {
            rigid: false,
            name: "Boxed".into(),
            arguments: vec![],
            variants: variants.clone(),
            schemas: std::sync::Arc::new(AlgebraicSchemas::new(std::collections::BTreeMap::from(
                [(
                    AlgebraicValueType::Algebraic {
                        name: "Boxed".into(),
                        arguments: vec![],
                    },
                    variants,
                )],
            ))),
        };
        let field = IntegerTerm::var(Variable(970101));
        let binder = IntegerTerm::var(Variable(970102));
        let mut left: SharedIntegerTerm = IntegerTerm::AlgebraicMatch {
            scrutinee: Box::new(AlgebraicTerm {
                algebraic_type: ty,
                node: AlgebraicTermNode::Constructor {
                    variant: "Wrap".into(),
                    fields: vec![AlgebraicValue::Integer(field.clone())],
                },
            }),
            arms: vec![AlgebraicIntegerMatchArm {
                binding_names: Default::default(),
                variant: "Wrap".into(),
                bindings: vec![AlgebraicValue::Integer(binder.clone())],
                body: binder.into(),
            }],
        }
        .into();
        let mut right: SharedIntegerTerm = field.into();
        for _ in 0..depth {
            left = IntegerTerm::Add(left.clone(), left).into();
            right = IntegerTerm::Add(right.clone(), right).into();
        }
        let goal = Proposition::condition_is(ConditionTerm::IntegerEqual(left, right), true);
        let (proved, work) =
            crate::instrumentation::measure_deterministic_work(|| computes_leaf(&goal));
        assert!(proved);
        assert!(work <= 64 * depth + 1024, "{depth}: {work}");
    }
}

#[test]
fn stored_byte_order_uses_only_the_exact_cells() {
    let _session = VerificationSession::enter();
    let block = |name: &str| Address {
        base: AddressBase::Concrete(name.into()),
        offset: AddressOffset::Constant(0),
    };
    let left = block("byte-order-left");
    let right = block("byte-order-right");
    let other = block("byte-order-other");
    let format = MachineIntegerType::Int32;
    let read = |memory: &SymbolicMemory, pointer: Address| {
        MachineTerm::machine_integer_cast(
            MachineIntegerType::UInt8,
            format,
            MachineTerm::MemoryLoad(
                ProgramPoint::at(&crate::kernel::intern_memory(memory.clone())),
                Box::new(pointer),
                LoadKind::UInt8,
            ),
        )
    };
    let before = SymbolicMemory::new()
        .with_block(left.base.clone(), 256)
        .with_block(right.base.clone(), 1)
        .with_block(other.base.clone(), 256);
    let order = |memory: &SymbolicMemory, left_address, right_address| {
        Proposition::condition_is(
            ConditionTerm::machine_compare(
                format,
                CompareRelation::LessThan,
                read(memory, left_address),
                read(memory, right_address),
            ),
            true,
        )
    };
    let right_only = before.store(right.clone(), uint8(255));
    let seeded_left = right_only.clone().with_seeded_cells(
        left.clone(),
        1,
        ProgramType::UInt8,
        0,
        16,
        crate::kernel::intern_memory_ref(&right_only),
    );
    for memory in [&right_only, &seeded_left] {
        let unknown = order(memory, left.clone(), right.clone());
        assert!(!computes_leaf(&unknown));
        assert!(!computes_leaf(&Proposition::Not(Box::new(unknown))));
    }

    let samples = [(4, 4), (64, 4), (256, 4), (4, 64), (4, 256)].map(|(related, unrelated)| {
        let runs = (0..related)
            .map(|offset| ConstantRun {
                offset,
                stride: 1,
                count: 1,
                value: uint8(if offset == 0 { 0 } else { 7 }),
            })
            .collect::<Vec<_>>();
        let mut memory = right_only.clone().seed_fresh_declared_runs(&left, &runs);
        for offset in 0..unrelated {
            memory = memory.store(other.offset_by_bytes(offset), uint8(7));
        }
        let overwritten = memory.clone().store(left.clone(), uint8(255));
        assert!(!computes_leaf(&order(
            &overwritten,
            left.clone(),
            right.clone()
        )));
        let increasing = order(&memory, left.clone(), right.clone());
        let decreasing = order(&memory, right.clone(), left.clone());
        let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
            assert!(computes_leaf(&increasing));
            assert!(!computes_leaf(&decreasing));
            assert!(computes_leaf(&Proposition::Not(Box::new(decreasing))));
        });
        work
    });
    assert!(
        samples[0] > 0 && samples.iter().all(|work| *work == samples[0]),
        "{samples:?}"
    );
}

#[test]
fn cached_read_definedness_checks_only_the_selected_typed_cell() {
    let _session = VerificationSession::enter();
    let selected = Address {
        base: AddressBase::Concrete("local:definedness-read".into()),
        offset: AddressOffset::Constant(0),
    };
    let unrelated = Address {
        base: AddressBase::Concrete("local:other-definedness-read".into()),
        offset: AddressOffset::Constant(0),
    };
    let int32 = |value| ProgramValue::Int32(MachineTerm::constant(value));
    let before = SymbolicMemory::new()
        .with_block(selected.base.clone(), 4096)
        .with_block(unrelated.base.clone(), 4096);
    let defined =
        |memory: &SymbolicMemory, pointer: Address, value_type| Proposition::MemoryReadDefined {
            at: None,
            memory: memory.clone(),
            pointer,
            value_type,
        };
    let before_store = defined(&before, selected.clone(), ProgramType::Int32);
    assert!(!computes_leaf(&before_store));
    assert!(!computes_leaf(&Proposition::Not(Box::new(before_store))));

    let work = [(4, 4), (64, 4), (256, 4), (4, 64), (4, 256)].map(|(related, other)| {
        let seeded = before.clone().with_seeded_cells(
            selected.clone(),
            4,
            ProgramType::Int32,
            0,
            related,
            crate::kernel::intern_memory_ref(&before),
        );
        let seeded_read = defined(
            &seeded,
            selected.offset_by_bytes((related - 1) * 4),
            ProgramType::Int32,
        );
        let mut memory = before.clone();
        for slot in 1..=related {
            memory = memory.store(selected.offset_by_bytes(slot * 4), int32(slot));
            memory = memory.store(selected.clone(), int32(slot));
        }
        for slot in 0..other {
            memory = memory.store(unrelated.offset_by_bytes(slot * 4), int32(slot));
        }
        let typed = defined(&memory, selected.clone(), ProgramType::Int32);
        let wrong_type = defined(&memory, selected.clone(), ProgramType::Int64);
        let (results, work) = crate::instrumentation::measure_deterministic_work(|| {
            [
                computes_leaf(&typed),
                computes_leaf(&wrong_type),
                computes_leaf(&seeded_read),
            ]
        });
        assert_eq!(results, [true, false, true]);
        let retired = memory.without_local_block(&selected.base);
        assert!(!computes_leaf(&defined(
            &retired,
            selected.clone(),
            ProgramType::Int32
        )));
        work
    });
    assert!(
        work[0] > 0 && work.iter().all(|sample| *sample == work[0]),
        "{work:?}"
    );
}

#[test]
fn declared_word_definedness_requires_its_complete_initialized_representation() {
    let _session = VerificationSession::enter();
    let pointer = Address {
        base: AddressBase::Concrete("local:initialized-word".into()),
        offset: AddressOffset::Constant(0),
    };
    let memory = SymbolicMemory::new().with_declared_scalar_block(
        pointer.base.clone(),
        4,
        ProgramType::UInt32,
    );
    let valid_at = |memory, pointer, value_type| {
        computes_leaf(&Proposition::MemoryReadDefined {
            at: None,
            memory,
            pointer,
            value_type,
        })
    };
    let partial = memory.clone().with_initialized_object(&pointer, 3);
    let full = memory.with_initialized_object(&pointer, 4);
    assert!(!valid_at(partial, pointer.clone(), ProgramType::UInt32));
    assert!(!valid_at(full.clone(), pointer.clone(), ProgramType::Int32));
    assert!(!valid_at(
        full.clone(),
        pointer.offset_by_bytes(1),
        ProgramType::UInt32
    ));
    assert!(valid_at(full, pointer, ProgramType::UInt32));
}

#[test]
fn computation_refusal_is_independent_of_memory_history() {
    let mut costs = Vec::new();
    for size in [4, 16, 64, 256] {
        let _session = VerificationSession::enter();
        let pointer = Address {
            base: AddressBase::Concrete("computation-read".into()),
            offset: AddressOffset::Constant(0),
        };
        let other = Address {
            base: AddressBase::Concrete("computation-write".into()),
            offset: AddressOffset::Constant(0),
        };
        let before = crate::kernel::intern_memory(
            SymbolicMemory::new()
                .with_block("computation-read", 4)
                .with_block("computation-write", 4),
        );
        let mut after = before.memory().clone();
        for _ in 0..size {
            after = after.store(other.clone(), ProgramValue::Int32(MachineTerm::constant(7)));
        }
        let after = crate::kernel::intern_memory(after);
        let left = MachineTerm::MemoryLoad(
            ProgramPoint::at(&before),
            Box::new(pointer.clone()),
            LoadKind::Int32,
        );
        let right = MachineTerm::MemoryLoad(
            ProgramPoint::at(&after),
            Box::new(pointer.clone()),
            LoadKind::Int32,
        );
        let read_equality =
            Proposition::condition_is(ConditionTerm::equal(left.clone(), right), true);
        let add = |left, right| MachineTerm::Binary {
            format: MachineIntegerType::Int32,
            op: MachineBinaryOp::Add,
            left: Box::new(left),
            right: Box::new(right),
        };
        let rearranged = Proposition::condition_is(
            ConditionTerm::equal(
                add(left.clone(), MachineTerm::constant(1)),
                add(MachineTerm::constant(1), left),
            ),
            true,
        );
        let ((resolved, cancelled), work) =
            crate::instrumentation::measure_deterministic_work(|| {
                (computes_leaf(&read_equality), computes_leaf(&rearranged))
            });
        assert!(!resolved);
        assert!(cancelled);
        costs.push(work);
        assert!(!computes_leaf(&Proposition::MemoryLoadable {
            memory: before.memory().clone(),
            base: pointer,
            bytes: (MachineTerm::constant(5)).into(),
            wide: false,
        }));
    }
    assert!(
        costs[0] > 0 && costs.iter().all(|work| *work == costs[0]),
        "{costs:?}"
    );
}

#[test]
fn monomial_normalization_work_tracks_written_factors() {
    let samples = [4, 16, 64].map(|size| {
        let factors = (0..size)
            .map(|n| IntegerTerm::var(Variable(880000 + n)))
            .collect::<Vec<_>>();
        let product =
            |values: Vec<IntegerTerm>| values.into_iter().reduce(IntegerTerm::multiply).unwrap();
        let a = product(factors.clone());
        let b = product(factors.into_iter().rev().collect());
        let condition = ConditionTerm::IntegerEqual(a.clone().into(), b.clone().into());
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            integer_linear_comparison(&condition)
        });
        assert_eq!(result, Some(true));
        assert_ne!(
            integer_linear_comparison(&ConditionTerm::IntegerEqual(
                a.into(),
                IntegerTerm::add(b, IntegerTerm::constant_i64(1)).into()
            )),
            Some(true)
        );
        work
    });
    assert!(samples.windows(2).all(|p| p[1] <= 6 * p[0]), "{samples:?}");
}

#[test]
fn distribution_check_is_one_local_step_and_never_expands_a_polynomial() {
    let [a, b, c, d]: [IntegerTerm; 4] =
        std::array::from_fn(|n| IntegerTerm::var(Variable(881000 + n as u64)));
    let mul = IntegerTerm::multiply;
    let add = IntegerTerm::add;
    let step = ConditionTerm::IntegerEqual(
        mul(add(a.clone(), b.clone()), c.clone()).into(),
        add(mul(a.clone(), c.clone()), mul(b.clone(), c)).into(),
    );
    assert!(integer_distribution_step(&step));
    // Surface evaluation retains raw arithmetic nodes, including products
    // by one. The local rule must retain that same representation.
    let factor = IntegerTerm::Add(a.clone().into(), IntegerTerm::constant_i64(2).into());
    let raw_step = ConditionTerm::IntegerEqual(
        IntegerTerm::Multiply(
            IntegerTerm::Add(a.clone().into(), IntegerTerm::constant_i64(1).into()).into(),
            factor.clone().into(),
        )
        .into(),
        IntegerTerm::Add(
            IntegerTerm::Multiply(a.clone().into(), factor.clone().into()).into(),
            IntegerTerm::Multiply(IntegerTerm::constant_i64(1).into(), factor.into()).into(),
        )
        .into(),
    );
    assert!(integer_distribution_step(&raw_step));
    let full = ConditionTerm::IntegerEqual(
        mul(add(a.clone(), b.clone()), add(a.clone(), d.clone())).into(),
        add(
            add(mul(a.clone(), a.clone()), mul(a.clone(), d.clone())),
            add(mul(b.clone(), a), mul(b, d)),
        )
        .into(),
    );
    assert!(!integer_distribution_step(&full));
    assert_eq!(integer_linear_comparison(&full), None);
}

#[test]
fn integer_normalization_uses_intrinsic_widenings_with_linear_work() {
    use crate::kernel::{MachineCastSpelling, MachineIntegerType as Ty};
    fn observation(variable: u64, destination: Ty) -> IntegerTerm {
        let value = MachineTerm::Variable(Variable(variable));
        let value = if destination == Ty::UInt8 {
            value
        } else {
            MachineTerm::Cast {
                spelling: MachineCastSpelling::Generic,
                value: Box::new(value),
                from: Ty::UInt8,
                to: destination,
            }
        };
        IntegerTerm::from_machine(destination, value).unwrap()
    }
    let samples = [4, 16, 64].map(|size| {
        let mut left = IntegerTerm::constant_i64(0);
        let mut right = IntegerTerm::constant_i64(0);
        for index in 0..size {
            let variable = 882000 + index;
            left = IntegerTerm::add(
                left,
                IntegerTerm::multiply(
                    IntegerTerm::constant_i64(2),
                    observation(variable, Ty::Int32),
                ),
            );
            let narrow = observation(variable, Ty::UInt8);
            right = IntegerTerm::add(right, IntegerTerm::add(narrow.clone(), narrow));
        }
        let condition = ConditionTerm::IntegerEqual(left.into(), right.into());
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            integer_linear_comparison(&condition)
        });
        assert_eq!(result, Some(true));
        work
    });
    assert!(
        samples.windows(2).all(|pair| pair[1] <= 6 * pair[0] + 8),
        "{samples:?}"
    );
    // Converting the same byte to a signed byte may change its value.
    let narrowing = ConditionTerm::IntegerEqual(
        observation(883000, Ty::Int8).into(),
        observation(883000, Ty::UInt8).into(),
    );
    assert_ne!(integer_linear_comparison(&narrowing), Some(true));
}
