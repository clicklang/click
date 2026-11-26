// Scaling tests of `src/kernel/proof/facts.rs` (module `integer_equality_fact_index_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;
use crate::kernel::{CompareRelation, MachineIntegerType};
use crate::kernel::{
    IntegerComparisonOperator, KernelFold, KernelFoldIndex, KernelIntegerOperator, KernelTerm,
    KernelTermExport, KernelTermImport, KernelType, StoredConditionTerm,
};

#[test]
fn wide_equality_decision_uses_only_its_indexed_component() {
    let left = OldMachineTerm::Variable(Variable(211_000));
    let middle = OldMachineTerm::Variable(Variable(211_001));
    let equality = |a: OldMachineTerm, b: OldMachineTerm| {
        Proposition::condition_is(
            OldConditionTerm::Compare {
                format: MachineIntegerType::Int64,
                relation: CompareRelation::Equal,
                left: Box::new(a),
                right: Box::new(b),
            },
            true,
        )
    };
    let required = equality(left.clone(), OldMachineTerm::uint64_constant(7));
    let wrong = equality(left.clone(), OldMachineTerm::uint64_constant(9));
    let mut work = Vec::new();
    for size in [8, 16, 32, 64] {
        let unrelated = (0..size)
            .map(|index| {
                equality(
                    OldMachineTerm::Variable(Variable(212_000 + index)),
                    OldMachineTerm::uint64_constant(index),
                )
            })
            .collect::<Vec<_>>();
        let facts = PureFactStore::from_ordered(&unrelated)
            .with_kernel_checked_fact(equality(left.clone(), middle.clone()))
            .with_kernel_checked_fact(equality(middle.clone(), OldMachineTerm::uint64_constant(7)));
        let (proved, measured) = crate::instrumentation::measure_deterministic_work(|| {
            facts.assumptions().proves_atomic_without_search(&required)
        });
        assert!(proved);
        assert!(!facts.assumptions().proves_atomic_without_search(&wrong));
        work.push(measured);
    }
    assert!(work.windows(2).all(|pair| pair[0] == pair[1]), "{work:?}");
}

/// A 32-bit equality does not decide a 64-bit one. Debug builds refuse the
/// mixed-width context outright; a release build must still not prove the
/// wide equality through it.
#[test]
#[cfg_attr(
    debug_assertions,
    should_panic(expected = "a variable used at another width")
)]
fn a_narrow_equality_does_not_decide_a_wide_one() {
    let left = OldMachineTerm::Variable(Variable(211_000));
    let middle = OldMachineTerm::Variable(Variable(211_001));
    let required = Proposition::condition_is(
        OldConditionTerm::Compare {
            format: MachineIntegerType::Int64,
            relation: CompareRelation::Equal,
            left: Box::new(left.clone()),
            right: Box::new(OldMachineTerm::uint64_constant(7)),
        },
        true,
    );
    let narrow = PureFactStore::from_ordered(&[
        Proposition::condition_is(
            OldConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: Box::new(left),
                right: Box::new(middle.clone()),
            },
            true,
        ),
        Proposition::condition_is(
            OldConditionTerm::Compare {
                format: MachineIntegerType::Int64,
                relation: CompareRelation::Equal,
                left: Box::new(middle),
                right: Box::new(OldMachineTerm::uint64_constant(7)),
            },
            true,
        ),
    ]);
    assert!(!narrow.assumptions().proves_atomic_without_search(&required));
}

#[test]
fn quantified_loadable_alpha_query_ignores_unrelated_state_size() {
    let mut work = Vec::new();
    for size in [8usize, 16, 32, 64] {
        let mut source_memory = SymbolicMemory::new();
        for index in 0..size {
            source_memory =
                source_memory.with_block(format!("quantified-viewable-work-{index}"), 8);
        }
        source_memory = source_memory.store(
            Address::new(
                "quantified-viewable-work-0".into(),
                AddressOffset::constant(0),
            ),
            // A value the binder does not name, as the alpha query compares
            // the retained state exactly.
            ProgramValue::Int32(OldMachineTerm::Variable(Variable(209_900))),
        );
        let source = loadable_forall(
            &source_memory,
            Variable(209_000),
            "quantified-viewable-work-0",
            Some(Variable(209_001)),
            4,
        );
        let required = loadable_forall(
            &source_memory,
            Variable(209_100),
            "quantified-viewable-work-0",
            Some(Variable(209_001)),
            4,
        );
        let facts = PureFactStore::from_ordered(std::slice::from_ref(&source));
        let (matched, measured) = crate::instrumentation::measure_deterministic_work(|| {
            facts.matching_quantified_fact(&required)
        });
        assert_eq!(matched, Some(source.clone()));
        work.push(measured);
    }
    for pair in work.windows(2) {
        assert_eq!(pair[1], pair[0], "{work:?}");
    }
}

#[test]
fn integer_alpha_index_skips_growing_scalar_certificate_facts() {
    let mut samples = Vec::new();
    for depth in [8usize, 16, 32, 64] {
        let scalar = growing_shared_scalar_dag(depth);
        let facts = (0..depth)
            .map(|value| equality(scalar.clone(), IntegerTerm::constant_i64(value as i64)))
            .collect::<Vec<_>>();

        crate::kernel::proof::reset_alpha_proposition_key_visits();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            let mut index: PersistentMap<u64, PersistentSequence<IntegerConditionAlphaCandidate>> =
                PersistentMap::default();
            for fact in &facts {
                index = index_integer_condition_fact(index, fact);
            }
            index
        });
        assert_eq!(
            crate::kernel::proof::alpha_proposition_key_visits(),
            0,
            "scalar certificate facts must stay off the fold alpha index"
        );
        let scalar = KernelTermImport::default().integer(&scalar.into());
        let retained = (0..depth)
            .map(|value| {
                let root = KernelTerm::integer_comparison(
                    IntegerComparisonOperator::Equal,
                    [scalar.clone(), KernelTerm::integer_literal(value.into())],
                )
                .unwrap();
                Proposition::condition_is(StoredConditionTerm::from_root(root).unwrap(), true)
            })
            .collect::<Vec<_>>();
        let exports = KernelTermExport::integer_export_count();
        let (_, retained_work) = crate::instrumentation::measure_deterministic_work(|| {
            retained
                .iter()
                .fold(PersistentMap::default(), index_integer_condition_fact)
        });
        assert_eq!(KernelTermExport::integer_export_count(), exports);
        assert!(
            retained_work <= depth,
            "depth={depth}, work={retained_work}"
        );
        samples.push(work);
    }
    for pair in samples.windows(2) {
        assert!(pair[1] <= pair[0] * 3 + 32, "{samples:?}");
    }
}

#[test]
fn integer_alpha_index_reads_arithmetic_only_folds_without_export() {
    for depth in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let comparison = |accumulator, end: i64| {
            let mut body = KernelTerm::variable(KernelType::Integer, Variable(accumulator));
            for _ in 0..depth {
                body = KernelTerm::integer_operation(
                    KernelIntegerOperator::Add,
                    vec![body.clone(), body],
                )
                .unwrap();
            }
            let zero = KernelTerm::integer_literal(0.into());
            let fold = KernelFold::new(
                KernelFoldIndex::Integer,
                Variable(accumulator),
                Variable(accumulator + 1),
                [
                    zero.clone(),
                    KernelTerm::integer_literal(end.into()),
                    zero,
                    body,
                ],
            )
            .unwrap();
            KernelTerm::integer_comparison(
                IntegerComparisonOperator::LessEqual,
                [fold.into_term(), KernelTerm::integer_literal(9.into())],
            )
            .unwrap()
        };
        let retained =
            |root| Proposition::condition_is(StoredConditionTerm::from_root(root).unwrap(), true);
        let source_root = comparison(214_000, 8);
        let source = retained(source_root.clone());
        let required = retained(comparison(215_000, 8));
        let different = retained(comparison(215_000, 9));
        let exports = KernelTermExport::integer_export_count();
        let index = index_integer_condition_fact(PersistentMap::default(), &source);
        let key = integer_condition_alpha_key(&required).unwrap();
        assert!(index.get(&key.fingerprint()).is_some());
        assert_eq!(KernelTermExport::integer_export_count(), exports);

        let native =
            Proposition::condition_is(KernelTermExport::condition(&source_root).unwrap(), true);
        assert_eq!(integer_condition_alpha_key(&native), Some(key));
        let mut samples = Vec::new();
        for unrelated in [0, 16, 64, 256] {
            let mut premises = vec![native.clone()];
            premises.extend((0..unrelated).map(|index| Proposition::Predicate {
                name: format!("unrelated_{index}"),
                arguments: vec![],
            }));
            let facts = PureFactStore::from_ordered(&premises);
            let exports = KernelTermExport::integer_export_count();
            let (matched, work) = crate::instrumentation::measure_deterministic_work(|| {
                (
                    facts.matching_integer_condition_alpha_fact(&required),
                    facts.matching_integer_condition_alpha_fact(&different),
                )
            });
            assert_eq!(matched, (Some(native.clone()), None));
            assert_eq!(KernelTermExport::integer_export_count(), exports);
            samples.push(work);
        }
        assert!(
            samples.iter().all(|work| *work == samples[0]),
            "{samples:?}"
        );
        assert!(
            samples[0] <= 50 * depth + 200,
            "depth={depth}, work={samples:?}"
        );
    }
}

#[test]
fn integer_alpha_index_keeps_one_source_for_renamed_fold_restatements() {
    let mut samples = Vec::new();
    for depth in [8usize, 16, 32, 64] {
        let (index, work) = crate::instrumentation::measure_deterministic_work(|| {
            let mut index: PersistentMap<u64, PersistentSequence<IntegerConditionAlphaCandidate>> =
                PersistentMap::default();
            for restatement in 0..depth {
                let accumulator = Variable(205_000 + restatement as u64 * 2);
                let item = Variable(205_001 + restatement as u64 * 2);
                let fold = fold(
                    integer_index(),
                    accumulator,
                    item,
                    IntegerTerm::add(IntegerTerm::var(accumulator), IntegerTerm::var(item)),
                );
                index = index_integer_condition_fact(
                    index,
                    &equality(IntegerTerm::constant_i64(9), fold),
                );
            }
            index
        });
        let representative = equality(
            IntegerTerm::constant_i64(9),
            fold(
                integer_index(),
                Variable(205_000),
                Variable(205_001),
                IntegerTerm::add(
                    IntegerTerm::var(Variable(205_000)),
                    IntegerTerm::var(Variable(205_001)),
                ),
            ),
        );
        let key = integer_condition_alpha_key(&representative)
            .expect("fold equality should be alpha-indexed")
            .fingerprint();
        let bucket = index.get(&key).expect("representative bucket");
        assert_eq!(
            bucket.len(),
            1,
            "renamed folds must not grow one alpha bucket"
        );
        assert_eq!(bucket.iter().next().unwrap().proposition, representative);
        samples.push(work);
    }
    for pair in samples.windows(2) {
        assert!(pair[1] <= pair[0] * 3 + 32, "{samples:?}");
    }
}

#[test]
fn proper_conjunct_index_walks_deep_conjunction_iteratively() {
    let leaf = Proposition::condition_is(
        OldConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::Equal,
            left: Box::new(OldMachineTerm::constant(0)),
            right: Box::new(OldMachineTerm::constant(0)),
        },
        true,
    );
    let mut fact = leaf.clone();
    for _ in 0..10_000 {
        fact = Proposition::And(Box::new(leaf.clone()), Box::new(fact));
    }
    let (indexed, work) = crate::instrumentation::measure_deterministic_work(|| {
        index_proper_conjuncts(PersistentSet::default(), &fact)
    });
    assert!(indexed.contains(&PropositionKey::new(&leaf)));
    assert!(work > 0);
}

#[test]
fn memory_erased_integer_keys_read_retained_observations_and_skip_scalar_dags() {
    use crate::kernel::MachineBinaryOp;
    let mut samples = Vec::new();
    for depth in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let format = MachineIntegerType::Int32;
        let mut operand = KernelTerm::variable(
            KernelType::Program(format.program_type()),
            Variable(216_000),
        );
        for _ in 0..depth {
            operand = KernelTerm::machine_binary_shared(
                format,
                MachineBinaryOp::Add,
                [operand.clone(), operand],
            );
        }
        let observation =
            IntegerTerm::Machine(SharedMachineIntegerTerm::from_shared(format, operand).unwrap());
        let observation = KernelTermImport::default().integer(&observation.into());
        let literal = KernelTerm::integer_literal(9.into());
        let retained = |root, truth| {
            Proposition::condition_is(StoredConditionTerm::from_root(root).unwrap(), truth)
        };
        let comparison = |operator| {
            KernelTerm::integer_comparison(operator, [observation.clone(), literal.clone()])
                .unwrap()
        };
        let exports = KernelTermExport::integer_export_count();
        let machine_exports = KernelTermExport::machine_export_count();
        let fact = retained(comparison(IntegerComparisonOperator::LessEqual), true);
        let (key, work) = crate::instrumentation::measure_deterministic_work(|| {
            memory_erased_proposition_key(&fact)
        });
        assert!(matches!(key, MemoryErasedPropositionKey::Condition(..)));
        assert_eq!(KernelTermExport::integer_export_count(), exports);
        assert_eq!(KernelTermExport::machine_export_count(), machine_exports);
        samples.push(work);

        for operator in [
            IntegerComparisonOperator::Equal,
            IntegerComparisonOperator::NotEqual,
            IntegerComparisonOperator::LessThan,
            IntegerComparisonOperator::LessEqual,
            IntegerComparisonOperator::GreaterThan,
            IntegerComparisonOperator::GreaterEqual,
        ] {
            let root = comparison(operator);
            let keys = [true, false]
                .map(|truth| check_retained_key_no_export(&retained(root.clone(), truth)));
            let native = KernelTermExport::condition(&root).unwrap();
            for (actual, truth) in keys.into_iter().zip([true, false]) {
                assert_eq!(
                    actual,
                    memory_erased_proposition_key(&Proposition::condition_is(
                        native.clone(),
                        truth
                    ))
                );
            }
        }

        let scalar = KernelTermImport::default().integer(&growing_shared_scalar_dag(depth).into());
        let huge = KernelTerm::integer_literal(num_bigint::BigInt::from(1) << 1024usize);
        let wide =
            KernelTerm::integer_comparison(IntegerComparisonOperator::Equal, [observation, huge])
                .unwrap();
        assert!(matches!(
            check_retained_key_no_export(&retained(wide, true)),
            MemoryErasedPropositionKey::Exact(_)
        ));
        let root =
            KernelTerm::integer_comparison(IntegerComparisonOperator::Equal, [scalar, literal])
                .unwrap();
        let fact = retained(root, true);
        let (key, work) = crate::instrumentation::measure_deterministic_work(|| {
            check_retained_key_no_export(&fact)
        });
        assert!(matches!(key, MemoryErasedPropositionKey::Exact(_)));
        assert!(work <= 2, "depth={depth}, work={work}");
    }
    for pair in samples.windows(2) {
        assert!(pair[1] <= 4 * pair[0] + 64, "{samples:?}");
    }
}

fn check_retained_key_no_export(fact: &Proposition) -> MemoryErasedPropositionKey {
    let exports = KernelTermExport::integer_export_count();
    let key = memory_erased_proposition_key(fact);
    assert_eq!(KernelTermExport::integer_export_count(), exports);
    key
}

#[test]
fn memory_erased_same_bucket_lookup_scales_without_deep_dedup() {
    let mut samples = Vec::new();
    for size in [4usize, 16, 64, 128] {
        let mut memories = Vec::with_capacity(size + 1);
        let base = SymbolicMemory::new().with_block("same-bucket-facts", 8);
        for value in 0..=size {
            let memory = base.clone().store(
                Address::new("same-bucket-facts".into(), AddressOffset::constant(0)),
                // Distinct states without contradictory literal
                // premises: each read may consistently equal zero.
                ProgramValue::Int32(OldMachineTerm::Variable(Variable(986_000 + value as u64))),
            );
            memories.push(crate::kernel::intern_memory(memory));
        }
        let load = |memory: &crate::kernel::SharedMemory| {
            OldMachineTerm::read_named(
                ProgramPoint::at(memory),
                Box::new(Address::new(
                    "same-bucket-facts".into(),
                    AddressOffset::constant(0),
                )),
                crate::kernel::LoadKind::Int32,
            )
        };
        let facts = memories[..size]
            .iter()
            .map(|memory| {
                Proposition::condition_is(
                    OldConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::Equal,
                        left: Box::new(load(memory)),
                        right: Box::new(OldMachineTerm::constant(0)),
                    },
                    true,
                )
            })
            .collect::<Vec<_>>();
        let required = Proposition::condition_is(
            OldConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: Box::new(load(memories.last().unwrap())),
                right: Box::new(OldMachineTerm::constant(0)),
            },
            true,
        );
        let proof_facts = PureFactStore::from_ordered(&facts);
        let key = memory_erased_proposition_key(&required);
        let bucket_len = proof_facts
            .by_memory_erased
            .get(&key)
            .map(PersistentSequence::len)
            .unwrap_or(0);
        assert_eq!(bucket_len, size);
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            assert!(!proof_facts.exact_available_across_effects(&required, &[]));
        });
        samples.push(work);
    }
    for pair in samples.windows(2) {
        assert!(pair[1] >= pair[0]);
        assert!(pair[1] <= pair[0] * 8 + 32, "{samples:?}");
    }
}

#[test]
fn proper_conjunct_observation_keys_ignore_unrelated_facts() {
    use crate::kernel::machine_integer::comparison::retained_arithmetic_comparison;
    let sum = OldMachineTerm::uint64_add(
        OldMachineTerm::Variable(Variable(992_801)),
        OldMachineTerm::uint64_constant(1),
    );
    let condition = OldConditionTerm::uint64_less_equal(sum, OldMachineTerm::uint64_constant(127));
    let native = Proposition::condition_is(condition.clone(), true);
    let retained_condition = retained_arithmetic_comparison(&condition).unwrap();
    let retained = Proposition::condition_is(retained_condition.clone(), true);
    let opposite = Proposition::condition_is(retained_condition, false);
    let mut work = Vec::new();
    for size in [8, 32, 128] {
        let unrelated: Vec<_> = (0..size)
            .map(|i| {
                Proposition::condition_is(
                    OldConditionTerm::uint64_equal(
                        OldMachineTerm::Variable(Variable(993_000 + i)),
                        OldMachineTerm::uint64_constant(i),
                    ),
                    true,
                )
            })
            .collect();
        for (source, requested) in [(&native, &retained), (&retained, &native)] {
            let facts =
                PureFactStore::from_ordered(&unrelated).with_kernel_checked_fact(Proposition::And(
                    Box::new(source.clone()),
                    Box::new(Proposition::condition_is(
                        OldConditionTerm::Constant(true),
                        true,
                    )),
                ));
            let exports = KernelTermExport::machine_export_count();
            let (found, cost) = crate::instrumentation::measure_deterministic_work(|| {
                facts.contains_proper_conjunct(requested)
            });
            assert!(found);
            assert!(!facts.contains_proper_conjunct(&opposite));
            assert_eq!(KernelTermExport::machine_export_count(), exports);
            assert!(
                !PureFactStore::from_ordered(std::slice::from_ref(source))
                    .contains_proper_conjunct(requested)
            );
            work.push(cost);
        }
    }
    assert!(work.iter().all(|cost| *cost <= work[0] * 2 + 8), "{work:?}");
}

#[test]
fn retained_call_atom_keys_own_their_observation_identities() {
    for count in [16, 64, 256] {
        let _session = VerificationSession::enter();
        let format = MachineIntegerType::Int32;
        let opaque = OldMachineTerm::ClickFunctionApplication {
            name: "opaque_argument".into(),
            arguments: Vec::new(),
        };
        let root = KernelTerm::retained_native_machine_operand(format, &opaque);
        let argument = PureFunctionArgument::SharedMachine(
            SharedMachineIntegerTerm::from_shared(format, root).unwrap(),
        );
        let term = OldMachineTerm::ClickFunctionApplication {
            name: "outer_call".into(),
            arguments: vec![argument],
        };
        let original = bitvector_equality_atom_key(&term).unwrap();
        let _noise: Vec<_> = (0..count)
            .map(|index| {
                SharedPureApplication::intern(
                    "unrelated_call_key".into(),
                    vec![PureFunctionArgument::Value(ProgramValue::Int32(
                        OldMachineTerm::Variable(Variable(998_800 + index)),
                    ))],
                )
            })
            .collect();
        let (repeated, work) = crate::instrumentation::measure_deterministic_work(|| {
            bitvector_equality_atom_key(&term).unwrap()
        });
        assert_eq!(original, repeated);
        assert!(work < 32, "unrelated calls {count}: {work}");
    }
}

#[test]
fn exact_call_lookup_retains_shared_argument_prefixes() {
    for depth in [16, 64, 256] {
        let _session = VerificationSession::enter();
        let format = MachineIntegerType::Int32;
        let mut root =
            KernelTerm::variable(KernelType::Program(ProgramType::Int32), Variable(998_900));
        for _ in 0..depth {
            root = KernelTerm::machine_binary_shared(
                format,
                MachineBinaryOp::Add,
                [root.clone(), root],
            );
        }
        let inner = OldMachineTerm::ClickFunctionApplication {
            name: "inner_retained_call".into(),
            arguments: vec![PureFunctionArgument::SharedMachine(
                SharedMachineIntegerTerm::from_shared(format, root).unwrap(),
            )],
        };
        let retained = SharedMachineIntegerTerm::from_shared(
            format,
            KernelTerm::retained_native_machine_operand(format, &inner),
        )
        .unwrap();
        let call = |argument| OldMachineTerm::ClickFunctionApplication {
            name: "outer_retained_call".into(),
            arguments: vec![argument],
        };
        let fact = |term| {
            Proposition::condition_is(
                OldConditionTerm::equal(term, OldMachineTerm::constant(0)),
                true,
            )
        };
        let source = fact(call(PureFunctionArgument::Value(ProgramValue::Int32(
            inner,
        ))));
        let requested = fact(call(PureFunctionArgument::SharedMachine(retained)));
        assert_ne!(source, requested);
        let facts = PureFactStore::from_ordered(&[source]);
        let exports = KernelTermExport::machine_export_count();
        let (available, work) =
            crate::instrumentation::measure_deterministic_work(|| facts.contains(&requested));
        assert!(available);
        assert!(work < 128, "argument prefix {depth}: {work}");
        assert_eq!(KernelTermExport::machine_export_count(), exports);
    }
}
