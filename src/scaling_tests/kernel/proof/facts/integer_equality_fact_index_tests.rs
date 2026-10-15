// Scaling tests of `src/kernel/proof/facts.rs` (module `integer_equality_fact_index_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn wide_equality_decision_uses_only_its_indexed_component() {
    let left = Bitvector32Term::Variable(Variable(211_000));
    let middle = Bitvector32Term::Variable(Variable(211_001));
    let equality = |a: Bitvector32Term, b: Bitvector32Term| {
        Proposition::ConditionIs(
            ConditionTerm::Bitvector64Equal(Box::new(a), Box::new(b)),
            true,
        )
    };
    let required = equality(left.clone(), Bitvector32Term::UInt64Constant(7));
    let wrong = equality(left.clone(), Bitvector32Term::UInt64Constant(9));
    let mut work = Vec::new();
    for size in [8, 16, 32, 64] {
        let unrelated = (0..size)
            .map(|index| {
                equality(
                    Bitvector32Term::Variable(Variable(212_000 + index)),
                    Bitvector32Term::UInt64Constant(index),
                )
            })
            .collect::<Vec<_>>();
        let facts = ProofFacts::from_ordered(&unrelated)
            .with_kernel_checked_fact(equality(left.clone(), middle.clone()))
            .with_kernel_checked_fact(equality(middle.clone(), Bitvector32Term::UInt64Constant(7)));
        let (proved, measured) = crate::instrumentation::measure_deterministic_work(|| {
            facts.assumptions().proves_atomic_without_search(&required)
        });
        assert!(proved);
        assert!(!facts.assumptions().proves_atomic_without_search(&wrong));
        work.push(measured);
    }
    assert!(work.windows(2).all(|pair| pair[0] == pair[1]), "{work:?}");
    let narrow = ProofFacts::from_ordered(&[
        Proposition::ConditionIs(
            ConditionTerm::Bitvector32Equal(Box::new(left), Box::new(middle.clone())),
            true,
        ),
        equality(middle, Bitvector32Term::UInt64Constant(7)),
    ]);
    assert!(!narrow.assumptions().proves_atomic_without_search(&required));
}

#[test]
fn quantified_loadable_alpha_query_ignores_unrelated_snapshot_size() {
    let mut work = Vec::new();
    for size in [8usize, 16, 32, 64] {
        let mut source_memory = CMemory::new();
        for index in 0..size {
            source_memory =
                source_memory.with_block(format!("quantified-viewable-work-{index}"), 8);
        }
        source_memory = source_memory.store(
            Pointer {
                block: "quantified-viewable-work-0".into(),
                offset: PointerOffsetTerm::Constant(0),
            },
            CValue::Int32(Bitvector32Term::Variable(Variable(209_000))),
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
        let facts = ProofFacts::from_ordered(std::slice::from_ref(&source));
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
        samples.push(work);
    }
    for pair in samples.windows(2) {
        assert!(pair[1] <= pair[0] * 3 + 32, "{samples:?}");
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
    let leaf = Proposition::ConditionIs(
        ConditionTerm::Bitvector32Equal(
            Box::new(Bitvector32Term::Constant(0)),
            Box::new(Bitvector32Term::Constant(0)),
        ),
        true,
    );
    let mut fact = leaf.clone();
    for _ in 0..10_000 {
        fact = Proposition::And(Box::new(leaf.clone()), Box::new(fact));
    }
    let (indexed, work) = crate::instrumentation::measure_deterministic_work(|| {
        index_proper_conjuncts(PersistentSet::default(), &fact)
    });
    assert!(indexed.contains(&leaf));
    assert!(work > 0);
}

#[test]
fn snapshot_blind_same_bucket_lookup_scales_without_deep_dedup() {
    let mut samples = Vec::new();
    for size in [4usize, 16, 64, 128] {
        let mut memories = Vec::with_capacity(size + 1);
        let base = CMemory::new().with_block("same-bucket-facts", 8);
        for value in 0..=size {
            let memory = base.clone().store(
                Pointer {
                    block: "same-bucket-facts".into(),
                    offset: PointerOffsetTerm::Constant(0),
                },
                // Distinct snapshots without contradictory literal
                // premises: each read may consistently equal zero.
                CValue::Int32(Bitvector32Term::Variable(Variable(986_000 + value as u64))),
            );
            memories.push(crate::kernel::intern_c_memory(memory));
        }
        let load = |memory: &crate::kernel::SharedCMemory| {
            Bitvector32Term::MemoryLoad(
                memory.clone(),
                Box::new(Pointer {
                    block: "same-bucket-facts".into(),
                    offset: PointerOffsetTerm::Constant(0),
                }),
                crate::kernel::LoadKind::Bits32,
            )
        };
        let facts = memories[..size]
            .iter()
            .map(|memory| {
                Proposition::ConditionIs(
                    ConditionTerm::Bitvector32Equal(
                        Box::new(load(memory)),
                        Box::new(Bitvector32Term::Constant(0)),
                    ),
                    true,
                )
            })
            .collect::<Vec<_>>();
        let required = Proposition::ConditionIs(
            ConditionTerm::Bitvector32Equal(
                Box::new(load(memories.last().unwrap())),
                Box::new(Bitvector32Term::Constant(0)),
            ),
            true,
        );
        let proof_facts = ProofFacts::from_ordered(&facts);
        let key = snapshot_blind_proposition_key(&required);
        let bucket_len = proof_facts
            .by_snapshot_blind
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
