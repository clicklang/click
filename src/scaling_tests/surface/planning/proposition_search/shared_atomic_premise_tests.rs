// Scaling tests of `src/surface/planning/proposition_search.rs` (module `shared_atomic_premise_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn simp_retains_recorded_equality_edges_instead_of_connected_aliases() {
    let mut samples = Vec::new();
    for count in [8, 16, 32, 64, 128] {
        let term = |index| Bitvector32Term::Variable(Variable(9_320_000 + index));
        let equality = |left, right| {
            Proposition::ConditionIs(
                ConditionTerm::Bitvector32Equal(Box::new(term(left)), Box::new(term(right))),
                true,
            )
        };
        let first = equality(0, 1);
        let second = equality(1, 2);
        let goal = equality(0, 2);
        let mut context = PureFactContext::new()
            .assume_proposition(first.clone())
            .assume_proposition(second.clone());
        for index in 2..count {
            context = context.assume_proposition(equality(1, 10 + index as u64));
        }
        let (derivation, work) = crate::instrumentation::measure_deterministic_work(|| {
            context.derive_simp_proposition(&goal).unwrap()
        });
        let premises = derivation.context_premises();
        assert_eq!(premises.len(), 2, "count {count}");
        assert!(premises.contains(&first) && premises.contains(&second));
        assert!(derivation.check(&context));
        for missing in [&first, &second] {
            assert!(!derivation.check(&context.without_exact_fact(missing)));
        }
        samples.push((count, work));
    }
    for pair in samples.windows(2) {
        assert!(pair[1].1 <= pair[0].1.saturating_mul(3), "{samples:?}");
    }
}

// Connected pointer aliases used to make simp spell every historical
// premise even though the checked equality uses just these two links.
#[test]
fn simp_reduces_connected_pointer_premises_before_spelling() {
    let mut samples = Vec::new();
    for count in [8, 16, 32, 64, 128] {
        let pointer = |index| Pointer::symbolic(Variable(index));
        let left = pointer(1);
        let middle = pointer(2);
        let right = pointer(3);
        let equality =
            |left, right| Proposition::ConditionIs(ConditionTerm::pointer_equal(left, right), true);
        let first = equality(left.clone(), middle.clone());
        let second = equality(middle.clone(), right.clone());
        let goal = equality(left, right);
        let mut context = PureFactContext::new()
            .assume_proposition(first.clone())
            .assume_proposition(second.clone());
        for index in 2..count {
            context =
                context.assume_proposition(equality(middle.clone(), pointer(10 + index as u64)));
        }
        let (evidence, id) = context.proves_atomic_for_derivation_with_id(&goal, true);
        let evidence = evidence.expect("the alias chain proves the goal");
        let (selected, work) = crate::instrumentation::measure_deterministic_work(|| {
            reduce_simp_atomic_premises(&goal, true, (context, id, evidence)).unwrap()
        });
        let (reduced, id, evidence) = selected;
        let premises = RetainedPremises::from_context(&reduced);
        assert_eq!(premises.named().len(), 2);
        assert!(premises.named().contains(&first));
        assert!(premises.named().contains(&second));
        let derivation = proposition_derivation(
            &goal,
            PropositionDerivationRule::ContextualAtomic {
                premises,
                premises_id: id,
                for_simp: true,
                evidence,
            },
        );
        assert!(derivation.check(&reduced));
        // Neither required link can be supplied by the discarded aliases.
        for missing in [&first, &second] {
            assert!(!derivation.check(&reduced.without_exact_fact(missing)));
        }
        samples.push((count, work));
    }
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1.saturating_mul(3),
            "bounded premise reduction grew too quickly: {samples:?}"
        );
    }
}

#[test]
fn simp_retains_recorded_load_address_equality_premises() {
    let mut samples = Vec::new();
    for count in [8u64, 16, 32, 64, 128] {
        let term = |index: u64| Bitvector32Term::Variable(Variable(9_330_000 + index));
        let memory = intern_c_memory(CMemory::new().with_block("indexed", 8));
        let load = |offset| {
            crate::kernel::canonical_term(&Bitvector32Term::MemoryLoad(
                memory.clone(),
                Box::new(Pointer {
                    block: "indexed".into(),
                    offset,
                }),
                LoadKind::Bits32,
            ))
        };
        let indexed = load(PointerOffsetTerm::Int32Scaled {
            value: Box::new(term(0)),
            byte_width: 4,
        });
        let first = load(PointerOffsetTerm::Constant(0));
        let equality = |left, right| {
            Proposition::ConditionIs(
                ConditionTerm::Bitvector32Equal(Box::new(left), Box::new(right)),
                true,
            )
        };
        let required = equality(term(0), Bitvector32Term::Constant(0));
        let mut context = PureFactContext::new().assume_proposition(required.clone());
        for index in 1..count {
            context = context.assume_proposition(equality(term(0), term(index)));
        }
        let goal = equality(indexed, first);
        let (derivation, work) = crate::instrumentation::measure_deterministic_work(|| {
            context.derive_simp_proposition(&goal).unwrap()
        });
        assert!(derivation.load_address_congruence_paths().is_some());
        assert_eq!(derivation.context_premises(), vec![required.clone()]);
        assert!(derivation.check(&context));
        assert!(!derivation.check(&context.without_exact_fact(&required)));
        samples.push((count, work));
    }
    for pair in samples.windows(2) {
        assert!(pair[1].1 <= pair[0].1.saturating_mul(3), "{samples:?}");
    }
}
