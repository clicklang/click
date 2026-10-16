// Scaling tests of `src/kernel/eval/pointer_tags.rs` (module `exact_word_address_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

// A compound word's exact address is an indexed premise. Unrelated word
// equalities must neither be searched nor create conversion obligations.
#[test]
#[ignore = "nightly: 0.5s in the parallel gate"]
fn compound_word_address_lookup_skips_unrelated_equalities() {
    let _session = crate::kernel::VerificationSession::enter();
    let pointer = Pointer::symbolic(Variable(960001));
    let word = Bitvector32Term::Variable(Variable(960002));
    let expressions = [
        Bitvector32Term::uint64_bitwise_and(word.clone(), Bitvector32Term::UInt64Constant(!3)),
        Bitvector32Term::uint64_bitwise_or(word, Bitvector32Term::Variable(Variable(960003))),
    ];
    for expression in expressions {
        let fact = Proposition::ConditionIs(
            ConditionTerm::uint64_equal(
                expression.clone(),
                Bitvector32Term::PointerAddress(Box::new(pointer.clone())),
            ),
            true,
        );
        let mut costs = Vec::new();
        for size in [16, 64, 256, 1024] {
            let mut assumptions = PureFactContext::new().assume_proposition(fact.clone());
            for index in 0..size {
                assumptions = assumptions.assume_condition(
                    ConditionTerm::uint64_equal(
                        Bitvector32Term::Variable(Variable(970000 + index)),
                        Bitvector32Term::UInt64Constant(index),
                    ),
                    true,
                );
            }
            let mut used = UsedFacts::new();
            let (form, work) = crate::instrumentation::measure_deterministic_work(|| {
                tagged_address_form(&expression, &assumptions, &mut used)
            });
            let form = form.expect("the exact address equation names the original pointer");
            assert_eq!(form.pointer, pointer);
            assert_eq!(form.tag.uint64_as_const(), Some(0));
            assert!(used.complete);
            assert_eq!(used.premises, vec![fact.clone()]);
            let mut obligations = Vec::new();
            assert_eq!(
                cast_tagged_address_to_pointer(&expression, &assumptions, &mut obligations)
                    .unwrap(),
                Some(pointer.clone())
            );
            assert!(obligations.is_empty());
            costs.push(work);
        }
        assert!(
            costs[0] > 0 && costs.iter().all(|work| *work <= costs[0] * 2),
            "{costs:?}"
        );
    }
}

#[test]
fn bounded_symbolic_tag_lookup_ignores_unrelated_facts() {
    let costs = [16u64, 64, 256, 1024].map(|size| {
        let _session = crate::kernel::VerificationSession::enter();
        let tag = Bitvector32Term::Variable(Variable(980_021));
        let pointer = Pointer::symbolic(Variable(980_022));
        let mut context = PureFactContext::new()
            .assume_condition(
                ConditionTerm::signed_less_equal(0u32.into(), tag.clone()),
                true,
            )
            .assume_condition(
                ConditionTerm::signed_less_equal(tag.clone(), 1u32.into()),
                true,
            )
            .assume_condition(ConditionTerm::pointer_aligned(pointer.clone(), 8), true);
        for index in 0..size {
            context = context.assume_condition(
                ConditionTerm::uint64_equal(
                    Bitvector32Term::Variable(Variable(990_000 + index)),
                    Bitvector32Term::UInt64Constant(index),
                ),
                true,
            );
        }
        let cleared = Bitvector32Term::uint64_bitwise_and(
            Bitvector32Term::uint64_bitwise_or(
                Bitvector32Term::pointer_address(pointer.clone()),
                Bitvector32Term::UInt64FromInt32(Box::new(tag)),
            ),
            Bitvector32Term::UInt64Constant(!3),
        );
        let (form, work) = crate::instrumentation::measure_deterministic_work(|| {
            tagged_address_form(&cleared, &context, &mut UsedFacts::new())
        });
        assert_eq!(form.unwrap().pointer, pointer);
        work
    });
    assert!(
        costs[0] > 0 && costs.iter().all(|work| *work <= costs[0] + 32),
        "{costs:?}"
    );
}
