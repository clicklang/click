// Scaling tests of `src/kernel/functions.rs` (module `composite_pointer_body_fact_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

// A fold's packed-word equation can use a new name for a checked copy.
// Rewriting that name must remain scoped, full-width, and independent
// of unrelated facts. No memory observation or ownership is invented.
#[test]
fn fold_copied_wide_word_preserves_scope_width_and_scales() {
    let _session = crate::kernel::VerificationSession::enter();
    let word = Bitvector32Term::Variable(Variable(710_000));
    let copied = Bitvector32Term::Variable(Variable(710_001));
    let changed = Bitvector32Term::Variable(Variable(710_002));
    let address = Bitvector32Term::PointerAddress(Box::new(Pointer::symbolic(Variable(710_003))));
    let packed = |word: &Bitvector32Term| {
        Proposition::ConditionIs(
            ConditionTerm::Bitvector64Equal(
                Box::new(word.clone()),
                Box::new(Bitvector32Term::UInt64Add(
                    Box::new(address.clone()),
                    Box::new(Bitvector32Term::UInt64BitwiseAnd(
                        Box::new(word.clone()),
                        Box::new(Bitvector32Term::UInt64Constant(1)),
                    )),
                )),
            ),
            true,
        )
    };
    let alias = Proposition::ConditionIs(
        ConditionTerm::Bitvector64Equal(Box::new(copied.clone()), Box::new(word.clone())),
        true,
    );
    // Force the selected-alias route rather than general condition reasoning.
    let parent = PureFactContext::new()
        .defer_non_exact_condition_reasoning()
        .assume_proposition(packed(&word));
    let context = parent.clone().assume_proposition(alias.clone());
    assert!(resource_body_fact_is_established(
        &context,
        &packed(&copied)
    ));
    assert!(!resource_body_fact_is_established(
        &parent,
        &packed(&copied)
    ));
    assert!(!resource_body_fact_is_established(
        &context,
        &packed(&changed)
    ));
    assert!(!resource_body_fact_is_established(
        &PureFactContext::new().assume_proposition(alias),
        &packed(&copied),
    ));
    let narrow = parent.clone().assume_proposition(Proposition::ConditionIs(
        ConditionTerm::Bitvector32Equal(Box::new(copied.clone()), Box::new(word.clone())),
        true,
    ));
    assert!(!resource_body_fact_is_established(
        &narrow,
        &packed(&copied)
    ));
    let mut previous = None;
    for count in [16_u64, 64, 256, 1024] {
        let mut padded = context.clone();
        for index in 0..count {
            padded = padded.assume_proposition(Proposition::ConditionIs(
                ConditionTerm::Bitvector64Equal(
                    Box::new(Bitvector32Term::Variable(Variable(720_000 + index))),
                    Box::new(Bitvector32Term::UInt64Constant(index)),
                ),
                true,
            ));
        }
        padded.build_stated_proposition_index();
        let (proved, work) = crate::instrumentation::measure_deterministic_work(|| {
            resource_body_fact_is_established(&padded, &packed(&copied))
        });
        assert!(proved);
        if let Some(previous) = previous {
            assert!(work <= previous + 64, "{count}: {work} after {previous}");
        }
        previous = Some(work);
    }
}

#[test]
fn fold_nonnull_fact_uses_an_exact_composite_pointer_alias() {
    let model = Pointer::symbolic(Variable(700));
    let program = Pointer {
        block: PointerBlock::Symbolic(Variable(701)),
        offset: PointerOffsetTerm::Int32Scaled {
            value: Box::new(Bitvector32Term::Variable(Variable(702))),
            byte_width: 4,
        },
    };
    let null = Pointer::null();
    let alias = pointer_fact(&model, &program, true);
    let nonnull = pointer_fact(&model, &null, false);
    let needed = pointer_fact(&program, &null, false);
    let context = PureFactContext::new()
        .assume_proposition(alias.clone())
        .assume_proposition(nonnull.clone());
    assert!(resource_body_fact_is_established(&context, &needed));
    assert!(!resource_body_fact_is_established(
        &context,
        &pointer_fact(&program, &null, true),
    ));
    assert!(!resource_body_fact_is_established(
        &PureFactContext::new().assume_proposition(alias.clone()),
        &needed,
    ));
    assert!(!resource_body_fact_is_established(
        &PureFactContext::new().assume_proposition(nonnull.clone()),
        &needed,
    ));
    let parent_fact = |pointer: &Pointer, value: u32| {
        Proposition::ConditionIs(
            ConditionTerm::Bitvector32Equal(
                Box::new(Bitvector32Term::ClickFunctionApplication {
                    name: "parent_is".into(),
                    arguments: vec![PureFunctionArgument::Value(CValue::typed_pointer(
                        pointer.clone(),
                        CType::Int32Pointer,
                    ))],
                }),
                Box::new(Bitvector32Term::Constant(value)),
            ),
            true,
        )
    };
    let model_parent = parent_fact(&model, 1);
    let needed_parent = parent_fact(&program, 1);
    let context = context.assume_proposition(model_parent.clone());
    assert!(resource_body_fact_is_established(&context, &needed_parent));
    assert!(!resource_body_fact_is_established(
        &context,
        &parent_fact(&program, 0)
    ));
    assert!(!resource_body_fact_is_established(
        &PureFactContext::new().assume_proposition(model_parent),
        &needed_parent,
    ));
    let mut work = Vec::new();
    for count in [16, 64, 256] {
        let mut padded = context.clone();
        for index in 0..count {
            padded = padded.assume_proposition(pointer_fact(
                &Pointer::symbolic(Variable(10_000 + index)),
                &Pointer::symbolic(Variable(20_000 + index)),
                true,
            ));
            padded = padded.assume_proposition(pointer_fact(
                &Pointer::symbolic(Variable(30_000 + index)),
                &null,
                true,
            ));
        }
        // Charge the deferred insertion of these new facts to building
        // the context, then measure only the fold's indexed query.
        padded.build_stated_proposition_index();
        let (proved, units) = crate::instrumentation::measure_deterministic_work(|| {
            let proved = resource_body_fact_is_established(&padded, &needed);
            assert!(resource_body_fact_is_established(&padded, &needed_parent));
            assert!(!resource_body_fact_is_established(
                &padded,
                &parent_fact(&program, 0)
            ));
            assert!(!resource_body_fact_is_established(
                &padded,
                &pointer_fact(&program, &null, true),
            ));
            proved
        });
        assert!(proved);
        work.push(units);
    }
    for pair in work.windows(2) {
        assert!(
            pair[1] <= pair[0] * 2 + 8,
            "unrelated aliases increased fold work: {work:?}"
        );
    }
}
