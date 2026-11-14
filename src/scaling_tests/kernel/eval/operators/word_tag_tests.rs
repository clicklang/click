// Selected checked-tag addition must not inspect unrelated assumptions.
use super::*;

#[test]
fn checked_word_tag_addition_ignores_unrelated_facts() {
    let costs = [4u64, 16, 64, 256].map(|size| {
        let _session = crate::kernel::VerificationSession::enter();
        let (bits, value) = word();
        let mut context = PureFactContext::new().assume_condition(
            ConditionTerm::uint64_equal(
                MachineTerm::uint64_bitwise_and(bits, MachineTerm::uint64_constant(1)),
                MachineTerm::uint64_constant(0),
            ),
            true,
        );
        for index in 0..size {
            context = context.assume_condition(
                ConditionTerm::uint64_equal(
                    MachineTerm::Variable(Variable(998_000 + index)),
                    MachineTerm::uint64_constant(index),
                ),
                true,
            );
        }
        let (paths, work) = crate::instrumentation::measure_deterministic_work(|| {
            apply_c_add(
                &ExecutionState::new(),
                value,
                ProgramValue::UInt64(MachineTerm::uint64_constant(1)),
                None,
                None,
                Vec::new().into(),
                Vec::new(),
                &context,
            )
        });
        assert!(matches!(&paths[0].outcome,
            ExpressionOutcome::Value(ProgramValue::PointerInteger(record))
                if matches!(record.kind, PointerIntegerKind::Word { changed_bits: 1 })));
        work
    });
    assert!(
        costs[0] > 0 && costs.iter().all(|work| *work <= costs[0] + 64),
        "{costs:?}"
    );
}

#[test]
fn commuted_word_tag_or_ignores_unrelated_facts() {
    let costs = [4u64, 16, 64, 256].map(|size| {
        let _session = crate::kernel::VerificationSession::enter();
        let (_, value) = word();
        let tag = MachineTerm::Variable(Variable(997_080));
        let tag_value =
            ProgramValue::UInt64(tag.clone()).complete_word(Pointer::symbolic(Variable(997_081)));
        let mut context = PureFactContext::new().assume_condition(
            ConditionTerm::uint64_less_equal(tag, MachineTerm::uint64_constant(1)),
            true,
        );
        for index in 0..size {
            context = context.assume_condition(
                ConditionTerm::uint64_equal(
                    MachineTerm::Variable(Variable(998_000 + index)),
                    MachineTerm::uint64_constant(index),
                ),
                true,
            );
        }
        let ProgramValue::PointerInteger(expected) = &value else {
            panic!("word carrier")
        };
        let (paths, work) = crate::instrumentation::measure_deterministic_work(|| {
            apply_c_bitwise_binary(
                tag_value,
                value.clone(),
                Vec::new().into(),
                Vec::new(),
                &context,
                BitwiseOperation::Or,
            )
        });
        assert!(matches!(&paths[0].outcome,
            ExpressionOutcome::Value(ProgramValue::PointerInteger(record))
                if record.pointer == expected.pointer
                    && matches!(record.kind, PointerIntegerKind::Word { changed_bits: 1 })));
        work
    });
    assert!(
        costs[0] > 0 && costs.iter().all(|work| *work <= costs[0] + 64),
        "{costs:?}"
    );
}

#[test]
fn tag_clearing_equations_ignore_unrelated_and_looser_bounds() {
    let costs = [4u64, 16, 64, 256].map(|size| {
        let _session = crate::kernel::VerificationSession::enter();
        let word = MachineTerm::Variable(Variable(997_090));
        let tag = MachineTerm::Variable(Variable(997_091));
        let mut context = PureFactContext::new().assume_condition(
            ConditionTerm::uint64_less_equal(tag.clone(), MachineTerm::uint64_constant(1)),
            true,
        );
        for index in 0..size {
            context = context
                .assume_condition(
                    ConditionTerm::uint64_equal(
                        MachineTerm::Variable(Variable(998_000 + index)),
                        MachineTerm::uint64_constant(index),
                    ),
                    true,
                )
                .assume_condition(
                    ConditionTerm::uint64_less_equal(
                        tag.clone(),
                        MachineTerm::uint64_constant(index + 8),
                    ),
                    true,
                );
        }
        let masked = MachineTerm::uint64_bitwise_and(
            MachineTerm::uint64_bitwise_or(word.clone(), tag),
            MachineTerm::uint64_constant(!3),
        );
        let (equation, work) = crate::instrumentation::measure_deterministic_work(|| {
            bounded_uint64_tag_equation(&masked, &context)
        });
        assert_eq!(
            equation,
            Some(ConditionTerm::uint64_equal(
                masked,
                MachineTerm::uint64_bitwise_and(word, MachineTerm::uint64_constant(!3))
            ))
        );
        work
    });
    assert!(
        costs[0] > 0 && costs.iter().all(|work| *work <= costs[0] + 64),
        "{costs:?}"
    );
}
