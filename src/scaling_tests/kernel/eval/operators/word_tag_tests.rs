// Selected checked-tag addition must not inspect unrelated assumptions.
use super::*;

#[test]
fn checked_word_tag_addition_ignores_unrelated_facts() {
    let costs = [4u64, 16, 64, 256].map(|size| {
        let _session = crate::kernel::VerificationSession::enter();
        let (bits, value) = word();
        let mut context = PureFactContext::new().assume_condition(
            ConditionTerm::uint64_equal(
                Bitvector32Term::uint64_bitwise_and(bits, Bitvector32Term::UInt64Constant(1)),
                Bitvector32Term::UInt64Constant(0),
            ),
            true,
        );
        for index in 0..size {
            context = context.assume_condition(
                ConditionTerm::uint64_equal(
                    Bitvector32Term::Variable(Variable(998_000 + index)),
                    Bitvector32Term::UInt64Constant(index),
                ),
                true,
            );
        }
        let (paths, work) = crate::instrumentation::measure_deterministic_work(|| {
            apply_c_add(
                &CState::new(),
                value,
                CValue::UInt64(Bitvector32Term::UInt64Constant(1)),
                None,
                None,
                Vec::new().into(),
                Vec::new(),
                &context,
            )
        });
        assert!(matches!(&paths[0].outcome,
            CExpressionOutcome::Value(CValue::PointerInteger(record))
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
        let tag = Bitvector32Term::Variable(Variable(997_080));
        let tag_value =
            CValue::UInt64(tag.clone()).complete_word(Pointer::symbolic(Variable(997_081)));
        let mut context = PureFactContext::new().assume_condition(
            ConditionTerm::uint64_less_equal(tag, Bitvector32Term::UInt64Constant(1)),
            true,
        );
        for index in 0..size {
            context = context.assume_condition(
                ConditionTerm::uint64_equal(
                    Bitvector32Term::Variable(Variable(998_000 + index)),
                    Bitvector32Term::UInt64Constant(index),
                ),
                true,
            );
        }
        let CValue::PointerInteger(expected) = &value else {
            panic!("word carrier")
        };
        let (paths, work) = crate::instrumentation::measure_deterministic_work(|| {
            apply_c_bitwise_binary(
                tag_value,
                value.clone(),
                Vec::new().into(),
                Vec::new(),
                &context,
                CBitwiseOperation::Or,
            )
        });
        assert!(matches!(&paths[0].outcome,
            CExpressionOutcome::Value(CValue::PointerInteger(record))
                if record.pointer == expected.pointer
                    && matches!(record.kind, PointerIntegerKind::Word { changed_bits: 1 })));
        work
    });
    assert!(
        costs[0] > 0 && costs.iter().all(|work| *work <= costs[0] + 64),
        "{costs:?}"
    );
}
