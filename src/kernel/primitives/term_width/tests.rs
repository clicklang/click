use super::*;

fn boxed(term: Bitvector32Term) -> Box<Bitvector32Term> {
    Box::new(term)
}

#[test]
fn operator_families_imply_their_carrier() {
    let x = Bitvector32Term::Variable(Variable(1));
    assert_eq!(term_width(&x), Ok(None));
    assert_eq!(
        term_width(&Bitvector32Term::Add(
            boxed(x.clone()),
            boxed(Bitvector32Term::Constant(1))
        )),
        Ok(Some(CarrierWidth::Bits32))
    );
    assert_eq!(
        term_width(&Bitvector32Term::UInt64Add(
            boxed(x.clone()),
            boxed(Bitvector32Term::UInt64Constant(1))
        )),
        Ok(Some(CarrierWidth::Bits64))
    );
    assert_eq!(
        term_width(&Bitvector32Term::Int64From32(boxed(
            Bitvector32Term::Constant(7)
        ))),
        Ok(Some(CarrierWidth::Bits64))
    );
    assert_eq!(
        term_width(&Bitvector32Term::MachineIntegerCast {
            value: boxed(Bitvector32Term::UInt64Constant(7)),
            source: MachineIntegerType::UInt64,
            destination: MachineIntegerType::UInt128,
        }),
        Ok(Some(CarrierWidth::Bits128))
    );
}

#[test]
fn an_operand_of_the_wrong_width_is_reported_where_it_meets_its_operator() {
    let mixed = Bitvector32Term::Int64Add(
        boxed(Bitvector32Term::Constant(1)),
        boxed(Bitvector32Term::Int64Constant(2)),
    );
    assert_eq!(
        term_width(&mixed),
        Err(WidthMismatch {
            site: "64-bit operator",
            expected: CarrierWidth::Bits64,
            found: CarrierWidth::Bits32,
        })
    );
    let arms = Bitvector32Term::If {
        condition: Box::new(ConditionTerm::Variable(Variable(3))),
        then_term: boxed(Bitvector32Term::Constant(0)),
        else_term: boxed(Bitvector32Term::UInt64Constant(0)),
    };
    assert!(term_width(&arms).is_err());
}

#[test]
fn a_value_tag_and_its_term_agree_on_the_carrier() {
    assert_eq!(
        value_width_mismatch(&CValue::UInt64(Bitvector32Term::Constant(0))),
        Some(WidthMismatch {
            site: "CValue::UInt64",
            expected: CarrierWidth::Bits64,
            found: CarrierWidth::Bits32,
        })
    );
    assert_eq!(
        value_width_mismatch(&CValue::UInt64(Bitvector32Term::UInt64Constant(0))),
        None
    );
    // Narrow values ride in the 32-bit carrier.
    assert_eq!(
        value_width_mismatch(&CValue::Int8(Bitvector32Term::Constant(5))),
        None
    );
    assert_eq!(
        value_width_mismatch(&CValue::Int64(Bitvector32Term::Variable(Variable(4)))),
        None
    );
}

#[test]
fn a_comparison_takes_operands_of_the_width_it_names() {
    let wide = Bitvector32Term::Int64Constant(1);
    assert!(
        condition_width_mismatch(&ConditionTerm::Bitvector64Equal(
            boxed(wide.clone()),
            boxed(Bitvector32Term::Variable(Variable(5)))
        ))
        .is_none()
    );
    assert_eq!(
        condition_width_mismatch(&ConditionTerm::Bitvector32Equal(
            boxed(Bitvector32Term::Constant(1)),
            boxed(wide)
        )),
        Some(WidthMismatch {
            site: "32-bit comparison",
            expected: CarrierWidth::Bits32,
            found: CarrierWidth::Bits64,
        })
    );
}

#[test]
fn a_condition_reports_each_variable_at_the_width_it_is_used() {
    let n = Variable(11);
    let i = Variable(12);
    let below = ConditionTerm::Bitvector64UnsignedLessThan(
        boxed(Bitvector32Term::Variable(i)),
        boxed(Bitvector32Term::Variable(n)),
    );
    assert_eq!(
        condition_variable_widths(&below),
        Ok(vec![(n, CarrierWidth::Bits64), (i, CarrierWidth::Bits64)])
    );
    // One variable at two widths within one condition.
    let mixed = ConditionTerm::Bitvector32Equal(
        boxed(Bitvector32Term::Variable(n)),
        boxed(Bitvector32Term::UInt32From64(boxed(
            Bitvector32Term::UInt64Add(
                boxed(Bitvector32Term::Variable(n)),
                boxed(Bitvector32Term::UInt64Constant(1)),
            ),
        ))),
    );
    assert_eq!(
        condition_variable_widths(&mixed),
        Err(variable_conflict(
            CarrierWidth::Bits32,
            CarrierWidth::Bits64
        ))
    );
}

#[test]
#[cfg_attr(
    debug_assertions,
    should_panic(expected = "a variable used at another width")
)]
fn one_fact_context_keeps_a_variable_at_one_width() {
    let n = Bitvector32Term::Variable(Variable(13));
    let facts = PureFactContext::new().assume_condition(
        ConditionTerm::Bitvector64UnsignedLessThan(
            boxed(n.clone()),
            boxed(Bitvector32Term::UInt64Constant(10)),
        ),
        true,
    );
    // The same variable in a 32-bit comparison of the same context.
    let _ = facts.assume_condition(
        ConditionTerm::Bitvector32SignedLessThan(boxed(n), boxed(Bitvector32Term::Constant(5))),
        true,
    );
}

#[test]
fn separate_fact_contexts_may_use_one_variable_number_at_different_widths() {
    let n = Bitvector32Term::Variable(Variable(14));
    let _wide = PureFactContext::new().assume_condition(
        ConditionTerm::Bitvector64UnsignedLessThan(
            boxed(n.clone()),
            boxed(Bitvector32Term::UInt64Constant(10)),
        ),
        true,
    );
    let _narrow = PureFactContext::new().assume_condition(
        ConditionTerm::Bitvector32SignedLessThan(boxed(n), boxed(Bitvector32Term::Constant(5))),
        true,
    );
}

#[test]
fn a_narrow_constant_stays_inside_its_type() {
    let c = Bitvector32Term::Constant;
    for in_range in [
        CValue::Bool(c(1)),
        CValue::Int8(c(-128i32 as u32)),
        CValue::Int8(c(127)),
        CValue::UInt8(c(255)),
        CValue::Int16(c(-32768i32 as u32)),
        CValue::UInt16(c(65535)),
        // A symbolic narrow value is kept in range by its path facts.
        CValue::UInt8(Bitvector32Term::Variable(Variable(15))),
    ] {
        assert_eq!(
            narrow_constant_out_of_range(&in_range),
            None,
            "{in_range:?}"
        );
    }
    for out_of_range in [
        CValue::Bool(c(2)),
        CValue::Int8(c(128)),
        CValue::Int8(c(-129i32 as u32)),
        CValue::UInt8(c(256)),
        // A negative int8 must be sign-extended, not zero-extended.
        CValue::Int8(c(0xff)),
        CValue::UInt16(c(65536)),
    ] {
        assert!(
            narrow_constant_out_of_range(&out_of_range).is_some(),
            "{out_of_range:?}"
        );
    }
}

/// The same order questions decide alike over `int32`, `int64` and
/// `uint64`: a chain, a chain to a constant bound, and a chain with a gap.
#[test]
fn order_chains_decide_alike_at_every_width() {
    type Less = fn(Bitvector32Term, Bitvector32Term) -> ConditionTerm;
    let widths: [(Less, fn(u64) -> Bitvector32Term); 3] = [
        (ConditionTerm::signed_less_than, |n| {
            Bitvector32Term::Constant(n as u32)
        }),
        (ConditionTerm::int64_signed_less_than, |n| {
            Bitvector32Term::Int64Constant(n as i64)
        }),
        (
            ConditionTerm::uint64_less_than,
            Bitvector32Term::UInt64Constant,
        ),
    ];
    for (base, (less, constant)) in widths.into_iter().enumerate() {
        let v = |n: u64| Bitvector32Term::Variable(Variable(997_000 + 100 * base as u64 + n));
        let mut facts = PureFactContext::new();
        for i in 0..3 {
            facts = facts.assume_condition(less(v(i), v(i + 1)), true);
        }
        facts = facts.assume_condition(less(v(3), constant(100)), true);
        // A second chain with a gap: v(10) < v(11), v(12) < v(13).
        facts = facts
            .assume_condition(less(v(10), v(11)), true)
            .assume_condition(less(v(12), v(13)), true);
        assert_eq!(
            facts.decide(&less(v(0), v(3))),
            Some(true),
            "chain at {base}"
        );
        assert_eq!(
            facts.decide(&less(v(0), constant(100))),
            Some(true),
            "bound at {base}"
        );
        assert_eq!(
            facts.decide(&less(v(3), v(0))),
            Some(false),
            "reversed at {base}"
        );
        assert_eq!(facts.decide(&less(v(10), v(13))), None, "gap at {base}");
    }
}
