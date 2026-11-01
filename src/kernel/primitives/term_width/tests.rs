use super::*;
use crate::kernel::CompareRelation;
use crate::kernel::binary_node;

fn boxed(term: Bitvector32Term) -> Box<Bitvector32Term> {
    Box::new(term)
}

#[test]
fn operator_families_imply_their_carrier() {
    let x = Bitvector32Term::Variable(Variable(1));
    assert_eq!(term_width(&x), Ok(None));
    assert_eq!(
        term_width(&binary_node!(
            Int32,
            Add,
            boxed(x.clone()),
            boxed(Bitvector32Term::Constant(1))
        )),
        Ok(Some(CarrierWidth::Bits32))
    );
    assert_eq!(
        term_width(&Bitvector32Term::Binary {
            format: MachineIntegerType::UInt64,
            op: MachineBinaryOp::Add,
            left: boxed(x.clone()),
            right: boxed(Bitvector32Term::UInt64Constant(1))
        }),
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
    let mixed = Bitvector32Term::Binary {
        format: MachineIntegerType::Int64,
        op: MachineBinaryOp::Add,
        left: boxed(Bitvector32Term::Constant(1)),
        right: boxed(Bitvector32Term::Int64Constant(2)),
    };
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
    assert_eq!(value_width_mismatch(&crate::kernel::int8(5)), None);
    assert_eq!(
        value_width_mismatch(&CValue::Int64(Bitvector32Term::Variable(Variable(4)))),
        None
    );
}

#[test]
fn a_comparison_takes_operands_of_the_width_it_names() {
    let wide = Bitvector32Term::Int64Constant(1);
    assert!(
        condition_width_mismatch(&ConditionTerm::Compare {
            format: MachineIntegerType::Int64,
            relation: CompareRelation::Equal,
            left: boxed(wide.clone()),
            right: boxed(Bitvector32Term::Variable(Variable(5)))
        })
        .is_none()
    );
    assert_eq!(
        condition_width_mismatch(&ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::Equal,
            left: boxed(Bitvector32Term::Constant(1)),
            right: boxed(wide)
        }),
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
    let below = ConditionTerm::Compare {
        format: MachineIntegerType::UInt64,
        relation: CompareRelation::LessThan,
        left: boxed(Bitvector32Term::Variable(i)),
        right: boxed(Bitvector32Term::Variable(n)),
    };
    assert_eq!(
        condition_variable_widths(&below),
        Ok(vec![(n, CarrierWidth::Bits64), (i, CarrierWidth::Bits64)])
    );
    // One variable at two widths within one condition.
    let mixed = ConditionTerm::Compare {
        format: MachineIntegerType::Int32,
        relation: CompareRelation::Equal,
        left: boxed(Bitvector32Term::Variable(n)),
        right: boxed(Bitvector32Term::UInt32From64(boxed(
            Bitvector32Term::Binary {
                format: MachineIntegerType::UInt64,
                op: MachineBinaryOp::Add,
                left: boxed(Bitvector32Term::Variable(n)),
                right: boxed(Bitvector32Term::UInt64Constant(1)),
            },
        ))),
    };
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
        ConditionTerm::Compare {
            format: MachineIntegerType::UInt64,
            relation: CompareRelation::LessThan,
            left: boxed(n.clone()),
            right: boxed(Bitvector32Term::UInt64Constant(10)),
        },
        true,
    );
    // The same variable in a 32-bit comparison of the same context.
    let _ = facts.assume_condition(
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::LessThan,
            left: boxed(n),
            right: boxed(Bitvector32Term::Constant(5)),
        },
        true,
    );
}

#[test]
fn separate_fact_contexts_may_use_one_variable_number_at_different_widths() {
    let n = Bitvector32Term::Variable(Variable(14));
    let _wide = PureFactContext::new().assume_condition(
        ConditionTerm::Compare {
            format: MachineIntegerType::UInt64,
            relation: CompareRelation::LessThan,
            left: boxed(n.clone()),
            right: boxed(Bitvector32Term::UInt64Constant(10)),
        },
        true,
    );
    let _narrow = PureFactContext::new().assume_condition(
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::LessThan,
            left: boxed(n),
            right: boxed(Bitvector32Term::Constant(5)),
        },
        true,
    );
}

#[test]
fn a_bool_constant_is_the_byte_zero_or_one() {
    let byte = |bits| Bitvector32Term::narrow_constant(MachineIntegerType::UInt8, bits);
    for in_range in [
        CValue::bool_constant(false),
        CValue::bool_constant(true),
        // A symbolic `Bool` carrier is kept in range by rule C1.
        CValue::Bool(Bitvector32Term::Variable(Variable(15))),
    ] {
        assert_eq!(
            narrow_constant_out_of_range(&in_range),
            None,
            "{in_range:?}"
        );
        assert_eq!(value_mismatch(&in_range), None, "{in_range:?}");
    }
    let out_of_range = CValue::Bool(byte(2));
    assert!(narrow_constant_out_of_range(&out_of_range).is_some());
    assert!(value_mismatch(&out_of_range).is_some());
    // A narrow value's constant is native: a 32-bit word in an 8- or 16-bit
    // value, a `Bool` among them, is a width mismatch, whatever its bits.
    let c = Bitvector32Term::Constant;
    for word in [
        CValue::Bool(c(1)),
        CValue::Int8(c(127)),
        CValue::UInt8(c(255)),
        CValue::Int16(c(-32768i32 as u32)),
        CValue::UInt16(c(65535)),
    ] {
        assert!(value_mismatch(&word).is_some(), "{word:?}");
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

/// Only the 32- and 64-bit formats have format-carrying operator nodes
/// (`design/machine-integers.md`, "Stage 3"; every operator of either
/// 32-bit format since "Every format its own nodes", step 4): the width
/// audit refuses a `Binary` or `Unary` node at any other format, whatever
/// its operands.
#[test]
fn a_format_carrying_operator_at_a_format_without_such_nodes_is_refused() {
    let x = boxed(Bitvector32Term::Variable(Variable(1)));
    // A narrow format has native sign-free operators (`narrow_tests`), but
    // no division; the 128-bit formats have no operators yet.
    for (format, op) in [
        (MachineIntegerType::Int8, MachineBinaryOp::Divide),
        (MachineIntegerType::UInt16, MachineBinaryOp::Remainder),
        (MachineIntegerType::Int128, MachineBinaryOp::Add),
        (MachineIntegerType::UInt128, MachineBinaryOp::Add),
    ] {
        let found = CarrierWidth::native(format);
        let binary = Bitvector32Term::Binary {
            format,
            op,
            left: x.clone(),
            right: x.clone(),
        };
        assert_eq!(
            term_width(&binary),
            Err(WidthMismatch {
                site: "format-carrying binary operator",
                expected: CarrierWidth::Bits64,
                found,
            }),
            "{format:?}"
        );
        let unary = Bitvector32Term::Unary {
            format,
            op: MachineUnaryOp::BitwiseNot,
            operand: x.clone(),
        };
        if format.format().bits() > 64 {
            assert_eq!(
                term_width(&unary),
                Err(WidthMismatch {
                    site: "format-carrying unary operator",
                    expected: CarrierWidth::Bits64,
                    found,
                }),
                "{format:?}"
            );
        } else {
            // A narrow complement is a native node of its width.
            assert_eq!(term_width(&unary), Ok(Some(found)), "{format:?}");
        }
        // The refusal reaches a condition that reads the node, so the
        // per-context audit of an assumed fact rejects it too.
        let condition = ConditionTerm::Compare {
            format: MachineIntegerType::Int64,
            relation: CompareRelation::LessThan,
            left: boxed(binary),
            right: boxed(Bitvector32Term::Int64Constant(0)),
        };
        assert!(condition_variable_widths(&condition).is_err(), "{format:?}");
    }
    for format in [MachineIntegerType::Int64, MachineIntegerType::UInt64] {
        let binary = Bitvector32Term::Binary {
            format,
            op: MachineBinaryOp::ShiftRight,
            left: x.clone(),
            right: boxed(Bitvector32Term::Constant(3)),
        };
        assert_eq!(term_width(&binary), Ok(Some(CarrierWidth::Bits64)));
    }
    for format in [MachineIntegerType::Int32, MachineIntegerType::UInt32] {
        let binary = Bitvector32Term::Binary {
            format,
            op: MachineBinaryOp::ShiftRight,
            left: x.clone(),
            right: boxed(Bitvector32Term::Constant(3)),
        };
        assert_eq!(term_width(&binary), Ok(Some(CarrierWidth::Bits32)));
    }
    for format in [MachineIntegerType::Int32, MachineIntegerType::UInt32] {
        let sum = Bitvector32Term::Binary {
            format,
            op: MachineBinaryOp::Add,
            left: x.clone(),
            right: x.clone(),
        };
        assert_eq!(term_width(&sum), Ok(Some(CarrierWidth::Bits32)));
        let complement = Bitvector32Term::Unary {
            format,
            op: MachineUnaryOp::BitwiseNot,
            operand: x.clone(),
        };
        assert_eq!(term_width(&complement), Ok(Some(CarrierWidth::Bits32)));
    }
}
