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
