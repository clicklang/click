use super::*;

const HI: Variable = Variable(72_201);
const ACCUMULATOR: Variable = Variable(72_202);
const ITEM: Variable = Variable(72_203);

fn int32(term: Bitvector32Term) -> SpecExpression {
    SpecExpression::Value(CValue::Int32(term))
}

fn predecessor_of_hi() -> SpecExpression {
    SpecExpression::Subtract(
        Box::new(int32(Bitvector32Term::Variable(HI))),
        Box::new(int32(Bitvector32Term::Constant(1))),
    )
}

fn fold(
    start: SpecExpression,
    end: SpecExpression,
    initial: SpecIntegerExpression,
    body: SpecIntegerExpression,
) -> SpecIntegerExpression {
    SpecIntegerExpression::RangeFold {
        index: SpecIntegerRangeFoldIndex::Int32 {
            start: Box::new(start),
            end: Box::new(end),
        },
        initial: Box::new(initial),
        accumulator: ACCUMULATOR,
        item: ITEM,
        body: Box::new(body),
    }
}

fn zero() -> SpecIntegerExpression {
    SpecIntegerExpression::Term(IntegerTerm::constant_i64(0))
}

fn hi_is_positive() -> PureFactContext {
    PureFactContext::new().assume_proposition(Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(
            Bitvector32Term::Constant(1),
            Bitvector32Term::Variable(HI),
        ),
        true,
    ))
}

fn subtraction_is_defined() -> Proposition {
    Proposition::ConditionIs(
        ConditionTerm::Bitvector32SignedSubtractOverflows(
            Box::new(Bitvector32Term::Variable(HI)),
            Box::new(Bitvector32Term::Constant(1)),
        ),
        false,
    )
}

#[test]
fn endpoint_definedness_the_context_decides_is_discharged() {
    let expression = fold(
        int32(Bitvector32Term::Constant(0)),
        predecessor_of_hi(),
        zero(),
        zero(),
    );

    // Without the guard the capture is refused, and the refusal names the
    // endpoint rather than the constant initializer.
    let refusal = capture_spec_integer_value(
        &CState::default(),
        &expression,
        None,
        &PureFactContext::new(),
    )
    .expect_err("an endpoint of unknown definedness is not capturable");
    let SpecCaptureRefusal::Undischarged {
        subterm,
        proposition,
    } = refusal
    else {
        panic!("an undischarged evaluation condition must name its subterm");
    };
    assert_eq!(subterm, SpecCaptureSubterm::RangeEndpoint);
    assert_eq!(proposition, subtraction_is_defined());

    // The same capture succeeds once the context decides that condition.
    capture_spec_integer_value(&CState::default(), &expression, None, &hi_is_positive())
        .expect("an endpoint whose definedness the context proves is capturable");
}

#[test]
fn an_exactly_stated_endpoint_condition_is_discharged() {
    let expression = fold(
        int32(Bitvector32Term::Constant(0)),
        predecessor_of_hi(),
        zero(),
        zero(),
    );
    let stated = PureFactContext::new().assume_proposition(subtraction_is_defined());
    capture_spec_integer_value(&CState::default(), &expression, None, &stated)
        .expect("the exact stated condition discharges the endpoint path fact");
}

#[test]
fn an_initializer_condition_is_named_as_the_initializer() {
    let expression = fold(
        int32(Bitvector32Term::Constant(0)),
        int32(Bitvector32Term::Constant(0)),
        SpecIntegerExpression::FromMachine(Box::new(predecessor_of_hi())),
        zero(),
    );
    let refusal = capture_spec_integer_value(
        &CState::default(),
        &expression,
        None,
        &PureFactContext::new(),
    )
    .expect_err("an initializer of unknown definedness is not capturable");
    let SpecCaptureRefusal::Undischarged {
        subterm,
        proposition,
    } = refusal
    else {
        panic!("an undischarged evaluation condition must name its subterm");
    };
    assert_eq!(subterm, SpecCaptureSubterm::FoldInitializer);
    assert_eq!(proposition, subtraction_is_defined());
}
