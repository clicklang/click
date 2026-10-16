use super::*;

#[test]
fn nested_integer_conversions_keep_current_parameter_reads_visible() {
    let value = SpecIntegerExpression::Negate(Box::new(SpecIntegerExpression::FromMachine(
        Box::new(SpecExpression::CExpression(c_variable("parameter"))),
    )));
    let conversion = SpecExpression::IntegerToMachine {
        value: Box::new(value.clone()),
        destination: MachineIntegerType::Int32,
    };
    assert!(spec_reads_current_parameter(
        SpecNode::Expression(&conversion),
        "parameter"
    ));
    assert!(!spec_reads_current_parameter(
        SpecNode::Expression(&conversion),
        "other"
    ));
    let comparison = SpecProposition::IntegerComparison {
        left: SpecIntegerExpression::Term(IntegerTerm::constant_i64(0)),
        operator: IntegerComparisonOperator::Equal,
        right: value,
    };
    assert!(spec_reads_current_parameter(
        SpecNode::Proposition(&comparison),
        "parameter"
    ));
    assert!(!spec_reads_current_parameter(
        SpecNode::Proposition(&comparison),
        "other"
    ));
}
