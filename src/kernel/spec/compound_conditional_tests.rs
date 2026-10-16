use super::*;

#[test]
fn compound_guards_select_exact_values_and_keep_unknowns_undecided() {
    let a = ConditionTerm::Variable(Variable(701));
    let b = ConditionTerm::Variable(Variable(702));
    for conjunction in [false, true] {
        let left = Box::new(Proposition::ConditionIs(a.clone(), true));
        let right = Box::new(Proposition::ConditionIs(b.clone(), false));
        let guard = if conjunction {
            Proposition::And(left, right)
        } else {
            Proposition::Or(left, right)
        };
        let value = conditional_spec_value(&guard, int32(7), int32(9)).unwrap();
        let CValue::Int32(bits) = value else {
            panic!("int32 conditional");
        };
        let is_seven = ConditionTerm::equal(bits, Bitvector32Term::Constant(7));
        assert_eq!(PureFactContext::new().decide(&is_seven), None);
        for left in [false, true] {
            for right in [false, true] {
                let facts = PureFactContext::new()
                    .assume_proposition(Proposition::ConditionIs(a.clone(), left))
                    .assume_proposition(Proposition::ConditionIs(b.clone(), right));
                let expected = if conjunction {
                    left && !right
                } else {
                    left || !right
                };
                assert_eq!(facts.decide(&is_seven), Some(expected));
            }
        }
    }
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/spec/compound_conditional_tests.rs");
}
