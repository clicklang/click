use super::*;

fn pointer_fact(left: &Pointer, right: &Pointer, equal: bool) -> Proposition {
    Proposition::ConditionIs(
        ConditionTerm::PointerEqual(Box::new(left.clone()), Box::new(right.clone())),
        equal,
    )
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/functions/composite_pointer_body_fact_tests.rs");
}
