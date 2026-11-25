use super::*;

fn pointer_fact(left: &Address, right: &Address, equal: bool) -> Proposition {
    Proposition::condition_is(
        OldConditionTerm::AddressEqual(Box::new(left.clone()), Box::new(right.clone())),
        equal,
    )
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/functions/composite_pointer_body_fact_tests.rs");
}
