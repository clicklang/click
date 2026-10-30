//! Trusted separation rules. Constructors retain exactly the written premises;
//! they do not search the fact store or inspect memory history.
use super::prelude::*;

pub(crate) fn prove_separation_restrict(
    left: CResource,
    right: CResource,
    left_part: CResource,
    right_part: CResource,
) -> Theorem {
    let premises = [
        Proposition::CResourceSeparate {
            left: Box::new(left.clone()),
            right: Box::new(right.clone()),
        },
        Proposition::CResourceContains {
            parent: Box::new(left),
            child: Box::new(left_part.clone()),
        },
        Proposition::CResourceContains {
            parent: Box::new(right),
            child: Box::new(right_part.clone()),
        },
    ];
    Theorem::new(premises.into_iter().rev().fold(
        Proposition::CResourceSeparate {
            left: Box::new(left_part),
            right: Box::new(right_part),
        },
        |body, premise| Proposition::Implies(Box::new(premise), Box::new(body)),
    ))
}
