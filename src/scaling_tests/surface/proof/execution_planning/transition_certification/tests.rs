use super::*;
use crate::kernel::{MemoryRange, OldConditionTerm, OldMachineTerm, Resource, Variable};

#[test]
fn stated_symbolic_write_separation_ignores_nearby_facts_and_aliases() {
    let write = Address::symbolic(Variable(70_100));
    let protected = Address::symbolic(Variable(70_101));
    let alias = Address::symbolic(Variable(70_102));
    let symbolic = |value| OldMachineTerm::Variable(Variable(value));
    let memory = |base: &Address, end| {
        Box::new(Resource::Memory(MemoryRange::new_with_element_width(
            base.clone(),
            0.into(),
            end,
            4,
        )))
    };
    let cell = memory(&write, 1.into());
    let separation = |left, right| Proposition::ResourceSeparate { left, right };
    let goal = separation(cell.clone(), memory(&protected, symbolic(70_104)));
    let fixed_goal = separation(cell.clone(), memory(&protected, 1.into()));
    let fixed_source = separation(
        Box::new(Resource::Memory(MemoryRange::new_with_element_width(
            alias.clone(),
            0.into(),
            4.into(),
            1,
        ))),
        memory(&protected, 1.into()),
    );
    let mut samples = Vec::new();
    for count in [4, 16, 64, 256] {
        let mut facts = PureFactContext::new().assume_condition(
            OldConditionTerm::address_equal(write.clone(), alias.clone()),
            true,
        );
        for candidate in 0..count {
            facts = facts.assume_condition(
                OldConditionTerm::address_equal(
                    write.clone(),
                    Address::symbolic(Variable(71_000 + candidate)),
                ),
                true,
            );
            facts = facts.assume_proposition(separation(
                cell.clone(),
                memory(&protected, symbolic(72_000 + candidate)),
            ));
        }
        let stated = facts.clone().assume_proposition(separation(
            memory(&protected, symbolic(70_104)),
            cell.clone(),
        ));
        let fixed = facts.clone().assume_proposition(fixed_source.clone());
        let mut cold = fixed.clone();
        for candidate in 0..count {
            cold = cold.assume_condition(
                OldConditionTerm::address_equal(
                    write.clone(),
                    Address::symbolic(Variable(73_000 + candidate)),
                ),
                true,
            );
        }
        let mut work = Vec::new();
        for (case, goal, context, expected) in [
            ("symbolic miss", &goal, &facts, false),
            ("symbolic reverse hit", &goal, &stated, true),
            ("fixed miss", &fixed_goal, &facts, false),
            ("indexed hit", &fixed_goal, &fixed, true),
            ("indexed hit after alias growth", &fixed_goal, &cold, true),
        ] {
            for _ in 0..2 {
                let (holds, units) = crate::instrumentation::measure_deterministic_work(|| {
                    states_write_separation(goal, context)
                });
                assert_eq!(holds, expected, "{case} at size {count}");
                work.push(units);
            }
        }
        samples.push((count, work));
    }
    assert!(
        samples.iter().all(|(_, work)| work
            .iter()
            .zip(&samples[0].1)
            .all(|(actual, first)| *actual <= first + 32)),
        "checking a fixed write inspected extra separations or aliases: {samples:?}"
    );
}
