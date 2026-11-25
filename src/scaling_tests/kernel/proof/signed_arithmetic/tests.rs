// Scaling tests of `src/kernel/proof/signed_arithmetic.rs` (module `tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;
use crate::kernel::{MachineCastSpelling, OldMachineTerm};

#[test]
fn narrowed_variable_atom_identity_work_scales_linearly() {
    let mut previous = None;
    for size in [16usize, 64, 256, 1024] {
        let terms: Vec<_> = (0..size)
            .map(|index| {
                OldMachineTerm::legacy_cast(
                    MachineCastSpelling::UInt32From64,
                    Box::new(OldMachineTerm::Variable(Variable(index as u64))),
                )
            })
            .collect();
        let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
            for term in &terms {
                assert_eq!(SignedArithmeticAtom::from_term(term).unwrap().work(), 1);
            }
        });
        assert!(work > 0);
        if let Some(previous) = previous {
            assert!(work <= 4 * previous + 4);
        }
        previous = Some(work);
    }
}

#[test]
fn opaque_payload_work_scales_with_application_identity() {
    let mut measurements = Vec::new();
    for payload_size in [8usize, 16, 32, 64] {
        let term = OldMachineTerm::PureFunctionApplication {
            name: "opaque".repeat(payload_size),
            arguments: (0..payload_size)
                .map(|index| OldMachineTerm::Variable(Variable(index as u64)))
                .collect(),
        };
        let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
            assert!(!crate::instrumentation::deadline_exceeded_with_work(
                signed_term_work(&term,)
            ));
        });
        measurements.push(work);
    }
    for pair in measurements.windows(2) {
        assert!(
            pair[1] > pair[0],
            "opaque payloads must be charged by their full identity: {measurements:?}"
        );
        assert!(pair[1] <= 5 * pair[0], "{measurements:?}");
    }
}

#[test]
fn deep_opaque_payload_work_is_iterative_and_budgeted() {
    let mut term = x();
    for _ in 0..4096 {
        term = OldMachineTerm::PureFunctionApplication {
            name: "f".to_string(),
            arguments: vec![term],
        };
    }
    assert!(is_opaque_atom(&term));
    let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
        assert!(!crate::instrumentation::deadline_exceeded_with_work(
            signed_term_work(&term)
        ));
    });
    assert!(work > 4096);
}
