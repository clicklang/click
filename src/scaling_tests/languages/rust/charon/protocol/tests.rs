// Scaling tests of `src/languages/rust/charon/protocol.rs` (module `tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn next_dispatch_output_scales_with_protocol_count() {
    for (shared, count) in [false, true]
        .into_iter()
        .flat_map(|shared| [8, 128, 1024].map(|count| (shared, count)))
    {
        let mut blocks = Vec::new();
        for index in 0..count {
            let offset = index * 4;
            let mut added = protocol();
            if shared {
                added[0].statements = vec![S::SharedArrayNext {
                    iterator: "iter".into(),
                    option: "option".into(),
                }];
                if let T::If { condition, .. } = &mut added[1].terminator {
                    *condition = E::SharedArrayOptionTag {
                        option: "option".into(),
                    };
                }
            }
            for block in &mut added {
                match &mut block.terminator {
                    T::Goto { target } => *target += offset,
                    T::If {
                        then_target,
                        else_target,
                        ..
                    } => {
                        *then_target += offset;
                        *else_target += offset;
                    }
                    _ => (),
                }
            }
            blocks.extend(added);
        }
        let (result, work) =
            crate::instrumentation::measure_deterministic_work(|| split_next_branches(&mut blocks));
        result.unwrap();
        assert_eq!(work, count * 12);
        assert_eq!(blocks.len(), count * 6);
        assert_eq!(blocks.iter().flat_map(|b| &b.statements).count(), count * 2);
    }
}
