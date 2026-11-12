// Scaling tests of `src/languages/cpp/link.rs` (module `scaling_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;
use crate::languages::c::syntax::{C0Function, C0Type};

/// Linking charges one unit for each function, layout, record spelling and
/// library contract each source holds, whatever the other sources hold: a
/// declaration another source repeats is bound by name, not compared with
/// every function.
#[test]
fn linking_work_scales_with_the_functions_each_source_holds() {
    for size in [8, 32, 128, 512] {
        let functions = |prefix: &str| {
            (0..size)
                .map(|index| {
                    C0Function::external(C0Type::Void, format!("{prefix}{index:04}"), vec![])
                })
                .collect::<Vec<_>>()
        };
        let execution = |functions: Vec<C0Function>| PreparedExecution {
            functions,
            layouts: Default::default(),
            library_contracts: String::new(),
            record_spellings: Default::default(),
        };
        // The second source repeats every declaration of the first and adds
        // as many of its own.
        let first = execution(functions("shared_"));
        let mut both = functions("shared_");
        both.extend(functions("own_"));
        let second = execution(both);
        let (linked, work) = crate::instrumentation::measure_deterministic_work(|| {
            link(&[("first.cpp", &first), ("second.cpp", &second)])
        });
        assert_eq!(linked.unwrap().functions.len(), 2 * size);
        assert_eq!(work, 3 * size, "size {size}");
    }
}
