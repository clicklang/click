// Scaling tests of `src/surface/tests/tactic_tests/logical_tactics.rs`: deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn pure_witness_integer_aliases_keep_shared_term_scaling() {
    for function_backed in [false, true] {
        let mut measured = Vec::new();
        for depth in [8, 16, 32, 64] {
            let mut source = if function_backed {
                "function f(x: Integer, y: Integer) -> Integer { x + y }\n theorem aliases(x: Integer) { let a0: Integer = x;\n".to_owned()
            } else {
                "theorem aliases(x: int32) { let a0: Integer = to_integer(x);\n".to_owned()
            };
            for index in 1..=depth {
                let previous = index - 1;
                let value = if function_backed {
                    format!("f(a{previous}, a{previous})")
                } else {
                    format!("a{previous} + a{previous}")
                };
                source.push_str(&format!("let a{index}: Integer = {value};\n"));
            }
            source.push_str(&format!("ensures exists (q: Integer) {{ q == a{depth} }} by {{ witness {{ q: a{depth} }}; simp(); }} }}"));
            let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                verify_c0_sources(&source, &[])
            });
            result.unwrap_or_else(|error| {
                panic!(
                    "function backed {function_backed}, depth {depth}: {}",
                    error.message()
                )
            });
            measured.push(work);
        }
        for pair in measured.windows(2) {
            assert!(
                pair[1] <= 3 * pair[0],
                "witness aliases must retain shared terms: {measured:?}"
            );
        }
    }
}
