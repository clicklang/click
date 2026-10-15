// Scaling tests of `src/surface/integer_conversions.rs` (module `tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn integer_conversion_aliases_preserve_shared_expression_scaling() {
    let mut measured = Vec::new();
    for depth in [8, 16, 32, 64] {
        let mut source =
            String::from("theorem aliases(x: int32) { let a0: Integer = to_integer(x);\n");
        for index in 1..=depth {
            source.push_str(&format!(
                "let a{index}: Integer = a{} + a{};\n",
                index - 1,
                index - 1
            ));
        }
        source.push_str(&format!(
            "requires a{depth} == a{depth}; ensures a{depth} == a{depth} by {{ assumption(); }} }}"
        ));
        let (result, work) =
            crate::instrumentation::measure_deterministic_work(|| verify_c0_sources(&source, &[]));
        result.unwrap_or_else(|error| panic!("depth {depth}: {}", error.message()));
        measured.push(work);
    }
    for pair in measured.windows(2) {
        assert!(
            pair[1] <= 3 * pair[0],
            "conversion aliases expanded their shared tree: {measured:?}"
        );
    }
}

#[test]
fn integer_function_let_aliases_preserve_shared_expression_scaling() {
    let mut measured = Vec::new();
    for depth in [8, 16, 32, 64] {
        let mut source = String::from(
            "function f(x: Integer, y: Integer) -> Integer { x + y }\n\
             theorem aliases(z: Integer) { let a0: Integer = z;\n",
        );
        for index in 1..=depth {
            source.push_str(&format!(
                "let a{index}: Integer = f(a{}, a{});\n",
                index - 1,
                index - 1
            ));
        }
        source.push_str(&format!(
            "requires a{depth} == a{depth}; ensures a{depth} == a{depth} by {{ assumption(); }} }}"
        ));
        let (result, work) =
            crate::instrumentation::measure_deterministic_work(|| verify_c0_sources(&source, &[]));
        result.unwrap_or_else(|error| panic!("depth {depth}: {}", error.message()));
        measured.push(work);
    }
    for pair in measured.windows(2) {
        assert!(
            pair[1] <= 3 * pair[0],
            "Integer aliases expanded: {measured:?}"
        );
    }
}

#[test]
fn deferred_integer_function_high_arity_scales_with_arguments() {
    let mut measured = Vec::new();
    for arity in [8, 16, 32, 64] {
        let parameters = (0..arity)
            .map(|index| format!("x{index}: int32"))
            .collect::<Vec<_>>()
            .join(", ");
        let arguments = (0..arity)
            .map(|index| format!("x{index}"))
            .collect::<Vec<_>>()
            .join(", ");
        let source = format!(
            "function mix({parameters}) -> Integer {{ to_integer(x0) }}\n\
             theorem call({parameters}) {{\n\
             ensures mix({arguments}) == mix({arguments}) by {{ simp(); }} }}"
        );
        let (result, work) =
            crate::instrumentation::measure_deterministic_work(|| verify_c0_sources(&source, &[]));
        result.unwrap_or_else(|error| panic!("arity {arity}: {}", error.message()));
        measured.push(work);
    }
    for pair in measured.windows(2) {
        assert!(
            pair[1] <= 3 * pair[0],
            "deferred arity expanded: {measured:?}"
        );
    }
}

#[test]
#[ignore = "nightly: 1.9s in the parallel gate"]
fn machine_integer_order_bridge_applications_scale_with_steps_and_unused_bounds() {
    for ty in ["int32", "int64", "uint64"] {
        let mut samples = Vec::new();
        for size in [4usize, 16, 64, 256] {
            let mut source = format!(
                "import click::integer; theorem bridge(x: {ty}, y: {ty}, z: {ty}) {{ requires to_integer(x) <= to_integer(y); "
            );
            for i in 0..size {
                source.push_str(&format!("requires to_integer(z) <= {i}; "));
            }
            source.push_str("ensures x <= y by { ");
            for _ in 0..size {
                source.push_str(&format!("have x <= y by {{ apply({ty}_to_integer_less_equal_implies_less_equal(x, y)) using {{ to_integer(x) <= to_integer(y); }} }} "));
            }
            source.push_str("assumption(); } }");
            let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                verify_c0_sources(&source, &[])
            });
            result.unwrap_or_else(|error| panic!("{ty}/{size}: {}", error.message()));
            samples.push(work);
        }
        for pair in samples.windows(2) {
            assert!(
                pair[1] <= pair[0] * 6,
                "bridge work grew faster than the proof: {ty}: {samples:?}"
            );
        }
    }
}

#[test]
#[ignore = "nightly: 1.7s in the parallel gate"]
fn int64_integer_operation_applications_scale_with_steps_and_unused_bounds() {
    for (name, op) in [
        ("click::integer::int64_add_to_integer", "+"),
        ("click::integer::int64_subtract_to_integer", "-"),
    ] {
        let guard = format!("defined(x {op} y)");
        let goal = format!("to_integer(x {op} y) == to_integer(x) {op} to_integer(y)");
        let mut samples = Vec::new();
        for size in [4usize, 16, 64, 256] {
            let mut source =
                format!("theorem exact(x: int64, y: int64, z: int64) {{ requires {guard}; ");
            for i in 0..size {
                source.push_str(&format!("requires to_integer(z) <= {i}; "));
            }
            source.push_str(&format!("ensures {goal} by {{ "));
            for _ in 0..size {
                source.push_str(&format!(
                    "have {goal} by {{ apply({name}(x, y)) using {{ {guard}; }} }} "
                ));
            }
            source.push_str("assumption(); } }");
            let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                verify_c0_sources(&source, &[])
            });
            result.unwrap_or_else(|error| panic!("{name}/{size}: {}", error.message()));
            samples.push(work);
        }
        for pair in samples.windows(2) {
            assert!(pair[1] <= pair[0] * 6, "{name}: {samples:?}");
        }
    }
}

#[test]
#[ignore = "nightly: 0.8s in the parallel gate"]
fn opaque_product_arithmetic_scales_with_steps_and_unused_bounds() {
    let goal = "q * d <= n";
    let mut samples = Vec::new();
    for size in [4usize, 16, 64, 256] {
        let mut source = String::from(
            "theorem bound(n: Integer, q: Integer, d: Integer, r: Integer, z: Integer) { requires n == q * d + r; requires 0 <= r; ",
        );
        for i in 0..size {
            source.push_str(&format!("requires z <= {i}; "));
        }
        source.push_str(&format!("ensures {goal} by {{ "));
        for _ in 0..size {
            source.push_str(&format!(
                "have {goal} by {{ arithmetic() using {{ n == q * d + r; 0 <= r; }} }} "
            ));
        }
        source.push_str("assumption(); } }");
        let (result, work) =
            crate::instrumentation::measure_deterministic_work(|| verify_c0_sources(&source, &[]));
        result.unwrap_or_else(|error| panic!("{size}: {}", error.message()));
        samples.push(work);
    }
    for pair in samples.windows(2) {
        assert!(pair[1] <= pair[0] * 6, "{samples:?}");
    }
}

#[test]
#[ignore = "nightly: 0.5s in the parallel gate"]
fn integer_multiply_add_applications_scale_with_steps_and_unused_bounds() {
    let goal = "(a + b) * c == a * c + b * c";
    let mut samples = Vec::new();
    for size in [4usize, 16, 64, 256] {
        let mut source = String::from(
            "import click::integer; theorem distribute(a: Integer, b: Integer, c: Integer, z: Integer) { ",
        );
        for i in 0..size {
            source.push_str(&format!("requires z <= {i}; "));
        }
        source.push_str(&format!("ensures {goal} by {{ "));
        for _ in 0..size {
            source.push_str(&format!(
                "have {goal} by {{ apply(integer_multiply_add(a, b, c)); }} "
            ));
        }
        source.push_str("assumption(); } }");
        let (result, work) =
            crate::instrumentation::measure_deterministic_work(|| verify_c0_sources(&source, &[]));
        result.unwrap_or_else(|error| panic!("{size}: {}", error.message()));
        samples.push(work);
    }
    for pair in samples.windows(2) {
        assert!(pair[1] <= pair[0] * 6, "{samples:?}");
    }
}

#[test]
#[ignore = "nightly: 0.8s in the parallel gate"]
fn integer_truncation_applications_scale_with_steps_and_unused_bounds() {
    let goal = "n == truncating_quotient(n, d) * d + truncating_remainder(n, d)";
    let mut samples = Vec::new();
    for size in [4usize, 16, 64, 256] {
        let mut source = String::from(
            "import click::integer; theorem law(n: Integer, d: Integer, z: Integer) { requires d != 0; ",
        );
        for i in 0..size {
            source.push_str(&format!("requires z <= {i}; "));
        }
        source.push_str(&format!("ensures {goal} by {{ "));
        for _ in 0..size {
            source.push_str(&format!(
                "have {goal} by {{ apply(integer_truncation_identity(n, d)) using {{ d != 0; }} }} "
            ));
        }
        source.push_str("assumption(); } }");
        let (result, work) =
            crate::instrumentation::measure_deterministic_work(|| verify_c0_sources(&source, &[]));
        result.unwrap_or_else(|error| panic!("{size}: {}", error.message()));
        samples.push(work);
    }
    for pair in samples.windows(2) {
        assert!(pair[1] <= pair[0] * 6, "{samples:?}");
    }
}

#[test]
#[ignore = "nightly: 0.7s in the parallel gate"]
fn multiply_order_applications_scale_with_explicit_inputs() {
    let mut samples = Vec::new();
    for size in [4usize, 16, 64, 256] {
        let mut source = String::from(
            "import click::integer; theorem order(a: Integer,b: Integer,c: Integer,z: Integer) { requires a <= b; requires 0 <= c; ",
        );
        for i in 0..size {
            source.push_str(&format!("requires z <= {i}; "));
        }
        source.push_str("ensures a * c <= b * c by { ");
        for _ in 0..size {
            source.push_str("have a * c <= b * c by { apply(integer_multiply_order_nonnegative(a,b,c)) using { a <= b; 0 <= c; } } ");
        }
        source.push_str("assumption(); } }");
        let (result, work) =
            crate::instrumentation::measure_deterministic_work(|| verify_c0_sources(&source, &[]));
        result.unwrap();
        samples.push(work);
    }
    for pair in samples.windows(2) {
        assert!(pair[1] <= pair[0] * 6, "{samples:?}");
    }
}

#[test]
#[ignore = "nightly: 0.8s in the parallel gate"]
fn scaled_quotient_applications_scale_with_steps_and_unused_bounds() {
    let mut samples = Vec::new();
    for size in [4usize, 16, 64, 256] {
        let mut source = String::from(
            "import click::integer; theorem lower(n: Integer, d: Integer, b: Integer, z: Integer) { requires d != 0; requires 1 <= d; requires b * d <= n; ",
        );
        for i in 0..size {
            source.push_str(&format!("requires z <= {i}; "));
        }
        source.push_str("ensures b <= truncating_quotient(n, d) by { ");
        for _ in 0..size {
            source.push_str("have b <= truncating_quotient(n, d) by { apply(integer_positive_divisor_quotient_lower(n, d, b)) using { d != 0; 1 <= d; b * d <= n; } } ");
        }
        source.push_str("assumption(); } }");
        let (checked, work) =
            crate::instrumentation::measure_deterministic_work(|| verify_c0_sources(&source, &[]));
        checked.unwrap_or_else(|error| panic!("{size}: {}", error.message()));
        samples.push(work);
    }
    for pair in samples.windows(2) {
        assert!(pair[1] <= pair[0] * 6, "{samples:?}");
    }
}

#[test]
#[ignore = "nightly: 1.0s in the parallel gate"]
fn correction_endpoint_applications_scale_with_steps_and_unused_bounds() {
    let mut samples = Vec::new();
    for size in [4usize, 16, 64, 256] {
        let mut source = String::from(
            "import click::integer; theorem correction(n: Integer, d: Integer, q: Integer, r: Integer, b: Integer, z: Integer) { requires b <= q; requires b * d <= n; requires n == q * d + r; requires r < 0; ",
        );
        for i in 0..size {
            source.push_str(&format!("requires z <= {i}; "));
        }
        source.push_str("ensures b + 1 <= q by { ");
        for _ in 0..size {
            source.push_str("have b + 1 <= q by { apply(integer_lower_correction_bound(n, d, q, r, b)) using { b <= q; b * d <= n; n == q * d + r; r < 0; } } ");
        }
        source.push_str("assumption(); } }");
        let (checked, work) =
            crate::instrumentation::measure_deterministic_work(|| verify_c0_sources(&source, &[]));
        checked.unwrap_or_else(|error| panic!("{size}: {}", error.message()));
        samples.push(work);
    }
    for pair in samples.windows(2) {
        assert!(pair[1] <= pair[0] * 6, "{samples:?}");
    }
}

#[test]
#[ignore = "nightly: 0.7s in the parallel gate"]
fn normalized_opposite_bound_certificates_scale_with_steps_and_unused_facts() {
    let mut samples = Vec::new();
    for size in [4usize, 16, 64, 256] {
        let mut source = String::from(
            "theorem pinned(x: Integer, b: Integer, z: Integer) { requires b <= x; requires not (b + 1 <= x); ",
        );
        for i in 0..size {
            source.push_str(&format!("requires z <= {i}; "));
        }
        source.push_str("ensures x == b by { ");
        for _ in 0..size {
            source.push_str("have x == b by { arithmetic() using { b <= x; not (b + 1 <= x); } } ");
        }
        source.push_str("assumption(); } }");
        let (checked, work) =
            crate::instrumentation::measure_deterministic_work(|| verify_c0_sources(&source, &[]));
        checked.unwrap_or_else(|error| panic!("{size}: {}", error.message()));
        samples.push(work);
    }
    for pair in samples.windows(2) {
        assert!(pair[1] <= pair[0] * 6, "{samples:?}");
    }
}
