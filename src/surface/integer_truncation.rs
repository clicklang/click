//! Explicit, guarded mathematical truncation, separate from Integer `/` policy.
use super::*;

pub(super) fn is_integer_truncation(name: &str) -> bool {
    matches!(name, "truncating_quotient" | "truncating_remainder")
}

pub(super) fn integer_truncation_arguments<'a>(
    name: &str,
    arguments: &'a [ContractExpression],
) -> Result<(&'a ContractExpression, &'a ContractExpression), String> {
    let [left, right] = arguments else {
        return Err(format!("{name} expects two Integer arguments"));
    };
    Ok((left, right))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn verify(source: &str) {
        verify_c0_sources(source, &[]).unwrap_or_else(|e| panic!("{}\n{source}", e.message()));
    }

    #[test]
    fn integer_truncation_constants_and_full_width_signs_verify_and_expand() {
        for (term, expected) in [
            ("truncating_quotient(-7, 3)", "-2"),
            ("truncating_remainder(-7, 3)", "-1"),
            ("truncating_quotient(7, -3)", "-2"),
            ("truncating_remainder(7, -3)", "1"),
            (
                "truncating_quotient(-170141183460469231731687303715884105728, -1)",
                "170141183460469231731687303715884105728",
            ),
            (
                "truncating_remainder(340282366920938463463374607431768211455, 3)",
                "0",
            ),
        ] {
            let source =
                format!("theorem truncation() {{ ensures {term} == {expected} by simp; }}");
            verify(&source);
            let expanded =
                expand_c0_claim_source_by_label(&source, &[], "truncation.ensures_0").unwrap();
            verify(&expanded);
            assert!(
                verify_c0_sources(
                    &source.replace(&format!("== {expected}"), &format!("== ({expected}) + 1")),
                    &[]
                )
                .is_err()
            );
        }
    }

    #[test]
    fn integer_truncation_symbolic_domain_survives_proofs_and_expansion() {
        for function in ["truncating_quotient", "truncating_remainder"] {
            for expression in [
                format!("{function}(a, b)"),
                format!("0 * {function}(a, b)"),
                format!("{function}(a, b) * 0"),
                format!("{function}(a, b) - {function}(a, b)"),
            ] {
                let source = format!(
                    "theorem truncation(a: Integer, b: Integer) {{ requires b != 0; ensures {expression} == {expression} by simp; }}"
                );
                verify(&source);
                let expanded =
                    expand_c0_claim_source_by_label(&source, &[], "truncation.ensures_0").unwrap();
                verify(&expanded);
                assert!(
                    verify_c0_sources(&source.replace("requires b != 0;", ""), &[]).is_err(),
                    "{source}"
                );
            }
        }
    }

    #[test]
    fn integer_truncation_rejects_zero_wrong_types_arities_and_shadowing() {
        for expression in [
            "truncating_quotient(7, 0)",
            "truncating_remainder(7, 0)",
            "0 * truncating_quotient(7, 0)",
            "truncating_remainder(7, 0) * 0",
            "truncating_quotient()",
            "truncating_remainder(1)",
            "truncating_quotient(1, 2, 3)",
            "truncating_quotient(x, 3)",
            "truncating_remainder(true, 3)",
        ] {
            let source = format!(
                "theorem bad(x: int32) {{ ensures {expression} == {expression} by simp; }}"
            );
            assert!(verify_c0_sources(&source, &[]).is_err(), "{source}");
        }
        for function in ["truncating_quotient", "truncating_remainder"] {
            let source = format!("function {function}(a: Integer, b: Integer) -> Integer {{ a }}");
            assert!(verify_c0_sources(&source, &[]).is_err());
        }
    }

    #[test]
    fn integer_truncation_preserves_operand_native_definedness() {
        for function in ["truncating_quotient", "truncating_remainder"] {
            let expression = format!("{function}(to_integer(x + 1), 3)");
            let source = format!(
                "theorem truncation(x: int32) {{ requires defined(x + 1); ensures {expression} == {expression} by simp; }}"
            );
            verify(&source);
            let expanded =
                expand_c0_claim_source_by_label(&source, &[], "truncation.ensures_0").unwrap();
            verify(&expanded);
            assert!(
                verify_c0_sources(&source.replace("requires defined(x + 1);", ""), &[]).is_err()
            );
        }
    }
    #[test]
    fn integer_truncation_pure_aliases_preserve_shared_scaling() {
        let mut measured = Vec::new();
        for depth in [8, 16, 32, 64] {
            let mut source = String::from("theorem aliases(z: Integer) { let a0: Integer = z;\n");
            for index in 1..=depth {
                source.push_str(&format!("let a{index}: Integer = truncating_quotient(a{}, 3) + truncating_remainder(a{}, 3);\n", index - 1, index - 1));
            }
            source.push_str(&format!("requires a{depth} == a{depth}; ensures a{depth} == a{depth} by {{ assumption(); }} }}"));
            let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                verify_c0_sources(&source, &[])
            });
            result.unwrap_or_else(|error| panic!("depth {depth}: {}", error.message()));
            measured.push(work);
        }
        for pair in measured.windows(2) {
            assert!(
                pair[1] <= 3 * pair[0],
                "truncation aliases expanded: {measured:?}"
            );
        }
    }
    #[test]
    fn integer_truncation_function_arguments_keep_their_domain() {
        for helper in ["truncating_quotient", "truncating_remainder"] {
            let expression = format!("identity({helper}(a, b))");
            let source = format!(
                "function identity(x: Integer) -> Integer {{ x }} theorem client(a: Integer, b: Integer) {{ requires b != 0; ensures {expression} == {expression} by simp; }}"
            );
            verify(&source);
            let expanded =
                expand_c0_claim_source_by_label(&source, &[], "client.ensures_0").unwrap();
            verify(&expanded);
            assert!(verify_c0_sources(&source.replace("requires b != 0;", ""), &[]).is_err());
        }
        let too_wide = "theorem bad() { ensures to_int128(truncating_quotient(-170141183460469231731687303715884105728, -1)) == to_int128(truncating_quotient(-170141183460469231731687303715884105728, -1)) by simp; }";
        assert!(verify_c0_sources(too_wide, &[]).is_err());
    }
}
