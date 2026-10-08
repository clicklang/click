//! Hermetic re-export of the pinned Bitcoin Core v31.1 MoneyRange fixture.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use click::cli::read_click_project;
use click::instrumentation::{self, VerificationEvent};
use click::languages::cpp::{load_import, refresh_import};
use click::surface::{
    C0VerificationSession, expand_program_prepared_project_claim_source_by_label,
    expand_program_prepared_project_tactic_source_at,
    program_prepared_project_smart_tactic_source_sites,
    program_prepared_project_tactic_source_position, verify_program_prepared_project,
};
use sha2::{Digest, Sha256};

const ARCHIVE: &[u8] =
    include_bytes!("../integrations/bitcoin-core-money-range/input-closure.tar.gz");
const PROVENANCE: &str =
    include_str!("../integrations/bitcoin-core-money-range/fixture-provenance.json");
const COMMAND: &str =
    include_str!("../integrations/bitcoin-core-money-range/feerate-command.json.in");
const SIDECAR: &str = include_str!("../integrations/bitcoin-core-money-range/MoneyRange.click");

fn check_upstream_fee_frac(selected: &str, name: &str, source: &str) {
    check_upstream_cpp(
        selected,
        name,
        source,
        "bitcoin-src/src/util/feefrac.h",
        "sysroot/usr/include/x86_64-linux-gnu/bits/stdint-intn.h",
    );
}

fn check_upstream_cpp(
    selected: &str,
    name: &str,
    source: &str,
    logical_source: &str,
    integer_header: &str,
) {
    check_upstream_cpp_rounding_phase(selected, name, source, logical_source, integer_header, None);
}

#[derive(Clone, Copy, PartialEq)]
enum RoundingPhase {
    Tools,
    FullExpansion,
    Rejections,
    TransportRejections,
    NumeratorRejections,
    RoundingRejections,
    FitRejections,
    AuthorityRejections,
    AdjustedNumeratorRejections,
}

fn check_upstream_cpp_rounding_phase(
    selected: &str,
    name: &str,
    source: &str,
    logical_source: &str,
    integer_header: &str,
    phase: Option<RoundingPhase>,
) {
    assert_eq!(
        sha256(ARCHIVE),
        "fceeaef86784f820339f6dc3fc24992eb9c6bcf52edccbf6b7869d79296a3c7d"
    );
    let root = std::env::temp_dir().join(format!(
        "click-bitcoin-fee-frac-{name}-{}",
        std::process::id()
    ));
    fs::create_dir(&root).unwrap();
    let archive_path = root.join("input-closure.tar.gz");
    fs::write(&archive_path, ARCHIVE).unwrap();
    let result = Command::new("tar")
        .args([
            "-xzf",
            archive_path.to_str().unwrap(),
            "-C",
            root.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert!(result.status.success());
    assert_eq!(
        sha256(&fs::read(root.join("bitcoin-src/src/util/feefrac.h")).unwrap()),
        "213a97d13eb82b34831466febcff24f4c20879603f36fc6edd894b89000f7ab9"
    );
    assert_eq!(
        sha256(&fs::read(root.join("bitcoin-src/src/serialize.h")).unwrap()),
        "87a273aa8cb9aeea82cd8038bb85284a5782c8abc35f8c826eb60f1a01e06775"
    );
    fs::create_dir_all(root.join("bitcoin-build/src")).unwrap();
    let clang = pinned_clang();
    let database = COMMAND
        .replace("@ROOT@", root.to_str().unwrap())
        .replace("@CLANGXX@", clang.to_str().unwrap())
        .replace("@RESOURCE_DIR@", &output(&clang, &["-print-resource-dir"]));
    fs::write(root.join("compile_commands.json"), database).unwrap();
    let mut config = serde_json::json!({
        "schema": 6, "language": "c++", "standard": "c++20", "target": "x86_64-unknown-linux-gnu",
        "exceptions": true, "rtti": true,
        "exporter": std::env::var("CLICK_CPP_EXPORTER").unwrap(),
        "compilation_database": "compile_commands.json", "working_directory": ".",
        "source": "bitcoin-src/src/policy/feerate.cpp", "logical_source": logical_source,
        "dependencies": [integer_header, "sysroot/usr/include/x86_64-linux-gnu/bits/types.h"],
        "function": selected, "artifact": format!("{name}.click-cpp.json")
    });
    let evaluation_caller = name.starts_with("FeeFracEvaluate");
    let fee_rate_boundary = name == "CFeeRateGetFeeBoundary";
    let result_fit_div = name.starts_with("FeeFracDivResultFit");
    let bounded_div = name == "FeeFracDivBounded" || result_fit_div;
    if evaluation_caller
        || fee_rate_boundary
        || bounded_div
        || matches!(
            name,
            "FeeFracDivConstevalRefused" | "FeeFracDivImported" | "FeeFracDivBounded"
        )
    {
        const CHECK_HASH: &str = "82705f6150e57b4de9123d22b3820f60f6f75f58c1c8b9fbff78863afca816a7";
        let header = "bitcoin-src/src/util/check.h";
        assert_eq!(sha256(&fs::read(root.join(header)).unwrap()), CHECK_HASH);
        config["dependencies"] = serde_json::json!([
            header,
            integer_header,
            "sysroot/usr/include/x86_64-linux-gnu/bits/types.h"
        ]);
        config["library_assertions"] = serde_json::json!([{
            "kind": "checked_boolean_statement_with_consteval_metadata",
            "function": "inline_assertion_check", "header": header, "sha256": CHECK_HASH
        }]);
    }
    if evaluation_caller || fee_rate_boundary || bounded_div || name == "FeeFracDivImported" {
        const STRING_VIEW_HASH: &str =
            "9b1a575ffad1e8575cd6fc1c9a24b0cdde3793275be431726cc9c1b178a8733c";
        let header = "sysroot/usr/include/c++/12/string_view";
        assert_eq!(
            sha256(&fs::read(root.join(header)).unwrap()),
            STRING_VIEW_HASH
        );
        config["dependencies"]
            .as_array_mut()
            .unwrap()
            .push(header.into());
        config["dependencies"]
            .as_array_mut()
            .unwrap()
            .sort_by(|a, b| a.as_str().cmp(&b.as_str()));
        config["library_assertions"][0]["kind"] =
            "checked_boolean_statement_with_literal_metadata".into();
        config["library_assertions"][0]["literal_constructor"] = serde_json::json!({
            "function": "std::basic_string_view::basic_string_view", "header": header, "sha256": STRING_VIEW_HASH
        });
    }
    let config_path = root.join(format!("{name}.click.import.json"));
    fs::write(&config_path, serde_json::to_vec_pretty(&config).unwrap()).unwrap();
    let sidecar = root.join(format!("{name}.click"));
    fs::write(&sidecar, source).unwrap();
    let refreshed = refresh_import(&config_path);
    if fee_rate_boundary {
        let error =
            refreshed.expect_err("GetFee must retain the unsupported condition-call boundary");
        assert!(error.contains("unsupported expression"), "{error}");
        assert!(error.contains("feerate.cpp:23:19"), "{error}");
        assert!(error.len() < 8000);
        assert!(!root.join(format!("{name}.click-cpp.json")).exists());
        fs::remove_dir_all(root).unwrap();
        return;
    }
    if selected == "FeeFrac::Div" && !bounded_div && name != "FeeFracDivImported" {
        let error = refreshed.expect_err("the library Assume boundary must remain explicit");
        assert!(error.contains("export C++ source"), "{error}");
        if name == "FeeFracDivConstevalRefused" {
            assert!(
                error.contains("metadata argument 2 requires a forced consteval"),
                "the real template, Boolean temporary, and source_location must reach the string_view boundary: {error}"
            );
        }
        assert!(!root.join(format!("{name}.click-cpp.json")).exists());
        assert!(!root.join(format!("{name}.click.import.json.lock")).exists());
        fs::remove_dir_all(root).unwrap();
        return;
    }
    refreshed.unwrap_or_else(|error| panic!("{selected}: {error}"));
    let import = load_import(&config_path).unwrap();
    assert_eq!(import.export().preprocessor_files.len(), 320);
    if evaluation_caller {
        let instance = if selected.ends_with("Down") {
            "FeeFrac_EvaluateFee__bool_true"
        } else {
            "FeeFrac_EvaluateFee__bool_false"
        };
        assert_eq!(
            import
                .export()
                .reachable_functions
                .iter()
                .map(|f| f.name.as_str())
                .collect::<Vec<_>>(),
            vec![instance, "FeeFrac_Mul", "FeeFrac_Div"]
        );
    } else {
        assert!(import.export().reachable_functions.is_empty());
    }
    if selected == "FeeFrac::Div" && !bounded_div {
        use click::languages::cpp::{CppLibraryMetadata, CppLiteralMetadataBinding, CppStatement};
        let CppStatement::LibraryAssert { metadata, .. } = &import.export().function.body[0] else {
            panic!("retained upstream annotation")
        };
        assert!(matches!(metadata[0], CppLibraryMetadata::Consteval(_)));
        let CppLibraryMetadata::Literal(literal) = &metadata[1] else {
            panic!("retained runtime literal")
        };
        assert_eq!(literal.literal, "d > 0");
        assert_eq!(literal.record, "std::basic_string_view");
        assert!(literal.record_type.contains("std::basic_string_view<char>"));
        assert_eq!(literal.binding, CppLiteralMetadataBinding::Value);
        click::languages::cpp::lower_import(&import).unwrap();
        for (premises, diagnostic) in [
            ("", "assumed library contract"),
            ("requires d > 0;", "division by zero"),
            (
                "requires d > 0; requires to_integer(n) == 0; requires to_integer(d) != 0; requires to_integer(d) != -1;",
                "signed overflow",
            ),
        ] {
            let proof = format!(
                "verifying \"bitcoin-src/src/util/feefrac.h\"; int64 FeeFrac_Div(int128 n, int32 d, bool round_down) {{ {premises} ensures 0 == 0; }} by {{ execute(); simp(); }}"
            );
            let parsed = read_click_project(&sidecar, &proof).unwrap();
            let error = verify_program_prepared_project(&parsed, &import).unwrap_err();
            assert!(error.message().contains(diagnostic), "{}", error.message());
            assert!(error.message().len() < 8000);
            if premises.is_empty() {
                assert!(error.message().contains("literal constructor"));
            }
        }
        // Derive the wide observer guards from the real narrow divisor
        // precondition. Execution must advance to the still-unproved narrow
        // correction; no wide guard is assumed in the contract.
        let guard_proof = r#"verifying "bitcoin-src/src/util/feefrac.h";
int64 FeeFrac_Div(int128 n, int32 d, bool round_down) {
    requires d > 0;
    ensures 0 == 0;
} by {
    have 1 <= d by { arithmetic() using { d > 0; } }
    apply(int32_less_equal_to_integer(1, d));
    have to_integer(d) != 0 by { arithmetic_certificate special {
        premise 0: 1 <= to_integer(d) => 1 <= to_integer(d);
        integer_bound_exclusion bounds [0] => to_integer(d) != 0;
        conclusion 0;
    } }
    have to_integer(d) != -1 by { arithmetic_certificate special {
        premise 0: 1 <= to_integer(d) => 1 <= to_integer(d);
        integer_bound_exclusion bounds [0] => to_integer(d) != -1;
        conclusion 0;
    } }
    execute(); simp();
}"#;
        let parsed = read_click_project(&sidecar, guard_proof).unwrap();
        let error = verify_program_prepared_project(&parsed, &import).unwrap_err();
        assert!(
            error.message().contains("signed overflow"),
            "{}",
            error.message()
        );
        assert!(
            !error.message().contains("division by zero"),
            "{}",
            error.message()
        );
        assert!(error.message().len() < 8000);
        fs::remove_dir_all(root).unwrap();
        return;
    }
    let project = read_click_project(&sidecar, source).unwrap();
    if matches!(phase, None | Some(RoundingPhase::Tools)) {
        verify_program_prepared_project(&project, &import)
            .unwrap_or_else(|error| panic!("{selected}: {}", error.message()));
    }
    if matches!(phase, None | Some(RoundingPhase::Tools))
        && matches!(
            selected,
            "GetSizeOfCompactSize" | "FeeFrac::Mul" | "FeeFrac::Div"
        )
    {
        let sites = program_prepared_project_smart_tactic_source_sites(&project, &import).unwrap();
        let first = sites.first().unwrap();
        let position = program_prepared_project_tactic_source_position(
            &project,
            &import,
            &first.claim_label,
            first.source_index,
        )
        .unwrap();
        let expanded = expand_program_prepared_project_tactic_source_at(
            &project,
            &import,
            position.line,
            position.column,
        )
        .unwrap();
        let rewritten = project.with_entry_source(expanded.clone());
        verify_program_prepared_project(&rewritten, &import)
            .expect("expanded upstream proof reverifies");
        let (session, _) =
            C0VerificationSession::new_program_prepared_project(&project, &import).unwrap();
        let sites =
            program_prepared_project_smart_tactic_source_sites(&rewritten, &import).unwrap();
        let first = sites.first().unwrap();
        let position = program_prepared_project_tactic_source_position(
            &rewritten,
            &import,
            &first.claim_label,
            first.source_index,
        )
        .unwrap();
        session
            .verify_at_project(&expanded, position.line, position.column)
            .expect("upstream retained audit agrees");
        let false_source = source
            .replace("ensures 0 == 0;", "ensures 0 == 1;")
            .replace(
                "ensures -9223372036854775808 <= to_integer(result);",
                "ensures 9223372036854775807 <= to_integer(result);",
            )
            .replace("ensures result ==", "ensures result !=")
            .replace(
                "ensures to_integer(result) ==",
                "ensures to_integer(result) !=",
            );
        let false_project = read_click_project(&sidecar, &false_source).unwrap();
        let Err(error) = verify_program_prepared_project(&false_project, &import) else {
            panic!("false upstream claim must be refused");
        };
        assert!(
            error.message().contains("unclosed goal"),
            "{}",
            error.message()
        );
    }

    if evaluation_caller && phase == Some(RoundingPhase::Tools) {
        let label = format!("{}.ensures_0", selected.replace("::", "_"));
        let expanded =
            expand_program_prepared_project_claim_source_by_label(&project, &import, &label)
                .unwrap();
        verify_program_prepared_project(&project.with_entry_source(expanded), &import).unwrap();
    }
    if evaluation_caller
        && (name.ends_with("Negative")
            || name.ends_with("PositiveWide")
            || name.ends_with("SymbolicFast")
            || name.ends_with("Unified"))
        && phase == Some(RoundingPhase::FullExpansion)
    {
        let instance = if selected.ends_with("Down") {
            "true"
        } else {
            "false"
        };
        let expanded = expand_program_prepared_project_claim_source_by_label(
            &project,
            &import,
            &format!("FeeFrac_EvaluateFee__bool_{instance}.ensures_0"),
        )
        .unwrap();
        let rewritten = project.with_entry_source(expanded.clone());
        verify_program_prepared_project(&rewritten, &import).unwrap();
        let (session, _) =
            C0VerificationSession::new_program_prepared_project(&project, &import).unwrap();
        let position = program_prepared_project_tactic_source_position(
            &rewritten,
            &import,
            &format!("FeeFrac_EvaluateFee__bool_{instance}.contract"),
            0,
        )
        .unwrap();
        session
            .verify_at_project(&expanded, position.line, position.column)
            .unwrap();
    }
    if evaluation_caller
        && matches!(
            phase,
            Some(
                RoundingPhase::Rejections
                    | RoundingPhase::TransportRejections
                    | RoundingPhase::NumeratorRejections
                    | RoundingPhase::RoundingRejections
                    | RoundingPhase::FitRejections
                    | RoundingPhase::AuthorityRejections
                    | RoundingPhase::AdjustedNumeratorRejections
            )
        )
    {
        let hostile = if name.contains("ResultFit") && name.ends_with("SymbolicFast") {
            let down = selected.ends_with("Down");
            let fit = if down {
                "requires to_integer(self->fee) * to_integer(at_size) < 9223372036854775808 * to_integer(self->size);"
            } else {
                "requires to_integer(self->fee) * to_integer(at_size) <= 9223372036854775807 * to_integer(self->size);"
            };
            if phase == Some(RoundingPhase::Rejections) {
                vec![
                    source.replace("views self->size;", ""),
                    source.replace("requires self->size > 0;", ""),
                    source.replace("requires 0 <= at_size;", ""),
                    source.replace("requires at_size <= 2147483647;", ""),
                    source.replace(fit, ""),
                    source.replace(
                        fit,
                        &fit.replace(
                            if down {
                                " < 9223372036854775808"
                            } else {
                                " <= 9223372036854775807"
                            },
                            " <= 18446744073709551615",
                        ),
                    ),
                ]
            } else if phase == Some(RoundingPhase::NumeratorRejections) {
                let mut cases = vec![
                    source.replace("apply(uint64_multiply_to_integer((uint64)self->fee, (uint64)at_size));", ""),
                    source.replace(if down { "apply(uint64_divide_to_integer(((uint64)self->fee * (uint64)at_size), (uint64)(uint32)self->size));" } else { "apply(uint64_divide_to_integer(((((uint64)self->fee * (uint64)at_size) + (uint64)self->size) - 1u64), (uint64)(uint32)self->size));" }, ""),
                ];
                if !down {
                    cases.extend([
                        source.replace("apply(uint64_add_to_integer(((uint64)self->fee * (uint64)at_size), (uint64)self->size));", ""),
                        source.replace("apply(uint64_subtract_to_integer((((uint64)self->fee * (uint64)at_size) + (uint64)self->size), 1u64));", ""),
                        source.replace("== to_integer(self->fee) * to_integer(at_size) + to_integer(self->size) - 1", "== to_integer(self->fee) * to_integer(at_size) + to_integer(self->size) - 2"),
                    ]);
                }
                cases
            } else if phase == Some(RoundingPhase::TransportRejections) {
                vec![
                    source.replace("requires self->fee < 8589934592i64;", ""),
                    source.replace("requires to_integer(self->fee) <= 8589934591;", ""),
                    source.replace("requires 0 <= to_integer(self->fee);", ""),
                ]
            } else {
                assert!(phase == Some(RoundingPhase::RoundingRejections));
                vec![
                    source.replace(
                        "ensures to_integer(result) == truncating_quotient(",
                        "ensures to_integer(result) != truncating_quotient(",
                    ),
                    source.replace(
                        if down {
                            "(to_integer(result) + 1) * to_integer(self->size)"
                        } else {
                            "(to_integer(result) + -1) * to_integer(self->size)"
                        },
                        "to_integer(result) * to_integer(self->size)",
                    ),
                ]
            }
        } else if name.contains("ResultFit") && name.ends_with("Unified") {
            let down = selected.ends_with("Down");
            let lower = if down {
                "requires -9223372036854775808 * to_integer(self->size) <= to_integer(self->fee) * to_integer(at_size);"
            } else {
                "requires -9223372036854775809 * to_integer(self->size) < to_integer(self->fee) * to_integer(at_size);"
            };
            let upper = if down {
                "requires to_integer(self->fee) * to_integer(at_size) < 9223372036854775808 * to_integer(self->size);"
            } else {
                "requires to_integer(self->fee) * to_integer(at_size) <= 9223372036854775807 * to_integer(self->size);"
            };
            match phase.unwrap() {
                RoundingPhase::AuthorityRejections => vec![
                    source.replace("views self->fee;", ""),
                    source.replace("views self->size;", ""),
                ],
                RoundingPhase::Rejections => vec![
                    source.replace("requires self->size > 0;", ""),
                    source.replace("requires 0 <= at_size;", ""),
                    source.replace("requires at_size <= 2147483647;", ""),
                ],
                RoundingPhase::FitRejections => {
                    let strict = if down { upper } else { lower };
                    vec![source.replace(lower, ""), source.replace(upper, ""), source.replace(strict, &strict.replace(" < ", " <= "))]
                }
                RoundingPhase::TransportRejections => vec![
                    source.replace("requires -9223372036854775808 <= to_integer(self->fee);", ""),
                    source.replace("requires to_integer(self->fee) <= 9223372036854775807;", ""),
                    source.replace("apply(int64_greater_equal_to_integer(self->fee, 0i64));", ""),
                    source.replace("apply(int64_less_than_to_integer(self->fee, 8589934592i64));", ""),
                ],
                RoundingPhase::RoundingRejections => vec![
                    source.replace(if down { "(to_integer(result) + 1) * to_integer(self->size)" } else { "(to_integer(result) + -1) * to_integer(self->size)" }, "to_integer(result) * to_integer(self->size)"),
                    source.replace(if down { "to_integer(result) * to_integer(self->size) <= to_integer(self->fee) * to_integer(at_size)" } else { "to_integer(self->fee) * to_integer(at_size) <= to_integer(result) * to_integer(self->size)" }, if down { "to_integer(result) * to_integer(self->size) < to_integer(self->fee) * to_integer(at_size)" } else { "to_integer(self->fee) * to_integer(at_size) < to_integer(result) * to_integer(self->size)" }),
                ],
                RoundingPhase::NumeratorRejections => vec![
                    source.replace("apply(uint64_multiply_to_integer((uint64)self->fee, (uint64)at_size));", ""),
                    source.replace("to_integer(product) == to_integer(self->fee) * to_integer(at_size)", "to_integer(product) == to_integer(self->fee) * to_integer(at_size) + 1"),
                    source.replace("to_integer(negative_product) == to_integer(self->fee) * to_integer(at_size)", "to_integer(negative_product) == to_integer(self->fee) * to_integer(at_size) + 1"),
                    source.replace(if down { "apply(uint64_divide_to_integer(((uint64)self->fee * (uint64)at_size), (uint64)(uint32)self->size));" } else { "apply(uint64_divide_to_integer(((((uint64)self->fee * (uint64)at_size) + (uint64)self->size) - 1u64), (uint64)(uint32)self->size));" }, ""),
                ],
                RoundingPhase::AdjustedNumeratorRejections => {
                    assert!(!down);
                    vec![
                        source.replace("apply(uint64_add_to_integer(((uint64)self->fee * (uint64)at_size), (uint64)self->size));", ""),
                        source.replace("apply(uint64_subtract_to_integer((((uint64)self->fee * (uint64)at_size) + (uint64)self->size), 1u64));", ""),
                        source.replace("== to_integer(self->fee) * to_integer(at_size) + to_integer(self->size) - 1", "== to_integer(self->fee) * to_integer(at_size) + to_integer(self->size) - 2"),
                    ]
                }
                _ => unreachable!(),
            }
        } else if name.contains("ResultFit") {
            let down = selected.ends_with("Down");
            let lower = if down {
                "requires -9223372036854775808 * to_integer(self->size) <= to_integer(self->fee) * to_integer(at_size);"
            } else {
                "requires -9223372036854775809 * to_integer(self->size) < to_integer(self->fee) * to_integer(at_size);"
            };
            let upper = if down {
                "requires to_integer(self->fee) * to_integer(at_size) < 9223372036854775808 * to_integer(self->size);"
            } else {
                "requires to_integer(self->fee) * to_integer(at_size) <= 9223372036854775807 * to_integer(self->size);"
            };
            if phase == Some(RoundingPhase::Rejections) {
                let strict = if down { upper } else { lower };
                vec![
                    source.replace("views self->size;", ""),
                    source.replace("requires self->size > 0;", ""),
                    source.replace("requires 0 <= at_size;", ""),
                    source.replace("requires at_size <= 2147483647;", ""),
                    source.replace(lower, ""),
                    source.replace(upper, ""),
                    source.replace(strict, &strict.replace(" < ", " <= ")),
                ]
            } else {
                vec![
                    source.replace(if name.ends_with("Negative") { "requires not (self->fee >= 0i64);" } else { "requires self->fee >= 0i64 and not (self->fee < 8589934592i64);" }, ""),
                    source.replace("requires to_integer(self->fee) <= 9223372036854775807;", ""),
                    source.replace("to_integer(product) == to_integer(self->fee) * to_integer(at_size)", "to_integer(product) == to_integer(self->fee) * to_integer(at_size) + 1"),
                    source.replace(if down { "(to_integer(result) + 1) * to_integer(self->size)" } else { "(to_integer(result) + -1) * to_integer(self->size)" }, "to_integer(result) * to_integer(self->size)"),
                    source.replace(if down { "to_integer(result) * to_integer(self->size) <= to_integer(self->fee) * to_integer(at_size)" } else { "to_integer(self->fee) * to_integer(at_size) <= to_integer(result) * to_integer(self->size)" }, if down { "to_integer(result) * to_integer(self->size) < to_integer(self->fee) * to_integer(at_size)" } else { "to_integer(self->fee) * to_integer(at_size) < to_integer(result) * to_integer(self->size)" }),
                ]
            }
        } else if name.ends_with("Unified") {
            if phase == Some(RoundingPhase::Rejections) {
                vec![
                    source.replace("views self->size;", ""),
                    source.replace("requires self->size > 0;", ""),
                    source.replace("requires 0 <= at_size;", ""),
                    source.replace("requires at_size <= self->size;", ""),
                ]
            } else {
                vec![
                    source.replace("requires to_integer(self->fee) <= 9223372036854775807;", ""),
                    source.replace(
                        if selected.ends_with("Down") {
                            "(to_integer(result) + 1) * to_integer(self->size)"
                        } else {
                            "(to_integer(result) + -1) * to_integer(self->size)"
                        },
                        "to_integer(result) * to_integer(self->size)",
                    ),
                    source.replace(
                        "apply(int64_less_than_to_integer(self->fee, 8589934592i64));",
                        "",
                    ),
                ]
            }
        } else if name.ends_with("SymbolicFast") {
            if phase == Some(RoundingPhase::NumeratorRejections) {
                assert!(selected.ends_with("Up"));
                vec![
                    source.replace(
                        "apply(uint64_add_to_integer(((uint64)self->fee * (uint64)at_size), (uint64)self->size));",
                        "",
                    ),
                    source.replace(
                        "apply(uint64_subtract_to_integer((((uint64)self->fee * (uint64)at_size) + (uint64)self->size), 1u64));",
                        "",
                    ),
                    source.replace(
                        "== to_integer(self->fee) * to_integer(at_size) + to_integer(self->size) - 1",
                        "== to_integer(self->fee) * to_integer(at_size) + to_integer(self->size) - 2",
                    ),
                ]
            } else if phase == Some(RoundingPhase::Rejections) {
                vec![
                    source.replace("views self->size;", ""),
                    source.replace("requires self->size > 0;", ""),
                    source.replace("requires 0 <= at_size;", ""),
                    source.replace("requires at_size <= self->size;", ""),
                ]
            } else {
                vec![
                    source.replace("requires self->fee < 8589934592i64;", ""),
                    source.replace("requires to_integer(self->fee) <= 8589934591;", ""),
                    source.replace("requires 0 <= to_integer(self->fee);", ""),
                    source.replace(
                        "ensures to_integer(result) == truncating_quotient(",
                        "ensures to_integer(result) != truncating_quotient(",
                    ),
                    source.replace(
                        if selected.ends_with("Down") {
                            "(to_integer(result) + 1) * to_integer(self->size)"
                        } else {
                            "(to_integer(result) + -1) * to_integer(self->size)"
                        },
                        "to_integer(result) * to_integer(self->size)",
                    ),
                ]
            }
        } else if name.ends_with("Negative") || name.ends_with("PositiveWide") {
            if phase == Some(RoundingPhase::Rejections) {
                vec![
                    source.replace("views self->size;", ""),
                    source.replace("requires self->size > 0;", ""),
                    source.replace("requires 0 <= at_size;", ""),
                    source.replace("requires at_size <= self->size;", ""),
                ]
            } else {
                vec![
                    source.replace(
                        if name.ends_with("Negative") {
                            "requires not (self->fee >= 0i64);"
                        } else {
                            "requires self->fee >= 0i64 and not (self->fee < 8589934592i64);"
                        },
                        "",
                    ),
                    source.replace("requires to_integer(self->fee) <= 9223372036854775807;", ""),
                    source
                        .replace("* to_integer(self->size) <=", "* to_integer(self->size) <")
                        .replace(
                            "<= to_integer(result) * to_integer(self->size)",
                            "< to_integer(result) * to_integer(self->size)",
                        ),
                    source.replace(
                        "to_integer(product) == to_integer(self->fee) * to_integer(at_size)",
                        "to_integer(product) == to_integer(self->fee) * to_integer(at_size) + 1",
                    ),
                    source.replace(
                        if selected.ends_with("Down") {
                            "(to_integer(result) + 1) * to_integer(self->size)"
                        } else {
                            "(to_integer(result) + -1) * to_integer(self->size)"
                        },
                        "to_integer(result) * to_integer(self->size)",
                    ),
                ]
            }
        } else {
            vec![
                source.replace("views self->size;", ""),
                source.replace("requires self->size == 3;", ""),
                source.replace("requires at_size == 2;", ""),
                source.replace("ensures result ==", "ensures result !="),
            ]
        };
        for (index, hostile) in hostile.into_iter().enumerate() {
            assert_ne!(
                hostile, source,
                "a rejection must change the claim or premises"
            );
            let parsed = read_click_project(&sidecar, &hostile).unwrap();
            let Err(error) = verify_program_prepared_project(&parsed, &import) else {
                panic!("{name} accepted hostile case {index}");
            };
            assert!(error.message().len() < 8000);
        }
    }
    if bounded_div && phase == Some(RoundingPhase::FullExpansion) {
        let expanded = expand_program_prepared_project_claim_source_by_label(
            &project,
            &import,
            "FeeFrac_Div.ensures_0",
        )
        .unwrap();
        verify_program_prepared_project(&project.with_entry_source(expanded), &import).unwrap();
    }
    if result_fit_div && phase == Some(RoundingPhase::Rejections) {
        let down = name.ends_with("Down");
        let mode_guard = if down {
            "requires round_down != 0;"
        } else {
            "requires round_down == 0;"
        };
        let lower = if down {
            "requires -9223372036854775808 * to_integer(d) <= to_integer(n);"
        } else {
            "requires -9223372036854775809 * to_integer(d) < to_integer(n);"
        };
        let upper = if down {
            "requires to_integer(n) < 9223372036854775808 * to_integer(d);"
        } else {
            "requires to_integer(n) <= 9223372036854775807 * to_integer(d);"
        };
        let strict = if down { upper } else { lower };
        for hostile in [
            source.replace(mode_guard, ""),
            source.replace(lower, ""),
            source.replace(upper, ""),
            source.replace("requires d > 0;", ""),
            source.replace("requires d <= 2147483647;", ""),
            source.replace("requires d > 0;", "requires d == 0;"),
            source.replace(strict, &strict.replace(" < ", " <= ")),
        ] {
            assert_ne!(hostile, source);
            let parsed = read_click_project(&sidecar, &hostile).unwrap();
            let Err(error) = verify_program_prepared_project(&parsed, &import) else {
                panic!("{name} accepted missing or weakened result-fit guard");
            };
            assert!(error.message().len() < 8000);
        }
    }
    if result_fit_div && phase == Some(RoundingPhase::TransportRejections) {
        let down = name.ends_with("Down");
        let strict_bound = if down {
            "to_integer(n) < (to_integer(result) + 1) * to_integer(d)"
        } else {
            "(to_integer(result) + -1) * to_integer(d) < to_integer(n)"
        };
        let bad_bound = if down {
            "to_integer(n) < to_integer(result) * to_integer(d)"
        } else {
            "to_integer(result) * to_integer(d) < to_integer(n)"
        };
        let inclusive = if down {
            "to_integer(result) * to_integer(d) <= to_integer(n)"
        } else {
            "to_integer(n) <= to_integer(result) * to_integer(d)"
        };
        let correction = if down {
            "apply(integer_lower_correction_bound(to_integer(n), to_integer(d), to_integer(quot), to_integer(mod), -9223372036854775808));"
        } else {
            "apply(integer_upper_correction_bound(to_integer(n), to_integer(d), to_integer(quot), to_integer(mod), 9223372036854775807));"
        };
        for hostile in [
            source.replace(strict_bound, bad_bound),
            source.replace(inclusive, &inclusive.replace(" <= ", " < ")),
            source.replace(correction, ""),
            source.replace(
                "integer_cast_identity bounds [0, 1]",
                "integer_cast_identity bounds [1, 0]",
            ),
            source.replace(
                "ensures -9223372036854775808 <= to_integer(result);",
                "ensures to_integer(result) == 9223372036854775808;",
            ),
        ] {
            assert_ne!(hostile, source);
            let parsed = read_click_project(&sidecar, &hostile).unwrap();
            let Err(error) = verify_program_prepared_project(&parsed, &import) else {
                panic!("{name} accepted false rounding or missing narrowing/correction evidence");
            };
            assert!(error.message().len() < 8000);
        }
    }
    if name == "FeeFracDivBounded" && phase == Some(RoundingPhase::Rejections) {
        for hostile in [
            source.replace(
                "round_down != 0 implies to_integer(result) * to_integer(d) <= to_integer(n)",
                "round_down != 0 implies to_integer(result) * to_integer(d) < to_integer(n)",
            ),
            source.replace(
                "round_down != 0 implies to_integer(n) < (to_integer(result) + 1) * to_integer(d)",
                "round_down != 0 implies to_integer(n) < to_integer(result) * to_integer(d)",
            ),
            source.replace(
                "round_down == 0 implies to_integer(n) <= to_integer(result) * to_integer(d)",
                "round_down == 0 implies to_integer(n) < to_integer(result) * to_integer(d)",
            ),
            source.replace(
                "round_down == 0 implies (to_integer(result) + -1) * to_integer(d) < to_integer(n)",
                "round_down == 0 implies to_integer(result) * to_integer(d) < to_integer(n)",
            ),
            source.replace(
                "requires -9223372036854775808 * to_integer(d) <= to_integer(n);",
                "",
            ),
            source.replace(
                "requires to_integer(n) <= 9223372036854775807 * to_integer(d);",
                "",
            ),
            source.replace("requires d > 0;", ""),
            source.replace("requires d <= 2147483647;", ""),
            source.replace("requires d > 0;", "requires d == 0;"),
            source.replace(
                "ensures -9223372036854775808 <= to_integer(result);",
                "ensures to_integer(result) == 9223372036854775808;",
            ),
            source.replace(
                "integer_cast_identity bounds [0, 1]",
                "integer_cast_identity bounds [1, 0]",
            ),
        ] {
            let parsed = read_click_project(&sidecar, &hostile).unwrap();
            let error = verify_program_prepared_project(&parsed, &import).unwrap_err();
            assert!(error.message().len() < 8000);
        }
    }
    if selected == "FeeFrac::Mul" {
        assert!(import.export().records.is_empty());
        assert_eq!(import.export().function.parameters.len(), 2);
        for omitted in [
            "requires -9223372036854775808 <= to_integer(a);",
            "requires to_integer(a) <= 9223372036854775807;",
            "requires -2147483648 <= to_integer(b);",
            "requires to_integer(b) <= 2147483647;",
        ] {
            let hostile = source.replace(omitted, "");
            let parsed = read_click_project(&sidecar, &hostile).unwrap();
            verify_program_prepared_project(&parsed, &import)
                .expect_err("explicit product certificates must establish all named bounds");
        }
        let unsafe_source = "verifying \"bitcoin-src/src/util/feefrac.h\"; int128 FeeFrac_Mul(int64 a, int32 b) { ensures 0 == 0; } by { execute(); simp(); }";
        let parsed = read_click_project(&sidecar, unsafe_source).unwrap();
        let error = verify_program_prepared_project(&parsed, &import).unwrap_err();
        assert!(
            error.message().contains("undefined behavior"),
            "{}",
            error.message()
        );
    }
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn pinned_upstream_fee_frac_mul_reexports_and_verifies() {
    check_upstream_fee_frac(
        "FeeFrac::Mul",
        "FeeFracMul",
        include_str!("../integrations/bitcoin-core-money-range/FeeFracMul.click"),
    );
}

#[test]
fn pinned_upstream_fee_frac_div_imports_and_retains_native_proof_obligations() {
    check_upstream_fee_frac("FeeFrac::Div", "FeeFracDivImported", "");
}

#[test]
fn pinned_upstream_fee_frac_div_consteval_contract_reaches_runtime_string_view_boundary() {
    check_upstream_fee_frac("FeeFrac::Div", "FeeFracDivConstevalRefused", "");
}

#[test]
fn pinned_upstream_fee_frac_div_refuses_unmodelled_library_assume() {
    check_upstream_fee_frac("FeeFrac::Div", "FeeFracDivRefused", "");
}

#[test]
fn pinned_upstream_fee_frac_isempty_reexports_and_verifies() {
    check_upstream_fee_frac(
        "FeeFrac::IsEmpty",
        "FeeFracIsEmpty",
        include_str!("../integrations/bitcoin-core-money-range/FeeFracIsEmpty.click"),
    );
}

#[test]
fn pinned_upstream_fee_frac_add_reexports_and_verifies() {
    check_upstream_fee_frac(
        "FeeFrac::operator+=",
        "FeeFracAdd",
        include_str!("../integrations/bitcoin-core-money-range/FeeFracAdd.click"),
    );
}

#[test]
fn pinned_upstream_fee_frac_addself_reexports_and_verifies() {
    check_upstream_fee_frac(
        "FeeFrac::operator+=",
        "FeeFracAddSelf",
        include_str!("../integrations/bitcoin-core-money-range/FeeFracAddSelf.click"),
    );
}

#[test]
fn pinned_upstream_fee_frac_subtract_reexports_and_verifies() {
    check_upstream_fee_frac(
        "FeeFrac::operator-=",
        "FeeFracSubtract",
        include_str!("../integrations/bitcoin-core-money-range/FeeFracSubtract.click"),
    );
}

#[test]
fn pinned_upstream_fee_frac_subtractself_reexports_and_verifies() {
    check_upstream_fee_frac(
        "FeeFrac::operator-=",
        "FeeFracSubtractSelf",
        include_str!("../integrations/bitcoin-core-money-range/FeeFracSubtractSelf.click"),
    );
}

fn sha256(bytes: &[u8]) -> String {
    format!("{:x}", Sha256::digest(bytes))
}

fn output(program: &Path, args: &[&str]) -> String {
    let result = Command::new(program).args(args).output().unwrap();
    assert!(
        result.status.success(),
        "{} {:?} failed: {}",
        program.display(),
        args,
        String::from_utf8_lossy(&result.stderr)
    );
    String::from_utf8(result.stdout).unwrap().trim().to_owned()
}

fn pinned_clang() -> PathBuf {
    let llvm_config = std::env::var_os("LLVM_CONFIG")
        .map(PathBuf::from)
        .or_else(|| {
            [
                "/usr/bin/llvm-config-19",
                "/usr/lib/llvm-19/bin/llvm-config",
                "/opt/homebrew/opt/llvm@19/bin/llvm-config",
            ]
            .into_iter()
            .map(PathBuf::from)
            .find(|path| path.is_file())
        })
        .expect("scripts/check.sh requires LLVM 19.1.7");
    assert_eq!(output(&llvm_config, &["--version"]), "19.1.7");
    let clang = std::env::var_os("CLANGXX")
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from(output(&llvm_config, &["--bindir"])).join("clang++"));
    assert!(
        output(&clang, &["--version"])
            .lines()
            .next()
            .unwrap_or_default()
            .contains("19.1.7")
    );
    clang
}

#[test]
fn pinned_upstream_money_range_reexports_and_verifies_in_normal_gate() {
    let manifest: serde_json::Value = serde_json::from_str(PROVENANCE).unwrap();
    assert_eq!(
        manifest["bitcoin_commit"],
        "9be056a8a72b624dae9623b2f7bded92c2a21c91"
    );
    assert_eq!(
        manifest["source_lock_identity"],
        "6552230b6f93c1d81c0344523d624088e3962899c7fddfd0397b0cc09461aa38"
    );
    assert_eq!(
        manifest["input_closure_sha256"],
        "fceeaef86784f820339f6dc3fc24992eb9c6bcf52edccbf6b7869d79296a3c7d"
    );
    assert_eq!(manifest["input_closure_sha256"], sha256(ARCHIVE));
    let root =
        std::env::temp_dir().join(format!("click-bitcoin-money-range-{}", std::process::id()));
    fs::create_dir(&root).expect("fixture directory must not already exist");
    let archive_path = root.join("input-closure.tar.gz");
    fs::write(&archive_path, ARCHIVE).unwrap();
    let tar = Command::new("tar")
        .args([
            "-xzf",
            archive_path.to_str().unwrap(),
            "-C",
            root.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert!(
        tar.status.success(),
        "{}",
        String::from_utf8_lossy(&tar.stderr)
    );
    let amount = root.join("bitcoin-src/src/consensus/amount.h");
    let feerate = root.join("bitcoin-src/src/policy/feerate.cpp");
    assert_eq!(
        manifest["amount_sha256"],
        sha256(&fs::read(&amount).unwrap())
    );
    assert_eq!(
        manifest["feerate_sha256"],
        sha256(&fs::read(&feerate).unwrap())
    );
    fs::create_dir_all(root.join("bitcoin-build/src")).unwrap();

    let clang = pinned_clang();
    let resource_dir = output(&clang, &["-print-resource-dir"]);
    let database = COMMAND
        .replace("@ROOT@", root.to_str().unwrap())
        .replace("@CLANGXX@", clang.to_str().unwrap())
        .replace("@RESOURCE_DIR@", &resource_dir);
    assert!(!database.contains("@ROOT@"));
    assert!(!database.contains("@CLANGXX@"));
    assert!(!database.contains("@RESOURCE_DIR@"));
    fs::write(root.join("compile_commands.json"), database).unwrap();
    let exporter = std::env::var("CLICK_CPP_EXPORTER")
        .expect("scripts/check.sh supplies the pinned C++ exporter");
    let config_path = root.join("MoneyRange.click.import.json");
    let config = serde_json::json!({
        "schema": 6,
        "language": "c++",
        "standard": "c++20",
        "target": "x86_64-unknown-linux-gnu",
        "exceptions": true,
        "rtti": true,
        "exporter": exporter,
        "compilation_database": "compile_commands.json",
        "working_directory": ".",
        "source": "bitcoin-src/src/policy/feerate.cpp",
        "logical_source": "bitcoin-src/src/consensus/amount.h",
        "dependencies": [
            "sysroot/usr/include/x86_64-linux-gnu/bits/stdint-intn.h",
            "sysroot/usr/include/x86_64-linux-gnu/bits/types.h"
        ],
        "function": "MoneyRange",
        "artifact": "MoneyRange.click-cpp.json"
    });
    fs::write(&config_path, serde_json::to_vec_pretty(&config).unwrap()).unwrap();
    let sidecar = root.join("MoneyRange.click");
    fs::write(&sidecar, SIDECAR).unwrap();

    refresh_import(&config_path)
        .expect("re-export unchanged Bitcoin source under the pinned CMake command");
    let imported = load_import(&config_path).expect("load the locked upstream import");
    assert_eq!(imported.export().preprocessor_files.len(), 320);
    assert!(
        imported
            .export()
            .profile
            .frontend_version
            .contains("19.1.7")
    );
    assert_eq!(imported.export().profile.standard, "c++20");
    assert_eq!(imported.export().profile.target, "x86_64-unknown-linux-gnu");
    let max_money = imported
        .export()
        .constants
        .iter()
        .find(|constant| constant.name == "MAX_MONEY")
        .expect("the upstream bound is imported from its C++ declaration");
    assert_eq!(max_money.evaluated_value, "2100000000000000");
    let project = read_click_project(&sidecar, SIDECAR).unwrap();
    // The one integration fixture owes termination evidence like every other
    // corpus fixture; it has no loop and no callee, so it owes no measure.
    let (verification, profile) =
        instrumentation::collect(|| verify_program_prepared_project(&project, &imported));
    verification.expect("verify the exact inclusive range contract and four boundary calls");
    let finished_claims = profile
        .iter()
        .filter_map(|event| match event {
            VerificationEvent::ClaimFinished { key, .. } => Some(key.as_str()),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert!(
        !finished_claims.is_empty(),
        "profile must observe checked claims"
    );
    assert!(
        profile
            .iter()
            .any(|event| matches!(event, VerificationEvent::TacticFinished { .. }))
    );

    let sites = program_prepared_project_smart_tactic_source_sites(&project, &imported).unwrap();
    assert_eq!(
        sites.len(),
        14,
        "audit must cover every upstream smart tactic"
    );
    for event in &profile {
        if let VerificationEvent::TacticFinished { tactic, .. } = event {
            program_prepared_project_tactic_source_position(
                &project,
                &imported,
                &tactic.claim,
                tactic.source_index,
            )
            .expect("each profiled tactic must resolve to its upstream sidecar position");
        }
    }
    for claim in [
        "MoneyRange.contract",
        "below_range_is_false.ensures_0",
        "zero_is_in_range.ensures_0",
        "max_money_is_in_range.ensures_0",
        "above_range_is_false.ensures_0",
    ] {
        assert!(
            sites.iter().any(|site| site.claim_label == claim),
            "{claim} has no source-selectable smart tactic"
        );
        let profiled_claim = if claim.ends_with(".ensures_0") {
            claim.replace(".ensures_0", ".contract")
        } else {
            claim.to_owned()
        };
        assert!(
            profile.iter().any(|event| matches!(event,
                VerificationEvent::TacticFinished { tactic, .. } if tactic.claim == profiled_claim
            )),
            "profile missed {claim}"
        );
    }
    let mut session_checks = Vec::new();
    let expanded_contract = expand_program_prepared_project_claim_source_by_label(
        &project,
        &imported,
        "MoneyRange.contract",
    )
    .expect("the documented claim expansion must use the locked upstream import");
    verify_program_prepared_project(&project.with_entry_source(expanded_contract), &imported)
        .expect("the documented expanded range claim must reverify");
    for site in sites {
        let claim = site.claim_label.as_str();
        let position = program_prepared_project_tactic_source_position(
            &project,
            &imported,
            claim,
            site.source_index,
        )
        .expect("each upstream claim has a selectable tactic");
        let profiled_claim = if claim.ends_with(".ensures_0") {
            claim.replace(".ensures_0", ".contract")
        } else {
            claim.to_owned()
        };
        let profiled_position = program_prepared_project_tactic_source_position(
            &project,
            &imported,
            &profiled_claim,
            site.source_index,
        )
        .expect("the profiler must resolve the same upstream tactic location");
        assert_eq!(profiled_position, position);
        let expanded = expand_program_prepared_project_tactic_source_at(
            &project,
            &imported,
            position.line,
            position.column,
        )
        .expect("expand a tactic against the same locked import");
        assert_ne!(expanded, SIDECAR);
        let rewritten = project.with_entry_source(expanded.clone());
        let remaining = program_prepared_project_smart_tactic_source_sites(&rewritten, &imported)
            .expect("expanded proof remains source-inventoriable")
            .into_iter()
            .filter(|candidate| candidate.claim_label == claim)
            .count();
        let original = program_prepared_project_smart_tactic_source_sites(&project, &imported)
            .unwrap()
            .into_iter()
            .filter(|candidate| candidate.claim_label == claim)
            .count();
        assert!(
            remaining < original,
            "expansion must remove the audited smart site"
        );
        verify_program_prepared_project(&rewritten, &imported)
            .expect("expanded certificate must reverify against the upstream import");
        let next = program_prepared_project_tactic_source_position(&rewritten, &imported, claim, 0)
            .expect("the audited claim remains source-selectable");
        session_checks.push((expanded, next));
    }
    // A retained session's environment names its own kernel tables, which
    // every verification above replaces, so the session starts after them.
    let (session, _) = C0VerificationSession::new_program_prepared_project(&project, &imported)
        .expect("start a retained audit session on the same import");
    for (expanded, next) in &session_checks {
        session
            .verify_at_project(expanded, next.line, next.column)
            .expect("audit session must accept the expanded certificate");
    }

    let source_contract = SIDECAR
        .split_once("contract bool BelowRange")
        .expect("the modular boundary contracts follow MoneyRange")
        .0;
    let false_source = source_contract.replace(
        "if old(nValue[0]) <= 2100000000000000i64",
        "if old(nValue[0]) < 2100000000000000i64",
    );
    assert_ne!(false_source, source_contract);
    fs::write(&sidecar, &false_source).unwrap();
    let false_project = read_click_project(&sidecar, &false_source).unwrap();
    let false_error = verify_program_prepared_project(&false_project, &imported)
        .expect_err("an exclusive upper bound must not prove the upstream function");
    assert!(
        false_error.message().contains("MoneyRange.contract")
            && false_error.message().contains("unclosed goal"),
        "{}",
        false_error.message()
    );
    fs::write(&sidecar, SIDECAR).unwrap();

    let amount_bytes = fs::read(&amount).unwrap();
    let mut changed_amount = amount_bytes.clone();
    changed_amount.push(b'\n');
    fs::write(&amount, changed_amount).unwrap();
    let changed_header = load_import(&config_path).unwrap_err();
    assert!(
        changed_header.contains("C++ logical source differs"),
        "{changed_header}"
    );
    fs::write(&amount, amount_bytes).unwrap();
    load_import(&config_path).expect("restoring upstream bytes restores the locked import");

    let transitive = root.join("sysroot/usr/include/c++/12/limits");
    let transitive_bytes = fs::read(&transitive).unwrap();
    let mut changed_transitive = transitive_bytes.clone();
    changed_transitive.push(b'\n');
    fs::write(&transitive, changed_transitive).unwrap();
    let changed_dependency = load_import(&config_path).unwrap_err();
    assert!(
        changed_dependency.contains("C++ preprocessor input inventory differs"),
        "{changed_dependency}"
    );
    fs::write(&transitive, transitive_bytes).unwrap();
    load_import(&config_path).expect("restoring a transitive header restores the locked import");

    let database_path = root.join("compile_commands.json");
    let database_bytes = fs::read_to_string(&database_path).unwrap();
    let changed_database = database_bytes.replace("-std=c++20", "-std=c++17");
    assert_ne!(changed_database, database_bytes);
    fs::write(&database_path, changed_database).unwrap();
    let changed_command = load_import(&config_path).unwrap_err();
    assert!(
        changed_command.contains("C++ compilation database differs"),
        "{changed_command}"
    );
    fs::write(&database_path, database_bytes).unwrap();
    load_import(&config_path).expect("restoring the CMake command restores the locked import");

    let config_bytes = fs::read(&config_path).unwrap();
    let mut wrong_profile: serde_json::Value = serde_json::from_slice(&config_bytes).unwrap();
    wrong_profile["rtti"] = serde_json::json!(false);
    fs::write(
        &config_path,
        serde_json::to_vec_pretty(&wrong_profile).unwrap(),
    )
    .unwrap();
    let changed_profile = load_import(&config_path).unwrap_err();
    assert!(
        changed_profile.contains("C++ import lock does not match the import config"),
        "{changed_profile}"
    );
    fs::write(&config_path, &config_bytes).unwrap();

    let mut wrong_location: serde_json::Value = serde_json::from_slice(&config_bytes).unwrap();
    wrong_location["logical_source"] = serde_json::json!("bitcoin-src/src/policy/feerate.h");
    fs::write(
        &config_path,
        serde_json::to_vec_pretty(&wrong_location).unwrap(),
    )
    .unwrap();
    let wrong_location_error = refresh_import(&config_path)
        .expect_err("MoneyRange must not resolve to a different upstream header");
    assert!(
        wrong_location_error.contains("selected function `MoneyRange` was not found"),
        "{wrong_location_error}"
    );
    let stale_selector = load_import(&config_path)
        .expect_err("a rejected selector must not load the old semantic artifact");
    assert!(
        stale_selector.contains("C++ import lock does not match the import config"),
        "{stale_selector}"
    );
    fs::write(&config_path, config_bytes).unwrap();
    load_import(&config_path).expect("the original selector and lock remain valid");
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn pinned_upstream_compact_size_1_reexports_and_verifies() {
    check_upstream_cpp(
        "GetSizeOfCompactSize",
        "CompactSize1",
        include_str!("../integrations/bitcoin-core-money-range/CompactSize1.click"),
        "bitcoin-src/src/serialize.h",
        "sysroot/usr/include/x86_64-linux-gnu/bits/stdint-uintn.h",
    );
}

#[test]
fn pinned_upstream_compact_size_3_reexports_and_verifies() {
    check_upstream_cpp(
        "GetSizeOfCompactSize",
        "CompactSize3",
        include_str!("../integrations/bitcoin-core-money-range/CompactSize3.click"),
        "bitcoin-src/src/serialize.h",
        "sysroot/usr/include/x86_64-linux-gnu/bits/stdint-uintn.h",
    );
}

#[test]
fn pinned_upstream_compact_size_5_reexports_and_verifies() {
    check_upstream_cpp(
        "GetSizeOfCompactSize",
        "CompactSize5",
        include_str!("../integrations/bitcoin-core-money-range/CompactSize5.click"),
        "bitcoin-src/src/serialize.h",
        "sysroot/usr/include/x86_64-linux-gnu/bits/stdint-uintn.h",
    );
}

#[test]
fn pinned_upstream_compact_size_9_reexports_and_verifies() {
    check_upstream_cpp(
        "GetSizeOfCompactSize",
        "CompactSize9",
        include_str!("../integrations/bitcoin-core-money-range/CompactSize9.click"),
        "bitcoin-src/src/serialize.h",
        "sysroot/usr/include/x86_64-linux-gnu/bits/stdint-uintn.h",
    );
}

#[test]
fn upstream_fee_frac_div_bounded_native_correction_is_safe() {
    check_bounded_upstream_rounding(RoundingPhase::Tools);
}

#[test]
fn upstream_fee_frac_div_bounded_full_expansion_reverifies() {
    check_bounded_upstream_rounding(RoundingPhase::FullExpansion);
}

#[test]
fn upstream_fee_frac_div_bounded_rejects_false_rounding_and_missing_guards() {
    check_bounded_upstream_rounding(RoundingPhase::Rejections);
}

#[test]
fn upstream_result_fit_div_down_verifies_native_narrowing_and_correction() {
    check_result_fit_upstream_rounding("Down", RoundingPhase::Tools);
}

#[test]
fn upstream_result_fit_div_down_expands_and_reverifies() {
    check_result_fit_upstream_rounding("Down", RoundingPhase::FullExpansion);
}

#[test]
fn upstream_result_fit_div_down_rejects_missing_or_inclusive_fit_guards() {
    check_result_fit_upstream_rounding("Down", RoundingPhase::Rejections);
}

#[test]
fn upstream_result_fit_div_down_rejects_false_rounding_and_missing_transport() {
    check_result_fit_upstream_rounding("Down", RoundingPhase::TransportRejections);
}

#[test]
fn upstream_result_fit_div_up_verifies_native_narrowing_and_correction() {
    check_result_fit_upstream_rounding("Up", RoundingPhase::Tools);
}

#[test]
fn upstream_result_fit_div_up_expands_and_reverifies() {
    check_result_fit_upstream_rounding("Up", RoundingPhase::FullExpansion);
}

#[test]
fn upstream_result_fit_div_up_rejects_missing_or_inclusive_fit_guards() {
    check_result_fit_upstream_rounding("Up", RoundingPhase::Rejections);
}

#[test]
fn upstream_result_fit_div_up_rejects_false_rounding_and_missing_transport() {
    check_result_fit_upstream_rounding("Up", RoundingPhase::TransportRejections);
}

fn check_result_fit_upstream_rounding(mode: &str, phase: RoundingPhase) {
    let source = match mode {
        "Down" => {
            include_str!("../integrations/bitcoin-core-money-range/FeeFracDivResultFitDown.click")
        }
        "Up" => {
            include_str!("../integrations/bitcoin-core-money-range/FeeFracDivResultFitUp.click")
        }
        _ => unreachable!(),
    };
    check_upstream_cpp_rounding_phase(
        "FeeFrac::Div",
        &format!("FeeFracDivResultFit{mode}"),
        source,
        "bitcoin-src/src/util/feefrac.h",
        "sysroot/usr/include/x86_64-linux-gnu/bits/stdint-intn.h",
        Some(phase),
    );
}

fn check_bounded_upstream_rounding(phase: RoundingPhase) {
    check_upstream_cpp_rounding_phase(
        "FeeFrac::Div",
        "FeeFracDivBounded",
        include_str!("../integrations/bitcoin-core-money-range/FeeFracDivBounded.click"),
        "bitcoin-src/src/util/feefrac.h",
        "sysroot/usr/include/x86_64-linux-gnu/bits/stdint-intn.h",
        Some(phase),
    );
}

fn check_upstream_fee_evaluation_fast(mode: &str, expected: i64, phase: RoundingPhase) {
    let instance = if mode == "Down" { "true" } else { "false" };
    let contract = format!(
        "views self->fee; views self->size; requires self->fee == 7i64; requires self->size == 3; requires at_size == 2; ensures result == {expected}i64; ensures self->fee == old(self->fee); ensures self->size == old(self->size);"
    );
    let div = include_str!("../integrations/bitcoin-core-money-range/FeeFracDivBounded.click")
        .split_once(';')
        .unwrap()
        .1;
    let source = format!(
        r#"{}
{div}
int64 FeeFrac_EvaluateFee__bool_{instance}(const struct FeeFrac* self, int32 at_size) {{ {contract} }} by {{ execute(); simp(); }}
int64 FeeFrac_EvaluateFee{mode}(const struct FeeFrac* self, int32 at_size) {{ {contract} }} by {{ execute(); simp(); }}
"#,
        include_str!("../integrations/bitcoin-core-money-range/FeeFracMul.click")
    );
    check_upstream_cpp_rounding_phase(
        &format!("FeeFrac::EvaluateFee{mode}"),
        &format!("FeeFracEvaluate{mode}Fast"),
        &source,
        "bitcoin-src/src/util/feefrac.h",
        "sysroot/usr/include/x86_64-linux-gnu/bits/stdint-intn.h",
        Some(phase),
    );
}

#[test]
fn upstream_fee_evaluation_down_exports_full_graph_and_verifies_fast_case() {
    check_upstream_fee_evaluation_fast("Down", 4, RoundingPhase::Tools);
}
#[test]
fn upstream_fee_evaluation_up_exports_full_graph_and_verifies_fast_case() {
    check_upstream_fee_evaluation_fast("Up", 5, RoundingPhase::Tools);
}

#[test]
fn upstream_fee_evaluation_down_rejects_missing_authority_bounds_and_false_results() {
    check_upstream_fee_evaluation_fast("Down", 4, RoundingPhase::Rejections);
}
#[test]
fn upstream_fee_evaluation_up_rejects_missing_authority_bounds_and_false_results() {
    check_upstream_fee_evaluation_fast("Up", 5, RoundingPhase::Rejections);
}

fn check_upstream_result_fit_fast_fee_evaluation(mode: &str, phase: RoundingPhase) {
    let (div, caller) = match mode {
        "Down" => (
            include_str!("../integrations/bitcoin-core-money-range/FeeFracDivResultFitDown.click"),
            include_str!(
                "../integrations/bitcoin-core-money-range/FeeFracEvaluateFastResultFitDown.click.in"
            ),
        ),
        "Up" => (
            include_str!("../integrations/bitcoin-core-money-range/FeeFracDivResultFitUp.click"),
            include_str!(
                "../integrations/bitcoin-core-money-range/FeeFracEvaluateFastResultFitUp.click.in"
            ),
        ),
        _ => unreachable!(),
    };
    let div = div.split_once(';').unwrap().1;
    let source = format!(
        "{}\n{div}\n{caller}",
        include_str!("../integrations/bitcoin-core-money-range/FeeFracMul.click")
    );
    check_upstream_cpp_rounding_phase(
        &format!("FeeFrac::EvaluateFee{mode}"),
        &format!("FeeFracEvaluate{mode}ResultFitSymbolicFast"),
        &source,
        "bitcoin-src/src/util/feefrac.h",
        "sysroot/usr/include/x86_64-linux-gnu/bits/stdint-intn.h",
        Some(phase),
    );
}

#[test]
fn upstream_fast_result_fit_down_verifies_beyond_size() {
    check_upstream_result_fit_fast_fee_evaluation("Down", RoundingPhase::Tools);
}

#[test]
fn upstream_fast_result_fit_down_expands_and_reverifies() {
    check_upstream_result_fit_fast_fee_evaluation("Down", RoundingPhase::FullExpansion);
}

#[test]
fn upstream_fast_result_fit_down_rejects_missing_or_weakened_fit_bounds() {
    check_upstream_result_fit_fast_fee_evaluation("Down", RoundingPhase::Rejections);
}

#[test]
fn upstream_fast_result_fit_down_rejects_missing_fee_and_branch_bounds() {
    check_upstream_result_fit_fast_fee_evaluation("Down", RoundingPhase::TransportRejections);
}

#[test]
fn upstream_fast_result_fit_down_rejects_false_rounding() {
    check_upstream_result_fit_fast_fee_evaluation("Down", RoundingPhase::RoundingRejections);
}

#[test]
fn upstream_fast_result_fit_down_rejects_missing_bridges_and_forged_numerator() {
    check_upstream_result_fit_fast_fee_evaluation("Down", RoundingPhase::NumeratorRejections);
}

#[test]
fn upstream_fast_result_fit_up_verifies_beyond_size() {
    check_upstream_result_fit_fast_fee_evaluation("Up", RoundingPhase::Tools);
}

#[test]
fn upstream_fast_result_fit_up_expands_and_reverifies() {
    check_upstream_result_fit_fast_fee_evaluation("Up", RoundingPhase::FullExpansion);
}

#[test]
fn upstream_fast_result_fit_up_rejects_missing_or_weakened_fit_bounds() {
    check_upstream_result_fit_fast_fee_evaluation("Up", RoundingPhase::Rejections);
}

#[test]
fn upstream_fast_result_fit_up_rejects_missing_fee_and_branch_bounds() {
    check_upstream_result_fit_fast_fee_evaluation("Up", RoundingPhase::TransportRejections);
}

#[test]
fn upstream_fast_result_fit_up_rejects_false_rounding() {
    check_upstream_result_fit_fast_fee_evaluation("Up", RoundingPhase::RoundingRejections);
}

#[test]
fn upstream_fast_result_fit_up_rejects_missing_bridges_and_forged_numerator() {
    check_upstream_result_fit_fast_fee_evaluation("Up", RoundingPhase::NumeratorRejections);
}

fn check_upstream_symbolic_fast_fee_evaluation(mode: &str, phase: RoundingPhase) {
    let div = include_str!("../integrations/bitcoin-core-money-range/FeeFracDivBounded.click")
        .split_once(';')
        .unwrap()
        .1;
    let caller = if mode == "Down" {
        include_str!("../integrations/bitcoin-core-money-range/FeeFracEvaluateFastDown.click.in")
    } else {
        assert_eq!(mode, "Up");
        include_str!("../integrations/bitcoin-core-money-range/FeeFracEvaluateFastUp.click.in")
    };
    let source = format!(
        "{}\n{div}\n{caller}",
        include_str!("../integrations/bitcoin-core-money-range/FeeFracMul.click")
    );
    check_upstream_cpp_rounding_phase(
        &format!("FeeFrac::EvaluateFee{mode}"),
        &format!("FeeFracEvaluate{mode}SymbolicFast"),
        &source,
        "bitcoin-src/src/util/feefrac.h",
        "sysroot/usr/include/x86_64-linux-gnu/bits/stdint-intn.h",
        Some(phase),
    );
}

#[test]
fn upstream_symbolic_fast_fee_evaluation_down_has_exact_floor_bounds() {
    check_upstream_symbolic_fast_fee_evaluation("Down", RoundingPhase::Tools);
}
#[test]
fn upstream_symbolic_fast_fee_evaluation_down_expands_and_reverifies() {
    check_upstream_symbolic_fast_fee_evaluation("Down", RoundingPhase::FullExpansion);
}
#[test]
fn upstream_symbolic_fast_fee_evaluation_down_rejects_missing_authority_and_amount_bounds() {
    check_upstream_symbolic_fast_fee_evaluation("Down", RoundingPhase::Rejections);
}
#[test]
fn upstream_symbolic_fast_fee_evaluation_down_rejects_missing_fee_bounds_and_false_rounding() {
    check_upstream_symbolic_fast_fee_evaluation("Down", RoundingPhase::TransportRejections);
}

#[test]
fn upstream_symbolic_fast_fee_evaluation_up_has_exact_ceiling_bounds() {
    check_upstream_symbolic_fast_fee_evaluation("Up", RoundingPhase::Tools);
}
#[test]
fn upstream_symbolic_fast_fee_evaluation_up_expands_and_reverifies() {
    check_upstream_symbolic_fast_fee_evaluation("Up", RoundingPhase::FullExpansion);
}
#[test]
fn upstream_symbolic_fast_fee_evaluation_up_rejects_missing_authority_and_amount_bounds() {
    check_upstream_symbolic_fast_fee_evaluation("Up", RoundingPhase::Rejections);
}
#[test]
fn upstream_symbolic_fast_fee_evaluation_up_rejects_missing_fee_bounds_and_false_rounding() {
    check_upstream_symbolic_fast_fee_evaluation("Up", RoundingPhase::TransportRejections);
}
#[test]
fn upstream_symbolic_fast_fee_evaluation_up_rejects_missing_bridges_and_forged_numerator() {
    check_upstream_symbolic_fast_fee_evaluation("Up", RoundingPhase::NumeratorRejections);
}

fn wide_fee_evaluation_source(mode: &str, positive: bool) -> String {
    wide_fee_evaluation_source_with_profile(mode, positive, false)
}

fn wide_fee_evaluation_source_with_profile(mode: &str, positive: bool, result_fit: bool) -> String {
    let down = mode == "Down";
    let bounds = |result: &str, size: &str, product: &str| {
        if down {
            [
                format!("{result} * {size} <= {product}"),
                format!("{product} < ({result} + 1) * {size}"),
            ]
        } else {
            [
                format!("{product} <= {result} * {size}"),
                format!("({result} + -1) * {size} < {product}"),
            ]
        }
    };
    let caller = bounds(
        "to_integer(result)",
        "to_integer(self->size)",
        "to_integer(self->fee) * to_integer(at_size)",
    );
    let helper = bounds(
        "to_integer(rounded)",
        "to_integer(denominator)",
        "to_integer(product)",
    );
    let fit_bounds = |product: &str| {
        if down {
            [
                format!("-9223372036854775808 * to_integer(self->size) <= {product}"),
                format!("{product} < 9223372036854775808 * to_integer(self->size)"),
            ]
        } else {
            [
                format!("-9223372036854775809 * to_integer(self->size) < {product}"),
                format!("{product} <= 9223372036854775807 * to_integer(self->size)"),
            ]
        }
    };
    let input = fit_bounds("to_integer(self->fee) * to_integer(at_size)");
    let product = fit_bounds("to_integer(product)");
    let template = if result_fit {
        include_str!(
            "../integrations/bitcoin-core-money-range/FeeFracEvaluateWideResultFit.click.in"
        )
    } else {
        include_str!("../integrations/bitcoin-core-money-range/FeeFracEvaluateWide.click.in")
    };
    let fragment = template
        .replace(
            "@WIDE_GUARD@",
            if positive {
                "self->fee >= 0i64 and not (self->fee < 8589934592i64)"
            } else {
                "not (self->fee >= 0i64)"
            },
        )
        .replace("@MODE@", mode)
        .replace("@INSTANCE@", if down { "true" } else { "false" })
        .replace("@ROUND@", if down { "1" } else { "0" })
        .replace("@CALLER_BOUND_1@", &caller[0])
        .replace("@CALLER_BOUND_2@", &caller[1])
        .replace("@DIV_BOUND_1@", &helper[0])
        .replace("@DIV_BOUND_2@", &helper[1])
        .replace("@INPUT_BOUND_1@", &input[0])
        .replace("@INPUT_BOUND_2@", &input[1])
        .replace("@PRODUCT_BOUND_1@", &product[0])
        .replace("@PRODUCT_BOUND_2@", &product[1])
        .replace(
            "@FEE_WITNESS@",
            if positive {
                "8589934592"
            } else {
                "-8589934592"
            },
        );
    assert!(!fragment.contains('@'));
    let div = if !result_fit {
        include_str!("../integrations/bitcoin-core-money-range/FeeFracDivBounded.click")
    } else if down {
        include_str!("../integrations/bitcoin-core-money-range/FeeFracDivResultFitDown.click")
    } else {
        include_str!("../integrations/bitcoin-core-money-range/FeeFracDivResultFitUp.click")
    }
    .split_once(';')
    .unwrap()
    .1;
    format!(
        "{}\n{div}\n{fragment}",
        include_str!("../integrations/bitcoin-core-money-range/FeeFracMul.click")
    )
}

fn check_upstream_result_fit_wide_fee_evaluation(mode: &str, positive: bool, phase: RoundingPhase) {
    check_upstream_cpp_rounding_phase(
        &format!("FeeFrac::EvaluateFee{mode}"),
        &format!(
            "FeeFracEvaluate{mode}ResultFit{}",
            if positive { "PositiveWide" } else { "Negative" }
        ),
        &wide_fee_evaluation_source_with_profile(mode, positive, true),
        "bitcoin-src/src/util/feefrac.h",
        "sysroot/usr/include/x86_64-linux-gnu/bits/stdint-intn.h",
        Some(phase),
    );
}

#[test]
fn upstream_wide_result_fit_down_negative_verifies_beyond_size() {
    check_upstream_result_fit_wide_fee_evaluation("Down", false, RoundingPhase::Tools);
}

#[test]
fn upstream_wide_result_fit_down_negative_expands_and_reverifies() {
    check_upstream_result_fit_wide_fee_evaluation("Down", false, RoundingPhase::FullExpansion);
}

#[test]
fn upstream_wide_result_fit_down_negative_rejects_missing_or_inclusive_fit_bounds() {
    check_upstream_result_fit_wide_fee_evaluation("Down", false, RoundingPhase::Rejections);
}

#[test]
fn upstream_wide_result_fit_down_negative_rejects_false_rounding_and_missing_transport() {
    check_upstream_result_fit_wide_fee_evaluation(
        "Down",
        false,
        RoundingPhase::TransportRejections,
    );
}

#[test]
fn upstream_wide_result_fit_down_positive_verifies_beyond_size() {
    check_upstream_result_fit_wide_fee_evaluation("Down", true, RoundingPhase::Tools);
}

#[test]
fn upstream_wide_result_fit_down_positive_expands_and_reverifies() {
    check_upstream_result_fit_wide_fee_evaluation("Down", true, RoundingPhase::FullExpansion);
}

#[test]
fn upstream_wide_result_fit_down_positive_rejects_missing_or_inclusive_fit_bounds() {
    check_upstream_result_fit_wide_fee_evaluation("Down", true, RoundingPhase::Rejections);
}

#[test]
fn upstream_wide_result_fit_down_positive_rejects_false_rounding_and_missing_transport() {
    check_upstream_result_fit_wide_fee_evaluation("Down", true, RoundingPhase::TransportRejections);
}

#[test]
fn upstream_wide_result_fit_up_negative_verifies_beyond_size() {
    check_upstream_result_fit_wide_fee_evaluation("Up", false, RoundingPhase::Tools);
}

#[test]
fn upstream_wide_result_fit_up_negative_expands_and_reverifies() {
    check_upstream_result_fit_wide_fee_evaluation("Up", false, RoundingPhase::FullExpansion);
}

#[test]
fn upstream_wide_result_fit_up_negative_rejects_missing_or_inclusive_fit_bounds() {
    check_upstream_result_fit_wide_fee_evaluation("Up", false, RoundingPhase::Rejections);
}

#[test]
fn upstream_wide_result_fit_up_negative_rejects_false_rounding_and_missing_transport() {
    check_upstream_result_fit_wide_fee_evaluation("Up", false, RoundingPhase::TransportRejections);
}

#[test]
fn upstream_wide_result_fit_up_positive_verifies_beyond_size() {
    check_upstream_result_fit_wide_fee_evaluation("Up", true, RoundingPhase::Tools);
}

#[test]
fn upstream_wide_result_fit_up_positive_expands_and_reverifies() {
    check_upstream_result_fit_wide_fee_evaluation("Up", true, RoundingPhase::FullExpansion);
}

#[test]
fn upstream_wide_result_fit_up_positive_rejects_missing_or_inclusive_fit_bounds() {
    check_upstream_result_fit_wide_fee_evaluation("Up", true, RoundingPhase::Rejections);
}

#[test]
fn upstream_wide_result_fit_up_positive_rejects_false_rounding_and_missing_transport() {
    check_upstream_result_fit_wide_fee_evaluation("Up", true, RoundingPhase::TransportRejections);
}

fn unified_fee_evaluation_source(mode: &str) -> String {
    unified_fee_evaluation_source_with_profile(mode, false)
}

fn unified_fee_evaluation_source_with_profile(mode: &str, result_fit: bool) -> String {
    let wide = wide_fee_evaluation_source_with_profile(mode, true, result_fit);
    let (helpers, callers) = wide.split_once("int64 FeeFrac_EvaluateFee__bool_").unwrap();
    let wide_body = callers
        .split_once("} by {")
        .unwrap()
        .1
        .split_once("\n}\nint64")
        .unwrap()
        .0;
    let negative = wide_body
        .replace("denominator", "negative_denominator")
        .replace("let product =", "let negative_product =")
        .replace("to_integer(product)", "to_integer(negative_product)")
        .replace("FeeFrac_Div(product,", "FeeFrac_Div(negative_product,")
        .replace("rounded", "negative_rounded");
    let fast = match (mode, result_fit) {
        ("Down", false) => include_str!(
            "../integrations/bitcoin-core-money-range/FeeFracEvaluateFastDown.click.in"
        ),
        ("Up", false) => {
            include_str!("../integrations/bitcoin-core-money-range/FeeFracEvaluateFastUp.click.in")
        }
        ("Down", true) => include_str!(
            "../integrations/bitcoin-core-money-range/FeeFracEvaluateFastResultFitDown.click.in"
        ),
        ("Up", true) => include_str!(
            "../integrations/bitcoin-core-money-range/FeeFracEvaluateFastResultFitUp.click.in"
        ),
        _ => panic!("unknown rounding mode"),
    };
    let fast_body = fast
        .split_once("} by {")
        .unwrap()
        .1
        .split_once("\n}\n\nint64")
        .unwrap()
        .0;
    let fast_body = fast_body.strip_suffix("    simp();").unwrap();
    let contract = callers.split_once("} by {").unwrap().0;
    let bounds = contract
        .lines()
        .filter_map(|l| l.trim().strip_prefix("ensures "))
        .filter(|l| l.contains(" * "))
        .map(|l| l.trim_end_matches(';'))
        .collect::<Vec<_>>();
    assert_eq!(bounds.len(), 2);
    let input_bounds = contract
        .lines()
        .filter_map(|l| l.trim().strip_prefix("requires "))
        .filter(|l| l.contains(" * "))
        .map(|l| l.trim_end_matches(';'))
        .collect::<Vec<_>>();
    let template = if result_fit {
        assert_eq!(input_bounds.len(), 2);
        include_str!("../integrations/bitcoin-core-money-range/FeeFracEvaluateResultFit.click.in")
    } else {
        include_str!("../integrations/bitcoin-core-money-range/FeeFracEvaluateBounded.click.in")
    };
    let template = if result_fit {
        template
            .replace("@INPUT_BOUND_1@", input_bounds[0])
            .replace("@INPUT_BOUND_2@", input_bounds[1])
    } else {
        template.to_owned()
    };
    let fragment = template
        .replace("@INSTANCE@", if mode == "Down" { "true" } else { "false" })
        .replace("@MODE@", mode)
        .replace("@CALLER_BOUND_1@", bounds[0])
        .replace("@CALLER_BOUND_2@", bounds[1])
        .replace("@FAST_PROOF@", fast_body)
        .replace("@WIDE_POSITIVE_PROOF@", wide_body)
        .replace("@WIDE_NEGATIVE_PROOF@", &negative);
    assert!(!fragment.contains('@'));
    format!("{helpers}{fragment}")
}

fn check_upstream_result_fit_unified_fee_evaluation(mode: &str, phase: RoundingPhase) {
    check_upstream_cpp_rounding_phase(
        &format!("FeeFrac::EvaluateFee{mode}"),
        &format!("FeeFracEvaluate{mode}ResultFitUnified"),
        &unified_fee_evaluation_source_with_profile(mode, true),
        "bitcoin-src/src/util/feefrac.h",
        "sysroot/usr/include/x86_64-linux-gnu/bits/stdint-intn.h",
        Some(phase),
    );
}

#[test]
fn upstream_unified_result_fit_down_verifies_all_fee_branches_beyond_size() {
    check_upstream_result_fit_unified_fee_evaluation("Down", RoundingPhase::Tools);
}

#[test]
fn upstream_unified_result_fit_down_expands_and_reverifies() {
    check_upstream_result_fit_unified_fee_evaluation("Down", RoundingPhase::FullExpansion);
}

#[test]
fn upstream_unified_result_fit_down_rejects_missing_field_authority() {
    check_upstream_result_fit_unified_fee_evaluation("Down", RoundingPhase::AuthorityRejections);
}

#[test]
fn upstream_unified_result_fit_down_rejects_missing_domain_bounds() {
    check_upstream_result_fit_unified_fee_evaluation("Down", RoundingPhase::Rejections);
}

#[test]
fn upstream_unified_result_fit_down_rejects_missing_or_weakened_fit_bounds() {
    check_upstream_result_fit_unified_fee_evaluation("Down", RoundingPhase::FitRejections);
}

#[test]
fn upstream_unified_result_fit_down_rejects_missing_fee_bounds_and_branch_transport() {
    check_upstream_result_fit_unified_fee_evaluation("Down", RoundingPhase::TransportRejections);
}

#[test]
fn upstream_unified_result_fit_down_rejects_false_rounding() {
    check_upstream_result_fit_unified_fee_evaluation("Down", RoundingPhase::RoundingRejections);
}

#[test]
fn upstream_unified_result_fit_down_rejects_missing_bridges_and_forged_numerator() {
    check_upstream_result_fit_unified_fee_evaluation("Down", RoundingPhase::NumeratorRejections);
}

#[test]
fn upstream_unified_result_fit_up_verifies_all_fee_branches_beyond_size() {
    check_upstream_result_fit_unified_fee_evaluation("Up", RoundingPhase::Tools);
}

#[test]
fn upstream_unified_result_fit_up_expands_and_reverifies() {
    check_upstream_result_fit_unified_fee_evaluation("Up", RoundingPhase::FullExpansion);
}

#[test]
fn upstream_unified_result_fit_up_rejects_missing_field_authority() {
    check_upstream_result_fit_unified_fee_evaluation("Up", RoundingPhase::AuthorityRejections);
}

#[test]
fn upstream_unified_result_fit_up_rejects_missing_domain_bounds() {
    check_upstream_result_fit_unified_fee_evaluation("Up", RoundingPhase::Rejections);
}

#[test]
fn upstream_unified_result_fit_up_rejects_missing_or_weakened_fit_bounds() {
    check_upstream_result_fit_unified_fee_evaluation("Up", RoundingPhase::FitRejections);
}

#[test]
fn upstream_unified_result_fit_up_rejects_missing_fee_bounds_and_branch_transport() {
    check_upstream_result_fit_unified_fee_evaluation("Up", RoundingPhase::TransportRejections);
}

#[test]
fn upstream_unified_result_fit_up_rejects_false_rounding() {
    check_upstream_result_fit_unified_fee_evaluation("Up", RoundingPhase::RoundingRejections);
}

#[test]
fn upstream_unified_result_fit_up_rejects_missing_bridges_and_forged_numerator() {
    check_upstream_result_fit_unified_fee_evaluation("Up", RoundingPhase::NumeratorRejections);
}

#[test]
fn upstream_unified_result_fit_up_rejects_missing_or_forged_adjusted_numerator() {
    check_upstream_result_fit_unified_fee_evaluation(
        "Up",
        RoundingPhase::AdjustedNumeratorRejections,
    );
}

fn check_upstream_unified_fee_evaluation(mode: &str, phase: RoundingPhase) {
    check_upstream_cpp_rounding_phase(
        &format!("FeeFrac::EvaluateFee{mode}"),
        &format!("FeeFracEvaluate{mode}Unified"),
        &unified_fee_evaluation_source(mode),
        "bitcoin-src/src/util/feefrac.h",
        "sysroot/usr/include/x86_64-linux-gnu/bits/stdint-intn.h",
        Some(phase),
    );
}

#[test]
fn upstream_unified_fee_evaluation_down_verifies_all_fee_branches() {
    check_upstream_unified_fee_evaluation("Down", RoundingPhase::Tools);
}
#[test]
fn upstream_unified_fee_evaluation_up_verifies_all_fee_branches() {
    check_upstream_unified_fee_evaluation("Up", RoundingPhase::Tools);
}
#[test]
fn upstream_unified_fee_evaluation_down_expands_and_reverifies() {
    check_upstream_unified_fee_evaluation("Down", RoundingPhase::FullExpansion);
}
#[test]
fn upstream_unified_fee_evaluation_up_expands_and_reverifies() {
    check_upstream_unified_fee_evaluation("Up", RoundingPhase::FullExpansion);
}
#[test]
fn upstream_unified_fee_evaluation_down_rejects_missing_domain_bounds() {
    check_upstream_unified_fee_evaluation("Down", RoundingPhase::Rejections);
}
#[test]
fn upstream_unified_fee_evaluation_up_rejects_missing_domain_bounds() {
    check_upstream_unified_fee_evaluation("Up", RoundingPhase::Rejections);
}
#[test]
fn upstream_unified_fee_evaluation_down_rejects_false_rounding_and_missing_transport() {
    check_upstream_unified_fee_evaluation("Down", RoundingPhase::TransportRejections);
}
#[test]
fn upstream_unified_fee_evaluation_up_rejects_false_rounding_and_missing_transport() {
    check_upstream_unified_fee_evaluation("Up", RoundingPhase::TransportRejections);
}

fn check_upstream_negative_fee_evaluation(mode: &str, phase: RoundingPhase) {
    check_upstream_cpp_rounding_phase(
        &format!("FeeFrac::EvaluateFee{mode}"),
        &format!("FeeFracEvaluate{mode}Negative"),
        &wide_fee_evaluation_source(mode, false),
        "bitcoin-src/src/util/feefrac.h",
        "sysroot/usr/include/x86_64-linux-gnu/bits/stdint-intn.h",
        Some(phase),
    );
}

#[test]
fn upstream_negative_fee_evaluation_down_has_symbolic_floor_bounds() {
    check_upstream_negative_fee_evaluation("Down", RoundingPhase::Tools);
}

#[test]
fn upstream_negative_fee_evaluation_up_has_symbolic_ceiling_bounds() {
    check_upstream_negative_fee_evaluation("Up", RoundingPhase::Tools);
}

#[test]
fn upstream_negative_fee_evaluation_down_instance_expands_and_reverifies() {
    check_upstream_negative_fee_evaluation("Down", RoundingPhase::FullExpansion);
}
#[test]
fn upstream_negative_fee_evaluation_up_instance_expands_and_reverifies() {
    check_upstream_negative_fee_evaluation("Up", RoundingPhase::FullExpansion);
}
#[test]
fn upstream_negative_fee_evaluation_down_rejects_false_bounds_and_missing_guards() {
    check_upstream_negative_fee_evaluation("Down", RoundingPhase::Rejections);
}
#[test]
fn upstream_negative_fee_evaluation_up_rejects_false_bounds_and_missing_guards() {
    check_upstream_negative_fee_evaluation("Up", RoundingPhase::Rejections);
}

#[test]
fn upstream_negative_fee_evaluation_down_rejects_forged_product_and_rounding_transport() {
    check_upstream_negative_fee_evaluation("Down", RoundingPhase::TransportRejections);
}
#[test]
fn upstream_negative_fee_evaluation_up_rejects_forged_product_and_rounding_transport() {
    check_upstream_negative_fee_evaluation("Up", RoundingPhase::TransportRejections);
}

fn check_upstream_positive_wide_fee_evaluation(mode: &str, phase: RoundingPhase) {
    check_upstream_cpp_rounding_phase(
        &format!("FeeFrac::EvaluateFee{mode}"),
        &format!("FeeFracEvaluate{mode}PositiveWide"),
        &wide_fee_evaluation_source(mode, true),
        "bitcoin-src/src/util/feefrac.h",
        "sysroot/usr/include/x86_64-linux-gnu/bits/stdint-intn.h",
        Some(phase),
    );
}

#[test]
fn upstream_positive_wide_fee_evaluation_down_has_symbolic_bounds() {
    check_upstream_positive_wide_fee_evaluation("Down", RoundingPhase::Tools);
}

#[test]
fn upstream_positive_wide_fee_evaluation_down_instance_expands_and_reverifies() {
    check_upstream_positive_wide_fee_evaluation("Down", RoundingPhase::FullExpansion);
}

#[test]
fn upstream_positive_wide_fee_evaluation_down_rejects_false_bounds_and_missing_guards() {
    check_upstream_positive_wide_fee_evaluation("Down", RoundingPhase::Rejections);
}

#[test]
fn upstream_positive_wide_fee_evaluation_down_rejects_forged_product_and_rounding_transport() {
    check_upstream_positive_wide_fee_evaluation("Down", RoundingPhase::TransportRejections);
}

#[test]
fn upstream_positive_wide_fee_evaluation_up_has_symbolic_bounds() {
    check_upstream_positive_wide_fee_evaluation("Up", RoundingPhase::Tools);
}

#[test]
fn upstream_positive_wide_fee_evaluation_up_instance_expands_and_reverifies() {
    check_upstream_positive_wide_fee_evaluation("Up", RoundingPhase::FullExpansion);
}

#[test]
fn upstream_positive_wide_fee_evaluation_up_rejects_false_bounds_and_missing_guards() {
    check_upstream_positive_wide_fee_evaluation("Up", RoundingPhase::Rejections);
}

#[test]
fn upstream_positive_wide_fee_evaluation_up_rejects_forged_product_and_rounding_transport() {
    check_upstream_positive_wide_fee_evaluation("Up", RoundingPhase::TransportRejections);
}

#[test]
fn pinned_upstream_fee_rate_getfee_retains_condition_call_boundary() {
    check_upstream_cpp_rounding_phase(
        "CFeeRate::GetFee",
        "CFeeRateGetFeeBoundary",
        "",
        "bitcoin-src/src/policy/feerate.cpp",
        "sysroot/usr/include/x86_64-linux-gnu/bits/stdint-intn.h",
        None,
    );
}
