//! Hermetic re-export of the pinned Bitcoin Core v31.1 MoneyRange fixture.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use click::cli::read_click_project;
use click::instrumentation::{self, VerificationEvent};
use click::languages::cpp::{PreparedCppImport, load_import, refresh_import};
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
    let fee_rate_import = name == "CFeeRateGetFeeImported";
    let fee_rate_per_k = selected == "CFeeRate::GetFeePerK";
    let fee_rate_caller = name.starts_with("CFeeRateGetFee");
    let result_fit_div = name.starts_with("FeeFracDivResultFit");
    let bounded_div = name == "FeeFracDivBounded" || result_fit_div;
    if evaluation_caller
        || fee_rate_caller
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
    if evaluation_caller || fee_rate_caller || bounded_div || name == "FeeFracDivImported" {
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
    if fee_rate_caller {
        for header in [
            "bitcoin-src/src/consensus/amount.h",
            "bitcoin-src/src/policy/feerate.h",
            "bitcoin-src/src/util/feefrac.h",
        ] {
            if header == logical_source {
                continue;
            }
            config["dependencies"]
                .as_array_mut()
                .unwrap()
                .push(header.into());
        }
        config["dependencies"]
            .as_array_mut()
            .unwrap()
            .sort_by(|a, b| a.as_str().cmp(&b.as_str()));
        if !fee_rate_import {
            let exporter = root.join("click-cpp-exporter");
            fs::copy(config["exporter"].as_str().unwrap(), &exporter).unwrap();
            config["exporter"] = exporter.to_str().unwrap().into();
        }
    }
    let config_path = root.join(format!("{name}.click.import.json"));
    fs::write(&config_path, serde_json::to_vec_pretty(&config).unwrap()).unwrap();
    let sidecar = root.join(format!("{name}.click"));
    fs::write(&sidecar, source).unwrap();
    let refreshed = refresh_import(&config_path);
    if fee_rate_import {
        refreshed.expect("GetFee must import its unchanged converted-call graph");
        let import = load_import(&config_path).unwrap();
        assert_eq!(import.export().function.name, "CFeeRate_GetFee");
        assert!(
            import
                .export()
                .reachable_functions
                .iter()
                .any(|callee| callee.span.file == "bitcoin-src/src/util/feefrac.h")
        );
        click::languages::cpp::lower_import(&import).unwrap();
        let artifact: serde_json::Value =
            serde_json::from_slice(&fs::read(root.join(format!("{name}.click-cpp.json"))).unwrap())
                .unwrap();
        let initializer = &artifact["function"]["body"]
            .as_array()
            .unwrap()
            .iter()
            .find(|statement| statement["kind"] == "declare")
            .unwrap()["initializer"];
        assert_eq!(initializer["kind"], "call");
        assert_eq!(initializer["conversions"][0]["cast_kind"], "no_op");
        assert_eq!(initializer["conversions"][0]["value_type"]["bits"], 64);
        assert!(root.join(format!("{name}.click-cpp.json")).exists());
        assert!(root.join(format!("{name}.click.import.json.lock")).exists());
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
    if fee_rate_caller {
        fs::remove_file(config["exporter"].as_str().unwrap()).unwrap();
    }
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
    } else if !fee_rate_caller {
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
    if fee_rate_caller {
        verify_program_prepared_project(&project, &import)
            .unwrap_or_else(|error| panic!("{selected}: {}", error.message()));
        let root_name = if fee_rate_per_k {
            "CFeeRate_GetFeePerK"
        } else {
            "CFeeRate_GetFee"
        };
        if matches!(
            phase,
            Some(RoundingPhase::FullExpansion | RoundingPhase::Tools)
        ) {
            let expanded = expand_program_prepared_project_claim_source_by_label(
                &project,
                &import,
                &format!("{root_name}.ensures_0"),
            )
            .unwrap();
            let rewritten = project.with_entry_source(expanded.clone());
            if phase == Some(RoundingPhase::FullExpansion) {
                verify_program_prepared_project(&rewritten, &import).unwrap();
            } else {
                let (session, _) =
                    C0VerificationSession::new_program_prepared_project(&project, &import).unwrap();
                let position = program_prepared_project_tactic_source_position(
                    &rewritten,
                    &import,
                    &format!("{root_name}.contract"),
                    0,
                )
                .unwrap();
                session
                    .verify_at_project(&expanded, position.line, position.column)
                    .unwrap();
            }
        } else if phase == Some(RoundingPhase::Rejections) {
            let (from, to) = match name {
                "CFeeRateGetFeeMissingFeeAuthority" => ("views this->m_feerate.base.fee;", ""),
                "CFeeRateGetFeeMissingSizeAuthority" => ("views this->m_feerate.base.size;", ""),
                "CFeeRateGetFeeMissingAmountGuard" => ("requires 0 <= virtual_bytes;", ""),
                "CFeeRateGetFeeMissingSizeGuard" => {
                    ("requires this->m_feerate.base.size >= 0;", "")
                }
                "CFeeRateGetFeeMissingLowerFit" => (
                    "requires this->m_feerate.base.size != 0 implies -9223372036854775809 * to_integer(this->m_feerate.base.size) < to_integer(this->m_feerate.base.fee) * to_integer(virtual_bytes);",
                    "",
                ),
                "CFeeRateGetFeeMissingUpperFit" => (
                    "requires this->m_feerate.base.size != 0 implies to_integer(this->m_feerate.base.fee) * to_integer(virtual_bytes) <= 9223372036854775807 * to_integer(this->m_feerate.base.size);",
                    "",
                ),
                "CFeeRateGetFeeInclusiveLowerFit" => (
                    "-9223372036854775809 * to_integer(this->m_feerate.base.size) <",
                    "-9223372036854775809 * to_integer(this->m_feerate.base.size) <=",
                ),
                "CFeeRateGetFeeFalseEmpty" => (
                    "this->m_feerate.base.size == 0 implies result == 0i64",
                    "this->m_feerate.base.size == 0 implies result == 1i64",
                ),
                "CFeeRateGetFeeFalseCorrection" => (
                    "or (result == -1i64 and virtual_bytes",
                    "or (result == 0i64 and virtual_bytes",
                ),
                "CFeeRateGetFeeMissingFeeBounds" => (
                    "requires this->m_feerate.base.size != 0 implies to_integer(this->m_feerate.base.fee) <= 9223372036854775807;",
                    "",
                ),
                "CFeeRateGetFeePerKMissingSizeGuard" => {
                    ("requires this->m_feerate.base.size > 0;", "")
                }
                "CFeeRateGetFeePerKMissingFeeAuthority" => ("views this->m_feerate.base.fee;", ""),
                "CFeeRateGetFeePerKMissingLowerFit" => (
                    "requires -9223372036854775808 * to_integer(this->m_feerate.base.size) <= to_integer(this->m_feerate.base.fee) * 1000;",
                    "",
                ),
                "CFeeRateGetFeePerKInclusiveUpperFit" => (
                    "* 1000 < 9223372036854775808",
                    "* 1000 <= 9223372036854775808",
                ),
                "CFeeRateGetFeePerKFalseRounding" => {
                    ("(to_integer(result) + 1)", "(to_integer(result) + -1)")
                }
                _ => panic!("unknown fee-rate rejection {name}"),
            };
            let root_signature = format!("int64 {root_name}(");
            let (helpers, root_source) = source.split_once(&root_signature).unwrap();
            assert!(root_source.contains(from), "missing mutation {name}");
            let hostile = format!(
                "{helpers}{root_signature}{}",
                root_source.replacen(from, to, 1)
            );
            let parsed = read_click_project(&sidecar, &hostile).unwrap();
            let error = verify_program_prepared_project(&parsed, &import).unwrap_err();
            assert!(error.message().len() < 8000, "{}", error.message());
        } else if phase == Some(RoundingPhase::TransportRejections) {
            fs::write(
                root.join("bitcoin-src/src/util/feefrac.h"),
                "// stale header\n",
            )
            .unwrap();
            let error = load_import(&config_path).unwrap_err();
            assert!(error.len() < 8000, "{error}");
        }
        fs::remove_dir_all(root).unwrap();
        return;
    }
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
                "requires to_integer(this->fee) * to_integer(at_size) < 9223372036854775808 * to_integer(this->size);"
            } else {
                "requires to_integer(this->fee) * to_integer(at_size) <= 9223372036854775807 * to_integer(this->size);"
            };
            if phase == Some(RoundingPhase::Rejections) {
                vec![
                    source.replace("views this->size;", ""),
                    source.replace("requires this->size > 0;", ""),
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
                    source.replace("apply(uint64_multiply_to_integer((uint64)this->fee, (uint64)at_size));", ""),
                    source.replace(if down { "apply(uint64_divide_to_integer(((uint64)this->fee * (uint64)at_size), (uint64)(uint32)this->size));" } else { "apply(uint64_divide_to_integer(((((uint64)this->fee * (uint64)at_size) + (uint64)this->size) - 1u64), (uint64)(uint32)this->size));" }, ""),
                ];
                if !down {
                    cases.extend([
                        source.replace("apply(uint64_add_to_integer(((uint64)this->fee * (uint64)at_size), (uint64)this->size));", ""),
                        source.replace("apply(uint64_subtract_to_integer((((uint64)this->fee * (uint64)at_size) + (uint64)this->size), 1u64));", ""),
                        source.replace("== to_integer(this->fee) * to_integer(at_size) + to_integer(this->size) - 1", "== to_integer(this->fee) * to_integer(at_size) + to_integer(this->size) - 2"),
                    ]);
                }
                cases
            } else if phase == Some(RoundingPhase::TransportRejections) {
                vec![
                    source.replace("requires this->fee < 8589934592i64;", ""),
                    source.replace("requires to_integer(this->fee) <= 8589934591;", ""),
                    source.replace("requires 0 <= to_integer(this->fee);", ""),
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
                            "(to_integer(result) + 1) * to_integer(this->size)"
                        } else {
                            "(to_integer(result) + -1) * to_integer(this->size)"
                        },
                        "to_integer(result) * to_integer(this->size)",
                    ),
                ]
            }
        } else if name.contains("ResultFit") && name.ends_with("Unified") {
            let down = selected.ends_with("Down");
            let lower = if down {
                "requires -9223372036854775808 * to_integer(this->size) <= to_integer(this->fee) * to_integer(at_size);"
            } else {
                "requires -9223372036854775809 * to_integer(this->size) < to_integer(this->fee) * to_integer(at_size);"
            };
            let upper = if down {
                "requires to_integer(this->fee) * to_integer(at_size) < 9223372036854775808 * to_integer(this->size);"
            } else {
                "requires to_integer(this->fee) * to_integer(at_size) <= 9223372036854775807 * to_integer(this->size);"
            };
            match phase.unwrap() {
                RoundingPhase::AuthorityRejections => vec![
                    source.replace("views this->fee;", ""),
                    source.replace("views this->size;", ""),
                ],
                RoundingPhase::Rejections => vec![
                    source.replace("requires this->size > 0;", ""),
                    source.replace("requires 0 <= at_size;", ""),
                    source.replace("requires at_size <= 2147483647;", ""),
                ],
                RoundingPhase::FitRejections => {
                    let strict = if down { upper } else { lower };
                    vec![source.replace(lower, ""), source.replace(upper, ""), source.replace(strict, &strict.replace(" < ", " <= "))]
                }
                RoundingPhase::TransportRejections => vec![
                    source.replace("requires -9223372036854775808 <= to_integer(this->fee);", ""),
                    source.replace("requires to_integer(this->fee) <= 9223372036854775807;", ""),
                    source.replace("apply(int64_greater_equal_to_integer(this->fee, 0i64));", ""),
                    source.replace("apply(int64_less_than_to_integer(this->fee, 8589934592i64));", ""),
                ],
                RoundingPhase::RoundingRejections => vec![
                    source.replace(if down { "(to_integer(result) + 1) * to_integer(this->size)" } else { "(to_integer(result) + -1) * to_integer(this->size)" }, "to_integer(result) * to_integer(this->size)"),
                    source.replace(if down { "to_integer(result) * to_integer(this->size) <= to_integer(this->fee) * to_integer(at_size)" } else { "to_integer(this->fee) * to_integer(at_size) <= to_integer(result) * to_integer(this->size)" }, if down { "to_integer(result) * to_integer(this->size) < to_integer(this->fee) * to_integer(at_size)" } else { "to_integer(this->fee) * to_integer(at_size) < to_integer(result) * to_integer(this->size)" }),
                ],
                RoundingPhase::NumeratorRejections => vec![
                    source.replace("apply(uint64_multiply_to_integer((uint64)this->fee, (uint64)at_size));", ""),
                    source.replace("to_integer(product) == to_integer(this->fee) * to_integer(at_size)", "to_integer(product) == to_integer(this->fee) * to_integer(at_size) + 1"),
                    source.replace("to_integer(negative_product) == to_integer(this->fee) * to_integer(at_size)", "to_integer(negative_product) == to_integer(this->fee) * to_integer(at_size) + 1"),
                    source.replace(if down { "apply(uint64_divide_to_integer(((uint64)this->fee * (uint64)at_size), (uint64)(uint32)this->size));" } else { "apply(uint64_divide_to_integer(((((uint64)this->fee * (uint64)at_size) + (uint64)this->size) - 1u64), (uint64)(uint32)this->size));" }, ""),
                ],
                RoundingPhase::AdjustedNumeratorRejections => {
                    assert!(!down);
                    vec![
                        source.replace("apply(uint64_add_to_integer(((uint64)this->fee * (uint64)at_size), (uint64)this->size));", ""),
                        source.replace("apply(uint64_subtract_to_integer((((uint64)this->fee * (uint64)at_size) + (uint64)this->size), 1u64));", ""),
                        source.replace("== to_integer(this->fee) * to_integer(at_size) + to_integer(this->size) - 1", "== to_integer(this->fee) * to_integer(at_size) + to_integer(this->size) - 2"),
                    ]
                }
                _ => unreachable!(),
            }
        } else if name.contains("ResultFit") {
            let down = selected.ends_with("Down");
            let lower = if down {
                "requires -9223372036854775808 * to_integer(this->size) <= to_integer(this->fee) * to_integer(at_size);"
            } else {
                "requires -9223372036854775809 * to_integer(this->size) < to_integer(this->fee) * to_integer(at_size);"
            };
            let upper = if down {
                "requires to_integer(this->fee) * to_integer(at_size) < 9223372036854775808 * to_integer(this->size);"
            } else {
                "requires to_integer(this->fee) * to_integer(at_size) <= 9223372036854775807 * to_integer(this->size);"
            };
            if phase == Some(RoundingPhase::Rejections) {
                let strict = if down { upper } else { lower };
                vec![
                    source.replace("views this->size;", ""),
                    source.replace("requires this->size > 0;", ""),
                    source.replace("requires 0 <= at_size;", ""),
                    source.replace("requires at_size <= 2147483647;", ""),
                    source.replace(lower, ""),
                    source.replace(upper, ""),
                    source.replace(strict, &strict.replace(" < ", " <= ")),
                ]
            } else {
                vec![
                    source.replace(if name.ends_with("Negative") { "requires not (this->fee >= 0i64);" } else { "requires this->fee >= 0i64 and not (this->fee < 8589934592i64);" }, ""),
                    source.replace("requires to_integer(this->fee) <= 9223372036854775807;", ""),
                    source.replace("to_integer(product) == to_integer(this->fee) * to_integer(at_size)", "to_integer(product) == to_integer(this->fee) * to_integer(at_size) + 1"),
                    source.replace(if down { "(to_integer(result) + 1) * to_integer(this->size)" } else { "(to_integer(result) + -1) * to_integer(this->size)" }, "to_integer(result) * to_integer(this->size)"),
                    source.replace(if down { "to_integer(result) * to_integer(this->size) <= to_integer(this->fee) * to_integer(at_size)" } else { "to_integer(this->fee) * to_integer(at_size) <= to_integer(result) * to_integer(this->size)" }, if down { "to_integer(result) * to_integer(this->size) < to_integer(this->fee) * to_integer(at_size)" } else { "to_integer(this->fee) * to_integer(at_size) < to_integer(result) * to_integer(this->size)" }),
                ]
            }
        } else if name.ends_with("Unified") {
            if phase == Some(RoundingPhase::Rejections) {
                vec![
                    source.replace("views this->size;", ""),
                    source.replace("requires this->size > 0;", ""),
                    source.replace("requires 0 <= at_size;", ""),
                    source.replace("requires at_size <= this->size;", ""),
                ]
            } else {
                vec![
                    source.replace("requires to_integer(this->fee) <= 9223372036854775807;", ""),
                    source.replace(
                        if selected.ends_with("Down") {
                            "(to_integer(result) + 1) * to_integer(this->size)"
                        } else {
                            "(to_integer(result) + -1) * to_integer(this->size)"
                        },
                        "to_integer(result) * to_integer(this->size)",
                    ),
                    source.replace(
                        "apply(int64_less_than_to_integer(this->fee, 8589934592i64));",
                        "",
                    ),
                ]
            }
        } else if name.ends_with("SymbolicFast") {
            if phase == Some(RoundingPhase::NumeratorRejections) {
                assert!(selected.ends_with("Up"));
                vec![
                    source.replace(
                        "apply(uint64_add_to_integer(((uint64)this->fee * (uint64)at_size), (uint64)this->size));",
                        "",
                    ),
                    source.replace(
                        "apply(uint64_subtract_to_integer((((uint64)this->fee * (uint64)at_size) + (uint64)this->size), 1u64));",
                        "",
                    ),
                    source.replace(
                        "== to_integer(this->fee) * to_integer(at_size) + to_integer(this->size) - 1",
                        "== to_integer(this->fee) * to_integer(at_size) + to_integer(this->size) - 2",
                    ),
                ]
            } else if phase == Some(RoundingPhase::Rejections) {
                vec![
                    source.replace("views this->size;", ""),
                    source.replace("requires this->size > 0;", ""),
                    source.replace("requires 0 <= at_size;", ""),
                    source.replace("requires at_size <= this->size;", ""),
                ]
            } else {
                vec![
                    source.replace("requires this->fee < 8589934592i64;", ""),
                    source.replace("requires to_integer(this->fee) <= 8589934591;", ""),
                    source.replace("requires 0 <= to_integer(this->fee);", ""),
                    source.replace(
                        "ensures to_integer(result) == truncating_quotient(",
                        "ensures to_integer(result) != truncating_quotient(",
                    ),
                    source.replace(
                        if selected.ends_with("Down") {
                            "(to_integer(result) + 1) * to_integer(this->size)"
                        } else {
                            "(to_integer(result) + -1) * to_integer(this->size)"
                        },
                        "to_integer(result) * to_integer(this->size)",
                    ),
                ]
            }
        } else if name.ends_with("Negative") || name.ends_with("PositiveWide") {
            if phase == Some(RoundingPhase::Rejections) {
                vec![
                    source.replace("views this->size;", ""),
                    source.replace("requires this->size > 0;", ""),
                    source.replace("requires 0 <= at_size;", ""),
                    source.replace("requires at_size <= this->size;", ""),
                ]
            } else {
                vec![
                    source.replace(
                        if name.ends_with("Negative") {
                            "requires not (this->fee >= 0i64);"
                        } else {
                            "requires this->fee >= 0i64 and not (this->fee < 8589934592i64);"
                        },
                        "",
                    ),
                    source.replace("requires to_integer(this->fee) <= 9223372036854775807;", ""),
                    source
                        .replace("* to_integer(this->size) <=", "* to_integer(this->size) <")
                        .replace(
                            "<= to_integer(result) * to_integer(this->size)",
                            "< to_integer(result) * to_integer(this->size)",
                        ),
                    source.replace(
                        "to_integer(product) == to_integer(this->fee) * to_integer(at_size)",
                        "to_integer(product) == to_integer(this->fee) * to_integer(at_size) + 1",
                    ),
                    source.replace(
                        if selected.ends_with("Down") {
                            "(to_integer(result) + 1) * to_integer(this->size)"
                        } else {
                            "(to_integer(result) + -1) * to_integer(this->size)"
                        },
                        "to_integer(result) * to_integer(this->size)",
                    ),
                ]
            }
        } else {
            vec![
                source.replace("views this->size;", ""),
                source.replace("requires this->size == 3;", ""),
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
#[ignore = "nightly: 3s in the parallel gate"]
fn pinned_upstream_fee_frac_mul_reexports_and_verifies() {
    check_upstream_fee_frac(
        "FeeFrac::Mul",
        "FeeFracMul",
        include_str!("../integrations/bitcoin-core-money-range/FeeFracMul.click"),
    );
}

#[test]
#[ignore = "nightly: 3s in the parallel gate"]
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
#[ignore = "nightly: 2s in the parallel gate"]
fn pinned_upstream_fee_frac_isempty_reexports_and_verifies() {
    check_upstream_fee_frac(
        "FeeFrac::IsEmpty",
        "FeeFracIsEmpty",
        include_str!("../integrations/bitcoin-core-money-range/FeeFracIsEmpty.click"),
    );
}

#[test]
#[ignore = "nightly: 3s in the parallel gate"]
fn pinned_upstream_fee_frac_add_reexports_and_verifies() {
    check_upstream_fee_frac(
        "FeeFrac::operator+=",
        "FeeFracAdd",
        include_str!("../integrations/bitcoin-core-money-range/FeeFracAdd.click"),
    );
}

#[test]
#[ignore = "nightly: 2s in the parallel gate"]
fn pinned_upstream_fee_frac_addself_reexports_and_verifies() {
    check_upstream_fee_frac(
        "FeeFrac::operator+=",
        "FeeFracAddSelf",
        include_str!("../integrations/bitcoin-core-money-range/FeeFracAddSelf.click"),
    );
}

#[test]
#[ignore = "nightly: 2s in the parallel gate"]
fn pinned_upstream_fee_frac_subtract_reexports_and_verifies() {
    check_upstream_fee_frac(
        "FeeFrac::operator-=",
        "FeeFracSubtract",
        include_str!("../integrations/bitcoin-core-money-range/FeeFracSubtract.click"),
    );
}

#[test]
#[ignore = "nightly: 2s in the parallel gate"]
fn pinned_upstream_fee_frac_subtractself_reexports_and_verifies() {
    check_upstream_fee_frac(
        "FeeFrac::operator-=",
        "FeeFracSubtractSelf",
        include_str!("../integrations/bitcoin-core-money-range/FeeFracSubtractSelf.click"),
    );
}

#[test]
#[ignore = "nightly: 7s in the parallel gate"]
fn pinned_std_span_size_preserves_full_width_extent_offline() {
    let (root, import) = pinned_span_fixture(
        "size",
        "#include <span.h>\nunsigned long probe(std::span<int>& span) { return span.size(); }\n",
    );
    assert_eq!(import.export().reachable_functions.len(), 2);
    assert!(
        import
            .export()
            .reachable_functions
            .iter()
            .all(|function| function.span.file == "sysroot/usr/include/c++/12/span")
    );
    let source = r#"verifying "span-probe.cpp";
uint64 __extent_storage__value_unsigned_long_18446744073709551615__M_extent(const struct __extent_storage__value_unsigned_long_18446744073709551615* this) {
 views this->_M_extent_value;
 ensures result == this->_M_extent_value;
 ensures this->_M_extent_value == old(this->_M_extent_value);
} by { execute(); simp(); }
uint64 span__int__value_unsigned_long_18446744073709551615_size(const struct span__int__value_unsigned_long_18446744073709551615* this) {
 views this->_M_extent._M_extent_value;
 ensures result == this->_M_extent._M_extent_value;
 ensures this->_M_extent._M_extent_value == old(this->_M_extent._M_extent_value);
} by { execute(); simp(); }
uint64 probe(struct span__int__value_unsigned_long_18446744073709551615& span) {
 views span._M_extent._M_extent_value;
 requires span._M_extent._M_extent_value == 18446744073709551615u64;
 ensures result == 18446744073709551615u64;
 ensures span._M_extent._M_extent_value == old(span._M_extent._M_extent_value);
} by { execute(); simp(); }
"#;
    let path = root.join("span.click");
    fs::write(&path, source).unwrap();
    let project = read_click_project(&path, source).unwrap();
    verify_program_prepared_project(&project, &import).unwrap();
    let expanded =
        expand_program_prepared_project_claim_source_by_label(&project, &import, "probe.contract")
            .unwrap();
    let rewritten = project.with_entry_source(expanded.clone());
    verify_program_prepared_project(&rewritten, &import).unwrap();
    let (session, _) =
        C0VerificationSession::new_program_prepared_project(&project, &import).unwrap();
    let position =
        program_prepared_project_tactic_source_position(&rewritten, &import, "probe.contract", 0)
            .unwrap();
    session
        .verify_at_project(&expanded, position.line, position.column)
        .unwrap();
    let hostile = source.replace(" views span._M_extent._M_extent_value;", "");
    let rejected = read_click_project(&path, &hostile).unwrap();
    assert!(verify_program_prepared_project(&rejected, &import).is_err());
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn pinned_std_span_size_bytes_preserves_native_unsigned_product_offline() {
    let (root, import) = pinned_span_fixture(
        "size-bytes",
        "#include <span.h>\nunsigned long probe(std::span<int>& span) { return span.size_bytes(); }\n",
    );
    let source = r#"verifying "span-probe.cpp";
uint64 __extent_storage__value_unsigned_long_18446744073709551615__M_extent(const struct __extent_storage__value_unsigned_long_18446744073709551615* this) {
 views this->_M_extent_value;
 ensures result == this->_M_extent_value;
} by { execute(); simp(); }
uint64 span__int__value_unsigned_long_18446744073709551615_size_bytes(const struct span__int__value_unsigned_long_18446744073709551615* this) {
 views this->_M_extent._M_extent_value;
 ensures result == this->_M_extent._M_extent_value * 4u64;
} by { execute(); simp(); }
uint64 probe(struct span__int__value_unsigned_long_18446744073709551615& span) {
 views span._M_extent._M_extent_value;
 ensures result == span._M_extent._M_extent_value * 4u64;
} by { execute(); simp(); }
"#;
    let path = root.join("span.click");
    fs::write(&path, source).unwrap();
    let project = read_click_project(&path, source).unwrap();
    verify_program_prepared_project(&project, &import).unwrap();
    for claim in [
        "span__int__value_unsigned_long_18446744073709551615_size_bytes.contract",
        "probe.contract",
    ] {
        let expanded =
            expand_program_prepared_project_claim_source_by_label(&project, &import, claim)
                .unwrap();
        let rewritten = project.with_entry_source(expanded.clone());
        verify_program_prepared_project(&rewritten, &import).unwrap();
        let (session, _) =
            C0VerificationSession::new_program_prepared_project(&project, &import).unwrap();
        let position =
            program_prepared_project_tactic_source_position(&rewritten, &import, claim, 0).unwrap();
        session
            .verify_at_project(&expanded, position.line, position.column)
            .unwrap();
    }
    // Size observation needs descriptor authority, but no backing-storage view.
    // Keep the native modulo-2^64 product, including empty and wrapping extents.
    for (extent, bytes) in [
        (0u64, 0u64),
        (1073741823, 4294967292),
        (u64::MAX, u64::MAX - 3),
    ] {
        let concrete = source.replace(
            " ensures result == span._M_extent._M_extent_value * 4u64;",
            &format!(" requires span._M_extent._M_extent_value == {extent}u64;\n ensures result == {bytes}u64;"),
        );
        verify_program_prepared_project(&read_click_project(&path, &concrete).unwrap(), &import)
            .unwrap();
    }
    for hostile in [
        source.replace(" views span._M_extent._M_extent_value;", ""),
        source.replace(" views this->_M_extent_value;", ""),
        source.replace(" views this->_M_extent._M_extent_value;", ""),
        source.replace(
            " ensures result == span._M_extent._M_extent_value * 4u64;",
            " ensures result == span._M_extent._M_extent_value * 8u64;",
        ),
    ] {
        assert!(
            verify_program_prepared_project(&read_click_project(&path, &hostile).unwrap(), &import)
                .is_err()
        );
    }
    fs::remove_dir_all(root).unwrap();
}

fn pinned_span_fixture(name: &str, harness: &str) -> (PathBuf, PreparedCppImport) {
    pinned_span_fixture_with_dependencies(name, harness, &[])
}

fn pinned_span_fixture_with_dependencies(
    name: &str,
    harness: &str,
    additional_dependencies: &[&str],
) -> (PathBuf, PreparedCppImport) {
    let mut dependencies = vec![
        "sysroot/usr/include/c++/12/span",
        "sysroot/usr/include/x86_64-linux-gnu/c++/12/bits/c++config.h",
    ];
    dependencies.extend_from_slice(additional_dependencies);
    pinned_span_fixture_with_exact_dependencies(name, harness, &dependencies)
}

fn pinned_span_fixture_with_exact_dependencies(
    name: &str,
    harness: &str,
    declaration_dependencies: &[&str],
) -> (PathBuf, PreparedCppImport) {
    assert_eq!(
        sha256(ARCHIVE),
        "fceeaef86784f820339f6dc3fc24992eb9c6bcf52edccbf6b7869d79296a3c7d"
    );
    let root =
        std::env::temp_dir().join(format!("click-bitcoin-span-{name}-{}", std::process::id()));
    fs::create_dir(&root).unwrap();
    let archive = root.join("input-closure.tar.gz");
    fs::write(&archive, ARCHIVE).unwrap();
    assert!(
        Command::new("tar")
            .args([
                "-xzf",
                archive.to_str().unwrap(),
                "-C",
                root.to_str().unwrap()
            ])
            .status()
            .unwrap()
            .success()
    );
    for (header, digest) in [
        (
            "bitcoin-src/src/span.h",
            "485dc37ba8ed9b0e8d8212061122a5c1cd4e71e6ecc5380ac1a2277de395b0e3",
        ),
        (
            "sysroot/usr/include/c++/12/span",
            "f1e67ea2c1e2e0faef697f37d995abb59eeb7fb0c0cf13a586fe2799ed9196bd",
        ),
    ] {
        assert_eq!(sha256(&fs::read(root.join(header)).unwrap()), digest);
    }
    fs::create_dir_all(root.join("bitcoin-build/src")).unwrap();
    // Only the harness TU changes; the archived sources and compile flags do not.
    fs::write(root.join("span-probe.cpp"), harness).unwrap();
    let clang = pinned_clang();
    let database = COMMAND
        .replace("@ROOT@", root.to_str().unwrap())
        .replace("@CLANGXX@", clang.to_str().unwrap())
        .replace("@RESOURCE_DIR@", &output(&clang, &["-print-resource-dir"]))
        .replace("bitcoin-src/src/policy/feerate.cpp", "span-probe.cpp");
    fs::write(root.join("compile_commands.json"), database).unwrap();
    let exporter = root.join("click-cpp-exporter");
    fs::copy(std::env::var("CLICK_CPP_EXPORTER").unwrap(), &exporter).unwrap();
    let mut config = serde_json::json!({
        "schema": 6, "language": "c++", "standard": "c++20", "target": "x86_64-unknown-linux-gnu",
        "exceptions": true, "rtti": true, "exporter": exporter,
        "compilation_database": "compile_commands.json", "working_directory": ".",
        "source": "span-probe.cpp", "logical_source": "span-probe.cpp",
        "dependencies": [],
        "function": "probe", "artifact": "span.click-cpp.json"
    });
    let dependencies = config["dependencies"].as_array_mut().unwrap();
    dependencies.extend(declaration_dependencies.iter().map(|path| (*path).into()));
    dependencies.sort_by(|a, b| a.as_str().cmp(&b.as_str()));
    let config_path = root.join("span.click.import.json");
    fs::write(&config_path, serde_json::to_vec_pretty(&config).unwrap()).unwrap();
    refresh_import(&config_path).unwrap();
    fs::remove_file(exporter).unwrap();
    let import = load_import(&config_path).unwrap();
    (root, import)
}

#[test]
// The actual archived declaration is an empty scoped enum. Forwarding all of
// its native values must work without inventing enumerators or backing access.
fn pinned_std_byte_values_verify_with_native_integer_contracts_offline() {
    use click::languages::cpp::CppType;
    let header = "sysroot/usr/include/c++/12/cstddef";
    let (root, import) = pinned_span_fixture_with_exact_dependencies(
        "byte-values",
        "#include <span.h>\nstd::byte probe(std::byte value) noexcept { return value; }\n",
        &[header],
    );
    assert_eq!(
        sha256(&fs::read(root.join(header)).unwrap()),
        "51409c852efecb6e4de3ef7c31e51e63ddd4ec376ee00e3c68e85e6579fa8648"
    );
    let CppType::Enumeration {
        declaration_id,
        name,
        is_scoped,
        is_fixed,
        span,
        ..
    } = &import.export().function.return_type
    else {
        panic!("std::byte lost its nominal enum declaration");
    };
    assert_eq!(declaration_id, "c:@N@std@E@byte");
    assert_eq!(name, "std::byte");
    assert!(*is_scoped && *is_fixed);
    assert_eq!(span.file, header);
    let source = "verifying \"span-probe.cpp\"; uint8 probe(uint8 value) { ensures result == value; } by { execute(); simp(); }";
    let path = root.join("byte.click");
    fs::write(&path, source).unwrap();
    let project = read_click_project(&path, source).unwrap();
    verify_program_prepared_project(&project, &import).unwrap();
    let expanded =
        expand_program_prepared_project_claim_source_by_label(&project, &import, "probe.contract")
            .unwrap();
    let rewritten = project.with_entry_source(expanded.clone());
    verify_program_prepared_project(&rewritten, &import).unwrap();
    let (session, _) =
        C0VerificationSession::new_program_prepared_project(&project, &import).unwrap();
    let position =
        program_prepared_project_tactic_source_position(&rewritten, &import, "probe.contract", 0)
            .unwrap();
    session
        .verify_at_project(&expanded, position.line, position.column)
        .unwrap();
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn pinned_std_span_back_verifies_unchanged_constexpr_assertion_offline() {
    check_pinned_std_span_back("verify");
}

#[test]
#[ignore = "nightly: expansion and retained checks from a 5.6s bundled span-back test"]
fn pinned_std_span_back_expands_and_retains_offline() {
    check_pinned_std_span_back("tools");
}

#[test]
#[ignore = "nightly: whole-project mutations from a 5.6s bundled span-back test"]
fn pinned_std_span_back_rejects_missing_views_and_false_claims_offline() {
    check_pinned_std_span_back("rejections");
}

fn check_pinned_std_span_back(phase: &str) {
    let (root, import) = pinned_span_fixture(
        &format!("back-{phase}"),
        "#include <span.h>\nint& probe(std::span<int>& span) { return span.back(); }\n",
    );
    let source = r#"verifying "span-probe.cpp";
bool std___is_constant_evaluated() { ensures result == 0; } by { execute(); simp(); }
uint64 __extent_storage__value_unsigned_long_18446744073709551615__M_extent(const struct __extent_storage__value_unsigned_long_18446744073709551615* this) {
 views this->_M_extent_value;
 ensures result == this->_M_extent_value;
} by { execute(); simp(); }
uint64 span__int__value_unsigned_long_18446744073709551615_size(const struct span__int__value_unsigned_long_18446744073709551615* this) {
 views this->_M_extent._M_extent_value;
 ensures result == this->_M_extent._M_extent_value;
} by { execute(); simp(); }
bool span__int__value_unsigned_long_18446744073709551615_empty(const struct span__int__value_unsigned_long_18446744073709551615* this) {
 views this->_M_extent._M_extent_value;
 ensures this->_M_extent._M_extent_value == 0u64 implies result == 1;
 ensures this->_M_extent._M_extent_value != 0u64 implies result == 0;
} by { execute(); simp(); }
int32& span__int__value_unsigned_long_18446744073709551615_back(const struct span__int__value_unsigned_long_18446744073709551615* this) {
 views this->_M_ptr;
 views this->_M_extent._M_extent_value;
 views this->_M_ptr[0..1];
 requires this->_M_extent._M_extent_value == 1u64;
 ensures &result == this->_M_ptr;
 ensures result == old(this->_M_ptr[0]);
} by { execute(); simp(); }
int32& probe(struct span__int__value_unsigned_long_18446744073709551615& span) {
 views span._M_ptr;
 views span._M_extent._M_extent_value;
 views span._M_ptr[0..1];
 requires span._M_extent._M_extent_value == 1u64;
 ensures &result == span._M_ptr;
 ensures result == old(span._M_ptr[0]);
} by { execute(); simp(); }
"#;
    let path = root.join("span.click");
    fs::write(&path, source).unwrap();
    let project = read_click_project(&path, source).unwrap();
    if phase != "rejections" {
        verify_program_prepared_project(&project, &import).unwrap();
    }
    if phase == "tools" {
        for claim in [
            "probe.contract",
            "span__int__value_unsigned_long_18446744073709551615_back.contract",
        ] {
            let expanded =
                expand_program_prepared_project_claim_source_by_label(&project, &import, claim)
                    .unwrap();
            let rewritten = project.with_entry_source(expanded.clone());
            verify_program_prepared_project(&rewritten, &import).unwrap();
            let (session, _) =
                C0VerificationSession::new_program_prepared_project(&project, &import).unwrap();
            let position =
                program_prepared_project_tactic_source_position(&rewritten, &import, claim, 0)
                    .unwrap();
            session
                .verify_at_project(&expanded, position.line, position.column)
                .unwrap();
        }
    }
    if phase == "rejections" {
        for hostile in [
            source.replace(" views span._M_ptr[0..1];", ""),
            source.replace(" views this->_M_ptr[0..1];", ""),
            source.replace(
                "requires this->_M_extent._M_extent_value == 1u64;",
                "requires this->_M_extent._M_extent_value == 0u64;",
            ),
            source.replace(
                "ensures &result == span._M_ptr;",
                "ensures &result == span._M_ptr + 1;",
            ),
        ] {
            assert!(
                verify_program_prepared_project(
                    &read_click_project(&path, &hostile).unwrap(),
                    &import
                )
                .is_err()
            );
        }
    }
    fs::remove_dir_all(root).unwrap();
}

#[derive(Clone, Copy)]
enum SpanFrontPhase {
    VerifyAndExpand,
    WriteCaller,
    RejectBounds,
    RejectAuthorityAndClaims,
}

fn check_pinned_std_span_front(phase: SpanFrontPhase) {
    let harness = match phase {
        SpanFrontPhase::WriteCaller => {
            "#include <span.h>\nint probe(std::span<int>& span, int input) { int& element = span.front(); element = input; return element; }\n"
        }
        _ => "#include <span.h>\nint& probe(std::span<int>& span) { return span.front(); }\n",
    };
    let (root, import) = pinned_span_fixture("symbolic-front", harness);
    // The extent is the code's `unsigned long`, uncast. Nothing bounds it
    // from above: the held range states its own extent limit.
    let prelude = r#"verifying "span-probe.cpp";
bool std___is_constant_evaluated() { ensures result == 0; } by { execute(); simp(); }
uint64 __extent_storage__value_unsigned_long_18446744073709551615__M_extent(const struct __extent_storage__value_unsigned_long_18446744073709551615* this) {
 views this->_M_extent_value;
 ensures result == this->_M_extent_value;
} by { execute(); simp(); }
uint64 span__int__value_unsigned_long_18446744073709551615_size(const struct span__int__value_unsigned_long_18446744073709551615* this) {
 views this->_M_extent._M_extent_value;
 ensures result == this->_M_extent._M_extent_value;
} by { execute(); simp(); }
bool span__int__value_unsigned_long_18446744073709551615_empty(const struct span__int__value_unsigned_long_18446744073709551615* this) {
 views this->_M_extent._M_extent_value;
 ensures this->_M_extent._M_extent_value == 0u64 implies result == 1;
 ensures this->_M_extent._M_extent_value != 0u64 implies result == 0;
} by { execute(); simp(); }
int32& span__int__value_unsigned_long_18446744073709551615_front(const struct span__int__value_unsigned_long_18446744073709551615* this) {
 views this->_M_ptr;
 views this->_M_extent._M_extent_value;
 views this->_M_ptr[0..this->_M_extent._M_extent_value];
 requires 1u64 <= this->_M_extent._M_extent_value;
 ensures &result == this->_M_ptr;
 ensures result == old(this->_M_ptr[0]);
} by { execute(); simp(); }
"#;
    let caller = if matches!(phase, SpanFrontPhase::WriteCaller) {
        r#"int32 probe(struct span__int__value_unsigned_long_18446744073709551615& span, int32 input) {
 views span._M_ptr;
 views span._M_extent._M_extent_value;
 owns span._M_ptr[0..span._M_extent._M_extent_value];
 requires 1u64 <= span._M_extent._M_extent_value;
 ensures result == input;
 ensures span._M_ptr[0] == input;
 ensures span._M_ptr == old(span._M_ptr);
 ensures span._M_extent._M_extent_value == old(span._M_extent._M_extent_value);
 ensures forall (k: uint64) { k < span._M_extent._M_extent_value and k != 0u64 implies span._M_ptr[k] == old(span._M_ptr[k]) };
} by {
 execute();
 have span._M_ptr == old(span._M_ptr) by simp();
 have span._M_extent._M_extent_value == old(span._M_extent._M_extent_value) by simp();
 transport(
  forall (k: uint64) { k < span._M_extent._M_extent_value and k != 0u64 implies old(span._M_ptr[k]) == old(span._M_ptr[k]) },
  forall (k: uint64) { k < span._M_extent._M_extent_value and k != 0u64 implies span._M_ptr[k] == old(span._M_ptr[k]) }
 );
 simp(); }

"#
    } else {
        r#"int32& probe(struct span__int__value_unsigned_long_18446744073709551615& span) {
 views span._M_ptr;
 views span._M_extent._M_extent_value;
 views span._M_ptr[0..span._M_extent._M_extent_value];
 requires 1u64 <= span._M_extent._M_extent_value;
 ensures &result == span._M_ptr;
 ensures result == old(span._M_ptr[0]);
} by { execute(); simp(); }
"#
    };
    let source = format!("{prelude}{caller}");
    let source = source.as_str();
    let path = root.join("span.click");
    fs::write(&path, source).unwrap();
    let project = read_click_project(&path, source).unwrap();
    match phase {
        SpanFrontPhase::VerifyAndExpand | SpanFrontPhase::WriteCaller => {
            verify_program_prepared_project(&project, &import).unwrap();
            for claim in [
                "span__int__value_unsigned_long_18446744073709551615_front.contract",
                "probe.contract",
            ] {
                let expanded =
                    expand_program_prepared_project_claim_source_by_label(&project, &import, claim)
                        .unwrap();
                let rewritten = project.with_entry_source(expanded.clone());
                verify_program_prepared_project(&rewritten, &import).unwrap();
                let (session, _) =
                    C0VerificationSession::new_program_prepared_project(&project, &import).unwrap();
                let position =
                    program_prepared_project_tactic_source_position(&rewritten, &import, claim, 0)
                        .unwrap();
                session
                    .verify_at_project(&expanded, position.line, position.column)
                    .unwrap();
            }
            if matches!(phase, SpanFrontPhase::WriteCaller) {
                for hostile in [
                    source.replace(
                        " owns span._M_ptr[0..span._M_extent._M_extent_value];",
                        " views span._M_ptr[0..span._M_extent._M_extent_value];",
                    ),
                    source.replace(
                        " ensures span._M_ptr[0] == input;",
                        " ensures span._M_ptr[0] == old(span._M_ptr[0]);",
                    ),
                ] {
                    assert_ne!(hostile, source);
                    assert!(
                        verify_program_prepared_project(
                            &read_click_project(&path, &hostile).unwrap(),
                            &import
                        )
                        .is_err()
                    );
                }
            }
        }
        SpanFrontPhase::RejectBounds | SpanFrontPhase::RejectAuthorityAndClaims => {
            let hostile = match phase {
                SpanFrontPhase::RejectBounds => vec![
                    source.replace(" requires 1u64 <= this->_M_extent._M_extent_value;", ""),
                    source.replace(" requires 1u64 <= span._M_extent._M_extent_value;", ""),
                    source.replace(
                        " requires 1u64 <= span._M_extent._M_extent_value;",
                        " requires span._M_extent._M_extent_value == 0u64;",
                    ),
                ],
                _ => vec![
                    source.replace(
                        " views this->_M_ptr[0..this->_M_extent._M_extent_value];",
                        "",
                    ),
                    source.replace(" views span._M_ptr[0..span._M_extent._M_extent_value];", ""),
                    source.replace(" views this->_M_ptr;", ""),
                    source.replace(" views this->_M_extent._M_extent_value;", ""),
                    source.replace(
                        " ensures &result == span._M_ptr;",
                        " ensures &result == span._M_ptr + 1;",
                    ),
                    source.replace(
                        " ensures result == old(span._M_ptr[0]);",
                        " ensures result == old(span._M_ptr[0]) + 1;",
                    ),
                ],
            };
            for bad in hostile {
                assert_ne!(bad, source);
                assert!(
                    verify_program_prepared_project(
                        &read_click_project(&path, &bad).unwrap(),
                        &import
                    )
                    .is_err()
                );
            }
        }
    }
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn pinned_std_span_front_bounded_reference_expands_and_retains_offline() {
    check_pinned_std_span_front(SpanFrontPhase::VerifyAndExpand);
}
#[test]
fn pinned_std_span_front_refuses_missing_bounds_and_empty_callers_offline() {
    check_pinned_std_span_front(SpanFrontPhase::RejectBounds);
}
#[test]
fn pinned_std_span_front_refuses_missing_views_and_false_reference_claims_offline() {
    check_pinned_std_span_front(SpanFrontPhase::RejectAuthorityAndClaims);
}

#[test]
fn pinned_std_span_front_reference_writes_require_backing_ownership_offline() {
    check_pinned_std_span_front(SpanFrontPhase::WriteCaller);
}

#[derive(Clone, Copy)]
enum SpanIndexPhase {
    VerifyAndExpand,
    WriteCaller,
    ExpandWriteCaller,
    RetainWriteCaller,
    RejectWriteCaller,
    RejectBounds,
    RejectAuthorityAndClaims,
}

fn check_pinned_std_span_index(phase: SpanIndexPhase) {
    let writes = matches!(
        phase,
        SpanIndexPhase::WriteCaller
            | SpanIndexPhase::ExpandWriteCaller
            | SpanIndexPhase::RetainWriteCaller
            | SpanIndexPhase::RejectWriteCaller
    );
    let harness = if writes {
        "#include <span.h>\nint probe(std::span<int>& span, unsigned long index, int input) { int& element = span[index]; element = input; return element; }\n"
    } else {
        "#include <span.h>\nint& probe(std::span<int>& span, unsigned long index) { return span[index]; }\n"
    };
    let (root, import) = pinned_span_fixture("symbolic-index", harness);
    // The extent and the index are the code's `unsigned long`, uncast.
    // Nothing bounds the extent from above: the held range states its own
    // extent limit.
    let prelude = r#"verifying "span-probe.cpp";
bool std___is_constant_evaluated() { ensures result == 0; } by { execute(); simp(); }
uint64 __extent_storage__value_unsigned_long_18446744073709551615__M_extent(const struct __extent_storage__value_unsigned_long_18446744073709551615* this) {
 views this->_M_extent_value;
 ensures result == this->_M_extent_value;
} by { execute(); simp(); }
uint64 span__int__value_unsigned_long_18446744073709551615_size(const struct span__int__value_unsigned_long_18446744073709551615* this) {
 views this->_M_extent._M_extent_value;
 ensures result == this->_M_extent._M_extent_value;
} by { execute(); simp(); }
int32& span__int__value_unsigned_long_18446744073709551615_operator_index(const struct span__int__value_unsigned_long_18446744073709551615* this, uint64 __idx) {
 views this->_M_ptr;
 views this->_M_extent._M_extent_value;
 views this->_M_ptr[0..this->_M_extent._M_extent_value];
 requires __idx < this->_M_extent._M_extent_value;
 ensures &result == this->_M_ptr + __idx;
 ensures result == old(this->_M_ptr[__idx]);
} by { execute(); simp(); }
"#;
    let caller = if writes {
        r#"int32 probe(struct span__int__value_unsigned_long_18446744073709551615& span, uint64 index, int32 input) {
 views span._M_ptr;
 views span._M_extent._M_extent_value;
 owns span._M_ptr[0..span._M_extent._M_extent_value];
 requires index < span._M_extent._M_extent_value;
 ensures result == input;
 ensures span._M_ptr[index] == input;
 ensures span._M_ptr == old(span._M_ptr);
 ensures span._M_extent._M_extent_value == old(span._M_extent._M_extent_value);
 ensures forall (k: uint64) { k < span._M_extent._M_extent_value and k != index implies span._M_ptr[k] == old(span._M_ptr[k]) };
} by {
 execute();
 have span._M_ptr == old(span._M_ptr) by simp();
 have span._M_extent._M_extent_value == old(span._M_extent._M_extent_value) by simp();
 transport(
  forall (k: uint64) { k < span._M_extent._M_extent_value and k != index implies old(span._M_ptr[k]) == old(span._M_ptr[k]) },
  forall (k: uint64) { k < span._M_extent._M_extent_value and k != index implies span._M_ptr[k] == old(span._M_ptr[k]) }
 );
 simp();
}
"#
    } else {
        r#"int32& probe(struct span__int__value_unsigned_long_18446744073709551615& span, uint64 index) {
 views span._M_ptr;
 views span._M_extent._M_extent_value;
 views span._M_ptr[0..span._M_extent._M_extent_value];
 requires index < span._M_extent._M_extent_value;
 ensures &result == span._M_ptr + index;
 ensures result == old(span._M_ptr[index]);
} by { execute(); simp(); }
"#
    };
    let source = format!("{prelude}{caller}");
    let source = source.as_str();
    let path = root.join("span.click");
    fs::write(&path, source).unwrap();
    let project = read_click_project(&path, source).unwrap();
    match phase {
        SpanIndexPhase::WriteCaller => {
            verify_program_prepared_project(&project, &import).unwrap();
        }
        SpanIndexPhase::ExpandWriteCaller => {
            let expanded = expand_program_prepared_project_claim_source_by_label(
                &project,
                &import,
                "probe.contract",
            )
            .unwrap();
            verify_program_prepared_project(&project.with_entry_source(expanded), &import).unwrap();
        }
        SpanIndexPhase::RetainWriteCaller => {
            let (session, _) =
                C0VerificationSession::new_program_prepared_project(&project, &import).unwrap();
            let position = program_prepared_project_tactic_source_position(
                &project,
                &import,
                "probe.contract",
                0,
            )
            .unwrap();
            session
                .verify_at_project(source, position.line, position.column)
                .unwrap();
        }
        SpanIndexPhase::RejectWriteCaller => {
            for bad in [
                source.replace(
                    " owns span._M_ptr[0..span._M_extent._M_extent_value];",
                    " views span._M_ptr[0..span._M_extent._M_extent_value];",
                ),
                source.replace(
                    " ensures span._M_ptr[index] == input;",
                    " ensures span._M_ptr[index] == old(span._M_ptr[index]);",
                ),
                source.replace(" and k != index implies", " implies"),
            ] {
                assert_ne!(bad, source);
                assert!(
                    verify_program_prepared_project(
                        &read_click_project(&path, &bad).unwrap(),
                        &import
                    )
                    .is_err()
                );
            }
        }
        SpanIndexPhase::VerifyAndExpand => {
            verify_program_prepared_project(&project, &import).unwrap();
            for claim in [
                "span__int__value_unsigned_long_18446744073709551615_operator_index.contract",
                "probe.contract",
            ] {
                let expanded =
                    expand_program_prepared_project_claim_source_by_label(&project, &import, claim)
                        .unwrap();
                let rewritten = project.with_entry_source(expanded.clone());
                verify_program_prepared_project(&rewritten, &import).unwrap();
                let (session, _) =
                    C0VerificationSession::new_program_prepared_project(&project, &import).unwrap();
                let position =
                    program_prepared_project_tactic_source_position(&rewritten, &import, claim, 0)
                        .unwrap();
                session
                    .verify_at_project(&expanded, position.line, position.column)
                    .unwrap();
            }
        }
        SpanIndexPhase::RejectBounds | SpanIndexPhase::RejectAuthorityAndClaims => {
            let hostile = match phase {
                SpanIndexPhase::RejectBounds => vec![
                    source.replace(" requires __idx < this->_M_extent._M_extent_value;", ""),
                    source.replace(
                        " requires __idx < this->_M_extent._M_extent_value;",
                        " requires __idx <= this->_M_extent._M_extent_value;",
                    ),
                    source.replace(
                        " requires index < span._M_extent._M_extent_value;",
                        " requires index == span._M_extent._M_extent_value;",
                    ),
                ],
                _ => vec![
                    source.replace(
                        " views this->_M_ptr[0..this->_M_extent._M_extent_value];",
                        "",
                    ),
                    source.replace(" views span._M_ptr[0..span._M_extent._M_extent_value];", ""),
                    source.replace(" views this->_M_ptr;", ""),
                    source.replace(" views this->_M_extent._M_extent_value;", ""),
                    source.replace(
                        " ensures &result == span._M_ptr + index;",
                        " ensures &result == span._M_ptr + index + 1;",
                    ),
                    source.replace(
                        " ensures result == old(span._M_ptr[index]);",
                        " ensures result == old(span._M_ptr[index]) + 1;",
                    ),
                ],
            };
            for bad in hostile {
                assert_ne!(bad, source);
                assert!(
                    verify_program_prepared_project(
                        &read_click_project(&path, &bad).unwrap(),
                        &import
                    )
                    .is_err()
                );
            }
        }
    }
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn pinned_std_span_index_bounded_reference_expands_and_retains_offline() {
    check_pinned_std_span_index(SpanIndexPhase::VerifyAndExpand);
}
#[test]
fn pinned_std_span_index_refuses_missing_bounds_and_out_of_range_callers_offline() {
    check_pinned_std_span_index(SpanIndexPhase::RejectBounds);
}
#[test]
fn pinned_std_span_index_refuses_missing_views_and_false_reference_claims_offline() {
    check_pinned_std_span_index(SpanIndexPhase::RejectAuthorityAndClaims);
}

#[test]
fn pinned_std_span_index_owned_write_preserves_siblings_offline() {
    check_pinned_std_span_index(SpanIndexPhase::WriteCaller);
}
#[test]
fn pinned_std_span_index_owned_write_expands_offline() {
    check_pinned_std_span_index(SpanIndexPhase::ExpandWriteCaller);
}
#[test]
fn pinned_std_span_index_owned_write_retains_offline() {
    check_pinned_std_span_index(SpanIndexPhase::RetainWriteCaller);
}
#[test]
fn pinned_std_span_index_owned_write_refuses_views_and_false_frames_offline() {
    check_pinned_std_span_index(SpanIndexPhase::RejectWriteCaller);
}

#[derive(Clone, Copy)]
enum SpanBackPhase {
    Ordinary,
    WriteCaller,
    ExpandWriteCaller,
    RetainWriteCaller,
    RejectWriteCaller,
    ExpandBack,
    ExpandCaller,
    RejectBounds,
    RejectAuthority,
    RejectValue,
}

fn check_pinned_std_span_back_symbolic_bounded_range(phase: SpanBackPhase) {
    let harness = match phase {
        SpanBackPhase::WriteCaller
        | SpanBackPhase::ExpandWriteCaller
        | SpanBackPhase::RetainWriteCaller
        | SpanBackPhase::RejectWriteCaller => {
            "#include <span.h>\nint probe(std::span<int>& span, int input) { int& element = span.back(); element = input; return element; }\n"
        }
        _ => "#include <span.h>\nint& probe(std::span<int>& span) { return span.back(); }\n",
    };
    let (root, import) = pinned_span_fixture("symbolic-back", harness);
    // The extent is the code's `unsigned long`, uncast, and the last element
    // is at `extent - 1` in that type. Nothing bounds the extent from above:
    // the held range states its own extent limit.
    let prelude = r#"verifying "span-probe.cpp";
bool std___is_constant_evaluated() { ensures result == 0; } by { execute(); simp(); }
uint64 __extent_storage__value_unsigned_long_18446744073709551615__M_extent(const struct __extent_storage__value_unsigned_long_18446744073709551615* this) {
 views this->_M_extent_value;
 ensures result == this->_M_extent_value;
} by { execute(); simp(); }
uint64 span__int__value_unsigned_long_18446744073709551615_size(const struct span__int__value_unsigned_long_18446744073709551615* this) {
 views this->_M_extent._M_extent_value;
 ensures result == this->_M_extent._M_extent_value;
} by { execute(); simp(); }
bool span__int__value_unsigned_long_18446744073709551615_empty(const struct span__int__value_unsigned_long_18446744073709551615* this) {
 views this->_M_extent._M_extent_value;
 ensures this->_M_extent._M_extent_value == 0u64 implies result == 1;
 ensures this->_M_extent._M_extent_value != 0u64 implies result == 0;
} by { execute(); simp(); }
int32& span__int__value_unsigned_long_18446744073709551615_back(const struct span__int__value_unsigned_long_18446744073709551615* this) {
 views this->_M_ptr;
 views this->_M_extent._M_extent_value;
 views this->_M_ptr[0..this->_M_extent._M_extent_value];
 requires 1u64 <= this->_M_extent._M_extent_value;
 ensures &result == this->_M_ptr + (this->_M_extent._M_extent_value - 1u64);
 ensures result == old(this->_M_ptr[this->_M_extent._M_extent_value - 1u64]);
} by { execute(); simp(); }
"#;
    let caller = if matches!(
        phase,
        SpanBackPhase::WriteCaller
            | SpanBackPhase::ExpandWriteCaller
            | SpanBackPhase::RetainWriteCaller
            | SpanBackPhase::RejectWriteCaller
    ) {
        r#"int32 probe(struct span__int__value_unsigned_long_18446744073709551615& span, int32 input) {
 views span._M_ptr;
 views span._M_extent._M_extent_value;
 owns span._M_ptr[0..span._M_extent._M_extent_value];
 requires 1u64 <= span._M_extent._M_extent_value;
 ensures result == input;
 ensures span._M_ptr[span._M_extent._M_extent_value - 1u64] == input;
 ensures span._M_ptr == old(span._M_ptr);
 ensures span._M_extent._M_extent_value == old(span._M_extent._M_extent_value);
 ensures forall (k: uint64) { k < span._M_extent._M_extent_value and k != span._M_extent._M_extent_value - 1u64 implies span._M_ptr[k] == old(span._M_ptr[k]) };
} by {
 execute();
 have span._M_ptr == old(span._M_ptr) by simp();
 have span._M_extent._M_extent_value == old(span._M_extent._M_extent_value) by simp();
 transport(
  forall (k: uint64) { k < span._M_extent._M_extent_value and k != span._M_extent._M_extent_value - 1u64 implies old(span._M_ptr[k]) == old(span._M_ptr[k]) },
  forall (k: uint64) { k < span._M_extent._M_extent_value and k != span._M_extent._M_extent_value - 1u64 implies span._M_ptr[k] == old(span._M_ptr[k]) }
 );
 simp();
}
"#
    } else {
        r#"int32& probe(struct span__int__value_unsigned_long_18446744073709551615& span) {
 views span._M_ptr;
 views span._M_extent._M_extent_value;
 views span._M_ptr[0..span._M_extent._M_extent_value];
 requires 1u64 <= span._M_extent._M_extent_value;
 ensures &result == span._M_ptr + (span._M_extent._M_extent_value - 1u64);
 ensures result == old(span._M_ptr[span._M_extent._M_extent_value - 1u64]);
} by { execute(); simp(); }
"#
    };
    let source = format!("{prelude}{caller}");
    let source = source.as_str();
    let path = root.join("span.click");
    fs::write(&path, source).unwrap();
    let project = read_click_project(&path, source).unwrap();
    match phase {
        SpanBackPhase::WriteCaller => { verify_program_prepared_project(&project, &import).unwrap(); }
        SpanBackPhase::ExpandWriteCaller => {
            let expanded = expand_program_prepared_project_claim_source_by_label(&project, &import, "probe.contract").unwrap();
            verify_program_prepared_project(&project.with_entry_source(expanded), &import).unwrap();
        }
        SpanBackPhase::RetainWriteCaller => {
            let (session, _) = C0VerificationSession::new_program_prepared_project(&project, &import).unwrap();
            let position = program_prepared_project_tactic_source_position(&project, &import, "probe.contract", 0).unwrap();
            session.verify_at_project(source, position.line, position.column).unwrap();
        }
        SpanBackPhase::RejectWriteCaller => {
            for bad in [
                source.replace(" owns span._M_ptr[0..span._M_extent._M_extent_value];", " views span._M_ptr[0..span._M_extent._M_extent_value];"),
                source.replace(" ensures span._M_ptr[span._M_extent._M_extent_value - 1u64] == input;", " ensures span._M_ptr[span._M_extent._M_extent_value - 1u64] == old(span._M_ptr[span._M_extent._M_extent_value - 1u64]);"),
            ] {
                assert_ne!(bad, source);
                assert!(verify_program_prepared_project(&read_click_project(&path, &bad).unwrap(), &import).is_err());
            }
        }
        SpanBackPhase::Ordinary => {
            verify_program_prepared_project(&project, &import).unwrap();
        }
        SpanBackPhase::ExpandBack | SpanBackPhase::ExpandCaller => {
            verify_program_prepared_project(&project, &import).unwrap();
            let claim = match phase {
                SpanBackPhase::ExpandBack => {
                    "span__int__value_unsigned_long_18446744073709551615_back.contract"
                }
                _ => "probe.contract",
            };
            let expanded =
                expand_program_prepared_project_claim_source_by_label(&project, &import, claim)
                    .unwrap();
            let rewritten = project.with_entry_source(expanded.clone());
            verify_program_prepared_project(&rewritten, &import).unwrap();
            let (session, _) =
                C0VerificationSession::new_program_prepared_project(&project, &import).unwrap();
            let position =
                program_prepared_project_tactic_source_position(&rewritten, &import, claim, 0)
                    .unwrap();
            session
                .verify_at_project(&expanded, position.line, position.column)
                .unwrap();
        }
        SpanBackPhase::RejectBounds
        | SpanBackPhase::RejectAuthority
        | SpanBackPhase::RejectValue => {
            let hostile = match phase {
                SpanBackPhase::RejectBounds => vec![
                    source.replace(" requires 1u64 <= this->_M_extent._M_extent_value;", ""),
                    source.replace("requires 1u64 <= this->_M_extent._M_extent_value;", "requires this->_M_extent._M_extent_value == 0u64;"),
                    source.replace(" requires 1u64 <= span._M_extent._M_extent_value;", ""),
                ],
                SpanBackPhase::RejectAuthority => vec![
                    source.replace(" views this->_M_ptr[0..this->_M_extent._M_extent_value];", ""),
                    source.replace(" views span._M_ptr[0..span._M_extent._M_extent_value];", ""),
                    source.replace(" views this->_M_extent._M_extent_value;", ""),
                ],
                _ => vec![
                    source.replace("ensures &result == span._M_ptr + (span._M_extent._M_extent_value - 1u64);", "ensures &result == span._M_ptr + span._M_extent._M_extent_value;"),
                    source.replace("ensures result == old(span._M_ptr[span._M_extent._M_extent_value - 1u64]);", "ensures result == old(span._M_ptr[span._M_extent._M_extent_value - 1u64]) + 1;"),
                ],
            };
            for bad in hostile {
                assert_ne!(bad, source);
                assert!(
                    verify_program_prepared_project(
                        &read_click_project(&path, &bad).unwrap(),
                        &import
                    )
                    .is_err()
                );
            }
        }
    }
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn pinned_std_span_back_symbolic_bounded_range_offline() {
    check_pinned_std_span_back_symbolic_bounded_range(SpanBackPhase::Ordinary);
}
#[test]
fn pinned_std_span_back_symbolic_expansion_and_retained_verification_offline() {
    check_pinned_std_span_back_symbolic_bounded_range(SpanBackPhase::ExpandBack);
}
#[test]
fn pinned_std_span_back_symbolic_caller_expansion_and_retained_verification_offline() {
    check_pinned_std_span_back_symbolic_bounded_range(SpanBackPhase::ExpandCaller);
}
#[test]
fn pinned_std_span_back_symbolic_refuses_missing_bounds_and_empty_ranges_offline() {
    check_pinned_std_span_back_symbolic_bounded_range(SpanBackPhase::RejectBounds);
}
#[test]
fn pinned_std_span_back_symbolic_refuses_missing_descriptor_and_backing_views_offline() {
    check_pinned_std_span_back_symbolic_bounded_range(SpanBackPhase::RejectAuthority);
}
#[test]
fn pinned_std_span_back_symbolic_refuses_false_alias_value_and_extent_claims_offline() {
    check_pinned_std_span_back_symbolic_bounded_range(SpanBackPhase::RejectValue);
}

#[test]
#[ignore = "nightly: 8s in the parallel gate"]
fn pinned_std_span_data_preserves_pointer_identity_without_backing_authority_offline() {
    let (root, import) = pinned_span_fixture(
        "data",
        "#include <span.h>\nint* probe(std::span<int>& span) { return span.data(); }\n",
    );
    assert_eq!(import.export().reachable_functions.len(), 1);
    assert_eq!(
        import.export().reachable_functions[0].span.file,
        "sysroot/usr/include/c++/12/span"
    );
    let source = r#"verifying "span-probe.cpp";
int32* span__int__value_unsigned_long_18446744073709551615_data(const struct span__int__value_unsigned_long_18446744073709551615* this) {
 views this->_M_ptr;
 ensures result == this->_M_ptr;
 ensures this->_M_ptr == old(this->_M_ptr);
} by { execute(); simp(); }
int32* probe(struct span__int__value_unsigned_long_18446744073709551615& span) {
 views span._M_ptr;
 ensures result == span._M_ptr;
 ensures span._M_ptr == old(span._M_ptr);
} by { execute(); simp(); }
"#;
    let path = root.join("span.click");
    fs::write(&path, source).unwrap();
    let project = read_click_project(&path, source).unwrap();
    verify_program_prepared_project(&project, &import).unwrap();
    let expanded =
        expand_program_prepared_project_claim_source_by_label(&project, &import, "probe.contract")
            .unwrap();
    let rewritten = project.with_entry_source(expanded.clone());
    verify_program_prepared_project(&rewritten, &import).unwrap();
    let (session, _) =
        C0VerificationSession::new_program_prepared_project(&project, &import).unwrap();
    let position =
        program_prepared_project_tactic_source_position(&rewritten, &import, "probe.contract", 0)
            .unwrap();
    session
        .verify_at_project(&expanded, position.line, position.column)
        .unwrap();
    let hostile = source.replace(" views span._M_ptr;", "");
    assert!(
        verify_program_prepared_project(&read_click_project(&path, &hostile).unwrap(), &import)
            .is_err()
    );
    fs::remove_dir_all(root).unwrap();
}

#[test]
#[ignore = "nightly: 8s in the parallel gate"]
fn pinned_std_span_trivial_assignment_copies_nested_descriptor_offline() {
    let (root, import) = pinned_span_fixture(
        "copy-assignment",
        "#include <span.h>\nint probe(std::span<int>& target, const std::span<int>& source) { target = source; return 0; }\n",
    );
    assert!(import.export().reachable_functions.is_empty());
    let source = r#"verifying "span-probe.cpp";
int32 probe(struct span__int__value_unsigned_long_18446744073709551615& target, const struct span__int__value_unsigned_long_18446744073709551615& source) {
 owns target._M_ptr;
 owns target._M_extent._M_extent_value;
 views source._M_ptr;
 views source._M_extent._M_extent_value;
 ensures result == 0;
 ensures target._M_ptr == source._M_ptr;
 ensures target._M_extent._M_extent_value == source._M_extent._M_extent_value;
 ensures source._M_ptr == old(source._M_ptr);
 ensures source._M_extent._M_extent_value == old(source._M_extent._M_extent_value);
} by { execute(); simp(); }
"#;
    let path = root.join("span.click");
    fs::write(&path, source).unwrap();
    let project = read_click_project(&path, source).unwrap();
    verify_program_prepared_project(&project, &import).unwrap();
    let expanded =
        expand_program_prepared_project_claim_source_by_label(&project, &import, "probe.contract")
            .unwrap();
    let rewritten = project.with_entry_source(expanded.clone());
    verify_program_prepared_project(&rewritten, &import).unwrap();
    let (session, _) =
        C0VerificationSession::new_program_prepared_project(&project, &import).unwrap();
    let position =
        program_prepared_project_tactic_source_position(&rewritten, &import, "probe.contract", 0)
            .unwrap();
    session
        .verify_at_project(&expanded, position.line, position.column)
        .unwrap();
    for hostile in [
        source.replace(" views source._M_ptr;", ""),
        source.replace(" owns target._M_extent._M_extent_value;", ""),
        source.replace(" owns target._M_ptr;", " views target._M_ptr;"),
        source.replace("ensures result == 0;", "ensures result == 1;"),
        source.replace(
            "ensures target._M_ptr == source._M_ptr;",
            "ensures target._M_ptr != source._M_ptr;",
        ),
        source.replace(
            "ensures target._M_extent._M_extent_value == source._M_extent._M_extent_value;",
            "ensures target._M_extent._M_extent_value != source._M_extent._M_extent_value;",
        ),
    ] {
        assert!(
            verify_program_prepared_project(&read_click_project(&path, &hostile).unwrap(), &import)
                .is_err()
        );
    }
    fs::remove_dir_all(root).unwrap();
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
#[ignore = "nightly: 16s in the parallel gate"]
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
        "if old(nValue) <= 2100000000000000i64",
        "if old(nValue) < 2100000000000000i64",
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
#[ignore = "nightly: 7s in the parallel gate"]
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
#[ignore = "nightly: 3s in the parallel gate"]
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
#[ignore = "nightly: 3s in the parallel gate"]
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
#[ignore = "nightly: 3s in the parallel gate"]
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
#[ignore = "nightly: 7s in the parallel gate"]
fn upstream_fee_frac_div_bounded_native_correction_is_safe() {
    check_bounded_upstream_rounding(RoundingPhase::Tools);
}

#[test]
#[ignore = "nightly: 4s in the parallel gate"]
fn upstream_fee_frac_div_bounded_full_expansion_reverifies() {
    check_bounded_upstream_rounding(RoundingPhase::FullExpansion);
}

#[test]
#[ignore = "nightly: 5s in the parallel gate"]
fn upstream_fee_frac_div_bounded_rejects_false_rounding_and_missing_guards() {
    check_bounded_upstream_rounding(RoundingPhase::Rejections);
}

#[test]
#[ignore = "nightly: 5s in the parallel gate"]
fn upstream_result_fit_div_down_verifies_native_narrowing_and_correction() {
    check_result_fit_upstream_rounding("Down", RoundingPhase::Tools);
}

#[test]
#[ignore = "nightly: 3s in the parallel gate"]
fn upstream_result_fit_div_down_expands_and_reverifies() {
    check_result_fit_upstream_rounding("Down", RoundingPhase::FullExpansion);
}

#[test]
#[ignore = "nightly: 3s in the parallel gate"]
fn upstream_result_fit_div_down_rejects_missing_or_inclusive_fit_guards() {
    check_result_fit_upstream_rounding("Down", RoundingPhase::Rejections);
}

#[test]
#[ignore = "nightly: 4s in the parallel gate"]
fn upstream_result_fit_div_down_rejects_false_rounding_and_missing_transport() {
    check_result_fit_upstream_rounding("Down", RoundingPhase::TransportRejections);
}

#[test]
#[ignore = "nightly: 5s in the parallel gate"]
fn upstream_result_fit_div_up_verifies_native_narrowing_and_correction() {
    check_result_fit_upstream_rounding("Up", RoundingPhase::Tools);
}

#[test]
#[ignore = "nightly: 3s in the parallel gate"]
fn upstream_result_fit_div_up_expands_and_reverifies() {
    check_result_fit_upstream_rounding("Up", RoundingPhase::FullExpansion);
}

#[test]
#[ignore = "nightly: 3s in the parallel gate"]
fn upstream_result_fit_div_up_rejects_missing_or_inclusive_fit_guards() {
    check_result_fit_upstream_rounding("Up", RoundingPhase::Rejections);
}

#[test]
#[ignore = "nightly: 4s in the parallel gate"]
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
        "views this->fee; views this->size; requires this->fee == 7i64; requires this->size == 3; requires at_size == 2; ensures result == {expected}i64; ensures this->fee == old(this->fee); ensures this->size == old(this->size);"
    );
    let div = include_str!("../integrations/bitcoin-core-money-range/FeeFracDivBounded.click")
        .split_once(';')
        .unwrap()
        .1;
    let source = format!(
        r#"{}
{div}
int64 FeeFrac_EvaluateFee__bool_{instance}(const struct FeeFrac* this, int32 at_size) {{ {contract} }} by {{ execute(); simp(); }}
int64 FeeFrac_EvaluateFee{mode}(const struct FeeFrac* this, int32 at_size) {{ {contract} }} by {{ execute(); simp(); }}
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
#[ignore = "nightly: 4s in the parallel gate"]
fn upstream_fee_evaluation_down_exports_full_graph_and_verifies_fast_case() {
    check_upstream_fee_evaluation_fast("Down", 4, RoundingPhase::Tools);
}
#[test]
#[ignore = "nightly: 4s in the parallel gate"]
fn upstream_fee_evaluation_up_exports_full_graph_and_verifies_fast_case() {
    check_upstream_fee_evaluation_fast("Up", 5, RoundingPhase::Tools);
}

#[test]
#[ignore = "nightly: 6s in the parallel gate"]
fn upstream_fee_evaluation_down_rejects_missing_authority_bounds_and_false_results() {
    check_upstream_fee_evaluation_fast("Down", 4, RoundingPhase::Rejections);
}
#[test]
#[ignore = "nightly: 6s in the parallel gate"]
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
#[ignore = "nightly: 5s in the parallel gate"]
fn upstream_fast_result_fit_down_verifies_beyond_size() {
    check_upstream_result_fit_fast_fee_evaluation("Down", RoundingPhase::Tools);
}

#[test]
#[ignore = "nightly: 6s in the parallel gate"]
fn upstream_fast_result_fit_down_expands_and_reverifies() {
    check_upstream_result_fit_fast_fee_evaluation("Down", RoundingPhase::FullExpansion);
}

#[test]
#[ignore = "nightly: 7s in the parallel gate"]
fn upstream_fast_result_fit_down_rejects_missing_or_weakened_fit_bounds() {
    check_upstream_result_fit_fast_fee_evaluation("Down", RoundingPhase::Rejections);
}

#[test]
#[ignore = "nightly: 5s in the parallel gate"]
fn upstream_fast_result_fit_down_rejects_missing_fee_and_branch_bounds() {
    check_upstream_result_fit_fast_fee_evaluation("Down", RoundingPhase::TransportRejections);
}

#[test]
#[ignore = "nightly: 5s in the parallel gate"]
fn upstream_fast_result_fit_down_rejects_false_rounding() {
    check_upstream_result_fit_fast_fee_evaluation("Down", RoundingPhase::RoundingRejections);
}

#[test]
#[ignore = "nightly: 4s in the parallel gate"]
fn upstream_fast_result_fit_down_rejects_missing_bridges_and_forged_numerator() {
    check_upstream_result_fit_fast_fee_evaluation("Down", RoundingPhase::NumeratorRejections);
}

#[test]
#[ignore = "nightly: 6s in the parallel gate"]
fn upstream_fast_result_fit_up_verifies_beyond_size() {
    check_upstream_result_fit_fast_fee_evaluation("Up", RoundingPhase::Tools);
}

#[test]
#[ignore = "nightly: 6s in the parallel gate"]
fn upstream_fast_result_fit_up_expands_and_reverifies() {
    check_upstream_result_fit_fast_fee_evaluation("Up", RoundingPhase::FullExpansion);
}

#[test]
#[ignore = "nightly: 7s in the parallel gate"]
fn upstream_fast_result_fit_up_rejects_missing_or_weakened_fit_bounds() {
    check_upstream_result_fit_fast_fee_evaluation("Up", RoundingPhase::Rejections);
}

#[test]
#[ignore = "nightly: 5s in the parallel gate"]
fn upstream_fast_result_fit_up_rejects_missing_fee_and_branch_bounds() {
    check_upstream_result_fit_fast_fee_evaluation("Up", RoundingPhase::TransportRejections);
}

#[test]
#[ignore = "nightly: 5s in the parallel gate"]
fn upstream_fast_result_fit_up_rejects_false_rounding() {
    check_upstream_result_fit_fast_fee_evaluation("Up", RoundingPhase::RoundingRejections);
}

#[test]
#[ignore = "nightly: 7s in the parallel gate"]
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
#[ignore = "nightly: 5s in the parallel gate"]
fn upstream_symbolic_fast_fee_evaluation_down_has_exact_floor_bounds() {
    check_upstream_symbolic_fast_fee_evaluation("Down", RoundingPhase::Tools);
}
#[test]
#[ignore = "nightly: 6s in the parallel gate"]
fn upstream_symbolic_fast_fee_evaluation_down_expands_and_reverifies() {
    check_upstream_symbolic_fast_fee_evaluation("Down", RoundingPhase::FullExpansion);
}
#[test]
#[ignore = "nightly: 6s in the parallel gate"]
fn upstream_symbolic_fast_fee_evaluation_down_rejects_missing_authority_and_amount_bounds() {
    check_upstream_symbolic_fast_fee_evaluation("Down", RoundingPhase::Rejections);
}
#[test]
#[ignore = "nightly: 9s in the parallel gate"]
fn upstream_symbolic_fast_fee_evaluation_down_rejects_missing_fee_bounds_and_false_rounding() {
    check_upstream_symbolic_fast_fee_evaluation("Down", RoundingPhase::TransportRejections);
}

#[test]
#[ignore = "nightly: 6s in the parallel gate"]
fn upstream_symbolic_fast_fee_evaluation_up_has_exact_ceiling_bounds() {
    check_upstream_symbolic_fast_fee_evaluation("Up", RoundingPhase::Tools);
}
#[test]
#[ignore = "nightly: 7s in the parallel gate"]
fn upstream_symbolic_fast_fee_evaluation_up_expands_and_reverifies() {
    check_upstream_symbolic_fast_fee_evaluation("Up", RoundingPhase::FullExpansion);
}
#[test]
#[ignore = "nightly: 6s in the parallel gate"]
fn upstream_symbolic_fast_fee_evaluation_up_rejects_missing_authority_and_amount_bounds() {
    check_upstream_symbolic_fast_fee_evaluation("Up", RoundingPhase::Rejections);
}
#[test]
#[ignore = "nightly: 9s in the parallel gate"]
fn upstream_symbolic_fast_fee_evaluation_up_rejects_missing_fee_bounds_and_false_rounding() {
    check_upstream_symbolic_fast_fee_evaluation("Up", RoundingPhase::TransportRejections);
}
#[test]
#[ignore = "nightly: 5s in the parallel gate"]
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
        "to_integer(this->size)",
        "to_integer(this->fee) * to_integer(at_size)",
    );
    let helper = bounds(
        "to_integer(rounded)",
        "to_integer(denominator)",
        "to_integer(product)",
    );
    let fit_bounds = |product: &str| {
        if down {
            [
                format!("-9223372036854775808 * to_integer(this->size) <= {product}"),
                format!("{product} < 9223372036854775808 * to_integer(this->size)"),
            ]
        } else {
            [
                format!("-9223372036854775809 * to_integer(this->size) < {product}"),
                format!("{product} <= 9223372036854775807 * to_integer(this->size)"),
            ]
        }
    };
    let input = fit_bounds("to_integer(this->fee) * to_integer(at_size)");
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
                "this->fee >= 0i64 and not (this->fee < 8589934592i64)"
            } else {
                "not (this->fee >= 0i64)"
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
#[ignore = "nightly: 4s in the parallel gate"]
fn upstream_wide_result_fit_down_negative_verifies_beyond_size() {
    check_upstream_result_fit_wide_fee_evaluation("Down", false, RoundingPhase::Tools);
}

#[test]
#[ignore = "nightly: 5s in the parallel gate"]
fn upstream_wide_result_fit_down_negative_expands_and_reverifies() {
    check_upstream_result_fit_wide_fee_evaluation("Down", false, RoundingPhase::FullExpansion);
}

#[test]
#[ignore = "nightly: 7s in the parallel gate"]
fn upstream_wide_result_fit_down_negative_rejects_missing_or_inclusive_fit_bounds() {
    check_upstream_result_fit_wide_fee_evaluation("Down", false, RoundingPhase::Rejections);
}

#[test]
#[ignore = "nightly: 6s in the parallel gate"]
fn upstream_wide_result_fit_down_negative_rejects_false_rounding_and_missing_transport() {
    check_upstream_result_fit_wide_fee_evaluation(
        "Down",
        false,
        RoundingPhase::TransportRejections,
    );
}

#[test]
#[ignore = "nightly: 4s in the parallel gate"]
fn upstream_wide_result_fit_down_positive_verifies_beyond_size() {
    check_upstream_result_fit_wide_fee_evaluation("Down", true, RoundingPhase::Tools);
}

#[test]
#[ignore = "nightly: 5s in the parallel gate"]
fn upstream_wide_result_fit_down_positive_expands_and_reverifies() {
    check_upstream_result_fit_wide_fee_evaluation("Down", true, RoundingPhase::FullExpansion);
}

#[test]
#[ignore = "nightly: 6s in the parallel gate"]
fn upstream_wide_result_fit_down_positive_rejects_missing_or_inclusive_fit_bounds() {
    check_upstream_result_fit_wide_fee_evaluation("Down", true, RoundingPhase::Rejections);
}

#[test]
#[ignore = "nightly: 5s in the parallel gate"]
fn upstream_wide_result_fit_down_positive_rejects_false_rounding_and_missing_transport() {
    check_upstream_result_fit_wide_fee_evaluation("Down", true, RoundingPhase::TransportRejections);
}

#[test]
#[ignore = "nightly: 5s in the parallel gate"]
fn upstream_wide_result_fit_up_negative_verifies_beyond_size() {
    check_upstream_result_fit_wide_fee_evaluation("Up", false, RoundingPhase::Tools);
}

#[test]
#[ignore = "nightly: 5s in the parallel gate"]
fn upstream_wide_result_fit_up_negative_expands_and_reverifies() {
    check_upstream_result_fit_wide_fee_evaluation("Up", false, RoundingPhase::FullExpansion);
}

#[test]
#[ignore = "nightly: 7s in the parallel gate"]
fn upstream_wide_result_fit_up_negative_rejects_missing_or_inclusive_fit_bounds() {
    check_upstream_result_fit_wide_fee_evaluation("Up", false, RoundingPhase::Rejections);
}

#[test]
#[ignore = "nightly: 6s in the parallel gate"]
fn upstream_wide_result_fit_up_negative_rejects_false_rounding_and_missing_transport() {
    check_upstream_result_fit_wide_fee_evaluation("Up", false, RoundingPhase::TransportRejections);
}

#[test]
#[ignore = "nightly: 5s in the parallel gate"]
fn upstream_wide_result_fit_up_positive_verifies_beyond_size() {
    check_upstream_result_fit_wide_fee_evaluation("Up", true, RoundingPhase::Tools);
}

#[test]
#[ignore = "nightly: 5s in the parallel gate"]
fn upstream_wide_result_fit_up_positive_expands_and_reverifies() {
    check_upstream_result_fit_wide_fee_evaluation("Up", true, RoundingPhase::FullExpansion);
}

#[test]
#[ignore = "nightly: 7s in the parallel gate"]
fn upstream_wide_result_fit_up_positive_rejects_missing_or_inclusive_fit_bounds() {
    check_upstream_result_fit_wide_fee_evaluation("Up", true, RoundingPhase::Rejections);
}

#[test]
#[ignore = "nightly: 6s in the parallel gate"]
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
#[ignore = "nightly: 6s in the parallel gate"]
fn upstream_unified_result_fit_down_verifies_all_fee_branches_beyond_size() {
    check_upstream_result_fit_unified_fee_evaluation("Down", RoundingPhase::Tools);
}

#[test]
#[ignore = "nightly: 6s in the parallel gate"]
fn upstream_unified_result_fit_down_expands_and_reverifies() {
    check_upstream_result_fit_unified_fee_evaluation("Down", RoundingPhase::FullExpansion);
}

#[test]
#[ignore = "nightly: 4s in the parallel gate"]
fn upstream_unified_result_fit_down_rejects_missing_field_authority() {
    check_upstream_result_fit_unified_fee_evaluation("Down", RoundingPhase::AuthorityRejections);
}

#[test]
#[ignore = "nightly: 5s in the parallel gate"]
fn upstream_unified_result_fit_down_rejects_missing_domain_bounds() {
    check_upstream_result_fit_unified_fee_evaluation("Down", RoundingPhase::Rejections);
}

#[test]
#[ignore = "nightly: 6s in the parallel gate"]
fn upstream_unified_result_fit_down_rejects_missing_or_weakened_fit_bounds() {
    check_upstream_result_fit_unified_fee_evaluation("Down", RoundingPhase::FitRejections);
}

#[test]
#[ignore = "nightly: 7s in the parallel gate"]
fn upstream_unified_result_fit_down_rejects_missing_fee_bounds_and_branch_transport() {
    check_upstream_result_fit_unified_fee_evaluation("Down", RoundingPhase::TransportRejections);
}

#[test]
#[ignore = "nightly: 5s in the parallel gate"]
fn upstream_unified_result_fit_down_rejects_false_rounding() {
    check_upstream_result_fit_unified_fee_evaluation("Down", RoundingPhase::RoundingRejections);
}

#[test]
#[ignore = "nightly: 7s in the parallel gate"]
fn upstream_unified_result_fit_down_rejects_missing_bridges_and_forged_numerator() {
    check_upstream_result_fit_unified_fee_evaluation("Down", RoundingPhase::NumeratorRejections);
}

#[test]
#[ignore = "nightly: 6s in the parallel gate"]
fn upstream_unified_result_fit_up_verifies_all_fee_branches_beyond_size() {
    check_upstream_result_fit_unified_fee_evaluation("Up", RoundingPhase::Tools);
}

#[test]
#[ignore = "nightly: 7s in the parallel gate"]
fn upstream_unified_result_fit_up_expands_and_reverifies() {
    check_upstream_result_fit_unified_fee_evaluation("Up", RoundingPhase::FullExpansion);
}

#[test]
#[ignore = "nightly: 5s in the parallel gate"]
fn upstream_unified_result_fit_up_rejects_missing_field_authority() {
    check_upstream_result_fit_unified_fee_evaluation("Up", RoundingPhase::AuthorityRejections);
}

#[test]
#[ignore = "nightly: 5s in the parallel gate"]
fn upstream_unified_result_fit_up_rejects_missing_domain_bounds() {
    check_upstream_result_fit_unified_fee_evaluation("Up", RoundingPhase::Rejections);
}

#[test]
#[ignore = "nightly: 6s in the parallel gate"]
fn upstream_unified_result_fit_up_rejects_missing_or_weakened_fit_bounds() {
    check_upstream_result_fit_unified_fee_evaluation("Up", RoundingPhase::FitRejections);
}

#[test]
#[ignore = "nightly: 7s in the parallel gate"]
fn upstream_unified_result_fit_up_rejects_missing_fee_bounds_and_branch_transport() {
    check_upstream_result_fit_unified_fee_evaluation("Up", RoundingPhase::TransportRejections);
}

#[test]
#[ignore = "nightly: 5s in the parallel gate"]
fn upstream_unified_result_fit_up_rejects_false_rounding() {
    check_upstream_result_fit_unified_fee_evaluation("Up", RoundingPhase::RoundingRejections);
}

#[test]
#[ignore = "nightly: 7s in the parallel gate"]
fn upstream_unified_result_fit_up_rejects_missing_bridges_and_forged_numerator() {
    check_upstream_result_fit_unified_fee_evaluation("Up", RoundingPhase::NumeratorRejections);
}

#[test]
#[ignore = "nightly: 6s in the parallel gate"]
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
#[ignore = "nightly: 5s in the parallel gate"]
fn upstream_unified_fee_evaluation_down_verifies_all_fee_branches() {
    check_upstream_unified_fee_evaluation("Down", RoundingPhase::Tools);
}
#[test]
#[ignore = "nightly: 6s in the parallel gate"]
fn upstream_unified_fee_evaluation_up_verifies_all_fee_branches() {
    check_upstream_unified_fee_evaluation("Up", RoundingPhase::Tools);
}
#[test]
#[ignore = "nightly: 6s in the parallel gate"]
fn upstream_unified_fee_evaluation_down_expands_and_reverifies() {
    check_upstream_unified_fee_evaluation("Down", RoundingPhase::FullExpansion);
}
#[test]
#[ignore = "nightly: 7s in the parallel gate"]
fn upstream_unified_fee_evaluation_up_expands_and_reverifies() {
    check_upstream_unified_fee_evaluation("Up", RoundingPhase::FullExpansion);
}
#[test]
#[ignore = "nightly: 6s in the parallel gate"]
fn upstream_unified_fee_evaluation_down_rejects_missing_domain_bounds() {
    check_upstream_unified_fee_evaluation("Down", RoundingPhase::Rejections);
}
#[test]
#[ignore = "nightly: 6s in the parallel gate"]
fn upstream_unified_fee_evaluation_up_rejects_missing_domain_bounds() {
    check_upstream_unified_fee_evaluation("Up", RoundingPhase::Rejections);
}
#[test]
#[ignore = "nightly: 5s in the parallel gate"]
fn upstream_unified_fee_evaluation_down_rejects_false_rounding_and_missing_transport() {
    check_upstream_unified_fee_evaluation("Down", RoundingPhase::TransportRejections);
}
#[test]
#[ignore = "nightly: 5s in the parallel gate"]
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
#[ignore = "nightly: 5s in the parallel gate"]
fn upstream_negative_fee_evaluation_down_has_symbolic_floor_bounds() {
    check_upstream_negative_fee_evaluation("Down", RoundingPhase::Tools);
}

#[test]
#[ignore = "nightly: 5s in the parallel gate"]
fn upstream_negative_fee_evaluation_up_has_symbolic_ceiling_bounds() {
    check_upstream_negative_fee_evaluation("Up", RoundingPhase::Tools);
}

#[test]
#[ignore = "nightly: 5s in the parallel gate"]
fn upstream_negative_fee_evaluation_down_instance_expands_and_reverifies() {
    check_upstream_negative_fee_evaluation("Down", RoundingPhase::FullExpansion);
}
#[test]
#[ignore = "nightly: 6s in the parallel gate"]
fn upstream_negative_fee_evaluation_up_instance_expands_and_reverifies() {
    check_upstream_negative_fee_evaluation("Up", RoundingPhase::FullExpansion);
}
#[test]
#[ignore = "nightly: 6s in the parallel gate"]
fn upstream_negative_fee_evaluation_down_rejects_false_bounds_and_missing_guards() {
    check_upstream_negative_fee_evaluation("Down", RoundingPhase::Rejections);
}
#[test]
#[ignore = "nightly: 6s in the parallel gate"]
fn upstream_negative_fee_evaluation_up_rejects_false_bounds_and_missing_guards() {
    check_upstream_negative_fee_evaluation("Up", RoundingPhase::Rejections);
}

#[test]
#[ignore = "nightly: 7s in the parallel gate"]
fn upstream_negative_fee_evaluation_down_rejects_forged_product_and_rounding_transport() {
    check_upstream_negative_fee_evaluation("Down", RoundingPhase::TransportRejections);
}
#[test]
#[ignore = "nightly: 6s in the parallel gate"]
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
#[ignore = "nightly: 5s in the parallel gate"]
fn upstream_positive_wide_fee_evaluation_down_has_symbolic_bounds() {
    check_upstream_positive_wide_fee_evaluation("Down", RoundingPhase::Tools);
}

#[test]
#[ignore = "nightly: 5s in the parallel gate"]
fn upstream_positive_wide_fee_evaluation_down_instance_expands_and_reverifies() {
    check_upstream_positive_wide_fee_evaluation("Down", RoundingPhase::FullExpansion);
}

#[test]
#[ignore = "nightly: 6s in the parallel gate"]
fn upstream_positive_wide_fee_evaluation_down_rejects_false_bounds_and_missing_guards() {
    check_upstream_positive_wide_fee_evaluation("Down", RoundingPhase::Rejections);
}

#[test]
#[ignore = "nightly: 7s in the parallel gate"]
fn upstream_positive_wide_fee_evaluation_down_rejects_forged_product_and_rounding_transport() {
    check_upstream_positive_wide_fee_evaluation("Down", RoundingPhase::TransportRejections);
}

#[test]
#[ignore = "nightly: 5s in the parallel gate"]
fn upstream_positive_wide_fee_evaluation_up_has_symbolic_bounds() {
    check_upstream_positive_wide_fee_evaluation("Up", RoundingPhase::Tools);
}

#[test]
#[ignore = "nightly: 5s in the parallel gate"]
fn upstream_positive_wide_fee_evaluation_up_instance_expands_and_reverifies() {
    check_upstream_positive_wide_fee_evaluation("Up", RoundingPhase::FullExpansion);
}

#[test]
#[ignore = "nightly: 6s in the parallel gate"]
fn upstream_positive_wide_fee_evaluation_up_rejects_false_bounds_and_missing_guards() {
    check_upstream_positive_wide_fee_evaluation("Up", RoundingPhase::Rejections);
}

#[test]
#[ignore = "nightly: 7s in the parallel gate"]
fn upstream_positive_wide_fee_evaluation_up_rejects_forged_product_and_rounding_transport() {
    check_upstream_positive_wide_fee_evaluation("Up", RoundingPhase::TransportRejections);
}

#[test]
#[ignore = "nightly: 2s in the parallel gate"]
fn pinned_upstream_fee_rate_getfee_imports_converted_call_graph() {
    check_upstream_cpp_rounding_phase(
        "CFeeRate::GetFee",
        "CFeeRateGetFeeImported",
        "",
        "bitcoin-src/src/policy/feerate.cpp",
        "sysroot/usr/include/x86_64-linux-gnu/bits/stdint-intn.h",
        None,
    );
}

fn getfee_source() -> String {
    let unified = unified_fee_evaluation_source_with_profile("Up", true);
    let helpers = unified
        .split_once("\ncontract int64 FastOversizeFee")
        .unwrap()
        .0
        .replace(
            "verifying \"bitcoin-src/src/util/feefrac.h\";",
            "verifying \"bitcoin-src/src/policy/feerate.cpp\";",
        );
    let empty = include_str!("../integrations/bitcoin-core-money-range/FeeFracIsEmpty.click")
        .split_once(';')
        .unwrap()
        .1;
    format!(
        "{helpers}\n{empty}\n{}",
        include_str!("../integrations/bitcoin-core-money-range/CFeeRateGetFee.click.in")
    )
}

fn check_getfee(name: &str, phase: Option<RoundingPhase>) {
    check_upstream_cpp_rounding_phase(
        "CFeeRate::GetFee",
        name,
        &getfee_source(),
        "bitcoin-src/src/policy/feerate.cpp",
        "sysroot/usr/include/x86_64-linux-gnu/bits/stdint-intn.h",
        phase,
    );
}

#[test]
#[ignore = "nightly: 6s in the parallel gate"]
fn upstream_getfee_expands_and_reverifies_offline() {
    check_getfee(
        "CFeeRateGetFeeExpansion",
        Some(RoundingPhase::FullExpansion),
    );
}

#[test]
#[ignore = "nightly: 8s in the parallel gate"]
fn upstream_getfee_retains_certificates_offline() {
    check_getfee("CFeeRateGetFeeRetained", Some(RoundingPhase::Tools));
}

#[test]
#[ignore = "nightly: 5s in the parallel gate"]
fn upstream_getfee_modular_callers_cover_empty_negative_and_oversize_inputs() {
    let source = getfee_source();
    let root_contract = source
        .split_once("int64 CFeeRate_GetFee(")
        .unwrap()
        .1
        .split_once("} by {")
        .unwrap()
        .0;
    let mut callers = String::new();
    for (name, requirements, conclusion) in [
        (
            "NegativeMinimumFee",
            "requires this->m_feerate.base.fee == -1i64; requires this->m_feerate.base.size == 2; requires virtual_bytes == 1; requires virtual_bytes != 0; requires this->m_feerate.base.fee < 0i64;",
            "ensures result != 0i64;",
        ),
        (
            "PositiveOversizeFee",
            "requires this->m_feerate.base.fee == 7i64; requires this->m_feerate.base.size == 1; requires virtual_bytes == 2;",
            "",
        ),
        (
            "ZeroAmountFee",
            "requires this->m_feerate.base.fee == 7i64; requires this->m_feerate.base.size == 2; requires virtual_bytes == 0;",
            "",
        ),
    ] {
        let proof = if conclusion.is_empty() {
            "execute(); simp();"
        } else {
            "have this->m_feerate.base.size != 0 by { simp(); } execute(); extract(result != 0i64); simp();"
        };
        let contract = root_contract.replacen(
            "views this->m_feerate.base.fee;",
            &format!("{requirements}\n    views this->m_feerate.base.fee;"),
            1,
        );
        callers.push_str(&format!("\ncontract int64 {name}({contract} {conclusion} }}\ntheorem {name}_application() executes CFeeRate_GetFee(const struct CFeeRate* this, int32 virtual_bytes) {{ ensures {name}(&CFeeRate_GetFee) by {{ {proof} }} }}\n"));
    }
    callers.push_str(r#"
contract int64 EmptyRate(const struct CFeeRate* this, int32 virtual_bytes) {
    views this->m_feerate.base.fee; views this->m_feerate.base.size;
    requires this->m_feerate.base.size == 0;
    requires 0 <= virtual_bytes; requires virtual_bytes <= 2147483647;
    ensures result == 0i64;
    ensures this->m_feerate.base.fee == old(this->m_feerate.base.fee);
    ensures this->m_feerate.base.size == old(this->m_feerate.base.size);
}
theorem empty_rate_application() executes CFeeRate_GetFee(const struct CFeeRate* this, int32 virtual_bytes) {
    ensures EmptyRate(&CFeeRate_GetFee) by {
        have this->m_feerate.base.size >= 0 by { arithmetic() using { this->m_feerate.base.size == 0; } }
        have this->m_feerate.base.size <= 2147483647 by { arithmetic() using { this->m_feerate.base.size == 0; } }
        have this->m_feerate.base.size != 0 implies -9223372036854775808 <= to_integer(this->m_feerate.base.fee) by { simp(); }
        have this->m_feerate.base.size != 0 implies to_integer(this->m_feerate.base.fee) <= 9223372036854775807 by { simp(); }
        have this->m_feerate.base.size != 0 implies -9223372036854775809 * to_integer(this->m_feerate.base.size) < to_integer(this->m_feerate.base.fee) * to_integer(virtual_bytes) by { simp(); }
        have this->m_feerate.base.size != 0 implies to_integer(this->m_feerate.base.fee) * to_integer(virtual_bytes) <= 9223372036854775807 * to_integer(this->m_feerate.base.size) by { simp(); }
        execute(); simp();
    }
}
"#);
    check_upstream_cpp_rounding_phase(
        "CFeeRate::GetFee",
        "CFeeRateGetFeeCallers",
        &format!("{source}{callers}"),
        "bitcoin-src/src/policy/feerate.cpp",
        "sysroot/usr/include/x86_64-linux-gnu/bits/stdint-intn.h",
        None,
    );
}

#[test]
#[ignore = "nightly: 5s in the parallel gate"]
fn upstream_getfee_rejects_missing_fee_authority() {
    check_getfee(
        "CFeeRateGetFeeMissingFeeAuthority",
        Some(RoundingPhase::Rejections),
    );
}
#[test]
#[ignore = "nightly: 5s in the parallel gate"]
fn upstream_getfee_rejects_missing_size_authority() {
    check_getfee(
        "CFeeRateGetFeeMissingSizeAuthority",
        Some(RoundingPhase::Rejections),
    );
}
#[test]
#[ignore = "nightly: 5s in the parallel gate"]
fn upstream_getfee_rejects_missing_amount_guard() {
    check_getfee(
        "CFeeRateGetFeeMissingAmountGuard",
        Some(RoundingPhase::Rejections),
    );
}
#[test]
#[ignore = "nightly: 5s in the parallel gate"]
fn upstream_getfee_rejects_missing_size_guard() {
    check_getfee(
        "CFeeRateGetFeeMissingSizeGuard",
        Some(RoundingPhase::Rejections),
    );
}
#[test]
#[ignore = "nightly: 6s in the parallel gate"]
fn upstream_getfee_rejects_missing_lower_fit() {
    check_getfee(
        "CFeeRateGetFeeMissingLowerFit",
        Some(RoundingPhase::Rejections),
    );
}
#[test]
#[ignore = "nightly: 6s in the parallel gate"]
fn upstream_getfee_rejects_missing_upper_fit() {
    check_getfee(
        "CFeeRateGetFeeMissingUpperFit",
        Some(RoundingPhase::Rejections),
    );
}
#[test]
#[ignore = "nightly: 5s in the parallel gate"]
fn upstream_getfee_rejects_inclusive_lower_fit() {
    check_getfee(
        "CFeeRateGetFeeInclusiveLowerFit",
        Some(RoundingPhase::Rejections),
    );
}
#[test]
#[ignore = "nightly: 6s in the parallel gate"]
fn upstream_getfee_rejects_false_empty_result() {
    check_getfee("CFeeRateGetFeeFalseEmpty", Some(RoundingPhase::Rejections));
}
#[test]
#[ignore = "nightly: 7s in the parallel gate"]
fn upstream_getfee_rejects_false_minimum_correction() {
    check_getfee(
        "CFeeRateGetFeeFalseCorrection",
        Some(RoundingPhase::Rejections),
    );
}
#[test]
#[ignore = "nightly: 5s in the parallel gate"]
fn upstream_getfee_rejects_missing_fee_observer_bounds() {
    check_getfee(
        "CFeeRateGetFeeMissingFeeBounds",
        Some(RoundingPhase::Rejections),
    );
}
#[test]
#[ignore = "nightly: 4s in the parallel gate"]
fn upstream_getfee_rejects_stale_reachable_header_offline() {
    check_getfee(
        "CFeeRateGetFeeStaleHeader",
        Some(RoundingPhase::TransportRejections),
    );
}

#[test]
#[ignore = "nightly: 4s in the parallel gate"]
fn upstream_getfee_composes_empty_and_nonempty_result_fit_profiles() {
    check_upstream_cpp_rounding_phase(
        "CFeeRate::GetFee",
        "CFeeRateGetFeeProof",
        &getfee_source(),
        "bitcoin-src/src/policy/feerate.cpp",
        "sysroot/usr/include/x86_64-linux-gnu/bits/stdint-intn.h",
        None,
    );
}

fn getfee_per_k_source() -> String {
    let unified = unified_fee_evaluation_source_with_profile("Down", true);
    let helpers = unified
        .split_once("\ncontract int64 FastOversizeFee")
        .unwrap()
        .0;
    format!(
        "{}\n{}",
        helpers.replace(
            "verifying \"bitcoin-src/src/util/feefrac.h\";",
            "verifying \"bitcoin-src/src/policy/feerate.h\";"
        ),
        include_str!("../integrations/bitcoin-core-money-range/CFeeRateGetFeePerK.click.in")
    )
}
fn check_getfee_per_k(name: &str, phase: Option<RoundingPhase>) {
    check_upstream_cpp_rounding_phase(
        "CFeeRate::GetFeePerK",
        name,
        &getfee_per_k_source(),
        "bitcoin-src/src/policy/feerate.h",
        "sysroot/usr/include/x86_64-linux-gnu/bits/stdint-intn.h",
        phase,
    );
}
#[test]
#[ignore = "nightly: 3s in the parallel gate"]
fn upstream_getfee_per_k_verifies_unchanged_down_rounding() {
    check_getfee_per_k("CFeeRateGetFeePerK", None);
}
#[test]
#[ignore = "nightly: 4s in the parallel gate"]
fn upstream_getfee_per_k_expands_and_reverifies_offline() {
    check_getfee_per_k(
        "CFeeRateGetFeePerKExpansion",
        Some(RoundingPhase::FullExpansion),
    );
}
#[test]
#[ignore = "nightly: 5s in the parallel gate"]
fn upstream_getfee_per_k_retains_certificates_offline() {
    check_getfee_per_k("CFeeRateGetFeePerKRetained", Some(RoundingPhase::Tools));
}
#[test]
#[ignore = "nightly: 4s in the parallel gate"]
fn upstream_getfee_per_k_rejects_zero_size() {
    check_getfee_per_k(
        "CFeeRateGetFeePerKMissingSizeGuard",
        Some(RoundingPhase::Rejections),
    );
}
#[test]
#[ignore = "nightly: 4s in the parallel gate"]
fn upstream_getfee_per_k_rejects_missing_authority() {
    check_getfee_per_k(
        "CFeeRateGetFeePerKMissingFeeAuthority",
        Some(RoundingPhase::Rejections),
    );
}
#[test]
#[ignore = "nightly: 4s in the parallel gate"]
fn upstream_getfee_per_k_rejects_missing_lower_fit() {
    check_getfee_per_k(
        "CFeeRateGetFeePerKMissingLowerFit",
        Some(RoundingPhase::Rejections),
    );
}
#[test]
#[ignore = "nightly: 4s in the parallel gate"]
fn upstream_getfee_per_k_rejects_inclusive_upper_fit() {
    check_getfee_per_k(
        "CFeeRateGetFeePerKInclusiveUpperFit",
        Some(RoundingPhase::Rejections),
    );
}
#[test]
#[ignore = "nightly: 4s in the parallel gate"]
fn upstream_getfee_per_k_rejects_false_rounding() {
    check_getfee_per_k(
        "CFeeRateGetFeePerKFalseRounding",
        Some(RoundingPhase::Rejections),
    );
}

#[test]
#[ignore = "nightly: 4s in the parallel gate"]
fn upstream_getfee_per_k_modular_callers_cover_signed_and_oversize_rates() {
    let source = getfee_per_k_source();
    let root_contract = source
        .split_once("int64 CFeeRate_GetFeePerK(")
        .unwrap()
        .1
        .split_once("} by {")
        .unwrap()
        .0;
    let mut callers = String::new();
    for (name, fee, size) in [
        ("PositivePerK", 7_i64, 2),
        ("NegativePerK", -1, 2),
        ("ZeroPerK", 0, 2),
        ("WidePerK", 8589934592, 1000),
    ] {
        let contract = root_contract.replacen("views this->m_feerate.base.fee;", &format!("requires this->m_feerate.base.fee == {fee}i64; requires this->m_feerate.base.size == {size}; views this->m_feerate.base.fee;"), 1);
        callers.push_str(&format!("\ncontract int64 {name}({contract} }}\ntheorem {name}_application() executes CFeeRate_GetFeePerK(const struct CFeeRate* this) {{ ensures {name}(&CFeeRate_GetFeePerK) by {{ execute(); simp(); }} }}\n"));
    }
    check_upstream_cpp_rounding_phase(
        "CFeeRate::GetFeePerK",
        "CFeeRateGetFeePerKCallers",
        &format!("{source}{callers}"),
        "bitcoin-src/src/policy/feerate.h",
        "sysroot/usr/include/x86_64-linux-gnu/bits/stdint-intn.h",
        None,
    );
}

#[test]
fn pinned_std_span_back_reference_writes_require_backing_ownership_offline() {
    check_pinned_std_span_back_symbolic_bounded_range(SpanBackPhase::WriteCaller);
}

#[test]
fn pinned_std_span_back_reference_write_expansion_offline() {
    check_pinned_std_span_back_symbolic_bounded_range(SpanBackPhase::ExpandWriteCaller);
}
#[test]
fn pinned_std_span_back_reference_write_retained_offline() {
    check_pinned_std_span_back_symbolic_bounded_range(SpanBackPhase::RetainWriteCaller);
}
#[test]
fn pinned_std_span_back_reference_write_refuses_missing_ownership_and_unchanged_claim_offline() {
    check_pinned_std_span_back_symbolic_bounded_range(SpanBackPhase::RejectWriteCaller);
}

// The unchanged pinned library constructs both descriptor fields through
// checked calls; backing range authority remains a caller-owned view.
#[test]
fn pinned_std_span_local_constructor_verifies_native_extent_offline() {
    check_pinned_std_span_local_constructor(SpanConstructionPhase::VerifyAndExpand);
}

#[test]
fn pinned_std_span_local_constructor_retained_offline() {
    check_pinned_std_span_local_constructor(SpanConstructionPhase::Retain);
}

#[test]
fn pinned_std_span_local_constructor_requires_backing_view_offline() {
    check_pinned_std_span_local_constructor(SpanConstructionPhase::RejectBacking);
}

enum SpanConstructionPhase {
    VerifyAndExpand,
    Retain,
    RejectBacking,
}

fn check_pinned_std_span_local_constructor(phase: SpanConstructionPhase) {
    let (root, import) = pinned_span_fixture_with_dependencies(
        "local-constructor",
        "#include <span.h>\nunsigned long probe(int* backing, unsigned long count) { std::span<int> span(backing, count); return span.size(); }\n",
        &["sysroot/usr/include/c++/12/bits/ptr_traits.h"],
    );
    let names = import
        .export()
        .reachable_functions
        .iter()
        .map(|function| function.name.as_str())
        .collect::<Vec<_>>();
    let address = names
        .iter()
        .find(|name| name.starts_with("std_to_address"))
        .unwrap();
    let inner_address = names
        .iter()
        .find(|name| name.starts_with("std___to_address"))
        .unwrap();
    let source = r#"verifying "span-probe.cpp";
int32* TO_ADDRESS(int32* __ptr) { ensures result == __ptr; } by { execute(); simp(); }
int32* INNER_ADDRESS(int32* __ptr) { ensures result == __ptr; } by { execute(); simp(); }
void __extent_storage__value_unsigned_long_18446744073709551615_constructor(struct __extent_storage__value_unsigned_long_18446744073709551615* this, uint64 __extent) {
 owns this->_M_extent_value;
 ensures this->_M_extent_value == __extent;
} by { execute(); simp(); }
void span__int__value_unsigned_long_18446744073709551615_constructor(struct span__int__value_unsigned_long_18446744073709551615* this, int32* __first, uint64 __count) {
 owns this->_M_ptr;
 owns this->_M_extent._M_extent_value;
 views __first[0..(int32)__count];
 requires 0u64 <= __count;
 requires __count <= 1073741823u64;
 ensures this->_M_ptr == __first;
 ensures this->_M_extent._M_extent_value == __count;
} by { execute(); simp(); }
uint64 __extent_storage__value_unsigned_long_18446744073709551615__M_extent(const struct __extent_storage__value_unsigned_long_18446744073709551615* this) {
 views this->_M_extent_value;
 ensures result == this->_M_extent_value;
} by { execute(); simp(); }
uint64 span__int__value_unsigned_long_18446744073709551615_size(const struct span__int__value_unsigned_long_18446744073709551615* this) {
 views this->_M_extent._M_extent_value;
 ensures result == this->_M_extent._M_extent_value;
} by { execute(); simp(); }
uint64 probe(int32* backing, uint64 count) {
 views backing[0..(int32)count];
 requires 1u64 <= count;
 requires count <= 1073741823u64;
 ensures result == count;
} by { execute(); simp(); }
"#.replace("TO_ADDRESS", address).replace("INNER_ADDRESS", inner_address);
    let path = root.join("span.click");
    fs::write(&path, &source).unwrap();
    let project = read_click_project(&path, &source).unwrap();
    match phase {
        SpanConstructionPhase::VerifyAndExpand => {
            verify_program_prepared_project(&project, &import).unwrap();
            let expanded = expand_program_prepared_project_claim_source_by_label(
                &project,
                &import,
                "probe.contract",
            )
            .unwrap();
            verify_program_prepared_project(&project.with_entry_source(expanded), &import).unwrap();
        }
        SpanConstructionPhase::Retain => {
            let (session, _) =
                C0VerificationSession::new_program_prepared_project(&project, &import).unwrap();
            let position = program_prepared_project_tactic_source_position(
                &project,
                &import,
                "probe.contract",
                0,
            )
            .unwrap();
            session
                .verify_at_project(&source, position.line, position.column)
                .unwrap();
        }
        SpanConstructionPhase::RejectBacking => {
            let missing = source.replace(" views backing[0..(int32)count];", "");
            assert!(
                verify_program_prepared_project(
                    &read_click_project(&path, &missing).unwrap(),
                    &import
                )
                .is_err()
            );
        }
    }
    fs::remove_dir_all(root).unwrap();
}

// The original pinned first() returns a descriptor with any bounded prefix,
// including zero; no source adaptation or user-managed return slot is used.
#[test]
fn pinned_std_span_first_constructs_zero_or_nonzero_extent_offline() {
    check_pinned_std_span_first(false, false);
}

#[test]
fn pinned_std_span_first_zero_needs_no_backing_authority_offline() {
    check_pinned_std_span_first(true, false);
}

#[test]
#[ignore = "nightly: 3.9s pinned returned first expansion and retained verification"]
fn pinned_std_span_first_expands_and_retains_offline() {
    check_pinned_std_span_first(false, true);
}

fn pinned_span_construction_contracts(import: &PreparedCppImport) -> String {
    let names = import
        .export()
        .reachable_functions
        .iter()
        .map(|function| function.name.as_str())
        .collect::<Vec<_>>();
    let address = names
        .iter()
        .find(|name| name.starts_with("std_to_address"))
        .unwrap();
    let inner_address = names
        .iter()
        .find(|name| name.starts_with("std___to_address"))
        .unwrap();
    r#"verifying "span-probe.cpp";
bool std___is_constant_evaluated() { ensures result == 0; } by { execute(); simp(); }
int32* TO_ADDRESS(int32* __ptr) { ensures result == __ptr; } by { execute(); simp(); }
int32* INNER_ADDRESS(int32* __ptr) { ensures result == __ptr; } by { execute(); simp(); }
void __extent_storage__value_unsigned_long_18446744073709551615_constructor(struct __extent_storage__value_unsigned_long_18446744073709551615* this, uint64 __extent) {
 owns this->_M_extent_value;
 ensures this->_M_extent_value == __extent;
} by { execute(); simp(); }
void span__int__value_unsigned_long_18446744073709551615_constructor(struct span__int__value_unsigned_long_18446744073709551615* this, int32* __first, uint64 __count) {
 owns this->_M_ptr;
 owns this->_M_extent._M_extent_value;
 views __first[0..(int32)__count];
 requires 0u64 <= __count;
 requires __count <= 1073741823u64;
 ensures this->_M_ptr == __first;
 ensures this->_M_extent._M_extent_value == __count;
} by { execute(); simp(); }
uint64 __extent_storage__value_unsigned_long_18446744073709551615__M_extent(const struct __extent_storage__value_unsigned_long_18446744073709551615* this) {
 views this->_M_extent_value;
 ensures result == this->_M_extent_value;
} by { execute(); simp(); }
uint64 span__int__value_unsigned_long_18446744073709551615_size(const struct span__int__value_unsigned_long_18446744073709551615* this) {
 views this->_M_extent._M_extent_value;
 ensures result == this->_M_extent._M_extent_value;
} by { execute(); simp(); }
int32* span__int__value_unsigned_long_18446744073709551615_data(const struct span__int__value_unsigned_long_18446744073709551615* this) {
 views this->_M_ptr;
 ensures result == this->_M_ptr;
} by { execute(); simp(); }
struct span__int__value_unsigned_long_18446744073709551615 span__int__value_unsigned_long_18446744073709551615_first(const struct span__int__value_unsigned_long_18446744073709551615* this, uint64 __count) {
 views this->_M_ptr;
 views this->_M_extent._M_extent_value;
 views this->_M_ptr[0..(int32)__count];
 requires __count <= this->_M_extent._M_extent_value;
 requires this->_M_extent._M_extent_value <= 1073741823u64;
 ensures result._M_ptr == old(this->_M_ptr);
 ensures result._M_extent._M_extent_value == __count;
 ensures this->_M_ptr == old(this->_M_ptr);
 ensures this->_M_extent._M_extent_value == old(this->_M_extent._M_extent_value);
} by { execute(); simp(); }
"#.replace("TO_ADDRESS", address).replace("INNER_ADDRESS", inner_address)
}

fn check_pinned_std_span_first(empty: bool, expand_and_retain: bool) {
    let harness = if empty {
        "#include <span.h>\nstd::span<int> probe(const std::span<int>& span) noexcept { return span.first(0); }\n"
    } else {
        "#include <span.h>\nstd::span<int> probe(const std::span<int>& span, unsigned long count) noexcept { return span.first(count); }\n"
    };
    let (root, import) = pinned_span_fixture_with_dependencies(
        "returned-first",
        harness,
        &["sysroot/usr/include/c++/12/bits/ptr_traits.h"],
    );
    let mut source = format!(
        "{}{}",
        pinned_span_construction_contracts(&import),
        r#"struct span__int__value_unsigned_long_18446744073709551615 probe(const struct span__int__value_unsigned_long_18446744073709551615& span, uint64 count) {
 views span._M_ptr;
 views span._M_extent._M_extent_value;
 views span._M_ptr[0..(int32)span._M_extent._M_extent_value];
 requires count <= span._M_extent._M_extent_value;
 requires span._M_extent._M_extent_value <= 1073741823u64;
 ensures result._M_ptr == old(span._M_ptr);
 ensures result._M_extent._M_extent_value == count;
} by { execute(); simp(); }
"#
    );
    if empty {
        let start = source
            .find("struct span__int__value_unsigned_long_18446744073709551615 probe(")
            .unwrap();
        source.truncate(start);
        source.push_str(r#"struct span__int__value_unsigned_long_18446744073709551615 probe(const struct span__int__value_unsigned_long_18446744073709551615& span) {
 views span._M_ptr;
 views span._M_extent._M_extent_value;
 requires span._M_extent._M_extent_value <= 1073741823u64;
 ensures result._M_ptr == old(span._M_ptr);
 ensures result._M_extent._M_extent_value == 0u64;
} by { execute(); simp(); }
"#);
    }
    let path = root.join("span.click");
    fs::write(&path, &source).unwrap();
    let project = read_click_project(&path, &source).unwrap();
    verify_program_prepared_project(&project, &import).unwrap();
    if expand_and_retain {
        let expanded = expand_program_prepared_project_claim_source_by_label(
            &project,
            &import,
            "probe.contract",
        )
        .unwrap();
        verify_program_prepared_project(&project.with_entry_source(expanded), &import).unwrap();
        let (session, _) =
            C0VerificationSession::new_program_prepared_project(&project, &import).unwrap();
        let position = program_prepared_project_tactic_source_position(
            &project,
            &import,
            "probe.ensures_0",
            0,
        )
        .unwrap();
        session
            .verify_at_project(&source, position.line, position.column)
            .unwrap();
    }
    if expand_and_retain {
        let missing = source.replace(
            " views span._M_ptr[0..(int32)span._M_extent._M_extent_value];",
            "",
        );
        assert!(
            verify_program_prepared_project(&read_click_project(&path, &missing).unwrap(), &import)
                .is_err()
        );
    }
    if expand_and_retain {
        let beyond = source.replace(
            " requires count <= span._M_extent._M_extent_value;",
            " requires span._M_extent._M_extent_value < count;",
        );
        let error =
            verify_program_prepared_project(&read_click_project(&path, &beyond).unwrap(), &import)
                .unwrap_err();
        assert!(
            error.message().contains("probe.contract"),
            "{}",
            error.message()
        );
    }
    fs::remove_dir_all(root).unwrap();
}

fn pinned_span_last_index_contracts() -> &'static str {
    r#"theorem bounded_span_back_address(pointer: int32*, index: uint64) {
 requires index <= 1073741822u64;
 ensures pointer + (int32)index == pointer + index by { simp() using { index <= 1073741822u64; } }
}
theorem bounded_span_last_index(n: uint64) {
 requires 1u64 <= n;
 requires n <= 1073741823u64;
 ensures 1 <= (int32)n and (int32)n <= 1073741823 and 0 <= (int32)n - 1 and (int32)n - 1 < (int32)n and 0 <= (int32)(n - 1u64) and (int32)(n - 1u64) < (int32)n and n - 1u64 <= 1073741822u64 and (int32)(n - 1u64) == (int32)n - 1 by {
 apply(uint64_less_equal_to_integer(1u64, n));
 apply(uint64_less_equal_to_integer(n, 1073741823u64));
 apply(uint64_subtract_to_integer(n, 1u64));
 have 0 <= to_integer((n - 1u64)) by {
     arithmetic() using {
         1 <= to_integer(n);
         to_integer(n) <= 1073741823;
         to_integer((n - 1u64)) == to_integer(n) - 1;
     }
 }
 have to_integer((n - 1u64)) <= 1073741822 by {
     arithmetic() using {
         1 <= to_integer(n);
         to_integer(n) <= 1073741823;
         to_integer((n - 1u64)) == to_integer(n) - 1;
         0 <= to_integer((n - 1u64));
     }
 }
 have n - 1u64 <= 1073741822u64 by apply(uint64_less_equal_of_to_integer((n - 1u64), 1073741822u64));
 have to_integer((int32)n) == to_integer(n) by {
 arithmetic_certificate special {
 premise 0: 1 <= to_integer(n) => 1 <= to_integer(n);
 premise 1: to_integer(n) <= 1073741823 => to_integer(n) <= 1073741823;
 integer_cast_identity bounds [0, 1] => to_integer((int32)n) == to_integer(n); conclusion 0;
 }
 }
 have 1 <= to_integer((int32)n) by {
     arithmetic() using {
         1 <= to_integer(n);
         to_integer((int32)n) == to_integer(n);
     }
 }
 apply(int32_less_equal_of_to_integer(1, (int32)n));
 have to_integer((int32)n) <= 1073741823 by {
 arithmetic() using {
  to_integer((int32)n) == to_integer(n);
  to_integer(n) <= 1073741823;
 }
 }
 apply(int32_less_equal_of_to_integer((int32)n, 1073741823));
 have 0 <= (int32)n - 1 by {
     arithmetic() using {
         1 <= (int32)n;
         (int32)n <= 1073741823;
     }
 }
 have (int32)n - 1 < (int32)n by {
     arithmetic() using {
         1 <= (int32)n;
         (int32)n <= 1073741823;
     }
 }
 have to_integer((int32)(n - 1u64)) == to_integer(n - 1u64) by {
 arithmetic_certificate special {
 premise 0: 0 <= to_integer(n - 1u64) => 0 <= to_integer(n - 1u64);
 premise 1: to_integer(n - 1u64) <= 1073741822 => to_integer(n - 1u64) <= 1073741822;
 integer_cast_identity bounds [0, 1] => to_integer((int32)(n - 1u64)) == to_integer(n - 1u64); conclusion 0;
 }
 }
 have to_integer((int32)n) - to_integer(1) >= -2147483648 by {
 arithmetic() using { 1 <= to_integer((int32)n); }
 }
 have to_integer((int32)n) - to_integer(1) <= 2147483647 by {
 arithmetic() using { to_integer((int32)n) <= 1073741823; }
 }
 have to_integer(n) <= 2147483647 by { arithmetic() using { to_integer(n) <= 1073741823; } }
 have n <= 2147483647u64 by apply(uint64_less_equal_of_to_integer(n, 2147483647u64));
 have defined((int32)n - 1) by {
 apply(int32_subtract_defined_by_integer_bounds((int32)n, 1));
 simp();
 }
 apply(int32_subtract_to_integer((int32)n, 1)) using { defined((int32)n - 1); }
 have to_integer((int32)(n - 1u64)) == to_integer((int32)n - 1) by {
 arithmetic() using {
  to_integer((int32)(n - 1u64)) == to_integer(n - 1u64);
  to_integer(n - 1u64) == to_integer(n) - 1;
  to_integer((int32)n) == to_integer(n);
  to_integer((int32)n - 1) == to_integer((int32)n) - to_integer(1);
 }
 }
 apply(int32_equal_of_to_integer((int32)(n - 1u64), (int32)n - 1));
 have 0 <= (int32)(n - 1u64) by { rewrite((int32)(n - 1u64) == (int32)n - 1); assumption(); }
 have (int32)(n - 1u64) < (int32)n by { rewrite((int32)(n - 1u64) == (int32)n - 1); assumption(); }
 simp();
 }
}
theorem bounded_span_last_address(pointer: int32*, n: uint64) {
 requires 1u64 <= n;
 requires n <= 1073741823u64;
 requires n - 1u64 <= 1073741822u64;
 ensures pointer + ((int32)n - 1) == pointer + (n - 1u64) by {
  apply(bounded_span_last_index(n));
  have (int32)n - 1 == (int32)(n - 1u64) by { simp() using { (int32)(n - 1u64) == (int32)n - 1; } }
  rewrite((int32)n - 1 == (int32)(n - 1u64));
  simp() using { n - 1u64 <= 1073741822u64; }
 }
}
"#
}

fn pinned_span_back_signed_address_contracts() -> &'static str {
    r#"int32& span__int__value_unsigned_long_18446744073709551615_back(const struct span__int__value_unsigned_long_18446744073709551615* this) {
 views this->_M_ptr;
 views this->_M_extent._M_extent_value;
 views this->_M_ptr[0..((int32)this->_M_extent._M_extent_value)];
 requires 1u64 <= this->_M_extent._M_extent_value;
 requires this->_M_extent._M_extent_value <= 1073741823u64;
 ensures &result == this->_M_ptr + ((int32)this->_M_extent._M_extent_value - 1);
 ensures &result == this->_M_ptr + (this->_M_extent._M_extent_value - 1u64);
 ensures result == old(this->_M_ptr[this->_M_extent._M_extent_value - 1u64]);
} by {
 apply(uint64_less_equal_to_integer(1u64, this->_M_extent._M_extent_value));
 apply(uint64_less_equal_to_integer(this->_M_extent._M_extent_value, 1073741823u64));
 apply(uint64_subtract_to_integer(this->_M_extent._M_extent_value, 1u64));
 have 0 <= to_integer((this->_M_extent._M_extent_value - 1u64)) by {
     arithmetic() using {
         1 <= to_integer(this->_M_extent._M_extent_value);
         to_integer(this->_M_extent._M_extent_value) <= 1073741823;
         to_integer((this->_M_extent._M_extent_value - 1u64)) == to_integer(this->_M_extent._M_extent_value) - 1;
     }
 }
 have to_integer((this->_M_extent._M_extent_value - 1u64)) <= 1073741822 by {
     arithmetic() using {
         1 <= to_integer(this->_M_extent._M_extent_value);
         to_integer(this->_M_extent._M_extent_value) <= 1073741823;
         to_integer((this->_M_extent._M_extent_value - 1u64)) == to_integer(this->_M_extent._M_extent_value) - 1;
         0 <= to_integer((this->_M_extent._M_extent_value - 1u64));
     }
 }
 have this->_M_extent._M_extent_value - 1u64 <= 1073741822u64 by apply(uint64_less_equal_of_to_integer((this->_M_extent._M_extent_value - 1u64), 1073741822u64));
 have to_integer((int32)this->_M_extent._M_extent_value) == to_integer(this->_M_extent._M_extent_value) by {
 arithmetic_certificate special {
 premise 0: 1 <= to_integer(this->_M_extent._M_extent_value) => 1 <= to_integer(this->_M_extent._M_extent_value);
 premise 1: to_integer(this->_M_extent._M_extent_value) <= 1073741823 => to_integer(this->_M_extent._M_extent_value) <= 1073741823;
 integer_cast_identity bounds [0, 1] => to_integer((int32)this->_M_extent._M_extent_value) == to_integer(this->_M_extent._M_extent_value); conclusion 0;
 }
 }
 have 1 <= to_integer((int32)this->_M_extent._M_extent_value) by {
     arithmetic() using {
         1 <= to_integer(this->_M_extent._M_extent_value);
         to_integer((int32)this->_M_extent._M_extent_value) == to_integer(this->_M_extent._M_extent_value);
     }
 }
 apply(int32_less_equal_of_to_integer(1, (int32)this->_M_extent._M_extent_value));
 have 0 <= (int32)this->_M_extent._M_extent_value - 1 by {
     arithmetic() using {
         1 <= (int32)this->_M_extent._M_extent_value;
         (int32)this->_M_extent._M_extent_value <= 1073741823;
     }
 }
 have (int32)this->_M_extent._M_extent_value - 1 < (int32)this->_M_extent._M_extent_value by {
     arithmetic() using {
         1 <= (int32)this->_M_extent._M_extent_value;
         (int32)this->_M_extent._M_extent_value <= 1073741823;
     }
 }
 apply(bounded_span_last_index(this->_M_extent._M_extent_value));
 execute();
 apply(bounded_span_last_address(this->_M_ptr, this->_M_extent._M_extent_value));
 rewrite(this->_M_ptr + ((int32)this->_M_extent._M_extent_value - 1) == this->_M_ptr + (this->_M_extent._M_extent_value - 1u64));
 simp();
}
"#
}

// The original Bitcoin helper preserves a saved reference and the complete
// incoming backing frame while retiring only its constructed RHS descriptor.
#[test]
#[ignore = "nightly: 20s parallel pinned symbolic SpanPopBack and full backing frame"]
fn pinned_span_pop_back_constructs_shorter_descriptor_offline() {
    check_pinned_span_pop_back(SpanPopBackPhase::Reference);
}

#[test]
#[ignore = "nightly: 131s parallel pinned SpanPopBack expansion and retained verification"]
fn pinned_span_pop_back_expands_and_retains_offline() {
    check_pinned_span_pop_back(SpanPopBackPhase::ProofTools);
}

#[test]
#[ignore = "nightly: 22s parallel pinned SpanPopBack read caller"]
fn pinned_span_pop_back_read_caller_offline() {
    check_pinned_span_pop_back(SpanPopBackPhase::Read);
}

#[test]
#[ignore = "nightly: 53s parallel pinned SpanPopBack owned write caller"]
fn pinned_span_pop_back_write_caller_offline() {
    check_pinned_span_pop_back(SpanPopBackPhase::Write);
}

#[test]
#[ignore = "nightly: 55s parallel pinned singleton SpanPopBack after empty RHS descriptor retirement"]
fn pinned_span_pop_back_singleton_read_offline() {
    check_pinned_span_pop_back(SpanPopBackPhase::SingletonRead);
}

#[test]
#[ignore = "nightly: 53s parallel pinned singleton SpanPopBack write after empty RHS descriptor retirement"]
fn pinned_span_pop_back_singleton_write_offline() {
    check_pinned_span_pop_back(SpanPopBackPhase::SingletonWrite);
}

#[test]
#[ignore = "nightly: 41s parallel pinned three-element SpanPopBack"]
fn pinned_span_pop_back_several_elements_offline() {
    check_pinned_span_pop_back(SpanPopBackPhase::Several);
}

#[test]
#[ignore = "nightly: 154s parallel pinned SpanPopBack read expansion and retained verification"]
fn pinned_span_pop_back_read_expands_and_retains_offline() {
    check_pinned_span_pop_back(SpanPopBackPhase::ReadTools);
}

#[test]
#[ignore = "nightly: 254s parallel pinned SpanPopBack write expansion and retained verification"]
fn pinned_span_pop_back_write_expands_and_retains_offline() {
    check_pinned_span_pop_back(SpanPopBackPhase::WriteTools);
}

#[test]
#[ignore = "nightly: 186s parallel pinned SpanPopBack authority and bounds refusals"]
fn pinned_span_pop_back_requires_authority_bounds_and_separation_offline() {
    check_pinned_span_pop_back(SpanPopBackPhase::Refusals);
}

#[derive(Clone, Copy)]
enum SpanPopBackPhase {
    Reference,
    ProofTools,
    Read,
    Write,
    SingletonRead,
    SingletonWrite,
    Several,
    ReadTools,
    WriteTools,
    Refusals,
}

fn check_pinned_span_pop_back(phase: SpanPopBackPhase) {
    let harness = match phase {
        SpanPopBackPhase::SingletonRead | SpanPopBackPhase::Read | SpanPopBackPhase::ReadTools => {
            "#include <span.h>\nint probe(std::span<int>& span) { int& back = SpanPopBack(span); return back; }\n"
        }
        SpanPopBackPhase::SingletonWrite
        | SpanPopBackPhase::Write
        | SpanPopBackPhase::WriteTools => {
            "#include <span.h>\nint probe(std::span<int>& span, int input) { int& back = SpanPopBack(span); back = input; return back; }\n"
        }
        _ => "#include <span.h>\nint& probe(std::span<int>& span) { return SpanPopBack(span); }\n",
    };
    let (root, import) = pinned_span_fixture_with_dependencies(
        "pop-back",
        harness,
        &[
            "sysroot/usr/include/c++/12/bits/ptr_traits.h",
            "bitcoin-src/src/span.h",
        ],
    );
    let pop_back = import
        .export()
        .reachable_functions
        .iter()
        .find(|function| function.name.starts_with("SpanPopBack"))
        .unwrap()
        .name
        .clone();
    let mut source = format!(
        "{}{}{}{}",
        pinned_span_construction_contracts(&import),
        pinned_span_last_index_contracts(),
        pinned_span_back_signed_address_contracts(),
        r#"
bool span__int__value_unsigned_long_18446744073709551615_empty(const struct span__int__value_unsigned_long_18446744073709551615* this) {
 views this->_M_extent._M_extent_value;
 ensures this->_M_extent._M_extent_value == 0u64 implies result == 1;
 ensures this->_M_extent._M_extent_value != 0u64 implies result == 0;
} by { execute(); simp(); }
theorem last_span_cells_separate(span: struct span__int__value_unsigned_long_18446744073709551615*, n: uint64) {
 requires 1u64 <= n;
 requires n <= 1073741823u64;
 requires separate(memory(span->_M_ptr), memory(span->_M_ptr[0..(int32)n]));
 requires separate(memory(span->_M_extent._M_extent_value), memory(span->_M_ptr[0..(int32)n]));
 ensures separate(memory(span->_M_ptr), memory(span->_M_ptr[n - 1u64])) and separate(memory(span->_M_extent._M_extent_value), memory(span->_M_ptr[n - 1u64])) by {
  apply(bounded_span_last_index(n));
  apply(bounded_span_last_address(span->_M_ptr, n));
  have separate(memory(span->_M_ptr), memory(span->_M_ptr[(int32)n - 1])) by { assumption(); }
  have separate(memory(span->_M_extent._M_extent_value), memory(span->_M_ptr[(int32)n - 1])) by { assumption(); }
  have span->_M_ptr + (n - 1u64) == span->_M_ptr + ((int32)n - 1) by { simp() using { span->_M_ptr + ((int32)n - 1) == span->_M_ptr + (n - 1u64); } }
  rewrite(span->_M_ptr + (n - 1u64) == span->_M_ptr + ((int32)n - 1));
  assumption();
 }
}
theorem bounded_span_prefix(n: uint64) {
 requires 1u64 <= n;
 requires n <= 1073741823u64;
 ensures n - 1u64 <= n and n - 1u64 <= 1073741822u64 and 0 <= (int32)(n - 1u64) and (int32)(n - 1u64) <= (int32)n by {
  apply(uint64_less_equal_to_integer(1u64, n));
  apply(uint64_less_equal_to_integer(n, 1073741823u64));
  apply(uint64_subtract_to_integer(n, 1u64));
  have 0 <= to_integer(n - 1u64) by {
   arithmetic() using { 1 <= to_integer(n); to_integer(n - 1u64) == to_integer(n) - 1; }
  }
  have to_integer(n - 1u64) <= to_integer(n) by {
   arithmetic() using { to_integer(n - 1u64) == to_integer(n) - 1; }
  }
  have to_integer(n - 1u64) <= 1073741822 by {
   arithmetic() using { to_integer(n) <= 1073741823; to_integer(n - 1u64) == to_integer(n) - 1; }
  }
  apply(uint64_less_equal_of_to_integer(n - 1u64, 1073741822u64));
  have to_integer((int32)n) == to_integer(n) by {
   arithmetic_certificate special {
    premise 0: 1 <= to_integer(n) => 1 <= to_integer(n);
    premise 1: to_integer(n) <= 1073741823 => to_integer(n) <= 1073741823;
    integer_cast_identity bounds [0, 1] => to_integer((int32)n) == to_integer(n); conclusion 0;
   }
  }
  have to_integer((int32)(n - 1u64)) == to_integer(n - 1u64) by {
   arithmetic_certificate special {
    premise 0: 0 <= to_integer(n - 1u64) => 0 <= to_integer(n - 1u64);
    premise 1: to_integer(n - 1u64) <= 1073741822 => to_integer(n - 1u64) <= 1073741822;
    integer_cast_identity bounds [0, 1] => to_integer((int32)(n - 1u64)) == to_integer(n - 1u64); conclusion 0;
   }
  }
  have 0 <= to_integer((int32)(n - 1u64)) by {
   arithmetic() using { 0 <= to_integer(n - 1u64); to_integer((int32)(n - 1u64)) == to_integer(n - 1u64); }
  }
  have to_integer((int32)(n - 1u64)) <= to_integer((int32)n) by {
   arithmetic() using { to_integer(n - 1u64) <= to_integer(n); to_integer((int32)(n - 1u64)) == to_integer(n - 1u64); to_integer((int32)n) == to_integer(n); }
  }
  apply(int32_less_equal_of_to_integer(0, (int32)(n - 1u64)));
  apply(int32_less_equal_of_to_integer((int32)(n - 1u64), (int32)n));
  apply(uint64_less_equal_of_to_integer(n - 1u64, n));
  simp();
 }
}
int32& POP_BACK(struct span__int__value_unsigned_long_18446744073709551615& span) {
 owns span._M_ptr;
 owns span._M_extent._M_extent_value;
 views span._M_ptr[0..(int32)span._M_extent._M_extent_value];
 requires separate(memory(span._M_ptr), memory(span._M_ptr[0..(int32)span._M_extent._M_extent_value]));
 requires separate(memory(span._M_extent._M_extent_value), memory(span._M_ptr[0..(int32)span._M_extent._M_extent_value]));

 requires separate(memory(span._M_extent._M_extent_value), memory(span._M_ptr[span._M_extent._M_extent_value - 1u64]));
 requires separate(memory(span._M_ptr), memory(span._M_ptr[span._M_extent._M_extent_value - 1u64]));
 requires 1u64 <= span._M_extent._M_extent_value;
 requires span._M_extent._M_extent_value <= 1073741823u64;
 ensures span._M_ptr == old(span._M_ptr);
 ensures span._M_extent._M_extent_value == old(span._M_extent._M_extent_value) - 1u64;
 ensures &result == old(span._M_ptr) + (old(span._M_extent._M_extent_value) - 1u64);
 ensures result == old(span._M_ptr[span._M_extent._M_extent_value - 1u64]);
 ensures forall (k: int32) { 0 <= k and k < old((int32)span._M_extent._M_extent_value) implies span._M_ptr[k] == old(span._M_ptr[k]) };
} by {
 apply(bounded_span_last_index(span._M_extent._M_extent_value));
 apply(bounded_span_prefix(span._M_extent._M_extent_value));
 apply(bounded_span_last_address(span._M_ptr, span._M_extent._M_extent_value));
 have span._M_ptr + (span._M_extent._M_extent_value - 1u64) == span._M_ptr + ((int32)span._M_extent._M_extent_value - 1) by { simp() using { span._M_ptr + ((int32)span._M_extent._M_extent_value - 1) == span._M_ptr + (span._M_extent._M_extent_value - 1u64); } }
 step(); step(); step(); step();
 have back == old(span._M_ptr[span._M_extent._M_extent_value - 1u64]) by simp;
 have &back == old(span._M_ptr) + (old(span._M_extent._M_extent_value) - 1u64) by simp;
 have size == span._M_extent._M_extent_value by simp;
 have 1u64 <= size by simp;
 have size <= 1073741823u64 by simp;
 apply(bounded_span_last_index(size));
 apply(bounded_span_prefix(size));
 have (int32)size == (int32)span._M_extent._M_extent_value by simp;

 have 0 <= (int32)(size - 1u64) by simp;
 have (int32)(size - 1u64) <= (int32)span._M_extent._M_extent_value by simp;
 have size - 1u64 <= span._M_extent._M_extent_value by { simp() using { size == span._M_extent._M_extent_value; size - 1u64 <= size; } }
 step(); step(); step();
 have back == old(span._M_ptr[span._M_extent._M_extent_value - 1u64]) by simp;
 step();
 have back == old(span._M_ptr[span._M_extent._M_extent_value - 1u64]) by simp;
 execute();
 have span._M_ptr == old(span._M_ptr) by simp;
 have forall (k: int32) { 0 <= k and k < old((int32)span._M_extent._M_extent_value) implies span._M_ptr[k] == old(span._M_ptr[k]) } by {
  intro() as k; intro();
  simp();
 }
 have span._M_ptr == old(span._M_ptr) by simp;
 have &result == old(span._M_ptr) + (old(span._M_extent._M_extent_value) - 1u64) by simp;
 rewrite(&result == old(span._M_ptr) + (old(span._M_extent._M_extent_value) - 1u64));
 simp(); }
int32& probe(struct span__int__value_unsigned_long_18446744073709551615& span) {
 owns span._M_ptr;
 owns span._M_extent._M_extent_value;
 views span._M_ptr[0..(int32)span._M_extent._M_extent_value];
 requires separate(memory(span._M_ptr), memory(span._M_ptr[0..(int32)span._M_extent._M_extent_value]));
 requires separate(memory(span._M_extent._M_extent_value), memory(span._M_ptr[0..(int32)span._M_extent._M_extent_value]));

 requires 1u64 <= span._M_extent._M_extent_value;
 requires span._M_extent._M_extent_value <= 1073741823u64;
 ensures span._M_ptr == old(span._M_ptr);
 ensures span._M_extent._M_extent_value == old(span._M_extent._M_extent_value) - 1u64;
 ensures &result == old(span._M_ptr) + (old(span._M_extent._M_extent_value) - 1u64);
 ensures result == old(span._M_ptr[span._M_extent._M_extent_value - 1u64]);
 ensures forall (k: int32) { 0 <= k and k < old((int32)span._M_extent._M_extent_value) implies span._M_ptr[k] == old(span._M_ptr[k]) };
} by { apply(last_span_cells_separate(&span, span._M_extent._M_extent_value)); execute(); simp(); }
"#
    )
    .replace("POP_BACK", &pop_back);
    if matches!(
        phase,
        SpanPopBackPhase::Read
            | SpanPopBackPhase::Write
            | SpanPopBackPhase::SingletonRead
            | SpanPopBackPhase::SingletonWrite
            | SpanPopBackPhase::ReadTools
            | SpanPopBackPhase::WriteTools
    ) {
        let start = source.rfind("int32& probe(").unwrap();
        let mut caller = source[start..].replace("int32& probe(", "int32 probe(");
        if matches!(
            phase,
            SpanPopBackPhase::Write
                | SpanPopBackPhase::SingletonWrite
                | SpanPopBackPhase::WriteTools
        ) {
            caller = caller.replace("& span) {", "& span, int32 input) {");
            caller = caller.replace(" views span._M_ptr[", " owns span._M_ptr[");
            caller = caller.replace(" ensures &result == old(span._M_ptr) + (old(span._M_extent._M_extent_value) - 1u64);", "");
            caller = caller.replace(" ensures result == old(span._M_ptr[span._M_extent._M_extent_value - 1u64]);", " ensures result == input;\n ensures span._M_ptr[old(span._M_extent._M_extent_value) - 1u64] == input;");
            caller = caller.replace(
                "implies span._M_ptr[k]",
                "and k != old((int32)span._M_extent._M_extent_value) - 1 implies span._M_ptr[k]",
            );
            caller = caller.replace(" execute(); simp();", r#"
 apply(bounded_span_last_index(span._M_extent._M_extent_value));
 apply(bounded_span_last_address(span._M_ptr, span._M_extent._M_extent_value));
 step(); step();
 have &back == old(span._M_ptr) + (old(span._M_extent._M_extent_value) - 1u64) by simp;
 apply(bounded_span_last_index(old(span._M_extent._M_extent_value)));
 apply(bounded_span_last_address(old(span._M_ptr), old(span._M_extent._M_extent_value)));
 have &back == old(span._M_ptr) + (old((int32)span._M_extent._M_extent_value) - 1) by { simp() using { &back == old(span._M_ptr) + (old(span._M_extent._M_extent_value) - 1u64); old(span._M_ptr) + (old((int32)span._M_extent._M_extent_value) - 1) == old(span._M_ptr) + (old(span._M_extent._M_extent_value) - 1u64); } }
 execute();
 have span._M_ptr == old(span._M_ptr) by simp;
 have forall (k: int32) { 0 <= k and k < old((int32)span._M_extent._M_extent_value) and k != old((int32)span._M_extent._M_extent_value) - 1 implies span._M_ptr[k] == old(span._M_ptr[k]) } by {
  intro() as k; intro(); simp();
 }
 have old(span._M_ptr) + (old(span._M_extent._M_extent_value) - 1u64) == old(span._M_ptr) + (old((int32)span._M_extent._M_extent_value) - 1) by { simp() using { old(span._M_ptr) + (old((int32)span._M_extent._M_extent_value) - 1) == old(span._M_ptr) + (old(span._M_extent._M_extent_value) - 1u64); } }
 have result == input by simp;
 have span._M_ptr[old(span._M_extent._M_extent_value) - 1u64] == input by {
  simp() using { span._M_ptr == old(span._M_ptr); old(span._M_ptr) + (old(span._M_extent._M_extent_value) - 1u64) == old(span._M_ptr) + (old((int32)span._M_extent._M_extent_value) - 1); result == input; }
 }
 simp();"#);
        } else {
            caller = caller.replace(" ensures &result == old(span._M_ptr) + (old(span._M_extent._M_extent_value) - 1u64);", "");
            caller = caller.replace(" execute(); simp();", r#"
 step(); step();
 apply(bounded_span_last_index(old(span._M_extent._M_extent_value)));
 apply(bounded_span_last_address(old(span._M_ptr), old(span._M_extent._M_extent_value)));
 have &back == old(span._M_ptr) + (old((int32)span._M_extent._M_extent_value) - 1) by { simp() using { &back == old(span._M_ptr) + (old(span._M_extent._M_extent_value) - 1u64); old(span._M_ptr) + (old((int32)span._M_extent._M_extent_value) - 1) == old(span._M_ptr) + (old(span._M_extent._M_extent_value) - 1u64); } }
 execute(); simp();"#);
        }
        source.truncate(start);
        source.push_str(&caller);
    }
    if matches!(
        phase,
        SpanPopBackPhase::SingletonRead | SpanPopBackPhase::SingletonWrite
    ) {
        let start = source.rfind("int32 probe(").unwrap();
        let caller = source[start..].replace(" requires 1u64 <= span._M_extent._M_extent_value;", " requires span._M_extent._M_extent_value == 1u64;\n requires 1u64 <= span._M_extent._M_extent_value;")
            .replace(" ensures span._M_ptr == old(span._M_ptr);", " ensures span._M_extent._M_extent_value == 0u64;\n ensures span._M_ptr == old(span._M_ptr);");
        let mut caller = caller;
        let finish = caller.rfind("simp();").unwrap();
        caller.insert_str(finish, r#"
 have old(span._M_extent._M_extent_value) == 1u64 by { assumption(); }
 have span._M_extent._M_extent_value == old(span._M_extent._M_extent_value) - 1u64 by simp;
 have span._M_extent._M_extent_value == 0u64 by { simp() using { old(span._M_extent._M_extent_value) == 1u64; span._M_extent._M_extent_value == old(span._M_extent._M_extent_value) - 1u64; } }
"#);
        source.truncate(start);
        source.push_str(&caller);
    }
    if matches!(phase, SpanPopBackPhase::Several) {
        let start = source.rfind("int32& probe(").unwrap();
        let caller = source[start..].replace(" requires 1u64 <= span._M_extent._M_extent_value;", " requires span._M_extent._M_extent_value == 3u64;\n requires 1u64 <= span._M_extent._M_extent_value;");
        source.truncate(start);
        source.push_str(&caller);
    }
    let path = root.join("span.click");
    fs::write(&path, &source).unwrap();
    let project = read_click_project(&path, &source).unwrap();
    verify_program_prepared_project(&project, &import).unwrap();
    if matches!(phase, SpanPopBackPhase::Refusals) {
        let start = source.rfind("int32& probe(").unwrap();
        let prefix = &source[..start];
        let caller = &source[start..];
        for (name, original, replacement) in [
            (
                "descriptor authority",
                " owns span._M_ptr;",
                " views span._M_ptr;",
            ),
            (
                "backing authority",
                " views span._M_ptr[0..(int32)span._M_extent._M_extent_value];",
                "",
            ),
            (
                "nonempty input",
                " requires 1u64 <= span._M_extent._M_extent_value;",
                " requires span._M_extent._M_extent_value == 0u64;",
            ),
            (
                "extent bound",
                " requires span._M_extent._M_extent_value <= 1073741823u64;",
                "",
            ),
            (
                "descriptor/backing separation",
                " requires separate(memory(span._M_ptr), memory(span._M_ptr[0..(int32)span._M_extent._M_extent_value]));",
                "",
            ),
        ] {
            assert!(
                caller.contains(original),
                "missing refusal mutation: {name}"
            );
            let missing = format!("{prefix}{}", caller.replace(original, replacement));
            let error = verify_program_prepared_project(
                &read_click_project(&path, &missing).unwrap(),
                &import,
            )
            .unwrap_err();
            assert!(
                error.message().contains("probe.contract"),
                "{name}: {}",
                error.message()
            );
        }
    }
    if matches!(phase, SpanPopBackPhase::WriteTools) {
        let start = source.rfind("int32 probe(").unwrap();
        let missing = format!(
            "{}{}",
            &source[..start],
            source[start..].replace(" owns span._M_ptr[", " views span._M_ptr[")
        );
        let error =
            verify_program_prepared_project(&read_click_project(&path, &missing).unwrap(), &import)
                .unwrap_err();
        assert!(
            error.message().contains("probe.contract"),
            "{}",
            error.message()
        );
    }
    if matches!(
        phase,
        SpanPopBackPhase::ProofTools | SpanPopBackPhase::ReadTools | SpanPopBackPhase::WriteTools
    ) {
        for claim in [format!("{pop_back}.contract"), "probe.contract".to_owned()] {
            let expanded =
                expand_program_prepared_project_claim_source_by_label(&project, &import, &claim)
                    .unwrap();
            let rewritten = project.with_entry_source(expanded.clone());
            verify_program_prepared_project(&rewritten, &import).unwrap();
            let (session, _) =
                C0VerificationSession::new_program_prepared_project(&project, &import).unwrap();
            let position =
                program_prepared_project_tactic_source_position(&rewritten, &import, &claim, 0)
                    .unwrap();
            session
                .verify_at_project(&expanded, position.line, position.column)
                .unwrap();
        }
    }
    fs::remove_dir_all(root).unwrap();
}

// The unchanged runtime suffix operation constructs into the caller's result
// destination, preserving the receiver and all of its backing view.
#[test]
#[ignore = "nightly: 3.7s parallel pinned runtime last returns bounded suffix"]
fn pinned_std_span_last_returns_bounded_suffix_offline() {
    check_pinned_std_span_last("symbolic");
}

#[test]
#[ignore = "nightly: 6.5s parallel pinned runtime last empty suffix"]
fn pinned_std_span_last_empty_suffix_offline() {
    check_pinned_std_span_last("empty");
}
#[test]
#[ignore = "nightly: 6.1s parallel pinned runtime last full suffix"]
fn pinned_std_span_last_full_suffix_offline() {
    check_pinned_std_span_last("full");
}
#[test]
#[ignore = "nightly: 4.3s parallel pinned runtime last empty input"]
fn pinned_std_span_last_empty_input_offline() {
    check_pinned_std_span_last("empty-input");
}
#[test]
#[ignore = "nightly: 8.8s parallel pinned runtime last method expands"]
fn pinned_std_span_last_method_expands_offline() {
    check_pinned_std_span_last("expand-method");
}
#[test]
#[ignore = "nightly: 10.8s parallel pinned runtime last caller expands"]
fn pinned_std_span_last_caller_expands_offline() {
    check_pinned_std_span_last("expand-caller");
}
#[test]
#[ignore = "nightly: 8.8s parallel pinned runtime last retains"]
fn pinned_std_span_last_retains_offline() {
    check_pinned_std_span_last("retain");
}
#[test]
#[ignore = "nightly: 5.7s parallel pinned runtime last refuses missing views"]
fn pinned_std_span_last_refuses_missing_views_offline() {
    check_pinned_std_span_last("refuse-views");
}
#[test]
#[ignore = "nightly: 7.3s parallel pinned runtime last refuses missing bounds"]
fn pinned_std_span_last_refuses_missing_bounds_offline() {
    check_pinned_std_span_last("refuse-bounds");
}
#[test]
#[ignore = "nightly: 7.8s parallel pinned runtime last refuses false results"]
fn pinned_std_span_last_refuses_false_results_offline() {
    check_pinned_std_span_last("refuse-results");
}

fn check_pinned_std_span_last(case: &str) {
    let harness = "#include <span.h>\nstd::span<int> probe(const std::span<int>& span, unsigned long count) noexcept { return span.last(count); }\n";
    let (root, import) = pinned_span_fixture_with_dependencies(
        &format!("returned-last-{case}"),
        harness,
        &["sysroot/usr/include/c++/12/bits/ptr_traits.h"],
    );
    let common = pinned_span_construction_contracts(&import);
    let start = common.find("struct span__int__value_unsigned_long_18446744073709551615 span__int__value_unsigned_long_18446744073709551615_first(").unwrap();
    let common = common[..start].replace("(int32)__count", "__count");
    let source = format!(
        "{}{}",
        common,
        r#"struct span__int__value_unsigned_long_18446744073709551615 span__int__value_unsigned_long_18446744073709551615_last(const struct span__int__value_unsigned_long_18446744073709551615* this, uint64 __count) {
 views this->_M_ptr;
 views this->_M_extent._M_extent_value;
 views this->_M_ptr[0..this->_M_extent._M_extent_value];
 requires __count <= this->_M_extent._M_extent_value;
 requires this->_M_extent._M_extent_value <= 1073741823u64;
 ensures result._M_ptr == old(this->_M_ptr) + (old(this->_M_extent._M_extent_value) - __count);
 ensures result._M_extent._M_extent_value == __count;
 ensures this->_M_ptr == old(this->_M_ptr);
 ensures this->_M_extent._M_extent_value == old(this->_M_extent._M_extent_value);
} by { execute(); simp(); }
struct span__int__value_unsigned_long_18446744073709551615 probe(const struct span__int__value_unsigned_long_18446744073709551615& span, uint64 count) {
 views span._M_ptr;
 views span._M_extent._M_extent_value;
 views span._M_ptr[0..span._M_extent._M_extent_value];
 requires count <= span._M_extent._M_extent_value;
 requires span._M_extent._M_extent_value <= 1073741823u64;
 ensures result._M_ptr == old(span._M_ptr) + (old(span._M_extent._M_extent_value) - count);
 ensures result._M_extent._M_extent_value == count;
 ensures span._M_ptr == old(span._M_ptr);
 ensures span._M_extent._M_extent_value == old(span._M_extent._M_extent_value);
 ensures forall (index: uint64) { index < old(span._M_extent._M_extent_value) implies span._M_ptr[index] == old(span._M_ptr[index]) };
} by { execute(); simp(); }
"#
    );
    let source = match case {
        "empty" => source.replace(
            " requires count <= span._M_extent._M_extent_value;",
            " requires count == 0u64;",
        ),
        "full" => source.replace(
            " requires count <= span._M_extent._M_extent_value;",
            " requires count == span._M_extent._M_extent_value;",
        ),
        "empty-input" => source.replace(
            " requires count <= span._M_extent._M_extent_value;",
            " requires count == 0u64; requires span._M_extent._M_extent_value == 0u64;",
        ),
        _ => source,
    };
    let path = root.join("span.click");
    fs::write(&path, &source).unwrap();
    let project = read_click_project(&path, &source).unwrap();
    verify_program_prepared_project(&project, &import).unwrap();
    if case.starts_with("expand-") {
        let label = if case == "expand-method" {
            "span__int__value_unsigned_long_18446744073709551615_last.contract"
        } else {
            "probe.contract"
        };
        let expanded =
            expand_program_prepared_project_claim_source_by_label(&project, &import, label)
                .unwrap();
        verify_program_prepared_project(&project.with_entry_source(expanded), &import).unwrap();
    }
    if case == "retain" {
        let (session, _) =
            C0VerificationSession::new_program_prepared_project(&project, &import).unwrap();
        let position = program_prepared_project_tactic_source_position(
            &project,
            &import,
            "probe.ensures_0",
            0,
        )
        .unwrap();
        session
            .verify_at_project(&source, position.line, position.column)
            .unwrap();
    }
    if case.starts_with("refuse-") {
        let hostile_sources = [
            source.replace(" views span._M_ptr[0..span._M_extent._M_extent_value];", ""),
            source.replace(" requires count <= span._M_extent._M_extent_value;", ""),
            source.replace(" requires span._M_extent._M_extent_value <= 1073741823u64;", ""),
            source.replace(" ensures result._M_extent._M_extent_value == count;", " ensures result._M_extent._M_extent_value != count;"),
            source.replace(" ensures result._M_ptr == old(span._M_ptr) + (old(span._M_extent._M_extent_value) - count);", " ensures result._M_ptr == old(span._M_ptr) + (old(span._M_extent._M_extent_value) - count + 1u64);"),
        ];
        let cases = match case {
            "refuse-views" => 0..1,
            "refuse-bounds" => 1..3,
            _ => 3..5,
        };
        for hostile in &hostile_sources[cases] {
            let error = verify_program_prepared_project(
                &read_click_project(&path, hostile).unwrap(),
                &import,
            )
            .unwrap_err();
            assert!(error.message().contains("probe"), "{}", error.message());
        }
    }
    fs::remove_dir_all(root).unwrap();
}

#[test]
#[ignore = "nightly: 3.5s pinned runtime subspan base proof; tools/refusals add rechecks"]
fn pinned_std_span_subspan_bounded_window_offline() {
    check_pinned_std_span_subspan("finite");
}

#[test]
#[ignore = "nightly: 3.5s pinned runtime subspan base proof; tools/refusals add rechecks"]
fn pinned_std_span_subspan_empty_window_offline() {
    check_pinned_std_span_subspan("empty");
}

#[test]
#[ignore = "nightly: 3.5s pinned runtime subspan base proof; tools/refusals add rechecks"]
fn pinned_std_span_subspan_empty_at_end_offline() {
    check_pinned_std_span_subspan("end");
}

#[test]
#[ignore = "nightly: 3.5s pinned runtime subspan base proof; tools/refusals add rechecks"]
fn pinned_std_span_subspan_full_window_offline() {
    check_pinned_std_span_subspan("full");
}

#[test]
#[ignore = "nightly: 3.5s pinned runtime subspan base proof; tools/refusals add rechecks"]
fn pinned_std_span_subspan_empty_input_offline() {
    check_pinned_std_span_subspan("empty-input");
}

#[test]
#[ignore = "nightly: 3.5s pinned runtime subspan base proof; tools/refusals add rechecks"]
fn pinned_std_span_subspan_method_expands_offline() {
    check_pinned_std_span_subspan("expand-method");
}

#[test]
#[ignore = "nightly: 3.5s pinned runtime subspan base proof; tools/refusals add rechecks"]
fn pinned_std_span_subspan_caller_expands_offline() {
    check_pinned_std_span_subspan("expand-caller");
}

#[test]
#[ignore = "nightly: 3.5s pinned runtime subspan base proof; tools/refusals add rechecks"]
fn pinned_std_span_subspan_retains_offline() {
    check_pinned_std_span_subspan("retain");
}

#[test]
#[ignore = "nightly: 3.5s pinned runtime subspan base proof; tools/refusals add rechecks"]
fn pinned_std_span_subspan_refuses_missing_views_offline() {
    check_pinned_std_span_subspan("refuse-views");
}

#[test]
#[ignore = "nightly: 3.5s pinned runtime subspan base proof; tools/refusals add rechecks"]
fn pinned_std_span_subspan_refuses_missing_bounds_offline() {
    check_pinned_std_span_subspan("refuse-bounds");
}

#[test]
#[ignore = "nightly: 3.5s pinned runtime subspan base proof; tools/refusals add rechecks"]
fn pinned_std_span_subspan_refuses_false_results_offline() {
    check_pinned_std_span_subspan("refuse-results");
}

#[test]
#[ignore = "nightly: 3.5s pinned runtime subspan base proof; tools/refusals add rechecks"]
fn pinned_std_span_subspan_explicit_dynamic_extent_offline() {
    check_pinned_std_span_subspan("sentinel");
}

// The original runtime subspan branch and returned constructor must verify
// without replacing the header with a specialized finite-count implementation.
fn check_pinned_std_span_subspan(case: &str) {
    let harness = "#include <span.h>\nstd::span<int> probe(const std::span<int>& span, unsigned long offset, unsigned long count) noexcept { return span.subspan(offset, count); }\n";
    let (root, import) = pinned_span_fixture_with_dependencies(
        &format!("returned-subspan-{case}"),
        harness,
        &["sysroot/usr/include/c++/12/bits/ptr_traits.h"],
    );
    let common = pinned_span_construction_contracts(&import);
    let start = common.find("struct span__int__value_unsigned_long_18446744073709551615 span__int__value_unsigned_long_18446744073709551615_first(").unwrap();
    let common = common[..start].replace("(int32)__count", "__count");
    let source = format!(
        "{}{}",
        common,
        r#"
theorem bounded_subspan_count(n: uint64, offset: uint64, count: uint64) {
 requires offset <= n;
 requires count <= n - offset;
 requires n <= 1073741823u64;
 ensures count <= 1073741823u64 and count != 18446744073709551615u64 by {
  apply(uint64_less_equal_to_integer(offset, n));
  apply(uint64_subtract_to_integer(n, offset));
  apply(uint64_less_equal_to_integer(count, n - offset));
  apply(uint64_less_equal_to_integer(n, 1073741823u64));
  apply(uint64_to_integer_bounds(offset));
  have to_integer(n - offset) <= to_integer(n) by { arithmetic() using { to_integer(n - offset) == to_integer(n) - to_integer(offset); 0 <= to_integer(offset); } }
  have to_integer(count) <= to_integer(n) by { arithmetic() using { to_integer(count) <= to_integer(n - offset); to_integer(n - offset) <= to_integer(n); } }
  have to_integer(count) <= 1073741823 by { arithmetic() using { to_integer(count) <= to_integer(n); to_integer(n) <= 1073741823; } }
  have count <= 1073741823u64 by apply(uint64_less_equal_of_to_integer(count, 1073741823u64));
  have to_integer(count) < 18446744073709551615 by { arithmetic() using { to_integer(count) <= 1073741823; } }
  have count < 18446744073709551615u64 by apply(uint64_less_than_of_to_integer(count, 18446744073709551615u64));
  if count == 18446744073709551615u64 {
   have not (count < 18446744073709551615u64) by { rewrite(count == 18446744073709551615u64); normalize(); }
   contradiction(count < 18446744073709551615u64);
  } else { both { assumption(); } and { assumption(); } }
 }
}
struct span__int__value_unsigned_long_18446744073709551615 span__int__value_unsigned_long_18446744073709551615_subspan(const struct span__int__value_unsigned_long_18446744073709551615* this, uint64 __offset, uint64 __count) {
 views this->_M_ptr;
 views this->_M_extent._M_extent_value;
 views this->_M_ptr[0..this->_M_extent._M_extent_value];
 requires __offset <= this->_M_extent._M_extent_value;
 requires __count <= this->_M_extent._M_extent_value - __offset;
 requires this->_M_extent._M_extent_value <= 1073741823u64;
 ensures result._M_ptr == old(this->_M_ptr) + __offset;
 ensures result._M_extent._M_extent_value == old(__count);
 ensures this->_M_ptr == old(this->_M_ptr);
 ensures this->_M_extent._M_extent_value == old(this->_M_extent._M_extent_value);
} by { apply(bounded_subspan_count(this->_M_extent._M_extent_value, __offset, __count)); execute(); simp(); }
struct span__int__value_unsigned_long_18446744073709551615 probe(const struct span__int__value_unsigned_long_18446744073709551615& span, uint64 offset, uint64 count) {
 views span._M_ptr;
 views span._M_extent._M_extent_value;
 views span._M_ptr[0..span._M_extent._M_extent_value];
 requires offset <= span._M_extent._M_extent_value;
 requires count <= span._M_extent._M_extent_value - offset;
 requires span._M_extent._M_extent_value <= 1073741823u64;
 ensures result._M_ptr == old(span._M_ptr) + offset;
 ensures result._M_extent._M_extent_value == count;
 ensures span._M_ptr == old(span._M_ptr);
 ensures span._M_extent._M_extent_value == old(span._M_extent._M_extent_value);
 ensures forall (index: uint64) { index < old(span._M_extent._M_extent_value) implies span._M_ptr[index] == old(span._M_ptr[index]) };
} by { apply(bounded_subspan_count(span._M_extent._M_extent_value, offset, count)); execute(); simp(); }
"#
    );
    let source = match case {
        "empty" => source.replace(" requires count <= span._M_extent._M_extent_value - offset;", " requires count <= span._M_extent._M_extent_value - offset;\n requires count == 0u64;"),
        "end" => source.replace(" requires count <= span._M_extent._M_extent_value - offset;", " requires count <= span._M_extent._M_extent_value - offset;\n requires count == 0u64; requires offset == span._M_extent._M_extent_value;"),
        "full" => source.replace(" requires count <= span._M_extent._M_extent_value - offset;", " requires count <= span._M_extent._M_extent_value - offset;\n requires offset == 0u64; requires count == span._M_extent._M_extent_value;"),
        "empty-input" => source.replace(" requires count <= span._M_extent._M_extent_value - offset;", " requires count <= span._M_extent._M_extent_value - offset;\n requires count == 0u64; requires offset == 0u64; requires span._M_extent._M_extent_value == 0u64;"),
        "sentinel" => source
          .replace(" requires __count <= this->_M_extent._M_extent_value - __offset;", " requires __count == 18446744073709551615u64;")
          .replace(" requires count <= span._M_extent._M_extent_value - offset;", " requires count == 18446744073709551615u64;")
          .replace("result._M_extent._M_extent_value == old(__count)", "result._M_extent._M_extent_value == old(this->_M_extent._M_extent_value) - __offset")
          .replace("result._M_extent._M_extent_value == count", "result._M_extent._M_extent_value == old(span._M_extent._M_extent_value) - offset")
          .replace("this->_M_extent._M_extent_value, __offset, __count)", "this->_M_extent._M_extent_value, __offset, this->_M_extent._M_extent_value - __offset)")
          .replace("span._M_extent._M_extent_value, offset, count)", "span._M_extent._M_extent_value, offset, span._M_extent._M_extent_value - offset)")
          .replace("apply(bounded_subspan_count(this->_M_extent._M_extent_value, __offset, this->_M_extent._M_extent_value - __offset)); execute(); simp();", r#"
 step(); step(); step(); step(); step(); step(); step(); step(); step(); step();
 let observed = step(span__int__value_unsigned_long_18446744073709551615_size(this), {});
 have observed == this->_M_extent._M_extent_value by simp;
 have __offset <= observed by { rewrite(observed == this->_M_extent._M_extent_value); assumption(); }
 have observed <= 1073741823u64 by { rewrite(observed == this->_M_extent._M_extent_value); assumption(); }
 apply(bounded_subspan_count(observed, __offset, observed - __offset));
 execute(); simp();
"#),
        _ => source,
    };
    let path = root.join("span.click");
    fs::write(&path, &source).unwrap();
    let project = read_click_project(&path, &source).unwrap();
    verify_program_prepared_project(&project, &import).unwrap();
    if case.starts_with("expand-") {
        let label = if case == "expand-method" {
            "span__int__value_unsigned_long_18446744073709551615_subspan.contract"
        } else {
            "probe.contract"
        };
        let expanded =
            expand_program_prepared_project_claim_source_by_label(&project, &import, label)
                .unwrap();
        verify_program_prepared_project(&project.with_entry_source(expanded), &import).unwrap();
    }
    if case == "retain" {
        let (session, _) =
            C0VerificationSession::new_program_prepared_project(&project, &import).unwrap();
        let position = program_prepared_project_tactic_source_position(
            &project,
            &import,
            "probe.ensures_0",
            0,
        )
        .unwrap();
        session
            .verify_at_project(&source, position.line, position.column)
            .unwrap();
    }
    if case.starts_with("refuse-") {
        let mutations = [
            source.replace(" views span._M_ptr[0..span._M_extent._M_extent_value];", ""),
            source.replace(" requires offset <= span._M_extent._M_extent_value;", ""),
            source.replace(
                " requires count <= span._M_extent._M_extent_value - offset;",
                "",
            ),
            source.replace(
                " requires span._M_extent._M_extent_value <= 1073741823u64;",
                "",
            ),
            source.replace(
                "result._M_extent._M_extent_value == count;",
                "result._M_extent._M_extent_value != count;",
            ),
            source.replace(
                "old(span._M_ptr) + offset;",
                "old(span._M_ptr) + offset + 1u64;",
            ),
        ];
        let range = match case {
            "refuse-views" => 0..1,
            "refuse-bounds" => 1..4,
            _ => 4..6,
        };
        for hostile in &mutations[range] {
            assert!(
                verify_program_prepared_project(
                    &read_click_project(&path, hostile).unwrap(),
                    &import
                )
                .is_err()
            );
        }
    }
    fs::remove_dir_all(root).unwrap();
}

// Actual std::byte pointers retain native one-byte strides, checked nominal
// identities and ordinary ownership across offline verification and expansion.
#[test]
fn pinned_std_byte_pointer_stores_verify_offline() {
    let (root, import) = pinned_span_fixture_with_exact_dependencies(
        "byte-pointer",
        "#include <span.h>\nstd::byte probe(std::byte* p, std::byte value) noexcept { *(p + 1) = value; return *(p + 1); }\n",
        &["sysroot/usr/include/c++/12/cstddef"],
    );
    let source = "verifying \"span-probe.cpp\"; uint8 probe(uint8* p, uint8 value) { owns p[0..2]; ensures p[1] == value; ensures p[0] == old(p[0]); ensures result == value; } by { execute(); simp(); }";
    check_pinned_byte_proof(&root, &import, source);
    let bad = source.replace("owns p[0..2]", "views p[0..2]");
    fs::write(root.join("bad.click"), &bad).unwrap();
    assert!(
        verify_program_prepared_project(
            &read_click_project(&root.join("bad.click"), &bad).unwrap(),
            &import
        )
        .is_err()
    );
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn pinned_std_byte_automatic_pointer_store_initializes_offline() {
    let (root, import) = pinned_span_fixture_with_exact_dependencies(
        "byte-address",
        "#include <span.h>\nstd::byte probe(std::byte value) noexcept { std::byte obj; *(&obj) = value; return obj; }\n",
        &["sysroot/usr/include/c++/12/cstddef"],
    );
    check_pinned_byte_proof(
        &root,
        &import,
        "verifying \"span-probe.cpp\"; uint8 probe(uint8 value) { ensures result == value; } by { execute(); simp(); }",
    );
    fs::remove_dir_all(root).unwrap();
}

fn check_pinned_byte_proof(root: &Path, import: &PreparedCppImport, source: &str) {
    fs::write(root.join("byte.click"), source).unwrap();
    let project = read_click_project(&root.join("byte.click"), source).unwrap();
    verify_program_prepared_project(&project, import).unwrap();
    let expanded =
        expand_program_prepared_project_claim_source_by_label(&project, import, "probe.contract")
            .unwrap();
    let rewritten = project.with_entry_source(expanded.clone());
    verify_program_prepared_project(&rewritten, import).unwrap();
    let (session, _) =
        C0VerificationSession::new_program_prepared_project(&project, import).unwrap();
    let position =
        program_prepared_project_tactic_source_position(&rewritten, import, "probe.contract", 0)
            .unwrap();
    session
        .verify_at_project(&expanded, position.line, position.column)
        .unwrap();
}

#[test]
// Consistent rehashing cannot substitute another nominal enum or move its
// declaration to another locked source to manufacture byte alias privilege.
fn pinned_std_byte_pointer_artifacts_reject_forged_declarations_offline() {
    let (root, _) = pinned_span_fixture_with_exact_dependencies(
        "byte-pointer-forgery",
        "#include <span.h>\nstd::byte probe(std::byte* p) noexcept { return *p; }\n",
        &["sysroot/usr/include/c++/12/cstddef"],
    );
    let artifact_path = root.join("span.click-cpp.json");
    let lock_path = root.join("span.click.import.json.lock");
    let artifact: serde_json::Value =
        serde_json::from_slice(&fs::read(&artifact_path).unwrap()).unwrap();
    let lock: serde_json::Value = serde_json::from_slice(&fs::read(&lock_path).unwrap()).unwrap();
    fn change_enums(value: &mut serde_json::Value, change: usize) {
        match value {
            serde_json::Value::Object(object) => {
                if object.get("kind").and_then(|v| v.as_str()) == Some("enumeration") {
                    match change {
                        0 => {
                            object.insert("name".into(), "Other".into());
                            object.insert("declaration_id".into(), "c:@E@Other".into());
                        }
                        1 => {
                            object.get_mut("span").unwrap()["file"] = "span-probe.cpp".into();
                        }
                        2 => {
                            object.get_mut("span").unwrap()["start_line"] = 70.into();
                        }
                        3 => {
                            object.get_mut("underlying_type").unwrap()["signed"] = true.into();
                        }
                        _ => unreachable!(),
                    }
                }
                for child in object.values_mut() {
                    change_enums(child, change);
                }
            }
            serde_json::Value::Array(values) => {
                for child in values {
                    change_enums(child, change);
                }
            }
            _ => {}
        }
    }
    for change in 0..5 {
        let mut forged = artifact.clone();
        if change == 4 {
            forged["preprocessor_files"]
                .as_array_mut()
                .unwrap()
                .retain(|file| {
                    !file["canonical_path"]
                        .as_str()
                        .unwrap()
                        .ends_with("/cstddef")
                });
        } else {
            change_enums(&mut forged, change);
        }
        let bytes = serde_json::to_vec_pretty(&forged).unwrap();
        let mut forged_lock = lock.clone();
        forged_lock["artifact_sha256"] = sha256(&bytes).into();
        forged_lock["artifact_bytes"] = bytes.len().into();
        fs::write(&artifact_path, bytes).unwrap();
        fs::write(&lock_path, serde_json::to_vec_pretty(&forged_lock).unwrap()).unwrap();
        assert!(
            load_import(&root.join("span.click.import.json")).is_err(),
            "mutation {change}"
        );
    }
    // A self-consistent dependency digest still cannot replace the standard
    // header pin. Keep the declaration spelling and span unchanged.
    let header = "sysroot/usr/include/c++/12/cstddef";
    let mut header_bytes = fs::read(root.join(header)).unwrap();
    header_bytes.extend_from_slice(b"\n// substituted standard header\n");
    fs::write(root.join(header), &header_bytes).unwrap();
    let mut forged_lock = lock;
    forged_lock["dependencies"][header] = sha256(&header_bytes).into();
    fs::write(
        &artifact_path,
        serde_json::to_vec_pretty(&artifact).unwrap(),
    )
    .unwrap();
    // Preserve the original artifact bytes hashed by the lock, rather than
    // relying on JSON formatting to round-trip byte-for-byte.
    let restored = fs::read(&artifact_path).unwrap();
    forged_lock["artifact_sha256"] = sha256(&restored).into();
    forged_lock["artifact_bytes"] = restored.len().into();
    fs::write(&lock_path, serde_json::to_vec_pretty(&forged_lock).unwrap()).unwrap();
    let error = load_import(&root.join("span.click.import.json")).unwrap_err();
    assert!(
        error.contains("std::byte declaration header differs"),
        "{error}"
    );
    fs::remove_dir_all(root).unwrap();
}

#[test]
// Allocated enum scalars can lend their exact byte owner to an ordinary helper;
// the returned contract value must refresh the caller binding.
fn pinned_std_byte_modular_pointer_call_verifies_offline() {
    let (root, import) = pinned_span_fixture_with_exact_dependencies(
        "byte-pointer-call",
        "#include <span.h>\nvoid fill(std::byte* p, std::byte value) noexcept { *p = value; } std::byte probe(std::byte value) noexcept { std::byte obj = static_cast<std::byte>(0); fill(&obj, value); return obj; }\n",
        &["sysroot/usr/include/c++/12/cstddef"],
    );
    check_pinned_byte_proof(
        &root,
        &import,
        "verifying \"span-probe.cpp\"; void fill(uint8* p, uint8 value) { owns p[0..1]; ensures p[0] == value; } by { execute(); simp(); } uint8 probe(uint8 value) { ensures result == value; } by { execute(); simp(); }",
    );
    fs::remove_dir_all(root).unwrap();
}

#[test]
// Pointer reinterpretation supplies no initialization. Four concrete byte
// stores complete the shared uint32 representation on the selected LE target.
fn pinned_std_byte_reinterpretation_initializes_uint32_offline() {
    let (root, import) = pinned_span_fixture_with_exact_dependencies(
        "byte-cast-word",
        "#include <span.h>\nunsigned int probe() noexcept { unsigned int obj; std::byte* p = reinterpret_cast<std::byte*>(&obj); *p = static_cast<std::byte>(120); *(p + 1) = static_cast<std::byte>(86); *(p + 2) = static_cast<std::byte>(52); *(p + 3) = static_cast<std::byte>(18); return obj; }\n",
        &["sysroot/usr/include/c++/12/cstddef"],
    );
    check_pinned_byte_proof(
        &root,
        &import,
        "verifying \"span-probe.cpp\"; uint32 probe() { ensures result == 305419896u32; } by { execute(); simp(); }",
    );
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn pinned_std_byte_reinterpreted_call_result_preserves_pointer_identity_offline() {
    let (root, import) = pinned_span_fixture_with_exact_dependencies(
        "byte-cast-call",
        "#include <span.h>\nunsigned int* echo(unsigned int* p) noexcept { return p; } std::byte* probe(unsigned int* p) noexcept { return reinterpret_cast<std::byte*>(echo(p)); }\n",
        &["sysroot/usr/include/c++/12/cstddef"],
    );
    check_pinned_byte_proof(
        &root,
        &import,
        "verifying \"span-probe.cpp\"; uint32* echo(uint32* p) { ensures result == p; } by { execute(); simp(); } uint8* probe(uint32* p) { ensures result == (uint8*)p; } by { execute(); simp(); }",
    );
    let artifact_path = root.join("span.click-cpp.json");
    let lock_path = root.join("span.click.import.json.lock");
    let artifact: serde_json::Value =
        serde_json::from_slice(&fs::read(&artifact_path).unwrap()).unwrap();
    let lock: serde_json::Value = serde_json::from_slice(&fs::read(&lock_path).unwrap()).unwrap();
    for change in 0..4 {
        let mut forged = artifact.clone();
        let conversion = &mut forged["function"]["body"][0]["conversions"][0];
        match change {
            0 => conversion["cast_kind"] = "no_op".into(),
            1 => conversion["explicit"] = false.into(),
            2 => conversion["source_type"]["pointee"]["bits"] = 64.into(),
            3 => {
                conversion["value_type"]["pointee"]["name"] = "Other".into();
                conversion["value_type"]["pointee"]["declaration_id"] = "c:@E@Other".into();
            }
            _ => unreachable!(),
        }
        let bytes = serde_json::to_vec_pretty(&forged).unwrap();
        let mut forged_lock = lock.clone();
        forged_lock["artifact_sha256"] = sha256(&bytes).into();
        forged_lock["artifact_bytes"] = bytes.len().into();
        fs::write(&artifact_path, bytes).unwrap();
        fs::write(&lock_path, serde_json::to_vec_pretty(&forged_lock).unwrap()).unwrap();
        assert!(
            load_import(&root.join("span.click.import.json")).is_err(),
            "mutation {change}"
        );
    }
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn pinned_std_byte_reinterpretation_does_not_initialize_partial_storage() {
    let (root, import) = pinned_span_fixture_with_exact_dependencies(
        "byte-cast-partial",
        "#include <span.h>\nunsigned int probe() noexcept { unsigned int obj; std::byte* p = reinterpret_cast<std::byte*>(&obj); *p = static_cast<std::byte>(120); return obj; }\n",
        &["sysroot/usr/include/c++/12/cstddef"],
    );
    let source = "verifying \"span-probe.cpp\"; uint32 probe() { ensures result == 120u32; } by { execute(); simp(); }";
    fs::write(root.join("bad.click"), source).unwrap();
    let error = verify_program_prepared_project(
        &read_click_project(&root.join("bad.click"), source).unwrap(),
        &import,
    )
    .unwrap_err();
    assert!(
        error.message().contains("uninitialized"),
        "{}",
        error.message()
    );
    fs::remove_dir_all(root).unwrap();
}

#[test]
// Changing the access type cannot mint write permission over the original word.
fn pinned_std_byte_reinterpretation_requires_original_storage_ownership() {
    let (root, import) = pinned_span_fixture_with_exact_dependencies(
        "byte-cast-authority",
        "#include <span.h>\nunsigned char probe(unsigned int* p) noexcept { std::byte* bytes = reinterpret_cast<std::byte*>(p); *bytes = static_cast<std::byte>(7); return static_cast<unsigned char>(*bytes); }\n",
        &["sysroot/usr/include/c++/12/cstddef"],
    );
    let source = "verifying \"span-probe.cpp\"; uint8 probe(uint32* p) { owns p[0..1]; ensures result == 7u8; } by { execute(); simp(); }";
    check_pinned_byte_proof(&root, &import, source);
    for bad in [
        source.replace("owns p[0..1];", "views p[0..1];"),
        source.replace("owns p[0..1];", ""),
    ] {
        fs::write(root.join("bad.click"), &bad).unwrap();
        assert!(
            verify_program_prepared_project(
                &read_click_project(&root.join("bad.click"), &bad).unwrap(),
                &import
            )
            .is_err()
        );
    }
    fs::remove_dir_all(root).unwrap();
}
