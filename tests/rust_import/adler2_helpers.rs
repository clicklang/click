use super::*;
use sha2::{Digest, Sha256};

const HELPERS: &str = include_str!("../../design/charon-trial/adler2/helpers.click");

fn adler2_helpers_project() -> Project {
    let p = Project::new("");
    fs::create_dir(p.root.join("src")).unwrap();
    let manifest: serde_json::Value =
        serde_json::from_str(include_str!("../../design/rust-checksum-sources.json")).unwrap();
    let pin = manifest["sources"]
        .as_array()
        .unwrap()
        .iter()
        .find(|entry| entry["name"] == "adler2")
        .unwrap();
    for (name, bytes) in [
        (
            "src/lib.rs",
            include_bytes!("../../design/charon-trial/adler2/src/lib.rs").as_slice(),
        ),
        (
            "src/algo.rs",
            include_bytes!("../../design/charon-trial/adler2/src/algo.rs").as_slice(),
        ),
    ] {
        let file = pin["files"]
            .as_array()
            .unwrap()
            .iter()
            .find(|file| file["path"] == name)
            .unwrap();
        assert_eq!(format!("{:x}", Sha256::digest(bytes)), file["sha256"]);
        fs::write(p.root.join(name), bytes).unwrap();
    }
    for (name, bytes) in [
        ("borrow.click", HELPERS.as_bytes()),
        (
            "borrow.click.import.json",
            include_bytes!("../../design/charon-trial/adler2/helpers.click.import.json").as_slice(),
        ),
        (
            "helpers.ullbc",
            include_bytes!("../../design/charon-trial/adler2/helpers.ullbc").as_slice(),
        ),
        (
            "borrow.click.import.json.lock",
            include_bytes!("../../design/charon-trial/adler2/helpers.click.import.json.lock")
                .as_slice(),
        ),
    ] {
        fs::write(p.root.join(name), bytes).unwrap();
    }
    p
}

fn helper_proof(index: usize) -> String {
    let blocks: Vec<_> = HELPERS.split("\n\n").collect();
    assert_eq!(blocks.len(), 5);
    format!("{}\n\n{}", blocks[0], blocks[index + 1])
}

fn reject_helper_contracts(index: usize, mutations: &[(&str, &str)]) {
    let p = adler2_helpers_project();
    let prepared = load_import(&p.config()).unwrap();
    let proof = helper_proof(index);
    C0VerificationSession::new_program_prepared(&proof, &prepared).unwrap();
    for (before, after) in mutations {
        let invalid = proof.replace(before, after);
        assert_ne!(invalid, proof, "missing mutation: {before}");
        assert!(
            C0VerificationSession::new_program_prepared(&invalid, &prepared).is_err(),
            "accepted {before} -> {after}"
        );
    }
}

#[test]
fn charon_adler2_helpers_prove_all_lanes_and_lock_original_modules() {
    let p = adler2_helpers_project();
    let prepared = load_import(&p.config()).unwrap();
    assert!(
        prepared
            .export()
            .functions
            .iter()
            .any(|f| f.name.ends_with("_I7_compute") && f.mir.is_some())
    );
    C0VerificationSession::new_program_prepared(HELPERS, &prepared).unwrap();
    // Module identity is checked even when all the proved helpers are unchanged.
    fs::write(p.root.join("src/lib.rs"), "// changed crate root\n").unwrap();
    assert!(
        load_import(&p.config())
            .unwrap_err()
            .contains("lock differs")
    );
}

#[test]
fn charon_adler2_helpers_from_rejects_false_lanes_and_short_reads() {
    reject_helper_contracts(
        0,
        &[
            ("result._0[3] == bytes[3]", "result._0[3] == bytes[2]"),
            ("requires bytes_len >= 4u64;", "requires bytes_len >= 3u64;"),
            ("views bytes[0..4];", "views bytes[0..3];"),
        ],
    );
}

#[test]
fn charon_adler2_helpers_add_rejects_false_lanes_and_overflow() {
    reject_helper_contracts(
        1,
        &[
            (
                "old(self->_0[3]) + other._0[3]",
                "old(self->_0[3]) + other._0[2]",
            ),
            (
                "requires ((int64)self->_0[3] + (int64)other._0[3]) <= 4294967295i64;",
                "",
            ),
            ("4294967295i64", "4294967296i64"),
            (
                "((int64)self->_0[3] + (int64)other._0[3]) <= 4294967295i64",
                "self->_0[3] + other._0[3] <= 4294967295u32",
            ),
            ("owns self->_0[0..4];", "views self->_0[0..4];"),
        ],
    );
}

#[test]
fn charon_adler2_helpers_rem_rejects_false_lanes_and_zero_divisor() {
    reject_helper_contracts(
        2,
        &[
            ("old(self->_0[3]) % quotient", "old(self->_0[2]) % quotient"),
            ("requires quotient != 0u32;", ""),
            ("owns self->_0[0..4];", "views self->_0[0..4];"),
        ],
    );
}

#[test]
fn charon_adler2_helpers_mul_rejects_false_lanes_and_overflow() {
    reject_helper_contracts(
        3,
        &[
            ("old(self->_0[3]) * rhs", "old(self->_0[2]) * rhs"),
            (
                "requires rhs == 0u32 or self->_0[3] <= 4294967295u32 / rhs;",
                "",
            ),
            ("owns self->_0[0..4];", "views self->_0[0..4];"),
        ],
    );
}

fn recheck_helper_tools(index: usize, commands: &[&str], expand: bool) {
    let p = adler2_helpers_project();
    let proof = helper_proof(index);
    let claim = proof
        .lines()
        .find(|line| line.starts_with("struct ") || line.starts_with("void "))
        .unwrap()
        .split_once('(')
        .unwrap()
        .0
        .split_whitespace()
        .last()
        .unwrap();
    fs::write(p.root.join("borrow.click"), &proof).unwrap();
    for command in commands {
        assert_cli(&p, &[command]);
    }
    if expand {
        assert_cli(
            &p,
            &[
                "expand",
                "--claim",
                &format!("{claim}.contract"),
                "--in-place",
            ],
        );
        assert_cli(&p, &["verify"]);
    }
}

#[test]
fn charon_adler2_helpers_from_tools_recheck_expanded_certificate() {
    recheck_helper_tools(0, &["verify", "profile", "audit"], true);
}
#[test]
fn charon_adler2_helpers_add_tools_recheck_expanded_certificate() {
    recheck_helper_tools(1, &["verify", "profile", "audit"], true);
}
#[test]
fn charon_adler2_helpers_rem_tools_recheck_expanded_certificate() {
    recheck_helper_tools(2, &["verify", "profile", "audit"], true);
}
#[test]
fn charon_adler2_helpers_mul_profile_checks_verified_contract() {
    recheck_helper_tools(3, &["verify", "profile"], false);
}
fn audit_mul_site(tactic: &str) {
    let p = adler2_helpers_project();
    let proof = helper_proof(3);
    fs::write(p.root.join("borrow.click"), &proof).unwrap();
    let prefix = proof.split_once(tactic).unwrap().0;
    let line = prefix.bytes().filter(|byte| *byte == b'\n').count() + 1;
    let column = prefix.rsplit('\n').next().unwrap().len() + 1;
    let cursor = format!("{}:{line}:{column}", p.root.join("borrow.click").display());
    // Each site still expands, rechecks retained/cold proofs, and checks its
    // fixed point. Bound the audit to one site so timings name that site.
    let result = p.cli(&["audit", "--start-at", &cursor, "--max-sites", "1"]);
    let stdout = String::from_utf8_lossy(&result.stdout);
    assert!(
        result.status.success(),
        "{stdout}\n{}",
        String::from_utf8_lossy(&result.stderr)
    );
    assert!(
        stdout.contains("SUMMARY: 1 sites passed; 0 site failures; 0 session failures;"),
        "{stdout}"
    );
}

#[test]
fn charon_adler2_helpers_mul_audit_execute_certificate() {
    audit_mul_site("execute()");
}
#[test]
fn charon_adler2_helpers_mul_audit_simp_certificate() {
    audit_mul_site("simp()");
}
#[test]
fn charon_adler2_helpers_mul_tools_recheck_expanded_certificate() {
    recheck_helper_tools(3, &["verify"], true);
}

#[test]
#[ignore = "requires the pinned live Charon extractor"]
fn charon_adler2_helpers_live_refresh_proves_original_bodies() {
    let p = adler2_helpers_project();
    let mut config: serde_json::Value =
        serde_json::from_slice(&fs::read(p.config()).unwrap()).unwrap();
    config["exporter"] = std::env::var("CLICK_CHARON").unwrap().into();
    fs::write(p.config(), serde_json::to_vec(&config).unwrap()).unwrap();
    refresh_import(&p.config()).unwrap();
    C0VerificationSession::new_program_prepared(HELPERS, &load_import(&p.config()).unwrap())
        .unwrap();
}

const BOUNDS: &str = include_str!("../../design/charon-trial/adler2/bounds.click");

#[test]
fn charon_adler2_lane_bounds_prove_batch_limits_and_step_safety() {
    use click::surface::verify_click_theorems;
    assert_eq!(verify_click_theorems(BOUNDS).unwrap().len(), 30);
    for (before, after) in [
        ("requires n <= 5552;", "requires n <= 5553;"),
        ("requires n < 5552;", "requires n <= 5552;"),
        ("requires byte <= 255;", "requires byte <= 256;"),
        (
            "requires to_integer(byte) <= 255;",
            "requires to_integer(byte) <= 256;",
        ),
        ("requires to_integer(b) <= adler_lane_b_ceiling(n);", ""),
        (
            "ensures to_integer(b + (a + byte)) <= adler_lane_b_ceiling(n + 1)",
            "ensures to_integer(b + (a + byte)) <= adler_lane_b_ceiling(n)",
        ),
        ("requires b <= adler_lane_b_ceiling(n);", ""),
        ("requires 0 <= n;", ""),
        (
            "integer_product_bounds bounds [0, 1, 2, 3] => n * (n + 1) <= 30830256;",
            "integer_product_bounds bounds [0, 1, 2, 3] => n * (n + 1) <= 30830255;",
        ),
        (
            "integer_division_bounds bounds [0, 1, 2, 3] => truncating_quotient(n * (n + 1), divisor) <= 15415128;",
            "integer_division_bounds bounds [0, 1, 2, 3] => truncating_quotient(n * (n + 1), divisor) <= 15415127;",
        ),
        (
            "ensures adler_lane_b_ceiling(5553) > 4294967295",
            "ensures adler_lane_b_ceiling(5553) <= 4294967295",
        ),
        (
            "ensures a + byte <= adler_lane_a_ceiling(n + 1)",
            "ensures a + byte <= adler_lane_a_ceiling(n)",
        ),
        (
            "ensures b + (a + byte) <= adler_lane_b_ceiling(n + 1)",
            "ensures b + (a + byte) <= adler_lane_b_ceiling(n)",
        ),
        (
            "integer_polynomial_identity bounds [] => (n + 1) * ((n + 1) + 1) == n * (n + 1) + 2 * (n + 1)",
            "integer_polynomial_identity bounds [] => (n + 1) * ((n + 1) + 1) == n * (n + 1) + 3 * (n + 1)",
        ),
        (
            "integer_quotient_shift bounds [0, 1]",
            "integer_quotient_shift bounds [1, 0]",
        ),
    ] {
        let invalid = BOUNDS.replace(before, after);
        assert_ne!(invalid, BOUNDS, "missing mutation: {before}");
        assert!(
            verify_click_theorems(&invalid).is_err(),
            "accepted {before} -> {after}"
        );
    }
}

#[test]
fn charon_adler2_lane_bounds_verify_with_original_helper_contracts() {
    let p = adler2_helpers_project();
    let prepared = load_import(&p.config()).unwrap();
    C0VerificationSession::new_program_prepared(&format!("{HELPERS}\n{BOUNDS}"), &prepared)
        .unwrap();
}

#[test]
fn charon_adler2_lane_bounds_tools_recheck_expanded_certificates() {
    let p = adler2_helpers_project();
    fs::write(p.root.join("bounds.click"), BOUNDS).unwrap();
    for command in ["verify", "profile", "audit"] {
        let result = Command::new(env!("CARGO_BIN_EXE_click"))
            .arg(command)
            .arg(p.root.join("bounds.click"))
            .output()
            .unwrap();
        assert!(
            result.status.success(),
            "{}\n{}",
            String::from_utf8_lossy(&result.stdout),
            String::from_utf8_lossy(&result.stderr)
        );
    }
}

#[test]
fn charon_adler2_lane_bounds_tools_expand_math_certificates() {
    expand_bounds_claims(&[
        ("adler_lane_half_product_5551", 1),
        ("adler_lane_triangle_5551", 1),
        ("adler_lane_ceiling_5551", 2),
        ("adler_lane_half_product_5552", 1),
        ("adler_lane_triangle_5552", 1),
        ("adler_lane_ceiling_5552", 2),
        ("adler_lane_initial_ceiling", 2),
        ("adler_lane_step_a", 2),
        ("adler_lane_step_b", 2),
        ("adler_lane_limit_is_tight", 4),
        ("adler_lane_a_invariant_step", 1),
        ("adler_lane_triangle_successor", 1),
        ("adler_lane_b_ceiling_successor", 1),
        ("adler_lane_b_invariant_step", 1),
    ]);
}

#[test]
fn charon_adler2_lane_bounds_tools_expand_native_certificates() {
    expand_bounds_claims(&[
        ("adler_lane_native_a_sum_fits", 1),
        ("adler_lane_native_a_step", 3),
        ("adler_lane_native_b_sum_fits", 1),
        ("adler_lane_native_b_step", 3),
    ]);
}

fn expand_bounds_claims(claims: &[(&str, usize)]) {
    let p = adler2_helpers_project();
    fs::write(p.root.join("bounds.click"), BOUNDS).unwrap();
    for &(name, ensures) in claims {
        for index in 0..ensures {
            let result = Command::new(env!("CARGO_BIN_EXE_click"))
                .args([
                    "expand",
                    "--claim",
                    &format!("{name}.ensures_{index}"),
                    "--in-place",
                ])
                .arg(p.root.join("bounds.click"))
                .output()
                .unwrap();
            assert!(
                result.status.success(),
                "{name}: {}\n{}",
                String::from_utf8_lossy(&result.stdout),
                String::from_utf8_lossy(&result.stderr)
            );
        }
    }
    let expanded = fs::read_to_string(p.root.join("bounds.click")).unwrap();
    assert_eq!(
        click::surface::verify_click_theorems(&expanded)
            .unwrap()
            .len(),
        30
    );
}

const ITERATOR_BOUNDS: &str =
    include_str!("../../design/charon-trial/adler2/iterator-bounds.click");

fn flat_iterator_bounds() -> String {
    format!(
        "{BOUNDS}\n{}",
        ITERATOR_BOUNDS
            .strip_prefix("import \"bounds.click\";\n")
            .unwrap()
    )
}

#[test]
fn charon_adler2_iterator_bounds_prove_derived_index_and_native_preservation() {
    use click::surface::verify_click_theorems;
    let source = flat_iterator_bounds();
    assert_eq!(verify_click_theorems(&source).unwrap().len(), 60);
    for (before, after) in [
        ("requires total <= 22208;", "requires total <= 22212;"),
        ("requires remaining <= total;", ""),
        ("requires 0 <= remaining;", ""),
        ("requires 4 <= remaining;", ""),
        ("requires defined(remaining - 4);", ""),
        ("requires 0 <= consumed;", ""),
        ("requires 0 <= increment;", ""),
        ("+ 4 * increment", "+ 8 * increment"),
        (
            "ensures adler_lane_vectors_consumed(22208, 0) == 5552",
            "ensures adler_lane_vectors_consumed(22208, 0) == 5551",
        ),
        (
            "ensures to_integer(b + (a + byte)) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(total, remaining - 4))",
            "ensures to_integer(b + (a + byte)) <= adler_lane_b_ceiling(adler_lane_vectors_consumed(total, remaining))",
        ),
    ] {
        let invalid = source.replace(before, after);
        assert_ne!(source, invalid, "missing mutation: {before}");
        assert!(
            verify_click_theorems(&invalid).is_err(),
            "accepted {before} -> {after}"
        );
    }
}

fn iterator_bounds_project() -> Project {
    let p = adler2_helpers_project();
    fs::write(p.root.join("bounds.click"), BOUNDS).unwrap();
    fs::write(p.root.join("iterator-bounds.click"), ITERATOR_BOUNDS).unwrap();
    p
}

#[test]
fn charon_adler2_iterator_bounds_verify_with_locked_original_helpers() {
    let p = iterator_bounds_project();
    let prepared = load_import(&p.config()).unwrap();
    let source = format!("{HELPERS}\nimport \"iterator-bounds.click\";\n");
    let project = click::cli::read_click_project(&p.root.join("borrow.click"), &source).unwrap();
    C0VerificationSession::new_program_prepared_project(&project, &prepared).unwrap();
}

#[test]
fn charon_adler2_iterator_bounds_tools_verify_profile_and_audit() {
    let p = iterator_bounds_project();
    for command in ["verify", "profile", "audit"] {
        let result = Command::new(env!("CARGO_BIN_EXE_click"))
            .arg(command)
            .arg(p.root.join("iterator-bounds.click"))
            .output()
            .unwrap();
        assert!(
            result.status.success(),
            "{command}: {}\n{}",
            String::from_utf8_lossy(&result.stdout),
            String::from_utf8_lossy(&result.stderr)
        );
    }
}

fn expand_iterator_bounds_claims(claims: &[(&str, usize)]) {
    let p = iterator_bounds_project();
    for &(name, ensures) in claims {
        for index in 0..ensures {
            let result = Command::new(env!("CARGO_BIN_EXE_click"))
                .args([
                    "expand",
                    "--claim",
                    &format!("{name}.ensures_{index}"),
                    "--in-place",
                ])
                .arg(p.root.join("iterator-bounds.click"))
                .output()
                .unwrap();
            assert!(
                result.status.success(),
                "{name}: {}\n{}",
                String::from_utf8_lossy(&result.stdout),
                String::from_utf8_lossy(&result.stderr)
            );
        }
    }
    let expanded = fs::read_to_string(p.root.join("iterator-bounds.click")).unwrap();
    let source = format!(
        "{BOUNDS}\n{}",
        expanded.strip_prefix("import \"bounds.click\";\n").unwrap()
    );
    assert_eq!(
        click::surface::verify_click_theorems(&source)
            .unwrap()
            .len(),
        60
    );
}

#[test]
fn charon_adler2_iterator_bounds_tools_expand_index_certificates() {
    expand_iterator_bounds_claims(&[
        ("adler_lane_iterator_observations", 3),
        ("adler_lane_iterator_consumed_bounds", 2),
        ("adler_lane_iterator_count_bounds", 2),
        ("adler_lane_iterator_index_bounds", 2),
        ("adler_lane_iterator_initial", 1),
        ("adler_lane_iterator_next_defined", 1),
        ("adler_lane_iterator_count_before_next", 1),
        ("adler_lane_iterator_index_before_next", 1),
        ("adler_lane_iterator_quotient_shift", 1),
        ("adler_lane_iterator_successor", 1),
    ]);
}

#[test]
fn charon_adler2_iterator_bounds_tools_expand_native_certificates() {
    expand_iterator_bounds_claims(&[
        ("adler_lane_iterator_native_step", 4),
        ("adler_lane_iterator_successor_ceilings", 2),
        ("adler_lane_iterator_native_preservation", 2),
        ("adler_lane_iterator_boundaries", 7),
    ]);
}
