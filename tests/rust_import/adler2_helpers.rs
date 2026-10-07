use super::*;
use sha2::{Digest, Sha256};

const HELPERS: &str = include_str!("../../design/charon-trial/adler2/helpers.click");
const SINGLE_BYTE_COMPUTE: &str =
    include_str!("../../design/charon-trial/adler2/single-byte-compute.click");

const TWO_BYTE_COMPUTE: &str =
    include_str!("../../design/charon-trial/adler2/two-byte-compute.click");
const THREE_BYTE_COMPUTE: &str =
    include_str!("../../design/charon-trial/adler2/three-byte-compute.click");

fn compute_proof(contract: &str) -> String {
    let computation = HELPERS.split_once("# Empty-input boundary").unwrap().1;
    let getters = &computation[computation.find("\nuint32 ").unwrap()..];
    // Function-contract imports are not admitted yet. Assemble one verification
    // unit from the canonical helper/getter bodies and this alternative compute
    // contract, rather than duplicating or assuming their interfaces.
    format!("{}\n{contract}\n{getters}", helper_library())
}

fn compute_project(contract: &str) -> Project {
    let p = adler2_helpers_project();
    fs::write(p.root.join("borrow.click"), compute_proof(contract)).unwrap();
    p
}

fn reject_compute(contract: &str, before: &str, after: &str) {
    let p = adler2_helpers_project();
    let prepared = load_import(&p.config()).unwrap();
    let changed = contract.replacen(before, after, 1);
    assert_ne!(changed, contract, "missing mutation: {before}");
    let invalid = compute_proof(&changed);
    let offset = invalid.find("execute_until(assignment(b, 0))").unwrap();
    let line = invalid[..offset].bytes().filter(|&b| b == b'\n').count() + 1;
    let error = click::surface::verify_program_prepared_sources_at(&invalid, &prepared, line, 2)
        .expect_err("invalid computation contract was accepted");
    assert!(
        !error.message().contains("budget exhausted"),
        "{}",
        error.message()
    );
}

fn reject_single_byte_compute(before: &str, after: &str) {
    reject_compute(SINGLE_BYTE_COMPUTE, before, after);
}

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

fn helper_library() -> &'static str {
    HELPERS.split_once("# Empty-input boundary").unwrap().0
}

fn helper_proof(index: usize) -> String {
    let blocks: Vec<_> = helper_library().trim_end().split("\n\n").collect();
    assert_eq!(blocks.len(), 5);
    assert!(index < 4);
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
    C0VerificationSession::new_program_prepared(helper_library(), &prepared).unwrap();
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

fn reject_helper_byte_bounds(lane: usize) {
    let native = format!("result._0[{lane}] <= 255u32");
    let false_native = format!("result._0[{lane}] <= 254u32");
    let upper = format!("to_integer(result._0[{lane}]) <= 255");
    let false_upper = format!("to_integer(result._0[{lane}]) <= 254");
    let lower = format!("0 <= to_integer(result._0[{lane}])");
    let false_lower = format!("1 <= to_integer(result._0[{lane}])");
    reject_helper_contracts(
        0,
        &[
            (&native, &false_native),
            (&upper, &false_upper),
            (&lower, &false_lower),
        ],
    );
}

#[test]
fn charon_adler2_helpers_from_rejects_false_byte_bounds_lane_0() {
    reject_helper_byte_bounds(0);
}

#[test]
fn charon_adler2_helpers_from_rejects_false_byte_bounds_lane_1() {
    reject_helper_byte_bounds(1);
}

#[test]
fn charon_adler2_helpers_from_rejects_false_byte_bounds_lane_2() {
    reject_helper_byte_bounds(2);
}

#[test]
fn charon_adler2_helpers_from_rejects_false_byte_bounds_lane_3() {
    reject_helper_byte_bounds(3);
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
                "requires to_integer(self->_0[3]) + to_integer(other._0[3]) <= 4294967295;",
                "",
            ),
            ("<= 4294967295;", "<= 4294967296;"),
            (
                "requires to_integer(self->_0[3]) + to_integer(other._0[3]) <= 4294967295;",
                "requires self->_0[3] + other._0[3] <= 4294967295u32;",
            ),
            ("owns self->_0[0..4];", "views self->_0[0..4];"),
        ],
    );
}

fn reject_helper_add_observations(lane: usize) {
    let exact = format!(
        "ensures to_integer(self->_0[{lane}]) == to_integer(old(self->_0[{lane}])) + to_integer(other._0[{lane}]);"
    );
    let wrong = format!(
        "ensures to_integer(self->_0[{lane}]) == to_integer(old(self->_0[{lane}])) + to_integer(other._0[{}]);",
        (lane + 1) % 4
    );
    let lower = format!("ensures 0 <= to_integer(self->_0[{lane}]);");
    let false_lower = format!("ensures 1 <= to_integer(self->_0[{lane}]);");
    reject_helper_contracts(1, &[(&exact, &wrong), (&lower, &false_lower)]);
}

#[test]
fn charon_adler2_helpers_add_rejects_false_observations_lane_0() {
    reject_helper_add_observations(0);
}

#[test]
fn charon_adler2_helpers_add_rejects_false_observations_lane_1() {
    reject_helper_add_observations(1);
}

#[test]
fn charon_adler2_helpers_add_rejects_false_observations_lane_2() {
    reject_helper_add_observations(2);
}

#[test]
fn charon_adler2_helpers_add_rejects_false_observations_lane_3() {
    reject_helper_add_observations(3);
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

fn reject_helper_reduction_bounds(lane: usize) {
    let native = format!("ensures self->_0[{lane}] < quotient;");
    let false_native = format!("ensures self->_0[{lane}] < quotient - 1u32;");
    let lower = format!("0 <= to_integer(self->_0[{lane}])");
    let false_lower = format!("1 <= to_integer(self->_0[{lane}])");
    let upper = format!("to_integer(self->_0[{lane}]) < to_integer(quotient)");
    let false_upper = format!("to_integer(self->_0[{lane}]) < to_integer(quotient) - 1");
    reject_helper_contracts(
        2,
        &[
            (&native, &false_native),
            (&lower, &false_lower),
            (&upper, &false_upper),
        ],
    );
}

#[test]
fn charon_adler2_helpers_rem_rejects_false_reduction_bounds_lane_0() {
    reject_helper_reduction_bounds(0);
}

#[test]
fn charon_adler2_helpers_rem_rejects_false_reduction_bounds_lane_1() {
    reject_helper_reduction_bounds(1);
}

#[test]
fn charon_adler2_helpers_rem_rejects_false_reduction_bounds_lane_2() {
    reject_helper_reduction_bounds(2);
}

#[test]
fn charon_adler2_helpers_rem_rejects_false_reduction_bounds_lane_3() {
    reject_helper_reduction_bounds(3);
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

fn reject_helper_product_observations(lane: usize) {
    let exact = format!(
        "ensures to_integer(self->_0[{lane}]) == to_integer(old(self->_0[{lane}])) * to_integer(rhs);"
    );
    let wrong_product = exact.replace("== to_integer", "== 1 + to_integer");
    let lower = format!("0 <= to_integer(self->_0[{lane}])");
    let false_lower = format!("1 <= to_integer(self->_0[{lane}])");
    let upper = format!("to_integer(self->_0[{lane}]) <= 4294967295");
    let false_upper = format!("to_integer(self->_0[{lane}]) <= 4294967294");
    let guard = format!("requires rhs == 0u32 or self->_0[{lane}] <= 4294967295u32 / rhs;");
    reject_helper_contracts(
        3,
        &[
            (&exact, &wrong_product),
            (&lower, &false_lower),
            (&upper, &false_upper),
            (&guard, ""),
        ],
    );
}

#[test]
fn charon_adler2_helpers_mul_rejects_false_observations_lane_0() {
    reject_helper_product_observations(0);
}

#[test]
fn charon_adler2_helpers_mul_rejects_false_observations_lane_1() {
    reject_helper_product_observations(1);
}

#[test]
fn charon_adler2_helpers_mul_rejects_false_observations_lane_2() {
    reject_helper_product_observations(2);
}

#[test]
fn charon_adler2_helpers_mul_rejects_false_observations_lane_3() {
    reject_helper_product_observations(3);
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
#[ignore = "nightly: whole-fixture proof-tool agreement and expansion coverage"]
fn charon_adler2_helpers_from_tools_recheck_expanded_certificate() {
    recheck_helper_tools(0, &["verify", "profile", "audit"], true);
}
#[test]
#[ignore = "nightly: whole-fixture proof-tool agreement and expansion coverage"]
fn charon_adler2_helpers_add_tools_recheck_expanded_certificate() {
    recheck_helper_tools(1, &["verify", "profile", "audit"], true);
}
#[test]
#[ignore = "nightly: whole-fixture proof-tool agreement and expansion coverage"]
fn charon_adler2_helpers_rem_tools_recheck_expanded_certificate() {
    recheck_helper_tools(2, &["verify", "profile", "audit"], true);
}
#[test]
#[ignore = "nightly: whole-fixture proof-tool agreement and expansion coverage"]
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
#[ignore = "nightly: whole-fixture proof-tool agreement and expansion coverage"]
fn charon_adler2_helpers_mul_audit_execute_certificate() {
    audit_mul_site("execute()");
}
#[test]
#[ignore = "nightly: whole-fixture proof-tool agreement and expansion coverage"]
fn charon_adler2_helpers_mul_audit_simp_certificate() {
    audit_mul_site("simp()");
}
#[test]
#[ignore = "nightly: whole-fixture proof-tool agreement and expansion coverage"]
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
    C0VerificationSession::new_program_prepared(
        helper_library(),
        &load_import(&p.config()).unwrap(),
    )
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
    C0VerificationSession::new_program_prepared(
        &format!("{}\n{BOUNDS}", helper_library()),
        &prepared,
    )
    .unwrap();
}

#[test]
#[ignore = "nightly: whole-fixture proof-tool agreement and expansion coverage"]
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
#[ignore = "nightly: whole-fixture proof-tool agreement and expansion coverage"]
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
#[ignore = "nightly: whole-fixture proof-tool agreement and expansion coverage"]
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
    let source = format!("{}\nimport \"iterator-bounds.click\";\n", helper_library());
    let project = click::cli::read_click_project(&p.root.join("borrow.click"), &source).unwrap();
    C0VerificationSession::new_program_prepared_project(&project, &prepared).unwrap();
}

#[test]
#[ignore = "nightly: whole-fixture proof-tool agreement and expansion coverage"]
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
#[ignore = "nightly: whole-fixture proof-tool agreement and expansion coverage"]
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
#[ignore = "nightly: whole-fixture proof-tool agreement and expansion coverage"]
fn charon_adler2_iterator_bounds_tools_expand_native_certificates() {
    expand_iterator_bounds_claims(&[
        ("adler_lane_iterator_native_step", 4),
        ("adler_lane_iterator_successor_ceilings", 2),
        ("adler_lane_iterator_native_preservation", 2),
        ("adler_lane_iterator_boundaries", 7),
    ]);
}

fn reject_empty_compute(before: &str, after: &str) {
    let p = adler2_helpers_project();
    let prepared = load_import(&p.config()).unwrap();
    let (library, computation) = HELPERS.split_once("# Empty-input boundary").unwrap();
    let changed = computation.replacen(before, after, 1);
    assert_ne!(computation, changed, "missing mutation: {before}");
    let invalid = format!("{library}# Empty-input boundary{changed}");
    // Reject this claim without reproving unrelated helper bodies for every
    // mutation; the complete fixture is checked separately below.
    let offset = invalid.find("execute_until(assignment(b, 0))").unwrap();
    let line = invalid[..offset].bytes().filter(|&b| b == b'\n').count() + 1;
    let error = click::surface::verify_program_prepared_sources_at(&invalid, &prepared, line, 2)
        .expect_err("invalid original computation contract was accepted");
    assert!(
        !error.message().contains("budget exhausted"),
        "rejection must be a proof error: {}",
        error.message()
    );
}

#[test]
fn charon_adler2_empty_compute_rejects_missing_input_lock() {
    reject_empty_compute("requires bytes_len == 0u64;", "");
}

#[test]
fn charon_adler2_empty_compute_rejects_missing_scalar_b_premise() {
    reject_empty_compute("requires self->b == 0;", "");
}

#[test]
fn charon_adler2_empty_compute_rejects_missing_ownership() {
    reject_empty_compute("owns self->a;", "");
    reject_empty_compute("owns self->b;", "");
}

#[test]
#[ignore = "nightly: complete original computation boundary proof"]
fn charon_adler2_empty_compute_proves_original_body_and_rejects_false_outputs() {
    let p = adler2_helpers_project();
    C0VerificationSession::new_program_prepared(HELPERS, &load_import(&p.config()).unwrap())
        .unwrap();
    reject_empty_compute("ensures self->a == 1;", "ensures self->a == 2;");
    reject_empty_compute("ensures self->b == 0;", "ensures self->b == 1;");
    reject_empty_compute("requires self->a == 1;", "requires self->a == 2;");
}

#[test]
#[ignore = "nightly: original computation proof-tool agreement and expansion"]
fn charon_adler2_empty_compute_tools_recheck_original_contract() {
    let p = adler2_helpers_project();
    for command in ["verify", "profile"] {
        assert_cli(&p, &[command]);
    }
    let source = fs::read_to_string(p.root.join("borrow.click")).unwrap();
    let offset = source.find("execute_until(assignment(b, 4))").unwrap();
    let line = source[..offset].bytes().filter(|&b| b == b'\n').count() + 1;
    let cursor = format!("{}:{line}:2", p.root.join("borrow.click").display());
    let audit = Command::new(env!("CARGO_BIN_EXE_click"))
        .args(["audit", "--start-at", &cursor, "--max-sites", "1"])
        .arg(p.root.join("borrow.click"))
        .output()
        .unwrap();
    assert!(
        audit.status.success(),
        "{}",
        String::from_utf8_lossy(&audit.stderr)
    );
    assert_cli(
        &p,
        &[
            "expand",
            "--claim",
            "__rust_q_I6_adler2_I4_algo_T29___rust_q_I6_adler2_I7_Adler32_I7_compute.contract",
            "--in-place",
        ],
    );
    assert_cli(&p, &["verify"]);
}

#[test]
fn charon_adler2_single_byte_compute_rejects_missing_length_and_view() {
    reject_single_byte_compute("requires bytes_len == 1u64;", "");
    reject_single_byte_compute("views bytes[0..1];", "");
}

#[test]
fn charon_adler2_single_byte_compute_rejects_empty_input() {
    reject_single_byte_compute("requires bytes_len == 1u64;", "requires bytes_len == 0u64;");
}

#[test]
#[ignore = "nightly: original single-byte computation proof and false-output rejections"]
fn charon_adler2_single_byte_compute_proves_original_body_and_rejects_false_outputs() {
    let p = compute_project(SINGLE_BYTE_COMPUTE);
    C0VerificationSession::new_program_prepared(
        &compute_proof(SINGLE_BYTE_COMPUTE),
        &load_import(&p.config()).unwrap(),
    )
    .unwrap();
    for field in ["a", "b"] {
        reject_single_byte_compute(
            &format!("ensures to_integer(self->{field}) == to_integer("),
            &format!("ensures to_integer(self->{field}) == 1 + to_integer("),
        );
    }
    reject_single_byte_compute(
        "ensures bytes[0] == old(bytes[0]);",
        "ensures bytes[0] == old(bytes[0]) + 1;",
    );
}

#[test]
#[ignore = "nightly: original single-byte computation proof-tool agreement and expansion"]
fn charon_adler2_single_byte_compute_tools_recheck_original_contract() {
    recheck_compute_tools(SINGLE_BYTE_COMPUTE, 1);
}

fn recheck_compute_tools(contract: &str, bytes: usize) {
    let p = compute_project(contract);
    for command in ["verify", "profile"] {
        assert_cli(&p, &[command]);
    }
    let source = fs::read_to_string(p.root.join("borrow.click")).unwrap();
    let site = if bytes == 1 {
        "execute_until(assignment(__rust_mir_144, 0))".to_owned()
    } else {
        format!("have __rust_mir_138_cursor == old(bytes) + {bytes}")
    };
    let offset = source.find(&site).unwrap();
    let line = source[..offset].bytes().filter(|&b| b == b'\n').count() + 1;
    let cursor = format!("{}:{line}:2", p.root.join("borrow.click").display());
    let audit = Command::new(env!("CARGO_BIN_EXE_click"))
        .args(["audit", "--start-at", &cursor, "--max-sites", "1"])
        .arg(p.root.join("borrow.click"))
        .output()
        .unwrap();
    assert!(
        audit.status.success(),
        "{}",
        String::from_utf8_lossy(&audit.stderr)
    );
    assert_cli(
        &p,
        &[
            "expand",
            "--claim",
            "__rust_q_I6_adler2_I4_algo_T29___rust_q_I6_adler2_I7_Adler32_I7_compute.contract",
            "--in-place",
        ],
    );
    assert_cli(&p, &["verify"]);
}

#[test]
fn charon_adler2_short_tail_compute_rejects_missing_length_and_view() {
    for (bytes, contract) in [(2, TWO_BYTE_COMPUTE), (3, THREE_BYTE_COMPUTE)] {
        reject_compute(contract, &format!("requires bytes_len == {bytes}u64;"), "");
        reject_compute(contract, &format!("views bytes[0..{bytes}];"), "");
    }
}

#[test]
fn charon_adler2_short_tail_compute_rejects_wrong_extent_and_constructor() {
    for (bytes, contract) in [(2, TWO_BYTE_COMPUTE), (3, THREE_BYTE_COMPUTE)] {
        reject_compute(
            contract,
            &format!("requires bytes_len == {bytes}u64;"),
            "requires bytes_len == 4u64;",
        );
        reject_compute(contract, "requires self->a == 1;", "requires self->a == 2;");
    }
}

fn check_short_tail_compute(contract: &str, bytes: usize) {
    let p = compute_project(contract);
    C0VerificationSession::new_program_prepared(
        &compute_proof(contract),
        &load_import(&p.config()).unwrap(),
    )
    .unwrap();
    for field in ["a", "b"] {
        reject_compute(
            contract,
            &format!("ensures to_integer(self->{field}) == to_integer("),
            &format!("ensures to_integer(self->{field}) == 1 + to_integer("),
        );
    }
    for index in 0..bytes {
        reject_compute(
            contract,
            &format!("ensures bytes[{index}] == old(bytes[{index}]);"),
            &format!("ensures bytes[{index}] == old(bytes[{index}]) + 1;"),
        );
    }
    // Swapping input bytes leaves A unchanged but changes the weighted B sum.
    // Only mutate the promised B result; the proof and original Rust stay fixed.
    let b_result = contract
        .lines()
        .find(|line| line.contains("ensures to_integer(self->b)"))
        .unwrap();
    let swapped = b_result
        .replace("bytes[0]", "@first@")
        .replace("bytes[1]", "bytes[0]")
        .replace("@first@", "bytes[1]");
    reject_compute(contract, b_result, &swapped);
    // The second and third actual reads cannot repeat the preceding byte.
    for index in 1..bytes {
        reject_compute(
            contract,
            &format!("have byte == old(bytes[{index}])"),
            &format!("have byte == old(bytes[{}])", index - 1),
        );
    }
}

#[test]
#[ignore = "nightly: original two-byte computation proof and false-result/read rejections"]
fn charon_adler2_two_byte_compute_proves_original_body_and_rejects_false_outputs() {
    check_short_tail_compute(TWO_BYTE_COMPUTE, 2);
}

#[test]
#[ignore = "nightly: original three-byte computation proof and false-result/read rejections"]
fn charon_adler2_three_byte_compute_proves_original_body_and_rejects_false_outputs() {
    check_short_tail_compute(THREE_BYTE_COMPUTE, 3);
}

#[test]
#[ignore = "nightly: original two-byte computation proof-tool agreement and expansion"]
fn charon_adler2_two_byte_compute_tools_recheck_original_contract() {
    recheck_compute_tools(TWO_BYTE_COMPUTE, 2);
}

#[test]
#[ignore = "nightly: original three-byte computation proof-tool agreement and expansion"]
fn charon_adler2_three_byte_compute_tools_recheck_original_contract() {
    recheck_compute_tools(THREE_BYTE_COMPUTE, 3);
}
