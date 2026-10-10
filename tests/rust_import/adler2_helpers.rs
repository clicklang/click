use super::*;
use sha2::{Digest, Sha256};

const HELPERS: &str = include_str!("../../design/charon-trial/adler2/helpers.click");
const SINGLE_BYTE_COMPUTE: &str =
    include_str!("../../design/charon-trial/adler2/single-byte-compute.click");

const TWO_BYTE_COMPUTE: &str =
    include_str!("../../design/charon-trial/adler2/two-byte-compute.click");
const THREE_BYTE_COMPUTE: &str =
    include_str!("../../design/charon-trial/adler2/three-byte-compute.click");
const FOUR_BYTE_COMPUTE: &str =
    include_str!("../../design/charon-trial/adler2/four-byte-compute.click");
const FOUR_BYTE_SPEC: &str = include_str!("../../design/charon-trial/adler2/four-byte-spec.click");
const SMALL_PARTITION: &str = include_str!("../../design/charon-trial/adler2/partition.click");
const TAIL_BOUNDS: &str = include_str!("../../design/charon-trial/adler2/tail-bounds.click");
const BOUNDED_COUNT: &str = include_str!("../../design/charon-trial/adler2/bounded-count.click");
const COUNT_BRIDGE: &str = include_str!("../../design/charon-trial/adler2/count-bridge.click");
const SMALL_BATCH_COMPUTE: &str =
    include_str!("../../design/charon-trial/adler2/small-batch-compute.click");

const GENERAL_COMPUTE: &str =
    include_str!("../../design/charon-trial/adler2/general-compute.click");

fn compute_proof(contract: &str) -> String {
    let computation = HELPERS.split_once("# Empty-input boundary").unwrap().1;
    let getters = &computation[computation.find("\nuint32 ").unwrap()..];
    // Function-contract imports are not admitted yet. Assemble one verification
    // unit from the canonical helper/getter bodies and this alternative compute
    // contract, rather than duplicating or assuming their interfaces.
    let lemmas = if contract.contains("adler_recombine_difference(") {
        RECOMBINATION
    } else {
        ""
    };
    let iterator_lemmas = if contract.contains("adler_lane_iterator_") {
        flat_iterator_bounds()
    } else {
        String::new()
    };
    let partition = if contract.contains("adler_small_tail_metadata(") {
        SMALL_PARTITION
    } else {
        ""
    };
    let general_partition = if contract.contains("adler_general_bounded_tail_metadata(") {
        GENERAL_PARTITION
    } else {
        ""
    };
    let tail_bounds = if contract.contains("adler_tail_iterator_step(") {
        TAIL_BOUNDS
    } else {
        ""
    };
    let count_bridge = if contract.contains("adler_count_") {
        COUNT_BRIDGE
    } else {
        ""
    };
    let bounded_count = if contract.contains("adler_bounded_count") {
        BOUNDED_COUNT
    } else {
        ""
    };
    let common_spec = if contract.contains("adler_spec_one(")
        || contract.contains("adler_four_byte_result_spec(")
    {
        COMMON_ADLER_SPEC
    } else {
        ""
    };
    let four_byte_spec = if contract.contains("adler_four_byte_result_spec(") {
        FOUR_BYTE_SPEC
    } else {
        ""
    };
    format!(
        "{}\n{common_spec}\n{four_byte_spec}\n{lemmas}\n{iterator_lemmas}\n{partition}\n{general_partition}\n{tail_bounds}\n{count_bridge}\n{bounded_count}\n{contract}\n{getters}",
        helper_library()
    )
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
    assert_eq!(blocks.len(), 6);
    assert!(index < 4);
    format!("{}\n\n{}\n\n{}", blocks[0], blocks[1], blocks[index + 2])
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
#[ignore = "nightly: 4s in the parallel gate"]
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
#[ignore = "nightly: 4s in the parallel gate"]
fn charon_adler2_helpers_from_rejects_false_byte_bounds_lane_0() {
    reject_helper_byte_bounds(0);
}

#[test]
#[ignore = "nightly: 4s in the parallel gate"]
fn charon_adler2_helpers_from_rejects_false_byte_bounds_lane_1() {
    reject_helper_byte_bounds(1);
}

#[test]
#[ignore = "nightly: 4s in the parallel gate"]
fn charon_adler2_helpers_from_rejects_false_byte_bounds_lane_2() {
    reject_helper_byte_bounds(2);
}

#[test]
#[ignore = "nightly: 4s in the parallel gate"]
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
#[ignore = "nightly: 7s in the parallel gate; lane 2 reaches the same code"]
fn charon_adler2_helpers_add_rejects_false_observations_lane_0() {
    reject_helper_add_observations(0);
}

#[test]
#[ignore = "nightly: 7s in the parallel gate; lane 2 reaches the same code"]
fn charon_adler2_helpers_add_rejects_false_observations_lane_1() {
    reject_helper_add_observations(1);
}

#[test]
fn charon_adler2_helpers_add_rejects_false_observations_lane_2() {
    reject_helper_add_observations(2);
}

#[test]
#[ignore = "nightly: 7s in the parallel gate; lane 2 reaches the same code"]
fn charon_adler2_helpers_add_rejects_false_observations_lane_3() {
    reject_helper_add_observations(3);
}

#[test]
#[ignore = "nightly: 11s in the parallel gate"]
fn charon_adler2_helpers_rem_preservation_rejects_false_lane_0() {
    reject_helper_reduction_preservation(0);
}

#[test]
#[ignore = "nightly: 11s in the parallel gate"]
fn charon_adler2_helpers_rem_preservation_rejects_false_lane_1() {
    reject_helper_reduction_preservation(1);
}

#[test]
#[ignore = "nightly: 11s in the parallel gate"]
fn charon_adler2_helpers_rem_preservation_rejects_false_lane_2() {
    reject_helper_reduction_preservation(2);
}

#[test]
#[ignore = "nightly: 11s in the parallel gate"]
fn charon_adler2_helpers_rem_preservation_rejects_false_lane_3() {
    reject_helper_reduction_preservation(3);
}

#[test]
#[ignore = "nightly: unchanged reduction rejects false mathematical observations"]
fn charon_adler2_helpers_rem_rejects_false_integer_residue_observations() {
    let exact = "ensures to_integer(self->_0[3]) == truncating_remainder(to_integer(old(self->_0[3])), to_integer(quotient));";
    reject_helper_contracts(
        2,
        &[
            (
                exact,
                &exact.replace("old(self->_0[3])", "old(self->_0[2])"),
            ),
            (exact, &exact.replace("));", ")) + 1;")),
        ],
    );
}

fn reject_helper_reduction_preservation(lane: usize) {
    let postcondition = format!(
        "ensures old(self->_0[{lane}]) < quotient implies self->_0[{lane}] == old(self->_0[{lane}])"
    );
    reject_helper_contracts(
        2,
        &[
            (
                &postcondition,
                &postcondition.replace(" < quotient", " <= quotient"),
            ),
            (&postcondition, &format!("{postcondition} + 1u32")),
            (
                &postcondition,
                &postcondition.replace(
                    &format!("== old(self->_0[{lane}])"),
                    &format!("== old(self->_0[{}])", (lane + 1) % 4),
                ),
            ),
        ],
    );
}

#[test]
#[ignore = "nightly: 3s in the parallel gate"]
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
#[ignore = "nightly: 3s in the parallel gate"]
fn charon_adler2_helpers_rem_rejects_false_reduction_bounds_lane_0() {
    reject_helper_reduction_bounds(0);
}

#[test]
#[ignore = "nightly: 3s in the parallel gate"]
fn charon_adler2_helpers_rem_rejects_false_reduction_bounds_lane_1() {
    reject_helper_reduction_bounds(1);
}

#[test]
#[ignore = "nightly: 3s in the parallel gate"]
fn charon_adler2_helpers_rem_rejects_false_reduction_bounds_lane_2() {
    reject_helper_reduction_bounds(2);
}

#[test]
#[ignore = "nightly: 3s in the parallel gate"]
fn charon_adler2_helpers_rem_rejects_false_reduction_bounds_lane_3() {
    reject_helper_reduction_bounds(3);
}

#[test]
#[ignore = "nightly: 5s in the parallel gate"]
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
#[ignore = "nightly: 8s in the parallel gate"]
fn charon_adler2_helpers_mul_rejects_false_observations_lane_0() {
    reject_helper_product_observations(0);
}

#[test]
#[ignore = "nightly: 8s in the parallel gate"]
fn charon_adler2_helpers_mul_rejects_false_observations_lane_1() {
    reject_helper_product_observations(1);
}

#[test]
#[ignore = "nightly: 8s in the parallel gate"]
fn charon_adler2_helpers_mul_rejects_false_observations_lane_2() {
    reject_helper_product_observations(2);
}

#[test]
#[ignore = "nightly: 8s in the parallel gate"]
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
        stdout.contains(
            "SUMMARY: 1 sites passed; 0 site failures; 0 claim failures; 0 session failures;"
        ),
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
const RECOMBINATION: &str = include_str!("../../design/charon-trial/adler2/recombination.click");

#[test]
#[ignore = "nightly: 4s in the parallel gate"]
fn charon_adler2_recombination_bounds_verify_with_original_helpers() {
    let p = adler2_helpers_project();
    let prepared = load_import(&p.config()).unwrap();
    C0VerificationSession::new_program_prepared(
        &format!("{}\n{RECOMBINATION}", helper_library()),
        &prepared,
    )
    .unwrap();
}

#[test]
fn charon_adler2_recombination_bounds_reject_underflow_overflow_and_false_weights() {
    use click::surface::verify_click_theorems;
    verify_click_theorems(RECOMBINATION).unwrap();
    for (before, after) in [
        ("requires a < 65521u32;", ""),
        ("requires a < 65521u32;", "requires a <= 65522u32;"),
        ("requires to_integer(b) <= 262080;", ""),
        ("<= 327601", "<= 327600"),
        ("<= 393122", "<= 393121"),
        ("<= 458643", "<= 458642"),
        (
            "+ (65521 - to_integer(a)) * 2",
            "+ (65521 - to_integer(a)) * 3",
        ),
        (
            "+ (65521 - to_integer(a)) * 3",
            "+ (65521 - to_integer(a)) * 2",
        ),
    ] {
        let invalid = RECOMBINATION.replace(before, after);
        assert_ne!(invalid, RECOMBINATION, "missing mutation: {before}");
        assert!(
            verify_click_theorems(&invalid).is_err(),
            "accepted {before} -> {after}"
        );
    }
}

#[test]
#[ignore = "nightly: Adler recombination proof-tool agreement and expansion"]
fn charon_adler2_recombination_bounds_tools_recheck_certificates() {
    let p = adler2_helpers_project();
    let path = p.root.join("recombination.click");
    fs::write(&path, RECOMBINATION).unwrap();
    let check = |args: &[&str]| {
        let result = Command::new(env!("CARGO_BIN_EXE_click"))
            .args(args)
            .arg(&path)
            .output()
            .unwrap();
        assert!(
            result.status.success(),
            "{args:?}: {}\n{}",
            String::from_utf8_lossy(&result.stdout),
            String::from_utf8_lossy(&result.stderr)
        );
    };
    for command in ["verify", "profile", "audit"] {
        check(&[command]);
    }
    for name in ["difference", "lane_1", "lane_2", "lane_3"] {
        let claim = format!("adler_recombine_{name}.ensures_0");
        check(&["expand", "--claim", &claim, "--in-place"]);
    }
    check(&["verify"]);
}

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
#[ignore = "nightly: 4s in the parallel gate"]
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
#[ignore = "nightly: 4s in the parallel gate"]
fn charon_adler2_iterator_bounds_prove_derived_index_and_native_preservation() {
    use click::surface::verify_click_theorems;
    let source = flat_iterator_bounds();
    assert_eq!(verify_click_theorems(&source).unwrap().len(), 64);
    for (before, after) in [
        ("requires total <= 22208;", "requires total <= 22212;"),
        ("requires to_integer(a) <= 65520;", ""),
        ("requires to_integer(b) <= 65520;", ""),
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
    // Mutate only the iterator-facing contracts, leaving their arithmetic
    // dependencies checked and unchanged.
    let (dependencies, contracts) = source
        .split_once("theorem adler_lane_iterator_add_contracts")
        .unwrap();
    for (before, after) in [
        (
            "ensures to_integer(a) + to_integer(byte) <= 4294967295",
            "ensures to_integer(a) + to_integer(byte) <= 1481279",
        ),
        (
            "ensures to_integer(b) + to_integer(a + byte) <= 4294967295",
            "ensures to_integer(b) + to_integer(a + byte) <= 4294690199",
        ),
    ] {
        let changed = contracts.replacen(before, after, 1);
        assert_ne!(contracts, changed, "missing mutation: {before}");
        let invalid = format!("{dependencies}theorem adler_lane_iterator_add_contracts{changed}");
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
#[ignore = "nightly: 4s in the parallel gate"]
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
        64
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
        ("adler_lane_iterator_reduced_initial", 2),
        ("adler_lane_iterator_add_contracts", 2),
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
#[ignore = "nightly: original computation mutation, 16s locally; exceeded 30s in CI"]
fn charon_adler2_empty_compute_rejects_missing_input_lock() {
    reject_empty_compute("requires bytes_len == 0u64;", "");
}

#[test]
#[ignore = "nightly: original computation mutation, 12s locally"]
fn charon_adler2_empty_compute_rejects_missing_scalar_b_premise() {
    reject_empty_compute("requires self->b == 0;", "");
}

#[test]
#[ignore = "nightly: original computation mutation, 21s locally; exceeded 30s in CI"]
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
#[ignore = "nightly: 5s in the parallel gate"]
fn charon_adler2_single_byte_compute_rejects_missing_length_and_view() {
    reject_single_byte_compute("requires bytes_len == 1u64;", "");
    reject_single_byte_compute("views bytes[0..1];", "");
}

#[test]
#[ignore = "nightly: 4s in the parallel gate"]
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
    for (field, specification) in [
        ("a", "adler_spec_a(bytes, 1, 1)"),
        ("b", "adler_spec_b(bytes, 1, 1, 0)"),
    ] {
        reject_single_byte_compute(
            &format!("ensures to_integer(self->{field}) == old({specification});"),
            &format!("ensures to_integer(self->{field}) == old({specification}) + 1;"),
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
    let site = if bytes == 4 {
        "have (int32)(uint32)__rust_mir_115_remaining == 3".to_owned()
    } else if bytes == 1 {
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
#[ignore = "nightly: 8s in the parallel gate"]
fn charon_adler2_short_tail_compute_rejects_missing_length_and_view() {
    for (bytes, contract) in [(2, TWO_BYTE_COMPUTE), (3, THREE_BYTE_COMPUTE)] {
        reject_compute(contract, &format!("requires bytes_len == {bytes}u64;"), "");
        reject_compute(contract, &format!("views bytes[0..{bytes}];"), "");
    }
}

#[test]
#[ignore = "nightly: 6s in the parallel gate"]
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

#[test]
#[ignore = "nightly: 3s in the parallel gate"]
fn charon_adler2_four_byte_compute_rejects_false_stored_iterator_observations() {
    reject_compute(
        FOUR_BYTE_COMPUTE,
        "have (int32)(uint32)__rust_mir_62_remaining == 4 by",
        "have (int32)(uint32)__rust_mir_62_remaining == 8 by",
    );
    reject_compute(
        FOUR_BYTE_COMPUTE,
        "have adler_lane_vectors_consumed(4, (int32)(uint32)__rust_mir_62_remaining) == 0 by",
        "have adler_lane_vectors_consumed(4, (int32)(uint32)__rust_mir_62_remaining) == 1 by",
    );
}

#[test]
#[ignore = "nightly: 3s in the parallel gate"]
fn charon_adler2_four_byte_compute_rejects_missing_extent_view_and_constructor() {
    for (before, after) in [
        ("requires bytes_len == 4u64;", ""),
        ("views bytes[0..4];", "views bytes[0..3];"),
        ("requires self->a == 1;", "requires self->a == 2;"),
    ] {
        reject_compute(FOUR_BYTE_COMPUTE, before, after);
    }
}

#[test]
#[ignore = "nightly: original four-byte vector computation and false-result/read rejections"]
fn charon_adler2_four_byte_compute_proves_original_body_and_rejects_false_outputs() {
    let p = compute_project(FOUR_BYTE_COMPUTE);
    C0VerificationSession::new_program_prepared(
        &compute_proof(FOUR_BYTE_COMPUTE),
        &load_import(&p.config()).unwrap(),
    )
    .unwrap();
    for field in ["a", "b"] {
        reject_compute(
            FOUR_BYTE_COMPUTE,
            &format!("ensures to_integer(self->{field}) == to_integer("),
            &format!("ensures to_integer(self->{field}) == 1 + to_integer("),
        );
        let specification = if field == "a" {
            "adler_spec_a(bytes, 4, 1)"
        } else {
            "adler_spec_b(bytes, 4, 1, 0)"
        };
        reject_compute(
            FOUR_BYTE_COMPUTE,
            &format!("ensures to_integer(self->{field}) == old({specification});"),
            &format!("ensures to_integer(self->{field}) == old({specification}) + 1;"),
        );
    }
    reject_compute(
        FOUR_BYTE_COMPUTE,
        "ensures bytes[3] == old(bytes[3]);",
        "ensures bytes[3] == old(bytes[3]) + 1;",
    );
    let b_result = FOUR_BYTE_COMPUTE
        .lines()
        .find(|line| line.contains("ensures to_integer(self->b)"))
        .unwrap();
    let swapped = b_result
        .replace("bytes[2]", "@third@")
        .replace("bytes[3]", "bytes[2]")
        .replace("@third@", "bytes[3]");
    reject_compute(FOUR_BYTE_COMPUTE, b_result, &swapped);
    reject_compute(
        FOUR_BYTE_COMPUTE,
        "have av == old((uint32)bytes[3])",
        "have av == old((uint32)bytes[2])",
    );
}

#[test]
#[ignore = "nightly: original vector-step preservation and false bound/state rejections"]
fn charon_adler2_four_byte_compute_rejects_false_native_step_bounds() {
    // The complete positive caller is checked by the existing computation
    // regression. These mutations target the bounds after both original calls,
    // independently of the final checksum expressions.
    let post_step = FOUR_BYTE_COMPUTE
        .split_once("# Both actual helper results satisfy the ceiling at next()'s new state.")
        .unwrap()
        .1;
    for field in ["a", "b"] {
        for lane in [0, 3] {
            let bound = format!(
                "have to_integer({field}_vec._0[{lane}]) <= adler_lane_{field}_ceiling(adler_lane_vectors_consumed(4, (int32)(uint32)__rust_mir_62_remaining)) by"
            );
            let changed = post_step.replacen(
                &bound,
                &format!("have to_integer({field}_vec._0[{lane}]) <= 0 by"),
                1,
            );
            assert_ne!(post_step, changed);
            reject_compute(FOUR_BYTE_COMPUTE, post_step, &changed);
        }
    }
    reject_compute(
        FOUR_BYTE_COMPUTE,
        "have to_integer(b_vec._0[3]) + to_integer(a_vec._0[3]) <= 4294967295 by",
        "have to_integer(b_vec._0[3]) + to_integer(a_vec._0[3]) <= 254 by",
    );
    reject_compute(
        FOUR_BYTE_COMPUTE,
        "# Both actual helper results satisfy the ceiling at next()'s new state.\n   have (int32)(uint32)__rust_mir_62_remaining == at(lane_head, (int32)(uint32)__rust_mir_62_remaining) - 4 by",
        "# Both actual helper results satisfy the ceiling at next()'s new state.\n   have (int32)(uint32)__rust_mir_62_remaining == at(lane_head, (int32)(uint32)__rust_mir_62_remaining) by",
    );
}

#[test]
#[ignore = "nightly: symbolic original vector-loop invariant and ranking rejections"]
fn charon_adler2_four_byte_compute_rejects_false_vector_loop_induction() {
    for (before, after) in [
        (
            "decreases __rust_mir_62_remaining;",
            "decreases 4 - __rust_mir_62_remaining;",
        ),
        (
            "invariant (int32)(uint32)__rust_mir_62_remaining % 4 == 0;",
            "invariant (int32)(uint32)__rust_mir_62_remaining % 4 == 1;",
        ),
        (
            "invariant (int32)(uint32)__rust_mir_62_remaining == 0 implies a_vec._0[3] == old((uint32)bytes[3]);",
            "invariant (int32)(uint32)__rust_mir_62_remaining == 0 implies a_vec._0[3] == old((uint32)bytes[2]);",
        ),
        (
            "invariant b_vec._0[3] <= 255u32;",
            "invariant b_vec._0[3] <= 254u32;",
        ),
    ] {
        reject_compute(FOUR_BYTE_COMPUTE, before, after);
    }
}

#[test]
#[ignore = "nightly: original four-byte computation proof-tool agreement and expansion"]
fn charon_adler2_four_byte_compute_tools_recheck_original_contract() {
    recheck_compute_tools(FOUR_BYTE_COMPUTE, 4);
}

#[test]
#[ignore = "nightly: checksum contract mutation checks"]
fn charon_adler2_small_batch_compute_rejects_missing_view_and_full_outer_batch() {
    reject_compute(SMALL_BATCH_COMPUTE, " views bytes[0..bytes_len];", "");
    reject_compute(
        SMALL_BATCH_COMPUTE,
        " requires bytes_len <= 22207u64;\n requires bytes_len < 22208u64;",
        " requires bytes_len <= 22208u64;",
    );
}

#[test]
#[ignore = "nightly: original 0..22207-byte vector and tail computation from canonical states"]
fn charon_adler2_small_batch_compute_proves_original_body() {
    let p = compute_project(SMALL_BATCH_COMPUTE);
    C0VerificationSession::new_program_prepared(
        &compute_proof(SMALL_BATCH_COMPUTE),
        &load_import(&p.config()).unwrap(),
    )
    .unwrap();
}

#[test]
#[ignore = "nightly: checksum contract mutation checks"]
fn charon_adler2_small_batch_compute_requires_canonical_a() {
    reject_compute(
        SMALL_BATCH_COMPUTE,
        " requires (uint32)self->a <= 65520u32;",
        "",
    );
}

#[test]
#[ignore = "nightly: checksum contract mutation checks"]
fn charon_adler2_small_batch_compute_requires_canonical_b() {
    reject_compute(
        SMALL_BATCH_COMPUTE,
        " requires (uint32)self->b <= 65520u32;",
        "",
    );
}

#[test]
#[ignore = "nightly: arbitrary small-batch induction and final-store rejection checks"]
fn charon_adler2_small_batch_compute_rejects_false_induction_and_final_bounds() {
    for (before, after) in [
        (
            "have __rust_mir_62_remaining == bytes_len - bytes_len % 4u64 by { simp(); }",
            "have __rust_mir_62_remaining == (bytes_len - bytes_len % 4u64) + 4u64 by { assumption(); }",
        ),
        ("ensures self->a < 65521;", "ensures self->a < 1;"),
        ("ensures self->b < 65521;", "ensures self->b < 1;"),
    ] {
        reject_compute(SMALL_BATCH_COMPUTE, before, after);
    }
}

#[test]
#[ignore = "nightly: original scalar-tail cursor and ranking rejections"]
fn charon_adler2_small_batch_compute_rejects_false_tail_state_and_ranking() {
    for (before, after) in [
        (
            "have __rust_mir_138_cursor == remainder by { normalize(); }",
            "have __rust_mir_138_cursor == remainder + 1 by { assumption(); }",
        ),
        (
            "have __rust_mir_138_remaining < at(tail_head, __rust_mir_138_remaining) by { arithmetic() using { __rust_mir_138_remaining == at(tail_head, __rust_mir_138_remaining) - 1u64; 1u64 <= at(tail_head, __rust_mir_138_remaining); } }",
            "have at(tail_head, __rust_mir_138_remaining) < __rust_mir_138_remaining by { assumption(); }",
        ),
    ] {
        reject_compute(SMALL_BATCH_COMPUTE, before, after);
    }
}

#[test]
#[ignore = "nightly: arbitrary small-batch proof-tool agreement and expansion"]
fn charon_adler2_small_batch_compute_tools_recheck_original_contract() {
    let p = compute_project(SMALL_BATCH_COMPUTE);
    let claim = "__rust_q_I6_adler2_I4_algo_T29___rust_q_I6_adler2_I7_Adler32_I7_compute.contract";
    for command in ["verify", "profile"] {
        assert_cli(&p, &[command]);
    }
    // Helpers and arithmetic lemmas have their own audits. Selecting the
    // complete computation claim keeps this long nightly check within one
    // bounded audit run and still expands every smart site of the body.
    assert_cli(&p, &["audit", "--claim", claim]);
    assert_cli(&p, &["expand", "--claim", claim, "--in-place"]);
    assert_cli(&p, &["verify"]);
}

#[test]
#[ignore = "nightly: checksum lemma expansion and mutation checks"]
fn charon_adler2_small_partition_verifies_and_expands() {
    click::surface::verify_c0_sources(SMALL_PARTITION, &[]).unwrap();
    for claim in [
        "adler_small_prefix_divisible.ensures_0",
        "adler_small_tail_metadata.ensures_0",
        "adler_signed_small_prefix.ensures_0",
        "adler_small_tail_indices.ensures_2",
    ] {
        let expanded =
            click::surface::expand_c0_claim_source_by_label(SMALL_PARTITION, &[], claim).unwrap();
        click::surface::verify_c0_sources(&expanded, &[]).unwrap();
    }
}

#[test]
#[ignore = "nightly: checksum lemma expansion and mutation checks"]
fn charon_adler2_scalar_tail_bounds_verify_expand_and_reject_false_updates() {
    click::surface::verify_c0_sources(TAIL_BOUNDS, &[]).unwrap();
    for claim in [
        "adler_tail_iterator_step.ensures_0",
        "adler_tail_iterator_step.ensures_3",
        "adler_tail_remaining_progress.ensures_0",
    ] {
        let expanded =
            click::surface::expand_c0_claim_source_by_label(TAIL_BOUNDS, &[], claim).unwrap();
        click::surface::verify_c0_sources(&expanded, &[]).unwrap();
    }
    for (before, after) in [
        ("ensures a + byte <= 328365", "ensures a + byte <= 328364"),
        (
            "ensures b + a + byte <= 2492061",
            "ensures b + a + byte <= 2492060",
        ),
        (
            "ensures adler_tail_consumed(total, remaining - 1) == adler_tail_consumed(total, remaining) + 1",
            "ensures adler_tail_consumed(total, remaining - 1) == adler_tail_consumed(total, remaining) + 2",
        ),
    ] {
        let invalid = TAIL_BOUNDS.replacen(before, after, 1);
        assert_ne!(invalid, TAIL_BOUNDS);
        assert!(click::surface::verify_c0_sources(&invalid, &[]).is_err());
    }
}

#[test]
#[ignore = "nightly: checksum contract mutation checks"]
fn charon_adler2_small_partition_rejects_false_metadata() {
    for (before, after) in [
        (
            "adler_vector_prefix(n) <= 22204 by",
            "adler_vector_prefix(n) <= 22203 by",
        ),
        (
            "ensures truncating_remainder(n, 4) <= 3",
            "ensures truncating_remainder(n, 4) <= 2",
        ),
        (
            "ensures (int32)(uint32)(n - n % 4u64) % 4 == 0",
            "ensures (int32)(uint32)(n - n % 4u64) % 4 == 1",
        ),
        (
            "ensures n - (n - n % 4u64) == n % 4u64",
            "ensures n - (n - n % 4u64) == n % 4u64 + 1u64",
        ),
        ("ensures n % 4u64 <= 3u64", "ensures n % 4u64 <= 2u64"),
        ("requires n <= 22207u64;", "requires n <= 22208u64;"),
    ] {
        let invalid = SMALL_PARTITION.replace(before, after);
        assert_ne!(invalid, SMALL_PARTITION, "{before}");
        assert!(
            click::surface::verify_c0_sources(&invalid, &[]).is_err(),
            "{before}"
        );
    }
}

// The original scalar tail needs safe A/B updates and actual remaining progress.
#[test]
fn charon_adler2_scalar_tail_bounds_verify() {
    click::surface::verify_c0_sources(TAIL_BOUNDS, &[]).unwrap();
}

// Full-width lengths must agree with four-byte prefixes and short-tail indices.
#[test]
fn charon_adler2_small_partition_verifies() {
    click::surface::verify_c0_sources(SMALL_PARTITION, &[]).unwrap();
}

const COMMON_ADLER_SPEC: &str = include_str!("../../design/adler32-spec.click");

// Checks the common mathematical target independently of an imported body:
// one/four-byte weighted order, canonical residues, empty seeds and packed bounds.
#[test]
fn adler_common_spec_recurrences_and_bounds_verify() {
    click::surface::verify_c0_sources(COMMON_ADLER_SPEC, &[]).unwrap();
}

#[test]
fn adler_four_byte_recombination_matches_the_common_spec() {
    let source = format!("{COMMON_ADLER_SPEC}\n{FOUR_BYTE_SPEC}");
    for theorem in [
        "adler_four_byte_native_result",
        "adler_four_byte_result_spec",
    ] {
        let offset = source.find(&format!("theorem {theorem}(")).unwrap();
        let body = offset + source[offset..].find(" by {\n").unwrap() + " by {\n".len();
        let line = source[..body].bytes().filter(|&b| b == b'\n').count() + 1;
        click::surface::verify_c0_sources_at(&source, &[], line, 2).unwrap();
    }
}

#[test]
fn adler_four_byte_recombination_rejects_reversed_byte_weights() {
    let source = format!("{COMMON_ADLER_SPEC}\n{FOUR_BYTE_SPEC}");
    let statement = FOUR_BYTE_SPEC
        .lines()
        .find(|line| line.starts_with("     and to_integer("))
        .unwrap();
    let incorrect = statement
        .replace("3 * to_integer((int32)x1)", "2 * to_integer((int32)x1)")
        .replace("2 * to_integer((int32)x2)", "3 * to_integer((int32)x2)");
    assert_ne!(incorrect, statement);
    let source = source.replacen(statement, &incorrect, 1);
    let offset = source
        .find("theorem adler_four_byte_native_result(")
        .unwrap();
    let body = offset + source[offset..].find(" by {\n").unwrap() + " by {\n".len();
    let line = source[..body].bytes().filter(|&b| b == b'\n').count() + 1;
    let error = click::surface::verify_c0_sources_at(&source, &[], line, 2)
        .expect_err("reversed middle-byte weights were accepted");
    assert!(
        !error.message().contains("budget exhausted"),
        "{}",
        error.message()
    );
}

#[test]
fn adler_four_byte_recombination_rejects_off_by_one_residues() {
    for prefix in [" ensures to_integer(", "     and to_integer("] {
        let statement = FOUR_BYTE_SPEC
            .lines()
            .find(|line| line.starts_with(prefix))
            .unwrap();
        let incorrect = statement.replacen(
            " == truncating_remainder(",
            " == 1 + truncating_remainder(",
            1,
        );
        assert_ne!(incorrect, statement);
        let source =
            format!("{COMMON_ADLER_SPEC}\n{FOUR_BYTE_SPEC}").replacen(statement, &incorrect, 1);
        let offset = source
            .find("theorem adler_four_byte_native_result(")
            .unwrap();
        let body = offset + source[offset..].find(" by {\n").unwrap() + " by {\n".len();
        let line = source[..body].bytes().filter(|&b| b == b'\n').count() + 1;
        let error = click::surface::verify_c0_sources_at(&source, &[], line, 2)
            .expect_err("an off-by-one native residue was accepted");
        assert!(
            !error.message().contains("budget exhausted"),
            "{}",
            error.message()
        );
    }
}

#[test]
#[ignore = "nightly: common checksum specification expansion and mutation checks"]
fn adler_common_spec_expands_and_rejects_false_results() {
    for claim in [
        "adler_byte_observation_same_index.ensures_0",
        "adler_sum_append_four.ensures_0",
        "adler_weighted_append_four.ensures_0",
        "adler_weight_shift.ensures_0",
        "adler_weighted_prefix_step.ensures_0",
        "adler_sum_nonnegative.ensures_0",
        "adler_weighted_nonnegative.ensures_0",
        "adler_residue_unique.ensures_0",
        "adler_residue_add.ensures_0",
        "adler_residue_congruent.ensures_0",
        "adler_spec_a_canonical.ensures_0",
        "adler_spec_b_canonical.ensures_0",
        "adler_spec_packing_bounds.ensures_0",
        "adler_spec_empty.ensures_0",
        "adler_spec_empty.ensures_1",
        "adler_spec_one.ensures_0",
        "adler_spec_one.ensures_1",
        "adler_spec_four.ensures_0",
        "adler_spec_four.ensures_1",
        "adler_byte_offset_association.ensures_0",
        "adler_sum_concat.ensures_0",
        "adler_weighted_concat.ensures_0",
        "adler_residue_add_left.ensures_0",
        "adler_spec_a_concat.ensures_0",
        "adler_sum_upper.ensures_0",
        "adler_seed_polynomial.ensures_0",
        "adler_residue_seed_update.ensures_0",
        "adler_concat_index_partition.ensures_0",
        "adler_weighted_prefix_concat.ensures_0",
        "adler_join_seed_polynomial.ensures_0",
        "adler_spec_b_concat.ensures_0",
        "adler_spec_checksum_concat.ensures_0",
    ] {
        let expanded =
            click::surface::expand_c0_claim_source_by_label(COMMON_ADLER_SPEC, &[], claim)
                .unwrap_or_else(|error| panic!("{claim}: {}", error.message()));
        click::surface::verify_c0_sources(&expanded, &[]).unwrap();
    }
    for (before, after) in [
        (
            "adler_weighted_sum(bytes, n - 1, n - 1) + adler_byte_sum(bytes, n) by",
            "adler_weighted_sum(bytes, n - 1, n - 1) + 2 * adler_byte_sum(bytes, n) by",
        ),
        (
            "+ 3 * to_integer((int32)bytes[n + 1]) + 2 * to_integer((int32)bytes[n + 2])",
            "+ 2 * to_integer((int32)bytes[n + 1]) + 3 * to_integer((int32)bytes[n + 2])",
        ),
        (
            "requires n == m + 65521 * q;",
            "requires n == m + 65520 * q;",
        ),
        ("requires n <= 2147483643;", "requires n <= 2147483644;"),
        ("<= 4293984240 by", "<= 4293984239 by"),
        (
            "ensures adler_byte_sum(bytes, prefix + suffix) == adler_byte_sum(bytes, prefix) + adler_byte_sum(bytes + prefix, suffix) by",
            "ensures adler_byte_sum(bytes, prefix + suffix) == adler_byte_sum(bytes, prefix) + adler_byte_sum(bytes + prefix, suffix) + 1 by",
        ),
        (
            "ensures adler_spec_b(bytes, prefix + suffix, a0, b0) == adler_spec_b(bytes + prefix, suffix, adler_spec_a(bytes, prefix, a0), adler_spec_b(bytes, prefix, a0, b0)) by",
            "ensures adler_spec_b(bytes, prefix + suffix, a0, b0) == adler_spec_b(bytes + prefix, suffix, adler_spec_a(bytes, prefix, a0), adler_spec_b(bytes, prefix, a0, b0) + 1) by",
        ),
        (
            "ensures adler_spec_checksum(bytes, prefix + suffix, a0, b0) == adler_spec_checksum(bytes + prefix, suffix, adler_spec_a(bytes, prefix, a0), adler_spec_b(bytes, prefix, a0, b0)) by",
            "ensures adler_spec_checksum(bytes, prefix + suffix, a0, b0) == adler_spec_checksum(bytes + prefix, suffix, adler_spec_a(bytes, prefix, a0), adler_spec_b(bytes, prefix, a0, b0)) + 1 by",
        ),
        (
            "adler_spec_a(bytes, 0, a0) == a0 by",
            "adler_spec_a(bytes, 0, a0) == a0 + 1 by",
        ),
        (
            "adler_spec_b(bytes, 0, a0, b0) == b0 by",
            "adler_spec_b(bytes, 0, a0, b0) == a0 by",
        ),
    ] {
        let invalid = COMMON_ADLER_SPEC.replacen(before, after, 1);
        assert_ne!(invalid, COMMON_ADLER_SPEC, "missing mutation: {before}");
        let error = click::surface::verify_c0_sources(&invalid, &[])
            .expect_err("false checksum specification lemma accepted");
        assert!(
            !error.message().contains("budget exhausted"),
            "{}",
            error.message()
        );
    }
}

const GENERAL_PARTITION: &str =
    include_str!("../../design/charon-trial/adler2/general-partition.click");

const STORED_GUARD_C: &str = r#"int adler_stored_guard(int remaining, unsigned long size) {
    while (0 < remaining && (size <= 2147483647UL && (int)(unsigned int)size <= remaining)) {
        remaining -= 22208;
    }
    return remaining;
}
"#;

const STORED_GUARD_PROOF: &str = r#"int adler_stored_guard(int remaining, uint64 size) {
 requires 0 <= remaining;
 requires remaining % 22208 == 0;
 requires size == 22208u64;
 ensures result == 0;
} by {
 loop {
  decreases remaining;
  invariant 0 <= remaining;
  invariant remaining % 22208 == 0;
  invariant size == 22208u64;
  preserve by {
   have 0 < remaining by { simp(); }
   apply(adler_outer_nonempty_remaining(remaining)) using { 0 < remaining; remaining % 22208 == 0; }
   mark head;
   apply(adler_outer_remaining_step(at(head, remaining), at(head, remaining))) using { 0 <= at(head, remaining); at(head, remaining) <= at(head, remaining); 22208 <= at(head, remaining); }
   apply(adler_outer_remaining_step_divisible(at(head, remaining))) using { 22208 <= at(head, remaining); at(head, remaining) % 22208 == 0; }
   step();
   have remaining == at(head, remaining) - 22208 by { simp(); }
   have 0 <= remaining by { rewrite(remaining == at(head, remaining) - 22208); assumption(); }
   have remaining % 22208 == 0 by { rewrite(remaining == at(head, remaining) - 22208); assumption(); }
   have remaining < at(head, remaining) by { rewrite(remaining == at(head, remaining) - 22208); assumption(); }
   close_invariants by { simp(); }
  }
 }
 have not (0 < remaining) or not ((int32)(uint32)size <= remaining) by { assumption(); }
 apply(adler_outer_exhausted_remaining(remaining, size)) using { 0 <= remaining; remaining % 22208 == 0; size == 22208u64; not (0 < remaining) or not ((int32)(uint32)size <= remaining); }
 execute(); simp();
}
"#;

// Unlike the small-batch fixture, checks full signed-range usize observations,
// aligned short remainders and actual full-batch progress. The native guard
// catches confusing its captured size comparison with a literal endpoint.
#[test]
fn charon_adler2_general_partition_and_outer_progress_verify() {
    let proof = format!("verifying \"stored-guard.c\";\n{GENERAL_PARTITION}\n{STORED_GUARD_PROOF}");
    click::surface::verify_c0_sources(&proof, &[("stored-guard.c", STORED_GUARD_C)]).unwrap();
}

#[test]
#[ignore = "nightly: general batch metadata expansion and mutation checks"]
fn charon_adler2_general_partition_rejects_stale_and_truncated_metadata() {
    let guard_proof =
        format!("verifying \"stored-guard.c\";\n{GENERAL_PARTITION}\n{STORED_GUARD_PROOF}");
    let guard_sources = [("stored-guard.c", STORED_GUARD_C)];
    let expanded_guard = click::surface::expand_c0_claim_source_by_label(
        &guard_proof,
        &guard_sources,
        "adler_stored_guard.contract",
    )
    .unwrap();
    click::surface::verify_c0_sources(&expanded_guard, &guard_sources).unwrap();
    for (before, after) in [
        ("requires remaining % 22208 == 0;", ""),
        ("ensures result == 0;", "ensures result == 1;"),
    ] {
        let invalid_guard = STORED_GUARD_PROOF.replacen(before, after, 1);
        assert_ne!(invalid_guard, STORED_GUARD_PROOF);
        let invalid =
            format!("verifying \"stored-guard.c\";\n{GENERAL_PARTITION}\n{invalid_guard}");
        assert!(click::surface::verify_c0_sources(&invalid, &guard_sources).is_err());
    }
    for claim in [
        "adler_aligned_outer_partition.ensures_0",
        "adler_outer_bulk_signed_multiple.ensures_0",
        "adler_outer_remaining_step.ensures_0",
        "adler_outer_remaining_step_divisible.ensures_0",
        "adler_absolute_chunk_access.ensures_0",
        "adler_absolute_chunk_access.ensures_1",
        "adler_pointer_sum_association.ensures_0",
        "adler_outer_cursor_step.ensures_0",
        "adler_bounded_slice_access.ensures_0",
        "adler_outer_bulk_within_prefix.ensures_0",
        "adler_outer_signed_partition_identity.ensures_0",
        "adler_outer_exhausted_remaining.ensures_0",
    ] {
        let expanded =
            click::surface::expand_c0_claim_source_by_label(GENERAL_PARTITION, &[], claim)
                .unwrap_or_else(|error| panic!("{claim}: {}", error.message()));
        click::surface::verify_c0_sources(&expanded, &[]).unwrap();
    }
    for (before, after) in [
        (
            "and (int32)(uint32)p == (int32)(uint32)(p - p % 22208u64) + (int32)(uint32)(p % 22208u64) by",
            "and (int32)(uint32)p == (int32)(uint32)(p - p % 22208u64) + (int32)(uint32)(p % 22204u64) by",
        ),
        (
            "requires not (0 < remaining) or not ((int32)(uint32)size <= remaining);",
            "requires 0 < remaining or (int32)(uint32)size <= remaining;",
        ),
        ("requires pos + 4 <= length;", "requires pos <= length;"),
        ("requires pos <= 22204;", "requires pos <= 22205;"),
        (
            "base + (total - (remaining - 22208)) by",
            "base + (total - (remaining - 22204)) by",
        ),
        ("and (t + pos) + 4 <= n by", "and (t + pos) + 4 < n by"),
        ("<= 2147483647u64;", "<= 2147483648u64;"),
        ("<= 22204 by", "<= 22200 by"),
        (
            "ensures remaining - 22208 < remaining",
            "ensures remaining < remaining - 22208",
        ),
        (
            "ensures (remaining - 22208) % 22208 == 0",
            "ensures remaining - 22208 == remaining",
        ),
    ] {
        let invalid = GENERAL_PARTITION.replacen(before, after, 1);
        assert_ne!(invalid, GENERAL_PARTITION, "{before}");
        assert!(
            click::surface::verify_c0_sources(&invalid, &[]).is_err(),
            "{before}"
        );
    }
}

#[test]
#[ignore = "nightly: whole unchanged computation for all signed-range lengths"]
fn charon_adler2_general_compute_proves_original_body() {
    let p = compute_project(GENERAL_COMPUTE);
    C0VerificationSession::new_program_prepared(
        &compute_proof(GENERAL_COMPUTE),
        &load_import(&p.config()).unwrap(),
    )
    .unwrap();
}

#[test]
#[ignore = "nightly: general computation authority, seeds and final bounds"]
fn charon_adler2_general_compute_rejects_invalid_contracts() {
    for (before, after) in [
        (" views bytes[0..bytes_len];", ""),
        (" requires (uint32)self->a <= 65520u32;", ""),
        (" requires (uint32)self->b <= 65520u32;", ""),
        ("ensures self->a < 65521;", "ensures self->a < 1;"),
    ] {
        reject_compute(GENERAL_COMPUTE, before, after);
    }
}

#[test]
#[ignore = "nightly: general whole-body proof-tool agreement and expansion"]
fn charon_adler2_general_compute_tools_recheck_original_contract() {
    let p = compute_project(GENERAL_COMPUTE);
    let claim = "__rust_q_I6_adler2_I4_algo_T29___rust_q_I6_adler2_I7_Adler32_I7_compute.contract";
    for command in ["verify", "profile"] {
        assert_cli(&p, &[command]);
    }
    assert_cli(&p, &["audit", "--claim", claim]);
    assert_cli(&p, &["expand", "--claim", claim, "--in-place"]);
    assert_cli(&p, &["verify"]);
}

#[test]
#[ignore = "nightly: actual general outer and tail cursor rejection"]
fn charon_adler2_general_compute_rejects_false_iterator_state() {
    for (before, after) in [
        (
            "have __rust_mir_27_cursor == old(bytes) by { simp(); }",
            "have __rust_mir_27_cursor == old(bytes) + 1 by { assumption(); }",
        ),
        (
            "have __rust_mir_138_cursor == remainder by { simp(); }",
            "have __rust_mir_138_cursor == remainder + 1 by { assumption(); }",
        ),
    ] {
        reject_compute(GENERAL_COMPUTE, before, after);
    }
}

const LANE_STATE: &str = include_str!("../../design/charon-trial/adler2/lane-state.click");

// Proves the lane recurrence and modular reductions without an imported
// computation summary, including signed reduction quotient witnesses.
#[test]
fn adler_lane_state_recurrences_and_reductions_verify() {
    let source = format!("{COMMON_ADLER_SPEC}\n{LANE_STATE}");
    click::surface::verify_c0_sources(&source, &[]).unwrap();
}

#[test]
#[ignore = "nightly: lane-state expansion and mutation checks"]
fn adler_lane_state_expands_and_rejects_false_relations() {
    let source = format!("{COMMON_ADLER_SPEC}\n{LANE_STATE}");
    for claim in [
        "adler_four_lane_state_step.ensures_0",
        "adler_four_lane_state_step.ensures_1",
        "adler_lane_a_reduction.ensures_0",
        "adler_lane_b_reduction.ensures_0",
        "adler_prefix_a_step_four.ensures_0",
        "adler_prefix_a_step_one.ensures_0",
        "adler_prefix_b_step_four.ensures_0",
    ] {
        let expanded = click::surface::expand_c0_claim_source_by_label(&source, &[], claim)
            .unwrap_or_else(|error| panic!("{claim}: {}", error.message()));
        click::surface::verify_c0_sources(&expanded, &[]).unwrap();
    }
    for (before, after) in [
        (
            "+ 4 * v0 + 3 * v1 + 2 * v2 + v3 by",
            "+ 4 * v0 + 2 * v1 + 3 * v2 + v3 by",
        ),
        (
            "requires 0 <= adler_lane_b(b, a1, a2, a3, b0, b1, b2, b3);",
            "",
        ),
        (
            "+ 3 * to_integer((int32)bytes[n + 1]) + 2 * to_integer((int32)bytes[n + 2])",
            "+ 2 * to_integer((int32)bytes[n + 1]) + 3 * to_integer((int32)bytes[n + 2])",
        ),
        (
            "adler_spec_b(bytes, n + 4, a_seed, b_seed) by",
            "adler_spec_b(bytes, n + 4, a_seed, b_seed + 1) by",
        ),
        ("requires 0 <= b_rep;", ""),
        ("requires n <= 2147483643;", "requires n <= 2147483644;"),
        (
            "adler_spec_a(bytes, n + 1, seed) by",
            "adler_spec_a(bytes, n + 1, seed + 1) by",
        ),
    ] {
        let changed = LANE_STATE.replacen(before, after, 1);
        assert_ne!(changed, LANE_STATE, "missing mutation: {before}");
        let error =
            click::surface::verify_c0_sources(&format!("{COMMON_ADLER_SPEC}\n{changed}"), &[])
                .expect_err("false lane-state relation accepted");
        assert!(
            !error.message().contains("budget exhausted"),
            "{}",
            error.message()
        );
    }
}

#[test]
#[ignore = "nightly: exact byte-observation mutation checks"]
fn charon_adler2_helpers_from_rejects_wrong_mathematical_bytes() {
    reject_helper_contracts(
        0,
        &[
            (
                "old(to_integer((int32)bytes[3]))",
                "old(to_integer((int32)bytes[2]))",
            ),
            (
                "old(to_integer((int32)bytes[0]))",
                "old(to_integer((int32)bytes[0])) + 1",
            ),
        ],
    );
}

// The bridge cannot equate a truncating signed observation with an unbounded
// native count. The selected count and pointer lemmas require the signed limit.
#[test]
fn adler_bounded_native_count_observations_verify() {
    click::surface::verify_c0_sources(BOUNDED_COUNT, &[]).unwrap();
    let changed = BOUNDED_COUNT.replacen(" requires count <= 2147483647u64;", "", 1);
    assert_ne!(changed, BOUNDED_COUNT);
    let error = click::surface::verify_c0_sources(&changed, &[])
        .expect_err("unbounded truncating observation accepted");
    assert!(
        !error.message().contains("budget exhausted"),
        "{}",
        error.message()
    );
}

const PACKING: &str = include_str!("../../design/charon-trial/adler2/packing.click");
const CHECKSUM: &str = include_str!("../../design/charon-trial/adler2/checksum.click");

#[test]
fn charon_adler2_checksum_packs_original_shared_fields() {
    let p = adler2_helpers_project();
    let prepared = load_import(&p.config()).unwrap();
    let source = format!("verifying \"src/lib.rs\";\n{COMMON_ADLER_SPEC}\n{PACKING}\n{CHECKSUM}");
    C0VerificationSession::new_program_prepared(&source, &prepared).unwrap();
}

#[test]
#[ignore = "nightly: original checksum false-result and authority mutations"]
fn charon_adler2_checksum_rejects_false_packing_and_missing_shared_authority() {
    let p = adler2_helpers_project();
    let prepared = load_import(&p.config()).unwrap();
    for (before, after) in [
        (
            "65536 * old(to_integer(self->b))",
            "65535 * old(to_integer(self->b))",
        ),
        (
            "+ old(to_integer(self->a));",
            "+ old(to_integer(self->a)) + 1;",
        ),
        ("views self->a;", ""),
        ("views self->b;", ""),
    ] {
        let contract = CHECKSUM.replacen(before, after, 1);
        assert_ne!(contract, CHECKSUM, "{before}");
        let source =
            format!("verifying \"src/lib.rs\";\n{COMMON_ADLER_SPEC}\n{PACKING}\n{contract}");
        let error = C0VerificationSession::new_program_prepared(&source, &prepared)
            .err()
            .expect("false packing or missing shared authority must be refused");
        assert!(
            !error.message().contains("budget exhausted"),
            "{}",
            error.message()
        );
    }
}

#[test]
#[ignore = "nightly: shared checksum verify/profile/audit/expansion agreement"]
fn charon_adler2_checksum_tools_recheck_original_contract() {
    let p = adler2_helpers_project();
    let source = format!("verifying \"src/lib.rs\";\n{COMMON_ADLER_SPEC}\n{PACKING}\n{CHECKSUM}");
    fs::write(p.root.join("borrow.click"), &source).unwrap();
    for command in ["verify", "profile"] {
        assert_cli(&p, &[command]);
    }
    let offset = source.find("have result == old(((uint32)self->b").unwrap();
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
    for claim in [
        "adler_u16_observation.ensures_0",
        "adler_pack_fields.ensures_0",
        "adler_pack_fields_spec.ensures_0",
    ] {
        assert_cli(&p, &["expand", "--claim", claim, "--in-place"]);
    }
    assert_cli(
        &p,
        &[
            "expand",
            "--claim",
            "__rust_q_I6_adler2_T29___rust_q_I6_adler2_I7_Adler32_I8_checksum.contract",
            "--in-place",
        ],
    );
    assert_cli(&p, &["verify"]);
}
