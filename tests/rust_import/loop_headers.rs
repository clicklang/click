//! Frozen sources and sidecars distinguish normalization from proof-interface parity.
use super::*;

fn project(name: &str, positive: bool) -> Project {
    let p = Project::new("");
    let files: &[(&str, &[u8])] = match name {
        "loops" => &[
            (
                "loops.rs",
                include_bytes!("../../design/charon-trial/loop-headers/loops.rs"),
            ),
            (
                "borrow.click",
                if positive {
                    include_bytes!("../../design/charon-trial/loop-headers/loops-proof.click")
                        .as_slice()
                } else {
                    include_bytes!("../../design/charon-trial/loop-headers/loops.click").as_slice()
                },
            ),
            (
                "borrow.click.import.json",
                include_bytes!("../../design/charon-trial/loop-headers/loops.click.import.json"),
            ),
            (
                "borrow.click.import.json.lock",
                include_bytes!(
                    "../../design/charon-trial/loop-headers/loops.click.import.json.lock"
                ),
            ),
            (
                "loops.ullbc",
                include_bytes!("../../design/charon-trial/loop-headers/loops.ullbc"),
            ),
        ],
        "sum" => &[
            (
                "sum.rs",
                include_bytes!("../../design/charon-trial/loop-headers/sum.rs"),
            ),
            (
                "borrow.click",
                include_bytes!("../../design/charon-trial/loop-headers/sum.click"),
            ),
            (
                "borrow.click.import.json",
                include_bytes!("../../design/charon-trial/loop-headers/sum.click.import.json"),
            ),
            (
                "borrow.click.import.json.lock",
                include_bytes!("../../design/charon-trial/loop-headers/sum.click.import.json.lock"),
            ),
            (
                "sum.ullbc",
                include_bytes!("../../design/charon-trial/loop-headers/sum.ullbc"),
            ),
        ],
        "headers" => &[
            (
                "headers.rs",
                include_bytes!("../../design/charon-trial/loop-headers/headers.rs"),
            ),
            (
                "borrow.click",
                include_bytes!("../../design/charon-trial/loop-headers/headers.click"),
            ),
            (
                "borrow.click.import.json",
                include_bytes!("../../design/charon-trial/loop-headers/headers.click.import.json"),
            ),
            (
                "borrow.click.import.json.lock",
                include_bytes!(
                    "../../design/charon-trial/loop-headers/headers.click.import.json.lock"
                ),
            ),
            (
                "headers.ullbc",
                include_bytes!("../../design/charon-trial/loop-headers/headers.ullbc"),
            ),
        ],
        _ => panic!("unknown checkpoint"),
    };
    for (name, bytes) in files {
        fs::write(p.root.join(name), bytes).unwrap();
    }
    p
}

#[test]
fn charon_loop_headers_import_unchanged_fixtures_and_retain_frontier_gaps() {
    assert_eq!(
        include_str!("../../design/charon-trial/loop-headers/loops.rs"),
        include_str!("../../examples/rust-loops/loops.rs")
    );
    assert_eq!(
        include_str!("../../design/charon-trial/loop-headers/loops.click"),
        include_str!("../../examples/rust-loops/loops.click")
    );
    assert_eq!(
        include_str!("../../design/charon-trial/loop-headers/sum.rs"),
        include_str!("../../examples/rust-byte-sum/sum.rs")
    );
    assert_eq!(
        include_str!("../../design/charon-trial/loop-headers/sum.click"),
        include_str!("../../examples/rust-byte-sum/sum.click")
    );
    for (name, diagnostic) in [
        ("loops", "requires the execution frontier to be at a loop"),
        ("sum", "local `i` has no value at this frontier"),
    ] {
        let p = project(name, false);
        let prepared = load_import(&p.config()).unwrap();
        let error = C0VerificationSession::new_program_prepared(
            &fs::read_to_string(p.root.join("borrow.click")).unwrap(),
            &prepared,
        )
        .err()
        .expect("retain the numeric-frontier proof-interface gap");
        assert!(error.message().contains(diagnostic), "{error:?}");
    }
}

#[test]
fn charon_loop_headers_check_real_guards_final_assignments_and_false_claims() {
    for name in ["loops", "headers"] {
        let p = project(name, true);
        let prepared = load_import(&p.config()).unwrap();
        let sidecar = fs::read_to_string(p.root.join("borrow.click")).unwrap();
        C0VerificationSession::new_program_prepared(&sidecar, &prepared).unwrap();
        for (before, after) in [
            ("ensures result == n;", "ensures result == 0;"),
            ("ensures result == bytes_len;", "ensures result == 0u64;"),
        ] {
            let invalid = sidecar.replace(before, after);
            if invalid != sidecar {
                assert!(C0VerificationSession::new_program_prepared(&invalid, &prepared).is_err());
            }
        }
    }
}

#[test]
fn charon_loop_headers_tools_recheck_expanded_certificates() {
    for (name, claims) in [
        (
            "loops",
            &["count.contract", "accumulate.contract", "walk.contract"][..],
        ),
        (
            "headers",
            &["final_header.contract", "negated.contract"][..],
        ),
    ] {
        let p = project(name, true);
        for command in ["verify", "profile", "audit"] {
            assert_cli(&p, &[command]);
        }
        for claim in claims {
            assert_cli(&p, &["expand", "--claim", claim, "--in-place"]);
            assert_cli(&p, &["verify"]);
        }
    }
}

#[test]
#[ignore = "requires the pinned live Charon/compiler; scripts/check.sh --charon-live"]
fn charon_loop_headers_live_refresh_and_effectful_header_rejections() {
    for name in ["loops", "sum", "headers"] {
        let p = project(name, true);
        let mut config: serde_json::Value =
            serde_json::from_slice(&fs::read(p.config()).unwrap()).unwrap();
        config["exporter"] = serde_json::json!(
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("target/charon/debug/charon")
        );
        fs::write(p.config(), serde_json::to_vec(&config).unwrap()).unwrap();
        refresh_import(&p.config()).unwrap();
        let prepared = load_import(&p.config()).unwrap();
        if name != "sum" {
            C0VerificationSession::new_program_prepared(
                &fs::read_to_string(p.root.join("borrow.click")).unwrap(),
                &prepared,
            )
            .unwrap();
        }
        if name != "headers" {
            continue;
        }
        for (source, diagnostic) in [
            (
                "pub fn bad(value: &i32) { while *value > 0 {} }",
                "pure scalar copies",
            ),
            (
                "pub fn guard(n: i32)->bool { n > 0 } pub fn bad(n: i32) { while guard(n) {} }",
                "conditional while header",
            ),
            (
                "pub fn bad(n: i32) { let mut i=0; while i<n+1 { i+=1; } }",
                "pure scalar copies",
            ),
            (
                "pub fn bad(n: i32) { let mut i=0; while i<n { if i==2 { break; } i+=1; } }",
                "extra exit",
            ),
        ] {
            fs::remove_file(p.root.join("headers.ullbc")).unwrap();
            fs::write(p.root.join("headers.rs"), source).unwrap();
            let error = refresh_import(&p.config()).unwrap_err();
            assert!(error.contains(diagnostic), "{error}");
            assert!(!p.root.join("headers.ullbc").exists());
            fs::write(
                p.root.join("headers.rs"),
                include_str!("../../design/charon-trial/loop-headers/headers.rs"),
            )
            .unwrap();
            refresh_import(&p.config()).unwrap();
        }
    }
}
