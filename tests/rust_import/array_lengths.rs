use super::*;
const ARRAYS_SOURCE: &str = include_str!("../../design/charon-trial/array-lengths/arrays.rs");
const ARRAYS_SIDECAR: &str = include_str!("../../design/charon-trial/array-lengths/arrays.click");
const BOUNDS_SOURCE: &str = include_str!("../../design/charon-trial/array-lengths/bounds.rs");
const BOUNDS_SIDECAR: &str = include_str!("../../design/charon-trial/array-lengths/bounds.click");
fn project(bounds: bool) -> Project {
    let p = Project::from_fixture("design/charon-trial/array-lengths");
    let sidecar = if bounds {
        BOUNDS_SIDECAR
    } else {
        ARRAYS_SIDECAR
    };
    fs::write(p.root.join("borrow.click"), sidecar).unwrap();
    p
}
#[test]
#[ignore = "nightly: 2s in the parallel gate; other gate tests reach the same code"]
fn charon_array_lengths_preserve_unchanged_sources_and_reject_false_claims() {
    assert_eq!(
        ARRAYS_SOURCE,
        include_str!("../../examples/rust-arrays/arrays.rs")
    );
    assert_eq!(
        ARRAYS_SIDECAR,
        include_str!("../../examples/rust-arrays/arrays.click")
    );
    for bounds in [false, true] {
        let p = project(bounds);
        let prepared = p.prepared().unwrap();
        let sidecar = if bounds {
            BOUNDS_SIDECAR
        } else {
            ARRAYS_SIDECAR
        };
        C0VerificationSession::new_program_prepared(sidecar, &prepared).unwrap();
        let invalid = sidecar.replace("ensures result == 0u64;", "ensures result == 1u64;");
        assert_ne!(invalid, sidecar);
        let head = if bounds { "fn empty_len(" } else { "fn empty(" };
        assert!(verify_rust_proof_after(&invalid, &prepared, head).is_err());
    }
}
#[test]
#[ignore = "nightly: 5s in the parallel gate"]
fn charon_array_lengths_proof_tools_recheck_metadata_and_array_certificates() {
    for bounds in [false, true] {
        let p = project(bounds);
        for command in ["profile", "audit"] {
            assert_cli(&p, &[command]);
        }
        for claim in if bounds {
            &[
                "signed_len.contract",
                "million_len.contract",
                "empty_len.contract",
            ][..]
        } else {
            &["length.contract", "empty.contract", "update.contract"][..]
        } {
            assert_cli(&p, &["expand", "--claim", claim, "--in-place"]);
        }
        assert_cli(&p, &["verify"]);
    }
}
#[test]
#[ignore = "requires the pinned live Charon/compiler; scripts/check.sh --charon-live"]
fn charon_array_lengths_live_refresh_and_compiler_rejections() {
    for bounds in [false, true] {
        let p = project(bounds);
        p.refresh().unwrap();
        C0VerificationSession::new_program_prepared(
            if bounds {
                BOUNDS_SIDECAR
            } else {
                ARRAYS_SIDECAR
            },
            p.prepared().unwrap(),
        )
        .unwrap();
    }
    let p = project(true);
    for (source, diagnostic) in [
        (
            "pub fn bad(x:&mut [u32;3])->usize { let y=&mut *x; let n=x.len(); y[0]=7; n }",
            "E0502",
        ),
        ("pub fn bad(x:&[u16;3])->usize { x.len() }", "scalar"),
    ] {
        fs::remove_file(p.artifact("bounds.rs")).unwrap();
        fs::write(p.root.join("bounds.rs"), source).unwrap();
        let error = p.refresh().unwrap_err();
        assert!(error.contains(diagnostic), "{error}");
        assert!(!p.artifact("bounds.rs").exists());
        fs::write(p.root.join("bounds.rs"), BOUNDS_SOURCE).unwrap();
        p.refresh().unwrap();
    }
}

#[test]
#[ignore = "nightly: verifies and expands Rust array bodies for literal spelling coverage"]
fn charon_rust_integer_literals_preserve_native_array_contracts() {
    let p = project(false);
    let sidecar = ARRAYS_SIDECAR
        .replace("[u8; 4]", "[u8; 0x4usize]")
        .replace("[u32; 3]", "[u32; 0b11usize]")
        .replace("4u64", "0b1_00usize")
        .replace("3u64", "0o3usize")
        .replace("2u64", "2_usize")
        .replace("0u64", "0_usize")
        .replace("7u32", "0b111_u32")
        .replace("9u32", "0o11_u32");
    assert_ne!(sidecar, ARRAYS_SIDECAR);
    fs::write(p.root.join("borrow.click"), &sidecar).unwrap();
    C0VerificationSession::new_program_prepared(&sidecar, p.prepared().unwrap()).unwrap();
    assert_cli(&p, &["expand", "--claim", "length.contract", "--in-place"]);
    assert_cli(&p, &["verify"]);
    let invalid = sidecar.replace("ensures result == 0o3usize;", "ensures result == 0o4usize;");
    assert_ne!(invalid, sidecar);
    assert!(C0VerificationSession::new_program_prepared(&invalid, p.prepared().unwrap()).is_err());
}
