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
        assert!(C0VerificationSession::new_program_prepared(&invalid, &prepared).is_err());
    }
}
#[test]
#[ignore = "nightly: 5s in the parallel gate"]
fn charon_array_lengths_proof_tools_recheck_metadata_and_array_certificates() {
    for bounds in [false, true] {
        let p = project(bounds);
        for command in ["verify", "profile", "audit"] {
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
            assert_cli(&p, &["verify"]);
        }
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
