use super::*;
use sha2::{Digest, Sha256};

#[test]
#[ignore = "requires the pinned live Charon extractor"]
fn charon_adler2_crate_trial_rejects_unlocked_module_closure() {
    let p = Project::isolated("");
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
            "lib.rs",
            include_bytes!("../../design/adler32/vendor/adler2-2.0.1/src/lib.rs").as_slice(),
        ),
        (
            "algo.rs",
            include_bytes!("../../design/adler32/vendor/adler2-2.0.1/src/algo.rs").as_slice(),
        ),
    ] {
        let file = pin["files"]
            .as_array()
            .unwrap()
            .iter()
            .find(|file| file["path"] == format!("src/{name}"))
            .unwrap();
        assert_eq!(format!("{:x}", Sha256::digest(bytes)), file["sha256"]);
        fs::write(p.root.join(name), bytes).unwrap();
    }
    fs::write(
        p.project_file(),
        r#"{"units": {"adler2": {"language": "rust", "sources": {"lib.rs": {}}}}}"#,
    )
    .unwrap();
    let error = p.refresh().unwrap_err();
    assert!(
        error.contains("requires exactly one locked source file"),
        "{error}"
    );
    assert!(!p.artifact("lib.rs").exists());
    assert!(!p.lock_file().exists());
}
