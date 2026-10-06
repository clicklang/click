use super::*;
use sha2::{Digest, Sha256};

#[test]
#[ignore = "requires the pinned live Charon extractor"]
fn charon_adler2_crate_trial_rejects_unlocked_module_closure() {
    let p = Project::new("");
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
            include_bytes!("../../design/charon-trial/adler2/src/lib.rs").as_slice(),
        ),
        (
            "algo.rs",
            include_bytes!("../../design/charon-trial/adler2/src/algo.rs").as_slice(),
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
        p.config(),
        serde_json::to_vec(&serde_json::json!({
            "schema": 3,
            "language": "rust",
            "target": "x86_64-unknown-linux-gnu",
            "source": "lib.rs",
            "exporter": std::env::var("CLICK_CHARON").unwrap(),
            "artifact": "adler2.ullbc"
        }))
        .unwrap(),
    )
    .unwrap();
    let error = refresh_import(&p.config()).unwrap_err();
    assert!(
        error.contains("requires exactly one locked source file"),
        "{error}"
    );
    assert!(!p.root.join("adler2.ullbc").exists());
    assert!(
        !p.config()
            .with_file_name("borrow.click.import.json.lock")
            .exists()
    );
}
