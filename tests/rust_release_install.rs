//! Dedicated release packaging check; intentionally outside the normal gate.
#[cfg(all(target_os = "linux", target_arch = "x86_64", target_env = "gnu"))]
#[path = "support/rust_frontend.rs"]
mod examples;
#[cfg(all(target_os = "linux", target_arch = "x86_64", target_env = "gnu"))]
#[path = "support/release_assets.rs"]
mod release_assets;

#[cfg(all(target_os = "linux", target_arch = "x86_64", target_env = "gnu"))]
#[test]
#[ignore = "release packaging: requires CLICK_RUST_FRONTEND_ARCHIVE from a release Charon build"]
fn rust_release_archive_installs_and_verifies() {
    use examples::{cli, success};
    use std::{
        fs,
        path::{Path, PathBuf},
        process::Command,
    };
    let archive = fs::canonicalize(PathBuf::from(std::env::var_os("CLICK_RUST_FRONTEND_ARCHIVE")
        .expect("set CLICK_RUST_FRONTEND_ARCHIVE to the release archive; no development-bundle fallback"))).unwrap();
    let name = "click-rust-frontend-x86_64-unknown-linux-gnu.tar.gz";
    assert_eq!(archive.file_name().unwrap(), name);
    let checksum = archive.with_file_name(format!("{name}.sha256"));
    assert!(
        checksum.is_file(),
        "the checksum must come from the release packaging step"
    );
    let t = tempfile::tempdir().unwrap();
    let assets = t.path().join("assets");
    fs::create_dir(&assets).unwrap();
    fs::hard_link(&archive, assets.join(name))
        .or_else(|_| fs::copy(&archive, assets.join(name)).map(|_| ()))
        .unwrap();
    fs::copy(checksum, assets.join(format!("{name}.sha256"))).unwrap();
    let transport = release_assets::curl_transport(t.path());
    let requests = t.path().join("requests.txt");
    let home = t.path().join("fresh-home");
    fs::create_dir_all(home.join("bin")).unwrap();
    let launcher = home.join("bin/click");
    fs::copy(env!("CARGO_BIN_EXE_click"), &launcher).unwrap();
    let version = env!("CARGO_PKG_VERSION");
    assert!(!home.join("versions").exists());
    success(
        Command::new(&launcher)
            .args(["install", version, "--rust"])
            .current_dir(t.path())
            .env("CLICK_HOME", &home)
            .env("HOME", home.join("empty-home"))
            .env("PATH", &transport)
            .env("CLICK_RELEASE_REPOSITORY", "clicklang/click")
            .env("FIXTURE_ASSETS", &assets)
            .env("FIXTURE_REQUESTS", &requests)
            .env_remove("CLICK_CHARON")
            .env_remove("RUSTUP_HOME")
            .env_remove("CARGO_HOME")
            .output()
            .unwrap(),
    );
    let expected = format!(
        "https://github.com/clicklang/click/releases/download/v{version}/{name}\nhttps://github.com/clicklang/click/releases/download/v{version}/{name}.sha256\n"
    );
    assert_eq!(fs::read_to_string(&requests).unwrap(), expected);

    // Relocate the installed version, then remove even the fixture transport.
    let relocated = t.path().join("relocated-home");
    fs::rename(&home, &relocated).unwrap();
    fs::remove_dir_all(assets).unwrap();
    fs::remove_dir_all(transport).unwrap();
    let installed = relocated.join("versions").join(version);
    let binary = installed.join("bin/click");
    let profile: serde_json::Value =
        serde_json::from_str(include_str!("../src/languages/rust/charon-profile.json")).unwrap();
    let listed = cli(&binary, &relocated, t.path(), &["versions"]);
    assert!(listed.status.success());
    assert!(String::from_utf8_lossy(&listed.stdout).contains(&format!(
        "Rust frontend: Charon {}",
        profile["extractor_version"].as_str().unwrap()
    )));
    success(cli(
        &binary,
        &relocated,
        t.path(),
        &["install", version, "--rust"],
    ));

    let basic = t.path().join("basic");
    examples::committed_project(&basic, "examples/basic-rust");
    success(cli(&binary, &relocated, &basic, &["import", "lock"]));
    success(cli(
        &binary,
        &relocated,
        &basic,
        &["verify", "borrow.click"],
    ));
    let lock = fs::read(basic.join("click.project.lock.json")).unwrap();
    assert_eq!(
        lock,
        include_bytes!("../examples/basic-rust/click.project.lock.json")
    );
    success(cli(&binary, &relocated, &basic, &["import", "lock"]));
    assert_eq!(
        fs::read(basic.join("click.project.lock.json")).unwrap(),
        lock
    );
    // The Adler project also holds the zlib C unit, which needs GCC to lock;
    // this check is about the Rust frontend, so it locks the Rust units alone
    // and compares their entries with the committed ones.
    let adler = t.path().join("adler-proof");
    examples::committed_project(&adler, "design/adler32");
    let mut config: serde_json::Value =
        serde_json::from_slice(&fs::read(adler.join("click.project.json")).unwrap()).unwrap();
    config["units"]
        .as_object_mut()
        .unwrap()
        .retain(|_, unit| unit["language"] == "rust");
    fs::write(
        adler.join("click.project.json"),
        serde_json::to_vec_pretty(&config).unwrap(),
    )
    .unwrap();
    success(cli(&binary, &relocated, &adler, &["import", "lock"]));
    success(cli(
        &binary,
        &relocated,
        &adler,
        &["verify", "adler2/restoration.click"],
    ));
    let fresh: serde_json::Value =
        serde_json::from_slice(&fs::read(adler.join("click.project.lock.json")).unwrap()).unwrap();
    let mut committed: serde_json::Value =
        serde_json::from_slice(include_bytes!("../design/adler32/click.project.lock.json"))
            .unwrap();
    committed["units"]
        .as_object_mut()
        .unwrap()
        .retain(|_, unit| unit["language"] == "rust");
    assert_eq!(fresh, committed);
    assert_eq!(
        fs::read(basic.join("borrow.rs")).unwrap(),
        include_bytes!("../examples/basic-rust/borrow.rs")
    );
    let trial = Path::new(env!("CARGO_MANIFEST_DIR")).join("design/adler32/adler2");
    for file in ["src/lib.rs", "src/algo.rs"] {
        assert_eq!(
            fs::read(adler.join("adler2").join(file)).unwrap(),
            fs::read(trial.join(file)).unwrap()
        );
    }
    // Prepare unchanged fragments on the build host, then move the entire demo.
    // Verification below uses the relocated inputs, with an empty PATH and
    // the installed frontend removed.
    let staged_demo = t.path().join("staged-demo");
    success(
        Command::new("python3")
            .arg(Path::new(env!("CARGO_MANIFEST_DIR")).join("scripts/prepare-adler32-demo.py"))
            .arg(&staged_demo)
            .output()
            .unwrap(),
    );
    let demo = t.path().join("relocated-demo");
    fs::rename(staged_demo, &demo).unwrap();
    fs::remove_dir_all(installed.join("frontends/rust")).unwrap();
    success(cli(
        &binary,
        &relocated,
        &basic,
        &["verify", "borrow.click"],
    ));
    success(cli(
        &binary,
        &relocated,
        &adler,
        &["verify", "adler2/restoration.click"],
    ));
    let trial = demo.join("design/adler32");
    for sidecar in [
        "zlib/canonical-demo.click",
        "zlib/incremental-demo.click",
        "zlib/reset-demo.click",
        "adler2/public-demo.click",
        "adler2/incremental-demo.click",
        "adler2/resumed-demo.click",
        "adler2/correspondence.click",
    ] {
        let proof = trial.join(sidecar);
        let output = cli(
            &binary,
            &relocated,
            &demo,
            &["verify", proof.to_str().unwrap()],
        );
        assert!(
            output.status.success(),
            "{sidecar}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        eprintln!(
            "{sidecar}: {}",
            String::from_utf8_lossy(&output.stdout).trim()
        );
    }
}
