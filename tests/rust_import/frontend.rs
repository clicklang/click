//! Installed Rust frontend selection and extraction, outside the repository.
use std::{fs, path::Path, process::Command};

#[path = "../support/rust_frontend.rs"]
mod examples;
use examples::{cli, project, success};

#[test]
fn missing_installed_rust_frontend_names_the_version_and_install_location() {
    let t = tempfile::tempdir().unwrap();
    let source = t.path().join("project");
    let home = t.path().join("home");
    project(&source);
    let output = cli(
        Path::new(env!("CARGO_BIN_EXE_click")),
        &home,
        &source,
        &["import", "lock"],
    );
    let error = String::from_utf8_lossy(&output.stderr);
    assert!(!output.status.success());
    assert!(error.contains(env!("CARGO_PKG_VERSION")), "{error}");
    if cfg!(all(
        target_os = "linux",
        target_arch = "x86_64",
        target_env = "gnu"
    )) {
        assert!(
            error.contains("Rust frontend is not installed") && error.contains("frontends/rust"),
            "{error}"
        );
        assert!(
            error.contains(&format!(
                "click install {} --rust",
                env!("CARGO_PKG_VERSION")
            )),
            "{error}"
        );
    } else {
        assert!(error.contains("unavailable"), "{error}");
    }
    assert!(!source.join("click.project.lock.json").exists());
}

#[cfg(all(target_os = "linux", target_arch = "x86_64", target_env = "gnu"))]
#[test]
#[ignore = "requires separately built pinned Charon/compiler; copies the runtime bundle"]
fn installed_rust_frontend_extracts_and_verifies_without_rustup() {
    let t = tempfile::tempdir().unwrap();
    let profile: serde_json::Value =
        serde_json::from_str(include_str!("../../src/languages/rust/charon-profile.json")).unwrap();
    let charon = fs::canonicalize(std::env::var_os("CLICK_CHARON").expect("CLICK_CHARON")).unwrap();
    let sysroot = Command::new("rustup")
        .args([
            "run",
            profile["toolchain"].as_str().unwrap(),
            "rustc",
            "--print",
            "sysroot",
        ])
        .output()
        .unwrap();
    assert!(sysroot.status.success());
    let staged = t.path().join("staged");
    success(
        Command::new("python3")
            .arg(Path::new(env!("CARGO_MANIFEST_DIR")).join("scripts/package-rust-frontend.py"))
            .arg(&staged)
            .arg("--charon-bin")
            .arg(charon.parent().unwrap())
            .arg("--charon-license")
            .arg(Path::new(env!("CARGO_MANIFEST_DIR")).join("target/charon-source/LICENSE.md"))
            .arg("--sysroot")
            .arg(String::from_utf8(sysroot.stdout).unwrap().trim())
            .output()
            .unwrap(),
    );
    let home = t.path().join("moved-home");
    let version = home.join("versions").join(env!("CARGO_PKG_VERSION"));
    fs::create_dir_all(version.join("frontends")).unwrap();
    let bundle = version.join("frontends/rust");
    fs::rename(staged, &bundle).unwrap();
    fs::create_dir_all(version.join("bin")).unwrap();
    let binary = version.join("bin/click");
    fs::copy(env!("CARGO_BIN_EXE_click"), &binary).unwrap();
    let source = t.path().join("project");
    project(&source);
    success(cli(&binary, &home, &source, &["import", "lock"]));
    success(cli(&binary, &home, &source, &["verify", "borrow.click"]));
    let lock = fs::read(source.join("click.project.lock.json")).unwrap();
    success(cli(&binary, &home, &source, &["import", "lock"]));
    assert_eq!(
        fs::read(source.join("click.project.lock.json")).unwrap(),
        lock
    );

    // The existing launch proof also uses the external-crate configuration.
    let adler = t.path().join("adler-proof");
    examples::adler_project(&adler);
    success(cli(&binary, &home, &adler, &["import", "lock"]));
    success(cli(
        &binary,
        &home,
        &adler,
        &["verify", "restoration.click"],
    ));

    // Legacy sidecars may omit the development exporter path as well.
    let legacy = t.path().join("legacy");
    fs::create_dir_all(&legacy).unwrap();
    fs::write(
        legacy.join("borrow.rs"),
        include_bytes!("../../examples/basic-rust/borrow.rs"),
    )
    .unwrap();
    fs::write(
        legacy.join("borrow.click"),
        include_bytes!("../../examples/basic-rust/borrow.click"),
    )
    .unwrap();
    fs::write(
        legacy.join("borrow.click.import.json"),
        serde_json::json!({
            "schema": 3, "language": "rust", "target": "x86_64-unknown-linux-gnu",
            "source": "borrow.rs", "artifact": "borrow.ullbc"
        })
        .to_string(),
    )
    .unwrap();
    success(cli(
        &binary,
        &home,
        &legacy,
        &["import", "lock", "borrow.click"],
    ));
    success(cli(&binary, &home, &legacy, &["verify", "borrow.click"]));

    // A compiler-identity mismatch is diagnosed before replacing the lock.
    let manifest_path = bundle.join("frontend.json");
    let original = fs::read(&manifest_path).unwrap();
    let mut manifest: serde_json::Value = serde_json::from_slice(&original).unwrap();
    manifest["compiler_commit"] = "wrong-compiler".into();
    fs::write(&manifest_path, manifest.to_string()).unwrap();
    let failed = cli(&binary, &home, &source, &["import", "lock"]);
    assert!(!failed.status.success());
    let error = String::from_utf8_lossy(&failed.stderr);
    assert!(
        error.contains("Rust frontend version mismatch") && error.contains("wrong-compiler"),
        "{error}"
    );
    assert!(
        error.contains("Remove the Rust frontend") && error.contains("--rust"),
        "{error}"
    );
    assert_eq!(
        fs::read(source.join("click.project.lock.json")).unwrap(),
        lock
    );
    fs::write(&manifest_path, original).unwrap();

    // Check executable handshakes too, rather than trusting the manifest.
    use std::os::unix::fs::PermissionsExt;
    for (file, expected) in [
        ("bin/charon", "Rust frontend version mismatch"),
        (
            "runtime/bin/rustc",
            "Rust frontend compiler version mismatch",
        ),
        ("bin/charon-driver", "Rust frontend driver version mismatch"),
    ] {
        let path = bundle.join(file);
        let saved = path.with_extension("saved");
        fs::rename(&path, &saved).unwrap();
        fs::write(&path, "#!/bin/sh\necho wrong-version\n").unwrap();
        fs::set_permissions(&path, fs::Permissions::from_mode(0o755)).unwrap();
        let failed = cli(&binary, &home, &source, &["import", "lock"]);
        assert!(!failed.status.success());
        let error = String::from_utf8_lossy(&failed.stderr);
        assert!(error.contains(expected), "{error}");
        assert!(
            error.contains("got ") && error.contains("Remove the Rust frontend"),
            "{error}"
        );
        assert!(
            error.contains(&format!(
                "click install {} --rust",
                env!("CARGO_PKG_VERSION")
            )),
            "{error}"
        );
        assert_eq!(
            fs::read(source.join("click.project.lock.json")).unwrap(),
            lock
        );
        fs::rename(saved, path).unwrap();
    }

    // A partial installation must explain how to replace it: a plain repeat
    // install will correctly refuse the existing incomplete bundle.
    fs::remove_file(&manifest_path).unwrap();
    let missing = cli(&binary, &home, &source, &["import", "lock"]);
    let error = String::from_utf8_lossy(&missing.stderr);
    assert!(!missing.status.success());
    assert!(
        error.contains("Remove the Rust frontend") && error.contains("--rust"),
        "{error}"
    );

    // Verification needs neither the compiler nor the frontend manifest.
    fs::remove_dir_all(bundle).unwrap();
    success(cli(&binary, &home, &source, &["verify", "borrow.click"]));
}

#[test]
#[ignore = "requires the pinned source-built Charon executable and rustup"]
fn missing_development_toolchain_names_setup_and_override_action() {
    let t = tempfile::tempdir().unwrap();
    project(t.path());
    let output = Command::new(env!("CARGO_BIN_EXE_click"))
        .args(["import", "lock"])
        .current_dir(t.path())
        .env(
            "CLICK_CHARON",
            std::env::var_os("CLICK_CHARON").expect("CLICK_CHARON"),
        )
        .env("RUSTUP_HOME", t.path().join("empty-rustup"))
        .env("HOME", t.path().join("empty-home"))
        .env("CLICK_HOME", t.path().join("click-home"))
        .output()
        .unwrap();
    let error = String::from_utf8_lossy(&output.stderr);
    assert!(!output.status.success());
    assert!(
        error.contains("toolchain") && error.contains("CLICK_CHARON"),
        "{error}"
    );
    assert!(
        error.contains("scripts/build-charon.sh --install-toolchain"),
        "{error}"
    );
    assert!(!t.path().join("click.project.lock.json").exists());
}
