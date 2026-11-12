use std::{fs, process::Command};

#[test]
fn version_manager_help_succeeds_without_installation_or_project_changes() {
    let directory = tempfile::tempdir().unwrap();
    let home = directory.path().join("uncreated-home");
    let pin = directory.path().join(".click-version");
    // Help must work even when reading the selected version would fail.
    fs::write(&pin, "invalid/version\n").unwrap();
    for command in ["install", "use", "default", "versions"] {
        for flag in ["--help", "-h"] {
            let output = Command::new(env!("CARGO_BIN_EXE_click"))
                .args([command, flag])
                .current_dir(directory.path())
                .env("CLICK_HOME", &home)
                // Any attempted download would fail, even on a networked host.
                .env("PATH", "")
                .env("CLICK_RELEASE_REPOSITORY", "invalid repository")
                .output()
                .unwrap();
            assert!(output.status.success(), "{command} {flag}: {output:?}");
            assert!(output.stderr.is_empty(), "{command} {flag}: {output:?}");
            assert_eq!(
                String::from_utf8(output.stdout).unwrap(),
                "version-manager commands:\n  click install <VERSION|latest> [--rust] [--cpp]\n  click use [VERSION|--unset]\n  click default [VERSION]\n  click versions\n",
                "{command} {flag}"
            );
            assert!(!home.exists(), "{command} {flag} created CLICK_HOME");
            assert_eq!(fs::read_to_string(&pin).unwrap(), "invalid/version\n");
        }
    }
}

#[cfg(all(target_os = "linux", target_arch = "x86_64", target_env = "gnu"))]
#[test]
fn rust_frontend_install_checks_the_archive_and_installs_beside_its_click_version() {
    use flate2::{Compression, write::GzEncoder};
    use sha2::{Digest, Sha256};
    use std::{io::Write, os::unix::fs::PermissionsExt};
    let t = tempfile::tempdir().unwrap();
    let version = env!("CARGO_PKG_VERSION");
    let staged = t.path().join("staged");
    for name in ["bin/charon", "bin/charon-driver", "runtime/bin/rustc"] {
        fs::create_dir_all(staged.join(name).parent().unwrap()).unwrap();
        fs::write(staged.join(name), b"frontend fixture").unwrap();
    }
    fs::create_dir_all(staged.join("runtime/lib/rustlib/x86_64-unknown-linux-gnu/lib")).unwrap();
    fs::write(
        staged.join("frontend.json"),
        serde_json::json!({
            "schema": 1, "click_version": version, "host": "x86_64-unknown-linux-gnu",
        "extractor_version": "fixture-version", "extractor_revision": "fixture-revision", "compiler_commit": "fixture-compiler",
            "charon": "bin/charon", "driver": "bin/charon-driver",
            "rustc": "runtime/bin/rustc", "sysroot": "runtime"
        })
        .to_string(),
    )
    .unwrap();
    let encoder = GzEncoder::new(Vec::new(), Compression::fast());
    let mut tar = tar::Builder::new(encoder);
    tar.append_dir_all("rust", &staged).unwrap();
    let archive = tar.into_inner().unwrap().finish().unwrap();
    let assets = t.path().join("assets");
    fs::create_dir(&assets).unwrap();
    let name = "click-rust-frontend-x86_64-unknown-linux-gnu.tar.gz";
    fs::write(assets.join(name), &archive).unwrap();
    let checksum = format!("{:x}  {name}\n", Sha256::digest(&archive));
    fs::write(assets.join(format!("{name}.sha256")), &checksum).unwrap();
    let bin = t.path().join("tools");
    fs::create_dir(&bin).unwrap();
    let mut curl = fs::File::create(bin.join("curl")).unwrap();
    // The fixture transport supplies exactly the release assets. Downloads
    // still pass through the real checksum and archive installation code.
    curl.write_all(b"#!/bin/sh\nwhile [ \"$1\" != --output ]; do shift; done\nshift\noutput=$1\nshift\n/bin/cp \"$FIXTURE_ASSETS/${1##*/}\" \"$output\"\n").unwrap();
    drop(curl);
    fs::set_permissions(bin.join("curl"), fs::Permissions::from_mode(0o755)).unwrap();
    let home = t.path().join("home");
    let installed = home.join("versions").join(version);
    fs::create_dir_all(installed.join("bin")).unwrap();
    fs::copy(env!("CARGO_BIN_EXE_click"), installed.join("bin/click")).unwrap();
    let run = |args: &[&str]| {
        Command::new(env!("CARGO_BIN_EXE_click"))
            .args(args)
            .current_dir(t.path())
            .env("CLICK_HOME", &home)
            .env("PATH", &bin)
            .env("FIXTURE_ASSETS", &assets)
            .output()
            .unwrap()
    };
    let result = run(&["install", version, "--rust"]);
    assert!(result.status.success(), "{result:?}");
    assert!(installed.join("frontends/rust/runtime/bin/rustc").is_file());
    assert!(
        String::from_utf8_lossy(&run(&["versions"]).stdout)
            .contains("Rust frontend: Charon fixture-version")
    );
    // Repeated installs use the existing bundle without downloading it again.
    fs::remove_file(assets.join(name)).unwrap();
    assert!(run(&["install", version, "--rust"]).status.success());
    fs::remove_dir_all(installed.join("frontends")).unwrap();
    fs::write(assets.join(name), archive).unwrap();
    fs::write(assets.join(format!("{name}.sha256")), "0".repeat(64)).unwrap();
    let failed = run(&["install", version, "--rust"]);
    assert!(!failed.status.success());
    assert!(
        String::from_utf8_lossy(&failed.stderr).contains("SHA-256 mismatch"),
        "{failed:?}"
    );
    assert!(!installed.join("frontends/rust").exists());
}

#[cfg(all(target_os = "linux", target_arch = "x86_64", target_env = "gnu"))]
#[test]
fn cpp_frontend_install_checks_the_bundle_against_the_pinned_profile() {
    use flate2::{Compression, write::GzEncoder};
    use sha2::{Digest, Sha256};
    use std::{io::Write, os::unix::fs::PermissionsExt};
    let t = tempfile::tempdir().unwrap();
    let version = env!("CARGO_PKG_VERSION");
    let profile: serde_json::Value =
        serde_json::from_str(include_str!("../src/languages/cpp/frontend-profile.json")).unwrap();
    let archive = |clang_version: &serde_json::Value| {
        let staged = t.path().join("staged");
        let _ = fs::remove_dir_all(&staged);
        fs::create_dir_all(staged.join("clang-resource/include")).unwrap();
        fs::write(staged.join("click-cpp-exporter"), b"exporter fixture").unwrap();
        fs::write(staged.join("clang-resource/include/stddef.h"), b"").unwrap();
        fs::write(
            staged.join("frontend.json"),
            serde_json::json!({
                "schema": 1, "click_version": version, "host": "x86_64-unknown-linux-gnu",
                "exporter_version": profile["exporter_version"], "clang_version": clang_version,
                "artifact_schema": profile["artifact_schema"],
                "exporter": "click-cpp-exporter", "resource_dir": "clang-resource"
            })
            .to_string(),
        )
        .unwrap();
        let mut tar = tar::Builder::new(GzEncoder::new(Vec::new(), Compression::fast()));
        tar.append_dir_all("cpp", &staged).unwrap();
        tar.into_inner().unwrap().finish().unwrap()
    };
    let assets = t.path().join("assets");
    fs::create_dir(&assets).unwrap();
    let name = "click-cpp-frontend-x86_64-unknown-linux-gnu.tar.gz";
    let publish = |archive: &[u8]| {
        fs::write(assets.join(name), archive).unwrap();
        let checksum = format!("{:x}  {name}\n", Sha256::digest(archive));
        fs::write(assets.join(format!("{name}.sha256")), checksum).unwrap();
    };
    let bin = t.path().join("tools");
    fs::create_dir(&bin).unwrap();
    let mut curl = fs::File::create(bin.join("curl")).unwrap();
    curl.write_all(b"#!/bin/sh\nwhile [ \"$1\" != --output ]; do shift; done\nshift\noutput=$1\nshift\n/bin/cp \"$FIXTURE_ASSETS/${1##*/}\" \"$output\"\n").unwrap();
    drop(curl);
    fs::set_permissions(bin.join("curl"), fs::Permissions::from_mode(0o755)).unwrap();
    let home = t.path().join("home");
    let installed = home.join("versions").join(version);
    fs::create_dir_all(installed.join("bin")).unwrap();
    fs::copy(env!("CARGO_BIN_EXE_click"), installed.join("bin/click")).unwrap();
    let run = |args: &[&str]| {
        Command::new(env!("CARGO_BIN_EXE_click"))
            .args(args)
            .current_dir(t.path())
            .env("CLICK_HOME", &home)
            .env("PATH", &bin)
            .env("FIXTURE_ASSETS", &assets)
            .output()
            .unwrap()
    };
    // A bundle built against another Clang is refused and not installed.
    publish(&archive(&serde_json::json!("0.0.0")));
    let failed = run(&["install", version, "--cpp"]);
    assert!(!failed.status.success());
    assert!(
        String::from_utf8_lossy(&failed.stderr)
            .contains("C++ frontend bundle is incomplete or does not match"),
        "{failed:?}"
    );
    assert!(!installed.join("frontends/cpp").exists());
    publish(&archive(&profile["clang_version"]));
    let result = run(&["install", version, "--cpp"]);
    assert!(result.status.success(), "{result:?}");
    // The layout the C++ runtime resolves.
    assert!(installed.join("frontends/cpp/click-cpp-exporter").is_file());
    assert!(
        installed
            .join("frontends/cpp/clang-resource/include/stddef.h")
            .is_file()
    );
    assert!(
        String::from_utf8_lossy(&run(&["versions"]).stdout).contains(&format!(
            "C++ frontend: exporter {} (Clang {})",
            profile["exporter_version"].as_str().unwrap(),
            profile["clang_version"].as_str().unwrap()
        ))
    );
    assert!(
        !run(&["install", version, "--cpp", "--cpp"])
            .status
            .success()
    );
}
