//! Dedicated release packaging check; intentionally outside the normal gate.
#[cfg(all(target_os = "linux", target_arch = "x86_64", target_env = "gnu"))]
#[path = "support/release_assets.rs"]
mod release_assets;

#[cfg(all(target_os = "linux", target_arch = "x86_64", target_env = "gnu"))]
#[test]
#[ignore = "release packaging: requires CLICK_CPP_FRONTEND_ARCHIVE from a release exporter build"]
fn cpp_release_archive_installs_and_locks() {
    use sha2::{Digest, Sha256};
    use std::{
        fs,
        path::{Path, PathBuf},
        process::{Command, Output},
    };
    fn success(output: Output) -> Output {
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        output
    }
    fn copy(from: &Path, to: &Path) {
        fs::create_dir_all(to).unwrap();
        for entry in fs::read_dir(from).unwrap() {
            let entry = entry.unwrap();
            if entry.file_type().unwrap().is_dir() {
                copy(&entry.path(), &to.join(entry.file_name()));
            } else {
                fs::copy(entry.path(), to.join(entry.file_name())).unwrap();
            }
        }
    }
    // No compiler, LLVM library path or exporter override: only the installed
    // front end is available.
    let cli = |binary: &Path, home: &Path, project: &Path, args: &[&str]| {
        Command::new(binary)
            .args(args)
            .current_dir(project)
            .env("CLICK_HOME", home)
            .env("CLICK_NO_VERSION_DISPATCH", "1")
            .env("PATH", "")
            .env("HOME", home.join("empty-home"))
            .env_remove("CLICK_CPP_EXPORTER")
            .env_remove("LD_LIBRARY_PATH")
            .output()
            .unwrap()
    };
    let archive = fs::canonicalize(PathBuf::from(
        std::env::var_os("CLICK_CPP_FRONTEND_ARCHIVE").expect(
            "set CLICK_CPP_FRONTEND_ARCHIVE to the release archive; no development-exporter fallback",
        ),
    ))
    .unwrap();
    let name = "click-cpp-frontend-x86_64-unknown-linux-gnu.tar.gz";
    assert_eq!(archive.file_name().unwrap(), name);
    let checksum = archive.with_file_name(format!("{name}.sha256"));
    assert!(
        checksum.is_file(),
        "the checksum must come from the release packaging step"
    );
    let t = tempfile::tempdir().unwrap();
    let assets = t.path().join("assets");
    fs::create_dir(&assets).unwrap();
    fs::copy(&archive, assets.join(name)).unwrap();
    fs::copy(checksum, assets.join(format!("{name}.sha256"))).unwrap();
    let transport = release_assets::curl_transport(t.path());
    let requests = t.path().join("requests.txt");
    let home = t.path().join("fresh-home");
    fs::create_dir_all(home.join("bin")).unwrap();
    let launcher = home.join("bin/click");
    fs::copy(env!("CARGO_BIN_EXE_click"), &launcher).unwrap();
    let version = env!("CARGO_PKG_VERSION");
    success(
        Command::new(&launcher)
            .args(["install", version, "--cpp"])
            .current_dir(t.path())
            .env("CLICK_HOME", &home)
            .env("HOME", home.join("empty-home"))
            .env("PATH", &transport)
            .env("CLICK_RELEASE_REPOSITORY", "clicklang/click")
            .env("FIXTURE_ASSETS", &assets)
            .env("FIXTURE_REQUESTS", &requests)
            .env_remove("CLICK_CPP_EXPORTER")
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
    let listed = success(cli(&binary, &relocated, t.path(), &["versions"]));
    assert!(
        String::from_utf8_lossy(&listed.stdout).contains("C++ frontend: exporter"),
        "{listed:?}"
    );
    success(cli(
        &binary,
        &relocated,
        t.path(),
        &["install", version, "--cpp"],
    ));

    // Locking the committed example with the installed exporter reproduces
    // its committed artifacts, and the lock names that exporter by digest.
    let example = Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/basic-cpp");
    let basic = t.path().join("basic");
    copy(&example, &basic);
    fs::remove_dir_all(basic.join(".click")).unwrap();
    fs::remove_file(basic.join("click.project.lock.json")).unwrap();
    success(cli(&binary, &relocated, &basic, &["import", "lock"]));
    for source in [
        "increment.cpp",
        "with_restore.cpp",
        "with_restore_caller.cpp",
    ] {
        let artifact = format!(".click/basic/{source}.click-cpp.json");
        assert_eq!(
            fs::read(basic.join(&artifact)).unwrap(),
            fs::read(example.join(&artifact)).unwrap(),
            "{artifact}"
        );
    }
    let exporter = installed.join("frontends/cpp/click-cpp-exporter");
    let digest = format!("{:x}", Sha256::digest(fs::read(&exporter).unwrap()));
    let lock = fs::read(basic.join("click.project.lock.json")).unwrap();
    let parsed: serde_json::Value = serde_json::from_slice(&lock).unwrap();
    assert_eq!(
        parsed["units"]["basic"]["lock"]["frontend"]["identity"], digest,
        "{parsed}"
    );
    success(cli(&binary, &relocated, &basic, &["import", "lock"]));
    assert_eq!(
        fs::read(basic.join("click.project.lock.json")).unwrap(),
        lock
    );
    for sidecar in [
        "increment.click",
        "with_restore.click",
        "with_restore_caller.click",
    ] {
        success(cli(&binary, &relocated, &basic, &["verify", sidecar]));
    }
    // Verification uses the lock offline, with the front end removed.
    fs::remove_dir_all(installed.join("frontends/cpp")).unwrap();
    success(cli(
        &binary,
        &relocated,
        &basic,
        &["verify", "with_restore_caller.click"],
    ));
}
