//! Shared installed-Rust examples and isolated CLI invocation.
use std::{fs, path::Path, process::Command};

#[allow(dead_code)] // Used by the installed-runtime test, not the release-archive test.
pub fn project(root: &Path) {
    fs::create_dir_all(root).unwrap();
    fs::write(
        root.join("borrow.rs"),
        include_bytes!("../../examples/basic-rust/borrow.rs"),
    )
    .unwrap();
    fs::write(
        root.join("borrow.click"),
        include_str!("../../examples/basic-rust/borrow.click")
            .replace("fn ", "fn basic::")
            .replace("Pair", "basic::Pair"),
    )
    .unwrap();
    fs::write(root.join("click.project.json"), serde_json::json!({"units": {"basic": {
        "language": "rust", "sources": {"borrow.rs": {}},
        "crate": {"name": "basic", "edition": "2024", "features": [], "roots": ["basic::choose", "basic::set_seven", "basic::update", "basic::shared_field"], "files": ["borrow.rs"]}
    }}}).to_string()).unwrap();
}

pub fn cli(binary: &Path, home: &Path, project: &Path, args: &[&str]) -> std::process::Output {
    Command::new(binary)
        .args(args)
        .current_dir(project)
        .env("CLICK_HOME", home)
        .env("CLICK_NO_VERSION_DISPATCH", "1")
        .env("PATH", "")
        .env("HOME", home.join("empty-home"))
        .env_remove("CLICK_CHARON")
        .env_remove("RUSTUP_HOME")
        .env_remove("CARGO_HOME")
        .env_remove("LD_LIBRARY_PATH")
        .output()
        .unwrap()
}

pub fn success(output: std::process::Output) {
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

#[allow(dead_code)] // Used by the installed-runtime test, not the release-archive test.
pub fn adler_project(root: &Path) {
    let vendor = root.parent().unwrap().join("vendor/adler2");
    fs::create_dir_all(root).unwrap();
    fs::create_dir_all(vendor.join("src")).unwrap();
    let trial = Path::new(env!("CARGO_MANIFEST_DIR")).join("design/charon-trial/adler2");
    for file in ["src/lib.rs", "src/algo.rs"] {
        fs::copy(trial.join(file), vendor.join(file)).unwrap();
    }
    fs::write(
        root.join("restoration.click"),
        fs::read_to_string(trial.join("restoration.click"))
            .unwrap()
            .replace(
                "verifying \"src/lib.rs\";",
                "verifying \"../vendor/adler2/src/lib.rs\";",
            ),
    )
    .unwrap();
    fs::write(
        root.join("click.project.json"),
        serde_json::json!({"units": {"adler2": {
            "language": "rust", "root": "../vendor/adler2", "sources": {"src/lib.rs": {}},
            "crate": {"name": "adler2", "edition": "2021", "features": ["std"],
                "roots": ["adler2::Adler32::from_checksum"], "files": ["src/lib.rs", "src/algo.rs"]}
        }}})
        .to_string(),
    )
    .unwrap();
}

/// Copy an unchanged committed project, including its lock and native artifacts.
#[allow(dead_code)]
pub fn committed_project(root: &Path, directory: &str) {
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
    copy(&Path::new(env!("CARGO_MANIFEST_DIR")).join(directory), root);
}
