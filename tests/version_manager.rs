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
                "version-manager commands:\n  click install <VERSION|latest>\n  click use [VERSION|--unset]\n  click default [VERSION]\n  click versions\n",
                "{command} {flag}"
            );
            assert!(!home.exists(), "{command} {flag} created CLICK_HOME");
            assert_eq!(fs::read_to_string(&pin).unwrap(), "invalid/version\n");
        }
    }
}
