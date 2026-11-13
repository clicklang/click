//! Locating the pinned C++ exporter. One order, shared in shape with the Rust
//! front end: the `CLICK_CPP_EXPORTER` development override, then the exporter
//! installed beside this version of `click`, otherwise an error that says how
//! to provide one. Nothing falls back to a path from the build machine.

use std::path::{Path, PathBuf};

const VERSION: &str = env!("CARGO_PKG_VERSION");
/// The exporter's file name inside an installed front end.
pub(crate) const EXPORTER_NAME: &str = "click-cpp-exporter";

/// Where the C++ front end for this Click version is installed under `home`.
pub(crate) fn installed_frontend(home: &Path) -> PathBuf {
    home.join("versions").join(VERSION).join("frontends/cpp")
}

/// The exporter to run, by the documented resolution order.
pub(crate) fn resolve_exporter() -> Result<PathBuf, String> {
    resolve_exporter_from(
        std::env::var_os("CLICK_CPP_EXPORTER").filter(|value| !value.is_empty()),
        click_home(),
        PREBUILT_HOST,
    )
}

/// Whether releases ship a prebuilt C++ front end for the host Click runs
/// on, which `click add cpp` installs. Other hosts build the
/// exporter from a Click checkout.
const PREBUILT_HOST: bool = cfg!(all(
    target_os = "linux",
    target_arch = "x86_64",
    target_env = "gnu"
));

/// The host, as a diagnostic names it.
fn host_description() -> String {
    format!("{} {}", std::env::consts::OS, std::env::consts::ARCH)
}

fn click_home() -> Option<PathBuf> {
    std::env::var_os("CLICK_HOME")
        .filter(|value| !value.is_empty())
        .map(PathBuf::from)
        .or_else(|| {
            std::env::var_os("HOME")
                .or_else(|| std::env::var_os("USERPROFILE"))
                .map(|home| PathBuf::from(home).join(".click"))
        })
}

fn resolve_exporter_from(
    override_path: Option<std::ffi::OsString>,
    home: Option<PathBuf>,
    prebuilt_host: bool,
) -> Result<PathBuf, String> {
    if let Some(path) = override_path {
        let path = PathBuf::from(path);
        if !path.is_file() {
            return Err(format!(
                "CLICK_CPP_EXPORTER names `{}`, which is not a file; correct or unset it to use the installed C++ front end",
                path.display()
            ));
        }
        return Ok(path);
    }
    let Some(home) = home else {
        return Err(
            "cannot locate the C++ front end; set CLICK_HOME, or set CLICK_CPP_EXPORTER to an exporter built with scripts/build-cpp-exporter.sh"
                .into(),
        );
    };
    let exporter = installed_frontend(&home).join(EXPORTER_NAME);
    if exporter.is_file() {
        return Ok(exporter);
    }
    if !prebuilt_host {
        return Err(format!(
            "no prebuilt C++ front end is available for this platform ({}); build the exporter from a Click checkout with scripts/build-cpp-exporter.sh and set CLICK_CPP_EXPORTER to the path it prints",
            host_description()
        ));
    }
    Err(format!(
        "the C++ front end is not installed for Click {VERSION} (expected `{}`); install it with `click add cpp`, or set CLICK_CPP_EXPORTER to an exporter built with scripts/build-cpp-exporter.sh",
        exporter.display()
    ))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_override_then_the_installed_frontend_then_a_named_error() {
        let home = std::env::temp_dir().join(format!("click-cpp-runtime-{}", std::process::id()));
        let installed = installed_frontend(&home).join(EXPORTER_NAME);
        let _ = std::fs::remove_dir_all(&home);

        let missing = resolve_exporter_from(None, Some(home.clone()), true).unwrap_err();
        assert!(missing.contains("not installed for Click"), "{missing}");
        assert!(missing.contains("click add cpp"), "{missing}");
        // A host releases ship no front end for says so, rather than
        // pointing at an install that would fail.
        let unbuilt = resolve_exporter_from(None, Some(home.clone()), false).unwrap_err();
        assert!(
            unbuilt.contains("no prebuilt C++ front end is available for this platform"),
            "{unbuilt}"
        );
        assert!(!unbuilt.contains("click add cpp"), "{unbuilt}");
        assert!(
            missing.contains(&installed.display().to_string()),
            "{missing}"
        );

        std::fs::create_dir_all(installed.parent().unwrap()).unwrap();
        std::fs::write(&installed, b"").unwrap();
        assert_eq!(
            resolve_exporter_from(None, Some(home.clone()), true),
            Ok(installed.clone())
        );

        let override_path = home.join("dev-exporter");
        std::fs::write(&override_path, b"").unwrap();
        assert_eq!(
            resolve_exporter_from(Some(override_path.clone().into()), Some(home.clone()), true),
            Ok(override_path)
        );
        let wrong =
            resolve_exporter_from(Some(home.join("absent").into()), Some(home.clone()), true)
                .unwrap_err();
        assert!(wrong.contains("CLICK_CPP_EXPORTER names"), "{wrong}");

        assert!(
            resolve_exporter_from(None, None, true)
                .unwrap_err()
                .contains("CLICK_HOME")
        );
        let _ = std::fs::remove_dir_all(&home);
    }
}
