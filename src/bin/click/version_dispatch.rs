use std::{
    env, fs,
    path::{Path, PathBuf},
    process::Command,
};

const PACKAGE_VERSION: &str = env!("CARGO_PKG_VERSION");
const PROJECT_PIN: &str = ".click-version";

pub fn maybe_dispatch(binary: &str, arguments: &[String]) -> Result<Option<i32>, String> {
    if binary == "click" && arguments.first().is_some_and(|arg| is_manager_command(arg)) {
        return Ok(None);
    }
    if env::var_os("CLICK_NO_VERSION_DISPATCH").is_some() || is_development_binary() {
        return Ok(None);
    }

    let Some(version) = selected_version(binary)? else {
        return Ok(None);
    };
    if version == PACKAGE_VERSION {
        return Ok(None);
    }

    let executable = version_binary(&click_home()?, &version, binary);
    let status = Command::new(&executable)
        .args(arguments)
        .env("CLICK_NO_VERSION_DISPATCH", "1")
        .status()
        .map_err(|error| format!("could not run Click {version}: {error}"))?;
    Ok(Some(status.code().unwrap_or(1)))
}

pub fn click_home() -> Result<PathBuf, String> {
    if let Some(home) = env::var_os("CLICK_HOME").filter(|value| !value.is_empty()) {
        return Ok(PathBuf::from(home));
    }
    let home = env::var_os("HOME")
        .or_else(|| env::var_os("USERPROFILE"))
        .ok_or_else(|| "could not determine home directory; set CLICK_HOME".to_string())?;
    Ok(PathBuf::from(home).join(".click"))
}

pub fn binary_filename(binary: &str) -> String {
    if cfg!(windows) && !binary.ends_with(".exe") {
        format!("{binary}.exe")
    } else {
        binary.to_string()
    }
}

pub fn version_binary(home: &Path, version: &str, binary: &str) -> PathBuf {
    home.join("versions")
        .join(version)
        .join("bin")
        .join(binary_filename(binary))
}

pub fn project_pin_path() -> Result<Option<PathBuf>, String> {
    let mut directory =
        env::current_dir().map_err(|error| format!("could not read current directory: {error}"))?;
    loop {
        let pin = directory.join(PROJECT_PIN);
        match fs::metadata(&pin) {
            Ok(_) => return Ok(Some(pin)),
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
            Err(error) => {
                return Err(format!(
                    "could not inspect project Click version at {}: {error}",
                    pin.display()
                ));
            }
        }
        if !directory.pop() {
            return Ok(None);
        }
    }
}

pub fn project_pin() -> Result<Option<String>, String> {
    let Some(path) = project_pin_path()? else {
        return Ok(None);
    };
    fs::read_to_string(&path).map(Some).map_err(|error| {
        format!(
            "could not read project Click version at {}: {error}",
            path.display()
        )
    })
}

pub fn normalize_version(value: &str) -> Result<String, String> {
    let trimmed = value.trim();
    let version = trimmed.strip_prefix('v').unwrap_or(trimmed);
    if version.is_empty()
        || !version
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || matches!(byte, b'.' | b'-' | b'+'))
        || version.starts_with('.')
        || version.ends_with('.')
        || version.contains("..")
    {
        return Err(format!("invalid Click version {value:?}"));
    }
    Ok(version.to_string())
}

fn selected_version(binary: &str) -> Result<Option<String>, String> {
    let home = click_home()?;
    let version = if let Some(value) = project_pin()? {
        Some(normalize_version(&value)?)
    } else {
        let path = home.join("default");
        match fs::read_to_string(&path) {
            Ok(value) => Some(normalize_version(&value)?),
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => None,
            Err(error) => {
                return Err(format!(
                    "could not read global Click default at {}: {error}",
                    path.display()
                ));
            }
        }
    };

    if let Some(version) = &version {
        let executable = version_binary(&home, version, binary);
        if !executable.is_file() {
            return Err(format!(
                "Click {version} is selected but {} is not installed; run `click install {version}`",
                binary_filename(binary)
            ));
        }
    }
    Ok(version)
}

fn is_development_binary() -> bool {
    let Ok(executable) = env::current_exe() else {
        return false;
    };
    let Ok(executable) = executable.canonicalize() else {
        return false;
    };
    let manifest = Path::new(env!("CARGO_MANIFEST_DIR"));
    let Ok(manifest) = manifest.canonicalize() else {
        return false;
    };
    executable.starts_with(manifest)
}

fn is_manager_command(command: &str) -> bool {
    matches!(command, "install" | "use" | "default" | "versions")
}
