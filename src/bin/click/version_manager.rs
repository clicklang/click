use super::version_dispatch::{
    binary_filename, click_home, normalize_version, project_pin, project_pin_path, version_binary,
};
use flate2::read::GzDecoder;
use sha2::{Digest, Sha256};
use std::{
    env,
    fs::{self, File, OpenOptions},
    io::{BufReader, Read, Write},
    path::{Path, PathBuf},
    process::Command,
    time::{SystemTime, UNIX_EPOCH},
};
use tar::Archive;

const PACKAGE_NAME: &str = env!("CARGO_PKG_NAME");
const PACKAGE_VERSION: &str = env!("CARGO_PKG_VERSION");
const RELEASE_BINARY: &str = "click";

struct TemporaryDirectory(PathBuf);

impl Drop for TemporaryDirectory {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

pub fn entry_with(command: &str, arguments: Vec<String>) -> Result<(), String> {
    match command {
        "install" => install_command(&arguments),
        "use" => use_command(&arguments),
        "default" => default_command(&arguments),
        "versions" => versions_command(&arguments),
        _ => Err(usage().to_string()),
    }
}

fn usage() -> &'static str {
    "version-manager commands:
  click install <VERSION|latest>
  click use [VERSION|--unset]
  click default [VERSION]
  click versions"
}

fn install_command(arguments: &[String]) -> Result<(), String> {
    if arguments.len() != 1 {
        return Err(usage().to_string());
    }
    let requested = arguments[0].as_str();
    let version = if requested == "latest" {
        latest_version()?
    } else {
        normalize_version(requested)?
    };
    install_version(&version)?;
    Ok(())
}

fn install_version(version: &str) -> Result<(), String> {
    let home = click_home()?;
    let destination = home.join("versions").join(version);
    if release_is_installed(&home, version) {
        println!("Click {version} is already installed.");
        return Ok(());
    }
    if destination.exists() {
        return Err(format!(
            "the Click {version} installation at {} is incomplete; remove it before retrying",
            destination.display()
        ));
    }

    let target = host_target()?;
    let temporary = temporary_directory(&home)?;
    let staged_version = temporary.0.join("version");
    let staged_bin = staged_version.join("bin");
    fs::create_dir_all(&staged_bin)
        .map_err(|error| format!("could not prepare Click {version} install: {error}"))?;

    if version == PACKAGE_VERSION && is_installed_launcher(&home) {
        let launcher_bin = home.join("bin");
        let current = launcher_bin.join(binary_filename(RELEASE_BINARY));
        if !current.is_file() {
            return Err(format!(
                "the Click launcher directory did not contain {}",
                current.display()
            ));
        }
        fs::copy(&current, staged_bin.join(binary_filename(RELEASE_BINARY)))
            .map_err(|error| format!("could not stage {}: {error}", current.display()))?;
    } else {
        download_and_extract(version, &target, &temporary.0, &staged_bin)?;
    }

    if !staged_bin.join(binary_filename(RELEASE_BINARY)).is_file() {
        return Err(format!(
            "the release archive did not contain {RELEASE_BINARY}"
        ));
    }
    let versions = home.join("versions");
    fs::create_dir_all(&versions)
        .map_err(|error| format!("could not create {}: {error}", versions.display()))?;
    fs::rename(&staged_version, &destination).map_err(|error| {
        format!(
            "could not install Click {version} at {}: {error}",
            destination.display()
        )
    })?;
    println!("Installed Click {version} for {target}.");
    Ok(())
}

fn is_installed_launcher(home: &Path) -> bool {
    let Ok(current) = env::current_exe().and_then(|path| path.canonicalize()) else {
        return false;
    };
    let launcher = home.join("bin").join(binary_filename("click"));
    launcher
        .canonicalize()
        .map(|path| current == path)
        .unwrap_or(false)
}

fn download_and_extract(
    version: &str,
    target: &str,
    temporary: &Path,
    staged_bin: &Path,
) -> Result<(), String> {
    let repository = release_repository()?;
    let tag = format!("v{version}");
    let archive_name = format!("{PACKAGE_NAME}-{target}.tar.gz");
    let base = format!("https://github.com/{repository}/releases/download/{tag}");
    let archive_path = temporary.join(&archive_name);
    let checksum_path = temporary.join(format!("{archive_name}.sha256"));

    download(&format!("{base}/{archive_name}"), &archive_path)?;
    download(&format!("{base}/{archive_name}.sha256"), &checksum_path)?;
    verify_sha256(&archive_path, &checksum_path)?;

    let extracted = temporary.join("archive");
    fs::create_dir_all(&extracted)
        .map_err(|error| format!("could not prepare archive extraction: {error}"))?;
    let file = File::open(&archive_path)
        .map_err(|error| format!("could not read {}: {error}", archive_path.display()))?;
    let decoder = GzDecoder::new(file);
    let mut archive = Archive::new(decoder);
    archive
        .unpack(&extracted)
        .map_err(|error| format!("could not safely extract Click {version}: {error}"))?;

    let filename = binary_filename(RELEASE_BINARY);
    let source = find_binary(&extracted, &filename)?
        .ok_or_else(|| format!("the Click {version} archive did not contain {filename}"))?;
    fs::copy(&source, staged_bin.join(&filename)).map_err(|error| {
        format!(
            "could not install {filename} from {}: {error}",
            source.display()
        )
    })?;
    Ok(())
}

fn find_binary(directory: &Path, expected_name: &str) -> Result<Option<PathBuf>, String> {
    let entries = fs::read_dir(directory)
        .map_err(|error| format!("could not inspect {}: {error}", directory.display()))?;
    for entry in entries {
        let entry = entry.map_err(|error| format!("could not inspect archive entry: {error}"))?;
        let file_type = entry
            .file_type()
            .map_err(|error| format!("could not inspect archive entry: {error}"))?;
        let path = entry.path();
        if file_type.is_dir() {
            if let Some(binary) = find_binary(&path, expected_name)? {
                return Ok(Some(binary));
            }
        } else if file_type.is_file() && entry.file_name() == expected_name {
            return Ok(Some(path));
        }
    }
    Ok(None)
}

fn verify_sha256(archive: &Path, checksum_file: &Path) -> Result<(), String> {
    let checksum = fs::read_to_string(checksum_file)
        .map_err(|error| format!("could not read release checksum: {error}"))?;
    let expected = checksum
        .split_whitespace()
        .find(|word| word.len() == 64 && word.bytes().all(|byte| byte.is_ascii_hexdigit()))
        .ok_or_else(|| "the release checksum file did not contain a SHA-256 digest".to_string())?
        .to_ascii_lowercase();

    let mut reader = BufReader::new(
        File::open(archive)
            .map_err(|error| format!("could not read {}: {error}", archive.display()))?,
    );
    let mut digest = Sha256::new();
    let mut buffer = [0_u8; 16 * 1024];
    loop {
        let count = reader
            .read(&mut buffer)
            .map_err(|error| format!("could not hash {}: {error}", archive.display()))?;
        if count == 0 {
            break;
        }
        digest.update(&buffer[..count]);
    }
    let mut actual = String::with_capacity(64);
    for byte in digest.finalize() {
        actual.push_str(&format!("{byte:02x}"));
    }
    if actual != expected {
        return Err(format!(
            "SHA-256 mismatch for {}: expected {expected}, got {actual}",
            archive.display()
        ));
    }
    Ok(())
}

fn latest_version() -> Result<String, String> {
    let repository = release_repository()?;
    let url = format!("https://api.github.com/repos/{repository}/releases/latest");
    let response = curl_output(&url)?;
    let value: serde_json::Value = serde_json::from_slice(&response)
        .map_err(|error| format!("GitHub returned invalid release metadata: {error}"))?;
    let tag = value
        .get("tag_name")
        .and_then(serde_json::Value::as_str)
        .ok_or_else(|| "GitHub's latest release response did not contain tag_name".to_string())?;
    normalize_version(tag)
}

fn release_repository() -> Result<String, String> {
    let repository = env::var("CLICK_RELEASE_REPOSITORY").unwrap_or_else(|_| {
        env!("CARGO_PKG_REPOSITORY")
            .trim_start_matches("https://github.com/")
            .trim_end_matches(".git")
            .to_string()
    });
    let mut parts = repository.split('/');
    let owner = parts.next().unwrap_or_default();
    let name = parts.next().unwrap_or_default();
    let valid_part = |part: &str| {
        !part.is_empty()
            && part
                .bytes()
                .all(|byte| byte.is_ascii_alphanumeric() || matches!(byte, b'-' | b'_' | b'.'))
    };
    if !valid_part(owner) || !valid_part(name) || parts.next().is_some() {
        return Err(
            "CLICK_RELEASE_REPOSITORY must be a GitHub repository in owner/name form".to_string(),
        );
    }
    Ok(format!("{owner}/{name}"))
}

fn host_target() -> Result<String, String> {
    #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
    {
        return Ok("aarch64-apple-darwin".to_string());
    }
    #[cfg(all(target_os = "macos", target_arch = "x86_64"))]
    {
        return Ok("x86_64-apple-darwin".to_string());
    }
    #[cfg(all(target_os = "linux", target_arch = "aarch64", target_env = "musl"))]
    {
        return Ok("aarch64-unknown-linux-musl".to_string());
    }
    #[cfg(all(target_os = "linux", target_arch = "x86_64", target_env = "musl"))]
    {
        return Ok("x86_64-unknown-linux-musl".to_string());
    }
    #[cfg(all(target_os = "linux", target_arch = "aarch64", not(target_env = "musl")))]
    {
        return Ok("aarch64-unknown-linux-gnu".to_string());
    }
    #[cfg(all(target_os = "linux", target_arch = "x86_64", not(target_env = "musl")))]
    {
        return Ok("x86_64-unknown-linux-gnu".to_string());
    }
    #[cfg(all(target_os = "windows", target_arch = "aarch64"))]
    {
        return Ok("aarch64-pc-windows-msvc".to_string());
    }
    #[cfg(all(target_os = "windows", target_arch = "x86_64"))]
    {
        return Ok("x86_64-pc-windows-msvc".to_string());
    }
    #[allow(unreachable_code)]
    Err(format!(
        "prebuilt Click releases do not support this platform ({}/{})",
        env::consts::OS,
        env::consts::ARCH
    ))
}

fn curl_output(url: &str) -> Result<Vec<u8>, String> {
    let output = Command::new("curl")
        .args([
            "--fail",
            "--location",
            "--silent",
            "--show-error",
            "--proto",
            "=https",
            "--tlsv1.2",
            "--connect-timeout",
            "15",
            "--max-time",
            "300",
            "--header",
            "Accept: application/vnd.github+json",
            "--header",
            "User-Agent: clicklang",
            url,
        ])
        .output()
        .map_err(|error| format!("could not run curl to download Click: {error}"))?;
    if !output.status.success() {
        return Err(format!(
            "could not download {url}: {}",
            String::from_utf8_lossy(&output.stderr).trim()
        ));
    }
    Ok(output.stdout)
}

fn download(url: &str, destination: &Path) -> Result<(), String> {
    let output = Command::new("curl")
        .args([
            "--fail",
            "--location",
            "--silent",
            "--show-error",
            "--proto",
            "=https",
            "--tlsv1.2",
            "--connect-timeout",
            "15",
            "--max-time",
            "600",
            "--header",
            "User-Agent: clicklang",
            "--output",
        ])
        .arg(destination)
        .arg(url)
        .output()
        .map_err(|error| format!("could not run curl to download Click: {error}"))?;
    if !output.status.success() {
        return Err(format!(
            "could not download {url}: {}",
            String::from_utf8_lossy(&output.stderr).trim()
        ));
    }
    Ok(())
}

fn temporary_directory(home: &Path) -> Result<TemporaryDirectory, String> {
    let root = home.join("tmp");
    fs::create_dir_all(&root)
        .map_err(|error| format!("could not create {}: {error}", root.display()))?;
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default()
        .as_nanos();
    for attempt in 0..16 {
        let path = root.join(format!("install-{}-{nonce}-{attempt}", std::process::id()));
        match fs::create_dir(&path) {
            Ok(()) => return Ok(TemporaryDirectory(path)),
            Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => {}
            Err(error) => {
                return Err(format!("could not create {}: {error}", path.display()));
            }
        }
    }
    Err(format!(
        "could not allocate a temporary directory under {}",
        root.display()
    ))
}

fn install_is_present(version: &str) -> Result<bool, String> {
    Ok(release_is_installed(&click_home()?, version))
}

fn release_is_installed(home: &Path, version: &str) -> bool {
    version_binary(home, version, RELEASE_BINARY).is_file()
}

fn use_command(arguments: &[String]) -> Result<(), String> {
    let cwd =
        env::current_dir().map_err(|error| format!("could not read current directory: {error}"))?;
    match arguments {
        [] => match project_pin()? {
            Some(version) => println!("Project Click version: {}", normalize_version(&version)?),
            None => println!("No Click version is pinned for this project."),
        },
        [argument] if argument == "--unset" => {
            let pin = project_pin_path()?.unwrap_or_else(|| cwd.join(".click-version"));
            match fs::remove_file(&pin) {
                Ok(()) => println!("Removed the Click version pin at {}.", pin.display()),
                Err(error) if error.kind() == std::io::ErrorKind::NotFound => {
                    println!("No Click version pin exists in {}.", cwd.display())
                }
                Err(error) => {
                    return Err(format!("could not remove {}: {error}", pin.display()));
                }
            }
        }
        [argument] => {
            let version = normalize_version(argument)?;
            if !install_is_present(&version)? {
                return Err(format!(
                    "Click {version} is not installed; run `click install {version}`"
                ));
            }
            let pin = project_pin_path()?.unwrap_or_else(|| cwd.join(".click-version"));
            replace_file(&pin, format!("{version}\n").as_bytes())?;
            println!("Pinned Click {version} for {}.", cwd.display());
        }
        _ => return Err(usage().to_string()),
    }
    Ok(())
}

fn default_command(arguments: &[String]) -> Result<(), String> {
    let path = click_home()?.join("default");
    match arguments {
        [] => match fs::read_to_string(&path) {
            Ok(value) => println!("Global Click default: {}", normalize_version(&value)?),
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => {
                println!("No global Click default is set.")
            }
            Err(error) => {
                return Err(format!(
                    "could not read global Click default at {}: {error}",
                    path.display()
                ));
            }
        },
        [argument] => {
            let version = normalize_version(argument)?;
            if !install_is_present(&version)? {
                return Err(format!(
                    "Click {version} is not installed; run `click install {version}`"
                ));
            }
            replace_file(&path, format!("{version}\n").as_bytes())?;
            println!("Set the global Click default to {version}.");
        }
        _ => return Err(usage().to_string()),
    }
    Ok(())
}

fn versions_command(arguments: &[String]) -> Result<(), String> {
    if !arguments.is_empty() {
        return Err(usage().to_string());
    }
    let home = click_home()?;
    let versions = home.join("versions");
    let default = match fs::read_to_string(home.join("default")) {
        Ok(value) => Some(value),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => None,
        Err(error) => return Err(format!("could not read global Click default: {error}")),
    };
    let project = project_pin()?;
    let mut installed = Vec::new();
    match fs::read_dir(&versions) {
        Ok(entries) => {
            for entry in entries {
                let entry =
                    entry.map_err(|error| format!("could not read installed versions: {error}"))?;
                if entry
                    .file_type()
                    .map_err(|error| format!("could not inspect installed version: {error}"))?
                    .is_dir()
                {
                    let version = entry.file_name().to_string_lossy().into_owned();
                    if release_is_installed(&home, &version) {
                        installed.push(version);
                    }
                }
            }
        }
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
        Err(error) => return Err(format!("could not read {}: {error}", versions.display())),
    }
    installed.sort();
    if installed.is_empty() {
        println!("No Click versions are installed.");
        return Ok(());
    }
    for version in installed {
        let global_marker = if default.as_deref().map(str::trim) == Some(version.as_str()) {
            " (default)"
        } else {
            ""
        };
        let project_marker = if project.as_deref().map(str::trim) == Some(version.as_str()) {
            " (project)"
        } else {
            ""
        };
        println!("{version}{global_marker}{project_marker}");
    }
    Ok(())
}

fn replace_file(path: &Path, contents: &[u8]) -> Result<(), String> {
    let parent = path
        .parent()
        .ok_or_else(|| format!("{} has no parent directory", path.display()))?;
    fs::create_dir_all(parent)
        .map_err(|error| format!("could not create {}: {error}", parent.display()))?;
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default()
        .as_nanos();
    let name = path
        .file_name()
        .unwrap_or_default()
        .to_string_lossy()
        .into_owned();
    let temporary = parent.join(format!(".{name}.tmp-{}-{nonce}", std::process::id()));
    let mut file = OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(&temporary)
        .map_err(|error| format!("could not create {}: {error}", temporary.display()))?;
    if let Err(error) = file.write_all(contents).and_then(|_| file.sync_all()) {
        let _ = fs::remove_file(&temporary);
        return Err(format!("could not write {}: {error}", temporary.display()));
    }
    drop(file);

    if path.exists() {
        let backup = parent.join(format!(".{name}.backup-{}-{nonce}", std::process::id()));
        fs::rename(path, &backup).map_err(|error| {
            format!(
                "could not preserve {} while updating it: {error}",
                path.display()
            )
        })?;
        if let Err(error) = fs::rename(&temporary, path) {
            let _ = fs::rename(&backup, path);
            let _ = fs::remove_file(&temporary);
            return Err(format!("could not update {}: {error}", path.display()));
        }
        let _ = fs::remove_file(backup);
    } else {
        fs::rename(&temporary, path)
            .map_err(|error| format!("could not update {}: {error}", path.display()))?;
    }
    Ok(())
}
