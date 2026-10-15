//! Versioned Rust frontend bundles. Installed extraction never needs rustup.
use super::profile;
use crate::languages::compiler_process::{CompilerLimits, run_compiler};
use serde::Deserialize;
use std::collections::BTreeMap;
use std::path::{Component, Path, PathBuf};

const VERSION: &str = env!("CARGO_PKG_VERSION");
const HOST: &str = "x86_64-unknown-linux-gnu";

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Manifest {
    schema: u32,
    click_version: String,
    host: String,
    extractor_revision: String,
    extractor_version: String,
    compiler_commit: String,
    charon: String,
    driver: String,
    rustc: String,
    sysroot: String,
}

pub(super) struct Runtime {
    pub executable: PathBuf,
    pub driver: PathBuf,
    pub environment: BTreeMap<String, String>,
    compiler: PathBuf,
    compiler_prefix: Vec<String>,
    pub sysroot: Option<PathBuf>,
    recovery: String,
}

pub(super) fn resolve(legacy: Option<&Path>) -> Result<Runtime, String> {
    if let Some(path) = legacy {
        return with_recovery(
            Runtime::legacy(path),
            "Correct the legacy `exporter` path; for a source build run `scripts/build-charon.sh --install-toolchain`, or omit `exporter` to select the installed Rust frontend"
                .into(),
        );
    }
    if let Some(path) = std::env::var_os("CLICK_CHARON").filter(|s| !s.is_empty()) {
        let path = PathBuf::from(path);
        let runtime = if path.is_dir() {
            Runtime::bundle(&path)
        } else {
            Runtime::legacy(&path)
        };
        return with_recovery(
            runtime,
            format!(
                "Correct or unset CLICK_CHARON to select the installed Rust frontend. For a source-built executable, run `scripts/build-charon.sh --install-toolchain` (toolchain {})",
                profile::get().toolchain
            ),
        );
    }
    if !cfg!(all(
        target_os = "linux",
        target_arch = "x86_64",
        target_env = "gnu"
    )) {
        return Err(format!(
            "Rust frontend bundle for Click {VERSION} is unavailable on {}/{}; the packaged host is {HOST}",
            std::env::consts::OS,
            std::env::consts::ARCH
        ));
    }
    let home = std::env::var_os("CLICK_HOME")
        .filter(|s| !s.is_empty())
        .map(PathBuf::from)
        .or_else(|| {
            std::env::var_os("HOME")
                .or_else(|| std::env::var_os("USERPROFILE"))
                .map(|p| PathBuf::from(p).join(".click"))
        })
        .ok_or("cannot locate the Rust frontend; set CLICK_HOME")?;
    let bundle = home.join("versions").join(VERSION).join("frontends/rust");
    if !bundle.exists() {
        return Err(format!(
            "Rust frontend is not installed for Click {VERSION} ({}/{}); run `click install {VERSION} --rust` to install its pinned bundle at `{}`. CLICK_CHARON is a development override",
            std::env::consts::OS,
            std::env::consts::ARCH,
            bundle.display()
        ));
    }
    with_recovery(
        Runtime::bundle(&bundle),
        format!(
            "Remove the Rust frontend at `{}` and reinstall with `click install {VERSION} --rust`",
            bundle.display()
        ),
    )
}

fn with_recovery(result: Result<Runtime, String>, recovery: String) -> Result<Runtime, String> {
    match result {
        Ok(mut runtime) => {
            runtime.recovery = recovery;
            Ok(runtime)
        }
        Err(error) => Err(format!("{error}. {recovery}")),
    }
}

fn bundled_path(root: &Path, name: &str) -> Result<PathBuf, String> {
    if name.is_empty()
        || !Path::new(name)
            .components()
            .all(|c| matches!(c, Component::Normal(_)))
    {
        return Err("Rust frontend manifest paths must be relative bundle paths".into());
    }
    std::fs::canonicalize(root.join(name))
        .map_err(|e| format!("Rust frontend bundle is incomplete (`{name}`): {e}"))
}

impl Runtime {
    fn legacy(path: &Path) -> Result<Self, String> {
        let executable = std::fs::canonicalize(path)
            .map_err(|e| format!("Rust frontend `{}`: {e}", path.display()))?;
        let driver = executable.with_file_name(if cfg!(windows) {
            "charon-driver.exe"
        } else {
            "charon-driver"
        });
        if !driver.is_file() {
            return Err(format!(
                "Rust source-built frontend is missing its paired driver at `{}`",
                driver.display()
            ));
        }
        let environment: BTreeMap<_, _> = [
            "PATH",
            "HOME",
            "RUSTUP_HOME",
            "CARGO_HOME",
            "RUST_MIN_STACK",
        ]
        .into_iter()
        .filter_map(|key| std::env::var(key).ok().map(|v| (key.to_string(), v)))
        .collect();
        let compiler = std::env::split_paths(
            environment.get("PATH").ok_or("development Charon runtime needs PATH")?,
        )
        .map(|p| p.join(if cfg!(windows) { "rustup.exe" } else { "rustup" }))
        .find(|p| p.is_file())
        .ok_or("development Charon runtime needs rustup; use an installed Rust frontend bundle to extract without rustup")?;
        Ok(Self {
            driver,
            executable,
            environment,
            compiler,
            compiler_prefix: vec![
                "run".into(),
                profile::get().toolchain.clone(),
                "rustc".into(),
            ],
            sysroot: None,
            recovery: String::new(),
        })
    }

    pub(super) fn bundle(root: &Path) -> Result<Self, String> {
        use std::io::Read;
        let mut bytes = Vec::new();
        std::fs::File::open(root.join("frontend.json"))
            .map_err(|e| format!("read Rust frontend manifest: {e}"))?
            .take((64 << 10) + 1)
            .read_to_end(&mut bytes)
            .map_err(|e| e.to_string())?;
        if bytes.len() > 64 << 10 {
            return Err("Rust frontend manifest exceeds its byte bound".into());
        }
        let m: Manifest =
            serde_json::from_slice(&bytes).map_err(|e| format!("Rust frontend manifest: {e}"))?;
        let p = profile::get();
        if m.schema != 1
            || m.click_version != VERSION
            || m.extractor_revision != p.extractor_revision
            || m.extractor_version != p.extractor_version
            || m.compiler_commit != p.compiler_commit
        {
            return Err(format!(
                "Rust frontend version mismatch; expected bundle schema 1 for Click {VERSION}, Charon {} ({}), rustc {}; got schema {}, Click {}, Charon {} ({}), rustc {}",
                p.extractor_version,
                p.extractor_revision,
                p.compiler_commit,
                m.schema,
                short_identity(&m.click_version),
                short_identity(&m.extractor_version),
                short_identity(&m.extractor_revision),
                short_identity(&m.compiler_commit)
            ));
        }
        if m.host != HOST
            || !cfg!(all(
                target_os = "linux",
                target_arch = "x86_64",
                target_env = "gnu"
            ))
        {
            return Err(format!(
                "this Rust frontend bundle requires host {HOST}; this Click runs on {}/{}",
                std::env::consts::OS,
                std::env::consts::ARCH
            ));
        }
        let executable = bundled_path(root, &m.charon)?;
        let driver = bundled_path(root, &m.driver)?;
        // The pinned Charon wrapper launches its sibling driver. The manifest
        // must explicitly name that same file; it cannot silently select another.
        if driver
            != std::fs::canonicalize(executable.with_file_name("charon-driver"))
                .map_err(|e| format!("Rust frontend Charon/driver layout: {e}"))?
        {
            return Err("Rust frontend manifest driver differs from Charon's paired driver".into());
        }
        let compiler = bundled_path(root, &m.rustc)?;
        let sysroot = bundled_path(root, &m.sysroot)?;
        if !sysroot.join("lib/rustlib").join(HOST).join("lib").is_dir() {
            return Err("Rust frontend bundle lacks the pinned target libraries".into());
        }
        let environment = BTreeMap::from([
            (
                "PATH".into(),
                compiler.parent().unwrap().to_string_lossy().into_owned(),
            ),
            (
                "LD_LIBRARY_PATH".into(),
                sysroot.join("lib").to_string_lossy().into_owned(),
            ),
            ("CHARON_TOOLCHAIN_IS_IN_PATH".into(), "1".into()),
        ]);
        Ok(Self {
            executable,
            driver,
            environment,
            compiler,
            compiler_prefix: vec![],
            sysroot: Some(sysroot),
            recovery: String::new(),
        })
    }

    pub(super) fn compiler_args(&self, args: &[String]) -> Vec<String> {
        let mut result = self.compiler_prefix.clone();
        result.extend_from_slice(args);
        if let Some(sysroot) = &self.sysroot {
            result.push(format!("--sysroot={}", sysroot.display()));
        }
        result
    }

    pub(super) fn run_rustc(
        &self,
        args: &[String],
        root: &Path,
        limits: CompilerLimits,
    ) -> Result<crate::languages::compiler_process::CompilerOutput, String> {
        run_compiler(
            &self.compiler,
            &self.compiler_args(args),
            root,
            &self.environment,
            limits,
        )
    }

    pub(super) fn check(&self, root: &Path, limits: CompilerLimits) -> Result<(), String> {
        self.check_identity(root, limits)
            .map_err(|error| format!("{error}. {}", self.recovery))
    }

    fn check_identity(&self, root: &Path, limits: CompilerLimits) -> Result<(), String> {
        let p = profile::get();
        let version = run_compiler(
            &self.executable,
            &["version".into()],
            root,
            &self.environment,
            limits,
        )?;
        if String::from_utf8_lossy(&version.stdout).trim()
            != format!("{} ({})", p.extractor_version, p.extractor_revision)
        {
            return Err(format!(
                "Rust frontend version mismatch; expected Charon {} ({}), got {:?}",
                p.extractor_version,
                p.extractor_revision,
                String::from_utf8_lossy(&version.stdout)
                    .trim()
                    .chars()
                    .take(160)
                    .collect::<String>()
            ));
        }
        let expected = format!("commit-hash: {}", p.compiler_commit);
        let compiler = self.run_rustc(&["-vV".into()], root, limits)?;
        if !String::from_utf8_lossy(&compiler.stdout)
            .lines()
            .any(|s| s == expected)
        {
            return Err(format!(
                "Rust frontend compiler version mismatch; expected rustc {}, got {}",
                p.compiler_commit,
                reported_commit(&compiler.stdout)
            ));
        }
        if self.sysroot.is_some() {
            let driver = run_compiler(
                &self.driver,
                &["rustc".into(), "-vV".into()],
                root,
                &self.environment,
                limits,
            )?;
            if !String::from_utf8_lossy(&driver.stdout)
                .lines()
                .any(|s| s == expected)
            {
                return Err(format!(
                    "Rust frontend driver version mismatch; expected rustc {}, got {}",
                    p.compiler_commit,
                    reported_commit(&driver.stdout)
                ));
            }
        }
        Ok(())
    }
}

fn reported_commit(bytes: &[u8]) -> String {
    String::from_utf8_lossy(bytes)
        .lines()
        .find_map(|line| line.strip_prefix("commit-hash: "))
        .map_or_else(
            || "no compiler commit reported".into(),
            |s| format!("{:?}", s.chars().take(160).collect::<String>()),
        )
}

fn short_identity(value: &str) -> String {
    format!("{:?}", value.chars().take(160).collect::<String>())
}
