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
}

pub(super) fn resolve(legacy: Option<&Path>) -> Result<Runtime, String> {
    if let Some(path) = legacy {
        return Runtime::legacy(path);
    }
    if let Some(path) = std::env::var_os("CLICK_CHARON").filter(|s| !s.is_empty()) {
        let path = PathBuf::from(path);
        return if path.is_dir() {
            Runtime::bundle(&path)
        } else {
            Runtime::legacy(&path)
        };
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
    if !bundle.join("frontend.json").is_file() {
        return Err(format!(
            "Rust frontend is not installed for Click {VERSION} ({}/{}); run `click install {VERSION} --rust` to install its pinned bundle at `{}`. CLICK_CHARON is a development override",
            std::env::consts::OS,
            std::env::consts::ARCH,
            bundle.display()
        ));
    }
    Runtime::bundle(&bundle)
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
            driver: executable.with_file_name(if cfg!(windows) {
                "charon-driver.exe"
            } else {
                "charon-driver"
            }),
            executable,
            environment,
            compiler,
            compiler_prefix: vec![
                "run".into(),
                profile::get().toolchain.clone(),
                "rustc".into(),
            ],
            sysroot: None,
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
                "Rust frontend version mismatch; expected Click {VERSION}, Charon {} ({}), rustc {}",
                p.extractor_version, p.extractor_revision, p.compiler_commit
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
                "Rust frontend version mismatch; expected Charon {} ({})",
                p.extractor_version, p.extractor_revision
            ));
        }
        let expected = format!("commit-hash: {}", p.compiler_commit);
        let compiler = self.run_rustc(&["-vV".into()], root, limits)?;
        if !String::from_utf8_lossy(&compiler.stdout)
            .lines()
            .any(|s| s == expected)
        {
            return Err(format!(
                "Rust frontend compiler version mismatch; expected rustc {}",
                p.compiler_commit
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
                    "Rust frontend driver version mismatch; expected rustc {}",
                    p.compiler_commit
                ));
            }
        }
        Ok(())
    }
}
