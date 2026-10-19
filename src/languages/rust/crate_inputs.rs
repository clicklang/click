//! Versioned crate inputs; source closure comes from rustc dep-info, not names.
pub(super) const PROFILE_ID: &str = "click-charon-crate-v4";

use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, BTreeSet};
use std::path::{Component, Path, PathBuf};

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct CrateConfig {
    pub name: String,
    pub edition: String,
    pub features: Vec<String>,
    pub roots: Vec<String>,
    pub files: Vec<String>,
}
impl CrateConfig {
    pub fn validate(&self, source: &str) -> Result<(), String> {
        fn ident(s: &str) -> bool {
            !s.is_empty()
                && s.bytes().enumerate().all(|(i, b)| {
                    b == b'_' || b.is_ascii_alphabetic() || (i > 0 && b.is_ascii_digit())
                })
        }
        fn unique(xs: &[String]) -> bool {
            xs.iter().collect::<BTreeSet<_>>().len() == xs.len()
        }
        if !ident(&self.name)
            || !matches!(self.edition.as_str(), "2021" | "2024")
            || self.features.len() > 32
            || self.roots.is_empty()
            || self.roots.len() > 64
            || self.files.is_empty()
            || self.files.len() > 64
            || !unique(&self.features)
            || !unique(&self.roots)
            || !unique(&self.files)
            || !self.files.iter().any(|f| f == source)
            || self.features.iter().any(|f| {
                f.is_empty()
                    || !f
                        .bytes()
                        .all(|b| b.is_ascii_alphanumeric() || b == b'_' || b == b'-')
            })
            || self
                .roots
                .iter()
                .any(|r| !r.starts_with(&format!("{}::", self.name)) || !r.split("::").all(ident))
        {
            return Err("invalid Rust crate name/edition/features/roots/files".into());
        }
        Ok(())
    }
    pub fn flags(&self) -> Vec<String> {
        let mut flags = super::profile::get().flags.clone();
        flags.retain(|f| !f.starts_with("--edition="));
        flags.push(format!("--edition={}", self.edition));
        for feature in &self.features {
            flags.extend(["--cfg".into(), format!("feature=\"{feature}\"")]);
        }
        flags
    }
}

pub(super) fn file(root: &Path, name: &str) -> Result<PathBuf, String> {
    let relative = Path::new(name);
    if name.is_empty()
        || !relative
            .components()
            .all(|c| matches!(c, Component::Normal(_)))
    {
        return Err("Rust crate inputs must stay inside the import directory".into());
    }
    let normalized: PathBuf = relative.components().collect();
    if normalized.as_os_str() != relative.as_os_str() {
        return Err("Rust crate input paths must be normalized".into());
    }
    let mut path = root.to_path_buf();
    for component in relative.components() {
        path.push(component);
        let metadata = std::fs::symlink_metadata(&path)
            .map_err(|e| format!("Rust crate input `{name}`: {e}"))?;
        if metadata.file_type().is_symlink() {
            return Err("Rust crate inputs cannot use symlinks".into());
        }
    }
    Ok(path)
}

pub(super) fn dep_files(bytes: &[u8], root: &Path) -> Result<BTreeSet<String>, String> {
    let text = std::str::from_utf8(bytes).map_err(|_| "Rust dep-info is not UTF-8")?;
    if text.lines().any(|l| l.starts_with("# env-dep:")) {
        return Err("Rust crate environment-dependent source is unsupported".into());
    }
    let first = text.lines().next().ok_or("missing Rust dep-info")?;
    let (_, dependencies) = first.split_once(": ").ok_or("invalid Rust dep-info")?;
    let mut tokens = Vec::new();
    let mut token = String::new();
    let mut escaped = false;
    for ch in dependencies.chars() {
        if escaped {
            token.push(ch);
            escaped = false;
        } else if ch == '\\' {
            escaped = true;
        } else if ch.is_whitespace() {
            if !token.is_empty() {
                tokens.push(std::mem::take(&mut token));
            }
        } else {
            token.push(ch);
        }
    }
    if escaped {
        return Err("invalid Rust dep-info escape".into());
    }
    if !token.is_empty() {
        tokens.push(token);
    }
    let mut files = BTreeSet::new();
    for token in tokens {
        let path = Path::new(&token);
        let path = if path.is_absolute() {
            path.to_path_buf()
        } else {
            root.join(path)
        };
        let relative = path
            .strip_prefix(root)
            .map_err(|_| "Rust compiler read a file outside the locked crate")?;
        let relative = resolve_parents(root, relative)?;
        let name = relative
            .to_str()
            .ok_or("Rust crate path is not UTF-8")?
            .to_string();
        file(root, &name)?;
        if !files.insert(name) {
            return Err("duplicate Rust dep-info input".into());
        }
    }
    if files.is_empty() {
        return Err("empty Rust source closure".into());
    }
    Ok(files)
}

/// Resolves the `..` components of a path the compiler reports relative to
/// the crate root, as a `#[path = "../shared/lib.rs"]` attribute produces.
/// A `..` is resolved only after the component it steps back over has been
/// found to be a directory and not a symbolic link, so the textual result
/// names the file the compiler opened; a path that climbs above the root is
/// outside the crate.
pub(super) fn resolve_parents(root: &Path, relative: &Path) -> Result<PathBuf, String> {
    let mut resolved = PathBuf::new();
    for component in relative.components() {
        match component {
            Component::Normal(name) => resolved.push(name),
            Component::CurDir => {}
            Component::ParentDir => {
                let metadata = std::fs::symlink_metadata(root.join(&resolved))
                    .map_err(|e| format!("Rust crate input `{}`: {e}", relative.display()))?;
                if !metadata.is_dir() {
                    return Err("Rust crate inputs cannot use symlinks".into());
                }
                if !resolved.pop() {
                    return Err("Rust compiler read a file outside the locked crate".into());
                }
            }
            Component::RootDir | Component::Prefix(_) => {
                return Err("Rust compiler read a file outside the locked crate".into());
            }
        }
    }
    Ok(resolved)
}

pub(super) type SourceFiles = BTreeMap<String, Vec<u8>>;

pub(super) fn check_closure(
    configured: &[String],
    observed: &BTreeSet<String>,
) -> Result<(), String> {
    let configured: BTreeSet<_> = configured.iter().cloned().collect();
    if &configured == observed {
        return Ok(());
    }
    fn names<'a>(paths: impl Iterator<Item = &'a String>) -> String {
        let paths: Vec<_> = paths.collect();
        if paths.is_empty() {
            return "none".into();
        }
        let mut shown: Vec<_> = paths
            .iter()
            .take(12)
            .map(|name| {
                let mut escaped = name.chars().flat_map(char::escape_default);
                let snippet: String = escaped.by_ref().take(160).collect();
                format!(
                    "\"{snippet}{}\"",
                    if escaped.next().is_some() { "..." } else { "" }
                )
            })
            .collect();
        if paths.len() > 12 {
            shown.push(format!("and {} more", paths.len() - 12));
        }
        shown.join(", ")
    }
    Err(format!(
        "Rust compiler source closure differs from configured crate files; missing from `crate.files`: {}; extra in `crate.files`: {}. Update `crate.files` and run `click import lock`",
        names(observed.difference(&configured)),
        names(configured.difference(observed))
    ))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn crate_closure_diagnostic_names_missing_and_extra_inputs_and_bounds_lists() {
        let configured = vec!["lib.rs".into(), "unused.rs".into()];
        let observed = BTreeSet::from(["lib.rs".into(), "module.rs".into()]);
        let error = check_closure(&configured, &observed).unwrap_err();
        assert!(
            error.contains("missing from `crate.files`: \"module.rs\""),
            "{error}"
        );
        assert!(
            error.contains("extra in `crate.files`: \"unused.rs\""),
            "{error}"
        );
        assert!(check_closure(&configured, &configured.iter().cloned().collect()).is_ok());
        let many = (0..64)
            .map(|i| format!("{i:02}-{}", "\n".repeat(1000)))
            .collect();
        let error = check_closure(&[], &many).unwrap_err();
        assert!(error.len() < 4096);
        assert!(error.contains("and 52 more"));
        assert!(!error.contains('\n'));
    }

    #[test]
    fn dep_info_checks_escaped_paths_and_rejects_environment_inputs() {
        let root = tempfile::tempdir().unwrap();
        std::fs::write(root.path().join("with space.rs"), "pub fn entry() {}\n").unwrap();
        let dependency = format!("out.d: {}/with\\ space.rs\n\n", root.path().display());
        assert_eq!(
            dep_files(dependency.as_bytes(), root.path()).unwrap(),
            BTreeSet::from(["with space.rs".to_string()])
        );
        let environment = format!("{dependency}# env-dep:HOME=/somewhere\n");
        assert!(
            dep_files(environment.as_bytes(), root.path())
                .unwrap_err()
                .contains("environment-dependent")
        );
        assert!(
            dep_files(b"out.d: /outside.rs\n", root.path())
                .unwrap_err()
                .contains("outside the locked crate")
        );
    }

    /// A `#[path]` attribute that steps up from a client crate's directory to
    /// a shared library is resolved through real directories only.
    #[test]
    fn dep_info_resolves_parent_steps_through_real_directories() {
        let root = tempfile::tempdir().unwrap();
        let root = root.path();
        std::fs::create_dir_all(root.join("client")).unwrap();
        std::fs::create_dir_all(root.join("vendor/lib/src")).unwrap();
        std::fs::write(root.join("client/main.rs"), "").unwrap();
        std::fs::write(root.join("vendor/lib/src/lib.rs"), "").unwrap();
        let dependency = format!(
            "out.d: {0}/client/main.rs {0}/client/../vendor/lib/src/lib.rs\n",
            root.display()
        );
        assert_eq!(
            dep_files(dependency.as_bytes(), root).unwrap(),
            BTreeSet::from([
                "client/main.rs".to_string(),
                "vendor/lib/src/lib.rs".to_string()
            ])
        );
        let escape = format!("out.d: {0}/client/../../outside.rs\n", root.display());
        assert!(
            dep_files(escape.as_bytes(), root)
                .unwrap_err()
                .contains("outside the locked crate")
        );
        // A `..` after a symbolic link would name a different file than the
        // one the compiler opened.
        std::os::unix::fs::symlink(root.join("vendor/lib/src"), root.join("link")).unwrap();
        let through_link = format!("out.d: {0}/link/../src/lib.rs\n", root.display());
        assert!(
            dep_files(through_link.as_bytes(), root)
                .unwrap_err()
                .contains("symlinks")
        );
    }
}
