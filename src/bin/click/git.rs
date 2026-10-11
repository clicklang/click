//! Git queries shared by `click verify` and `click audit` for incremental
//! (`--changed-since`) runs.

use std::path::{Path, PathBuf};
use std::process::Command;

use click::cli::containing_directory;

pub(crate) fn git_repo_root(path: &Path) -> Result<PathBuf, String> {
    let anchor = if path.is_dir() {
        path
    } else {
        containing_directory(path)
    };
    let output = Command::new("git")
        .args([
            "-C",
            &anchor.display().to_string(),
            "rev-parse",
            "--show-toplevel",
        ])
        .output()
        .map_err(|error| format!("failed to run git: {error}"))?;
    if !output.status.success() {
        return Err(format!(
            "`{}` is not inside a readable git worktree",
            path.display()
        ));
    }
    Ok(PathBuf::from(
        String::from_utf8_lossy(&output.stdout).trim(),
    ))
}

pub(crate) fn git_commit_id(repo: &Path, revision: &str) -> Result<String, String> {
    let output = Command::new("git")
        .args([
            "-C",
            &repo.display().to_string(),
            "rev-parse",
            "--verify",
            &format!("{revision}^{{commit}}"),
        ])
        .output()
        .map_err(|error| format!("failed to run git: {error}"))?;
    if output.status.success() {
        Ok(String::from_utf8_lossy(&output.stdout).trim().to_string())
    } else {
        Err(format!("unknown git revision `{revision}`"))
    }
}

pub(crate) fn git_show(repo: &Path, revision: &str, path: &Path) -> Result<Option<String>, String> {
    let relative = path.strip_prefix(repo).map_err(|_| {
        format!(
            "`{}` is outside git worktree `{}`",
            path.display(),
            repo.display()
        )
    })?;
    let spec = format!("{revision}:{}", relative.display());
    let output = Command::new("git")
        .args(["-C", &repo.display().to_string(), "show", &spec])
        .output()
        .map_err(|error| format!("failed to run git: {error}"))?;
    if output.status.success() {
        Ok(Some(String::from_utf8_lossy(&output.stdout).into_owned()))
    } else {
        Ok(None)
    }
}
