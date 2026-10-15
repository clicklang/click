use std::path::{Path, PathBuf};

use click::project::{FILE_NAME, Project};

const USAGE: &str = "usage: click import lock [<project-dir> | <sidecar.click>]\n\nPrepares the units of the nearest `click.project.json` into its lock; a sidecar names its project.";

/// What `click import lock` prepares.
#[derive(Debug, PartialEq, Eq)]
enum LockTarget {
    /// The project found from this directory.
    Project(PathBuf),
    /// A sidecar: its project.
    Sidecar(PathBuf),
}

pub(crate) fn entry_with(arguments: impl IntoIterator<Item = String>) -> Result<(), String> {
    let arguments = arguments.into_iter().collect::<Vec<_>>();
    if matches!(arguments.as_slice(), [argument] if argument == "-h" || argument == "--help") {
        println!("{USAGE}");
        return Ok(());
    }
    match parse_arguments(arguments)? {
        LockTarget::Project(directory) => lock_project(&directory),
        LockTarget::Sidecar(sidecar) => {
            let config = import_config_path(&sidecar);
            if config.exists() {
                return Err(click::cli::per_sidecar_config_refusal(&config));
            }
            match Project::find(click::cli::containing_directory(&sidecar))? {
                Some(project) if project.has_units() => project.lock(),
                _ => Err(format!(
                    "`{}` is not in a project with units; declare its sources as a unit of a `{FILE_NAME}` at the project root",
                    sidecar.display()
                )),
            }
        }
    }
}

fn lock_project(directory: &Path) -> Result<(), String> {
    match Project::find(directory)? {
        Some(project) => project.lock(),
        None => Err(format!(
            "no `{FILE_NAME}` in `{}` or any directory above it",
            directory.display()
        )),
    }
}

fn parse_arguments(arguments: impl IntoIterator<Item = String>) -> Result<LockTarget, String> {
    let arguments = arguments.into_iter().collect::<Vec<_>>();
    let (command, target, positional) = match arguments.as_slice() {
        [command] => return lock_command(command).map(|()| LockTarget::Project(".".into())),
        [command, separator, target] if separator == "--" => (command, target, true),
        [command, target] => (command, target, false),
        _ => {
            return Err(format!(
                "expected `lock [<project-dir> | <sidecar.click>]`\n{USAGE}"
            ));
        }
    };
    lock_command(command)?;
    if target.is_empty() || (!positional && target.starts_with('-')) {
        return Err("the project directory or sidecar.click path must be a non-option path".into());
    }
    let path = PathBuf::from(target);
    if path.is_dir() {
        return Ok(LockTarget::Project(path));
    }
    if path.file_name().is_some_and(|name| name == FILE_NAME) {
        return Ok(LockTarget::Project(
            click::cli::containing_directory(&path).to_path_buf(),
        ));
    }
    Ok(LockTarget::Sidecar(path))
}

fn lock_command(command: &str) -> Result<(), String> {
    if command != "lock" {
        return Err(format!("unsupported import command `{command}`\n{USAGE}"));
    }
    Ok(())
}

fn import_config_path(sidecar: &Path) -> PathBuf {
    let name = sidecar
        .file_name()
        .and_then(|name| name.to_str())
        .unwrap_or_default();
    sidecar.with_file_name(format!("{name}.import.json"))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn derives_fixed_import_config_name() {
        assert_eq!(
            import_config_path(Path::new("demo/sidecar.click")),
            PathBuf::from("demo/sidecar.click.import.json")
        );
    }

    #[test]
    fn requires_lock_command() {
        assert!(parse_arguments(Vec::<String>::new()).is_err());
        assert!(parse_arguments(["refresh".into(), "demo.click".into()]).is_err());
        assert_eq!(
            parse_arguments(["lock".into(), "demo.click".into()]).unwrap(),
            LockTarget::Sidecar(PathBuf::from("demo.click"))
        );
        assert_eq!(
            parse_arguments(["lock".into()]).unwrap(),
            LockTarget::Project(PathBuf::from("."))
        );
        assert_eq!(
            parse_arguments(["lock".into(), "demo/click.project.json".into()]).unwrap(),
            LockTarget::Project(PathBuf::from("demo"))
        );
    }
}
