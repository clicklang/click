use std::path::{Path, PathBuf};

use click::project::{FILE_NAME, Project};

const USAGE: &str = "usage: click capture [<project-dir> | <source>... | <sidecar.click>]\n\nRecords compiler output under .click/captures/. With no paths, captures the current project.";

pub(crate) fn entry_with(arguments: impl IntoIterator<Item = String>) -> Result<(), String> {
    let arguments = arguments.into_iter().collect::<Vec<_>>();
    if matches!(arguments.as_slice(), [argument] if argument == "-h" || argument == "--help") {
        println!("{USAGE}");
        return Ok(());
    }
    let explicit_paths = arguments.first().is_some_and(|arg| arg == "--");
    let paths = &arguments[usize::from(explicit_paths)..];
    if paths
        .iter()
        .any(|path| path.is_empty() || (!explicit_paths && path.starts_with('-')))
    {
        return Err(USAGE.into());
    }
    match paths {
        [] => find_project(Path::new("."))?.lock(),
        [path] if Path::new(path).is_dir() => find_project(Path::new(path))?.lock(),
        [path]
            if Path::new(path)
                .file_name()
                .is_some_and(|name| name == FILE_NAME) =>
        {
            find_project(click::cli::containing_directory(Path::new(path)))?.lock()
        }
        [path]
            if Path::new(path)
                .extension()
                .is_some_and(|ext| ext == "click") =>
        {
            click::cli::capture_sidecar(Path::new(path))
        }
        _ => {
            let paths = paths.iter().map(PathBuf::from).collect::<Vec<_>>();
            let directory = click::cli::containing_directory(&paths[0]);
            let project = match Project::find(directory)? {
                Some(project) => project,
                None => find_project(Path::new("."))?,
            };
            project.capture_sources(&paths)
        }
    }
}

fn find_project(directory: &Path) -> Result<Project, String> {
    Project::find(directory)?.ok_or_else(|| {
        format!(
            "no `{FILE_NAME}` in `{}` or any directory above it",
            directory.display()
        )
    })
}
