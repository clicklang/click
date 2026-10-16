#![allow(dead_code)]
//! C++ test fixtures describe an import in the per-sidecar config format of
//! earlier releases: a JSON description naming a compilation database, the
//! selected source and function, and a profile. Click reads only project
//! units, so these helpers translate a description into the equivalent unit
//! of a `click.project.json` beside it, named by the description file's stem,
//! and lock or load it through `click::project::Project`.

use std::fs;
use std::path::{Path, PathBuf};

use click::languages::cpp::PreparedCppImport;

/// The unit a description translates to: the description file's name up to
/// its first `.`.
pub fn unit_name(description: &Path) -> String {
    let name = description.file_name().unwrap().to_str().unwrap();
    name.split('.').next().unwrap().to_string()
}

fn read_json(path: &Path, label: &str) -> Result<serde_json::Value, String> {
    let bytes = fs::read(path).map_err(|error| format!("read {label}: {error}"))?;
    serde_json::from_slice(&bytes).map_err(|error| format!("parse {label}: {error}"))
}

fn root(description: &Path, config: &serde_json::Value) -> PathBuf {
    description
        .parent()
        .unwrap()
        .join(config["working_directory"].as_str().unwrap_or("."))
}

/// Writes the description's unit into the project file beside it and returns
/// the project file, the description's exporter and its logical source.
pub fn describe_project(description: &Path) -> Result<(PathBuf, PathBuf, String), String> {
    let directory = description.parent().unwrap();
    let config = read_json(description, "import description")?;
    let root = root(description, &config);
    let database = read_json(
        &directory.join(config["compilation_database"].as_str().unwrap()),
        "C++ compilation database",
    )?;
    let commands = database.as_array().unwrap();
    if commands.len() != 1 {
        return Err(format!(
            "C++ compilation database has {} commands; exactly one is required",
            commands.len()
        ));
    }
    let words: Vec<String> = match commands[0].get("arguments") {
        Some(arguments) => arguments
            .as_array()
            .unwrap()
            .iter()
            .map(|argument| argument.as_str().unwrap().to_string())
            .collect(),
        None => commands[0]["command"]
            .as_str()
            .unwrap()
            .split_whitespace()
            .map(str::to_string)
            .collect(),
    };
    // Paths under the unit root become relative to it, as a unit states them.
    let prefixes = [
        root.clone(),
        fs::canonicalize(&root).unwrap_or(root.clone()),
    ]
    .map(|prefix| format!("{}/", prefix.to_string_lossy().trim_end_matches("/.")));
    let mut words = words.into_iter().skip(1);
    let mut args = Vec::new();
    while let Some(word) = words.next() {
        match word.as_str() {
            "-x" | "-c" | "-o" => {
                words.next();
            }
            "-fexceptions" | "-fno-exceptions" | "-frtti" | "-fno-rtti" => {}
            _ if word.starts_with("-std=")
                || word.starts_with("--target=")
                || word.starts_with("-resource-dir=") => {}
            _ => {
                let mut word = word;
                for prefix in &prefixes {
                    word = word.replace(prefix.as_str(), "");
                }
                args.push(word);
            }
        }
    }
    let logical = config["logical_source"].as_str().unwrap().to_string();
    let mut source = serde_json::json!({
        "functions": [config["function"]],
        "dependencies": config["dependencies"],
    });
    if !config["exception_behavior"].is_null() {
        source["exception_behavior"] = config["exception_behavior"].clone();
    }
    if config["source"] != config["logical_source"] {
        source["translation_unit"] = config["source"].clone();
    }
    if let Some(assertions) = config.get("library_assertions") {
        source["library_assertions"] = assertions.clone();
    }
    let mut unit = serde_json::json!({
        "language": "c++",
        "exceptions": config["exceptions"],
        "rtti": config["rtti"],
        "args": args,
        "sources": {&logical: source},
    });
    if let Some(root) = config["working_directory"]
        .as_str()
        .filter(|root| *root != ".")
    {
        unit["root"] = root.into();
    }
    let project_file = directory.join(click::project::FILE_NAME);
    fs::write(
        &project_file,
        serde_json::to_vec_pretty(&serde_json::json!({"units": {unit_name(description): unit}}))
            .unwrap(),
    )
    .unwrap();
    let exporter = directory.join(config["exporter"].as_str().unwrap());
    Ok((project_file, exporter, logical))
}

/// Locks the described unit, with `fallback` when the description's own
/// exporter is gone.
pub fn lock_description(description: &Path, fallback: Option<PathBuf>) -> Result<(), String> {
    let (project_file, exporter, _) = describe_project(description)?;
    let exporter = match fallback {
        Some(fallback) if !exporter.exists() => fallback,
        _ => exporter,
    };
    click::project::Project::load(&project_file)?.lock_with_cpp_exporter(Some(&exporter))
}

/// Prepares the described import as its project's unit.
pub fn refresh_import(description: &Path) -> Result<(), String> {
    lock_description(description, None)
}

/// Loads the described import's locked unit without the exporter.
pub fn load_import(description: &Path) -> Result<PreparedCppImport, String> {
    let (project_file, _, logical) = describe_project(description)?;
    let config = read_json(description, "import description")?;
    let path = fs::canonicalize(root(description, &config).join(&logical)).ok();
    match click::project::Project::load(&project_file)?.prepared_sources(&[(logical, path)])? {
        Some(click::project::UnitSelection::Program(click::languages::PreparedProgram::Cpp(
            import,
        ))) => Ok(import),
        _ => Err("expected the prepared C++ unit".into()),
    }
}

/// The described unit's artifact for its logical source.
pub fn artifact(description: &Path) -> PathBuf {
    let config = read_json(description, "import description").unwrap();
    description.parent().unwrap().join(format!(
        ".click/{}/{}.click-cpp.json",
        unit_name(description),
        config["logical_source"].as_str().unwrap()
    ))
}

/// A unit's one source entry in a project lock.
pub fn lock_entry(lock: &serde_json::Value) -> &serde_json::Value {
    let units = lock["units"].as_object().unwrap();
    assert_eq!(units.len(), 1, "a fixture's project has one unit");
    units.values().next().unwrap()["lock"]
        .as_object()
        .unwrap()
        .values()
        .next()
        .unwrap()
}

pub fn lock_entry_mut(lock: &mut serde_json::Value) -> &mut serde_json::Value {
    let units = lock["units"].as_object_mut().unwrap();
    assert_eq!(units.len(), 1, "a fixture's project has one unit");
    units.values_mut().next().unwrap()["lock"]
        .as_object_mut()
        .unwrap()
        .values_mut()
        .next()
        .unwrap()
}

/// The digest a project lock records for the described unit: its
/// description as written and the project's default target.
#[allow(dead_code)]
pub fn unit_digest(description: &Path) -> String {
    use sha2::{Digest, Sha256};
    let (project_file, _, _) = describe_project(description).unwrap();
    let project = read_json(&project_file, "project file").unwrap();
    let data = serde_json::to_vec(&serde_json::json!({
        "target": "x86_64-unknown-linux-gnu",
        "unit": project["units"][unit_name(description)],
    }))
    .unwrap();
    format!("{:x}", Sha256::digest(&data))
}
