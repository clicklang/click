//! Comparing a checked-in C++ import (its lock and semantic artifacts) with a
//! fresh export by the pinned exporter, for the import freshness checks of
//! `tests/mdtests.rs` and the cross-language integer fixture in
//! `tests/examples/integer_languages.rs`.

use std::fs;
use std::path::{Path, PathBuf};

/// Whether two imports hold the same lock and artifacts apart from which
/// build of the pinned toolchain exported them. Every machine builds its own
/// exporter, whose digest and the identities derived from it differ, and the
/// pinned Clang 19.1.7 may be packaged differently (a source build or a
/// distribution package of the same release), which only its version string
/// records. The artifacts themselves are compared, so the lock's record of
/// their digest and size is left out too.
pub(crate) fn same_import(
    left: &std::collections::BTreeMap<PathBuf, Vec<u8>>,
    right: &std::collections::BTreeMap<PathBuf, Vec<u8>>,
) -> bool {
    fn without_build_provenance(value: &mut serde_json::Value) {
        match value {
            serde_json::Value::Object(fields) => {
                for (name, field) in fields.iter_mut() {
                    match (name.as_str(), &*field) {
                        ("identity" | "unit", serde_json::Value::String(_)) => {
                            *field = serde_json::Value::Null;
                        }
                        ("frontend_version", serde_json::Value::String(version))
                            if version.contains("clang version 19.1.7 ") =>
                        {
                            *field = serde_json::Value::Null;
                        }
                        ("artifact", serde_json::Value::Object(record)) => {
                            let path = record.get("path").cloned();
                            *field = serde_json::json!({ "path": path });
                        }
                        _ => without_build_provenance(field),
                    }
                }
            }
            serde_json::Value::Array(items) => items.iter_mut().for_each(without_build_provenance),
            _ => {}
        }
    }
    let normalized = |bytes: &[u8]| {
        let mut value = serde_json::from_slice::<serde_json::Value>(bytes).ok()?;
        without_build_provenance(&mut value);
        Some(value)
    };
    left.len() == right.len()
        && left
            .iter()
            .zip(right)
            .all(|((left_path, left_bytes), (right_path, right_bytes))| {
                left_path == right_path
                    && normalized(left_bytes)
                        .is_some_and(|left| Some(left) == normalized(right_bytes))
            })
}

/// Where a checked-in import first differs from a fresh export, for the
/// freshness failure message.
pub(crate) fn first_import_difference(
    checked_in: &std::collections::BTreeMap<PathBuf, Vec<u8>>,
    exported: &std::collections::BTreeMap<PathBuf, Vec<u8>>,
) -> String {
    for path in checked_in.keys().chain(exported.keys()) {
        let (Some(old), Some(new)) = (checked_in.get(path), exported.get(path)) else {
            return format!("only one side has `{}`", path.display());
        };
        if old == new {
            continue;
        }
        let at = old.iter().zip(new).take_while(|(a, b)| a == b).count();
        let context = |bytes: &[u8]| {
            let start = at.saturating_sub(80);
            String::from_utf8_lossy(&bytes[start..(at + 80).min(bytes.len())]).into_owned()
        };
        return format!(
            "`{}` differs at byte {at}\n    checked in: {}\n    exported:   {}",
            path.display(),
            context(old),
            context(new)
        );
    }
    "the lock differs only in its exporter identity".into()
}

/// The files under `directory`, by their paths inside it.
#[allow(dead_code)] // Used by the mdtest import check, not the integer fixture.
pub(crate) fn checked_in_files(directory: &Path) -> std::collections::BTreeMap<PathBuf, Vec<u8>> {
    let mut files = std::collections::BTreeMap::new();
    let mut pending = vec![PathBuf::new()];
    while let Some(relative) = pending.pop() {
        for entry in fs::read_dir(directory.join(&relative))
            .into_iter()
            .flatten()
        {
            let entry = entry.unwrap();
            let child = relative.join(entry.file_name());
            if entry.file_type().unwrap().is_dir() {
                pending.push(child);
            } else {
                files.insert(child.clone(), fs::read(directory.join(&child)).unwrap());
            }
        }
    }
    files
}
