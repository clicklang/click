//! Input handling shared by the importers and the project file: bounded
//! reads of regular files, stable re-reads, digests, and the check that no
//! output a lock writes is one of its inputs. Each importer chooses its own
//! limits and labels; the behavior behind them is the same.

use std::fs::{self, File, OpenOptions};
use std::io::Read;
use std::path::{Path, PathBuf};

use sha2::{Digest, Sha256};

/// Whether a read accepts a path whose final component is a symbolic link.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Leaf {
    /// The link is followed; the file it names must be regular.
    Follow,
    /// The path itself must be a regular file.
    Refuse,
}

/// The lowercase hexadecimal SHA-256 of `bytes`.
pub(crate) fn hex_digest(bytes: &[u8]) -> String {
    format!("{:x}", Sha256::digest(bytes))
}

/// Opens `path` for reading after checking that it is a regular file, so a
/// FIFO or device never blocks or streams. The opened file is checked again,
/// so a file replaced after the first check is refused.
pub(crate) fn open_regular(path: &Path, label: &str, leaf: Leaf) -> Result<File, String> {
    if leaf == Leaf::Refuse {
        let metadata = fs::symlink_metadata(path)
            .map_err(|error| format!("read {label} `{}`: {error}", path.display()))?;
        if !metadata.file_type().is_file() {
            return Err(not_regular(path, label));
        }
    }
    let mut options = OpenOptions::new();
    options.read(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt;
        options.custom_flags(libc::O_NONBLOCK);
    }
    let file = options
        .open(path)
        .map_err(|error| format!("read {label} `{}`: {error}", path.display()))?;
    if !file
        .metadata()
        .map_err(|error| format!("read {label} `{}`: {error}", path.display()))?
        .is_file()
    {
        return Err(not_regular(path, label));
    }
    Ok(file)
}

fn not_regular(path: &Path, label: &str) -> String {
    format!("{label} `{}` is not a regular file", path.display())
}

/// Reads at most `limit` bytes of the regular file at `path`; a longer file
/// is refused without reading past the limit.
pub(crate) fn read_regular(
    path: &Path,
    limit: usize,
    label: &str,
    leaf: Leaf,
) -> Result<Vec<u8>, String> {
    let file = open_regular(path, label, leaf)?;
    let mut bytes = Vec::new();
    file.take(limit as u64 + 1)
        .read_to_end(&mut bytes)
        .map_err(|error| format!("read {label} `{}`: {error}", path.display()))?;
    if bytes.len() > limit {
        return Err(format!(
            "{label} `{}` exceeds its {limit}-byte limit",
            path.display()
        ));
    }
    Ok(bytes)
}

/// [`read_regular`], refusing a file whose size, modification or change
/// time, or inode differs after the read from before it.
pub(crate) fn read_stable(
    path: &Path,
    limit: usize,
    label: &str,
    leaf: Leaf,
) -> Result<Vec<u8>, String> {
    let before = signature(path, label, leaf)?;
    let bytes = read_regular(path, limit, label, leaf)?;
    if signature(path, label, leaf)? != before {
        return Err(format!(
            "{label} `{}` changed while being read",
            path.display()
        ));
    }
    Ok(bytes)
}

fn signature(path: &Path, label: &str, leaf: Leaf) -> Result<(u64, u128, u128, u64), String> {
    let metadata = match leaf {
        Leaf::Follow => fs::metadata(path),
        Leaf::Refuse => fs::symlink_metadata(path),
    }
    .map_err(|error| format!("read {label} `{}`: {error}", path.display()))?;
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt;
        let nanos = |seconds: i64, nanoseconds: i64| {
            (seconds as i128 * 1_000_000_000 + nanoseconds as i128) as u128
        };
        Ok((
            metadata.len(),
            nanos(metadata.mtime(), metadata.mtime_nsec()),
            nanos(metadata.ctime(), metadata.ctime_nsec()),
            metadata.ino(),
        ))
    }
    #[cfg(not(unix))]
    {
        let modified = metadata
            .modified()
            .ok()
            .and_then(|time| time.duration_since(std::time::UNIX_EPOCH).ok())
            .map_or(0, |time| time.as_nanos());
        Ok((metadata.len(), modified, 0, 0))
    }
}

/// The file `path` names: its canonical path, or, for a file not yet
/// written, its canonical parent joined with its name.
pub(crate) fn path_identity(path: &Path) -> Result<PathBuf, String> {
    match fs::canonicalize(path) {
        Ok(path) => return Ok(path),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
        Err(error) => return Err(format!("resolve `{}`: {error}", path.display())),
    }
    let name = path
        .file_name()
        .ok_or_else(|| format!("`{}` names no file", path.display()))?;
    let parent = match path.parent() {
        Some(parent) if !parent.as_os_str().is_empty() => parent,
        _ => Path::new("."),
    };
    let parent = fs::canonicalize(parent)
        .map_err(|error| format!("resolve `{}`: {error}", parent.display()))?;
    Ok(parent.join(name))
}

/// Refuses an output that is one of `inputs`, or another output, compared
/// by the file each path names. Each path carries a label for the message.
pub(crate) fn reject_output_collisions<'a>(
    outputs: &[(&str, &Path)],
    inputs: impl IntoIterator<Item = (&'a str, &'a Path)>,
) -> Result<(), String> {
    let outputs = outputs
        .iter()
        .map(|(label, path)| Ok((*label, path_identity(path)?)))
        .collect::<Result<Vec<_>, String>>()?;
    for (index, (label, path)) in outputs.iter().enumerate() {
        if let Some((other, _)) = outputs[..index].iter().find(|(_, other)| other == path) {
            return Err(format!(
                "the {label} output `{}` is also the {other} output",
                path.display()
            ));
        }
    }
    for (input_label, input) in inputs {
        let input = path_identity(input)?;
        if let Some((label, path)) = outputs.iter().find(|(_, output)| *output == input) {
            return Err(format!(
                "the {label} output `{}` is the {input_label} input",
                path.display()
            ));
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn scratch(name: &str) -> PathBuf {
        let directory =
            std::env::temp_dir().join(format!("click-inputs-{name}-{}", std::process::id()));
        let _ = fs::remove_dir_all(&directory);
        fs::create_dir_all(&directory).unwrap();
        fs::canonicalize(directory).unwrap()
    }

    #[test]
    fn a_read_stops_at_its_limit_and_refuses_what_is_not_a_regular_file() {
        let directory = scratch("limit");
        let file = directory.join("input");
        fs::write(&file, b"12345").unwrap();
        assert_eq!(
            read_regular(&file, 5, "input", Leaf::Refuse).unwrap(),
            b"12345"
        );
        let error = read_regular(&file, 4, "input", Leaf::Refuse).unwrap_err();
        assert!(error.contains("exceeds its 4-byte limit"), "{error}");
        let error = read_regular(&directory, 4, "input", Leaf::Follow).unwrap_err();
        assert!(error.contains("is not a regular file"), "{error}");
        #[cfg(unix)]
        {
            let link = directory.join("link");
            std::os::unix::fs::symlink(&file, &link).unwrap();
            assert!(read_regular(&link, 5, "input", Leaf::Refuse).is_err());
            assert_eq!(
                read_stable(&link, 5, "input", Leaf::Follow).unwrap(),
                b"12345"
            );
        }
        let _ = fs::remove_dir_all(directory);
    }

    #[test]
    fn an_output_may_not_be_an_input_or_another_output() {
        let directory = scratch("collisions");
        let source = directory.join("a.c");
        fs::write(&source, b"").unwrap();
        let artifact = directory.join("a.i");
        let lock = directory.join("lock.json");
        reject_output_collisions(
            &[("artifact", &artifact), ("lock", &lock)],
            [("source", source.as_path())],
        )
        .unwrap();
        let error = reject_output_collisions(
            &[("artifact", &source), ("lock", &lock)],
            [("source", source.as_path())],
        )
        .unwrap_err();
        assert!(error.contains("is the source input"), "{error}");
        let error = reject_output_collisions(
            &[
                ("artifact", &lock),
                ("lock", &directory.join("./lock.json")),
            ],
            [],
        )
        .unwrap_err();
        assert!(error.contains("is also the artifact output"), "{error}");
        let _ = fs::remove_dir_all(directory);
    }
}
