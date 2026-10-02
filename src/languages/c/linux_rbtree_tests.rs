//! The pinned Linux `lib/rbtree.c` input closure in
//! `integrations/linux-rbtree/`.
//!
//! This is a negative discovery gate. Click does not import this
//! translation unit yet; the tests pin where it stops, so that progress and
//! regressions both show up as a changed expectation.

use std::collections::BTreeMap;
use std::fs;
use std::io::Read;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};

use sha2::{Digest, Sha256};

use super::compiler_import::create_lock;
use super::{provenance::CSourceMap, syntax};
use crate::source::SourcePosition;

/// The first rejection of the complete pinned translation unit: the
/// anonymous union member of `struct ftrace_branch_data`, the artifact's
/// first declaration.
const FIRST_REJECTION: &str =
    "././include/linux/compiler_types.h:172: expected union name, got `{`";

/// The existing compiler-import profile refuses the recorded kernel
/// compiler arguments before it runs the compiler.
const IMPORT_REJECTION: &str = "unsupported compiler argument `-fmacro-prefix-map=./=`";

/// Set to a non-empty value to fail, instead of reporting, when the host
/// toolchain is not the recorded one.
const REQUIRE_TOOLCHAIN: &str = "CLICK_LINUX_RBTREE_REQUIRE_TOOLCHAIN";

/// Set to an output path to write the per-declaration rejection inventory.
const INVENTORY: &str = "CLICK_LINUX_RBTREE_INVENTORY";

fn fixture() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("integrations/linux-rbtree")
}

fn sha256(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

fn provenance() -> serde_json::Value {
    serde_json::from_slice(&fs::read(fixture().join("provenance.json")).unwrap()).unwrap()
}

fn text<'a>(value: &'a serde_json::Value, path: &[&str]) -> &'a str {
    path.iter()
        .fold(value, |value, key| &value[*key])
        .as_str()
        .unwrap_or_else(|| panic!("provenance has no string at {path:?}"))
}

/// The closure extracted into a fresh directory, removed on drop.
struct Closure(PathBuf);

impl Drop for Closure {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

/// Extracts the checked-in archive after checking it, member by member,
/// against the provenance record.
fn extract_closure(provenance: &serde_json::Value) -> Closure {
    let archive = fs::read(fixture().join("input-closure.tar.gz")).unwrap();
    extract_archive(provenance, &archive, true)
}

/// `check_archive_hash` is false only for the tamper regressions, which
/// reach the per-member checks behind the whole-archive hash.
fn extract_archive(
    provenance: &serde_json::Value,
    archive: &[u8],
    check_archive_hash: bool,
) -> Closure {
    if check_archive_hash {
        assert_eq!(
            sha256(archive),
            text(provenance, &["closure", "archive_sha256"]),
            "input-closure.tar.gz differs from provenance.json"
        );
    }
    let mut expected = provenance["closure"]["files"]
        .as_array()
        .unwrap()
        .iter()
        .map(|file| {
            (
                file["path"].as_str().unwrap().to_string(),
                (
                    file["sha256"].as_str().unwrap().to_string(),
                    file["bytes"].as_u64().unwrap(),
                ),
            )
        })
        .collect::<BTreeMap<_, _>>();
    let notices = provenance["closure"]["notices"]
        .as_array()
        .unwrap()
        .iter()
        .map(|notice| notice.as_str().unwrap())
        .collect::<Vec<_>>();

    static NEXT: AtomicUsize = AtomicUsize::new(0);
    let root = std::env::temp_dir().join(format!(
        "click-linux-rbtree-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    fs::create_dir(&root).expect("create isolated closure directory");
    let closure = Closure(root);
    let mut entries = tar::Archive::new(flate2::read::GzDecoder::new(archive));
    for entry in entries.entries().unwrap() {
        let mut entry = entry.unwrap();
        assert!(
            entry.header().entry_type().is_file(),
            "the closure holds only regular files"
        );
        let path = entry.path().unwrap().to_str().unwrap().to_string();
        let mut bytes = Vec::new();
        entry.read_to_end(&mut bytes).unwrap();
        match expected.remove(&path) {
            Some((digest, size)) => {
                assert_eq!(bytes.len() as u64, size, "{path}: size differs");
                assert_eq!(sha256(&bytes), digest, "{path}: content differs");
            }
            None => assert!(
                notices.contains(&path.as_str()),
                "{path}: not a recorded input"
            ),
        }
        assert!(
            Path::new(&path)
                .components()
                .all(|part| matches!(part, std::path::Component::Normal(_))),
            "{path}: not a plain relative path"
        );
        let target = closure.0.join(&path);
        fs::create_dir_all(target.parent().unwrap()).unwrap();
        fs::write(target, bytes).unwrap();
    }
    assert!(
        expected.is_empty(),
        "recorded inputs missing from the closure: {:?}",
        expected.keys().collect::<Vec<_>>()
    );
    closure
}

/// Whether the host compiler driver and `cc1` are the recorded binaries.
fn recorded_toolchain(provenance: &serde_json::Value) -> Result<(), String> {
    for tool in ["gcc", "cc1"] {
        let path = text(provenance, &["toolchain", tool, "path"]);
        let bytes = fs::read(path).map_err(|error| format!("{path}: {error}"))?;
        if sha256(&bytes) != text(provenance, &["toolchain", tool, "sha256"]) {
            return Err(format!("{path} is not the recorded binary"));
        }
    }
    Ok(())
}

/// `Ok(None)` when the host has the recorded compiler. Otherwise the
/// frontier checks cannot run: that is a notice to print, or an error when
/// the recorded compiler is required.
fn toolchain_gate(
    provenance: &serde_json::Value,
    required: bool,
) -> Result<Option<String>, String> {
    match recorded_toolchain(provenance) {
        Ok(()) => Ok(None),
        Err(reason) if required => Err(format!("{REQUIRE_TOOLCHAIN} is set, but {reason}")),
        Err(reason) => Ok(Some(format!(
            "linux-rbtree: NOT CHECKED: preprocessing and the frontier pin need the recorded GCC ({reason}); only the closure was checked"
        ))),
    }
}

#[test]
fn linux_rbtree_gate_reports_or_refuses_another_compiler() {
    // Another compiler is simulated by recording a different identity.
    let mut other_binary = provenance();
    other_binary["toolchain"]["cc1"]["sha256"] = "0".repeat(64).into();
    let mut missing = provenance();
    missing["toolchain"]["gcc"]["path"] = "/nonexistent/click-linux-rbtree-gcc".into();
    for (provenance, reason) in [
        (other_binary, "is not the recorded binary"),
        (missing, "/nonexistent/click-linux-rbtree-gcc"),
    ] {
        // The reason does not depend on whether this host has the recorded
        // compiler: an unreadable recorded `gcc` path is also "another compiler".
        let Err(actual) = recorded_toolchain(&provenance) else {
            panic!("a changed identity must not match the host compiler");
        };
        if fs::metadata(text(&provenance, &["toolchain", "gcc", "path"])).is_ok()
            && fs::metadata(text(&provenance, &["toolchain", "cc1", "path"])).is_ok()
        {
            assert!(actual.contains(reason), "{actual}");
        }
        let notice = toolchain_gate(&provenance, false)
            .expect("another compiler is not a failure by default")
            .expect("another compiler must be reported, not silently accepted");
        assert!(notice.contains("NOT CHECKED"), "{notice}");
        let refusal = toolchain_gate(&provenance, true)
            .expect_err("a required recorded compiler must fail the gate");
        assert!(refusal.contains(REQUIRE_TOOLCHAIN), "{refusal}");
    }
}

fn panic_message(result: std::thread::Result<Closure>) -> String {
    let payload = result.err().expect("a tampered closure must be refused");
    payload
        .downcast_ref::<String>()
        .cloned()
        .or_else(|| payload.downcast_ref::<&str>().map(|text| text.to_string()))
        .unwrap_or_default()
}

#[test]
fn linux_rbtree_gate_refuses_a_tampered_closure() {
    let provenance = provenance();
    let archive = fs::read(fixture().join("input-closure.tar.gz")).unwrap();

    // One flipped byte anywhere changes the archive hash.
    let mut flipped = archive.clone();
    let middle = flipped.len() / 2;
    flipped[middle] ^= 1;
    let message = panic_message(std::panic::catch_unwind(|| {
        extract_archive(&provenance, &flipped, true)
    }));
    assert!(
        message.contains("differs from provenance.json"),
        "{message}"
    );

    // Behind the archive hash, each member is checked on its own: a changed
    // file, a missing file, and an unrecorded file are each refused.
    let mut raw = Vec::new();
    flate2::read::GzDecoder::new(archive.as_slice())
        .read_to_end(&mut raw)
        .unwrap();
    let repack = |edit: &dyn Fn(&str, &mut Vec<u8>) -> bool, extra: Option<&str>| {
        let mut builder = tar::Builder::new(flate2::write::GzEncoder::new(
            Vec::new(),
            flate2::Compression::fast(),
        ));
        let mut append = |path: &str, bytes: &[u8]| {
            let mut header = tar::Header::new_ustar();
            header.set_size(bytes.len() as u64);
            header.set_mode(0o644);
            header.set_cksum();
            builder.append_data(&mut header, path, bytes).unwrap();
        };
        for entry in tar::Archive::new(raw.as_slice()).entries().unwrap() {
            let mut entry = entry.unwrap();
            let path = entry.path().unwrap().to_str().unwrap().to_string();
            let mut bytes = Vec::new();
            entry.read_to_end(&mut bytes).unwrap();
            if edit(&path, &mut bytes) {
                append(&path, &bytes);
            }
        }
        if let Some(path) = extra {
            append(path, b"int unrecorded;\n");
        }
        builder.into_inner().unwrap().finish().unwrap()
    };
    let cases: [(Vec<u8>, &str); 3] = [
        (
            repack(
                &|path, bytes| {
                    if path == "include/linux/rbtree.h" {
                        bytes[0] ^= 1;
                    }
                    true
                },
                None,
            ),
            "include/linux/rbtree.h: content differs",
        ),
        (
            repack(&|path, _| path != "include/linux/rbtree_types.h", None),
            "recorded inputs missing from the closure",
        ),
        (
            repack(&|_, _| true, Some("include/linux/unrecorded.h")),
            "include/linux/unrecorded.h: not a recorded input",
        ),
    ];
    for (tampered, expected) in cases {
        let message = panic_message(std::panic::catch_unwind(|| {
            extract_archive(&provenance, &tampered, false)
        }));
        assert!(message.contains(expected), "{expected}: {message}");
    }
}

#[test]
fn linux_rbtree_closure_matches_its_provenance() {
    let provenance = provenance();
    let closure = extract_closure(&provenance);
    let files = provenance["closure"]["files"].as_array().unwrap();
    assert_eq!(
        files.len() as u64,
        provenance["closure"]["file_count"].as_u64().unwrap()
    );
    assert!(closure.0.join("lib/rbtree.c").is_file());

    // The import configuration names the recorded invocation: the recorded
    // arguments without the ones the importer's kernel profile fixes itself.
    let config: serde_json::Value =
        serde_json::from_slice(&fs::read(fixture().join("rbtree.click.import.json")).unwrap())
            .unwrap();
    let fixed = ["-E", "-nostdinc", "-std=gnu11", "-funsigned-char", "-m64"];
    let mut recorded = provenance["preprocess"]["argv"]
        .as_array()
        .unwrap()
        .iter()
        .map(|argument| argument.as_str().unwrap())
        .filter(|argument| !fixed.contains(argument))
        .collect::<Vec<_>>();
    assert_eq!(recorded.pop(), Some("lib/rbtree.c"));
    let configured = config["sources"][0]["args"]
        .as_array()
        .unwrap()
        .iter()
        .map(|argument| argument.as_str().unwrap())
        .collect::<Vec<_>>();
    assert_eq!(configured, recorded);
    assert_eq!(
        config["compiler"].as_str().unwrap(),
        text(&provenance, &["preprocess", "program"])
    );
}

#[test]
fn linux_rbtree_pinned_translation_unit_stops_at_its_recorded_frontier() {
    let provenance = provenance();
    let closure = extract_closure(&provenance);
    let required = std::env::var_os(REQUIRE_TOOLCHAIN).is_some_and(|value| !value.is_empty());
    if let Some(notice) =
        toolchain_gate(&provenance, required).unwrap_or_else(|error| panic!("{error}"))
    {
        eprintln!("{notice}");
        return;
    }

    // The import route: the importer's profile refuses the recorded
    // arguments, so no lock and no artifact are produced.
    for name in ["rbtree.click", "rbtree.click.import.json"] {
        fs::copy(fixture().join(name), closure.0.join(name)).unwrap();
    }
    let config_path = closure.0.join("rbtree.click.import.json");
    let config = fs::read_to_string(&config_path).unwrap();
    assert!(config.contains("\"working_directory\": \"inputs\""));
    fs::write(
        &config_path,
        config.replace(
            "\"working_directory\": \"inputs\"",
            "\"working_directory\": \".\"",
        ),
    )
    .unwrap();
    let error = create_lock(&config_path)
        .expect_err("the importer profile does not accept the kernel compiler arguments");
    assert!(error.contains(IMPORT_REJECTION), "{error}");
    assert!(!closure.0.join("rbtree.click.import.lock.json").exists());
    assert!(!closure.0.join("rbtree.i").exists());

    // The recorded preprocessing, run directly, reproduces the recorded
    // artifact from the closure alone.
    let mut command = Command::new(text(&provenance, &["preprocess", "program"]));
    command.current_dir(&closure.0).env_clear();
    for argument in provenance["preprocess"]["argv"].as_array().unwrap() {
        command.arg(argument.as_str().unwrap());
    }
    for (name, value) in provenance["preprocess"]["environment"].as_object().unwrap() {
        command.env(name, value.as_str().unwrap());
    }
    let output = command.output().expect("run the recorded compiler");
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(
        output.stdout.len() as u64,
        provenance["preprocess"]["output"]["bytes"]
            .as_u64()
            .unwrap()
    );
    assert_eq!(
        sha256(&output.stdout),
        text(&provenance, &["preprocess", "output", "sha256"]),
        "the preprocessed translation unit differs from the recorded artifact"
    );

    let artifact = String::from_utf8(output.stdout).expect("preprocessed C is UTF-8");
    let (source, map) = CSourceMap::decode(&artifact).expect("decode line markers");
    let error = match syntax::parse_translation_unit_for_import(&source, "lib/rbtree.c", &map) {
        Ok(_) => panic!(
            "the pinned translation unit now parses; replace this negative gate with the import regression"
        ),
        Err(error) => error.to_string(),
    };
    assert_eq!(
        error, FIRST_REJECTION,
        "the first rejection moved; update the pin and the inventory in issues/kernel-scale-preprocessing.md"
    );

    if let Some(path) = std::env::var_os(INVENTORY).filter(|path| !path.is_empty()) {
        fs::write(path, rejection_inventory(&source, &map)).expect("write the inventory");
    }
}

/// Byte ranges of the file-scope declarations and definitions in
/// marker-free preprocessed C: each ends at a file-scope `;` or at the
/// closing brace of a function body.
fn file_scope_items(source: &str) -> Vec<(usize, usize)> {
    let bytes = source.as_bytes();
    let mut items = Vec::new();
    let (mut start, mut depth, mut index) = (0, 0usize, 0);
    let mut last_significant = b' ';
    let mut function_body = false;
    while index < bytes.len() {
        let byte = bytes[index];
        match byte {
            b'"' | b'\'' => {
                index += 1;
                while index < bytes.len() && bytes[index] != byte {
                    if bytes[index] == b'\\' {
                        index += 1;
                    }
                    index += 1;
                }
            }
            b'(' | b'[' => depth += 1,
            b')' | b']' => depth = depth.saturating_sub(1),
            b'{' => {
                if depth == 0 {
                    function_body = last_significant == b')';
                }
                depth += 1;
            }
            b'}' => {
                depth = depth.saturating_sub(1);
                if depth == 0 && function_body {
                    items.push((start, index + 1));
                    start = index + 1;
                    function_body = false;
                }
            }
            b';' if depth == 0 => {
                items.push((start, index + 1));
                start = index + 1;
            }
            _ => {}
        }
        if !byte.is_ascii_whitespace() {
            last_significant = byte;
        }
        index += 1;
    }
    if !source[start..].trim().is_empty() {
        items.push((start, bytes.len()));
    }
    items
}

/// One line per file-scope item: its original location, whether the parser
/// accepts it after the accepted items before it, and its first rejection.
///
/// A rejected item is blanked, so a later item that needs it is rejected in
/// turn; an item reports only its first rejection. This is a measurement
/// aid: it parses the growing prefix once per item, which is quadratic and
/// is why the gate does not run it.
fn rejection_inventory(source: &str, map: &CSourceMap) -> String {
    let mut accepted = String::with_capacity(source.len());
    let mut inventory = String::new();
    for (start, end) in file_scope_items(source) {
        let item = &source[start..end];
        let leading = item.len() - item.trim_start().len();
        let line = source[..start + leading]
            .bytes()
            .filter(|byte| *byte == b'\n')
            .count()
            + 1;
        let origin = map.lookup(SourcePosition::new(line, 1));
        let base = accepted.len();
        accepted.push_str(item);
        let verdict =
            match syntax::parse_translation_unit_for_import(&accepted, "lib/rbtree.c", map) {
                Ok(_) => "accepted".to_string(),
                Err(error) => {
                    accepted.truncate(base);
                    accepted.extend(
                        item.chars()
                            .map(|character| if character == '\n' { '\n' } else { ' ' }),
                    );
                    error.to_string().replace(['\n', '\t'], " ")
                }
            };
        let excerpt = item
            .split_whitespace()
            .collect::<Vec<_>>()
            .join(" ")
            .chars()
            .take(120)
            .collect::<String>();
        inventory.push_str(&format!("{origin}\t{verdict}\t{excerpt}\n"));
    }
    inventory
}
