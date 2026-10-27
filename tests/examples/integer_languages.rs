//! The cross-language integer fixture: the same small integer programs in C,
//! C++ and Rust, `examples/integer-languages/{c,cpp,rust}/integers.*`, with
//! one sidecar per language that states the same claims. It is the
//! language-level counterpart of the kernel's per-format matrix
//! (`src/kernel/machine_integer/matrix_tests.rs`; `design/machine-integers.md`,
//! "Coverage").
//!
//! Every case of [`CASES`] is in each language's sidecar (`c.click`,
//! `cpp.click`, `rust.click`) or, as a named gap, in its gap file
//! (`cpp.click-gap`, `rust.click-gap`), which holds the same claims and proof; a
//! language with no gap has no gap file.
//! [`claims_agree_across_languages`] holds every language to the same
//! signatures and claims. The example harness verifies the three sidecars as
//! it verifies every example, so a language that falls behind fails there,
//! naming its sidecar and function. A gap file is not a `.click` file, so the
//! corpus tools leave it alone; this module checks that each gap is still
//! one, so closing a gap fails until its case moves into the sidecar:
//!
//! - [`Gap::Verify`]: the source imports but the claims do not verify; checked
//!   here, in the nightly, with the goal the refusal names.
//! - [`Gap::Import`]: the front end refuses the source. A C++ import gap is
//!   checked with the pinned exporter, where `CLICK_CPP_EXPORTER` names it; a
//!   Rust one with Charon, in the nightly. A Rust import gap's source is in
//!   `gaps.rs`, outside the crate, since Charon translates every function of
//!   a crate; a C++ one stays in `integers.cpp`, unselected in the project.
//!
//! The C++ and Rust imports are checked in, so the gate needs neither
//! toolchain. After changing a source, run `click import lock` on its
//! directory, `examples/integer-languages/cpp` or `rust`, with its toolchain
//! (`docs/internals/testing.md`, "Cross-language integer fixture").

use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};

use click::cli::{read_c_inputs_for_project, read_click_project_at_root};
use click::surface::verify_project_functions;

#[path = "../support/cpp_imports.rs"]
mod cpp_imports;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Language {
    C,
    Cpp,
    Rust,
}

const LANGUAGES: [Language; 3] = [Language::C, Language::Cpp, Language::Rust];

impl Language {
    fn stem(self) -> &'static str {
        match self {
            Language::C => "c",
            Language::Cpp => "cpp",
            Language::Rust => "rust",
        }
    }
}

/// Why a language does not verify a case yet.
#[derive(Clone, Copy, Debug)]
enum Gap {
    /// The front end refuses the source, with this message.
    Import(&'static str),
    /// The source imports, but verification refuses the claims at this goal.
    /// No case has one since Stage 4 of `design/machine-integers.md` gave
    /// the three languages one narrowing term; the next one is named here.
    #[allow(dead_code, reason = "no verification gap remains; a new one uses it")]
    Verify(&'static str),
}

struct Case {
    name: &'static str,
    /// Each language's gap, in [`LANGUAGES`] order; `None` verifies.
    gaps: [Option<Gap>; 3],
}

const SHIFT: Gap = Gap::Import("unsupported binary operator");
const SIGNED_CHAR: Gap = Gap::Import("the supported C++ slice supports bool");
const WRAPPING: Gap = Gap::Import("unmodeled external call");

#[rustfmt::skip]
const CASES: &[Case] = &[
    Case { name: "add_i32", gaps: [None, None, None] },
    Case { name: "sub_i32", gaps: [None, None, None] },
    Case { name: "mul_i32", gaps: [None, None, None] },
    Case { name: "wrapping_add_u32", gaps: [None, None, Some(WRAPPING)] },
    Case { name: "wrapping_sub_u32", gaps: [None, None, Some(WRAPPING)] },
    Case { name: "wrapping_mul_u32", gaps: [None, None, Some(WRAPPING)] },
    Case { name: "above_int32_max", gaps: [None, None, None] },
    Case { name: "keep_above_int32_max", gaps: [None, None, None] },
    Case { name: "to_signed_i32", gaps: [None, None, None] },
    Case { name: "to_unsigned_u32", gaps: [None, None, None] },
    Case { name: "div_u32", gaps: [None, None, None] },
    Case { name: "rem_u32", gaps: [None, None, None] },
    Case { name: "shr_u32", gaps: [None, Some(SHIFT), None] },
    Case { name: "div_i32", gaps: [None, None, None] },
    Case { name: "rem_i32", gaps: [None, None, None] },
    Case { name: "shr_i32", gaps: [None, Some(SHIFT), None] },
    Case { name: "narrow_u8", gaps: [None, None, None] },
    Case { name: "narrow_i8", gaps: [None, Some(SIGNED_CHAR), None] },
    Case { name: "narrow_u8_in_range", gaps: [None, None, None] },
    Case { name: "add_i64", gaps: [None, None, None] },
    Case { name: "wrapping_add_u64", gaps: [None, None, Some(WRAPPING)] },
    Case { name: "below_i32", gaps: [None, None, None] },
    Case { name: "below_u32", gaps: [None, None, None] },
    Case { name: "sign_bit_set", gaps: [None, None, None] },
    Case { name: "not_bool", gaps: [None, None, None] },
    Case { name: "and_bool", gaps: [None, None, None] },
    Case { name: "int_to_bool", gaps: [None, None, None] },
    Case { name: "bool_to_u8", gaps: [None, None, None] },
    Case { name: "bool_sum", gaps: [None, None, None] },
    Case { name: "select_i32", gaps: [None, None, None] },
];

/// The language's part of the fixture: `examples/integer-languages/c`, `cpp`
/// or `rust`, each verified by the example harness on its own.
fn fixture(language: Language) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("examples/integer-languages")
        .join(language.stem())
}

fn read(language: Language, name: &str) -> String {
    fs::read_to_string(fixture(language).join(name))
        .unwrap_or_else(|error| panic!("failed to read `{name}`: {error}"))
}

fn sidecar(language: Language) -> String {
    read(language, &format!("{}.click", language.stem()))
}

/// The language's gap file, or nothing for a language with no gap.
fn gap_file(language: Language) -> String {
    let name = format!("{}.click-gap", language.stem());
    if fixture(language).join(&name).exists() {
        read(language, &name)
    } else {
        String::new()
    }
}

/// Verifies `function` from `source`, read as the language's sidecar in the
/// fixture project.
fn verify(language: Language, source: &str, function: &str) -> Result<(), String> {
    let (source, function) = (source.to_string(), function.to_string());
    super::limits::spawn("integer fixture verifier", function.clone(), move || {
        let root = fixture(language);
        let path = root.join(format!("{}.click", language.stem()));
        let project = read_click_project_at_root(&path, &source, &root)?;
        let inputs = read_c_inputs_for_project(&path, &source, &project)?;
        verify_project_functions(&project, &inputs.program_inputs(), [function])
            .map(|_| ())
            .map_err(|error| format!("{error}"))
    })?
}

/// One function of a sidecar: its signature, in Click's type names, and its
/// contract's lines.
#[derive(Debug, PartialEq, Eq)]
struct Contract {
    signature: String,
    claims: Vec<String>,
}

/// The functions a sidecar or gap file states, by name.
fn contracts(source: &str) -> BTreeMap<String, Contract> {
    fn click_type(rust: &str) -> &str {
        match rust {
            "i8" => "int8",
            "u8" => "uint8",
            "i32" => "int32",
            "u32" => "uint32",
            "i64" => "int64",
            "u64" => "uint64",
            other => other,
        }
    }
    let mut contracts = BTreeMap::new();
    let mut lines = source.lines();
    while let Some(line) = lines.next() {
        let Some(head) = line.strip_suffix(" {") else {
            continue;
        };
        if line.starts_with(char::is_whitespace) || head.starts_with("//") {
            continue;
        }
        let (open, close) = (head.find('(').unwrap(), head.rfind(')').unwrap());
        let parameters = head[open + 1..close]
            .split(',')
            .map(str::trim)
            .filter(|parameter| !parameter.is_empty());
        // `fn name(x: u32) -> u8` and `uint8 name(uint32 x)` alike become
        // `uint8 name(uint32 x)`.
        let (name, signature) = match head.strip_prefix("fn ") {
            Some(rest) => {
                let name = &rest[..rest.find('(').unwrap()];
                let result = click_type(head[close + 1..].trim().trim_start_matches("-> "));
                let parameters = parameters
                    .map(|parameter| {
                        let (name, ty) = parameter.split_once(": ").unwrap();
                        format!("{} {name}", click_type(ty))
                    })
                    .collect::<Vec<_>>();
                (name, format!("{result} {name}({})", parameters.join(", ")))
            }
            None => {
                let (result, name) = head[..open].split_once(' ').unwrap();
                let parameters = parameters.collect::<Vec<_>>();
                (name, format!("{result} {name}({})", parameters.join(", ")))
            }
        };
        let claims = lines
            .by_ref()
            .take_while(|line| !line.starts_with('}'))
            .map(|line| line.trim().to_string())
            .collect();
        assert!(
            contracts
                .insert(name.to_string(), Contract { signature, claims })
                .is_none(),
            "`{name}` is stated twice"
        );
    }
    contracts
}

/// Every case is in each language's sidecar or, as its gap says, in its gap
/// file, with the same signature and claims in every language.
#[test]
fn claims_agree_across_languages() {
    let stated = LANGUAGES.map(|language| {
        (
            contracts(&sidecar(language)),
            contracts(&gap_file(language)),
        )
    });
    let mut problems = Vec::new();
    for (index, &language) in LANGUAGES.iter().enumerate() {
        let (verified, gaps) = &stated[index];
        for name in verified.keys().chain(gaps.keys()) {
            if !CASES.iter().any(|case| case.name == name) {
                problems.push(format!("{language:?} states `{name}`, which is not a case"));
            }
        }
        for case in CASES {
            let (expected, other) = match case.gaps[index] {
                None => ("sidecar", gaps),
                Some(_) => ("gap file", verified),
            };
            let held = if case.gaps[index].is_none() {
                verified
            } else {
                gaps
            };
            if !held.contains_key(case.name) {
                problems.push(format!(
                    "{language:?} does not state `{}` in its {expected}",
                    case.name
                ));
            }
            if other.contains_key(case.name) {
                problems.push(format!(
                    "{language:?} states `{}` outside its {expected}",
                    case.name
                ));
            }
        }
    }
    for case in CASES {
        let mut forms = stated
            .iter()
            .zip(LANGUAGES)
            .filter_map(|((verified, gaps), language)| {
                verified
                    .get(case.name)
                    .or_else(|| gaps.get(case.name))
                    .map(|contract| (language, contract))
            });
        let Some((first_language, first)) = forms.next() else {
            continue;
        };
        for (language, contract) in forms {
            if contract != first {
                problems.push(format!(
                    "`{}` differs between {first_language:?} and {language:?}:\n  {first:?}\n  {contract:?}",
                    case.name
                ));
            }
        }
    }
    assert!(problems.is_empty(), "{}", problems.join("\n"));
}

/// Each verification gap of `language` is still refused, at its goal. When
/// one verifies, move its function from the gap file into the sidecar and
/// drop the gap.
fn verification_gaps_are_still_refused(language: Language) {
    let index = LANGUAGES
        .iter()
        .position(|other| *other == language)
        .unwrap();
    for case in CASES {
        let Some(Gap::Verify(goal)) = case.gaps[index] else {
            continue;
        };
        match verify(language, &gap_file(language), case.name) {
            Ok(()) => panic!(
                "{language:?} now verifies `{}`: move it into its sidecar",
                case.name
            ),
            Err(error) => assert!(
                error.contains(goal),
                "{language:?} refuses `{}` at another goal than `{goal}`:\n{error}",
                case.name
            ),
        }
    }
}

#[test]
#[ignore = "nightly: each gap verifies its case (0.4 to 0.8s in the parallel gate, 2026-10-26)"]
fn verification_gaps_are_still_refused_in_every_language() {
    for language in LANGUAGES {
        verification_gaps_are_still_refused(language);
    }
}

/// A false claim about a `uint32` above `INT32_MAX` is refused, and the
/// refusal prints the value in its own type.
fn a_refused_uint32_above_int32_max_prints_as_itself(language: Language) {
    let claim = "ensures result == 4000000000u32;";
    let source = sidecar(language);
    assert!(source.contains(claim), "{language:?}");
    let error = verify(
        language,
        &source.replacen(claim, "ensures result == 4000000001u32;", 1),
        "above_int32_max",
    )
    .err()
    .unwrap_or_else(|| panic!("{language:?} accepts a false `above_int32_max`"));
    assert!(
        error.contains("left side evaluated to 4000000000u32"),
        "{language:?}: {error}"
    );
}

#[test]
#[ignore = "nightly: 0.65s in the parallel gate (2026-10-26)"]
fn c_refuses_a_false_uint32_above_int32_max_as_itself() {
    a_refused_uint32_above_int32_max_prints_as_itself(Language::C);
}

#[test]
#[ignore = "nightly: 0.6s in the parallel gate (2026-10-26)"]
fn cpp_refuses_a_false_uint32_above_int32_max_as_itself() {
    a_refused_uint32_above_int32_max_prints_as_itself(Language::Cpp);
}

#[test]
#[ignore = "nightly: 0.7s in the parallel gate (2026-10-26)"]
fn rust_refuses_a_false_uint32_above_int32_max_as_itself() {
    a_refused_uint32_above_int32_max_prints_as_itself(Language::Rust);
}

/// The source of one function of `source`: from its line to its closing
/// brace at the start of a line.
fn function_source(source: &str, name: &str) -> String {
    let start = source
        .lines()
        .position(|line| line.contains(&format!(" {name}(")) && !line.starts_with(' '))
        .unwrap_or_else(|| panic!("no function `{name}`"));
    let mut lines = source.lines().skip(start);
    let mut function = Vec::new();
    for line in lines.by_ref() {
        function.push(line);
        if line.starts_with('}') {
            break;
        }
    }
    function.join("\n") + "\n"
}

/// A one-unit project in a fresh temporary directory, removed on drop.
struct Scratch(PathBuf);

impl Scratch {
    fn new(label: &str) -> Self {
        use std::sync::atomic::{AtomicUsize, Ordering};
        static NEXT: AtomicUsize = AtomicUsize::new(0);
        let directory = std::env::temp_dir().join(format!(
            "click-integer-languages-{label}-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir_all(&directory).unwrap();
        Self(directory)
    }

    fn lock(&self, project: serde_json::Value, cpp_exporter: Option<&Path>) -> Result<(), String> {
        let file = self.0.join(click::project::FILE_NAME);
        fs::write(&file, serde_json::to_vec_pretty(&project).unwrap()).unwrap();
        click::project::Project::load(&file)?.lock_with_cpp_exporter(cpp_exporter)
    }
}

impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

fn checked_in_project(language: Language) -> serde_json::Value {
    serde_json::from_str(&read(language, click::project::FILE_NAME)).unwrap()
}

/// The project with only its unit `unit`.
fn one_unit(unit: &str, value: serde_json::Value) -> serde_json::Value {
    serde_json::json!({ "units": { unit: value } })
}

fn cpp_exporter() -> Option<PathBuf> {
    let exporter = std::env::var_os("CLICK_CPP_EXPORTER").map(PathBuf::from);
    if exporter.is_none() {
        println!("SKIPPING: CLICK_CPP_EXPORTER is not set");
    }
    exporter
}

/// A unit's checked-in artifact and lock entry, or a fresh lock's, keyed for
/// [`cpp_imports::same_import`].
fn unit_import(root: &Path, unit: &str, source: &str) -> BTreeMap<PathBuf, Vec<u8>> {
    let lock: serde_json::Value =
        serde_json::from_slice(&fs::read(root.join(click::project::LOCK_NAME)).unwrap()).unwrap();
    let artifact = PathBuf::from(".click").join(unit).join(source);
    BTreeMap::from([
        (
            PathBuf::from(click::project::LOCK_NAME),
            serde_json::to_vec(&lock["units"][unit]).unwrap(),
        ),
        (artifact.clone(), fs::read(root.join(&artifact)).unwrap()),
    ])
}

/// The checked-in C++ import is what the pinned exporter produces now.
#[test]
#[ignore = "nightly: 0.9s in the parallel gate (2026-10-26)"]
fn cpp_import_matches_the_pinned_exporter() {
    let Some(exporter) = cpp_exporter() else {
        return;
    };
    let scratch = Scratch::new("cpp");
    let cpp = fixture(Language::Cpp);
    fs::copy(cpp.join("integers.cpp"), scratch.0.join("integers.cpp")).unwrap();
    let unit = checked_in_project(Language::Cpp)["units"]["integers_cpp"].clone();
    scratch
        .lock(one_unit("integers_cpp", unit), Some(&exporter))
        .unwrap();
    let artifact = "integers.cpp.click-cpp.json";
    let checked_in = unit_import(&cpp, "integers_cpp", artifact);
    let exported = unit_import(&scratch.0, "integers_cpp", artifact);
    assert!(
        cpp_imports::same_import(&checked_in, &exported),
        "the fixture's C++ import differs from the pinned exporter's; run `click import lock examples/integer-languages/cpp`: {}",
        cpp_imports::first_import_difference(&checked_in, &exported)
    );
}

/// Each C++ import gap is still refused by the pinned exporter.
#[test]
fn cpp_import_gaps_are_still_refused() {
    let Some(exporter) = cpp_exporter() else {
        return;
    };
    let mut unit = checked_in_project(Language::Cpp)["units"]["integers_cpp"].clone();
    let source = read(Language::Cpp, "integers.cpp");
    for case in CASES {
        let Some(Gap::Import(refusal)) = case.gaps[1] else {
            continue;
        };
        let scratch = Scratch::new("cpp-gap");
        fs::write(scratch.0.join("integers.cpp"), &source).unwrap();
        unit["sources"]["integers.cpp"]["functions"] = serde_json::json!([case.name]);
        match scratch.lock(one_unit("integers_cpp", unit.clone()), Some(&exporter)) {
            Ok(()) => panic!(
                "the exporter now imports `{}`: select it and move it into `cpp.click`",
                case.name
            ),
            Err(error) => assert!(error.contains(refusal), "`{}`: {error}", case.name),
        }
    }
}

/// The checked-in Rust import is what pinned Charon extracts now.
#[test]
#[ignore = "nightly: re-extracts the fixture with the pinned Rust compiler"]
fn rust_import_matches_live_charon_extraction() {
    let scratch = Scratch::new("rust");
    let rust = fixture(Language::Rust);
    fs::copy(rust.join("integers.rs"), scratch.0.join("integers.rs")).unwrap();
    let unit = checked_in_project(Language::Rust)["units"]["integers_rust"].clone();
    scratch.lock(one_unit("integers_rust", unit), None).unwrap();
    let artifact = "integers.rs.ullbc";
    let checked_in = unit_import(&rust, "integers_rust", artifact);
    let extracted = unit_import(&scratch.0, "integers_rust", artifact);
    assert!(
        cpp_imports::same_import(&checked_in, &extracted),
        "the fixture's Rust import differs from live extraction; run `click import lock examples/integer-languages/rust`: {}",
        cpp_imports::first_import_difference(&checked_in, &extracted)
    );
}

/// Each Rust import gap in `gaps.rs` is still refused by Charon.
#[test]
#[ignore = "nightly: runs the pinned Rust compiler once per gap"]
fn rust_import_gaps_are_still_refused() {
    let gaps = read(Language::Rust, "gaps.rs");
    for case in CASES {
        let Some(Gap::Import(refusal)) = case.gaps[2] else {
            continue;
        };
        let scratch = Scratch::new("rust-gap");
        fs::write(scratch.0.join("gap.rs"), function_source(&gaps, case.name)).unwrap();
        let unit = serde_json::json!({ "language": "rust", "sources": { "gap.rs": {} } });
        match scratch.lock(one_unit("gap", unit), None) {
            Ok(()) => panic!(
                "Charon now imports `{}`: move it from `gaps.rs` into `integers.rs`",
                case.name
            ),
            Err(error) => assert!(error.contains(refusal), "`{}`: {error}", case.name),
        }
    }
}
