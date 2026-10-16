//! `std::function` parameters, against a pinned libc++ closure. Click models a
//! `std::function<R(A...)>` as the callable it holds: a lambda passed for one
//! is made from the values it captures by copy, a function is its address,
//! and a call through it is checked against a contract of the value, which
//! implies it is not empty.

use std::fs;
use std::path::PathBuf;
use std::process::Command;

use click::cli::read_click_project;
use click::languages::cpp::{PreparedCppImport, load_import, refresh_import};
use click::surface::{
    ProgramInputs, display_source_names, expand_project_claim_source_by_label,
    verify_program_prepared_project,
};

#[path = "support/pinned_clang.rs"]
mod pinned_clang;
use pinned_clang::{output, pinned_clang, sha256};

const ARCHIVE: &[u8] = include_bytes!("fixtures/libcxx-functional/input-closure.tar.gz");

/// Writes `source` beside the pinned libc++ closure and imports `function`
/// from it, or returns the importer's refusal.
fn import(
    name: &str,
    source: &str,
    function: &str,
) -> Result<(PathBuf, PreparedCppImport), String> {
    assert_eq!(
        sha256(ARCHIVE),
        "3d0597d0eea563ec3f84d23cc46ccba577f0264dc1123544f4aaafb4b9616a98"
    );
    let root = std::env::temp_dir().join(format!(
        "click-libcxx-function-{name}-{}",
        std::process::id()
    ));
    let _ = fs::remove_dir_all(&root);
    fs::create_dir(&root).unwrap();
    let archive = root.join("input-closure.tar.gz");
    fs::write(&archive, ARCHIVE).unwrap();
    assert!(
        Command::new("tar")
            .args([
                "-xzf",
                archive.to_str().unwrap(),
                "-C",
                root.to_str().unwrap()
            ])
            .status()
            .unwrap()
            .success()
    );
    assert_eq!(
        sha256(&fs::read(root.join("libcxx/include/c++/v1/functional")).unwrap()),
        "c9fd255a9882be3803f3b2f6a8d07f2ee769986922128f46da1486e5ae7c81f9"
    );
    fs::write(root.join("callback.cpp"), source).unwrap();
    let clang = pinned_clang();
    let r = root.to_str().unwrap();
    let command = format!(
        "{} --target=x86_64-unknown-linux-gnu --sysroot={r}/sysroot -resource-dir={} -nostdinc++ \
         -isystem {r}/libcxx/include/x86_64-unknown-linux-gnu/c++/v1 -isystem {r}/libcxx/include/c++/v1 \
         -fno-exceptions -fno-rtti -std=c++20 -c {r}/callback.cpp",
        clang.display(),
        output(&clang, &["-print-resource-dir"])
    );
    let database = serde_json::json!([{ "directory": r, "command": command, "file": format!("{r}/callback.cpp") }]);
    fs::write(
        root.join("compile_commands.json"),
        serde_json::to_vec_pretty(&database).unwrap(),
    )
    .unwrap();
    let exporter = root.join("click-cpp-exporter");
    fs::copy(std::env::var("CLICK_CPP_EXPORTER").unwrap(), &exporter).unwrap();
    let config = serde_json::json!({
        "schema": 6, "language": "c++", "standard": "c++20", "target": "x86_64-unknown-linux-gnu",
        "exceptions": false, "rtti": false, "exporter": exporter,
        "compilation_database": "compile_commands.json", "working_directory": ".",
        "source": "callback.cpp", "logical_source": "callback.cpp", "dependencies": [],
        "function": function, "artifact": "callback.click-cpp.json"
    });
    let config_path = root.join("callback.click.import.json");
    fs::write(&config_path, serde_json::to_vec_pretty(&config).unwrap()).unwrap();
    refresh_import(&config_path)?;
    fs::remove_file(exporter).unwrap();
    Ok((root, load_import(&config_path).unwrap()))
}

/// Verifies `sidecar`, then the expansion of each of `claims`.
fn verify(
    root: &std::path::Path,
    import: &PreparedCppImport,
    sidecar: &str,
    claims: &[&str],
) -> Result<(), String> {
    let path = root.join("callback.click");
    fs::write(&path, sidecar).unwrap();
    let parsed = read_click_project(&path, sidecar).unwrap();
    verify_program_prepared_project(&parsed, import)
        .map_err(|error| display_source_names(error.message()).into_owned())?;
    for claim in claims {
        let expanded =
            expand_project_claim_source_by_label(&parsed, &ProgramInputs::program(import), claim)
                .map_err(|error| display_source_names(error.message()).into_owned())?;
        verify_program_prepared_project(&parsed.with_entry_source(expanded), import)
            .map_err(|error| format!("{claim}: {}", display_source_names(error.message())))?;
    }
    Ok(())
}

const CAPTURING_SOURCE: &str = "#include <functional>\n\
int apply(const std::function<int(int)>& f, int x, int k) noexcept { return f(x); }\n\
int caller(int k, int x) noexcept { return apply([k](int y) noexcept { return y + k; }, x, k); }\n";

const CAPTURING_SIDECAR: &str = r#"verifying "callback.cpp";
contract int Adds(int x) {
    let amount: int;
    requires 0 <= x and x <= 1000;
    requires 0 <= amount and amount <= 1000;
    ensures result == x + amount;
}
int apply(const std::function<int(int)>& f, int x, int k) {
    requires Adds(f, { amount: k });
    requires 0 <= x and x <= 1000;
    requires 0 <= k and k <= 1000;
    ensures result == x + k;
} by { execute(); simp(); }
int caller::(lambda#0)(int y) {
    requires 0 <= y and y <= 1000;
    requires 0 <= k and k <= 1000;
    ensures result == y + k;
} by { execute(); simp(); }
int caller(int k, int x) {
    requires 0 <= k and k <= 1000;
    requires 0 <= x and x <= 1000;
    ensures result == x + k;
} by { execute(); simp(); }
"#;

// A lambda passed for a `std::function` parameter is made from the value it
// captures, and its contract, which reads the capture by name, is fixed to
// that value; the callee's parameterized contract is met by refinement.
#[test]
#[ignore = "nightly: 4.5s in the parallel gate"]
fn libcxx_std_function_holds_a_capturing_lambda() {
    let (root, import) = import("capturing", CAPTURING_SOURCE, "caller").unwrap();
    verify(
        &root,
        &import,
        CAPTURING_SIDECAR,
        &["caller::(lambda#0).contract", "caller.contract"],
    )
    .unwrap_or_else(|error| panic!("{error}"));
    for (before, after, expected) in [
        (
            "    ensures result == y + k;\n",
            "    ensures result >= y;\n",
            "is missing prerequisite (precondition clause 1 of `apply`)",
        ),
        (
            "    ensures result == y + k;\n",
            "    ensures result == y + k + 1;\n",
            "caller::(lambda#0).ensures_0",
        ),
        (
            "    requires Adds(f, { amount: k });\n",
            "",
            "cannot verify call through function pointer `f`",
        ),
    ] {
        let hostile = CAPTURING_SIDECAR.replacen(before, after, 1);
        assert_ne!(hostile, CAPTURING_SIDECAR);
        let error = verify(&root, &import, &hostile, &[])
            .expect_err("a std::function without the contract its call needs must fail");
        assert!(error.contains(expected), "{error}");
    }
}

// A function passed for a `std::function` is its address, and a
// `std::function` parameter, by value or by const reference, can be passed
// on, carrying the contract its callee requires.
#[test]
#[ignore = "nightly: 7.1s in the parallel gate"]
fn libcxx_std_function_holds_a_function_and_is_passed_on() {
    for parameter in [
        "const std::function<int(int)>& f",
        "std::function<int(int)> f",
    ] {
        let source = format!(
            "#include <functional>\n\
             int apply({parameter}, int x) noexcept {{ return f(x); }}\n\
             int twice(int y) noexcept {{ return y + y; }}\n\
             int relay({parameter}, int x) noexcept {{ return apply(f, x); }}\n\
             int caller(int x) noexcept {{ return relay(twice, x); }}\n"
        );
        let sidecar = format!(
            r#"verifying "callback.cpp";
contract int Doubling(int x) {{ requires 0 <= x and x <= 1000; ensures result == x + x; }}
int apply({parameter}, int x) {{ requires Doubling(f); requires 0 <= x and x <= 1000; ensures result == x + x; }} by {{ execute(); simp(); }}
int relay({parameter}, int x) {{ requires Doubling(f); requires 0 <= x and x <= 1000; ensures result == x + x; }} by {{ execute(); simp(); }}
int twice(int y) {{ requires 0 <= y and y <= 1000; ensures result == y + y; }} by {{ execute(); simp(); }}
int caller(int x) {{ requires 0 <= x and x <= 1000; ensures result == x + x; }} by {{ execute(); simp(); }}
"#
        );
        let (root, import) = import("function", &source, "caller").unwrap();
        verify(&root, &import, &sidecar, &[]).unwrap_or_else(|error| panic!("{error}"));
        let weak = sidecar.replacen("ensures result == y + y;", "ensures result >= y;", 1);
        let error = verify(&root, &import, &weak, &[]).expect_err("a weak `twice` must fail");
        assert!(
            error.contains("does not satisfy named contract `Doubling`"),
            "{error}"
        );
    }
}

// A capture by reference is refused: C++ does not keep the variable from
// changing while the closure lives, so its value at the call is not the
// value when the lambda was made.
#[test]
fn libcxx_std_function_refuses_a_reference_capture() {
    let source = CAPTURING_SOURCE.replace("[k]", "[&k]");
    let Err(error) = import("reference", &source, "caller") else {
        panic!("a reference capture was imported");
    };
    assert!(
        error.contains("a C++ lambda captures only scalar locals and parameters, by copy"),
        "{error}"
    );
}
