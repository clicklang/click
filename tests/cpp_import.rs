use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};

use click::cli::{CInput, parse_mdtest, read_c_inputs, read_click_project};
use click::kernel::{
    Bitvector32Term, CExpression, CFunctionOutcome, CMemory, CMemoryRange, CResourceFact, CState,
    CStatement, CType, CUndefinedBehavior, Pointer, PointerOffsetTerm, Proposition,
    PureFactContext, ResourceContext, c_typed_pointer_value, int32,
    prove_symbolic_c_function_execution,
};
use click::languages::cpp::{
    CppBinaryOperator, CppCallArgument, CppCleanup, CppExceptionBehavior, CppExpression,
    CppFunctionKind, CppInitializer, CppStatement, CppType, load_import, lower_import,
    refresh_import,
};
use click::surface::{
    C0VerificationSession, VerifiedClaim, expand_program_prepared_project_claim_source_by_label,
    expand_program_prepared_project_tactic_source_at,
    program_prepared_project_smart_tactic_source_sites,
    program_prepared_project_tactic_source_position, verify_program_prepared_project,
};

const SOURCE: &str = include_str!("../examples/basic-cpp/increment.cpp");
const SIDECAR: &str = include_str!("../examples/basic-cpp/increment.click");
const BRANCH_SOURCE: &str = include_str!("fixtures/cpp-verification/branch-return/choose.cpp");
const BRANCH_SIDECAR: &str = include_str!("fixtures/cpp-verification/branch-return/choose.click");
const CONST_REFERENCE_SOURCE: &str =
    include_str!("fixtures/cpp-verification/const-reference-alias/write_then_read.cpp");
const CONST_REFERENCE_SIDECAR: &str =
    include_str!("fixtures/cpp-verification/const-reference-alias/write_then_read.click");
const DIRECT_CALL_SOURCE: &str =
    include_str!("fixtures/cpp-verification/direct-call/call_set_seven.cpp");
const DIRECT_CALL_SIDECAR: &str =
    include_str!("fixtures/cpp-verification/direct-call/call_set_seven.click");
const SCALAR_LOCAL_SOURCE: &str =
    include_str!("fixtures/cpp-verification/scalar-local/relay_value.cpp");
const SCALAR_LOCAL_SIDECAR: &str =
    include_str!("fixtures/cpp-verification/scalar-local/relay_value.click");
const POINTER_SOURCE: &str = include_str!("fixtures/cpp-verification/pointer/bump_reference.cpp");
const POINTER_SIDECAR: &str =
    include_str!("fixtures/cpp-verification/pointer/bump_reference.click");
const STRUCT_MEMBER_SOURCE: &str =
    include_str!("fixtures/cpp-verification/struct-member/stage_restore.cpp");
const STRUCT_MEMBER_SIDECAR: &str =
    include_str!("fixtures/cpp-verification/struct-member/stage_restore.click");
const LOCAL_AGGREGATE_SOURCE: &str =
    include_str!("fixtures/cpp-verification/local-aggregate/stage_restore.cpp");
const LOCAL_AGGREGATE_SIDECAR: &str =
    include_str!("fixtures/cpp-verification/local-aggregate/stage_restore.click");
const CONSTRUCTOR_LOCAL_SOURCE: &str =
    include_str!("fixtures/cpp-verification/constructor-local/capture.cpp");
const CONSTRUCTOR_LOCAL_SIDECAR: &str =
    include_str!("fixtures/cpp-verification/constructor-local/capture.click");
const TERMINAL_DESTRUCTOR_SOURCE: &str =
    include_str!("fixtures/cpp-verification/terminal-destructor/capture.cpp");
const TERMINAL_DESTRUCTOR_SIDECAR: &str =
    include_str!("fixtures/cpp-verification/terminal-destructor/capture.click");
const EARLY_RETURN_DESTRUCTOR_SOURCE: &str = include_str!("../examples/basic-cpp/with_restore.cpp");
const EARLY_RETURN_DESTRUCTOR_SIDECAR: &str =
    include_str!("../examples/basic-cpp/with_restore.click");
const RESTORE_CALLER_SOURCE: &str = include_str!("../examples/basic-cpp/with_restore_caller.cpp");
const RESTORE_CALLER_SIDECAR: &str =
    include_str!("../examples/basic-cpp/with_restore_caller.click");
const REVERSE_DESTRUCTOR_SOURCE: &str =
    include_str!("fixtures/cpp-verification/reverse-destructor-order/restore_twice.cpp");
const REVERSE_DESTRUCTOR_SIDECAR: &str =
    include_str!("fixtures/cpp-verification/reverse-destructor-order/restore_twice.click");
const NESTED_SCOPE_DESTRUCTOR_SOURCE: &str =
    include_str!("fixtures/cpp-verification/nested-scope-destructor/scoped_restore.cpp");
const NESTED_SCOPE_DESTRUCTOR_SIDECAR: &str =
    include_str!("fixtures/cpp-verification/nested-scope-destructor/scoped_restore.click");
const SIBLING_SCOPE_DESTRUCTORS_SOURCE: &str =
    include_str!("fixtures/cpp-verification/sibling-scope-destructors/sibling_restore.cpp");
const SIBLING_SCOPE_DESTRUCTORS_SIDECAR: &str =
    include_str!("fixtures/cpp-verification/sibling-scope-destructors/sibling_restore.click");
const OVERLAPPING_SCOPE_DESTRUCTORS_SOURCE: &str =
    include_str!("fixtures/cpp-verification/overlapping-scope-destructors/overlap_restore.cpp");
const OVERLAPPING_SCOPE_DESTRUCTORS_SIDECAR: &str =
    include_str!("fixtures/cpp-verification/overlapping-scope-destructors/overlap_restore.click");
const CONDITIONAL_CONSTRUCTION_SOURCE: &str =
    include_str!("fixtures/cpp-verification/conditional-construction/conditional_restore.cpp");
const CONDITIONAL_CONSTRUCTION_SIDECAR: &str =
    include_str!("fixtures/cpp-verification/conditional-construction/conditional_restore.click");
const INT64_PREDICATE_SOURCE: &str =
    include_str!("fixtures/cpp-verification/int64-predicate/money_nonnegative.cpp");
const INT64_PREDICATE_SIDECAR: &str =
    include_str!("fixtures/cpp-verification/int64-predicate/money_nonnegative.click");
const CONSTEXPR_COIN_SOURCE: &str =
    include_str!("fixtures/cpp-verification/constexpr-coin/at_least_one_coin.cpp");
const CONSTEXPR_COIN_SIDECAR: &str =
    include_str!("fixtures/cpp-verification/constexpr-coin/at_least_one_coin.click");
const CONSTEXPR_COIN_CSTDINT: &str =
    include_str!("fixtures/cpp-verification/constexpr-coin/cstdint");
const CONSTEXPR_MAX_MONEY_SOURCE: &str =
    include_str!("fixtures/cpp-verification/constexpr-max-money/at_least_max_money.cpp");
const CONSTEXPR_MAX_MONEY_SIDECAR: &str =
    include_str!("fixtures/cpp-verification/constexpr-max-money/at_least_max_money.click");
const CONSTEXPR_MAX_MONEY_LE_SIDECAR: &str =
    include_str!("fixtures/cpp-verification/constexpr-max-money/at_most_max_money.click");
const CONSTEXPR_MAX_MONEY_RANGE_SIDECAR: &str =
    include_str!("fixtures/cpp-verification/constexpr-max-money/money_range.click");
const CONSTEXPR_MAX_MONEY_CSTDINT: &str =
    include_str!("fixtures/cpp-verification/constexpr-max-money/cstdint");
const ONE_GUARD_UNWIND_MDTEST: &str = include_str!("../mdtests/cpp_one_guard_unwind.md");
const GUARD_BEFORE_SECOND_MDTEST: &str =
    include_str!("../mdtests/cpp_guard_unwind_before_second.md");

struct Project {
    directory: PathBuf,
    exporter: PathBuf,
    source_name: String,
    dependencies: Vec<String>,
}

impl Project {
    fn new() -> Self {
        Self::with_fixture("increment.cpp", "increment", SOURCE)
    }

    fn branch_return() -> Self {
        Self::with_fixture("choose.cpp", "choose", BRANCH_SOURCE)
    }

    fn const_reference_alias() -> Self {
        Self::with_fixture(
            "write_then_read.cpp",
            "write_then_read",
            CONST_REFERENCE_SOURCE,
        )
    }

    fn direct_call() -> Self {
        Self::with_fixture("call_set_seven.cpp", "call_set_seven", DIRECT_CALL_SOURCE)
    }

    fn scalar_local() -> Self {
        Self::with_fixture("relay_value.cpp", "relay_value", SCALAR_LOCAL_SOURCE)
    }

    fn pointer() -> Self {
        Self::with_fixture("bump_reference.cpp", "bump_reference", POINTER_SOURCE)
    }

    fn struct_member() -> Self {
        Self::with_fixture("stage_restore.cpp", "stage_restore", STRUCT_MEMBER_SOURCE)
    }

    fn local_aggregate() -> Self {
        Self::with_fixture("stage_restore.cpp", "stage_restore", LOCAL_AGGREGATE_SOURCE)
    }

    fn constructor_local() -> Self {
        Self::with_fixture("capture.cpp", "capture", CONSTRUCTOR_LOCAL_SOURCE)
    }

    fn terminal_destructor() -> Self {
        Self::with_fixture("capture.cpp", "capture", TERMINAL_DESTRUCTOR_SOURCE)
    }

    fn early_return_destructor() -> Self {
        Self::with_fixture(
            "with_restore.cpp",
            "with_restore",
            EARLY_RETURN_DESTRUCTOR_SOURCE,
        )
    }

    fn restore_caller() -> Self {
        Self::with_fixture(
            "with_restore_caller.cpp",
            "call_with_restore",
            RESTORE_CALLER_SOURCE,
        )
    }

    fn reverse_destructor_order() -> Self {
        Self::with_fixture(
            "restore_twice.cpp",
            "restore_twice",
            REVERSE_DESTRUCTOR_SOURCE,
        )
    }

    fn nested_scope_destructor() -> Self {
        Self::with_fixture(
            "scoped_restore.cpp",
            "scoped_restore",
            NESTED_SCOPE_DESTRUCTOR_SOURCE,
        )
    }

    fn sibling_scope_destructors() -> Self {
        Self::with_fixture(
            "sibling_restore.cpp",
            "sibling_restore",
            SIBLING_SCOPE_DESTRUCTORS_SOURCE,
        )
    }

    fn overlapping_scope_destructors() -> Self {
        Self::with_fixture(
            "overlap_restore.cpp",
            "overlap_restore",
            OVERLAPPING_SCOPE_DESTRUCTORS_SOURCE,
        )
    }

    fn conditional_construction() -> Self {
        Self::with_fixture(
            "conditional_restore.cpp",
            "conditional_restore",
            CONDITIONAL_CONSTRUCTION_SOURCE,
        )
    }

    fn header_function() -> Self {
        let project = Self::with_fixture(
            "driver.cpp",
            "header_increment",
            "#include \"selected.h\"\n",
        );
        fs::write(
            project.logical_header(),
            "inline int header_increment(int& value) noexcept {\n    value = value + 1;\n    return value;\n}\n",
        )
        .unwrap();
        project.write_config_with_logical_source("header_increment", "selected.h");
        project
    }

    fn exception_enabled_header_function() -> Self {
        let project = Self::header_function();
        fs::write(
            project.logical_header(),
            "inline int header_increment(int& value) {\n    value = value + 1;\n    return value;\n}\n",
        )
        .unwrap();
        project.write_exception_enabled_compilation_database();
        project.write_config_with_profile("header_increment", "selected.h", true);
        project
    }

    fn int64_predicate() -> Self {
        let project = Self::with_fixture(
            "money_nonnegative.cpp",
            "money_nonnegative",
            INT64_PREDICATE_SOURCE,
        );
        project.write_exception_enabled_compilation_database();
        project.write_config_with_profile("money_nonnegative", "money_nonnegative.cpp", true);
        project
    }

    fn constexpr_coin() -> Self {
        let mut project = Self::with_fixture(
            "at_least_one_coin.cpp",
            "at_least_one_coin",
            CONSTEXPR_COIN_SOURCE,
        );
        fs::write(project.directory.join("cstdint"), CONSTEXPR_COIN_CSTDINT).unwrap();
        project.dependencies.push("cstdint".into());
        project.write_exception_enabled_compilation_database_with_local_include();
        project.write_config_with_profile("at_least_one_coin", "at_least_one_coin.cpp", true);
        project
    }

    fn constexpr_max_money() -> Self {
        let mut project = Self::with_fixture(
            "at_least_max_money.cpp",
            "at_least_max_money",
            CONSTEXPR_MAX_MONEY_SOURCE,
        );
        fs::write(
            project.directory.join("cstdint"),
            CONSTEXPR_MAX_MONEY_CSTDINT,
        )
        .unwrap();
        project.dependencies.push("cstdint".into());
        project.write_exception_enabled_compilation_database_with_local_include();
        project.write_config_with_profile("at_least_max_money", "at_least_max_money.cpp", true);
        project
    }

    fn constexpr_max_money_less_equal() -> Self {
        let project = Self::constexpr_max_money();
        project.write_config_with_profile("at_most_max_money", "at_least_max_money.cpp", true);
        project
    }

    fn constexpr_max_money_range() -> Self {
        let project = Self::constexpr_max_money();
        project.write_config_with_profile("money_range", "at_least_max_money.cpp", true);
        project
    }

    fn with_fixture(source_name: &str, function: &str, source: &str) -> Self {
        static NEXT: AtomicUsize = AtomicUsize::new(0);
        let directory = std::env::temp_dir().join(format!(
            "click-cpp-import-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        if directory.exists() {
            fs::remove_dir_all(&directory).unwrap();
        }
        fs::create_dir(&directory).unwrap();
        let built_exporter = std::env::var_os("CLICK_CPP_EXPORTER")
            .map(PathBuf::from)
            .expect("scripts/check.sh supplies the pinned C++ exporter");
        let exporter = directory.join("click-cpp-exporter");
        fs::copy(&built_exporter, &exporter).expect("copy C++ exporter into isolated fixture");
        fs::write(directory.join(source_name), source).unwrap();
        let project = Self {
            directory,
            exporter,
            source_name: source_name.to_string(),
            dependencies: Vec::new(),
        };
        project.write_compilation_database();
        project.write_config(function);
        project
    }

    fn config(&self) -> PathBuf {
        self.directory.join("demo.click.import.json")
    }

    fn artifact(&self) -> PathBuf {
        self.directory
            .join(format!("{}.click-cpp.json", self.source_name))
    }

    fn lock(&self) -> PathBuf {
        self.directory.join("demo.click.import.json.lock")
    }

    fn source(&self) -> PathBuf {
        self.directory.join(&self.source_name)
    }

    fn logical_header(&self) -> PathBuf {
        self.directory.join("selected.h")
    }

    fn compilation_database(&self) -> PathBuf {
        self.directory.join("compile_commands.json")
    }

    fn compilation_arguments(&self) -> Vec<String> {
        [
            "clang++",
            "-x",
            "c++",
            "-std=c++20",
            "--target=x86_64-unknown-linux-gnu",
            "-fno-exceptions",
            "-fno-rtti",
            "-funsigned-char",
            "-ffreestanding",
            "-nostdinc",
            "-nostdinc++",
            "-Wno-reorder-ctor",
            "-c",
            &self.source_name,
            "-o",
            "fixture.o",
        ]
        .into_iter()
        .map(str::to_string)
        .collect()
    }

    fn exception_enabled_compilation_arguments(&self) -> Vec<String> {
        self.compilation_arguments()
            .into_iter()
            .map(|argument| {
                if argument == "-fno-exceptions" {
                    "-fexceptions".into()
                } else {
                    argument
                }
            })
            .collect()
    }

    fn write_compilation_database(&self) {
        self.write_compilation_database_commands(&[self.compilation_arguments()]);
    }

    fn write_exception_enabled_compilation_database(&self) {
        self.write_compilation_database_commands(&[self.exception_enabled_compilation_arguments()]);
    }

    fn write_exception_enabled_compilation_database_with_local_include(&self) {
        let mut arguments = self.exception_enabled_compilation_arguments();
        let compile = arguments
            .iter()
            .position(|argument| argument == "-c")
            .expect("fixture compilation command has -c");
        arguments.insert(compile, "-I.".into());
        self.write_compilation_database_commands(&[arguments]);
    }

    fn write_compilation_database_commands(&self, commands: &[Vec<String>]) {
        let database = commands
            .iter()
            .map(|arguments| {
                serde_json::json!({
                    "directory": self.directory,
                    "file": self.source_name,
                    "arguments": arguments,
                    "output": "fixture.o"
                })
            })
            .collect::<Vec<_>>();
        let mut bytes = serde_json::to_vec_pretty(&database).unwrap();
        bytes.push(b'\n');
        fs::write(self.compilation_database(), bytes).unwrap();
    }

    fn write_compilation_database_command_string(&self, command: &str) {
        let database = serde_json::json!([{
            "directory": self.directory,
            "file": self.source_name,
            "command": command,
            "output": "fixture.o"
        }]);
        let mut bytes = serde_json::to_vec_pretty(&database).unwrap();
        bytes.push(b'\n');
        fs::write(self.compilation_database(), bytes).unwrap();
    }

    fn write_config(&self, function: &str) {
        self.write_config_with_logical_source(function, &self.source_name);
    }

    fn write_config_with_logical_source(&self, function: &str, logical_source: &str) {
        self.write_config_with_profile(function, logical_source, false);
    }

    fn write_config_with_profile(&self, function: &str, logical_source: &str, exceptions: bool) {
        self.write_config_with_exception_behavior(
            function,
            logical_source,
            exceptions,
            "normal_only",
        );
    }

    fn write_config_with_exception_behavior(
        &self,
        function: &str,
        logical_source: &str,
        exceptions: bool,
        exception_behavior: &str,
    ) {
        let config = serde_json::json!({
            "schema": 6,
            "language": "c++",
            "standard": "c++20",
            "target": "x86_64-unknown-linux-gnu",
            "exceptions": exceptions,
            "exception_behavior": exception_behavior,
            "rtti": false,
            "exporter": self.exporter,
            "compilation_database": "compile_commands.json",
            "working_directory": ".",
            "source": &self.source_name,
            "logical_source": logical_source,
            "dependencies": &self.dependencies,
            "function": function,
            "artifact": format!("{}.click-cpp.json", self.source_name)
        });
        let mut bytes = serde_json::to_vec_pretty(&config).unwrap();
        bytes.push(b'\n');
        fs::write(self.config(), bytes).unwrap();
    }
}

impl Drop for Project {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.directory);
    }
}

#[test]
fn clang_export_is_deterministic_typed_and_loads_without_clang() {
    let project = Project::new();
    let output = Command::new(env!("CARGO_BIN_EXE_click"))
        .args([
            "import",
            "lock",
            project.directory.join("demo.click").to_str().unwrap(),
        ])
        .output()
        .expect("run the ordinary import command");
    assert!(
        output.status.success(),
        "click import failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let first_artifact = fs::read(project.artifact()).unwrap();
    let first_lock = fs::read(project.lock()).unwrap();
    refresh_import(&project.config()).expect("repeat the same semantic export");
    assert_eq!(fs::read(project.artifact()).unwrap(), first_artifact);
    assert_eq!(fs::read(project.lock()).unwrap(), first_lock);

    fs::remove_file(&project.exporter).expect("make the frontend unavailable after refresh");
    let prepared = load_import(&project.config()).expect("locked loading must not execute Clang");
    assert_eq!(prepared.export().schema, 33);
    assert!(prepared.export().reachable_functions.is_empty());
    assert_eq!(prepared.logical_source(), "increment.cpp");
    assert_eq!(prepared.identity().len(), 64);
    assert_eq!(
        prepared.export().profile.compilation_directory,
        project.directory.to_string_lossy()
    );
    assert_eq!(
        prepared.export().profile.compilation_file,
        project.source_name
    );
    assert_eq!(
        prepared.export().profile.compilation_command,
        project.compilation_arguments()
    );
    let function = &prepared.export().function;
    assert_eq!(function.name, "increment");
    assert!(function.declaration_id.starts_with("c:@F@increment#"));
    assert_eq!(
        function.parameters[0].value_type,
        CppType::LvalueReference {
            pointee: Box::new(CppType::Integer {
                bits: 32,
                signed: true,
                is_const: false,
                source_aliases: Vec::new(),
            }),
        }
    );
    let CppStatement::Assign { value, .. } = &function.body[0] else {
        panic!("first semantic operation was not assignment")
    };
    assert!(matches!(
        value,
        CppExpression::Binary {
            operator: CppBinaryOperator::Add,
            left,
            right,
            ..
        } if matches!(left.as_ref(), CppExpression::Load { .. })
            && matches!(right.as_ref(), CppExpression::IntegerLiteral { value, .. } if value == "1")
    ));
    assert!(matches!(
        function.body[1],
        CppStatement::Return {
            value: CppExpression::Load { .. },
            ..
        }
    ));
}

#[test]
fn out_of_tree_compilation_locks_dependency_root_and_rtti_profile() {
    let project = Project::constexpr_coin();
    let build = project.directory.join("build");
    fs::create_dir(&build).unwrap();
    let mut arguments = project.exception_enabled_compilation_arguments();
    for argument in &mut arguments {
        if argument == "-fno-rtti" {
            *argument = "-frtti".into();
        } else if argument == &project.source_name {
            *argument = project.source().to_string_lossy().into_owned();
        }
    }
    arguments.insert(1, format!("-I{}", project.directory.display()));
    let database = serde_json::json!([{
        "directory": build,
        "file": project.source(),
        "arguments": arguments,
        "output": "fixture.o"
    }]);
    fs::write(
        build.join("compile_commands.json"),
        serde_json::to_vec_pretty(&database).unwrap(),
    )
    .unwrap();
    let mut config: serde_json::Value =
        serde_json::from_slice(&fs::read(project.config()).unwrap()).unwrap();
    config["compilation_database"] = "build/compile_commands.json".into();
    config["rtti"] = true.into();
    fs::write(
        project.config(),
        serde_json::to_vec_pretty(&config).unwrap(),
    )
    .unwrap();

    refresh_import(&project.config()).expect("export with out-of-tree build directory");
    let prepared = load_import(&project.config()).expect("offline import");
    assert!(prepared.export().profile.exceptions);
    assert!(prepared.export().profile.rtti);
    assert_eq!(prepared.export().dependencies, ["cstdint"]);
    assert_eq!(
        prepared.export().profile.compilation_directory,
        build.to_string_lossy()
    );

    fs::write(
        project.directory.join("cstdint"),
        "typedef long int64_t;\n// changed\n",
    )
    .unwrap();
    assert!(
        load_import(&project.config())
            .unwrap_err()
            .contains("dependency inventory differs")
    );
}

#[test]
fn every_opened_header_is_locked_even_outside_the_reachable_graph() {
    let project = Project::new();
    let header = project.directory.join("prelude.h");
    fs::write(&header, "#define PRELUDE 1\n").unwrap();
    fs::write(
        project.source(),
        format!("#include \"prelude.h\"\n{SOURCE}"),
    )
    .unwrap();

    refresh_import(&project.config()).expect("lock all opened headers");
    let prepared = load_import(&project.config()).expect("load unmodified header");
    assert!(prepared.export().dependencies.is_empty());
    let canonical_header = header.canonicalize().unwrap();
    assert!(
        prepared
            .export()
            .preprocessor_files
            .iter()
            .any(|file| { file.canonical_path == canonical_header.to_string_lossy() })
    );

    fs::write(&header, "#define PRELUDE 2\n").unwrap();
    assert!(
        load_import(&project.config())
            .unwrap_err()
            .contains("preprocessor input inventory differs")
    );
}

#[cfg(unix)]
#[test]
fn opened_header_symlink_target_is_locked() {
    use std::os::unix::fs::symlink;

    let project = Project::new();
    let header = project.directory.join("prelude.h");
    let first = project.directory.join("first.h");
    let second = project.directory.join("second.h");
    fs::write(&first, "#define PRELUDE 1\n").unwrap();
    fs::write(&second, "#define PRELUDE 1\n").unwrap();
    symlink(&first, &header).unwrap();
    fs::write(
        project.source(),
        format!("#include \"prelude.h\"\n{SOURCE}"),
    )
    .unwrap();

    refresh_import(&project.config()).expect("lock symlinked header");
    let prepared = load_import(&project.config()).expect("load original target");
    assert!(prepared.export().preprocessor_files.iter().any(|file| {
        file.accessed_path.ends_with("/prelude.h")
            && file.canonical_path == first.canonicalize().unwrap().to_string_lossy()
    }));

    fs::remove_file(&header).unwrap();
    symlink(&second, &header).unwrap();
    assert!(
        load_import(&project.config())
            .unwrap_err()
            .contains("changed its resolved target")
    );
}

#[test]
fn compilation_database_command_is_selected_locked_and_validated() {
    let project = Project::new();
    refresh_import(&project.config()).expect("export through the selected compilation command");
    let first = load_import(&project.config()).expect("load the locked compilation command");
    let first_identity = first.identity().to_string();
    let lock: serde_json::Value =
        serde_json::from_slice(&fs::read(project.lock()).unwrap()).unwrap();
    assert_eq!(
        lock["compilation_database_sha256"].as_str().unwrap().len(),
        64
    );
    assert_eq!(
        lock["profile"]["compilation_command"],
        serde_json::json!(project.compilation_arguments())
    );

    let mut changed = project.compilation_arguments();
    changed.insert(changed.len() - 4, "-DCLICK_COMMAND_VARIANT=1".into());
    project.write_compilation_database_commands(&[changed.clone()]);
    let error = load_import(&project.config()).unwrap_err();
    assert!(error.contains("compilation database differs"), "{error}");
    refresh_import(&project.config()).expect("refresh after an explicit command change");
    let refreshed = load_import(&project.config()).unwrap();
    assert_ne!(refreshed.identity(), first_identity);
    assert_eq!(refreshed.export().profile.compilation_command, changed);

    let command_string = Project::new();
    let arguments = command_string.compilation_arguments();
    command_string.write_compilation_database_command_string(&arguments.join(" "));
    refresh_import(&command_string.config()).expect("parse a CMake-style command string entry");
    assert_eq!(
        load_import(&command_string.config())
            .unwrap()
            .export()
            .profile
            .compilation_command,
        arguments
    );

    let missing = Project::new();
    missing.write_compilation_database_commands(&[]);
    let error = refresh_import(&missing.config()).unwrap_err();
    assert!(error.contains("has no command"), "{error}");
    assert!(!missing.artifact().exists());

    let ambiguous = Project::new();
    let command = ambiguous.compilation_arguments();
    ambiguous.write_compilation_database_commands(&[command.clone(), command]);
    let error = refresh_import(&ambiguous.config()).unwrap_err();
    assert!(error.contains("exactly one is required"), "{error}");
    assert!(!ambiguous.artifact().exists());

    let wrong_driver = Project::new();
    let mut command = wrong_driver.compilation_arguments();
    command[0] = "g++".into();
    wrong_driver.write_compilation_database_commands(&[command]);
    let error = refresh_import(&wrong_driver.config()).unwrap_err();
    assert!(error.contains("pinned Clang driver"), "{error}");
    assert!(!wrong_driver.artifact().exists());

    for untracked in ["@flags.rsp", "-include-pch", "-ivfsoverlay"] {
        let project = Project::new();
        let mut command = project.compilation_arguments();
        command.insert(1, untracked.into());
        project.write_compilation_database_commands(&[command]);
        let error = refresh_import(&project.config()).unwrap_err();
        assert!(
            error.contains("untracked preprocessor input mode"),
            "{error}"
        );
        assert!(!project.artifact().exists());
    }

    let wrong_standard = Project::new();
    let command = wrong_standard
        .compilation_arguments()
        .into_iter()
        .map(|argument| {
            if argument == "-std=c++20" {
                "-std=gnu++20".into()
            } else {
                argument
            }
        })
        .collect::<Vec<_>>();
    wrong_standard.write_compilation_database_commands(&[command]);
    let error = refresh_import(&wrong_standard.config()).unwrap_err();
    assert!(
        error.contains("profile must match the configured"),
        "{error}"
    );
    assert!(!wrong_standard.artifact().exists());

    let wrong_target = Project::new();
    let command = wrong_target
        .compilation_arguments()
        .into_iter()
        .map(|argument| {
            if argument == "--target=x86_64-unknown-linux-gnu" {
                "--target=aarch64-unknown-linux-gnu".into()
            } else {
                argument
            }
        })
        .collect::<Vec<_>>();
    wrong_target.write_compilation_database_commands(&[command]);
    let error = refresh_import(&wrong_target.config()).unwrap_err();
    assert!(
        error.contains("profile must match the configured"),
        "{error}"
    );
    assert!(!wrong_target.artifact().exists());
}

#[test]
fn included_header_definition_is_selected_locked_and_validated() {
    let project = Project::header_function();
    refresh_import(&project.config()).expect("export the selected header definition");
    let lock: serde_json::Value =
        serde_json::from_slice(&fs::read(project.lock()).unwrap()).unwrap();
    assert_eq!(lock["logical_source_sha256"].as_str().unwrap().len(), 64);

    let prepared = load_import(&project.config()).expect("load the locked header definition");
    assert_eq!(prepared.logical_source(), "selected.h");
    assert_eq!(prepared.export().logical_source, "selected.h");
    assert_eq!(prepared.export().profile.compilation_file, "driver.cpp");
    assert_eq!(prepared.export().function.name, "header_increment");
    assert_eq!(prepared.export().function.span.file, "selected.h");

    let sidecar = project.directory.join("demo.click");
    let sidecar_source = SIDECAR
        .replace("increment.cpp", "selected.h")
        .replace("increment", "header_increment");
    fs::write(&sidecar, &sidecar_source).unwrap();
    fs::remove_file(&project.exporter).expect("make the exporter unavailable after refresh");
    let inputs = read_c_inputs(&sidecar, &sidecar_source).expect("load the header import offline");
    let CInput::PreparedProgram(import) = inputs else {
        panic!("language=c++ must select the C++ prepared-input path")
    };
    let click_project = read_click_project(&sidecar, &sidecar_source).unwrap();
    verify_program_prepared_project(&click_project, &import)
        .expect("verify the selected header function through the ordinary workflow");

    let stale = Project::header_function();
    refresh_import(&stale.config()).expect("lock the original header contents");
    let original_identity = load_import(&stale.config()).unwrap().identity().to_string();
    fs::write(
        stale.logical_header(),
        "inline int header_increment(int& value) noexcept {\n    value = value + 1;\n    return value;\n}\n\n",
    )
    .unwrap();
    let error = load_import(&stale.config()).unwrap_err();
    assert!(error.contains("logical source differs"), "{error}");
    refresh_import(&stale.config()).expect("refresh after changing the selected header");
    assert_ne!(
        load_import(&stale.config()).unwrap().identity(),
        original_identity
    );

    let wrong_location = Project::header_function();
    fs::write(
        wrong_location.directory.join("wrong.h"),
        "// not selected\n",
    )
    .unwrap();
    wrong_location.write_config_with_logical_source("header_increment", "wrong.h");
    let error = refresh_import(&wrong_location.config()).unwrap_err();
    assert!(error.contains("was not found"), "{error}");
    assert!(!wrong_location.artifact().exists());

    let ambiguous = Project::header_function();
    fs::write(
        ambiguous.logical_header(),
        "inline int header_increment(int& value) noexcept { return value; }\ninline int header_increment(const int& value) noexcept { return value; }\n",
    )
    .unwrap();
    let error = refresh_import(&ambiguous.config()).unwrap_err();
    assert!(error.contains("is overloaded"), "{error}");
    assert!(!ambiguous.artifact().exists());
}

#[test]
fn exception_enabled_profile_verifies_a_checked_normal_only_header_graph() {
    let project = Project::exception_enabled_header_function();
    refresh_import(&project.config()).expect("export the exception-enabled normal-only function");
    let prepared = load_import(&project.config()).expect("load the locked semantic artifact");
    assert!(prepared.export().profile.exceptions);
    assert_eq!(
        prepared.export().exception_behavior,
        CppExceptionBehavior::NormalOnly
    );
    assert!(!prepared.export().function.declared_noexcept);
    assert!(prepared.export().records.is_empty());

    let sidecar = project.directory.join("demo.click");
    let sidecar_source = SIDECAR
        .replace("increment.cpp", "selected.h")
        .replace("increment", "header_increment");
    fs::write(&sidecar, &sidecar_source).unwrap();
    fs::remove_file(&project.exporter).expect("make the exporter unavailable after refresh");
    let inputs = read_c_inputs(&sidecar, &sidecar_source)
        .expect("load the exception-enabled header import offline");
    let CInput::PreparedProgram(import) = inputs else {
        panic!("language=c++ must select the C++ prepared-input path")
    };
    let click_project = read_click_project(&sidecar, &sidecar_source).unwrap();
    verify_program_prepared_project(&click_project, &import)
        .expect("verify the normal-only function through the ordinary workflow");

    let graph = Project::direct_call();
    fs::write(
        graph.source(),
        "int set_seven(int& value) {\n    value = 7;\n    return value;\n}\n\nint call_set_seven(int& value) {\n    set_seven(value);\n    return value;\n}\n",
    )
    .unwrap();
    graph.write_exception_enabled_compilation_database();
    graph.write_config_with_profile("call_set_seven", "call_set_seven.cpp", true);
    refresh_import(&graph.config()).expect("export a closed normal-only direct-call graph");
    let graph = load_import(&graph.config()).unwrap();
    assert!(!graph.export().function.declared_noexcept);
    assert_eq!(graph.export().reachable_functions.len(), 1);
    assert!(!graph.export().reachable_functions[0].declared_noexcept);
}

#[test]
fn scalar_int32_profile_verifies_a_typed_throw_and_keeps_its_lock_identity() {
    let project = Project::new();
    fs::write(project.source(), "int increment(int& value) { throw 7; }\n").unwrap();
    project.write_exception_enabled_compilation_database();
    project.write_config_with_exception_behavior(
        "increment",
        "increment.cpp",
        true,
        "scalar_int32",
    );
    refresh_import(&project.config()).expect("export a typed scalar throw");
    let prepared = load_import(&project.config()).expect("load the locked scalar exception");
    assert_eq!(
        prepared.export().exception_behavior,
        CppExceptionBehavior::ScalarInt32
    );
    assert!(matches!(
        prepared.export().function.body.as_slice(),
        [CppStatement::Throw { .. }]
    ));

    let sidecar_source = "verifying \"increment.cpp\";\n\
        int32 increment(int32* value) throws int32 {\n\
            ensures result == 0;\n\
            exceptional ensures exception == 7;\n\
        }\n";
    let sidecar = project.directory.join("demo.click");
    fs::write(&sidecar, sidecar_source).unwrap();
    fs::remove_file(&project.exporter).expect("make the exporter unavailable after refresh");
    let click_project = read_click_project(&sidecar, sidecar_source).unwrap();
    verify_program_prepared_project(&click_project, &prepared)
        .expect("a source throw must establish the declared exceptional outcome");

    let missing_signature = "verifying \"increment.cpp\";\n\
        int32 increment(int32* value) { ensures result == 0; }\n";
    let missing_signature_project = read_click_project(&sidecar, missing_signature).unwrap();
    verify_program_prepared_project(&missing_signature_project, &prepared)
        .expect_err("a source throw cannot cross an undeclared exceptional boundary");
}

#[test]
fn scalar_int32_profile_propagates_a_modular_throw_past_a_normal_call_continuation() {
    let project = Project::with_fixture(
        "caller.cpp",
        "caller",
        "int helper(bool should_throw) {\n\
             if (should_throw) { throw 7; }\n\
             return 5;\n\
         }\n\
         int caller(bool should_throw) {\n\
             int result = helper(should_throw);\n\
             result = 5;\n\
             return result;\n\
         }\n",
    );
    project.write_exception_enabled_compilation_database();
    project.write_config_with_exception_behavior("caller", "caller.cpp", true, "scalar_int32");
    refresh_import(&project.config()).expect("export both reachable outcomes");
    let prepared = load_import(&project.config()).expect("load the locked call graph");
    assert_eq!(prepared.export().reachable_functions.len(), 1);
    let sidecar_source = "verifying \"caller.cpp\";\n\
        int32 helper(bool should_throw) throws int32 {\n\
            ensures result == 5;\n\
            exceptional ensures exception == 7;\n\
        }\n\
        int32 caller(bool should_throw) throws int32 {\n\
            ensures result == 5;\n\
            exceptional ensures exception == 7;\n\
        }\n";
    let sidecar = project.directory.join("demo.click");
    fs::write(&sidecar, sidecar_source).unwrap();
    let click_project = read_click_project(&sidecar, sidecar_source).unwrap();
    verify_program_prepared_project(&click_project, &prepared)
        .expect("the caller must preserve the helper's exceptional exit");
    let expanded = expand_program_prepared_project_claim_source_by_label(
        &click_project,
        &prepared,
        "caller.exceptional_ensures_0",
    )
    .expect("expand the caller's exceptional proof");
    let rewritten = click_project.with_entry_source(expanded.clone());
    verify_program_prepared_project(&rewritten, &prepared)
        .expect("the expanded exceptional proof must reverify");
    let (session, _) = C0VerificationSession::new_program_prepared_project(&rewritten, &prepared)
        .expect("retain the expanded scalar exception environment");
    let site = program_prepared_project_tactic_source_position(
        &rewritten,
        &prepared,
        "caller.exceptional_ensures_0",
        0,
    )
    .expect("locate the expanded exceptional proof");
    session
        .verify_at_project(&expanded, site.line, site.column)
        .expect("retained audit must accept the expanded exceptional proof");

    let mut false_caller_claim = sidecar_source.to_string();
    let claim = "exceptional ensures exception == 7;";
    let caller_claim = false_caller_claim
        .rfind(claim)
        .expect("caller exception claim");
    false_caller_claim.replace_range(
        caller_claim..caller_claim + claim.len(),
        "exceptional ensures exception == 8;",
    );
    let false_project = read_click_project(&sidecar, &false_caller_claim).unwrap();
    verify_program_prepared_project(&false_project, &prepared)
        .expect_err("the caller cannot claim a different exception payload");
}

#[test]
fn scalar_int32_profile_catches_a_modular_throw_with_a_typed_payload() {
    let project = Project::with_fixture(
        "caller.cpp",
        "caller",
        "int helper(bool should_throw) {\n\
             if (should_throw) { throw 7; }\n\
             return 7;\n\
         }\n\
         int caller(bool should_throw) {\n\
             try { helper(should_throw); }\n\
             catch (int caught) { return caught; }\n\
             return 7;\n\
         }\n",
    );
    project.write_exception_enabled_compilation_database();
    project.write_config_with_exception_behavior("caller", "caller.cpp", true, "scalar_int32");
    refresh_import(&project.config()).expect("export the exact scalar handler");
    let prepared = load_import(&project.config()).expect("load the typed handler offline");
    let [
        CppStatement::TryCatchInt32 {
            binding,
            try_body,
            handler,
            ..
        },
        CppStatement::Return { .. },
    ] = prepared.export().function.body.as_slice()
    else {
        panic!("the source try/catch was not retained as a typed handler");
    };
    assert_eq!(binding.name, "caught");
    assert!(matches!(
        binding.value_type,
        CppType::Integer {
            bits: 32,
            signed: true,
            is_const: false,
            ..
        }
    ));
    assert!(matches!(try_body.as_slice(), [CppStatement::Call { .. }]));
    assert!(matches!(handler.as_slice(), [CppStatement::Return { .. }]));

    let sidecar_source = "verifying \"caller.cpp\";\n\
        int32 helper(bool should_throw) throws int32 {\n\
            ensures result == 7;\n\
            exceptional ensures exception == 7;\n\
        }\n\
        int32 caller(bool should_throw) {\n\
            ensures result == 7;\n\
        }\n";
    let sidecar = project.directory.join("demo.click");
    fs::write(&sidecar, sidecar_source).unwrap();
    fs::remove_file(&project.exporter).expect("verification must use the locked artifact");
    let click_project = read_click_project(&sidecar, sidecar_source).unwrap();
    verify_program_prepared_project(&click_project, &prepared)
        .expect("a caught modular throw should satisfy a nonthrowing caller signature");
    let expanded = expand_program_prepared_project_claim_source_by_label(
        &click_project,
        &prepared,
        "caller.ensures_0",
    )
    .expect("expand the handler proof");
    let returned_proof = expanded
        .split_once("returned {")
        .and_then(|(_, rest)| rest.split_once("threw {"))
        .map(|(returned, _)| returned)
        .expect("the expansion must keep a returned certificate");
    let threw_proof = expanded
        .split_once("threw {")
        .map(|(_, threw)| threw)
        .expect("the expansion must keep a threw certificate");
    assert!(
        expanded.contains("outcomes {")
            && returned_proof.contains("normalize();")
            && threw_proof.contains("assumption();")
            && !threw_proof.contains("normalize();")
            && !expanded.contains("trivial();"),
        "distinct exact path closers should retain returned/threw certificates: {expanded}"
    );
    let rewritten = click_project.with_entry_source(expanded.clone());
    verify_program_prepared_project(&rewritten, &prepared)
        .expect("the expanded handler proof must reverify");
    let (session, _) = C0VerificationSession::new_program_prepared_project(&rewritten, &prepared)
        .expect("retain the expanded handler environment");
    let site = program_prepared_project_tactic_source_position(
        &rewritten,
        &prepared,
        "caller.ensures_0",
        0,
    )
    .expect("locate the expanded handler proof");
    session
        .verify_at_project(&expanded, site.line, site.column)
        .expect("retained audit must accept the handler proof");

    let mut false_claim = sidecar_source.to_string();
    let caller_claim = false_claim
        .rfind("ensures result == 7;")
        .expect("caller claim");
    false_claim.replace_range(
        caller_claim..caller_claim + "ensures result == 7;".len(),
        "ensures result == 8;",
    );
    assert_ne!(false_claim, sidecar_source);
    let false_project = read_click_project(&sidecar, &false_claim).unwrap();
    verify_program_prepared_project(&false_project, &prepared)
        .expect_err("the handler cannot prove a false result claim");
}

#[test]
fn scalar_int32_profile_joins_a_caught_throw_inside_conditional_cleanup() {
    let project = Project::with_fixture(
        "caller.cpp",
        "caller",
        "struct Restore {\n\
             int* pointer;\n\
             int saved;\n\
             explicit Restore(int* slot) noexcept : pointer(slot), saved(*slot) { *pointer = 9; }\n\
             ~Restore() noexcept { *pointer = saved; }\n\
         };\n\
         int helper(bool should_throw) {\n\
             if (should_throw) { throw 7; }\n\
             return 5;\n\
         }\n\
         int caller(int& value, bool construct, bool should_throw) {\n\
             try {\n\
                 if (construct) {\n\
                     Restore guard(&value);\n\
                     helper(should_throw);\n\
                 }\n\
             } catch (int caught) {\n\
                 return value;\n\
             }\n\
             return value;\n\
         }\n",
    );
    project.write_exception_enabled_compilation_database();
    project.write_config_with_exception_behavior("caller", "caller.cpp", true, "scalar_int32");
    refresh_import(&project.config()).expect("export conditional cleanup and catch");
    let prepared = load_import(&project.config()).expect("load the conditional cleanup artifact");
    assert!(matches!(
        prepared.export().function.body.as_slice(),
        [CppStatement::If { then_branch, else_branch, .. }, CppStatement::Return { .. }]
            if matches!(then_branch.as_slice(), [CppStatement::TryCatchInt32 { .. }])
                && else_branch.is_empty()
    ));

    let sidecar_source = r#"verifying "caller.cpp";
        void Restore_constructor(struct Restore* self, int32* slot) {
            owns &self->pointer;
            owns self->saved;
            owns slot[0..1];
            ensures self->pointer == slot;
            ensures self->saved == old(slot[0]);
            ensures slot[0] == 9;
            ensures separate(memory(object(self)), memory(self->pointer[0..1]));
        } by { execute(); simp(); }
        void Restore_destructor(struct Restore* self) {
            requires separate(memory(object(self)), memory(self->pointer[0..1]));
            owns &self->pointer;
            owns self->saved;
            owns self->pointer[0..1];
            ensures self->pointer == old(self->pointer);
            ensures self->saved == old(self->saved);
            ensures self->pointer[0] == old(self->saved);
        } by { execute(); simp(); }
        int32 helper(bool should_throw) throws int32 {
            ensures result == 5;
            exceptional ensures exception == 7;
        }
        int32 caller(int32* value, bool construct, bool should_throw) {
            owns value[0..1];
            ensures result == old(value[0]);
            ensures value[0] == old(value[0]);
        } by {
            branch {
                then {
                    step();
                    step();
                    outcomes {
                        returned { step(); step(); }
                        threw { step(); execute(); simp(); }
                    }
                }
                else { }
            }
            step();
            simp();
        }
"#;
    let sidecar = project.directory.join("demo.click");
    fs::write(&sidecar, sidecar_source).unwrap();
    fs::remove_file(&project.exporter).expect("verification must use the locked artifact");
    let click_project = read_click_project(&sidecar, sidecar_source).unwrap();
    verify_program_prepared_project(&click_project, &prepared)
        .expect("the mixed conditional cleanup join should verify");
    let expanded = expand_program_prepared_project_claim_source_by_label(
        &click_project,
        &prepared,
        "caller.contract",
    )
    .expect("expand the mixed outcome proof");
    let rewritten = click_project.with_entry_source(expanded.clone());
    verify_program_prepared_project(&rewritten, &prepared)
        .expect("the expanded mixed outcome proof must reverify");
    let (session, _) =
        C0VerificationSession::new_program_prepared_project(&click_project, &prepared)
            .expect("retain the mixed outcome verification environment");
    let site = program_prepared_project_tactic_source_position(
        &rewritten,
        &prepared,
        "caller.contract",
        0,
    )
    .expect("locate the rewritten branch proof");
    session
        .verify_at_project(&expanded, site.line, site.column)
        .expect("retained audit must accept the expanded mixed outcome proof");
}

#[test]
fn scalar_int32_profile_rejects_unsupported_handler_shapes() {
    let cases = [
        (
            "catch_all",
            "try { throw 7; } catch (...) { return 7; }",
            "named by-value `int` binding",
        ),
        (
            "bool_binding",
            "try { throw 7; } catch (bool caught) { return 7; }",
            "named by-value `int` binding",
        ),
        (
            "multiple_handlers",
            "try { throw 7; } catch (int caught) { return caught; } catch (...) { return 7; }",
            "exactly one handler",
        ),
        (
            "try_local",
            "try { int local = 7; throw local; } catch (int caught) { return caught; }",
            "automatic C++ locals are currently supported only in the function body",
        ),
        (
            "handler_local",
            "try { throw 7; } catch (int caught) { int local = caught; return local; }",
            "automatic C++ locals are currently supported only in the function body",
        ),
        (
            "nested_handler",
            "try { try { throw 7; } catch (int inner) { return inner; } } catch (int caught) { return caught; }",
            "nested try/catch is outside the scalar int32 exception profile",
        ),
    ];
    for (name, handler, expected) in cases {
        let source = format!("int caller() {{ {handler} return 7; }}\n");
        let project = Project::with_fixture("caller.cpp", "caller", &source);
        project.write_exception_enabled_compilation_database();
        project.write_config_with_exception_behavior("caller", "caller.cpp", true, "scalar_int32");
        let error = refresh_import(&project.config())
            .expect_err(&format!("{name} must not enter a locked artifact"));
        assert!(error.contains(expected), "{name}: {error}");
        assert!(
            !project.artifact().exists(),
            "{name} was unexpectedly locked"
        );
    }
}

#[test]
fn scalar_int32_profile_unwinds_one_guard_on_both_paths() {
    let mdtest = parse_mdtest(
        Path::new("cpp_one_guard_unwind.md"),
        ONE_GUARD_UNWIND_MDTEST,
    )
    .unwrap();
    let cpp = mdtest.cpp_source.unwrap();
    let sidecar_source = mdtest.click_source.unwrap();
    let project = Project::with_fixture(&cpp.filename, &cpp.function, &cpp.source);
    project.write_exception_enabled_compilation_database();
    project.write_config_with_exception_behavior(&cpp.function, &cpp.filename, true, &cpp.profile);
    refresh_import(&project.config()).expect("export a guard local to the try block");
    let prepared = load_import(&project.config()).expect("load the guard artifact offline");
    let [
        CppStatement::TryCatchInt32 { try_body, .. },
        CppStatement::Return { .. },
    ] = prepared.export().function.body.as_slice()
    else {
        panic!("the source try/catch was not retained");
    };
    let [CppStatement::Scope { body, cleanups, .. }] = try_body.as_slice() else {
        panic!("the guard's lifetime was not retained inside the try block");
    };
    assert!(matches!(
        body.as_slice(),
        [CppStatement::Declare { .. }, CppStatement::Call { .. }]
    ));
    assert!(matches!(
        cleanups.as_slice(),
        [CppCleanup::Destructor { .. }]
    ));

    let sidecar = project.directory.join("demo.click");
    fs::write(&sidecar, &sidecar_source).unwrap();
    fs::remove_file(&project.exporter).expect("verification must use the locked artifact");
    let click_project = read_click_project(&sidecar, &sidecar_source).unwrap();
    verify_program_prepared_project(&click_project, &prepared)
        .expect("normal and caught exceptional paths must restore the original value");
}

#[test]
fn scalar_int32_profile_emits_function_scope_cleanup_edges_for_escaping_throws() {
    let project = Project::with_fixture(
        "escaping.cpp",
        "escaping",
        "struct Restore {\n\
             int* pointer;\n\
             explicit Restore(int* slot) noexcept : pointer(slot) { *pointer = 9; }\n\
             ~Restore() noexcept { *pointer = 42; }\n\
         };\n\
         int helper(bool should_throw) {\n\
             if (should_throw) { throw 7; }\n\
             return 5;\n\
         }\n\
         int escaping(int& value, bool throw_now, bool initializer_throws) {\n\
             Restore guard(&value);\n\
             if (throw_now) { throw 7; }\n\
             int ignored = helper(initializer_throws);\n\
             return value;\n\
         }\n",
    );
    project.write_exception_enabled_compilation_database();
    project.write_config_with_exception_behavior("escaping", "escaping.cpp", true, "scalar_int32");
    refresh_import(&project.config()).expect("export the escaping throw and initializer paths");
    let prepared = load_import(&project.config()).expect("load the checked C++ artifact");
    let lowered = lower_import(&prepared).expect("lower function-scope unwind edges");

    fn collect_unwind_edges<'a>(
        statement: &'a CStatement,
        edges: &mut Vec<(&'a CStatement, &'a CStatement)>,
    ) {
        match statement {
            CStatement::TryCatchInt32 {
                try_body,
                handler,
                cleanup_unwind: true,
                ..
            } => {
                edges.push((try_body, handler));
                collect_unwind_edges(try_body, edges);
                collect_unwind_edges(handler, edges);
            }
            CStatement::Seq(first, second) => {
                collect_unwind_edges(first, edges);
                collect_unwind_edges(second, edges);
            }
            CStatement::If {
                then_branch,
                else_branch,
                ..
            } => {
                collect_unwind_edges(then_branch, edges);
                collect_unwind_edges(else_branch, edges);
            }
            CStatement::TryCatchInt32 {
                try_body, handler, ..
            } => {
                collect_unwind_edges(try_body, edges);
                collect_unwind_edges(handler, edges);
            }
            _ => {}
        }
    }

    let mut edges = Vec::new();
    collect_unwind_edges(lowered.kernel_function().body(), &mut edges);
    assert_eq!(
        edges.len(),
        2,
        "both exceptional operations need cleanup edges"
    );
    for (_, handler) in &edges {
        assert!(
            matches!(handler, CStatement::Seq(cleanup, rethrow)
                if contains_call(cleanup, "Restore_destructor")
                    && matches!(rethrow.as_ref(), CStatement::Throw(_))),
            "each escaping edge must run the live destructor before rethrowing"
        );
    }
    assert!(
        edges
            .iter()
            .any(|(try_body, _)| matches!(try_body, CStatement::Throw(_)))
    );
    assert!(edges.iter().any(|(try_body, _)| {
        matches!(try_body, CStatement::Seq(declare, call)
            if matches!(declare.as_ref(), CStatement::Declare { name, .. } if name == "ignored")
                && matches!(call.as_ref(), CStatement::CallAssign { function_name, .. } if function_name == "helper"))
    }));
}

#[test]
fn scalar_int32_profile_rejects_hostile_cleanup_proofs() {
    let mdtest = parse_mdtest(
        Path::new("cpp_guard_unwind_before_second.md"),
        GUARD_BEFORE_SECOND_MDTEST,
    )
    .unwrap();
    let cpp = mdtest.cpp_source.unwrap();
    let sidecar_source = mdtest.click_source.unwrap();
    let project = Project::with_fixture(&cpp.filename, &cpp.function, &cpp.source);
    project.write_exception_enabled_compilation_database();
    project.write_config_with_exception_behavior(&cpp.function, &cpp.filename, true, &cpp.profile);
    refresh_import(&project.config()).expect("export the conditional cleanup frontier");
    let prepared = load_import(&project.config()).expect("load the cleanup artifact");
    let sidecar = project.directory.join("demo.click");
    fs::write(&sidecar, &sidecar_source).unwrap();
    fs::remove_file(&project.exporter).expect("verification must use the locked artifact");

    let click_project = read_click_project(&sidecar, &sidecar_source).unwrap();
    verify_program_prepared_project(&click_project, &prepared)
        .expect("the unmodified conditional cleanup proof must pass");

    let cases = [
        (
            "wrong_cleanup_order",
            sidecar_source.replacen(
                "            step();\n            step();\n            step();\n            step();\n            have second_cell[0] == old(second_cell[0]) by { simp(); }",
                "            step();\n            step();\n            have first_cell[0] == old(first_cell[0]) by { simp(); }\n            step();\n            step();\n            have second_cell[0] == old(second_cell[0]) by { simp(); }",
                1,
            ),
            "the first guard cannot be restored before the second cleanup",
        ),
        (
            "omitted_cleanup",
            sidecar_source.replacen(
                "            step();\n            step();\n            step();\n            step();\n            have second_cell[0] == old(second_cell[0]) by { simp(); }",
                "            step();\n            step();\n            step();\n            have second_cell[0] == old(second_cell[0]) by { simp(); }",
                1,
            ),
            "a proof cannot omit a required destructor",
        ),
        // Each `step()` runs the next lowered statement, so a destructor runs
        // once however many steps a proof writes: once both destructors and
        // the return have run, no step is left. One extra step only moves
        // the `have` past the first guard's destructor, where it still holds
        // and now verifies, since the caller's `second_cell[0]` is kept
        // across that call although its value is not cached
        // (`mdtests/call_keeps_an_uncached_flat_field_beside_folded_state.md`).
        (
            "duplicated_cleanup",
            sidecar_source.replacen(
                "            step();\n            step();\n            step();\n            step();\n            have second_cell[0] == old(second_cell[0]) by { simp(); }",
                "            step();\n            step();\n            step();\n            step();\n            step();\n            step();\n            step();\n            have second_cell[0] == old(second_cell[0]) by { simp(); }",
                1,
            ),
            "a proof cannot execute a destructor twice",
        ),
        (
            "unconstructed_second_guard",
            sidecar_source.replacen(
                "        threw {\n            step();\n            have second_cell[0] == old(second_cell[0]) by { simp(); }",
                "        threw {\n            step();\n            step();\n            have second_cell[0] == 9 by { simp(); }",
                1,
            ),
            "the exceptional path cannot destroy the skipped second guard",
        ),
        (
            "normal_value_on_exceptional_path",
            sidecar_source.replacen(
                "    exceptional ensures exception == 7;",
                "    exceptional ensures exception == 5;",
                1,
            ),
            "the normal return value cannot justify the exceptional outcome",
        ),
    ];

    for (name, hostile_source, expectation) in cases {
        assert_ne!(
            hostile_source, sidecar_source,
            "{name} did not change the hostile proof"
        );
        let hostile_project = read_click_project(&sidecar, &hostile_source).unwrap();
        assert!(
            verify_program_prepared_project(&hostile_project, &prepared).is_err(),
            "{expectation}: {name} unexpectedly verified"
        );
    }
}

#[test]
fn scalar_int32_profile_rejects_broader_guarded_try_shapes() {
    let mdtest = parse_mdtest(
        Path::new("cpp_one_guard_unwind.md"),
        ONE_GUARD_UNWIND_MDTEST,
    )
    .unwrap();
    let cpp = mdtest.cpp_source.unwrap();
    let declaration = "        Restore guard(&value);\n        helper(should_throw);";
    assert!(cpp.source.contains(declaration));
    let cases = [
        (
            "late_guard",
            "        helper(should_throw);\n        Restore guard(&value);",
            "guard construction first",
        ),
        (
            "return_inside_try",
            "        Restore guard(&value);\n        return value;",
            "return from a guarded try region",
        ),
    ];
    for (name, replacement, expected) in cases {
        let source = cpp.source.replacen(declaration, replacement, 1);
        assert_ne!(source, cpp.source);
        let project = Project::with_fixture(&cpp.filename, &cpp.function, &source);
        project.write_exception_enabled_compilation_database();
        project.write_config_with_exception_behavior(
            &cpp.function,
            &cpp.filename,
            true,
            &cpp.profile,
        );
        let error = refresh_import(&project.config())
            .expect_err(&format!("{name} must not enter a locked artifact"));
        assert!(error.contains(expected), "{name}: {error}");
        assert!(
            !project.artifact().exists(),
            "{name} was unexpectedly locked"
        );
    }

    let destructor = "~Restore() noexcept { *pointer = saved; }";
    assert!(cpp.source.contains(destructor));
    let throwing_destructor =
        cpp.source
            .replacen(destructor, "~Restore() noexcept { throw 7; }", 1);
    let calling_destructor = format!(
        "int destructor_helper();\n{}\nint destructor_helper() {{ throw 7; }}\n",
        cpp.source.replacen(
            destructor,
            "~Restore() noexcept { destructor_helper(); *pointer = saved; }",
            1,
        )
    );
    for (name, source, expected) in [
        (
            "throwing_destructor",
            throwing_destructor,
            "has a non-throwing exception specification but can still throw",
        ),
        (
            "calling_destructor",
            calling_destructor,
            "noexcept C++ object operation",
        ),
    ] {
        let project = Project::with_fixture(&cpp.filename, &cpp.function, &source);
        project.write_exception_enabled_compilation_database();
        project.write_config_with_exception_behavior(
            &cpp.function,
            &cpp.filename,
            true,
            &cpp.profile,
        );
        let error = refresh_import(&project.config())
            .expect_err(&format!("{name} must not enter a locked artifact"));
        assert!(error.contains(expected), "{name}: {error}");
        assert!(
            !project.artifact().exists(),
            "{name} was unexpectedly locked"
        );
    }
}

#[test]
fn scalar_int32_profile_rejects_a_non_int32_exception_payload() {
    let disabled = Project::new();
    disabled.write_config_with_exception_behavior(
        "increment",
        "increment.cpp",
        false,
        "scalar_int32",
    );
    let error = refresh_import(&disabled.config())
        .expect_err("the scalar exception profile needs an exception-enabled compiler");
    assert!(error.contains("requires C++ exceptions enabled"), "{error}");

    let noexcept = Project::new();
    noexcept.write_exception_enabled_compilation_database();
    noexcept.write_config_with_exception_behavior(
        "increment",
        "increment.cpp",
        true,
        "scalar_int32",
    );
    let error = refresh_import(&noexcept.config())
        .expect_err("the scalar profile must not mis-model noexcept termination");
    assert!(
        error.contains("does not model noexcept termination"),
        "{error}"
    );

    let project = Project::new();
    fs::write(
        project.source(),
        "int increment(int& value) { throw true; }\n",
    )
    .unwrap();
    project.write_exception_enabled_compilation_database();
    project.write_config_with_exception_behavior(
        "increment",
        "increment.cpp",
        true,
        "scalar_int32",
    );
    let error = refresh_import(&project.config()).expect_err("bool is not an int32 exception");
    assert!(error.contains("exception payload"), "{error}");
    assert!(!project.artifact().exists());
}

#[test]
fn signed_int64_predicate_retains_alias_and_verifies_offline() {
    let project = Project::int64_predicate();
    let sidecar = project.directory.join("demo.click");
    fs::write(&sidecar, INT64_PREDICATE_SIDECAR).unwrap();
    refresh_import(&project.config()).expect("export the signed-64 predicate");
    fs::remove_file(&project.exporter).expect("make the exporter unavailable after refresh");

    let import = load_import(&project.config()).expect("load the predicate artifact offline");
    assert_eq!(import.export().schema, 33);
    assert!(import.export().profile.exceptions);
    assert!(!import.export().function.declared_noexcept);
    assert!(matches!(
        import.export().function.return_type,
        CppType::Boolean {
            bits: 8,
            is_const: false
        }
    ));
    let CppType::LvalueReference { pointee } = &import.export().function.parameters[0].value_type
    else {
        panic!("CAmount parameter did not retain reference type")
    };
    let CppType::Integer {
        bits: 64,
        signed: true,
        is_const: true,
        source_aliases,
    } = pointee.as_ref()
    else {
        panic!("CAmount parameter did not retain its signed-64 alias: {pointee:#?}")
    };
    let [alias] = source_aliases.as_slice() else {
        panic!("CAmount parameter did not retain exactly one direct alias")
    };
    assert_eq!(alias.name, "CAmount");
    assert!(!alias.declaration_id.is_empty());
    assert_eq!(alias.span.file, "money_nonnegative.cpp");
    assert_eq!(alias.span.start_line, 1);
    assert!(matches!(
        import.export().function.body.as_slice(),
        [CppStatement::Return {
            value: CppExpression::Binary {
                operator: CppBinaryOperator::GreaterEqual,
                left,
                right,
                ..
            },
            ..
        }] if matches!(left.as_ref(), CppExpression::Load { .. })
            && matches!(right.as_ref(), CppExpression::IntegralCast { value, .. }
                if matches!(value.as_ref(), CppExpression::IntegerLiteral { value, .. } if value == "0"))
    ));

    let lowered = lower_import(&import).expect("lower the predicate directly to the kernel");
    assert_eq!(lowered.kernel_function().return_type(), CType::Bool);
    assert_eq!(
        lowered.kernel_function().parameters()[0].c_type(),
        CType::Int64Pointer
    );
    assert!(lowered.kernel_function().parameters()[0].pointee_is_constant());

    let click_project = read_click_project(&sidecar, INT64_PREDICATE_SIDECAR).unwrap();
    verify_program_prepared_project(&click_project, &import)
        .expect("verify the signed-64 comparison through the offline artifact");

    let false_source = INT64_PREDICATE_SIDECAR.replace(">= 0i64", "> 0i64");
    let false_project = read_click_project(&sidecar, &false_source).unwrap();
    let error = verify_program_prepared_project(&false_project, &import).unwrap_err();
    assert!(
        error.message().contains("unclosed goal"),
        "{}",
        error.message()
    );
}

#[test]
fn signed_int64_predicate_rejects_inequality_and_disjunction() {
    let less_than = Project::int64_predicate();
    fs::write(
        less_than.source(),
        INT64_PREDICATE_SOURCE.replace("nValue >= 0", "nValue != 0"),
    )
    .unwrap();
    let error = refresh_import(&less_than.config()).unwrap_err();
    assert!(error.contains("unsupported binary operator"), "{error}");

    let disjunction = Project::int64_predicate();
    fs::write(
        disjunction.source(),
        INT64_PREDICATE_SOURCE.replace("nValue >= 0", "nValue >= 0 || nValue <= 2100000000000000L"),
    )
    .unwrap();
    let error = refresh_import(&disjunction.config()).unwrap_err();
    assert!(error.contains("built-in bool && bool only"), "{error}");

    let unsigned = Project::int64_predicate();
    fs::write(
        unsigned.source(),
        INT64_PREDICATE_SOURCE.replace("typedef long CAmount", "typedef unsigned long CAmount"),
    )
    .unwrap();
    let error = refresh_import(&unsigned.config()).unwrap_err();
    assert!(error.contains("const signed-64 reference"), "{error}");

    let mutable = Project::int64_predicate();
    fs::write(
        mutable.source(),
        INT64_PREDICATE_SOURCE.replace("const CAmount&", "CAmount&"),
    )
    .unwrap();
    let error = refresh_import(&mutable.config()).unwrap_err();
    assert!(error.contains("const signed-64 reference"), "{error}");
}

#[test]
fn constexpr_coin_retains_alias_chain_and_verifies_offline() {
    let project = Project::constexpr_coin();
    let sidecar = project.directory.join("demo.click");
    fs::write(&sidecar, CONSTEXPR_COIN_SIDECAR).unwrap();
    refresh_import(&project.config()).expect("export the constexpr coin predicate");
    fs::remove_file(&project.exporter).expect("make the exporter unavailable after refresh");

    let import = load_import(&project.config()).expect("load the constexpr artifact offline");
    assert_eq!(import.export().schema, 33);
    assert_eq!(import.export().dependencies, ["cstdint"]);
    let CppType::LvalueReference { pointee } = &import.export().function.parameters[0].value_type
    else {
        panic!("CAmount parameter did not retain reference type")
    };
    let CppType::Integer {
        bits: 64,
        signed: true,
        is_const: true,
        source_aliases,
    } = pointee.as_ref()
    else {
        panic!("CAmount parameter did not retain its alias chain: {pointee:#?}")
    };
    assert_eq!(
        source_aliases
            .iter()
            .map(|alias| alias.name.as_str())
            .collect::<Vec<_>>(),
        ["CAmount", "int64_t"]
    );
    assert_eq!(source_aliases[0].span.file, "at_least_one_coin.cpp");
    assert_eq!(source_aliases[1].span.file, "cstdint");

    let [constant] = import.export().constants.as_slice() else {
        panic!("COIN was not captured as the sole reachable constant")
    };
    assert_eq!(constant.name, "COIN");
    assert_eq!(constant.evaluated_value, "100000000");
    assert!(matches!(
        &constant.initializer,
        CppExpression::IntegralCast { value, .. }
            if matches!(value.as_ref(), CppExpression::IntegerLiteral { value, .. }
                if value == "100000000")
    ));
    assert!(matches!(
        import.export().function.body.as_slice(),
        [CppStatement::Return {
            value: CppExpression::Binary {
                operator: CppBinaryOperator::GreaterEqual,
                right,
                ..
            },
            ..
        }] if matches!(right.as_ref(), CppExpression::ConstantReference { constant: reference, .. }
            if reference.declaration_id == constant.declaration_id && reference.name == "COIN")
    ));

    let lowered = lower_import(&import).expect("lower the constexpr predicate directly");
    assert_eq!(lowered.kernel_function().return_type(), CType::Bool);
    let click_project = read_click_project(&sidecar, CONSTEXPR_COIN_SIDECAR).unwrap();
    verify_program_prepared_project(&click_project, &import)
        .expect("verify the constexpr comparison through the offline artifact");

    let false_source = CONSTEXPR_COIN_SIDECAR.replace(">= 100000000i64", "> 100000000i64");
    let false_project = read_click_project(&sidecar, &false_source).unwrap();
    let error = verify_program_prepared_project(&false_project, &import).unwrap_err();
    assert!(
        error.message().contains("unclosed goal"),
        "{}",
        error.message()
    );

    fs::write(project.directory.join("cstdint"), "typedef int int64_t;\n").unwrap();
    let error = load_import(&project.config()).unwrap_err();
    assert!(error.contains("dependency inventory differs"), "{error}");
}

#[test]
fn constexpr_coin_rejects_unlocked_mutable_and_nonleaf_constants() {
    let mutable = Project::constexpr_coin();
    fs::write(
        mutable.source(),
        CONSTEXPR_COIN_SOURCE.replace("static constexpr CAmount", "static CAmount"),
    )
    .unwrap();
    let error = refresh_import(&mutable.config()).unwrap_err();
    assert!(error.contains("static constexpr"), "{error}");

    let nonleaf = Project::constexpr_coin();
    fs::write(
        nonleaf.source(),
        CONSTEXPR_COIN_SOURCE.replace("100000000;", "50000000 + 50000000;"),
    )
    .unwrap();
    let error = refresh_import(&nonleaf.config()).unwrap_err();
    assert!(
        error.contains("literal leaf or one dependent multiplication"),
        "{error}"
    );

    let mut unlocked = Project::constexpr_coin();
    unlocked.dependencies.clear();
    unlocked.write_config_with_profile("at_least_one_coin", "at_least_one_coin.cpp", true);
    let error = refresh_import(&unlocked.config()).unwrap_err();
    assert!(
        error.contains("differ from configured dependencies"),
        "{error}"
    );
}

#[test]
fn constexpr_max_money_retains_checked_dependency_and_verifies_offline() {
    let project = Project::constexpr_max_money();
    let sidecar = project.directory.join("demo.click");
    fs::write(&sidecar, CONSTEXPR_MAX_MONEY_SIDECAR).unwrap();
    refresh_import(&project.config()).expect("export the dependent constexpr predicate");
    fs::remove_file(&project.exporter).expect("make the exporter unavailable after refresh");

    let import = load_import(&project.config()).expect("load the dependent artifact offline");
    assert_eq!(import.export().schema, 33);
    let [coin, max_money] = import.export().constants.as_slice() else {
        panic!("COIN and MAX_MONEY were not captured as one ordered dependency")
    };
    assert_eq!(coin.name, "COIN");
    assert_eq!(coin.evaluated_value, "100000000");
    assert_eq!(max_money.name, "MAX_MONEY");
    assert_eq!(max_money.evaluated_value, "2100000000000000");
    assert!(matches!(
        &max_money.initializer,
        CppExpression::Binary {
            operator: CppBinaryOperator::Multiply,
            left,
            right,
            ..
        } if matches!(left.as_ref(), CppExpression::IntegralCast { value, .. }
            if matches!(value.as_ref(), CppExpression::IntegerLiteral { value, .. }
                if value == "21000000"))
            && matches!(right.as_ref(), CppExpression::ConstantReference { constant, .. }
                if constant.declaration_id == coin.declaration_id && constant.name == "COIN")
    ));
    assert!(matches!(
        import.export().function.body.as_slice(),
        [CppStatement::Return {
            value: CppExpression::Binary {
                operator: CppBinaryOperator::GreaterEqual,
                right,
                ..
            },
            ..
        }] if matches!(right.as_ref(), CppExpression::ConstantReference { constant, .. }
            if constant.declaration_id == max_money.declaration_id
                && constant.name == "MAX_MONEY")
    ));

    let lowered = lower_import(&import).expect("lower the dependent constexpr predicate");
    assert_eq!(lowered.kernel_function().return_type(), CType::Bool);
    let click_project = read_click_project(&sidecar, CONSTEXPR_MAX_MONEY_SIDECAR).unwrap();
    verify_program_prepared_project(&click_project, &import)
        .expect("verify the dependent constexpr comparison offline");

    let false_source =
        CONSTEXPR_MAX_MONEY_SIDECAR.replace(">= 2100000000000000i64", "> 2100000000000000i64");
    let false_project = read_click_project(&sidecar, &false_source).unwrap();
    let error = verify_program_prepared_project(&false_project, &import).unwrap_err();
    assert!(
        error.message().contains("unclosed goal"),
        "{}",
        error.message()
    );
}

#[test]
fn signed_int64_less_equal_verifies_max_money_upper_bound_offline() {
    let project = Project::constexpr_max_money_less_equal();
    let sidecar = project.directory.join("demo.click");
    fs::write(&sidecar, CONSTEXPR_MAX_MONEY_LE_SIDECAR).unwrap();
    refresh_import(&project.config()).expect("export the signed-64 upper-bound predicate");
    fs::remove_file(&project.exporter).expect("make the exporter unavailable after refresh");

    let import = load_import(&project.config()).expect("load the upper-bound artifact offline");
    assert_eq!(import.export().schema, 33);
    let [coin, max_money] = import.export().constants.as_slice() else {
        panic!("the upper-bound artifact lost the MAX_MONEY dependency graph")
    };
    assert_eq!(coin.name, "COIN");
    assert_eq!(max_money.name, "MAX_MONEY");
    assert!(matches!(
        import.export().function.body.as_slice(),
        [CppStatement::Return {
            value: CppExpression::Binary {
                operator: CppBinaryOperator::LessEqual,
                right,
                ..
            },
            ..
        }] if matches!(right.as_ref(), CppExpression::ConstantReference { constant, .. }
            if constant.declaration_id == max_money.declaration_id
                && constant.name == "MAX_MONEY")
    ));

    let lowered = lower_import(&import).expect("lower signed-64 less-equal directly");
    assert_eq!(lowered.kernel_function().return_type(), CType::Bool);
    let click_project = read_click_project(&sidecar, CONSTEXPR_MAX_MONEY_LE_SIDECAR).unwrap();
    verify_program_prepared_project(&click_project, &import)
        .expect("verify the inclusive MAX_MONEY upper bound offline");

    let false_source =
        CONSTEXPR_MAX_MONEY_LE_SIDECAR.replace("<= 2100000000000000i64", "< 2100000000000000i64");
    let false_project = read_click_project(&sidecar, &false_source).unwrap();
    let error = verify_program_prepared_project(&false_project, &import).unwrap_err();
    assert!(
        error.message().contains("unclosed goal"),
        "{}",
        error.message()
    );
}

#[test]
fn built_in_cpp_logical_and_verifies_inclusive_money_range_offline() {
    let project = Project::constexpr_max_money_range();
    let sidecar = project.directory.join("demo.click");
    fs::write(&sidecar, CONSTEXPR_MAX_MONEY_RANGE_SIDECAR).unwrap();
    refresh_import(&project.config()).expect("export the built-in short-circuit predicate");
    fs::remove_file(&project.exporter).expect("make the exporter unavailable after refresh");

    let import = load_import(&project.config()).expect("load the range artifact offline");
    assert_eq!(import.export().schema, 33);
    let [coin, max_money] = import.export().constants.as_slice() else {
        panic!("the range artifact lost the ordered MAX_MONEY dependency graph")
    };
    assert_eq!(coin.name, "COIN");
    assert_eq!(max_money.name, "MAX_MONEY");
    let [
        CppStatement::Return {
            value:
                CppExpression::Binary {
                    operator: CppBinaryOperator::LogicalAnd,
                    left,
                    right,
                    value_type:
                        CppType::Boolean {
                            bits: 8,
                            is_const: false,
                        },
                    ..
                },
            ..
        },
    ] = import.export().function.body.as_slice()
    else {
        panic!("the range return did not retain Clang's built-in logical-and node")
    };
    assert!(matches!(left.as_ref(), CppExpression::Binary {
        operator: CppBinaryOperator::GreaterEqual,
        right,
        ..
    } if matches!(right.as_ref(), CppExpression::IntegralCast { value, .. }
        if matches!(value.as_ref(), CppExpression::IntegerLiteral { value, .. }
            if value == "0"))));
    assert!(matches!(right.as_ref(), CppExpression::Binary {
        operator: CppBinaryOperator::LessEqual,
        right,
        ..
    } if matches!(right.as_ref(), CppExpression::ConstantReference { constant, .. }
        if constant.declaration_id == max_money.declaration_id
            && constant.name == "MAX_MONEY")));

    let lowered = lower_import(&import).expect("lower built-in C++ && directly");
    assert_eq!(lowered.kernel_function().return_type(), CType::Bool);
    assert!(matches!(lowered.kernel_function().body(),
        CStatement::Return(CExpression::Cast {
            expression,
            target_type: CType::Bool,
            ..
        }) if matches!(expression.as_ref(), CExpression::And(_, _))));
    let click_project = read_click_project(&sidecar, CONSTEXPR_MAX_MONEY_RANGE_SIDECAR).unwrap();
    verify_program_prepared_project(&click_project, &import)
        .expect("verify the inclusive range contract offline");

    let false_source = CONSTEXPR_MAX_MONEY_RANGE_SIDECAR
        .replace("<= 2100000000000000i64", "< 2100000000000000i64");
    let false_project = read_click_project(&sidecar, &false_source).unwrap();
    let error = verify_program_prepared_project(&false_project, &import).unwrap_err();
    assert!(
        error.message().contains("unclosed goal"),
        "{}",
        error.message()
    );
}

#[test]
fn built_in_cpp_logical_and_accepts_checked_integer_to_bool_conversion() {
    let project = Project::constexpr_max_money_range();
    fs::write(
        project.source(),
        CONSTEXPR_MAX_MONEY_SOURCE.replace(
            "value >= 0 && value <= MAX_MONEY",
            "value && value <= MAX_MONEY",
        ),
    )
    .unwrap();
    refresh_import(&project.config()).unwrap();
    lower_import(&load_import(&project.config()).unwrap()).unwrap();
}

#[test]
fn constexpr_max_money_accepts_deeper_constant_graphs_and_rejects_new_initializer_semantics() {
    let addition = Project::constexpr_max_money();
    fs::write(
        addition.source(),
        CONSTEXPR_MAX_MONEY_SOURCE.replace("21000000 * COIN", "21000000 + COIN"),
    )
    .unwrap();
    let error = refresh_import(&addition.config()).unwrap_err();
    assert!(
        error.contains("literal leaf or one dependent multiplication"),
        "{error}"
    );

    let third = Project::constexpr_max_money();
    let source = CONSTEXPR_MAX_MONEY_SOURCE
        .replace(
            "static constexpr CAmount MAX_MONEY = 21000000 * COIN;",
            "static constexpr CAmount MAX_MONEY = 21000000 * COIN;\nstatic constexpr CAmount TOO_MUCH = 2 * MAX_MONEY;",
        )
        .replace("value >= MAX_MONEY", "value >= TOO_MUCH");
    fs::write(third.source(), source).unwrap();
    refresh_import(&third.config()).unwrap();
    let import = load_import(&third.config()).unwrap();
    assert_eq!(import.export().constants.len(), 3);
    lower_import(&import).unwrap();

    let runtime_multiply = Project::constexpr_max_money();
    fs::write(
        runtime_multiply.source(),
        CONSTEXPR_MAX_MONEY_SOURCE.replace("value >= MAX_MONEY", "value >= MAX_MONEY * 1"),
    )
    .unwrap();
    refresh_import(&runtime_multiply.config()).unwrap();
    lower_import(&load_import(&runtime_multiply.config()).unwrap()).unwrap();
}

#[test]
fn exception_enabled_profile_rejects_exception_and_object_semantics() {
    let throwing = Project::new();
    fs::write(
        throwing.source(),
        "int increment(int& value) {\n    throw value;\n}\n",
    )
    .unwrap();
    throwing.write_exception_enabled_compilation_database();
    throwing.write_config_with_profile("increment", "increment.cpp", true);
    let error = refresh_import(&throwing.config()).unwrap_err();
    assert!(error.contains("increment.cpp:2"), "{error}");
    assert!(error.contains("throw expressions are outside"), "{error}");
    assert!(!throwing.artifact().exists());

    let catching = Project::new();
    fs::write(
        catching.source(),
        "int increment(int& value) {\n    try { value = value + 1; } catch (...) { return 0; }\n    return value;\n}\n",
    )
    .unwrap();
    catching.write_exception_enabled_compilation_database();
    catching.write_config_with_profile("increment", "increment.cpp", true);
    let error = refresh_import(&catching.config()).unwrap_err();
    assert!(error.contains("increment.cpp:2"), "{error}");
    assert!(error.contains("try/catch is outside"), "{error}");
    assert!(!catching.artifact().exists());

    let unresolved = Project::direct_call();
    fs::write(
        unresolved.source(),
        "int set_seven(int& value);\n\nint call_set_seven(int& value) {\n    set_seven(value);\n    return value;\n}\n",
    )
    .unwrap();
    unresolved.write_exception_enabled_compilation_database();
    unresolved.write_config_with_profile("call_set_seven", "call_set_seven.cpp", true);
    let error = refresh_import(&unresolved.config()).unwrap_err();
    assert!(
        error.contains("no reachable function definition"),
        "{error}"
    );
    assert!(!unresolved.artifact().exists());

    let object = Project::new();
    fs::write(
        object.source(),
        "struct Box { int stored; };\nint increment(int& value) {\n    Box box{value};\n    return box.stored;\n}\n",
    )
    .unwrap();
    object.write_exception_enabled_compilation_database();
    object.write_config_with_profile("increment", "increment.cpp", true);
    let error = refresh_import(&object.config()).unwrap_err();
    assert!(error.contains("increment.cpp:3"), "{error}");
    assert!(error.contains("borrowed records only"), "{error}");
    assert!(!object.artifact().exists());
}

#[test]
fn locked_cpp_function_verifies_through_the_shared_sidecar_path_offline() {
    let project = Project::new();
    let sidecar = project.directory.join("demo.click");
    fs::write(&sidecar, SIDECAR).unwrap();
    refresh_import(&project.config()).expect("refresh the C++ import explicitly");
    fs::remove_file(&project.exporter).expect("make the exporter unavailable after refresh");

    let click_source = fs::read_to_string(&sidecar).unwrap();
    let inputs = read_c_inputs(&sidecar, &click_source).expect("load the locked sidecar input");
    let CInput::PreparedProgram(import) = inputs else {
        panic!("language=c++ must select the C++ prepared-input path")
    };
    let click_project = read_click_project(&sidecar, &click_source).unwrap();
    let verified = verify_program_prepared_project(&click_project, &import)
        .expect("verify the directly lowered C++ function");
    assert_eq!(
        verified
            .iter()
            .map(|theorem| match theorem.claim {
                VerifiedClaim::Ensure { index, .. } => index,
                VerifiedClaim::ExceptionalEnsure { index, .. } => index,
            })
            .collect::<Vec<_>>(),
        vec![0, 1, 2],
        "the grouped proof checks returned ownership plus both value postconditions"
    );
    assert!(
        verified
            .iter()
            .all(|theorem| { theorem.import_identity.as_deref() == Some(import.identity()) })
    );
}

#[test]
fn locked_cpp_branch_and_early_return_verify_through_the_shared_sidecar_path() {
    let project = Project::branch_return();
    let sidecar = project.directory.join("demo.click");
    fs::write(&sidecar, BRANCH_SIDECAR).unwrap();
    refresh_import(&project.config()).expect("refresh the branching C++ import explicitly");
    fs::remove_file(&project.exporter).expect("make the exporter unavailable after refresh");

    let import = load_import(&project.config()).expect("load branching artifact offline");
    let source = &import.export().function;
    assert_eq!(source.parameters.len(), 2);
    assert!(matches!(
        source.parameters[0].value_type,
        CppType::Boolean {
            bits: 8,
            is_const: false,
        }
    ));
    assert!(matches!(
        source.body.as_slice(),
        [
            CppStatement::Assign { .. },
            CppStatement::If {
                then_branch,
                else_branch,
                ..
            },
            CppStatement::Assign { .. },
            CppStatement::Return { .. },
        ] if matches!(then_branch.as_slice(), [CppStatement::Return { .. }])
            && else_branch.is_empty()
    ));

    let lowered = lower_import(&import).expect("lower the typed branch directly");
    assert_eq!(
        lowered.kernel_function().parameters()[0].c_type(),
        CType::Bool
    );
    assert!(contains_if(lowered.kernel_function().body()));

    let click_source = fs::read_to_string(&sidecar).unwrap();
    let inputs = read_c_inputs(&sidecar, &click_source).unwrap();
    let CInput::PreparedProgram(import) = inputs else {
        panic!("language=c++ must select the C++ prepared-input path")
    };
    let click_project = read_click_project(&sidecar, &click_source).unwrap();
    let verified = verify_program_prepared_project(&click_project, &import)
        .expect("verify both C++ return paths against one contract");
    assert_eq!(
        verified
            .iter()
            .map(|theorem| match theorem.claim {
                VerifiedClaim::Ensure { index, .. } => index,
                VerifiedClaim::ExceptionalEnsure { index, .. } => index,
            })
            .collect::<Vec<_>>(),
        vec![0, 1, 2, 0, 1, 2],
        "both return paths certify returned ownership and both postconditions"
    );

    let sites =
        program_prepared_project_smart_tactic_source_sites(&click_project, &import).unwrap();
    assert_eq!(
        sites
            .iter()
            .map(|site| site.tactic_name.as_str())
            .collect::<Vec<_>>(),
        vec!["execute", "simp"]
    );
    let execute = program_prepared_project_tactic_source_position(
        &click_project,
        &import,
        "choose.contract",
        0,
    )
    .unwrap();
    let expanded = expand_program_prepared_project_tactic_source_at(
        &click_project,
        &import,
        execute.line,
        execute.column,
    )
    .expect("expand the branch execution into a checkable source proof");
    let rewritten = click_project.with_entry_source(expanded.clone());
    verify_program_prepared_project(&rewritten, &import)
        .expect("the expanded branch proof must reverify");
    let (session, _) = C0VerificationSession::new_program_prepared_project(&click_project, &import)
        .expect("retain the original branch verification environment");
    let next =
        program_prepared_project_tactic_source_position(&rewritten, &import, "choose.contract", 0)
            .unwrap();
    session
        .verify_at_project(&expanded, next.line, next.column)
        .expect("retained audit session must accept the expanded branch proof");
}

#[test]
fn const_reference_preserves_qualification_and_may_alias_a_mutable_reference() {
    let project = Project::const_reference_alias();
    let sidecar = project.directory.join("demo.click");
    fs::write(&sidecar, CONST_REFERENCE_SIDECAR).unwrap();
    refresh_import(&project.config()).expect("refresh the const-reference C++ import explicitly");
    fs::remove_file(&project.exporter).expect("make the exporter unavailable after refresh");

    let import = load_import(&project.config()).expect("load const-reference artifact offline");
    let source = &import.export().function;
    assert_eq!(source.parameters.len(), 2);
    assert_eq!(
        source.parameters[0].value_type,
        CppType::LvalueReference {
            pointee: Box::new(CppType::Integer {
                bits: 32,
                signed: true,
                is_const: false,
                source_aliases: Vec::new(),
            }),
        }
    );
    assert_eq!(
        source.parameters[1].value_type,
        CppType::LvalueReference {
            pointee: Box::new(CppType::Integer {
                bits: 32,
                signed: true,
                is_const: true,
                source_aliases: Vec::new(),
            }),
        }
    );

    let lowered = lower_import(&import).expect("lower both C++ reference qualifiers directly");
    let parameters = lowered.kernel_function().parameters();
    assert_eq!(parameters[0].c_type(), CType::Int32Pointer);
    assert!(!parameters[0].pointee_is_constant());
    assert_eq!(parameters[1].c_type(), CType::Int32Pointer);
    assert!(parameters[1].pointee_is_constant());

    let click_source = fs::read_to_string(&sidecar).unwrap();
    let inputs = read_c_inputs(&sidecar, &click_source).unwrap();
    let CInput::PreparedProgram(import) = inputs else {
        panic!("language=c++ must select the C++ prepared-input path")
    };
    let click_project = read_click_project(&sidecar, &click_source).unwrap();
    let verified = verify_program_prepared_project(&click_project, &import)
        .expect("one owned cell should authorize an aliased mutable write and const read");
    assert_eq!(
        verified
            .iter()
            .map(|theorem| match theorem.claim {
                VerifiedClaim::Ensure { index, .. } => index,
                VerifiedClaim::ExceptionalEnsure { index, .. } => index,
            })
            .collect::<Vec<_>>(),
        vec![0, 1, 2],
        "the proof returns ownership and checks both postconditions without an inferred view"
    );

    let sites =
        program_prepared_project_smart_tactic_source_sites(&click_project, &import).unwrap();
    assert_eq!(
        sites
            .iter()
            .map(|site| site.tactic_name.as_str())
            .collect::<Vec<_>>(),
        vec!["execute", "simp"]
    );
    let execute = program_prepared_project_tactic_source_position(
        &click_project,
        &import,
        "write_then_read.contract",
        0,
    )
    .unwrap();
    let expanded = expand_program_prepared_project_tactic_source_at(
        &click_project,
        &import,
        execute.line,
        execute.column,
    )
    .expect("expand the aliased reference execution into a checkable proof");
    let rewritten = click_project.with_entry_source(expanded.clone());
    verify_program_prepared_project(&rewritten, &import)
        .expect("the expanded const-reference proof must reverify");
    let (session, _) = C0VerificationSession::new_program_prepared_project(&click_project, &import)
        .expect("retain the const-reference verification environment");
    let next = program_prepared_project_tactic_source_position(
        &rewritten,
        &import,
        "write_then_read.contract",
        0,
    )
    .unwrap();
    session
        .verify_at_project(&expanded, next.line, next.column)
        .expect("retained audit session must accept the expanded const-reference proof");

    let mutable_signature =
        CONST_REFERENCE_SIDECAR.replace("const int32* readable", "int32* readable");
    fs::write(&sidecar, &mutable_signature).unwrap();
    let mismatched_project = read_click_project(&sidecar, &mutable_signature).unwrap();
    let error = verify_program_prepared_project(&mismatched_project, &import).unwrap_err();
    assert!(
        error
            .message()
            .contains("signature mismatch for `write_then_read` parameter 2"),
        "{}",
        error.message()
    );
}

fn contains_if(statement: &CStatement) -> bool {
    match statement {
        CStatement::If { .. } => true,
        CStatement::Seq(first, second) => contains_if(first) || contains_if(second),
        _ => false,
    }
}

fn contains_call(statement: &CStatement, expected: &str) -> bool {
    match statement {
        CStatement::Call { function_name, .. } => function_name == expected,
        CStatement::Seq(first, second) => {
            contains_call(first, expected) || contains_call(second, expected)
        }
        CStatement::If {
            then_branch,
            else_branch,
            ..
        } => contains_call(then_branch, expected) || contains_call(else_branch, expected),
        _ => false,
    }
}

fn call_order(statement: &CStatement) -> Vec<&str> {
    fn visit<'a>(statement: &'a CStatement, calls: &mut Vec<&'a str>) {
        match statement {
            CStatement::Call { function_name, .. } => calls.push(function_name),
            CStatement::Seq(first, second) => {
                visit(first, calls);
                visit(second, calls);
            }
            CStatement::If {
                then_branch,
                else_branch,
                ..
            } => {
                visit(then_branch, calls);
                visit(else_branch, calls);
            }
            _ => {}
        }
    }
    let mut calls = Vec::new();
    visit(statement, &mut calls);
    calls
}

fn destructor_object_order<'a>(statement: &'a CStatement, destructor: &str) -> Vec<&'a str> {
    fn visit<'a>(statement: &'a CStatement, destructor: &str, objects: &mut Vec<&'a str>) {
        match statement {
            CStatement::Call {
                function_name,
                arguments,
            } if function_name == destructor => {
                if let [CExpression::Cast { expression, .. }] = arguments.as_slice()
                    && let CExpression::Variable(name) = expression.as_ref()
                {
                    objects.push(name);
                }
            }
            CStatement::Seq(first, second) => {
                visit(first, destructor, objects);
                visit(second, destructor, objects);
            }
            CStatement::If {
                then_branch,
                else_branch,
                ..
            } => {
                visit(then_branch, destructor, objects);
                visit(else_branch, destructor, objects);
            }
            _ => {}
        }
    }
    let mut objects = Vec::new();
    visit(statement, destructor, &mut objects);
    objects
}

fn contains_aggregate_construction_begin(statement: &CStatement, expected: &str) -> bool {
    match statement {
        CStatement::DeclareAggregate {
            name,
            construction: true,
            ..
        } => name == expected,
        CStatement::Seq(first, second) => {
            contains_aggregate_construction_begin(first, expected)
                || contains_aggregate_construction_begin(second, expected)
        }
        CStatement::If {
            then_branch,
            else_branch,
            ..
        } => {
            contains_aggregate_construction_begin(then_branch, expected)
                || contains_aggregate_construction_begin(else_branch, expected)
        }
        _ => false,
    }
}

fn contains_scalar_local_pipeline(
    statement: &CStatement,
    call_local: &str,
    value_local: &str,
    callee: &str,
) -> [bool; 4] {
    let mut found = [false; 4];
    fn visit(
        statement: &CStatement,
        call_local: &str,
        value_local: &str,
        callee: &str,
        found: &mut [bool; 4],
    ) {
        match statement {
            CStatement::Declare {
                name,
                c_type: CType::Int32,
                ..
            } if name == call_local => found[0] = true,
            CStatement::CallAssign {
                target,
                function_name,
                ..
            } if target == call_local && function_name == callee => found[1] = true,
            CStatement::Declare {
                name,
                c_type: CType::Int32,
                ..
            } if name == value_local => found[2] = true,
            CStatement::Assign { name, .. } if name == value_local => found[3] = true,
            CStatement::Seq(first, second) => {
                visit(first, call_local, value_local, callee, found);
                visit(second, call_local, value_local, callee, found);
            }
            CStatement::If {
                then_branch,
                else_branch,
                ..
            } => {
                visit(then_branch, call_local, value_local, callee, found);
                visit(else_branch, call_local, value_local, callee, found);
            }
            _ => {}
        }
    }
    visit(statement, call_local, value_local, callee, &mut found);
    found
}

fn contains_local_aggregate_pipeline(statement: &CStatement, local: &str) -> [bool; 3] {
    let mut found = [false; 3];
    fn visit(statement: &CStatement, local: &str, found: &mut [bool; 3]) {
        match statement {
            CStatement::DeclareAggregate { name, layout, .. } if name == local => {
                found[0] = layout.size_bytes() == 16
                    && layout.alignment_bytes() == 8
                    && layout.fields().len() == 2;
            }
            CStatement::TypedStore {
                pointer,
                value_type,
                ..
            } => {
                if matches!(pointer, CExpression::Variable(name) if name == local)
                    && *value_type == CType::Int32Pointer
                {
                    found[1] = true;
                }
                if let CExpression::PointerOffsetBytes { pointer, bytes } = pointer
                    && matches!(pointer.as_ref(), CExpression::Variable(name) if name == local)
                {
                    if *bytes == 0 && *value_type == CType::Int32Pointer {
                        found[1] = true;
                    }
                    if *bytes == 8 && *value_type == CType::Int32 {
                        found[2] = true;
                    }
                }
            }
            CStatement::Seq(first, second) => {
                visit(first, local, found);
                visit(second, local, found);
            }
            CStatement::If {
                then_branch,
                else_branch,
                ..
            } => {
                visit(then_branch, local, found);
                visit(else_branch, local, found);
            }
            _ => {}
        }
    }
    visit(statement, local, &mut found);
    found
}

#[test]
fn direct_cpp_call_exports_reachable_definition_and_verifies_modularly_offline() {
    let project = Project::direct_call();
    let sidecar = project.directory.join("demo.click");
    fs::write(&sidecar, DIRECT_CALL_SIDECAR).unwrap();
    refresh_import(&project.config()).expect("export the resolved C++ call graph");
    fs::remove_file(&project.exporter).expect("make the frontend unavailable after refresh");

    let import = load_import(&project.config()).expect("load the call graph artifact offline");
    assert_eq!(import.export().schema, 33);
    assert_eq!(import.export().function.name, "call_set_seven");
    assert_eq!(import.export().reachable_functions.len(), 1);
    let reachable = &import.export().reachable_functions[0];
    assert_eq!(reachable.name, "set_seven");
    let CppStatement::Call {
        callee, arguments, ..
    } = &import.export().function.body[0]
    else {
        panic!("first caller operation was not a resolved call")
    };
    assert_eq!(callee.declaration_id, reachable.declaration_id);
    assert!(matches!(
        arguments.as_slice(),
        [CppCallArgument::Reference { place }]
            if place.declaration_id == import.export().function.parameters[0].declaration_id
    ));

    let lowered = lower_import(&import).expect("lower both C++ functions directly");
    assert!(contains_call(lowered.kernel_function().body(), "set_seven"));
    assert_eq!(lowered.reachable_kernel_functions().len(), 1);
    assert_eq!(lowered.reachable_kernel_functions()[0].name(), "set_seven");

    let click_source = fs::read_to_string(&sidecar).unwrap();
    let click_project = read_click_project(&sidecar, &click_source).unwrap();
    let verified = verify_program_prepared_project(&click_project, &import)
        .expect("verify the helper and caller through shared modular call rules");
    assert_eq!(verified.len(), 6);

    let sites =
        program_prepared_project_smart_tactic_source_sites(&click_project, &import).unwrap();
    assert_eq!(
        sites
            .iter()
            .map(|site| site.tactic_name.as_str())
            .collect::<Vec<_>>(),
        vec!["execute", "simp", "execute", "simp"]
    );
    let execute = program_prepared_project_tactic_source_position(
        &click_project,
        &import,
        "call_set_seven.contract",
        0,
    )
    .unwrap();
    let expanded = expand_program_prepared_project_tactic_source_at(
        &click_project,
        &import,
        execute.line,
        execute.column,
    )
    .expect("expand the caller's modular execution proof");
    let rewritten = click_project.with_entry_source(expanded.clone());
    verify_program_prepared_project(&rewritten, &import)
        .expect("the expanded modular C++ proof must reverify");
    let (session, _) = C0VerificationSession::new_program_prepared_project(&click_project, &import)
        .expect("retain the modular C++ verification environment");
    let next = program_prepared_project_tactic_source_position(
        &rewritten,
        &import,
        "call_set_seven.contract",
        0,
    )
    .unwrap();
    session
        .verify_at_project(&expanded, next.line, next.column)
        .expect("retained audit session must accept the expanded caller proof");
}

#[test]
fn scalar_local_captures_a_direct_call_result_and_verifies_offline() {
    let project = Project::scalar_local();
    let sidecar = project.directory.join("demo.click");
    fs::write(&sidecar, SCALAR_LOCAL_SIDECAR).unwrap();
    refresh_import(&project.config()).expect("export the typed C++ local and call result");
    fs::remove_file(&project.exporter).expect("make the frontend unavailable after refresh");

    let import = load_import(&project.config()).expect("load the scalar-local artifact offline");
    assert_eq!(import.export().schema, 33);
    assert_eq!(import.export().function.name, "relay_value");
    assert_eq!(import.export().reachable_functions.len(), 1);
    let reachable = &import.export().reachable_functions[0];
    assert_eq!(reachable.name, "read_value");
    let [
        CppStatement::Declare {
            local: captured,
            initializer: CppInitializer::Call {
                callee, arguments, ..
            },
            ..
        },
        CppStatement::Declare {
            local: relayed,
            initializer: CppInitializer::Value { value: copied },
            ..
        },
        CppStatement::Assign { target, value, .. },
        CppStatement::Return {
            value: returned, ..
        },
    ] = import.export().function.body.as_slice()
    else {
        panic!("caller did not retain declaration, local assignment, and return")
    };
    assert_eq!(captured.name, "captured");
    assert!(!captured.declaration_id.is_empty());
    assert_eq!(relayed.name, "relayed");
    assert_ne!(captured.declaration_id, relayed.declaration_id);
    assert_eq!(callee.declaration_id, reachable.declaration_id);
    assert!(matches!(
        arguments.as_slice(),
        [CppCallArgument::Reference { .. }]
    ));
    assert!(matches!(
        copied,
        CppExpression::Load { place, .. }
            if place.declaration_id == captured.declaration_id
    ));
    assert_eq!(target.declaration_id, relayed.declaration_id);
    assert!(matches!(
        value,
        CppExpression::Binary { left, .. }
            if matches!(left.as_ref(), CppExpression::Load { place, .. }
                if place.declaration_id == relayed.declaration_id)
    ));
    assert!(matches!(
        returned,
        CppExpression::Load { place, .. } if place.declaration_id == relayed.declaration_id
    ));

    let lowered = lower_import(&import).expect("lower the scalar local through kernel statements");
    assert_eq!(
        contains_scalar_local_pipeline(
            lowered.kernel_function().body(),
            "captured",
            "relayed",
            "read_value"
        ),
        [true, true, true, true]
    );

    let click_source = fs::read_to_string(&sidecar).unwrap();
    let click_project = read_click_project(&sidecar, &click_source).unwrap();
    let verified = verify_program_prepared_project(&click_project, &import)
        .expect("verify local initialization through the shared call-result rule");
    assert_eq!(verified.len(), 5);

    let execute = program_prepared_project_tactic_source_position(
        &click_project,
        &import,
        "relay_value.contract",
        0,
    )
    .unwrap();
    let expanded = expand_program_prepared_project_tactic_source_at(
        &click_project,
        &import,
        execute.line,
        execute.column,
    )
    .expect("expand the scalar-local caller proof");
    let rewritten = click_project.with_entry_source(expanded.clone());
    verify_program_prepared_project(&rewritten, &import)
        .expect("the expanded scalar-local proof must reverify");
    let (session, _) = C0VerificationSession::new_program_prepared_project(&click_project, &import)
        .expect("retain the scalar-local verification environment");
    let next = program_prepared_project_tactic_source_position(
        &rewritten,
        &import,
        "relay_value.contract",
        0,
    )
    .unwrap();
    session
        .verify_at_project(&expanded, next.line, next.column)
        .expect("retained audit session must accept the expanded local proof");

    let false_contract = SCALAR_LOCAL_SIDECAR.replace(
        "ensures result == value[0] + 1;",
        "ensures result == value[0] + 2;",
    );
    fs::write(&sidecar, &false_contract).unwrap();
    let false_project = read_click_project(&sidecar, &false_contract).unwrap();
    verify_program_prepared_project(&false_project, &import)
        .expect_err("a false claim about the captured call result must be rejected");
}

#[test]
fn mutable_pointer_dereference_and_reference_address_verify_offline() {
    let project = Project::pointer();
    let sidecar = project.directory.join("demo.click");
    fs::write(&sidecar, POINTER_SIDECAR).unwrap();
    refresh_import(&project.config()).expect("export pointer operations and the resolved call");
    fs::remove_file(&project.exporter).expect("make the frontend unavailable after refresh");

    let import = load_import(&project.config()).expect("load the pointer artifact offline");
    assert_eq!(import.export().schema, 33);
    let caller = &import.export().function;
    assert_eq!(caller.name, "bump_reference");
    assert!(matches!(
        caller.parameters[0].value_type,
        CppType::LvalueReference { .. }
    ));
    let [helper] = import.export().reachable_functions.as_slice() else {
        panic!("the pointer helper was not captured")
    };
    assert_eq!(helper.name, "bump_pointer");
    assert!(matches!(
        helper.parameters[0].value_type,
        CppType::Pointer { ref pointee }
            if matches!(pointee.as_ref(), CppType::Integer {
                bits: 32,
                signed: true,
                is_const: false,
                ..
            })
    ));

    let [
        CppStatement::Declare {
            initializer: CppInitializer::Call {
                callee, arguments, ..
            },
            ..
        },
        CppStatement::Return { .. },
    ] = caller.body.as_slice()
    else {
        panic!("the reference caller did not retain its call-result local")
    };
    assert_eq!(callee.declaration_id, helper.declaration_id);
    assert!(matches!(
        arguments.as_slice(),
        [CppCallArgument::Value {
            value: CppExpression::AddressOf { place, value_type, .. }
        }] if place.declaration_id == caller.parameters[0].declaration_id
            && matches!(value_type, CppType::Pointer { .. })
    ));

    let [
        CppStatement::Store {
            pointer: stored_through,
            value: CppExpression::Binary {
                left: loaded_value, ..
            },
            ..
        },
        CppStatement::Return {
            value: returned_value,
            ..
        },
    ] = helper.body.as_slice()
    else {
        panic!("the pointer helper did not retain its checked load/store operations")
    };
    assert!(matches!(
        stored_through,
        CppExpression::Load { place, value_type, .. }
            if place.declaration_id == helper.parameters[0].declaration_id
                && matches!(value_type, CppType::Pointer { .. })
    ));
    assert!(matches!(
        loaded_value.as_ref(),
        CppExpression::Dereference { pointer, .. }
            if matches!(pointer.as_ref(), CppExpression::Load { place, .. }
                if place.declaration_id == helper.parameters[0].declaration_id)
    ));
    assert!(matches!(
        returned_value,
        CppExpression::Dereference { pointer, .. }
            if matches!(pointer.as_ref(), CppExpression::Load { place, .. }
                if place.declaration_id == helper.parameters[0].declaration_id)
    ));

    let lowered =
        lower_import(&import).expect("lower pointer operations through kernel memory rules");
    assert_eq!(
        lowered.kernel_function().parameters()[0].c_type(),
        CType::Int32Pointer
    );
    assert_eq!(
        lowered.reachable_kernel_functions()[0].parameters()[0].c_type(),
        CType::Int32Pointer
    );
    assert!(!lowered.reachable_kernel_functions()[0].parameters()[0].pointee_is_constant());

    let click_source = fs::read_to_string(&sidecar).unwrap();
    let click_project = read_click_project(&sidecar, &click_source).unwrap();
    let verified = verify_program_prepared_project(&click_project, &import)
        .expect("verify pointer load/store and reference address through shared rules");
    assert_eq!(verified.len(), 6);

    let execute = program_prepared_project_tactic_source_position(
        &click_project,
        &import,
        "bump_reference.contract",
        0,
    )
    .unwrap();
    let expanded = expand_program_prepared_project_tactic_source_at(
        &click_project,
        &import,
        execute.line,
        execute.column,
    )
    .expect("expand the pointer caller proof");
    verify_program_prepared_project(&click_project.with_entry_source(expanded), &import)
        .expect("the expanded pointer proof must reverify");

    let missing_ownership = POINTER_SIDECAR.replacen("    owns pointer[0..1];\n", "", 1);
    fs::write(&sidecar, &missing_ownership).unwrap();
    let missing_ownership_project = read_click_project(&sidecar, &missing_ownership).unwrap();
    verify_program_prepared_project(&missing_ownership_project, &import)
        .expect_err("dereferencing without memory authority must not verify");

    let false_contract = POINTER_SIDECAR.replace(
        "ensures value[0] == old(value[0]) + 1;",
        "ensures value[0] == old(value[0]) + 2;",
    );
    fs::write(&sidecar, &false_contract).unwrap();
    let false_project = read_click_project(&sidecar, &false_contract).unwrap();
    verify_program_prepared_project(&false_project, &import)
        .expect_err("a false pointer-mediated memory effect must be rejected");
}

#[test]
fn record_reference_member_loads_and_stores_verify_offline() {
    let project = Project::struct_member();
    let sidecar = project.directory.join("demo.click");
    fs::write(&sidecar, STRUCT_MEMBER_SIDECAR).unwrap();
    refresh_import(&project.config()).expect("export the resolved C++ record layout and fields");
    fs::remove_file(&project.exporter).expect("make the frontend unavailable after refresh");

    let import = load_import(&project.config()).expect("load the record artifact offline");
    assert_eq!(import.export().schema, 33);
    let [record] = import.export().records.as_slice() else {
        panic!("the referenced record layout was not captured")
    };
    assert_eq!(record.name, "RestoreState");
    assert_eq!((record.size_bytes, record.alignment_bytes), (16, 8));
    let [pointer, saved] = record.fields.as_slice() else {
        panic!("the record fields were not captured")
    };
    assert_eq!(
        (
            pointer.name.as_str(),
            pointer.offset_bytes,
            pointer.size_bytes
        ),
        ("pointer", 0, 8)
    );
    assert!(matches!(pointer.value_type, CppType::Pointer { .. }));
    assert_eq!(
        (saved.name.as_str(), saved.offset_bytes, saved.size_bytes),
        ("saved", 8, 4)
    );
    assert!(matches!(saved.value_type, CppType::Integer { .. }));

    let function = &import.export().function;
    assert!(matches!(
        &function.parameters[0].value_type,
        CppType::LvalueReference { pointee }
            if matches!(pointee.as_ref(), CppType::Record { name, declaration_id, .. }
                if name == "RestoreState" && declaration_id == &record.declaration_id)
    ));
    assert!(matches!(
        function.body.as_slice(),
        [
            CppStatement::MemberStore { field: first, .. },
            CppStatement::MemberStore { field: second, .. },
            CppStatement::Store {
                pointer: CppExpression::MemberLoad { field: third, .. },
                ..
            },
            CppStatement::Return {
                value: CppExpression::MemberLoad { field: fourth, .. },
                ..
            },
        ] if first.declaration_id == pointer.declaration_id
            && second.declaration_id == saved.declaration_id
            && third.declaration_id == pointer.declaration_id
            && fourth.declaration_id == saved.declaration_id
    ));

    let lowered = lower_import(&import).expect("lower member operations through checked offsets");
    assert_eq!(
        lowered.kernel_function().parameters()[0].c_type(),
        CType::Int32Pointer
    );

    let click_source = fs::read_to_string(&sidecar).unwrap();
    let click_project = read_click_project(&sidecar, &click_source).unwrap();
    let verified = verify_program_prepared_project(&click_project, &import)
        .expect("verify field access and the loaded pointer through shared memory rules");
    assert_eq!(verified.len(), 7);

    let execute = program_prepared_project_tactic_source_position(
        &click_project,
        &import,
        "stage_restore.contract",
        0,
    )
    .unwrap();
    let expanded = expand_program_prepared_project_tactic_source_at(
        &click_project,
        &import,
        execute.line,
        execute.column,
    )
    .expect("expand the record execution proof");
    verify_program_prepared_project(&click_project.with_entry_source(expanded), &import)
        .expect("the expanded record proof must reverify");

    let missing_ownership = STRUCT_MEMBER_SIDECAR.replace("    owns &state->pointer;\n", "");
    fs::write(&sidecar, &missing_ownership).unwrap();
    let missing_project = read_click_project(&sidecar, &missing_ownership).unwrap();
    verify_program_prepared_project(&missing_project, &import)
        .expect_err("writing a field without its memory authority must not verify");

    let false_contract =
        STRUCT_MEMBER_SIDECAR.replace("ensures value[0] == 7;", "ensures value[0] == 8;");
    fs::write(&sidecar, &false_contract).unwrap();
    let false_project = read_click_project(&sidecar, &false_contract).unwrap();
    verify_program_prepared_project(&false_project, &import)
        .expect_err("a false pointer-mediated member effect must be rejected");
}

#[test]
fn brace_initialized_local_aggregate_verifies_offline() {
    let project = Project::local_aggregate();
    let sidecar = project.directory.join("demo.click");
    fs::write(&sidecar, LOCAL_AGGREGATE_SIDECAR).unwrap();
    refresh_import(&project.config()).expect("export the local aggregate initializer");
    fs::remove_file(&project.exporter).expect("make the frontend unavailable after refresh");

    let import = load_import(&project.config()).expect("load the aggregate artifact offline");
    assert_eq!(import.export().schema, 33);
    let [record] = import.export().records.as_slice() else {
        panic!("the local aggregate record layout was not captured")
    };
    let [pointer, saved] = record.fields.as_slice() else {
        panic!("the local aggregate fields were not captured")
    };
    let [
        CppStatement::Declare {
            local,
            initializer: CppInitializer::Aggregate { fields, .. },
            ..
        },
        CppStatement::Store {
            pointer: CppExpression::MemberLoad { object, field, .. },
            ..
        },
        CppStatement::Return {
            value:
                CppExpression::MemberLoad {
                    object: returned_object,
                    field: returned_field,
                    ..
                },
            ..
        },
    ] = import.export().function.body.as_slice()
    else {
        panic!("the local object did not retain initialization and member use")
    };
    assert!(matches!(
        &local.value_type,
        CppType::Record { declaration_id, name, .. }
            if declaration_id == &record.declaration_id && name == "RestoreState"
    ));
    assert!(matches!(
        fields.as_slice(),
        [first, second]
            if first.field.declaration_id == pointer.declaration_id
                && second.field.declaration_id == saved.declaration_id
                && matches!(first.value, CppExpression::AddressOf { .. })
                && matches!(second.value, CppExpression::Load { .. })
    ));
    assert_eq!(object.declaration_id, local.declaration_id);
    assert_eq!(field.declaration_id, pointer.declaration_id);
    assert_eq!(returned_object.declaration_id, local.declaration_id);
    assert_eq!(returned_field.declaration_id, saved.declaration_id);

    let lowered = lower_import(&import).expect("lower the local aggregate to checked stack memory");
    assert_eq!(
        contains_local_aggregate_pipeline(lowered.kernel_function().body(), "state"),
        [true, true, true]
    );

    let click_source = fs::read_to_string(&sidecar).unwrap();
    let click_project = read_click_project(&sidecar, &click_source).unwrap();
    let verified = verify_program_prepared_project(&click_project, &import)
        .expect("verify local aggregate initialization and later field reads");
    assert_eq!(verified.len(), 3);

    let execute = program_prepared_project_tactic_source_position(
        &click_project,
        &import,
        "stage_restore.contract",
        0,
    )
    .unwrap();
    let expanded = expand_program_prepared_project_tactic_source_at(
        &click_project,
        &import,
        execute.line,
        execute.column,
    )
    .expect("expand the local aggregate execution proof");
    verify_program_prepared_project(&click_project.with_entry_source(expanded), &import)
        .expect("the expanded local aggregate proof must reverify");

    let missing_ownership = LOCAL_AGGREGATE_SIDECAR.replace("    owns value[0..1];\n", "");
    fs::write(&sidecar, &missing_ownership).unwrap();
    let missing_project = read_click_project(&sidecar, &missing_ownership).unwrap();
    verify_program_prepared_project(&missing_project, &import)
        .expect_err("the initializer and later pointer write require input memory authority");

    let false_contract =
        LOCAL_AGGREGATE_SIDECAR.replace("ensures result == old(value[0]);", "ensures result == 7;");
    fs::write(&sidecar, &false_contract).unwrap();
    let false_project = read_click_project(&sidecar, &false_contract).unwrap();
    verify_program_prepared_project(&false_project, &import)
        .expect_err("a false claim about the saved initialized field must be rejected");
}

#[test]
fn explicit_constructor_local_verifies_as_a_modular_call() {
    let project = Project::constructor_local();
    let sidecar = project.directory.join("demo.click");
    fs::write(&sidecar, CONSTRUCTOR_LOCAL_SIDECAR).unwrap();
    refresh_import(&project.config()).expect("export the direct constructor call and body");
    fs::remove_file(&project.exporter).expect("make the frontend unavailable after refresh");

    let import = load_import(&project.config()).expect("load the constructor artifact offline");
    assert_eq!(import.export().schema, 33);
    let [record] = import.export().records.as_slice() else {
        panic!("the constructed record layout was not captured")
    };
    let [constructor] = import.export().reachable_functions.as_slice() else {
        panic!("the resolved constructor definition was not exported")
    };
    assert!(matches!(
        &constructor.function_kind,
        CppFunctionKind::Constructor {
            record_declaration_id,
            record_name,
        } if record_declaration_id == &record.declaration_id
            && record_name == "RestoreState"
    ));
    assert_eq!(constructor.name, "RestoreState_constructor");
    assert_eq!(constructor.return_type, CppType::Void);
    assert!(matches!(
        constructor.parameters.as_slice(),
        [self_parameter, slot]
            if self_parameter.name == "self"
                && matches!(
                    &self_parameter.value_type,
                    CppType::LvalueReference { pointee }
                        if matches!(
                            pointee.as_ref(),
                            CppType::Record { declaration_id, .. }
                                if declaration_id == &record.declaration_id
                        )
                )
                && slot.name == "slot"
                && matches!(slot.value_type, CppType::Pointer { .. })
    ));
    assert!(matches!(
        constructor.body.as_slice(),
        [
            CppStatement::MemberStore { field: pointer, .. },
            CppStatement::MemberStore { field: saved, .. },
            CppStatement::Store {
                pointer: CppExpression::MemberLoad { field: used, .. },
                ..
            },
        ] if pointer.name == "pointer" && saved.name == "saved" && used.name == "pointer"
    ));

    let [
        CppStatement::Declare {
            local,
            initializer:
                CppInitializer::Constructor {
                    callee, arguments, ..
                },
            ..
        },
        CppStatement::Return { .. },
    ] = import.export().function.body.as_slice()
    else {
        panic!("the direct object construction was not retained")
    };
    assert_eq!(local.name, "state");
    assert_eq!(callee.declaration_id, constructor.declaration_id);
    assert_eq!(callee.name, constructor.name);
    assert!(matches!(
        arguments.as_slice(),
        [CppCallArgument::Value {
            value: CppExpression::AddressOf { .. }
        }]
    ));

    let lowered = lower_import(&import).expect("lower construction through the shared call rules");
    assert!(contains_aggregate_construction_begin(
        lowered.kernel_function().body(),
        "state"
    ));
    assert!(contains_call(
        lowered.kernel_function().body(),
        "RestoreState_constructor"
    ));
    assert_eq!(lowered.reachable_kernel_functions().len(), 1);
    assert_eq!(
        lowered.reachable_kernel_functions()[0].parameters()[0].c_type(),
        CType::Int32Pointer
    );
    assert_eq!(
        lowered.reachable_kernel_functions()[0].parameters()[1].c_type(),
        CType::Int32Pointer
    );
    assert_eq!(
        lowered.reachable_kernel_functions()[0].return_type(),
        CType::Void
    );

    let click_source = fs::read_to_string(&sidecar).unwrap();
    let click_project = read_click_project(&sidecar, &click_source).unwrap();
    verify_program_prepared_project(&click_project, &import)
        .expect("verify the constructor body and its implicit local invocation modularly");

    let execute = program_prepared_project_tactic_source_position(
        &click_project,
        &import,
        "capture.contract",
        0,
    )
    .unwrap();
    let expanded = expand_program_prepared_project_tactic_source_at(
        &click_project,
        &import,
        execute.line,
        execute.column,
    )
    .expect("expand the caller proof across construction");
    verify_program_prepared_project(&click_project.with_entry_source(expanded), &import)
        .expect("the expanded constructor caller proof must reverify");

    let missing_field_ownership = CONSTRUCTOR_LOCAL_SIDECAR.replace("    owns self->saved;\n", "");
    fs::write(&sidecar, &missing_field_ownership).unwrap();
    let missing_project = read_click_project(&sidecar, &missing_field_ownership).unwrap();
    verify_program_prepared_project(&missing_project, &import)
        .expect_err("constructor member initialization requires field authority");

    let false_constructor_contract = CONSTRUCTOR_LOCAL_SIDECAR.replace(
        "ensures self->saved == old(slot[0]);",
        "ensures self->saved == old(slot[0]) + 1;",
    );
    fs::write(&sidecar, &false_constructor_contract).unwrap();
    let false_project = read_click_project(&sidecar, &false_constructor_contract).unwrap();
    verify_program_prepared_project(&false_project, &import)
        .expect_err("a false constructor field effect must be rejected");
}

#[test]
fn terminal_return_captures_value_before_checked_destructor_cleanup() {
    let project = Project::terminal_destructor();
    let sidecar = project.directory.join("demo.click");
    fs::write(&sidecar, TERMINAL_DESTRUCTOR_SIDECAR).unwrap();
    refresh_import(&project.config()).expect("export constructor and terminal destructor cleanup");
    fs::remove_file(&project.exporter).expect("make the frontend unavailable after refresh");

    let import = load_import(&project.config()).expect("load the cleanup artifact offline");
    assert_eq!(import.export().schema, 33);
    let [record] = import.export().records.as_slice() else {
        panic!("the destructible record layout was not captured")
    };
    let destructor_reference = record
        .destructor
        .as_ref()
        .expect("the record must retain its declared destructor identity");
    let constructor = import
        .export()
        .reachable_functions
        .iter()
        .find(|function| matches!(function.function_kind, CppFunctionKind::Constructor { .. }))
        .expect("constructor definition must be reachable");
    let destructor = import
        .export()
        .reachable_functions
        .iter()
        .find(|function| matches!(function.function_kind, CppFunctionKind::Destructor { .. }))
        .expect("destructor definition must be reachable");
    assert_eq!(
        destructor_reference.declaration_id,
        destructor.declaration_id
    );
    assert_eq!(destructor_reference.name, "RestoreState_destructor");
    assert!(matches!(
        &destructor.function_kind,
        CppFunctionKind::Destructor {
            record_declaration_id,
            record_name,
        } if record_declaration_id == &record.declaration_id
            && record_name == "RestoreState"
    ));
    assert_eq!(destructor.return_type, CppType::Void);
    assert!(matches!(
        destructor.parameters.as_slice(),
        [self_parameter] if self_parameter.name == "self"
    ));
    assert!(matches!(
        destructor.body.as_slice(),
        [CppStatement::Store {
            pointer: CppExpression::MemberLoad { field: pointer, .. },
            value: CppExpression::MemberLoad { field: saved, .. },
            ..
        }] if pointer.name == "pointer" && saved.name == "saved"
    ));

    let [
        CppStatement::Declare {
            local,
            initializer: CppInitializer::Constructor { callee, .. },
            ..
        },
        CppStatement::Return {
            cleanups,
            value: CppExpression::Load { .. },
            ..
        },
    ] = import.export().function.body.as_slice()
    else {
        panic!("the terminal cleanup edge was not retained")
    };
    assert_eq!(local.name, "state");
    assert_eq!(callee.declaration_id, constructor.declaration_id);
    assert!(matches!(
        cleanups.as_slice(),
        [CppCleanup::Destructor {
            object,
            callee,
            ..
        }] if object.declaration_id == local.declaration_id
            && callee.declaration_id == destructor.declaration_id
    ));

    let lowered = lower_import(&import).expect("lower return capture and destructor cleanup");
    assert_eq!(
        call_order(lowered.kernel_function().body()),
        ["RestoreState_constructor", "RestoreState_destructor"]
    );
    assert!(matches!(
        lowered.kernel_function().body(),
        CStatement::Seq(_, returned)
            if matches!(
                returned.as_ref(),
                CStatement::Seq(_, returned)
                    if matches!(
                        returned.as_ref(),
                        CStatement::Return(CExpression::Variable(name))
                            if name.starts_with("__click_cpp_return_value")
                    )
            )
    ));

    let click_source = fs::read_to_string(&sidecar).unwrap();
    let click_project = read_click_project(&sidecar, &click_source).unwrap();
    verify_program_prepared_project(&click_project, &import)
        .expect("verify captured result and restored caller memory");

    let execute = program_prepared_project_tactic_source_position(
        &click_project,
        &import,
        "capture.contract",
        0,
    )
    .unwrap();
    let expanded = expand_program_prepared_project_tactic_source_at(
        &click_project,
        &import,
        execute.line,
        execute.column,
    )
    .expect("expand the proof across terminal cleanup");
    verify_program_prepared_project(&click_project.with_entry_source(expanded), &import)
        .expect("expanded terminal-cleanup proof must reverify");

    let missing_destructor = TERMINAL_DESTRUCTOR_SIDECAR.replace(
        "void RestoreState_destructor(struct RestoreState* self) {\n    requires separate(memory(object(self)), memory(self->pointer[0..1]));\n    owns &self->pointer;\n    owns self->saved;\n    owns self->pointer[0..1];\n    ensures self->pointer == old(self->pointer);\n    ensures self->saved == old(self->saved);\n    ensures self->pointer[0] == old(self->saved);\n} by {\n    execute();\n    simp();\n}\n\n",
        "",
    );
    fs::write(&sidecar, &missing_destructor).unwrap();
    let missing_project = read_click_project(&sidecar, &missing_destructor).unwrap();
    verify_program_prepared_project(&missing_project, &import)
        .expect_err("implicit cleanup requires a checked destructor contract");

    let false_destructor = TERMINAL_DESTRUCTOR_SIDECAR.replace(
        "ensures self->pointer[0] == old(self->saved);",
        "ensures self->pointer[0] == old(self->saved) + 1;",
    );
    fs::write(&sidecar, &false_destructor).unwrap();
    let false_project = read_click_project(&sidecar, &false_destructor).unwrap();
    verify_program_prepared_project(&false_project, &import)
        .expect_err("a false destructor restore effect must be rejected");

    let wrong_capture = TERMINAL_DESTRUCTOR_SIDECAR
        .replace("ensures result == 7;", "ensures result == old(value[0]);");
    fs::write(&sidecar, &wrong_capture).unwrap();
    let wrong_project = read_click_project(&sidecar, &wrong_capture).unwrap();
    verify_program_prepared_project(&wrong_project, &import)
        .expect_err("the return value must be captured before destruction");
}

#[test]
fn every_return_after_construction_runs_the_checked_destructor() {
    let project = Project::early_return_destructor();
    let sidecar = project.directory.join("demo.click");
    fs::write(&sidecar, EARLY_RETURN_DESTRUCTOR_SIDECAR).unwrap();
    refresh_import(&project.config()).expect("export cleanup on both C++ return edges");
    fs::remove_file(&project.exporter).expect("make the frontend unavailable after refresh");

    let import = load_import(&project.config()).expect("load the cleanup artifact offline");
    assert_eq!(import.export().schema, 33);
    let destructor = import
        .export()
        .reachable_functions
        .iter()
        .find(|function| matches!(function.function_kind, CppFunctionKind::Destructor { .. }))
        .expect("destructor definition must be reachable");
    let [
        CppStatement::Declare { local, .. },
        CppStatement::If { then_branch, .. },
        CppStatement::Assign { .. },
        CppStatement::Return {
            cleanups: final_cleanups,
            ..
        },
    ] = import.export().function.body.as_slice()
    else {
        panic!("the two cleanup-bearing return paths were not retained")
    };
    let [
        CppStatement::Return {
            cleanups: early_cleanups,
            ..
        },
    ] = then_branch.as_slice()
    else {
        panic!("the early return edge was not retained")
    };
    for cleanups in [early_cleanups, final_cleanups] {
        assert!(matches!(
            cleanups.as_slice(),
            [CppCleanup::Destructor {
                object,
                callee,
                ..
            }] if object.declaration_id == local.declaration_id
                && callee.declaration_id == destructor.declaration_id
        ));
    }

    let lowered = lower_import(&import).expect("lower cleanup on both return edges");
    assert_eq!(
        call_order(lowered.kernel_function().body()),
        [
            "Restore_constructor",
            "Restore_destructor",
            "Restore_destructor"
        ]
    );

    let click_source = fs::read_to_string(&sidecar).unwrap();
    let click_project = read_click_project(&sidecar, &click_source).unwrap();
    let verified = verify_program_prepared_project(&click_project, &import)
        .expect("verify both captured results and both restored-memory paths");
    let ensure_indices = verified
        .iter()
        .map(|theorem| match theorem.claim {
            VerifiedClaim::Ensure { index, .. } => index,
            VerifiedClaim::ExceptionalEnsure { index, .. } => index,
        })
        .collect::<Vec<_>>();
    assert!(
        ensure_indices.ends_with(&[0, 1, 2, 3, 0, 1, 2, 3]),
        "both caller return paths must certify ownership, the captured result, and restoration: {ensure_indices:?}"
    );

    let execute = program_prepared_project_tactic_source_position(
        &click_project,
        &import,
        "with_restore.contract",
        0,
    )
    .unwrap();
    let expanded = expand_program_prepared_project_tactic_source_at(
        &click_project,
        &import,
        execute.line,
        execute.column,
    )
    .expect("expand the proof across both cleanup edges");
    verify_program_prepared_project(&click_project.with_entry_source(expanded), &import)
        .expect("the expanded early-return cleanup proof must reverify");

    let wrong_early_result = EARLY_RETURN_DESTRUCTOR_SIDECAR.replace(
        "ensures early != 0 implies result == 7;",
        "ensures early != 0 implies result == 9;",
    );
    fs::write(&sidecar, &wrong_early_result).unwrap();
    let wrong_project = read_click_project(&sidecar, &wrong_early_result).unwrap();
    verify_program_prepared_project(&wrong_project, &import)
        .expect_err("cleanup must not overwrite the value captured by the early return");
}

#[test]
fn modular_caller_observes_captured_result_and_restored_entry_value() {
    assert!(
        RESTORE_CALLER_SOURCE.starts_with(EARLY_RETURN_DESTRUCTOR_SOURCE),
        "the caller fixture must preserve the original RAII source verbatim"
    );
    let project = Project::restore_caller();
    let sidecar = project.directory.join("demo.click");
    fs::write(&sidecar, RESTORE_CALLER_SIDECAR).unwrap();
    refresh_import(&project.config()).expect("export the RAII helper and its modular caller");
    fs::remove_file(&project.exporter).expect("make the frontend unavailable after refresh");

    let import = load_import(&project.config()).expect("load the caller artifact offline");
    assert_eq!(import.export().function.name, "call_with_restore");
    assert!(
        import
            .export()
            .reachable_functions
            .iter()
            .any(|function| function.name == "with_restore"),
        "the helper definition must be reachable from the selected caller"
    );
    let CppStatement::Declare {
        initializer: CppInitializer::Call { callee, .. },
        ..
    } = &import.export().function.body[0]
    else {
        panic!("the caller must capture a resolved call result")
    };
    assert_eq!(callee.name, "with_restore");
    let lowered = lower_import(&import).expect("lower the modular RAII call");
    assert!(
        contains_scalar_local_pipeline(
            lowered.kernel_function().body(),
            "captured",
            "unused",
            "with_restore"
        )[..2]
            .iter()
            .all(|found| *found),
        "the captured call must remain a checked kernel call assignment"
    );

    let click_project = read_click_project(&sidecar, RESTORE_CALLER_SIDECAR).unwrap();
    verify_program_prepared_project(&click_project, &import)
        .expect("the caller must receive 7 or 9 and still own an unchanged 41");
    let execute = program_prepared_project_tactic_source_position(
        &click_project,
        &import,
        "call_with_restore.contract",
        0,
    )
    .unwrap();
    let expanded = expand_program_prepared_project_tactic_source_at(
        &click_project,
        &import,
        execute.line,
        execute.column,
    )
    .expect("expand the caller's checked modular execution");
    let rewritten = click_project.with_entry_source(expanded.clone());
    verify_program_prepared_project(&rewritten, &import)
        .expect("the expanded RAII caller proof must reverify");
    let (session, _) = C0VerificationSession::new_program_prepared_project(&click_project, &import)
        .expect("retain the caller's original verification environment");
    let next = program_prepared_project_tactic_source_position(
        &rewritten,
        &import,
        "call_with_restore.contract",
        0,
    )
    .unwrap();
    session
        .verify_at_project(&expanded, next.line, next.column)
        .expect("retained audit session must accept the expanded RAII caller proof");

    let false_restoration =
        RESTORE_CALLER_SIDECAR.replace("ensures value[0] == 41;", "ensures value[0] == 42;");
    fs::write(&sidecar, &false_restoration).unwrap();
    let false_project = read_click_project(&sidecar, &false_restoration).unwrap();
    verify_program_prepared_project(&false_project, &import)
        .expect_err("the caller cannot claim a different post-call value");
}

#[test]
fn two_constructed_objects_are_destroyed_in_reverse_order_on_every_return() {
    let project = Project::reverse_destructor_order();
    let sidecar = project.directory.join("demo.click");
    fs::write(&sidecar, REVERSE_DESTRUCTOR_SIDECAR).unwrap();
    refresh_import(&project.config()).expect("export reverse cleanup on both C++ return edges");
    fs::remove_file(&project.exporter).expect("make the frontend unavailable after refresh");

    let import = load_import(&project.config()).expect("load the ordered cleanup artifact offline");
    assert_eq!(import.export().schema, 33);
    let [
        CppStatement::Declare { local: first, .. },
        CppStatement::Declare { local: second, .. },
        CppStatement::If { then_branch, .. },
        CppStatement::Assign { .. },
        CppStatement::Return {
            cleanups: final_cleanups,
            ..
        },
    ] = import.export().function.body.as_slice()
    else {
        panic!("the two constructed objects and return edges were not retained")
    };
    let [
        CppStatement::Return {
            cleanups: early_cleanups,
            ..
        },
    ] = then_branch.as_slice()
    else {
        panic!("the early return edge was not retained")
    };
    assert_eq!(first.name, "first");
    assert_eq!(second.name, "second");
    for cleanups in [early_cleanups, final_cleanups] {
        let [
            CppCleanup::Destructor {
                object: second_cleanup,
                ..
            },
            CppCleanup::Destructor {
                object: first_cleanup,
                ..
            },
        ] = cleanups.as_slice()
        else {
            panic!("each return must retain two destructor calls")
        };
        assert_eq!(second_cleanup.declaration_id, second.declaration_id);
        assert_eq!(first_cleanup.declaration_id, first.declaration_id);
    }

    let lowered = lower_import(&import).expect("lower both reversed cleanup lists");
    assert_eq!(
        destructor_object_order(lowered.kernel_function().body(), "Restore_destructor"),
        ["second", "first", "second", "first"]
    );

    let click_source = fs::read_to_string(&sidecar).unwrap();
    let click_project = read_click_project(&sidecar, &click_source).unwrap();
    verify_program_prepared_project(&click_project, &import)
        .expect("verify both return values and reverse-order restoration");

    let execute = program_prepared_project_tactic_source_position(
        &click_project,
        &import,
        "restore_twice.contract",
        0,
    )
    .unwrap();
    let expanded = expand_program_prepared_project_tactic_source_at(
        &click_project,
        &import,
        execute.line,
        execute.column,
    )
    .expect("expand the proof across both ordered cleanup lists");
    verify_program_prepared_project(&click_project.with_entry_source(expanded), &import)
        .expect("the expanded reverse-cleanup proof must reverify");

    let rejected = Project::reverse_destructor_order();
    fs::write(
        rejected.source(),
        REVERSE_DESTRUCTOR_SOURCE.replace(
            "Restore second(&value);",
            "Restore second(&value);\n    Restore third(&value);",
        ),
    )
    .unwrap();
    let error = refresh_import(&rejected.config()).unwrap_err();
    assert!(error.contains("restore_twice.cpp"), "{error}");
    assert!(
        error.contains("exactly two destructible objects"),
        "{error}"
    );
}

#[test]
fn nested_scope_destroys_its_object_on_return_and_fallthrough() {
    let project = Project::nested_scope_destructor();
    let sidecar = project.directory.join("demo.click");
    fs::write(&sidecar, NESTED_SCOPE_DESTRUCTOR_SIDECAR).unwrap();
    refresh_import(&project.config()).expect("export both nested-scope cleanup edges");
    fs::remove_file(&project.exporter).expect("make the frontend unavailable after refresh");

    let import = load_import(&project.config()).expect("load the nested-scope artifact offline");
    assert_eq!(import.export().schema, 33);
    let destructor = import
        .export()
        .reachable_functions
        .iter()
        .find(|function| matches!(function.function_kind, CppFunctionKind::Destructor { .. }))
        .expect("destructor definition must be reachable");
    let [
        CppStatement::Scope {
            body,
            cleanups: fallthrough_cleanups,
            ..
        },
        CppStatement::Return {
            cleanups: outer_cleanups,
            ..
        },
    ] = import.export().function.body.as_slice()
    else {
        panic!("the lexical cleanup boundary was not retained")
    };
    let [
        CppStatement::Declare { local, .. },
        CppStatement::If { then_branch, .. },
        CppStatement::Assign { .. },
    ] = body.as_slice()
    else {
        panic!("the nested block body was not retained")
    };
    let [
        CppStatement::Return {
            cleanups: early_cleanups,
            ..
        },
    ] = then_branch.as_slice()
    else {
        panic!("the nested early return was not retained")
    };
    assert!(outer_cleanups.is_empty());
    for cleanups in [early_cleanups, fallthrough_cleanups] {
        assert!(matches!(
            cleanups.as_slice(),
            [CppCleanup::Destructor {
                object,
                callee,
                ..
            }] if object.declaration_id == local.declaration_id
                && callee.declaration_id == destructor.declaration_id
        ));
    }

    let lowered = lower_import(&import).expect("lower the lexical cleanup boundary directly");
    assert_eq!(
        destructor_object_order(lowered.kernel_function().body(), "Restore_destructor"),
        ["guard", "guard"]
    );

    let click_source = fs::read_to_string(&sidecar).unwrap();
    let click_project = read_click_project(&sidecar, &click_source).unwrap();
    verify_program_prepared_project(&click_project, &import)
        .expect("verify early exit and normal exit from the nested scope");

    let execute = program_prepared_project_tactic_source_position(
        &click_project,
        &import,
        "scoped_restore.contract",
        0,
    )
    .unwrap();
    let expanded = expand_program_prepared_project_tactic_source_at(
        &click_project,
        &import,
        execute.line,
        execute.column,
    )
    .expect("expand the proof across both nested-scope cleanup edges");
    verify_program_prepared_project(&click_project.with_entry_source(expanded), &import)
        .expect("the expanded nested-scope proof must reverify");

    let wrong_fallthrough = NESTED_SCOPE_DESTRUCTOR_SIDECAR.replace(
        "ensures early == 0 implies result == old(value[0]);",
        "ensures early == 0 implies result == 9;",
    );
    fs::write(&sidecar, &wrong_fallthrough).unwrap();
    let wrong_project = read_click_project(&sidecar, &wrong_fallthrough).unwrap();
    verify_program_prepared_project(&wrong_project, &import)
        .expect_err("fallthrough destruction must occur before the outer return");
}

#[test]
fn sibling_scopes_reuse_a_local_name_with_independent_cleanup() {
    let project = Project::sibling_scope_destructors();
    let sidecar = project.directory.join("demo.click");
    fs::write(&sidecar, SIBLING_SCOPE_DESTRUCTORS_SIDECAR).unwrap();
    refresh_import(&project.config()).expect("export both sibling cleanup scopes");
    fs::remove_file(&project.exporter).expect("make the frontend unavailable after refresh");

    let import = load_import(&project.config()).expect("load the sibling-scope artifact offline");
    let [
        CppStatement::Scope {
            body: first_body,
            cleanups: first_fallthrough,
            ..
        },
        CppStatement::Scope {
            body: second_body,
            cleanups: second_fallthrough,
            ..
        },
        CppStatement::Return {
            cleanups: outer_cleanups,
            ..
        },
    ] = import.export().function.body.as_slice()
    else {
        panic!("the two sibling lifetime boundaries were not retained")
    };
    let [
        CppStatement::Declare {
            local: first_local, ..
        },
        CppStatement::If {
            then_branch: first_then,
            ..
        },
        CppStatement::Assign { .. },
    ] = first_body.as_slice()
    else {
        panic!("the first sibling scope was not retained")
    };
    let [
        CppStatement::Declare {
            local: second_local,
            ..
        },
        CppStatement::If {
            then_branch: second_then,
            ..
        },
        CppStatement::Assign { .. },
    ] = second_body.as_slice()
    else {
        panic!("the second sibling scope was not retained")
    };
    assert_eq!(first_local.name, "guard");
    assert_eq!(second_local.name, "guard");
    assert_ne!(first_local.declaration_id, second_local.declaration_id);
    assert!(outer_cleanups.is_empty());
    for (local, branch, fallthrough) in [
        (first_local, first_then, first_fallthrough),
        (second_local, second_then, second_fallthrough),
    ] {
        let [
            CppStatement::Return {
                cleanups: return_cleanups,
                ..
            },
        ] = branch.as_slice()
        else {
            panic!("a sibling scope lost its early return")
        };
        for cleanups in [return_cleanups, fallthrough] {
            assert!(matches!(
                cleanups.as_slice(),
                [CppCleanup::Destructor { object, .. }]
                    if object.declaration_id == local.declaration_id
                        && object.name == local.name
            ));
        }
    }

    let lowered = lower_import(&import).expect("lower the sibling lexical lifetimes directly");
    assert_eq!(
        call_order(lowered.kernel_function().body()),
        [
            "Restore_constructor",
            "Restore_destructor",
            "Restore_destructor",
            "Restore_constructor",
            "Restore_destructor",
            "Restore_destructor",
        ]
    );

    let click_source = fs::read_to_string(&sidecar).unwrap();
    let click_project = read_click_project(&sidecar, &click_source).unwrap();
    verify_program_prepared_project(&click_project, &import)
        .expect("verify independent cleanup and restoration in both sibling scopes");

    let execute = program_prepared_project_tactic_source_position(
        &click_project,
        &import,
        "sibling_restore.contract",
        0,
    )
    .unwrap();
    let expanded = expand_program_prepared_project_tactic_source_at(
        &click_project,
        &import,
        execute.line,
        execute.column,
    )
    .expect("expand the proof across both sibling lifetime boundaries");
    verify_program_prepared_project(&click_project.with_entry_source(expanded), &import)
        .expect("the expanded sibling-scope proof must reverify");

    let wrong_final = SIBLING_SCOPE_DESTRUCTORS_SIDECAR.replace(
        "second_early == 0 implies result == old(value[0])",
        "second_early == 0 implies result == 11",
    );
    fs::write(&sidecar, &wrong_final).unwrap();
    let wrong_project = read_click_project(&sidecar, &wrong_final).unwrap();
    verify_program_prepared_project(&wrong_project, &import)
        .expect_err("the second scope must clean up before the final outer return");

    let rejected = Project::sibling_scope_destructors();
    fs::write(
        rejected.source(),
        SIBLING_SCOPE_DESTRUCTORS_SOURCE.replace(
            "    return value;\n}",
            "    {\n        Restore guard(&value);\n        value = 13;\n    }\n    return value;\n}",
        ),
    )
    .unwrap();
    let error = refresh_import(&rejected.config()).unwrap_err();
    assert!(error.contains("sibling_restore.cpp"), "{error}");
    assert!(
        error.contains("at most two sibling cleanup scopes"),
        "{error}"
    );
    assert!(!rejected.artifact().exists());
}

#[test]
fn overlapping_scope_destroys_inner_before_outer_on_every_exit() {
    let project = Project::overlapping_scope_destructors();
    let sidecar = project.directory.join("demo.click");
    fs::write(&sidecar, OVERLAPPING_SCOPE_DESTRUCTORS_SIDECAR).unwrap();
    refresh_import(&project.config()).expect("export overlapping cleanup lifetimes");
    fs::remove_file(&project.exporter).expect("make the frontend unavailable after refresh");

    let import =
        load_import(&project.config()).expect("load the overlapping-scope artifact offline");
    let [
        CppStatement::Declare {
            local: outer_local, ..
        },
        CppStatement::Scope {
            body: inner_body,
            cleanups: inner_fallthrough,
            ..
        },
        CppStatement::Declare { .. },
        CppStatement::Return {
            cleanups: final_cleanups,
            ..
        },
    ] = import.export().function.body.as_slice()
    else {
        panic!("the overlapping lexical cleanup boundary was not retained")
    };
    let [
        CppStatement::Declare {
            local: inner_local, ..
        },
        CppStatement::If { then_branch, .. },
        CppStatement::Assign { .. },
    ] = inner_body.as_slice()
    else {
        panic!("the inner cleanup scope body was not retained")
    };
    let [
        CppStatement::Return {
            cleanups: early_cleanups,
            ..
        },
    ] = then_branch.as_slice()
    else {
        panic!("the overlapping early return was not retained")
    };
    assert_eq!(outer_local.name, "outer");
    assert_eq!(inner_local.name, "inner");
    assert!(matches!(
        inner_fallthrough.as_slice(),
        [CppCleanup::Destructor { object, .. }]
            if object.declaration_id == inner_local.declaration_id
    ));
    assert!(matches!(
        early_cleanups.as_slice(),
        [
            CppCleanup::Destructor {
                object: inner_object,
                ..
            },
            CppCleanup::Destructor {
                object: outer_object,
                ..
            },
        ] if inner_object.declaration_id == inner_local.declaration_id
            && outer_object.declaration_id == outer_local.declaration_id
    ));
    assert!(matches!(
        final_cleanups.as_slice(),
        [CppCleanup::Destructor { object, .. }]
            if object.declaration_id == outer_local.declaration_id
    ));

    let lowered = lower_import(&import).expect("lower the overlapping lifetimes directly");
    assert_eq!(
        destructor_object_order(lowered.kernel_function().body(), "Restore_destructor"),
        ["inner", "outer", "inner", "outer"]
    );

    let click_source = fs::read_to_string(&sidecar).unwrap();
    let click_project = read_click_project(&sidecar, &click_source).unwrap();
    verify_program_prepared_project(&click_project, &import)
        .expect("verify inner-then-outer cleanup and memory restoration");

    let execute = program_prepared_project_tactic_source_position(
        &click_project,
        &import,
        "overlap_restore.contract",
        0,
    )
    .unwrap();
    let expanded = expand_program_prepared_project_tactic_source_at(
        &click_project,
        &import,
        execute.line,
        execute.column,
    )
    .expect("expand the proof across overlapping cleanup lifetimes");
    verify_program_prepared_project(&click_project.with_entry_source(expanded), &import)
        .expect("the expanded overlapping-cleanup proof must reverify");

    let wrong_result = OVERLAPPING_SCOPE_DESTRUCTORS_SIDECAR
        .replace("ensures result == 7;", "ensures result == 11;");
    fs::write(&sidecar, &wrong_result).unwrap();
    let wrong_project = read_click_project(&sidecar, &wrong_result).unwrap();
    verify_program_prepared_project(&wrong_project, &import)
        .expect_err("inner fallthrough cleanup must restore 7 before the final return");
}

#[test]
fn overlapping_scope_rejects_shadowing_and_a_second_inner_lifetime() {
    for (source, expected) in [
        (
            OVERLAPPING_SCOPE_DESTRUCTORS_SOURCE.replace("Restore inner", "Restore outer"),
            "shadows another supported place",
        ),
        (
            OVERLAPPING_SCOPE_DESTRUCTORS_SOURCE.replace(
                "    int observed = value;",
                "    {\n        Restore later(&value);\n        value = 13;\n    }\n    int observed = value;",
            ),
            "permits one inner cleanup scope with an outer object",
        ),
    ] {
        let project = Project::overlapping_scope_destructors();
        fs::write(project.source(), source).unwrap();
        let error = refresh_import(&project.config()).unwrap_err();
        assert!(error.contains(expected), "{error}");
        assert!(!project.artifact().exists());
    }
}

#[test]
fn conditional_construction_cleans_up_only_the_constructed_arm() {
    let project = Project::conditional_construction();
    let sidecar = project.directory.join("demo.click");
    fs::write(&sidecar, CONDITIONAL_CONSTRUCTION_SIDECAR).unwrap();
    refresh_import(&project.config()).expect("export the conditional object lifetime");
    fs::remove_file(&project.exporter).expect("make the frontend unavailable after refresh");

    let import =
        load_import(&project.config()).expect("load the conditional-construction artifact offline");
    let [
        CppStatement::If {
            then_branch,
            else_branch,
            ..
        },
        CppStatement::Return {
            cleanups: final_cleanups,
            ..
        },
    ] = import.export().function.body.as_slice()
    else {
        panic!("the conditional lifetime boundary was not retained")
    };
    let [
        CppStatement::Scope {
            body,
            cleanups: fallthrough_cleanups,
            ..
        },
    ] = then_branch.as_slice()
    else {
        panic!("the constructed arm was not retained as a cleanup scope")
    };
    let [
        CppStatement::Declare { local, .. },
        CppStatement::If {
            then_branch: early_branch,
            ..
        },
        CppStatement::Assign { .. },
    ] = body.as_slice()
    else {
        panic!("the conditional cleanup scope body was not retained")
    };
    let [
        CppStatement::Return {
            cleanups: early_cleanups,
            ..
        },
    ] = early_branch.as_slice()
    else {
        panic!("the constructed arm's early return was not retained")
    };
    assert!(else_branch.is_empty());
    assert!(final_cleanups.is_empty());
    for cleanups in [early_cleanups, fallthrough_cleanups] {
        assert!(matches!(
            cleanups.as_slice(),
            [CppCleanup::Destructor { object, .. }]
                if object.declaration_id == local.declaration_id
                    && object.name == "guard"
        ));
    }

    let lowered = lower_import(&import).expect("lower the conditional lifetime directly");
    assert_eq!(
        call_order(lowered.kernel_function().body()),
        [
            "Restore_constructor",
            "Restore_destructor",
            "Restore_destructor",
        ]
    );

    let click_source = fs::read_to_string(&sidecar).unwrap();
    let click_project = read_click_project(&sidecar, &click_source).unwrap();
    verify_program_prepared_project(&click_project, &import).expect(
        "verify cleanup on constructed paths without calling the destructor on the skipped path",
    );

    let execute = program_prepared_project_tactic_source_position(
        &click_project,
        &import,
        "conditional_restore.contract",
        0,
    )
    .unwrap();
    let expanded = expand_program_prepared_project_tactic_source_at(
        &click_project,
        &import,
        execute.line,
        execute.column,
    )
    .expect("expand the proof across the conditional lifetime");
    verify_program_prepared_project(&click_project.with_entry_source(expanded), &import)
        .expect("the expanded conditional-construction proof must reverify");

    let wrong_skipped_result = CONDITIONAL_CONSTRUCTION_SIDECAR.replace(
        "ensures construct == 0 implies result == 41;",
        "ensures construct == 0 implies result == 7;",
    );
    fs::write(&sidecar, &wrong_skipped_result).unwrap();
    let wrong_project = read_click_project(&sidecar, &wrong_skipped_result).unwrap();
    verify_program_prepared_project(&wrong_project, &import)
        .expect_err("the skipped-construction path must return the untouched input");
}

#[test]
fn conditional_construction_rejects_both_arms_outer_objects_and_deeper_objects() {
    for (source, expected) in [
        (
            CONDITIONAL_CONSTRUCTION_SOURCE.replace(
                "        value = 9;\n    }\n    return value;",
                "        value = 9;\n    } else {\n        Restore other(&value);\n        value = 11;\n    }\n    return value;",
            ),
            "exactly one cleanup scope in one if arm",
        ),
        (
            CONDITIONAL_CONSTRUCTION_SOURCE.replace(
                "int conditional_restore(bool construct, bool early, int& value) noexcept {\n    if (construct)",
                "int conditional_restore(bool construct, bool early, int& value) noexcept {\n    Restore outer(&value);\n    if (construct)",
            ),
            "conditional construction cannot yet be combined with an outer aggregate object",
        ),
        (
            CONDITIONAL_CONSTRUCTION_SOURCE.replace(
                "        Restore guard(&value);",
                "        if (early) {\n            Restore nested(&value);\n        }\n        Restore guard(&value);",
            ),
            "automatic C++ locals are currently supported only in the function body",
        ),
    ] {
        let project = Project::conditional_construction();
        fs::write(project.source(), source).unwrap();
        let error = refresh_import(&project.config()).unwrap_err();
        assert!(error.contains(expected), "{error}");
        assert!(!project.artifact().exists());
    }
}

#[test]
fn nested_scope_rejects_conditional_construction_and_deeper_blocks() {
    for (source, expected) in [
        (
            NESTED_SCOPE_DESTRUCTOR_SOURCE.replace(
                "        Restore guard(&value);\n        if (early) {\n            return value;\n        }\n        value = 9;",
                "        if (early) {\n            Restore guard(&value);\n        }",
            ),
            "automatic C++ locals are currently supported only in the function body",
        ),
        (
            NESTED_SCOPE_DESTRUCTOR_SOURCE.replace(
                "        Restore guard(&value);",
                "        {\n            Restore guard(&value);\n        }",
            ),
            "permits one nested scope directly in a free-function body",
        ),
    ] {
        let project = Project::nested_scope_destructor();
        fs::write(project.source(), source).unwrap();
        let error = refresh_import(&project.config()).unwrap_err();
        assert!(error.contains("scoped_restore.cpp"), "{error}");
        assert!(error.contains(expected), "{error}");
        assert!(!project.artifact().exists());
    }
}

#[test]
fn constructor_local_rejects_implicit_throwing_partial_and_reordered_forms() {
    let project = Project::constructor_local();
    for (source, expected) in [
        (
            "struct RestoreState {\n    int* pointer;\n    int saved;\n    RestoreState(int* slot) noexcept : pointer(slot), saved(*slot) {}\n};\nint capture(int& value) noexcept { RestoreState state(&value); return state.saved; }\n",
            "public explicit non-default noexcept constructor",
        ),
        (
            "struct RestoreState {\n    int* pointer;\n    int saved;\n    explicit RestoreState(int* slot) : pointer(slot), saved(*slot) {}\n};\nint capture(int& value) noexcept { RestoreState state(&value); return state.saved; }\n",
            "public explicit non-default noexcept constructor",
        ),
        (
            "struct RestoreState {\n    int* pointer;\n    int saved;\n    explicit RestoreState(int* slot) noexcept : pointer(slot) {}\n};\nint capture(int& value) noexcept { RestoreState state(&value); return state.saved; }\n",
            "explicitly initialize every field",
        ),
        (
            "struct RestoreState {\n    int* pointer;\n    int saved;\n    explicit RestoreState(int* slot) noexcept : saved(*slot), pointer(slot) {}\n};\nint capture(int& value) noexcept { RestoreState state(&value); return state.saved; }\n",
            "initializer list must follow declaration order",
        ),
    ] {
        fs::write(project.source(), source).unwrap();
        let error = refresh_import(&project.config()).unwrap_err();
        assert!(error.contains("capture.cpp"), "{error}");
        assert!(error.contains(expected), "{error}");
        assert!(!project.artifact().exists());
    }
}

#[test]
fn terminal_destructor_rejects_throwing_virtual_empty_and_nonterminal_cleanup() {
    let project = Project::terminal_destructor();
    for (source, expected) in [
        (
            TERMINAL_DESTRUCTOR_SOURCE.replace(
                "~RestoreState() noexcept",
                "~RestoreState() noexcept(false)",
            ),
            "public, non-virtual, non-deleted, and explicitly noexcept",
        ),
        (
            TERMINAL_DESTRUCTOR_SOURCE.replace("~RestoreState() noexcept", "~RestoreState()"),
            "public, non-virtual, non-deleted, and explicitly noexcept",
        ),
        (
            TERMINAL_DESTRUCTOR_SOURCE.replace(
                "~RestoreState() noexcept",
                "virtual ~RestoreState() noexcept",
            ),
            "standard-layout",
        ),
        (
            TERMINAL_DESTRUCTOR_SOURCE.replace(
                "~RestoreState() noexcept {\n        *pointer = saved;\n    }",
                "~RestoreState() noexcept {}",
            ),
            "nonempty destructor body",
        ),
        (
            TERMINAL_DESTRUCTOR_SOURCE.replace(
                "return value;",
                "int result = value;\n    return result;\n    value = 9;",
            ),
            "requires one final return",
        ),
    ] {
        fs::write(project.source(), source).unwrap();
        let error = refresh_import(&project.config()).unwrap_err();
        assert!(error.contains("capture.cpp"), "{error}");
        assert!(error.contains(expected), "{error}");
        assert!(!project.artifact().exists());
    }
}

#[test]
fn cpp_local_aggregate_rejects_partial_default_copy_nested_and_second_objects() {
    let project = Project::local_aggregate();

    for (source, expected) in [
        (
            "struct RestoreState { int* pointer; int saved; };\nint stage_restore(int& value) noexcept {\n    RestoreState state{&value};\n    return value;\n}\n",
            "one direct brace initializer per field",
        ),
        (
            "struct RestoreState { int* pointer; int saved; };\nint stage_restore(int& value) noexcept {\n    RestoreState state;\n    return value;\n}\n",
            "one direct brace initializer per field",
        ),
        (
            "struct RestoreState { int* pointer; int saved; };\nint stage_restore(RestoreState& original, int& value) noexcept {\n    RestoreState copied = original;\n    return value;\n}\n",
            "one direct brace initializer per field",
        ),
        (
            "struct RestoreState { int* pointer; int saved; };\nint stage_restore(int& value, bool condition) noexcept {\n    if (condition) { RestoreState state{&value, value}; }\n    return value;\n}\n",
            "only in the function body",
        ),
        (
            "struct RestoreState { int* pointer; int saved; };\nint stage_restore(int& value) noexcept {\n    RestoreState first{&value, value};\n    RestoreState second{&value, value};\n    return value;\n}\n",
            "one aggregate object or exactly two destructible objects",
        ),
    ] {
        fs::write(project.source(), source).unwrap();
        let error = refresh_import(&project.config()).unwrap_err();
        assert!(error.contains("stage_restore.cpp"), "{error}");
        assert!(error.contains(expected), "{error}");
        assert!(!project.artifact().exists());
    }
}

#[test]
fn cpp_pointer_slice_rejects_arithmetic_null_multilevel_and_pointer_locals() {
    let project = Project::pointer();

    fs::write(
        project.source(),
        "int bump_reference(int* pointer) noexcept {\n    return *(pointer + 1);\n}\n",
    )
    .unwrap();
    let error = refresh_import(&project.config()).unwrap_err();
    assert!(error.contains("bump_reference.cpp:2"), "{error}");
    assert!(error.contains("pointer arithmetic"), "{error}");
    assert!(!project.artifact().exists());

    fs::write(
        project.source(),
        "int read_pointer(int* pointer) noexcept { return *pointer; }\n\nint bump_reference(int& value) noexcept {\n    int result = read_pointer(nullptr);\n    return result;\n}\n",
    )
    .unwrap();
    let error = refresh_import(&project.config()).unwrap_err();
    assert!(error.contains("bump_reference.cpp:4"), "{error}");
    assert!(error.contains("unsupported implicit conversion"), "{error}");
    assert!(!project.artifact().exists());

    fs::write(
        project.source(),
        "int bump_reference(int& value) noexcept {\n    int* pointer = &value;\n    return *pointer;\n}\n",
    )
    .unwrap();
    let error = refresh_import(&project.config()).unwrap_err();
    assert!(error.contains("bump_reference.cpp:2"), "{error}");
    assert!(
        error.contains("must resolve to mutable signed/unsigned 32/64-bit integer"),
        "{error}"
    );
    assert!(!project.artifact().exists());

    fs::write(
        project.source(),
        "int bump_reference(int** pointer) noexcept {\n    return **pointer;\n}\n",
    )
    .unwrap();
    let error = refresh_import(&project.config()).unwrap_err();
    assert!(error.contains("bump_reference.cpp:1"), "{error}");
    assert!(error.contains("mutable int* parameter"), "{error}");
    assert!(!project.artifact().exists());
}

#[test]
fn cpp_record_slice_rejects_unresolved_methods_bitfields_and_inheritance() {
    let project = Project::struct_member();

    fs::write(
        project.source(),
        "struct RestoreState {\n    int saved;\n    int read() noexcept;\n};\n\nint stage_restore(RestoreState& state, int& value) noexcept {\n    state.read();\n    return state.saved;\n}\n",
    )
    .unwrap();
    let error = refresh_import(&project.config()).unwrap_err();
    assert!(
        error.contains("no reachable function definition"),
        "{error}"
    );
    assert!(!project.artifact().exists());

    fs::write(
        project.source(),
        "struct RestoreState {\n    int saved : 4;\n};\n\nint stage_restore(RestoreState& state, int& value) noexcept {\n    return state.saved;\n}\n",
    )
    .unwrap();
    let error = refresh_import(&project.config()).unwrap_err();
    assert!(error.contains("stage_restore.cpp:2"), "{error}");
    assert!(error.contains("without bit-fields"), "{error}");
    assert!(!project.artifact().exists());

    fs::write(
        project.source(),
        "struct Base { int base; };\nstruct RestoreState : Base { int saved; };\n\nint stage_restore(RestoreState& state, int& value) noexcept {\n    return state.saved;\n}\n",
    )
    .unwrap();
    let error = refresh_import(&project.config()).unwrap_err();
    assert!(error.contains("stage_restore.cpp:2"), "{error}");
    assert!(error.contains("have no bases"), "{error}");
    assert!(!project.artifact().exists());

    fs::write(
        project.source(),
        "struct First { int value; };\nstruct Second { int value; };\n\nint stage_restore(First& first, Second& second) noexcept {\n    first.value = second.value;\n    return first.value;\n}\n",
    )
    .unwrap();
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    assert_eq!(import.export().records.len(), 2);
    check_return_call_sidecar(
        &project,
        &import,
        r#"verifying "stage_restore.cpp";
int32 stage_restore(struct First* first, struct Second* second) {
 owns first->value; owns second->value;
 ensures result == old(second->value); ensures first->value == old(second->value);
} by { execute(); simp(); }
"#,
    );
}

#[test]
fn cpp_profile_expansion_and_audit_session_share_the_locked_input() {
    let project = Project::new();
    let sidecar = project.directory.join("demo.click");
    fs::write(&sidecar, SIDECAR).unwrap();
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let import = load_import(&project.config()).unwrap();
    let click_source = fs::read_to_string(&sidecar).unwrap();
    let click_project = read_click_project(&sidecar, &click_source).unwrap();

    let sites =
        program_prepared_project_smart_tactic_source_sites(&click_project, &import).unwrap();
    assert_eq!(
        sites
            .iter()
            .map(|site| site.tactic_name.as_str())
            .collect::<Vec<_>>(),
        vec!["execute", "simp"]
    );
    let execute = program_prepared_project_tactic_source_position(
        &click_project,
        &import,
        "increment.contract",
        0,
    )
    .unwrap();
    let expanded = expand_program_prepared_project_tactic_source_at(
        &click_project,
        &import,
        execute.line,
        execute.column,
    )
    .unwrap();
    assert_ne!(expanded, click_source);
    let rewritten = click_project.with_entry_source(expanded.clone());
    verify_program_prepared_project(&rewritten, &import).expect("expanded proof must reverify");

    let (session, _) = C0VerificationSession::new_program_prepared_project(&click_project, &import)
        .expect("start the retained audit session");
    let next = program_prepared_project_tactic_source_position(
        &rewritten,
        &import,
        "increment.contract",
        0,
    )
    .unwrap();
    session
        .verify_at_project(&expanded, next.line, next.column)
        .expect("retained session must verify the rewritten C++ proof");
}

#[test]
fn cpp_sidecar_reports_source_and_signature_mismatches_without_c_fallback() {
    let project = Project::new();
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let import = load_import(&project.config()).unwrap();

    let wrong_source = SIDECAR.replace("increment.cpp", "other.cpp");
    let sidecar = project.directory.join("demo.click");
    fs::write(&sidecar, &wrong_source).unwrap();
    let click_project = read_click_project(&sidecar, &wrong_source).unwrap();
    let error = verify_program_prepared_project(&click_project, &import).unwrap_err();
    assert!(
        error
            .message()
            .contains("prepared C++ import logical source must exactly match"),
        "{}",
        error.message()
    );

    let wrong_signature = SIDECAR.replace("int32* value", "uint32* value");
    fs::write(&sidecar, &wrong_signature).unwrap();
    let click_project = read_click_project(&sidecar, &wrong_signature).unwrap();
    let error = verify_program_prepared_project(&click_project, &import).unwrap_err();
    assert!(
        error
            .message()
            .contains("signature mismatch for `increment` parameter 1"),
        "{}",
        error.message()
    );
}

#[test]
fn locked_cpp_artifact_lowers_directly_and_executes_reference_semantics() {
    let project = Project::new();
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let prepared = load_import(&project.config()).expect("load the locked artifact offline");
    let declaration_id = prepared.export().function.declaration_id.clone();
    let function_span = prepared.export().function.span.clone();
    let lowered = lower_import(&prepared).expect("lower the typed artifact directly");

    assert_eq!(lowered.source().identity(), prepared.identity());
    assert_eq!(lowered.source_function().declaration_id, declaration_id);
    assert_eq!(lowered.source_function().span, function_span);
    let function = lowered.kernel_function();
    assert_eq!(function.name(), "increment");
    assert_eq!(function.return_type(), CType::Int32);
    assert_eq!(function.parameters().len(), 1);
    assert_eq!(function.parameters()[0].name(), "value");
    assert_eq!(function.parameters()[0].c_type(), CType::Int32Pointer);
    assert!(matches!(
        function.body(),
        CStatement::Seq(store, returned)
            if matches!(
                store.as_ref(),
                CStatement::TypedStore {
                    pointer: CExpression::Variable(pointer),
                    value: CExpression::Add(left, right),
                    value_type: CType::Int32,
                    volatile: false,
                    pointee_constant: false,
                } if pointer == "value"
                    && matches!(
                        left.as_ref(),
                        CExpression::TypedLoad {
                            pointer,
                            value_type: CType::Int32,
                            volatile: false,
                            ..
                        } if matches!(pointer.as_ref(), CExpression::Variable(name) if name == "value")
                    )
                    && matches!(right.as_ref(), CExpression::Value(value) if value == &int32(1))
            )
            && matches!(
                returned.as_ref(),
                CStatement::Return(CExpression::TypedLoad {
                    pointer,
                    value_type: CType::Int32,
                    volatile: false,
                    ..
                }) if matches!(pointer.as_ref(), CExpression::Variable(name) if name == "value")
            )
    ));

    let pointer = Pointer {
        block: "cpp-reference".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let resources =
        ResourceContext::new().unchecked_with_fact(CResourceFact::own_memory(CMemoryRange::new(
            pointer.clone(),
            Bitvector32Term::Constant(0),
            Bitvector32Term::Constant(1),
        )));
    let arguments = vec![c_typed_pointer_value(pointer.clone(), CType::Int32Pointer)];
    let state = CState::new()
        .with_memory(CMemory::new().store(pointer.clone(), int32(41)))
        .with_resource_context(resources.clone());
    let expected_state = CState::new()
        .with_memory(CMemory::new().store(pointer.clone(), int32(42)))
        .with_resource_context(resources.clone());
    let theorem = prove_symbolic_c_function_execution(
        state.clone(),
        function.clone(),
        arguments.clone(),
        PureFactContext::new(),
    )
    .expect("the lowered reference function should execute");
    assert_eq!(
        theorem.proposition(),
        &Proposition::CFunctionExecutes {
            state,
            function: function.clone(),
            arguments: arguments.clone(),
            outcome: CFunctionOutcome::Return {
                value: int32(42),
                state: expected_state,
            },
        }
    );

    let max_state = CState::new()
        .with_memory(CMemory::new().store(pointer, int32(i32::MAX as u32)))
        .with_resource_context(resources);
    let overflow = prove_symbolic_c_function_execution(
        max_state.clone(),
        function.clone(),
        arguments.clone(),
        PureFactContext::new(),
    )
    .expect("concrete signed overflow should produce a checked outcome");
    assert_eq!(
        overflow.proposition(),
        &Proposition::CFunctionExecutes {
            state: max_state,
            function: function.clone(),
            arguments,
            outcome: CFunctionOutcome::UndefinedBehavior(CUndefinedBehavior::SignedOverflow),
        }
    );
}

#[test]
fn locked_cpp_import_rejects_stale_source_config_and_artifact() {
    let project = Project::new();
    refresh_import(&project.config()).unwrap();

    fs::write(project.source(), SOURCE.replace("+ 1", "+ 2")).unwrap();
    let error = load_import(&project.config()).unwrap_err();
    assert!(error.contains("source differs"), "{error}");

    fs::write(project.source(), SOURCE).unwrap();
    project.write_config("other");
    let error = load_import(&project.config()).unwrap_err();
    assert!(error.contains("config"), "{error}");

    project.write_config("increment");
    let mut artifact = fs::read(project.artifact()).unwrap();
    artifact.push(b' ');
    fs::write(project.artifact(), artifact).unwrap();
    let error = load_import(&project.config()).unwrap_err();
    assert!(error.contains("artifact differs"), "{error}");
}

#[test]
fn cpp_frontend_rejects_unsupported_source_without_a_c_fallback() {
    let project = Project::new();
    fs::write(
        project.source(),
        "int increment(int& value) noexcept {\n    value *= 2;\n    return value;\n}\n",
    )
    .unwrap();
    let error = refresh_import(&project.config()).unwrap_err();
    assert!(error.contains("increment.cpp:2"), "{error}");
    assert!(error.contains("supports only simple assignment"), "{error}");
    assert!(!project.artifact().exists());

    fs::write(
        project.source(),
        "int increment(const int* value) noexcept {\n    return *value;\n}\n",
    )
    .unwrap();
    let error = refresh_import(&project.config()).unwrap_err();
    assert!(error.contains("mutable int* parameter"), "{error}");
    assert!(!project.artifact().exists());

    fs::write(
        project.source(),
        "struct Guard {\n    int& value;\n    explicit Guard(int& input) noexcept : value(input) {}\n    ~Guard() noexcept { value = 0; }\n};\n\nint increment(int& value) noexcept {\n    Guard guard(value);\n    return value;\n}\n",
    )
    .unwrap();
    let error = refresh_import(&project.config()).unwrap_err();
    assert!(error.contains("increment.cpp:1"), "{error}");
    assert!(
        error.contains("standard-layout and trivially-copyable"),
        "{error}"
    );
    assert!(!project.artifact().exists());

    fs::write(
        project.source(),
        "int increment(const int& value) noexcept {\n    value = 7;\n    return value;\n}\n",
    )
    .unwrap();
    let error = refresh_import(&project.config()).unwrap_err();
    assert!(error.contains("increment.cpp:2"), "{error}");
    assert!(error.contains("const-qualified"), "{error}");
    assert!(!project.artifact().exists());
}

#[test]
fn cpp_scalar_locals_reject_uninitialized_reference_and_nested_declarations() {
    let project = Project::scalar_local();
    fs::write(
        project.source(),
        "int relay_value(int& value) noexcept {\n    int captured;\n    return value;\n}\n",
    )
    .unwrap();
    let error = refresh_import(&project.config()).unwrap_err();
    assert!(error.contains("relay_value.cpp:2"), "{error}");
    assert!(error.contains("requires an initializer"), "{error}");
    assert!(!project.artifact().exists());

    fs::write(
        project.source(),
        "int relay_value(int& value) noexcept {\n    int& captured = value;\n    return captured;\n}\n",
    )
    .unwrap();
    let error = refresh_import(&project.config()).unwrap_err();
    assert!(error.contains("relay_value.cpp:2"), "{error}");
    assert!(
        error.contains("must resolve to mutable signed/unsigned 32/64-bit integer"),
        "{error}"
    );
    assert!(!project.artifact().exists());

    fs::write(
        project.source(),
        "int relay_value(bool choose, int& value) noexcept {\n    if (choose) {\n        int captured = value;\n        return captured;\n    }\n    return value;\n}\n",
    )
    .unwrap();
    let error = refresh_import(&project.config()).unwrap_err();
    assert!(error.contains("relay_value.cpp:3"), "{error}");
    assert!(
        error.contains("supported only in the function body"),
        "{error}"
    );
    assert!(!project.artifact().exists());
}

#[test]
fn cpp_direct_calls_reject_missing_throwing_and_recursive_definitions() {
    let project = Project::direct_call();
    fs::write(
        project.source(),
        "int set_seven(int& value) noexcept;\n\nint call_set_seven(int& value) noexcept {\n    set_seven(value);\n    return value;\n}\n",
    )
    .unwrap();
    let error = refresh_import(&project.config()).unwrap_err();
    assert!(error.contains("call_set_seven.cpp:4"), "{error}");
    assert!(
        error.contains("no reachable function definition"),
        "{error}"
    );
    assert!(!project.artifact().exists());

    fs::write(
        project.source(),
        "int set_seven(int& value) {\n    value = 7;\n    return value;\n}\n\nint call_set_seven(int& value) noexcept {\n    set_seven(value);\n    return value;\n}\n",
    )
    .unwrap();
    let error = refresh_import(&project.config()).unwrap_err();
    assert!(error.contains("call_set_seven.cpp:1"), "{error}");
    assert!(error.contains("must declare noexcept"), "{error}");
    assert!(!project.artifact().exists());

    fs::write(
        project.source(),
        "int call_set_seven(int& value) noexcept {\n    call_set_seven(value);\n    return value;\n}\n",
    )
    .unwrap();
    let error = refresh_import(&project.config()).unwrap_err();
    assert!(error.contains("recursive C++ calls"), "{error}");
    assert!(
        error.contains("call_set_seven -> call_set_seven"),
        "{error}"
    );
    assert!(!project.artifact().exists());
}

#[test]
fn cpp_config_rejects_profiles_outside_the_pinned_slice() {
    let project = Project::new();
    let bytes = fs::read_to_string(project.config()).unwrap();
    fs::write(project.config(), bytes.replace("c++20", "gnu++20")).unwrap();
    let error = refresh_import(&project.config()).unwrap_err();
    assert!(error.contains("Clang c++20"), "{error}");

    let mismatch = Project::new();
    mismatch.write_config_with_profile("increment", "increment.cpp", true);
    let error = refresh_import(&mismatch.config()).unwrap_err();
    assert!(
        error.contains("profile must match the configured"),
        "{error}"
    );
    assert!(!mismatch.artifact().exists());
}

#[test]
fn exporter_path_is_not_needed_by_offline_load() {
    let project = Project::new();
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    assert!(!Path::new(&project.exporter).exists());
    load_import(&project.config()).unwrap();
}

#[test]
fn ordinary_value_methods_import_with_const_receiver_and_mixed_width_fields() {
    let source = include_str!("fixtures/cpp-verification/value-methods/value_methods.cpp");
    for (selected, sidecar_source) in [
        (
            "FeeFrac::IsEmpty",
            include_str!("fixtures/cpp-verification/value-methods/is_empty.click"),
        ),
        (
            "FeeFrac::operator+=",
            include_str!("fixtures/cpp-verification/value-methods/add_disjoint.click"),
        ),
        (
            "double_size",
            include_str!("fixtures/cpp-verification/value-methods/add_self.click"),
        ),
        (
            "double_size_direct",
            include_str!("fixtures/cpp-verification/value-methods/add_self.click"),
        ),
    ] {
        let project = Project::with_fixture("value_methods.cpp", selected, source);
        refresh_import(&project.config()).expect("export the selected value method graph");
        let import = load_import(&project.config()).unwrap();
        assert_eq!(import.export().records[0].fields[0].size_bytes, 8);
        assert_eq!(import.export().records[0].fields[1].size_bytes, 4);
        lower_import(&import).expect("lower the value method graph");
        let sidecar_source = if selected == "double_size_direct" {
            sidecar_source.replace("double_size(", "double_size_direct(")
        } else {
            sidecar_source.to_owned()
        };
        let sidecar = project.directory.join("demo.click");
        fs::write(&sidecar, &sidecar_source).unwrap();
        let parsed = read_click_project(&sidecar, &sidecar_source).unwrap();
        verify_program_prepared_project(&parsed, &import)
            .unwrap_or_else(|error| panic!("{selected}: {}", error.message()));
        let sites = program_prepared_project_smart_tactic_source_sites(&parsed, &import).unwrap();
        let site = sites.first().unwrap();
        let site = program_prepared_project_tactic_source_position(
            &parsed,
            &import,
            &site.claim_label,
            site.source_index,
        )
        .unwrap();
        let expanded = expand_program_prepared_project_tactic_source_at(
            &parsed,
            &import,
            site.line,
            site.column,
        )
        .unwrap();
        let rewritten = parsed.with_entry_source(expanded.clone());
        verify_program_prepared_project(&rewritten, &import)
            .expect("expanded method proof reverifies");
        let (session, _) =
            C0VerificationSession::new_program_prepared_project(&parsed, &import).unwrap();
        let next_sites =
            program_prepared_project_smart_tactic_source_sites(&rewritten, &import).unwrap();
        let next = next_sites.first().unwrap();
        let next = program_prepared_project_tactic_source_position(
            &rewritten,
            &import,
            &next.claim_label,
            next.source_index,
        )
        .unwrap();
        session
            .verify_at_project(&expanded, next.line, next.column)
            .expect("audit session checks the expanded method proof");
    }
}

#[test]
fn value_methods_reject_false_claims_missing_authority_and_overflow() {
    let source = include_str!("fixtures/cpp-verification/value-methods/value_methods.cpp");
    let add = include_str!("fixtures/cpp-verification/value-methods/add_disjoint.click");
    let empty = include_str!("fixtures/cpp-verification/value-methods/is_empty.click");
    for (selector, proof, expected) in [
        ("FeeFrac::IsEmpty", empty.replace("if old(self->size) == 0", "if old(self->size) == 1"), "unclosed goal"),
        ("FeeFrac::operator+=", add.replace("ensures self->fee == old(self->fee) + old(other->fee);", "ensures self->fee == old(self->fee);"), "unclosed goal"),
        ("FeeFrac::operator+=", add.replace("    owns self->fee;\n", ""), "missing resource fact"),
        ("FeeFrac::operator+=", add.replace("    requires -4611686018427387904 <= self->fee;\n    requires self->fee <= 4611686018427387903;\n", ""), "overflow"),
        ("FeeFrac::operator+=", add.replace("    requires -1073741824 <= self->size;\n    requires self->size <= 1073741823;\n", ""), "overflow"),
    ] {
        let project = Project::with_fixture("value_methods.cpp", selector, source);
        refresh_import(&project.config()).unwrap();
        let import = load_import(&project.config()).unwrap();
        let sidecar = project.directory.join("demo.click");
        fs::write(&sidecar, &proof).unwrap();
        let parsed = read_click_project(&sidecar, &proof).unwrap();
        let error = verify_program_prepared_project(&parsed, &import).unwrap_err();
        assert!(error.message().contains(expected), "{selector}: {}", error.message());
    }
}

const SIGNED_ARITHMETIC_SOURCE: &str =
    include_str!("fixtures/cpp-verification/signed-arithmetic/arithmetic.cpp");

fn check_arithmetic_sidecar(
    project: &Project,
    import: &click::languages::cpp::PreparedCppImport,
    source: &str,
) {
    check_sidecar_tactic(project, import, source, None);
}

fn check_return_call_sidecar(
    project: &Project,
    import: &click::languages::cpp::PreparedCppImport,
    source: &str,
) {
    let prefix = format!("{}.", import.export().function.name);
    check_sidecar_tactic(project, import, source, Some(&prefix));
}

fn check_sidecar_tactic(
    project: &Project,
    import: &click::languages::cpp::PreparedCppImport,
    source: &str,
    claim_prefix: Option<&str>,
) {
    let sidecar = project.directory.join("arithmetic.click");
    let source = source.replace(
        "-9223372036854775808i64",
        "(-9223372036854775807i64 - 1i64)",
    );
    fs::write(&sidecar, &source).unwrap();
    let parsed = read_click_project(&sidecar, &source).unwrap();
    verify_program_prepared_project(&parsed, import)
        .unwrap_or_else(|error| panic!("{}\n{source}", error.message()));
    let sites = program_prepared_project_smart_tactic_source_sites(&parsed, import).unwrap();
    let first = match claim_prefix {
        Some(prefix) => sites
            .iter()
            .find(|site| site.claim_label.starts_with(prefix))
            .expect("selected caller tactic"),
        None => sites.first().unwrap(),
    };
    let position = program_prepared_project_tactic_source_position(
        &parsed,
        import,
        &first.claim_label,
        first.source_index,
    )
    .unwrap();
    let expanded = expand_program_prepared_project_tactic_source_at(
        &parsed,
        import,
        position.line,
        position.column,
    )
    .unwrap();
    let rewritten = parsed.with_entry_source(expanded.clone());
    verify_program_prepared_project(&rewritten, import)
        .expect("expanded arithmetic certificate reverifies");
    let (session, _) =
        C0VerificationSession::new_program_prepared_project(&parsed, import).unwrap();
    let sites = program_prepared_project_smart_tactic_source_sites(&rewritten, import).unwrap();
    let first = match claim_prefix {
        Some(prefix) => sites
            .iter()
            .find(|site| site.claim_label.starts_with(prefix))
            .expect("selected caller tactic"),
        None => sites.first().unwrap(),
    };
    let position = program_prepared_project_tactic_source_position(
        &rewritten,
        import,
        &first.claim_label,
        first.source_index,
    )
    .unwrap();
    session
        .verify_at_project(&expanded, position.line, position.column)
        .expect("retained audit accepts arithmetic certificate");
}

#[test]
fn signed_scalar_arithmetic_verifies_through_the_shared_kernel_and_modular_calls() {
    for (selector, source) in [
        (
            "quotient",
            include_str!("fixtures/cpp-verification/signed-arithmetic/quotient.click"),
        ),
        (
            "remainder",
            include_str!("fixtures/cpp-verification/signed-arithmetic/remainder.click"),
        ),
        (
            "multiply",
            include_str!("fixtures/cpp-verification/signed-arithmetic/multiply.click"),
        ),
        (
            "relay",
            include_str!("fixtures/cpp-verification/signed-arithmetic/relay.click"),
        ),
    ] {
        let project = Project::with_fixture("arithmetic.cpp", selector, SIGNED_ARITHMETIC_SOURCE);
        refresh_import(&project.config()).unwrap();
        let import = load_import(&project.config()).unwrap();
        lower_import(&import).unwrap();
        check_arithmetic_sidecar(&project, &import, source);
    }
}

#[test]
fn signed_division_correction_covers_rounding_directions_and_boundary_cases() {
    let project =
        Project::with_fixture("arithmetic.cpp", "rounded_divide", SIGNED_ARITHMETIC_SOURCE);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    for (n, d, down, result) in [
        (7i64, 3, true, 2i64),
        (7, 3, false, 3),
        (-7, 3, true, -3),
        (-7, 3, false, -2),
        (6, 3, true, 2),
        (6, 3, false, 2),
        (-6, 3, true, -2),
        (-6, 3, false, -2),
        (0, 1, true, 0),
        (0, 1, false, 0),
        (i64::MAX, 1, false, i64::MAX),
        (i64::MIN, 1, true, i64::MIN),
        (i64::MAX, i32::MAX, false, 4294967299),
        (i64::MIN, i32::MAX, true, -4294967299),
    ] {
        let source = format!(
            "verifying \"arithmetic.cpp\";\nint64 rounded_divide(int64 n, int32 d, bool round_down) {{\nrequires n == {n}i64;\nrequires d == {d};\nrequires round_down == {};\nensures result == {result}i64;\n}} by {{ execute(); simp(); }}\n",
            i32::from(down)
        );
        check_arithmetic_sidecar(&project, &import, &source);
    }
}

#[test]
fn signed_scalar_arithmetic_rejects_undefined_operations_and_false_claims() {
    for (selector, parameters, preconditions, claim, expected) in [
        (
            "quotient",
            "int64 n, int64 d",
            "requires n == 7i64; requires d == 3i64;",
            "result == 3i64",
            "unclosed goal",
        ),
        (
            "rounded_divide",
            "int64 n, int32 d, bool round_down",
            "requires n == -7i64; requires d == 3; requires round_down == 1;",
            "result == -2i64",
            "unclosed goal",
        ),
        (
            "quotient",
            "int64 n, int64 d",
            "requires d == 0i64;",
            "result == 0i64",
            "division by zero",
        ),
        (
            "remainder",
            "int64 n, int64 d",
            "requires d == 0i64;",
            "result == 0i64",
            "division by zero",
        ),
        (
            "quotient",
            "int64 n, int64 d",
            "requires n == -9223372036854775808i64; requires d == -1i64;",
            "result == 0i64",
            "overflow",
        ),
        (
            "remainder",
            "int64 n, int64 d",
            "requires n == -9223372036854775808i64; requires d == -1i64;",
            "result == 0i64",
            "overflow",
        ),
        (
            "multiply",
            "int64 a, int64 b",
            "requires a == 2i64;",
            "result == a * b",
            "overflow",
        ),
        (
            "negate",
            "int64 n",
            "requires n == -9223372036854775808i64;",
            "result == 0i64",
            "overflow",
        ),
    ] {
        let project = Project::with_fixture("arithmetic.cpp", selector, SIGNED_ARITHMETIC_SOURCE);
        refresh_import(&project.config()).unwrap();
        let import = load_import(&project.config()).unwrap();
        let source = format!(
            "verifying \"arithmetic.cpp\";\nint64 {selector}({parameters}) {{ {preconditions} ensures {claim}; }} by {{ execute(); simp(); }}\n"
        );
        let source = source.replace(
            "-9223372036854775808i64",
            "(-9223372036854775807i64 - 1i64)",
        );
        fs::write(project.directory.join("arithmetic.click"), &source).unwrap();
        let parsed =
            read_click_project(&project.directory.join("arithmetic.click"), &source).unwrap();
        let error = verify_program_prepared_project(&parsed, &import).unwrap_err();
        assert!(
            error.message().contains(expected),
            "{selector}: {}",
            error.message()
        );
    }
}

#[test]
fn signed_scalar_casts_preserve_cpp20_boolean_and_narrowing_semantics() {
    for (selector, cpp_source, parameters, preconditions, result_type, expected) in [
        (
            "narrow",
            SIGNED_ARITHMETIC_SOURCE,
            "int64 n",
            "requires n == 4294967297i64;",
            "int32",
            "1",
        ),
        (
            "narrow",
            SIGNED_ARITHMETIC_SOURCE,
            "int64 n",
            "requires n == 2147483648i64;",
            "int32",
            "-2147483648",
        ),
        (
            "truth",
            "bool truth(long n) noexcept { return bool(n); }",
            "int64 n",
            "requires n == 4294967296i64;",
            "bool",
            "1",
        ),
        (
            "truth",
            "bool truth(long n) noexcept { return bool(n); }",
            "int64 n",
            "requires n == 0i64;",
            "bool",
            "0",
        ),
        (
            "negate",
            SIGNED_ARITHMETIC_SOURCE,
            "int64 n",
            "requires n == 9223372036854775807i64;",
            "int64",
            "-9223372036854775807i64",
        ),
    ] {
        let project = Project::with_fixture("arithmetic.cpp", selector, cpp_source);
        refresh_import(&project.config()).unwrap();
        let import = load_import(&project.config()).unwrap();
        let source = format!(
            "verifying \"arithmetic.cpp\";\n{result_type} {selector}({parameters}) {{ {preconditions} ensures result == {expected}; }} by {{ execute(); simp(); }}\n"
        );
        check_arithmetic_sidecar(&project, &import, &source);
    }
    let project = Project::with_fixture(
        "arithmetic.cpp",
        "relay",
        "long quotient(long n, long d) noexcept { return n / d; }\nlong relay(long n, long d, int& untouched) noexcept { int captured = quotient(n, d); return captured; }",
    );
    let error = refresh_import(&project.config()).unwrap_err();
    assert!(error.contains("call capture requires matching"), "{error}");
}

#[test]
fn subtraction_method_self_aliasing_is_defined_without_bounds_and_frames_caller_memory() {
    let project = Project::with_fixture(
        "subtract_methods.cpp",
        "clear_value",
        include_str!("fixtures/cpp-verification/subtract-methods/subtract_methods.cpp"),
    );
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let proof = include_str!("fixtures/cpp-verification/subtract-methods/clear_value.click");
    check_arithmetic_sidecar(&project, &import, proof);
    for (source, expected) in [
        (
            proof.replace("ensures self->fee == 0i64", "ensures self->fee == 1i64"),
            "unclosed goal",
        ),
        (
            proof.replace("    owns self->fee;\n", ""),
            "missing resource fact",
        ),
    ] {
        fs::write(project.directory.join("arithmetic.click"), &source).unwrap();
        let parsed =
            read_click_project(&project.directory.join("arithmetic.click"), &source).unwrap();
        let error = verify_program_prepared_project(&parsed, &import).unwrap_err();
        assert!(error.message().contains(expected), "{}", error.message());
    }
}

#[test]
fn arithmetic_profile_rejects_narrow_and_wide_integer_semantics() {
    for source in [
        "__int128 wide(__int128 n) noexcept { return n / 3; }",
        "unsigned short wide(unsigned short n) noexcept { return n / 3; }",
    ] {
        let project = Project::with_fixture("arithmetic.cpp", "wide", source);
        let error = refresh_import(&project.config()).unwrap_err();
        assert!(
            error.contains("signed/unsigned 32/64-bit integers"),
            "{error}"
        );
        assert!(!project.artifact().exists());
    }
}

#[test]
fn signed_scalar_return_and_parameters_retain_locked_header_aliases() {
    let mut project = Project::with_fixture(
        "arithmetic.cpp",
        "quotient",
        "#include <cstdint>\nint64_t quotient(int64_t n, int64_t d) noexcept { return n / d; }",
    );
    fs::write(
        project.directory.join("cstdint"),
        CONSTEXPR_MAX_MONEY_CSTDINT,
    )
    .unwrap();
    project.dependencies.push("cstdint".into());
    project.write_exception_enabled_compilation_database_with_local_include();
    project.write_config_with_profile("quotient", "arithmetic.cpp", true);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let CppType::Integer { source_aliases, .. } = &import.export().function.return_type else {
        panic!("missing signed return type")
    };
    assert_eq!(source_aliases[0].name, "int64_t");
    assert_eq!(source_aliases[0].span.file, "cstdint");
    check_arithmetic_sidecar(
        &project,
        &import,
        include_str!("fixtures/cpp-verification/signed-arithmetic/quotient.click"),
    );
}

const UNSIGNED_ARITHMETIC_SOURCE: &str =
    include_str!("fixtures/cpp-verification/unsigned-arithmetic/arithmetic.cpp");

#[test]
fn unsigned_scalar_operations_wrap_and_preserve_conversion_semantics() {
    for (name, params, requires, result_type, expected) in [
        ("maximum", "", "", "uint64", "18446744073709551615u64"),
        (
            "mixed",
            "int64 a, uint32 b",
            "requires a == -1i64; requires b == 1u32;",
            "uint64",
            "0u64",
        ),
        (
            "mixed",
            "int64 a, uint32 b",
            "requires a == -1i64; requires b == 1u32;",
            "uint64",
            "0u64",
        ),
        (
            "add64",
            "uint64 a, uint64 b",
            "requires a == 18446744073709551615u64; requires b == 1u64;",
            "uint64",
            "0u64",
        ),
        (
            "sub64",
            "uint64 a, uint64 b",
            "requires a == 0u64; requires b == 1u64;",
            "uint64",
            "18446744073709551615u64",
        ),
        (
            "mul64",
            "uint64 a, uint64 b",
            "requires a == 9223372036854775808u64; requires b == 2u64;",
            "uint64",
            "0u64",
        ),
        (
            "div64",
            "uint64 a, uint64 b",
            "requires a == 18446744073709551615u64; requires b == 2u64;",
            "uint64",
            "9223372036854775807u64",
        ),
        (
            "rem64",
            "uint64 a, uint64 b",
            "requires a == 18446744073709551615u64; requires b == 2u64;",
            "uint64",
            "1u64",
        ),
        (
            "neg64",
            "uint64 a",
            "requires a == 1u64;",
            "uint64",
            "18446744073709551615u64",
        ),
        (
            "add32",
            "uint32 a, uint32 b",
            "requires a == 4294967295u32; requires b == 1u32;",
            "uint32",
            "0u32",
        ),
        (
            "signed_to_unsigned",
            "int32 a",
            "requires a == -1;",
            "uint64",
            "18446744073709551615u64",
        ),
        (
            "narrow_unsigned",
            "int64 a",
            "requires a == -1i64;",
            "uint32",
            "4294967295u32",
        ),
        (
            "narrow_signed",
            "uint64 a",
            "requires a == 18446744073709551615u64;",
            "int32",
            "-1",
        ),
        (
            "widen_unsigned",
            "uint32 a",
            "requires a == 4294967295u32;",
            "int64",
            "4294967295i64",
        ),
        (
            "truth",
            "uint64 a",
            "requires a == 4294967296u64;",
            "bool",
            "1",
        ),
    ] {
        let project = Project::with_fixture("unsigned.cpp", name, UNSIGNED_ARITHMETIC_SOURCE);
        refresh_import(&project.config()).unwrap();
        let import = load_import(&project.config()).unwrap();
        let source = format!(
            "verifying \"unsigned.cpp\";\n{result_type} {name}({params}) {{ {requires} ensures result == {expected}; }} by {{ execute(); simp(); }}"
        );
        check_arithmetic_sidecar(&project, &import, &source);
    }
}

#[test]
fn unsigned_modular_calls_frame_unrelated_memory_and_reject_false_wrap_claims() {
    let project = Project::with_fixture("unsigned.cpp", "relay", UNSIGNED_ARITHMETIC_SOURCE);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let source = r#"verifying "unsigned.cpp";
uint64 add64(uint64 a, uint64 b) { ensures result == a + b; } by { execute(); simp(); }
uint64 relay(uint64 a, uint64 b, int32* untouched) {
 owns untouched[0..1];
 ensures result == a + b;
 ensures untouched[0] == old(untouched[0]);
} by { execute(); simp(); }
"#;
    check_arithmetic_sidecar(&project, &import, source);
    let project = Project::with_fixture("unsigned.cpp", "add64", UNSIGNED_ARITHMETIC_SOURCE);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let source = r#"verifying "unsigned.cpp";
uint64 add64(uint64 a, uint64 b) {
 requires a == 18446744073709551615u64; requires b == 1u64;
 ensures result == 1u64;
} by { execute(); simp(); }
"#;
    fs::write(project.directory.join("bad.click"), source).unwrap();
    let parsed = read_click_project(&project.directory.join("bad.click"), source).unwrap();
    let error = verify_program_prepared_project(&parsed, &import).unwrap_err();
    assert!(
        error.message().contains("unclosed goal"),
        "{}",
        error.message()
    );
}

#[test]
fn unsigned_division_rejects_zero() {
    for name in ["div64", "rem64"] {
        let project = Project::with_fixture("unsigned.cpp", name, UNSIGNED_ARITHMETIC_SOURCE);
        refresh_import(&project.config()).unwrap();
        let import = load_import(&project.config()).unwrap();
        let source = format!(
            "verifying \"unsigned.cpp\"; uint64 {name}(uint64 a, uint64 b) {{ requires b == 0u64; ensures result == 0u64; }} by {{ execute(); simp(); }}"
        );
        fs::write(project.directory.join("bad.click"), &source).unwrap();
        let parsed = read_click_project(&project.directory.join("bad.click"), &source).unwrap();
        let error = verify_program_prepared_project(&parsed, &import).unwrap_err();
        assert!(
            error.message().contains("division by zero"),
            "{}",
            error.message()
        );
    }
}

#[test]
fn compiler_constants_retain_their_origin_and_reject_runtime_calls() {
    let project = Project::with_fixture(
        "constants.cpp",
        "size",
        "unsigned int size() noexcept { return sizeof(unsigned long) + sizeof(unsigned short); }",
    );
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    assert!(
        fs::read_to_string(project.artifact())
            .unwrap()
            .contains("compiler_constant")
    );
    check_arithmetic_sidecar(
        &project,
        &import,
        "verifying \"constants.cpp\"; uint32 size() { ensures result == 10u32; } by { execute(); simp(); }",
    );
    let project = Project::with_fixture(
        "constants.cpp",
        "size",
        "unsigned long runtime() noexcept; unsigned long size() noexcept { return runtime(); }",
    );
    assert!(refresh_import(&project.config()).is_err());
    assert!(!project.artifact().exists());
}

#[test]
fn unsigned_positive_divisor_contract_expands_and_reverifies() {
    let project = Project::with_fixture("unsigned.cpp", "div64", UNSIGNED_ARITHMETIC_SOURCE);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    check_arithmetic_sidecar(
        &project,
        &import,
        "verifying \"unsigned.cpp\"; uint64 div64(uint64 a, uint64 b) { requires b > 0u64; ensures result == a / b; } by { execute(); simp(); }",
    );
}

#[test]
fn unsigned_fee_fast_path_expressions_cover_large_products_and_rounding() {
    // Exact fast-path expressions from EvaluateFee; return the unsigned
    // intermediate; signed-result conversion is covered by signed-conversion fixtures.
    let cpp = include_str!("fixtures/cpp-verification/unsigned-arithmetic/fee_fast_path.cpp");
    for (name, up) in [("down", false), ("up", true)] {
        let project = Project::with_fixture("fast_path.cpp", name, cpp);
        refresh_import(&project.config()).unwrap();
        let import = load_import(&project.config()).unwrap();
        for (fee, at_size, size) in [
            (0i64, 0i32, 1i32),
            (7, 3, 5),
            (8, 3, 6),
            (8589934591, 2147483647, 2147483647),
        ] {
            let numerator = fee as u64 * at_size as u64;
            let expected = if up {
                numerator.div_ceil(size as u64)
            } else {
                numerator / size as u64
            };
            let proof = format!(
                "verifying \"fast_path.cpp\"; uint64 {name}(int64 fee, int32 at_size, int32 size) {{ requires fee == {fee}i64; requires at_size == {at_size}; requires size == {size}; ensures result == {expected}u64; }} by {{ execute(); simp(); }}"
            );
            check_arithmetic_sidecar(&project, &import, &proof);
        }
    }
}

#[test]
fn mixed_unsigned_return_preserves_signed_intermediate_overflow() {
    let project = Project::with_fixture("unsigned.cpp", "mixed", UNSIGNED_ARITHMETIC_SOURCE);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let source = "verifying \"unsigned.cpp\"; uint64 mixed(int64 a, uint32 b) { requires a == 9223372036854775807i64; requires b == 4294967295u32; ensures result == 0u64; } by { execute(); simp(); }";
    fs::write(project.directory.join("bad.click"), source).unwrap();
    let parsed = read_click_project(&project.directory.join("bad.click"), source).unwrap();
    let error = verify_program_prepared_project(&parsed, &import).unwrap_err();
    assert!(error.message().contains("overflow"), "{}", error.message());
}

#[test]
fn compiler_constant_calls_preserve_runtime_constant_evaluation_context() {
    // A constexpr function can distinguish constant evaluation from a runtime
    // call. The exporter must fold the latter meaning in an imported body.
    let cpp = "namespace std { template<class T> struct numeric_limits { static constexpr unsigned long max() noexcept { return __builtin_is_constant_evaluated() ? 1UL : 2UL; } }; } unsigned long probe() noexcept { return std::numeric_limits<unsigned long>::max(); }";
    let project = Project::with_fixture("constant_context.cpp", "probe", cpp);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    check_arithmetic_sidecar(
        &project,
        &import,
        "verifying \"constant_context.cpp\"; uint64 probe() { ensures result == 2u64; } by { execute(); simp(); }",
    );
    let bad = "verifying \"constant_context.cpp\"; uint64 probe() { ensures result == 1u64; } by { execute(); simp(); }";
    fs::write(project.directory.join("bad.click"), bad).unwrap();
    let parsed = read_click_project(&project.directory.join("bad.click"), bad).unwrap();
    assert!(verify_program_prepared_project(&parsed, &import).is_err());
}

const TEMPLATE_INSTANCE_SOURCE: &str =
    include_str!("fixtures/cpp-verification/template-instances/instances.cpp");

#[test]
fn concrete_template_instances_have_distinct_identities_and_modular_contracts() {
    let project = Project::with_fixture("instances.cpp", "both", TEMPLATE_INSTANCE_SOURCE);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let helpers = &import.export().reachable_functions;
    assert_eq!(helpers.len(), 2);
    assert_ne!(helpers[0].declaration_id, helpers[1].declaration_id);
    assert_eq!(helpers[0].name, "choose__bool_true");
    assert_eq!(helpers[1].name, "choose__bool_false");
    for (helper, chosen_then) in [(&helpers[0], true), (&helpers[1], false)] {
        let CppStatement::If {
            condition,
            then_branch,
            else_branch,
            span,
        } = &helper.body[0]
        else {
            panic!("constexpr selection must retain its conditional span");
        };
        assert_eq!(span.file, "instances.cpp");
        assert_eq!(span.start_line, 4);
        assert_eq!(then_branch.is_empty(), !chosen_then);
        assert_eq!(else_branch.is_empty(), chosen_then);
        let CppExpression::IntegralCast { value, .. } = condition else {
            panic!("typed Boolean selection")
        };
        assert!(matches!(
            value.as_ref(),
            CppExpression::CompilerConstant { .. }
        ));
    }
    let sidecar = r#"verifying "instances.cpp";
int32 choose__bool_true(int32 a, int32 b) {
 requires a >= -1073741824; requires a <= 1073741823;
 ensures result == a; ensures result >= -1073741824; ensures result <= 1073741823;
} by { execute(); simp(); }
int32 choose__bool_false(int32 a, int32 b) {
 requires b >= -1073741824; requires b <= 1073741823;
 ensures result == b; ensures result >= -1073741824; ensures result <= 1073741823;
} by { execute(); simp(); }
int32 both(int32 a, int32 b, int32* untouched) {
 requires a >= -1073741824; requires a <= 1073741823;
 requires b >= -1073741824; requires b <= 1073741823;
 owns untouched[0..1];
 ensures result == a + b;
 ensures untouched[0] == old(untouched[0]);
} by { execute(); simp(); }
"#;
    check_arithmetic_sidecar(&project, &import, sidecar);
    let hostile = sidecar.replace("ensures result == b;", "ensures result == a;");
    fs::write(project.directory.join("bad.click"), &hostile).unwrap();
    let parsed = read_click_project(&project.directory.join("bad.click"), &hostile).unwrap();
    assert!(verify_program_prepared_project(&parsed, &import).is_err());
}

#[test]
fn concrete_scalar_type_template_instances_preserve_width_and_signedness() {
    let project = Project::with_fixture("instances.cpp", "widths", TEMPLATE_INSTANCE_SOURCE);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    assert_eq!(import.export().reachable_functions[0].name, "identity__int");
    assert_eq!(
        import.export().reachable_functions[1].name,
        "identity__unsigned_long"
    );
    let sidecar = r#"verifying "instances.cpp";
int32 identity__int(int32 value) { ensures result == value; } by { execute(); simp(); }
uint64 identity__unsigned_long(uint64 value) { ensures result == value; } by { execute(); simp(); }
uint64 widths(int32 a, uint64 b) {
 requires a == 1; requires b == 18446744073709551615u64;
 ensures result == 0u64;
} by { execute(); simp(); }
"#;
    check_arithmetic_sidecar(&project, &import, sidecar);
}

#[test]
fn concrete_member_template_instances_preserve_receiver_authority() {
    let project = Project::with_fixture("instances.cpp", "member", TEMPLATE_INSTANCE_SOURCE);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let sidecar = r#"verifying "instances.cpp";
int64 Value_select__bool_true(const struct Value* self) {
 views self->fee;
 ensures result == self->fee;
 ensures self->fee == old(self->fee);
} by { execute(); simp(); }
int64 Value_select__bool_false(const struct Value* self) {
 views self->fee;
 ensures result == 0i64;
 ensures self->fee == old(self->fee);
} by { execute(); simp(); }
int64 member(const struct Value* value) {
 owns value->fee;
 ensures result == value->fee;
 ensures value->fee == old(value->fee);
} by { execute(); simp(); }
"#;
    check_arithmetic_sidecar(&project, &import, sidecar);
    let hostile = sidecar.replace(" owns value->fee;", "");
    fs::write(project.directory.join("bad.click"), &hostile).unwrap();
    let parsed = read_click_project(&project.directory.join("bad.click"), &hostile).unwrap();
    assert!(verify_program_prepared_project(&parsed, &import).is_err());
}

#[test]
fn constexpr_discards_only_the_compiler_selected_arm() {
    let project = Project::with_fixture("instances.cpp", "accepted", TEMPLATE_INSTANCE_SOURCE);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    assert_eq!(import.export().reachable_functions.len(), 1);
    let sidecar = r#"verifying "instances.cpp";
int32 bounded__bool_true(int32 value) { ensures result == value; } by { execute(); simp(); }
int32 accepted(int32 value) { ensures result == value; } by { execute(); simp(); }
"#;
    check_arithmetic_sidecar(&project, &import, sidecar);
    let rejected = Project::with_fixture("instances.cpp", "rejected", TEMPLATE_INSTANCE_SOURCE);
    let error = refresh_import(&rejected.config()).unwrap_err();
    assert!(
        error.contains("unsupported") || error.contains("reachable"),
        "{error}"
    );
    assert!(!rejected.artifact().exists());
}

#[test]
fn template_type_identity_does_not_merge_equal_width_cpp_types() {
    let project = Project::with_fixture("instances.cpp", "exact_types", TEMPLATE_INSTANCE_SOURCE);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let helpers = &import.export().reachable_functions;
    assert_eq!(helpers[0].name, "identity__unsigned_long");
    assert_eq!(helpers[1].name, "identity__unsigned_long_long");
    assert_ne!(helpers[0].declaration_id, helpers[1].declaration_id);
    let source = r#"verifying "instances.cpp";
uint64 identity__unsigned_long(uint64 value) { ensures result == value; } by { execute(); simp(); }
uint64 identity__unsigned_long_long(uint64 value) { ensures result == value; } by { execute(); simp(); }
uint64 exact_types(uint64 a, uint64 b) { ensures result == a + b; } by { execute(); simp(); }
"#;
    check_arithmetic_sidecar(&project, &import, source);
}

#[test]
fn constexpr_conditions_use_constant_context_and_allow_absent_else() {
    for (selected, params, expected) in [
        ("constant_context", "", "1"),
        ("discarded_without_else", "int32 value", "value"),
    ] {
        let project = Project::with_fixture("instances.cpp", selected, TEMPLATE_INSTANCE_SOURCE);
        refresh_import(&project.config()).unwrap();
        let import = load_import(&project.config()).unwrap();
        assert!(import.export().reachable_functions.is_empty());
        let source = format!(
            "verifying \"instances.cpp\"; int32 {selected}({params}) {{ ensures result == {expected}; }} by {{ execute(); simp(); }}"
        );
        check_arithmetic_sidecar(&project, &import, &source);
    }
    let project = Project::with_fixture("instances.cpp", "runtime_if", TEMPLATE_INSTANCE_SOURCE);
    let error = refresh_import(&project.config()).unwrap_err();
    assert!(
        error.contains("no reachable function definition"),
        "{error}"
    );
    assert!(!project.artifact().exists());
}

#[test]
fn substituted_boolean_template_arguments_are_typed_values() {
    let project = Project::with_fixture("instances.cpp", "get_flag", TEMPLATE_INSTANCE_SOURCE);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let source = r#"verifying "instances.cpp";
int32 flag__bool_true() { ensures result == 1; } by { execute(); simp(); }
int32 get_flag() { ensures result == 1; } by { execute(); simp(); }
"#;
    check_arithmetic_sidecar(&project, &import, source);
}

#[test]
fn unsupported_template_arguments_and_dependent_selection_fail_explicitly() {
    for (selected, source, diagnostic) in [
        (
            "call",
            "template<int N> int f(int value) noexcept { return value; } int call(int value) noexcept { int result = f<1>(value); return result; }",
            "template arguments require Boolean",
        ),
        (
            "call",
            "template<class T> int f(int value) noexcept { return value; } int call(int value) noexcept { int result = f<int*>(value); return result; }",
            "template type arguments require",
        ),
        (
            "call",
            "template<class... T> int f(int value) noexcept { return value; } int call(int value) noexcept { int result = f<int>(value); return result; }",
            "template arguments require Boolean",
        ),
        (
            "f",
            "template<bool B> int f(int value) noexcept { return value; }",
            "dependent template pattern",
        ),
    ] {
        let project = Project::with_fixture("unsupported.cpp", selected, source);
        let error = refresh_import(&project.config()).unwrap_err();
        assert!(error.contains(diagnostic), "{error}");
        assert!(!project.artifact().exists());
    }
}

#[test]
fn instantiated_fee_fast_paths_preserve_both_rounding_expressions() {
    for (fee, at_size, size) in [
        (0u64, 1u64, 3u64),
        (7, 2, 3),
        (8, 2, 4),
        (8589934591, 2147483647, 2147483647),
    ] {
        for (selected, instance, expected) in [
            ("fee_down", "fee_fast_path__bool_true", fee * at_size / size),
            (
                "fee_up",
                "fee_fast_path__bool_false",
                (fee * at_size).div_ceil(size),
            ),
        ] {
            let project =
                Project::with_fixture("instances.cpp", selected, TEMPLATE_INSTANCE_SOURCE);
            refresh_import(&project.config()).unwrap();
            let import = load_import(&project.config()).unwrap();
            let contract = format!(
                "requires fee == {fee}i64; requires at_size == {at_size}; requires size == {size}; ensures result == {expected}u64;"
            );
            let source = format!(
                "verifying \"instances.cpp\"; uint64 {instance}(int64 fee, int32 at_size, int32 size) {{ {contract} }} by {{ execute(); simp(); }} uint64 {selected}(int64 fee, int32 at_size, int32 size) {{ {contract} }} by {{ execute(); simp(); }}"
            );
            check_arithmetic_sidecar(&project, &import, &source);
            let hostile = source.replace(
                &format!("result == {expected}u64"),
                &format!("result == {}u64", expected + 1),
            );
            fs::write(project.directory.join("bad.click"), &hostile).unwrap();
            let parsed =
                read_click_project(&project.directory.join("bad.click"), &hostile).unwrap();
            assert!(verify_program_prepared_project(&parsed, &import).is_err());
        }
    }
}

#[test]
fn class_template_instances_remain_explicitly_unsupported() {
    let source = "template<class T> struct Box { int value; }; int call(const Box<int>& box) noexcept { return box.value; }";
    let project = Project::with_fixture("unsupported.cpp", "call", source);
    let error = refresh_import(&project.config()).unwrap_err();
    assert!(
        error.contains("class template instances are unsupported"),
        "{error}"
    );
    assert!(!project.artifact().exists());
}

const SIGNED_CONVERSION_SOURCE: &str =
    include_str!("fixtures/cpp-verification/signed-conversion/conversion.cpp");

#[test]
fn cpp20_unsigned_to_signed64_preserves_all_bits_at_boundaries() {
    for value in [
        0u64,
        1,
        i32::MAX as u64,
        u32::MAX as u64,
        i64::MAX as u64,
        1u64 << 63,
        (1u64 << 63) + 1,
        u64::MAX,
    ] {
        for selected in ["explicit_cast", "implicit_cast"] {
            let project =
                Project::with_fixture("conversion.cpp", selected, SIGNED_CONVERSION_SOURCE);
            refresh_import(&project.config()).unwrap();
            let import = load_import(&project.config()).unwrap();
            let expected = value as i64;
            let source = format!(
                "verifying \"conversion.cpp\"; int64 {selected}(uint64 value) {{ requires value == {value}u64; ensures result == {expected}i64; }} by {{ execute(); simp(); }}"
            );
            check_arithmetic_sidecar(&project, &import, &source);
            let hostile = source.replace(
                &format!("result == {expected}i64"),
                &format!("result == {}i64", expected.wrapping_add(1)),
            );
            fs::write(
                project.directory.join("bad.click"),
                hostile.replace(
                    "-9223372036854775808i64",
                    "(-9223372036854775807i64 - 1i64)",
                ),
            )
            .unwrap();
            let bad = fs::read_to_string(project.directory.join("bad.click")).unwrap();
            let parsed = read_click_project(&project.directory.join("bad.click"), &bad).unwrap();
            assert!(verify_program_prepared_project(&parsed, &import).is_err());
        }
    }
}

#[test]
fn cpp20_signed_unsigned_round_trips_verify_without_input_bounds() {
    for (selected, value_type) in [
        ("signed_round_trip", "int64"),
        ("unsigned_round_trip", "uint64"),
    ] {
        let project = Project::with_fixture("conversion.cpp", selected, SIGNED_CONVERSION_SOURCE);
        refresh_import(&project.config()).unwrap();
        let import = load_import(&project.config()).unwrap();
        let source = format!(
            "verifying \"conversion.cpp\"; {value_type} {selected}({value_type} value) {{ ensures result == value; }} by {{ execute(); simp(); }}"
        );
        check_arithmetic_sidecar(&project, &import, &source);
    }
}

#[test]
fn cpp20_modular_conversion_contract_preserves_bits_and_frames_memory() {
    let project = Project::with_fixture("conversion.cpp", "relay", SIGNED_CONVERSION_SOURCE);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let source = r#"verifying "conversion.cpp";
int64 explicit_cast(uint64 value) { ensures ((uint64)result) == value; } by { execute(); simp(); }
int64 relay(uint64 value, int32* untouched) {
 owns untouched[0..1];
 ensures ((uint64)result) == value;
 ensures untouched[0] == old(untouched[0]);
} by { execute(); simp(); }
"#;
    check_arithmetic_sidecar(&project, &import, source);
}

#[test]
fn cpp20_conversion_keeps_following_signed_overflow_obligations() {
    let project = Project::with_fixture("conversion.cpp", "arithmetic", SIGNED_CONVERSION_SOURCE);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    check_arithmetic_sidecar(
        &project,
        &import,
        "verifying \"conversion.cpp\"; int64 arithmetic(uint64 value) { requires value == 18446744073709551615u64; ensures result == 0i64; } by { execute(); simp(); }",
    );
    let source = "verifying \"conversion.cpp\"; int64 arithmetic(uint64 value) { requires value == 9223372036854775807u64; ensures result == 0i64; } by { execute(); simp(); }";
    fs::write(project.directory.join("bad.click"), source).unwrap();
    let parsed = read_click_project(&project.directory.join("bad.click"), source).unwrap();
    let error = verify_program_prepared_project(&parsed, &import).unwrap_err();
    assert!(error.message().contains("overflow"), "{}", error.message());
}

#[test]
fn cpp20_fee_fast_paths_preserve_the_signed_return_conversion() {
    for (fee, at_size, size) in [
        (0u64, 1u64, 3u64),
        (7, 2, 3),
        (8, 2, 4),
        (8589934591, 2147483647, 2147483647),
    ] {
        for (selected, instance, expected) in [
            ("fee_down", "fee__bool_true", (fee * at_size / size) as i64),
            (
                "fee_up",
                "fee__bool_false",
                (fee * at_size).div_ceil(size) as i64,
            ),
        ] {
            let project =
                Project::with_fixture("conversion.cpp", selected, SIGNED_CONVERSION_SOURCE);
            refresh_import(&project.config()).unwrap();
            let import = load_import(&project.config()).unwrap();
            let contract = format!(
                "requires fee == {fee}i64; requires at_size == {at_size}; requires size == {size}; ensures result == {expected}i64;"
            );
            let caller_contract = contract.replace("requires fee ==", "requires fee_value ==");
            let source = format!(
                "verifying \"conversion.cpp\"; int64 {instance}(int64 fee, int32 at_size, int32 size) {{ {contract} }} by {{ execute(); simp(); }} int64 {selected}(int64 fee_value, int32 at_size, int32 size) {{ {caller_contract} }} by {{ execute(); simp(); }}"
            );
            check_arithmetic_sidecar(&project, &import, &source);
        }
    }
}

const RETURN_CALL_SOURCE: &str = include_str!("fixtures/cpp-verification/return-call/relay.cpp");

#[test]
fn direct_return_calls_verify_modular_contracts_and_frame_memory() {
    let project = Project::with_fixture("relay.cpp", "relay", RETURN_CALL_SOURCE);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let [
        CppStatement::ReturnCall {
            callee,
            arguments,
            value_type,
            cleanups,
            span,
        },
    ] = import.export().function.body.as_slice()
    else {
        panic!("retain a typed direct return call");
    };
    assert_eq!(callee.name, "echo");
    assert_eq!(
        callee.declaration_id,
        import.export().reachable_functions[0].declaration_id
    );
    assert_eq!(arguments.len(), 1);
    assert!(matches!(
        value_type,
        CppType::Integer {
            bits: 32,
            signed: true,
            ..
        }
    ));
    assert!(cleanups.is_empty());
    assert_eq!(span.file, "relay.cpp");
    let source = r#"verifying "relay.cpp";
int32 echo(int32 value) { ensures result == value; } by { execute(); simp(); }
int32 relay(int32 value, int32* untouched) {
 owns untouched[0..1];
 ensures result == value;
 ensures untouched[0] == old(untouched[0]);
} by { execute(); simp(); }
"#;
    check_return_call_sidecar(&project, &import, source);
}

#[test]
fn direct_return_calls_preserve_each_scalar_type_and_branch_result() {
    for (selected, helper, value_type) in [
        ("relay64", "echo64", "int64"),
        ("relay_u32", "echo_u32", "uint32"),
        ("relay_u64", "echo_u64", "uint64"),
        ("relay_bool", "echo_bool", "bool"),
    ] {
        let project = Project::with_fixture("relay.cpp", selected, RETURN_CALL_SOURCE);
        refresh_import(&project.config()).unwrap();
        let import = load_import(&project.config()).unwrap();
        let source = format!(
            "verifying \"relay.cpp\"; {value_type} {helper}({value_type} value) {{ ensures result == value; }} by {{ execute(); simp(); }} {value_type} {selected}({value_type} value) {{ ensures result == value; }} by {{ execute(); simp(); }}"
        );
        check_return_call_sidecar(&project, &import, &source);
    }
    let project = Project::with_fixture("relay.cpp", "choose", RETURN_CALL_SOURCE);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let source = r#"verifying "relay.cpp";
int32 echo(int32 value) { ensures result == value; } by { execute(); simp(); }
int32 choose(bool first, int32 value) {
 ensures first != 0 implies result == value;
 ensures first == 0 implies result == 7;
} by { execute(); simp(); }
"#;
    check_return_call_sidecar(&project, &import, source);
}

#[test]
fn direct_return_calls_keep_internal_capture_names_fresh_and_reject_false_results() {
    let project = Project::with_fixture(
        "relay.cpp",
        "relay",
        "int echo(int value) noexcept { return value; } int relay(int __click_cpp_return_value) noexcept { return echo(__click_cpp_return_value); }",
    );
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let source = r#"verifying "relay.cpp";
int32 echo(int32 value) { ensures result == value; } by { execute(); simp(); }
int32 relay(int32 __click_cpp_return_value) { ensures result == __click_cpp_return_value; } by { execute(); simp(); }
"#;
    check_return_call_sidecar(&project, &import, source);
    let hostile = source.replace("result == __click_cpp_return_value", "result == 7");
    fs::write(project.directory.join("bad.click"), &hostile).unwrap();
    let parsed = read_click_project(&project.directory.join("bad.click"), &hostile).unwrap();
    assert!(verify_program_prepared_project(&parsed, &import).is_err());
}

#[test]
fn direct_return_calls_preserve_fee_method_template_wrappers() {
    for (selected, instance, expected) in [
        (
            "FeeFrac::EvaluateFeeDown",
            "FeeFrac_EvaluateFee__bool_true",
            4i64,
        ),
        (
            "FeeFrac::EvaluateFeeUp",
            "FeeFrac_EvaluateFee__bool_false",
            5i64,
        ),
    ] {
        let project = Project::with_fixture("relay.cpp", selected, RETURN_CALL_SOURCE);
        refresh_import(&project.config()).unwrap();
        let import = load_import(&project.config()).unwrap();
        let proof_name = selected.replace("::", "_");
        let contract = format!(
            "views self->fee; views self->size; requires self->fee == 7i64; requires self->size == 3; requires at_size == 2; ensures result == {expected}i64; ensures self->fee == old(self->fee); ensures self->size == old(self->size);"
        );
        let source = format!(
            "verifying \"relay.cpp\"; int64 {instance}(const struct FeeFrac* self, int32 at_size) {{ {contract} }} by {{ execute(); simp(); }} int64 {proof_name}(const struct FeeFrac* self, int32 at_size) {{ {contract} }} by {{ execute(); simp(); }}"
        );
        check_return_call_sidecar(&project, &import, &source);
        let hostile = source.replace(
            &format!("result == {expected}i64"),
            &format!("result == {}i64", expected + 1),
        );
        fs::write(project.directory.join("bad.click"), &hostile).unwrap();
        let parsed = read_click_project(&project.directory.join("bad.click"), &hostile).unwrap();
        assert!(verify_program_prepared_project(&parsed, &import).is_err());
    }
}

#[test]
fn direct_return_calls_reject_unsupported_expression_positions_and_recursive_graphs() {
    for (source, diagnostic) in [
        (
            "int echo(int value) noexcept { return value; } long relay(int value) noexcept { return echo(value); }",
            "unsupported expression",
        ),
        (
            "int echo(int value) noexcept; int relay(int value) noexcept { return echo(value); }",
            "no reachable function definition",
        ),
        (
            "int relay(int value) noexcept { return relay(value); }",
            "recursive C++ calls",
        ),
    ] {
        let project = Project::with_fixture("relay.cpp", "relay", source);
        let error = refresh_import(&project.config()).unwrap_err();
        assert!(error.contains(diagnostic), "{error}");
        assert!(!project.artifact().exists());
    }
}

#[test]
fn direct_return_calls_capture_typed_results_before_destructors() {
    let cpp = include_str!("fixtures/cpp-verification/return-call/cleanup.cpp");
    for (selected, helper, value_type, helper_parameters, helper_contract, expected) in [
        (
            "capture",
            "read",
            "int32",
            "int32* slot",
            "owns slot[0..1]; ensures result == slot[0]; ensures slot[0] == old(slot[0]);",
            "7",
        ),
        (
            "capture_nested",
            "read",
            "int32",
            "int32* slot",
            "owns slot[0..1]; ensures result == slot[0]; ensures slot[0] == old(slot[0]);",
            "7",
        ),
        (
            "capture_wide",
            "wide",
            "int64",
            "",
            "ensures result == 4294967303i64;",
            "4294967303i64",
        ),
        (
            "capture_bool",
            "is_seven",
            "bool",
            "int32* slot",
            "owns slot[0..1]; requires slot[0] == 7; ensures result == 1; ensures slot[0] == old(slot[0]);",
            "1",
        ),
        ("ordinary_wide", "", "int64", "", "", "4294967303i64"),
        ("ordinary_bool", "", "bool", "", "", "1"),
    ] {
        let project = Project::with_fixture("cleanup.cpp", selected, cpp);
        refresh_import(&project.config()).unwrap();
        let import = load_import(&project.config()).unwrap();
        let helper_definition = if helper.is_empty() {
            String::new()
        } else {
            format!(
                "{value_type} {helper}({helper_parameters}) {{ {helper_contract} }} by {{ execute(); simp(); }}"
            )
        };
        let nested_helper = if selected == "capture_nested" {
            "int32 echo(int32 value) { ensures result == value; } by { execute(); simp(); }"
        } else {
            ""
        };
        let source = format!(
            r#"verifying "cleanup.cpp";
void Restore_constructor(struct Restore* self, int32* slot) {{
 owns &self->p; owns self->saved; owns slot[0..1];
 ensures self->p == slot; ensures self->saved == old(slot[0]); ensures slot[0] == 7;
 ensures separate(memory(object(self)), memory(self->p[0..1]));
}} by {{ execute(); simp(); }}
void Restore_destructor(struct Restore* self) {{
 requires separate(memory(object(self)), memory(self->p[0..1]));
 owns &self->p; owns self->saved; owns self->p[0..1];
 ensures self->p == old(self->p); ensures self->saved == old(self->saved);
 ensures self->p[0] == old(self->saved);
}} by {{ execute(); simp(); }}
{helper_definition}
{nested_helper}
{value_type} {selected}(int32* value) {{
 owns value[0..1]; ensures result == {expected}; ensures value[0] == old(value[0]);
}} by {{ execute(); simp(); }}
"#
        );
        check_return_call_sidecar(&project, &import, &source);
        let hostile = source.replace(
            &format!("ensures result == {expected}; ensures value[0]"),
            "ensures result == 0; ensures value[0]",
        );
        fs::write(project.directory.join("bad.click"), &hostile).unwrap();
        let parsed = read_click_project(&project.directory.join("bad.click"), &hostile).unwrap();
        assert!(verify_program_prepared_project(&parsed, &import).is_err());
    }
}

#[test]
fn direct_return_calls_keep_guarded_try_returns_unsupported_and_emit_uncaught_cleanup() {
    let cpp = include_str!("fixtures/cpp-verification/return-call/unwind.cpp");
    for selected in ["caught", "caught_value"] {
        let project = Project::with_fixture("unwind.cpp", selected, cpp);
        project.write_exception_enabled_compilation_database();
        project.write_config_with_exception_behavior(selected, "unwind.cpp", true, "scalar_int32");
        let error = refresh_import(&project.config()).unwrap_err();
        assert!(
            error.contains("return from a guarded try region"),
            "{error}"
        );
        assert!(!project.artifact().exists());
    }

    // Uncaught cleanup edges are checked structurally: resource-bearing
    // exceptional contracts remain outside the existing surface slice.
    let escaping = Project::with_fixture("unwind.cpp", "escaping", cpp);
    escaping.write_exception_enabled_compilation_database();
    escaping.write_config_with_exception_behavior("escaping", "unwind.cpp", true, "scalar_int32");
    refresh_import(&escaping.config()).unwrap();
    let lowered = lower_import(&load_import(&escaping.config()).unwrap()).unwrap();
    fn has_unwind_cleanup(statement: &CStatement) -> bool {
        match statement {
            CStatement::TryCatchInt32 {
                handler,
                cleanup_unwind: true,
                ..
            } => {
                matches!(handler.as_ref(), CStatement::Seq(cleanup, rethrow) if contains_call(cleanup, "Restore_destructor") && matches!(rethrow.as_ref(), CStatement::Throw(_)))
            }
            CStatement::Seq(first, second) => {
                has_unwind_cleanup(first) || has_unwind_cleanup(second)
            }
            _ => false,
        }
    }
    assert!(has_unwind_cleanup(lowered.kernel_function().body()));
}

#[test]
fn direct_return_calls_propagate_object_free_exception_contracts() {
    let project = Project::with_fixture(
        "relay.cpp",
        "relay",
        "int helper(bool should_throw) { if (should_throw) { throw 7; } return 5; } int relay(bool should_throw) { return helper(should_throw); }",
    );
    project.write_exception_enabled_compilation_database();
    project.write_config_with_exception_behavior("relay", "relay.cpp", true, "scalar_int32");
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let source = r#"verifying "relay.cpp";
int32 helper(bool should_throw) throws int32 { ensures result == 5 by { execute(); simp(); } exceptional ensures exception == 7 by { execute(); simp(); } }
int32 relay(bool should_throw) throws int32 { ensures result == 5 by { execute(); simp(); } exceptional ensures exception == 7 by { execute(); simp(); } }
"#;
    check_return_call_sidecar(&project, &import, source);
    let hostile = source.replace(
        "exceptional ensures exception == 7 by",
        "exceptional ensures exception == 8 by",
    );
    fs::write(project.directory.join("bad.click"), &hostile).unwrap();
    let parsed = read_click_project(&project.directory.join("bad.click"), &hostile).unwrap();
    assert!(verify_program_prepared_project(&parsed, &import).is_err());
}

#[test]
fn nested_return_calls_verify_scalar_types_and_fresh_captures() {
    let cpp = include_str!("fixtures/cpp-verification/return-call/nested.cpp");
    for (selected, helper, value_type) in [
        ("nested", "echo", "int32"),
        ("nested64", "echo64", "int64"),
        ("nested_u32", "echo_u32", "uint32"),
        ("nested_u64", "echo_u64", "uint64"),
        ("nested_bool", "echo_bool", "bool"),
    ] {
        let project = Project::with_fixture("nested.cpp", selected, cpp);
        refresh_import(&project.config()).unwrap();
        let import = load_import(&project.config()).unwrap();
        let [CppStatement::ReturnCall { arguments, .. }] = import.export().function.body.as_slice()
        else {
            panic!("retain return call");
        };
        let [
            CppCallArgument::Call {
                callee,
                value_type: capture_type,
                span,
                ..
            },
        ] = arguments.as_slice()
        else {
            panic!("retain nested call");
        };
        assert_eq!(callee.name, helper);
        assert_eq!(span.file, "nested.cpp");
        assert_eq!(capture_type, &import.export().function.return_type);
        let source = format!(
            "verifying \"nested.cpp\"; {value_type} {helper}({value_type} value) {{ ensures result == value; }} by {{ execute(); simp(); }} {value_type} {selected}({value_type} value) {{ ensures result == value; }} by {{ execute(); simp(); }}"
        );
        check_return_call_sidecar(&project, &import, &source);
        let mut hostile = source.clone();
        let result_claim = hostile.rfind("result == value").unwrap();
        hostile.replace_range(
            result_claim..result_claim + "result == value".len(),
            "result != value",
        );
        fs::write(project.directory.join("bad.click"), &hostile).unwrap();
        let parsed = read_click_project(&project.directory.join("bad.click"), &hostile).unwrap();
        assert!(verify_program_prepared_project(&parsed, &import).is_err());
    }
    let project = Project::with_fixture("nested.cpp", "collision", cpp);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    check_return_call_sidecar(
        &project,
        &import,
        r#"verifying "nested.cpp";
int32 echo(int32 value) { ensures result == value; } by { execute(); simp(); }
int32 collision(int32 __click_cpp_nested_value_0, int32 __click_cpp_nested_value_1) {
 ensures result == __click_cpp_nested_value_0;
} by { execute(); simp(); }
"#,
    );
}

#[test]
fn nested_return_calls_reject_unspecified_order_conversions_and_cycles() {
    for (cpp, diagnostic) in [
        (
            "int echo(int x) noexcept { return x; } int pair(int x, int y) noexcept { return x; } int relay(int x) noexcept { return pair(echo(x), echo(x)); }",
            "preserve evaluation order",
        ),
        (
            "int echo(int x) noexcept { return x; } long wide(long x) noexcept { return x; } long relay(int x) noexcept { return wide(echo(x)); }",
            "unsupported expression",
        ),
        (
            "int echo(int x) noexcept { return x; } int relay(int x) noexcept { return echo(relay(x)); }",
            "recursive C++ calls",
        ),
    ] {
        let project = Project::with_fixture("nested.cpp", "relay", cpp);
        let error = refresh_import(&project.config()).unwrap_err();
        assert!(error.contains(diagnostic), "{error}");
        assert!(!project.artifact().exists());
    }
}

#[test]
fn nested_return_calls_propagate_inner_exceptions_without_evaluating_outer_call() {
    let cpp = "int inner(bool fail) { if (fail) { throw 7; } return 5; } int outer(int value) { return value; } int relay(bool fail) { return outer(inner(fail)); }";
    let project = Project::with_fixture("nested.cpp", "relay", cpp);
    project.write_exception_enabled_compilation_database();
    project.write_config_with_exception_behavior("relay", "nested.cpp", true, "scalar_int32");
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    check_return_call_sidecar(
        &project,
        &import,
        r#"verifying "nested.cpp";
int32 inner(bool fail) throws int32 {
 ensures result == 5 by { execute(); simp(); }
 exceptional ensures exception == 7 by { execute(); simp(); }
}
int32 outer(int32 value) { ensures result == value; } by { execute(); simp(); }
int32 relay(bool fail) throws int32 {
 ensures result == 5 by { execute(); simp(); }
 exceptional ensures exception == 7 by { execute(); simp(); }
}
"#,
    );
}

#[test]
fn nested_return_calls_use_distinct_capture_types_across_branches() {
    let project = Project::with_fixture(
        "nested.cpp",
        "choose",
        include_str!("fixtures/cpp-verification/return-call/nested.cpp"),
    );
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    check_return_call_sidecar(
        &project,
        &import,
        r#"verifying "nested.cpp";
int32 echo(int32 value) { ensures result == value; } by { execute(); simp(); }
int64 echo64(int64 value) { ensures result == value; } by { execute(); simp(); }
int64 outer32(int32 value) { requires value == 7; ensures result == 7i64; } by { execute(); simp(); }
int64 choose(bool first, int32 value) { requires value == 7; ensures result == 7i64; } by { execute(); simp(); }
"#,
    );
}

#[test]
fn nested_capture_name_probes_scale_with_calls_and_source_collisions() {
    for size in [2usize, 4, 8, 16] {
        let locals = (0..size)
            .map(|index| format!("int __click_cpp_nested_value_{index} = 0;"))
            .collect::<String>();
        let nested = format!("{}value{}", "echo(".repeat(size + 1), ")".repeat(size + 1));
        let cpp = format!(
            "int echo(int value) noexcept {{ return value; }} int relay(int value) noexcept {{ {locals} return {nested}; }}"
        );
        let project = Project::with_fixture("nested.cpp", "relay", &cpp);
        refresh_import(&project.config()).unwrap();
        let import = load_import(&project.config()).unwrap();
        let (lowered, work) =
            click::instrumentation::measure_deterministic_work(|| lower_import(&import));
        lowered.unwrap();
        assert!(
            work >= 2 * size && work <= 5 * size + 32,
            "{size} calls and collisions: {work} work"
        );
    }
}

const MULTIPLE_ARGUMENTS_SOURCE: &str =
    include_str!("fixtures/cpp-verification/return-call/multiple-arguments.cpp");

#[test]
fn nested_calls_with_stable_siblings_preserve_each_argument_position_and_casts() {
    for (selected, outer, slot) in [
        ("nested_first", "first", "a"),
        ("literal_siblings", "first", "a"),
        ("nested_second", "second", "b"),
        ("nested_third", "third", "c"),
    ] {
        let project = Project::with_fixture("arguments.cpp", selected, MULTIPLE_ARGUMENTS_SOURCE);
        refresh_import(&project.config()).unwrap();
        let import = load_import(&project.config()).unwrap();
        let source = format!(
            "verifying \"arguments.cpp\"; int32 echo(int32 value) {{ ensures result == value; }} by {{ execute(); simp(); }} int32 {outer}(int32 a, int32 b, int32 c) {{ ensures result == {slot}; }} by {{ execute(); simp(); }} int32 {selected}(int32 value) {{ ensures result == value; }} by {{ execute(); simp(); }}"
        );
        check_return_call_sidecar(&project, &import, &source);
        let [CppStatement::ReturnCall { arguments, .. }] = import.export().function.body.as_slice()
        else {
            panic!("retain return call");
        };
        assert_eq!(arguments.len(), 3);
        assert_eq!(
            arguments
                .iter()
                .filter(|arg| matches!(arg, CppCallArgument::Call { .. }))
                .count(),
            1
        );
    }
    for (selected, outer, inner, value_type) in [
        (
            "nested_unsigned",
            "pick_unsigned",
            "echo_unsigned",
            "uint32",
        ),
        ("nested_bool", "pick_bool", "echo_bool", "bool"),
    ] {
        let project = Project::with_fixture("arguments.cpp", selected, MULTIPLE_ARGUMENTS_SOURCE);
        refresh_import(&project.config()).unwrap();
        let import = load_import(&project.config()).unwrap();
        let source = format!(
            "verifying \"arguments.cpp\"; {value_type} {inner}({value_type} value) {{ ensures result == value; }} by {{ execute(); simp(); }} {value_type} {outer}({value_type} left, {value_type} right) {{ ensures result == right; }} by {{ execute(); simp(); }} {value_type} {selected}({value_type} value, int32 other) {{ ensures result == value; }} by {{ execute(); simp(); }}"
        );
        check_return_call_sidecar(&project, &import, &source);
    }
}

#[test]
fn nested_calls_with_stable_siblings_preserve_fee_rounding_pattern() {
    for (fee, round_down, expected) in [
        (7, true, 4),
        (7, false, 5),
        (-7, true, -5),
        (-7, false, -4),
        (10, true, 6),
        (10, false, 6),
    ] {
        let project =
            Project::with_fixture("arguments.cpp", "EvaluateFee", MULTIPLE_ARGUMENTS_SOURCE);
        refresh_import(&project.config()).unwrap();
        let import = load_import(&project.config()).unwrap();
        let product = fee * 3;
        let down = i32::from(round_down);
        let source = format!(
            r#"verifying "arguments.cpp";
int64 Mul(int64 fee, int32 at_size) {{ requires fee == {fee}i64; requires at_size == 3; ensures result == {product}i64; }} by {{ execute(); simp(); }}
int64 Div(int64 n, int32 d, bool round_down) {{ requires n == {product}i64; requires d == 5; requires round_down == {down}; ensures result == {expected}i64; }} by {{ execute(); simp(); }}
int64 EvaluateFee(int64 fee, int32 at_size, int32 divisor, bool round_down) {{ requires fee == {fee}i64; requires at_size == 3; requires divisor == 5; requires round_down == {down}; ensures result == {expected}i64; }} by {{ execute(); simp(); }}
"#
        );
        check_return_call_sidecar(&project, &import, &source);
        let mut hostile = source.clone();
        let claim = format!("result == {expected}i64");
        let start = hostile.rfind(&claim).unwrap();
        hostile.replace_range(
            start..start + claim.len(),
            &format!("result == {}i64", expected + 1),
        );
        fs::write(project.directory.join("bad.click"), &hostile).unwrap();
        let parsed = read_click_project(&project.directory.join("bad.click"), &hostile).unwrap();
        assert!(verify_program_prepared_project(&parsed, &import).is_err());
    }
}

#[test]
fn nested_calls_reject_sibling_memory_reads_effects_arithmetic_and_other_calls() {
    for cpp in [
        "int mutate(int& x) noexcept { x = 7; return x; } int pair(int a, int b) noexcept { return a; } int relay(int& x) noexcept { return pair(mutate(x), x); }",
        "int mutate(int* x) noexcept { *x = 7; return *x; } int pair(int a, int b) noexcept { return a; } int relay(int* x) noexcept { return pair(mutate(x), *x); }",
        "struct Box { int value; }; int mutate(Box& box) noexcept { box.value = 7; return box.value; } int pair(int a, int b) noexcept { return a; } int relay(Box& box) noexcept { return pair(mutate(box), box.value); }",
        "int echo(int x) noexcept { return x; } int pair(int a, int b) noexcept { return a; } int relay(int x) noexcept { return pair(echo(x), echo(x)); }",
        "int echo(int x) noexcept { return x; } int pair(int a, int b) noexcept { return a; } int relay(int x) noexcept { return pair(echo(x), x + 1); }",
        "int echo(int x) noexcept { return x; } int pair(int a, int b) noexcept { return a; } int relay(int x) noexcept { return pair(echo(x), ++x); }",
    ] {
        let project = Project::with_fixture("arguments.cpp", "relay", cpp);
        let error = refresh_import(&project.config()).unwrap_err();
        assert!(error.contains("preserve evaluation order"), "{error}");
        assert!(!project.artifact().exists());
    }
}

#[test]
fn nested_calls_with_stable_siblings_propagate_inner_exceptions() {
    let cpp = "int inner(bool fail) { if (fail) { throw 7; } return 5; } int outer(int left, int value, bool flag) { return value; } int relay(bool fail, int left) { return outer(left, inner(fail), fail); }";
    let project = Project::with_fixture("arguments.cpp", "relay", cpp);
    project.write_exception_enabled_compilation_database();
    project.write_config_with_exception_behavior("relay", "arguments.cpp", true, "scalar_int32");
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    check_return_call_sidecar(
        &project,
        &import,
        r#"verifying "arguments.cpp";
int32 inner(bool fail) throws int32 { ensures result == 5 by { execute(); simp(); } exceptional ensures exception == 7 by { execute(); simp(); } }
int32 outer(int32 left, int32 value, bool flag) { ensures result == value; } by { execute(); simp(); }
int32 relay(bool fail, int32 left) throws int32 { ensures result == 5 by { execute(); simp(); } exceptional ensures exception == 7 by { execute(); simp(); } }
"#,
    );
}

#[test]
fn nested_argument_lowering_scales_with_arity() {
    for size in [2usize, 8, 32, 128] {
        let parameters = (0..size)
            .map(|i| format!("int a{i}"))
            .collect::<Vec<_>>()
            .join(", ");
        let arguments = std::iter::once("inner()".to_string())
            .chain((1..size).map(|_| "7".to_string()))
            .collect::<Vec<_>>()
            .join(", ");
        let cpp = format!(
            "int inner() noexcept {{ return 7; }} int outer({parameters}) noexcept {{ return a0; }} int relay() noexcept {{ return outer({arguments}); }}"
        );
        let project = Project::with_fixture("arguments.cpp", "relay", &cpp);
        refresh_import(&project.config()).unwrap();
        let import = load_import(&project.config()).unwrap();
        let (lowered, work) =
            click::instrumentation::measure_deterministic_work(|| lower_import(&import));
        lowered.unwrap();
        assert!(
            work >= size && work <= 2 * size + 32,
            "{size} arguments: {work} work"
        );
    }
}

#[test]
fn stable_siblings_remain_valid_when_the_nested_call_writes_memory() {
    let project = Project::with_fixture(
        "arguments.cpp",
        "effectful_inner",
        MULTIPLE_ARGUMENTS_SOURCE,
    );
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    check_return_call_sidecar(
        &project,
        &import,
        r#"verifying "arguments.cpp";
int32 write_seven(int32* slot) {
 owns slot[0..1]; ensures slot[0] == 7; ensures result == 7;
} by { execute(); simp(); }
int32 second(int32 a, int32 b, int32 c) { ensures result == b; } by { execute(); simp(); }
int32 effectful_inner(int32* slot, int32 snapshot) {
 owns slot[0..1]; ensures slot[0] == 7; ensures result == 7;
} by { execute(); simp(); }
"#,
    );
}

#[test]
fn fee_pattern_contracts_reject_zero_divisors_and_unproved_product_bounds() {
    for (selected, source) in [
        (
            "Div",
            "verifying \"arguments.cpp\"; int64 Div(int64 n, int32 d, bool round_down) { requires n == 21i64; requires d == 0; ensures result == result; } by { execute(); simp(); }",
        ),
        (
            "Mul",
            "verifying \"arguments.cpp\"; int64 Mul(int64 fee, int32 at_size) { requires fee == 9223372036854775807i64; requires at_size == 3; ensures result == result; } by { execute(); simp(); }",
        ),
    ] {
        let project = Project::with_fixture("arguments.cpp", selected, MULTIPLE_ARGUMENTS_SOURCE);
        refresh_import(&project.config()).unwrap();
        let import = load_import(&project.config()).unwrap();
        fs::write(project.directory.join("bad.click"), source).unwrap();
        let parsed = read_click_project(&project.directory.join("bad.click"), source).unwrap();
        assert!(verify_program_prepared_project(&parsed, &import).is_err());
    }
}

#[test]
fn stable_constant_siblings_reject_external_linkage_and_mutable_globals() {
    for declaration in ["inline constexpr long value = 7;", "long value = 7;"] {
        let cpp = format!(
            "{declaration} int inner() noexcept {{ return 5; }} long outer(int first, long second) noexcept {{ return second; }} long relay() noexcept {{ return outer(inner(), value); }}"
        );
        let project = Project::with_fixture("arguments.cpp", "relay", &cpp);
        let error = refresh_import(&project.config()).unwrap_err();
        assert!(!project.artifact().exists());
        assert!(
            error.contains("constexpr") || error.contains("preserve evaluation order"),
            "{error}"
        );
    }
}

#[test]
fn scalar_local_siblings_survive_nested_memory_effects() {
    let project =
        Project::with_fixture("arguments.cpp", "local_sibling", MULTIPLE_ARGUMENTS_SOURCE);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    check_return_call_sidecar(
        &project,
        &import,
        r#"verifying "arguments.cpp";
int32 write_seven(int32* slot) { owns slot[0..1]; ensures slot[0] == 7; ensures result == 7; } by { execute(); simp(); }
int32 first(int32 a, int32 b, int32 c) { ensures result == a; } by { execute(); simp(); }
int32 local_sibling(int32* slot, int32 value) { owns slot[0..1]; ensures slot[0] == 7; ensures result == value; } by { execute(); simp(); }
"#,
    );
}

#[test]
fn nested_stable_siblings_preserve_concrete_boolean_template_rounding_wrappers() {
    for (selected, down, fee, expected) in [
        ("fee_down", 1, 7, 4),
        ("fee_up", 0, 7, 5),
        ("fee_down", 1, -7, -5),
        ("fee_up", 0, -7, -4),
    ] {
        let project = Project::with_fixture("arguments.cpp", selected, MULTIPLE_ARGUMENTS_SOURCE);
        refresh_import(&project.config()).unwrap();
        let import = load_import(&project.config()).unwrap();
        let [CppStatement::ReturnCall { callee, .. }] = import.export().function.body.as_slice()
        else {
            panic!("retain template return call");
        };
        let instance = &callee.name;
        let product = fee * 3;
        let source = format!(
            r#"verifying "arguments.cpp";
int64 Mul(int64 fee, int32 at_size) {{ requires fee == {fee}i64; requires at_size == 3; ensures result == {product}i64; }} by {{ execute(); simp(); }}
int64 Div(int64 n, int32 d, bool round_down) {{ requires n == {product}i64; requires d == 5; requires round_down == {down}; ensures result == {expected}i64; }} by {{ execute(); simp(); }}
int64 {instance}(int64 fee, int32 at_size, int32 divisor) {{ requires fee == {fee}i64; requires at_size == 3; requires divisor == 5; ensures result == {expected}i64; }} by {{ execute(); simp(); }}
int64 {selected}(int64 fee, int32 at_size, int32 divisor) {{ requires fee == {fee}i64; requires at_size == 3; requires divisor == 5; ensures result == {expected}i64; }} by {{ execute(); simp(); }}
"#
        );
        check_return_call_sidecar(&project, &import, &source);
    }
}

const STATIC_HELPERS_SOURCE: &str =
    include_str!("fixtures/cpp-verification/return-call/static-helpers.cpp");

#[test]
fn static_helpers_preserve_scalar_types_class_identity_and_no_receiver() {
    for (member, value_type) in [
        ("echo", "int32"),
        ("echo64", "int64"),
        ("echo_u32", "uint32"),
        ("echo_u64", "uint64"),
        ("echo_bool", "bool"),
    ] {
        let project = Project::with_fixture(
            "static.cpp",
            &format!("Scalar::{member}"),
            STATIC_HELPERS_SOURCE,
        );
        refresh_import(&project.config()).unwrap();
        let import = load_import(&project.config()).unwrap();
        assert!(matches!(&import.export().function.function_kind,
            CppFunctionKind::StaticMethod { record_name, record_declaration_id }
            if record_name == "Scalar" && !record_declaration_id.is_empty()));
        assert_eq!(import.export().function.parameters.len(), 1);
        assert!(import.export().records.is_empty());
        let source = format!(
            "verifying \"static.cpp\"; {value_type} Scalar_{member}({value_type} value) {{ ensures result == value; }} by {{ execute(); simp(); }}"
        );
        check_return_call_sidecar(&project, &import, &source);
        let hostile = source.replace("result == value", "result != value");
        fs::write(project.directory.join("bad.click"), &hostile).unwrap();
        let parsed = read_click_project(&project.directory.join("bad.click"), &hostile).unwrap();
        assert!(verify_program_prepared_project(&parsed, &import).is_err());
    }
}

#[test]
fn static_helpers_support_modular_nested_and_initializer_calls() {
    for selected in ["static_chain", "static_local"] {
        let project = Project::with_fixture("static.cpp", selected, STATIC_HELPERS_SOURCE);
        refresh_import(&project.config()).unwrap();
        let import = load_import(&project.config()).unwrap();
        let source = format!(
            r#"verifying "static.cpp";
int32 Scalar_echo(int32 value) {{ ensures result == value; }} by {{ execute(); simp(); }}
int32 Other_echo(int32 value) {{ ensures result == value; }} by {{ execute(); simp(); }}
int32 {selected}(int32 value) {{ ensures result == value; }} by {{ execute(); simp(); }}
"#
        );
        // The local caller reaches only Scalar_echo.
        let source = if selected == "static_local" {
            source.replace("int32 Other_echo(int32 value) { ensures result == value; } by { execute(); simp(); }\n", "")
        } else {
            source
        };
        check_return_call_sidecar(&project, &import, &source);
    }
}

#[test]
fn static_helpers_preserve_nested_fee_rounding_template_shape() {
    for (selected, down, fee, expected) in [
        ("static_fee_down", 1, 7, 4),
        ("static_fee_up", 0, 7, 5),
        ("static_fee_down", 1, -7, -5),
        ("static_fee_up", 0, -7, -4),
    ] {
        let project = Project::with_fixture("static.cpp", selected, STATIC_HELPERS_SOURCE);
        refresh_import(&project.config()).unwrap();
        let import = load_import(&project.config()).unwrap();
        let [CppStatement::ReturnCall { callee, .. }] = import.export().function.body.as_slice()
        else {
            panic!("static template call");
        };
        let product = fee * 3;
        let instance = &callee.name;
        let source = format!(
            r#"verifying "static.cpp";
int64 FeeMath_Mul(int64 fee, int32 at_size) {{ requires fee == {fee}i64; requires at_size == 3; ensures result == {product}i64; }} by {{ execute(); simp(); }}
int64 FeeMath_Div(int64 n, int32 d, bool round_down) {{ requires n == {product}i64; requires d == 5; requires round_down == {down}; ensures result == {expected}i64; }} by {{ execute(); simp(); }}
int64 {instance}(int64 fee, int32 at_size, int32 divisor) {{ requires fee == {fee}i64; requires at_size == 3; requires divisor == 5; ensures result == {expected}i64; }} by {{ execute(); simp(); }}
int64 {selected}(int64 fee, int32 at_size, int32 divisor) {{ requires fee == {fee}i64; requires at_size == 3; requires divisor == 5; ensures result == {expected}i64; }} by {{ execute(); simp(); }}
"#
        );
        check_return_call_sidecar(&project, &import, &source);
    }
}

#[test]
fn static_helpers_reject_object_dispatch_reference_parameters_and_recursion() {
    for (cpp, selected, diagnostic) in [
        (
            "struct H { int storage; static int echo(int x) noexcept { return x; } }; int relay(H& h, int x) noexcept { return h.echo(x); }",
            "relay",
            "class-qualified or unqualified",
        ),
        (
            "struct H { static int echo(int x) noexcept { return x; } }; int relay(int x) noexcept { return H{}.echo(x); }",
            "relay",
            "unsupported expression",
        ),
        (
            "struct H { static int echo(int x) noexcept { return x; } }; int relay(int x) noexcept { return ((void)++x, H{}).echo(x); }",
            "relay",
            "unsupported expression",
        ),
        (
            "struct H { static int read(const int& x) noexcept { return x; } };",
            "H::read",
            "by-value scalar",
        ),
        (
            "struct H { static int read(int* x) noexcept { return *x; } };",
            "H::read",
            "by-value scalar",
        ),
        (
            "struct H { static int recurse(int x) noexcept { return recurse(x); } };",
            "H::recurse",
            "recursive C++ calls",
        ),
    ] {
        let project = Project::with_fixture("static.cpp", selected, cpp);
        let error = refresh_import(&project.config()).unwrap_err();
        assert!(error.contains(diagnostic), "{error}");
        assert!(!project.artifact().exists());
    }
}

#[test]
fn static_helpers_propagate_scalar_exceptions_through_nested_calls() {
    let cpp = "struct H { static int inner(bool fail) { if (fail) { throw 7; } return 5; } static int outer(int value) { return value; } static int relay(bool fail) { return outer(inner(fail)); } };";
    let project = Project::with_fixture("static.cpp", "H::relay", cpp);
    project.write_exception_enabled_compilation_database();
    project.write_config_with_exception_behavior("H::relay", "static.cpp", true, "scalar_int32");
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    check_return_call_sidecar(
        &project,
        &import,
        r#"verifying "static.cpp";
int32 H_inner(bool fail) throws int32 { ensures result == 5 by { execute(); simp(); } exceptional ensures exception == 7 by { execute(); simp(); } }
int32 H_outer(int32 value) { ensures result == value; } by { execute(); simp(); }
int32 H_relay(bool fail) throws int32 { ensures result == 5 by { execute(); simp(); } exceptional ensures exception == 7 by { execute(); simp(); } }
"#,
    );
}

#[test]
fn static_helpers_called_from_value_methods_preserve_field_authority() {
    let project = Project::with_fixture("static.cpp", "FeeValue::Evaluate", STATIC_HELPERS_SOURCE);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let source = r#"verifying "static.cpp";
int64 FeeMath_Mul(int64 fee, int32 at_size) { requires fee == 7i64; requires at_size == 3; ensures result == 21i64; } by { execute(); simp(); }
int64 FeeValue_Evaluate(const struct FeeValue* self, int32 at_size) {
 owns self->fee;
 requires self->fee == 7i64;
 requires at_size == 3;
 ensures result == 21i64;
 ensures self->fee == old(self->fee);
} by { execute(); simp(); }
"#;
    check_return_call_sidecar(&project, &import, source);
    let hostile = source.replace(" owns self->fee;\n", "");
    fs::write(project.directory.join("bad.click"), &hostile).unwrap();
    let parsed = read_click_project(&project.directory.join("bad.click"), &hostile).unwrap();
    assert!(verify_program_prepared_project(&parsed, &import).is_err());
}

#[test]
fn static_helpers_cannot_skip_arithmetic_definedness_with_trivial_postconditions() {
    for (selected, contract) in [
        (
            "FeeMath::Mul",
            "int64 FeeMath_Mul(int64 fee, int32 at_size) { ensures result == result; } by { execute(); simp(); }",
        ),
        (
            "FeeMath::Div",
            "int64 FeeMath_Div(int64 n, int32 d, bool round_down) { ensures result == result; } by { execute(); simp(); }",
        ),
    ] {
        let project = Project::with_fixture("static.cpp", selected, STATIC_HELPERS_SOURCE);
        refresh_import(&project.config()).unwrap();
        let import = load_import(&project.config()).unwrap();
        let source = format!("verifying \"static.cpp\"; {contract}");
        fs::write(project.directory.join("bad.click"), &source).unwrap();
        let parsed = read_click_project(&project.directory.join("bad.click"), &source).unwrap();
        assert!(verify_program_prepared_project(&parsed, &import).is_err());
    }
}

const NORMALIZED_EVALUATION_SOURCE: &str =
    include_str!("fixtures/cpp-verification/return-call/normalized-evaluation.cpp");

#[test]
fn normalized_scalar_calls_agree_across_returns_initializers_and_discarded_results() {
    for (selected, contract) in [
        (
            "direct",
            "int32 direct(int32 value, int32 sibling) { ensures result == value; } by { execute(); simp(); }",
        ),
        (
            "initialized",
            "int32 initialized(int32 value, int32 sibling) { ensures result == value; } by { execute(); simp(); }",
        ),
        (
            "discarded",
            "int32 discarded(int32 value) { ensures result == value; } by { execute(); simp(); }",
        ),
    ] {
        let project =
            Project::with_fixture("evaluation.cpp", selected, NORMALIZED_EVALUATION_SOURCE);
        refresh_import(&project.config()).unwrap();
        let import = load_import(&project.config()).unwrap();
        let helpers = if selected == "discarded" {
            ""
        } else {
            "int32 first(int32 value, int32 sibling) { ensures result == value; } by { execute(); simp(); }"
        };
        let source = format!(
            "verifying \"evaluation.cpp\"; int32 echo(int32 value) {{ ensures result == value; }} by {{ execute(); simp(); }} {helpers} {contract}"
        );
        check_return_call_sidecar(&project, &import, &source);
        let hostile = source.replace("ensures result == value", "ensures result != value");
        fs::write(project.directory.join("bad.click"), &hostile).unwrap();
        let parsed = read_click_project(&project.directory.join("bad.click"), &hostile).unwrap();
        assert!(verify_program_prepared_project(&parsed, &import).is_err());
    }
}

#[test]
fn normalized_initializer_calls_preserve_scalar_types_and_static_helpers() {
    for (selected, helper, value_type) in [
        ("initialized64", "echo64", "int64"),
        ("initialized_u32", "echo_u32", "uint32"),
        ("initialized_u64", "echo_u64", "uint64"),
        ("Helper::initialized", "Helper_echo", "int32"),
    ] {
        let project =
            Project::with_fixture("evaluation.cpp", selected, NORMALIZED_EVALUATION_SOURCE);
        refresh_import(&project.config()).unwrap();
        let import = load_import(&project.config()).unwrap();
        let caller = &import.export().function.name;
        let source = format!(
            "verifying \"evaluation.cpp\"; {value_type} {helper}({value_type} value) {{ ensures result == value; }} by {{ execute(); simp(); }} {value_type} {caller}({value_type} value) {{ ensures result == value; }} by {{ execute(); simp(); }}"
        );
        check_return_call_sidecar(&project, &import, &source);
    }
}

#[test]
fn normalized_initializer_calls_capture_before_normal_cleanup() {
    let project = Project::with_fixture(
        "evaluation.cpp",
        "initialized_cleanup",
        NORMALIZED_EVALUATION_SOURCE,
    );
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    // Reuse the existing independently checked constructor/destructor contracts.
    let source = r#"verifying "evaluation.cpp";
void Restore_constructor(struct Restore* self, int32* value) {
 owns &self->slot; owns self->saved; owns value[0..1];
 ensures self->slot == value;
 ensures self->saved == old(value[0]);
 ensures value[0] == 7;
 ensures separate(memory(object(self)), memory(self->slot[0..1]));
} by { execute(); simp(); }
void Restore_destructor(struct Restore* self) {
 requires separate(memory(object(self)), memory(self->slot[0..1]));
 owns &self->slot; owns self->saved; owns self->slot[0..1];
 ensures self->slot == old(self->slot);
 ensures self->saved == old(self->saved);
 ensures self->slot[0] == old(self->saved);
} by { execute(); simp(); }
int32 read(int32* slot) { owns slot[0..1]; ensures result == old(slot[0]); ensures slot[0] == old(slot[0]); } by { execute(); simp(); }
int32 echo(int32 value) { ensures result == value; } by { execute(); simp(); }
int32 initialized_cleanup(int32* value) { owns value[0..1]; ensures result == 7; ensures value[0] == old(value[0]); } by { execute(); simp(); }
"#;
    check_return_call_sidecar(&project, &import, source);
    let lowered = lower_import(&import).unwrap();
    assert_eq!(
        lowered.contract_functions().len(),
        import.export().reachable_functions.len() + 1
    );
    assert!(lowered.record_layouts().contains_key("Restore"));
    let caller = lowered
        .contract_functions()
        .iter()
        .find(|f| f.name() == "initialized_cleanup")
        .unwrap();
    assert_eq!(
        caller
            .local_struct_values()
            .get("guard")
            .map(String::as_str),
        Some("Restore")
    );
}

#[test]
fn normalized_call_order_rejections_are_independent_of_source_context() {
    for body in [
        "return first(echo(value), *slot);",
        "int captured = first(echo(value), *slot); return captured;",
        "first(echo(value), *slot); return value;",
    ] {
        let cpp = format!(
            "int echo(int value) noexcept {{ return value; }} int first(int value, int sibling) noexcept {{ return value; }} int relay(int value, int* slot) noexcept {{ {body} }}"
        );
        let project = Project::with_fixture("evaluation.cpp", "relay", &cpp);
        let error = refresh_import(&project.config()).unwrap_err();
        assert!(error.contains("preserve evaluation order"), "{error}");
        assert!(!project.artifact().exists());
    }
}

#[test]
fn normalized_initializer_calls_propagate_inner_exceptions() {
    let cpp = "int inner(bool fail) { if (fail) { throw 7; } return 5; } int outer(int value) { return value; } int relay(bool fail) { int captured = outer(inner(fail)); return captured; }";
    let project = Project::with_fixture("evaluation.cpp", "relay", cpp);
    project.write_exception_enabled_compilation_database();
    project.write_config_with_exception_behavior("relay", "evaluation.cpp", true, "scalar_int32");
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    check_return_call_sidecar(
        &project,
        &import,
        r#"verifying "evaluation.cpp";
int32 inner(bool fail) throws int32 { ensures result == 5 by { execute(); simp(); } exceptional ensures exception == 7 by { execute(); simp(); } }
int32 outer(int32 value) { ensures result == value; } by { execute(); simp(); }
int32 relay(bool fail) throws int32 { ensures result == 5 by { execute(); simp(); } exceptional ensures exception == 7 by { execute(); simp(); } }
"#,
    );
}

#[test]
fn normalized_initializer_and_return_work_scales_with_argument_arity() {
    for size in [2usize, 8, 32, 128] {
        let parameters = (0..size)
            .map(|i| format!("int value{i}"))
            .collect::<Vec<_>>()
            .join(", ");
        let arguments = (0..size)
            .map(|i| {
                if i == size / 2 {
                    "echo(value)".into()
                } else {
                    "value".into()
                }
            })
            .collect::<Vec<String>>()
            .join(", ");
        let cpp = format!(
            "int echo(int value) noexcept {{ return value; }} int first({parameters}) noexcept {{ return value0; }} int direct(int value) noexcept {{ return first({arguments}); }} int initialized(int value) noexcept {{ int captured = first({arguments}); return captured; }}"
        );
        let mut measured = Vec::new();
        for selected in ["direct", "initialized"] {
            let project = Project::with_fixture("evaluation.cpp", selected, &cpp);
            refresh_import(&project.config()).unwrap();
            let import = load_import(&project.config()).unwrap();
            let (lowered, work) =
                click::instrumentation::measure_deterministic_work(|| lower_import(&import));
            let lowered = lowered.unwrap();
            assert_eq!(lowered.contract_functions().len(), 3);
            assert!(
                work >= size && work <= 2 * size + 32,
                "{selected}, arity {size}: {work}"
            );
            measured.push(work);
        }
        assert_eq!(
            measured[0] + 1,
            measured[1],
            "the initializer adds one lifetime-planning source event at arity {size}"
        );
    }
}

#[test]
fn lifetime_returns_destroy_only_the_objects_constructed_on_that_path() {
    let cpp =
        include_str!("fixtures/cpp-verification/reverse-destructor-order/construction_prefix.cpp");
    let project = Project::with_fixture("restore_twice.cpp", "construction_prefix", cpp);
    refresh_import(&project.config()).expect("export an early return before a later construction");
    let import = load_import(&project.config()).unwrap();
    let [
        CppStatement::Declare { .. },
        CppStatement::If { then_branch, .. },
        CppStatement::Declare { .. },
        CppStatement::Assign { .. },
        CppStatement::Return {
            cleanups: final_cleanups,
            ..
        },
    ] = import.export().function.body.as_slice()
    else {
        panic!("construction events must retain their source order");
    };
    let [
        CppStatement::Return {
            cleanups: early_cleanups,
            ..
        },
    ] = then_branch.as_slice()
    else {
        panic!("early return cleanup edge");
    };
    assert_eq!(early_cleanups.len(), 1);
    assert_eq!(final_cleanups.len(), 2);
    let source = REVERSE_DESTRUCTOR_SIDECAR.replace("restore_twice(", "construction_prefix(");
    check_return_call_sidecar(&project, &import, &source);
    let false_claim = source.replace(
        "early != 0 implies result == 7",
        "early != 0 implies result == 9",
    );
    let sidecar = project.directory.join("demo.click");
    fs::write(&sidecar, &false_claim).unwrap();
    let false_project = read_click_project(&sidecar, &false_claim).unwrap();
    verify_program_prepared_project(&false_project, &import)
        .expect_err("a future object cannot change the early return result");
}

#[test]
fn lifetime_return_before_any_construction_has_no_cleanup() {
    let cpp =
        include_str!("fixtures/cpp-verification/reverse-destructor-order/construction_prefix.cpp");
    let project = Project::with_fixture("restore_twice.cpp", "before_construction", cpp);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let [
        CppStatement::If { then_branch, .. },
        CppStatement::Declare { .. },
        CppStatement::Return {
            cleanups: final_cleanups,
            ..
        },
    ] = import.export().function.body.as_slice()
    else {
        panic!("source construction order");
    };
    let [CppStatement::Return { cleanups, .. }] = then_branch.as_slice() else {
        panic!("early return");
    };
    assert!(cleanups.is_empty());
    assert_eq!(final_cleanups.len(), 1);
    let source = REVERSE_DESTRUCTOR_SIDECAR
        .replace("restore_twice(", "before_construction(")
        .replace(
            "early != 0 implies result == 7",
            "early != 0 implies result == old(value[0])",
        )
        .replace(
            "early == 0 implies result == 9",
            "early == 0 implies result == 7",
        );
    check_return_call_sidecar(&project, &import, &source);
}

#[test]
fn resolved_declaration_identities_bind_overloads_scopes_and_equal_width_types() {
    let project = Project::with_fixture(
        "identity.cpp",
        "relay",
        include_str!("fixtures/cpp-verification/declaration-identity/identity.cpp"),
    );
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let lowered = lower_import(&import).unwrap();
    let helpers = &import.export().reachable_functions;
    assert_eq!(helpers.len(), 6);
    let names = helpers
        .iter()
        .map(|function| lowered.contract_name(&function.declaration_id).unwrap())
        .collect::<std::collections::BTreeSet<_>>();
    assert_eq!(names.len(), helpers.len());
    assert_eq!(lowered.kernel_function().name(), "relay");
    let mut sidecar = String::from("verifying \"identity.cpp\";\n");
    for helper in helpers {
        let [
            CppStatement::Return {
                value: CppExpression::IntegerLiteral { value, .. },
                ..
            },
        ] = helper.body.as_slice()
        else {
            panic!("constant helper body: {:?}", helper.body);
        };
        let name = lowered.contract_name(&helper.declaration_id).unwrap();
        let parameter_type = match helper.parameters[0].value_type {
            CppType::Integer {
                bits: 64,
                signed: true,
                ..
            } => "int64",
            _ => "int32",
        };
        sidecar.push_str(&format!("int32 {name}({parameter_type} x) {{ ensures result == {value}; }} by {{ execute(); simp(); }}\n"));
        assert!(
            lowered
                .contract_functions()
                .iter()
                .any(|function| function.name() == name)
        );
        assert!(
            lowered
                .reachable_kernel_functions()
                .iter()
                .any(|function| function.name() == name)
        );
    }
    sidecar.push_str("int32 relay(int64 x, int64 y, int32 z) { ensures result == 76; } by { execute(); simp(); }\n");
    check_return_call_sidecar(&project, &import, &sidecar);
    let false_claim = sidecar.replace("result == 76", "result == 74");
    let path = project.directory.join("wrong.click");
    fs::write(&path, &false_claim).unwrap();
    let parsed = read_click_project(&path, &false_claim).unwrap();
    assert!(verify_program_prepared_project(&parsed, &import).is_err());
}

#[test]
fn qualified_namespace_selection_has_an_ordinary_readable_contract_name() {
    let project = Project::with_fixture(
        "namespace.cpp",
        "A::Nested::echo",
        "namespace A { namespace Nested { int echo(int x) noexcept { return x; } } } int echo(int x) noexcept { return 3; }",
    );
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let lowered = lower_import(&import).unwrap();
    assert_eq!(lowered.kernel_function().name(), "A_Nested_echo");
    check_return_call_sidecar(
        &project,
        &import,
        "verifying \"namespace.cpp\"; int32 A_Nested_echo(int32 x) { ensures result == x; } by { execute(); simp(); }",
    );
}

#[test]
fn selected_function_collision_uses_the_same_identity_binding_as_its_helper() {
    let project = Project::with_fixture(
        "selected.cpp",
        "H_same",
        "struct H { static int same(int x) noexcept { return 5; } }; int H_same(int x) noexcept { return H::same(x); }",
    );
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let lowered = lower_import(&import).unwrap();
    let selected = lowered
        .contract_name(&import.export().function.declaration_id)
        .unwrap();
    let helper = lowered
        .contract_name(&import.export().reachable_functions[0].declaration_id)
        .unwrap();
    assert_ne!(selected, helper);
    assert_eq!(lowered.kernel_function().name(), selected);
    let sidecar = format!(
        "verifying \"selected.cpp\"; int32 {helper}(int32 x) {{ ensures result == 5; }} by {{ execute(); simp(); }} int32 {selected}(int32 x) {{ ensures result == 5; }} by {{ execute(); simp(); }}"
    );
    check_sidecar_tactic(&project, &import, &sidecar, Some(&format!("{selected}.")));
}

#[test]
fn anonymous_namespace_helper_has_a_valid_identity_based_contract_name() {
    let project = Project::with_fixture(
        "anonymous.cpp",
        "relay",
        "namespace { int same(int x) noexcept { return x; } } int relay(int x) noexcept { return same(x); }",
    );
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let lowered = lower_import(&import).unwrap();
    let name = lowered
        .contract_name(&import.export().reachable_functions[0].declaration_id)
        .unwrap();
    assert!(name.starts_with("__click_cpp_decl_"));
    let sidecar = format!(
        "verifying \"anonymous.cpp\"; int32 {name}(int32 x) {{ ensures result == x; }} by {{ execute(); simp(); }} int32 relay(int32 x) {{ ensures result == x; }} by {{ execute(); simp(); }}"
    );
    check_return_call_sidecar(&project, &import, &sidecar);
}

#[test]
fn bounded_constant_forests_scale_without_expanding_dependency_chains() {
    for size in [4usize, 16, 64, 256] {
        let mut cpp =
            String::from("static constexpr long long C0 = 1; static constexpr long long C1 = 3;\n");
        for index in 2..size {
            cpp.push_str(&format!(
                "static constexpr long long C{index} = 1 * C{};\n",
                index - 2
            ));
        }
        cpp.push_str(&format!(
            "long long total() noexcept {{ return C{} + C{}; }}\n",
            size - 2,
            size - 1
        ));
        let project = Project::with_fixture("forest.cpp", "total", &cpp);
        refresh_import(&project.config()).unwrap();
        let (import, validation_work) =
            click::instrumentation::measure_deterministic_work(|| load_import(&project.config()));
        let import = import.unwrap();
        assert_eq!(import.export().constants.len(), size);
        let artifact_bytes = fs::metadata(project.artifact()).unwrap().len() as usize;
        assert!(
            validation_work >= artifact_bytes && validation_work <= artifact_bytes + 8 * size + 100,
            "{size} constants: {validation_work} work for {artifact_bytes} bytes"
        );
        let (lowered, work) =
            click::instrumentation::measure_deterministic_work(|| lower_import(&import));
        lowered.unwrap();
        assert!(
            work >= size && work <= 3 * size + 32,
            "{size} constants: {work} lowering work"
        );
        check_return_call_sidecar(
            &project,
            &import,
            "verifying \"forest.cpp\"; int64 total() { ensures result == 4i64; } by { execute(); simp(); }",
        );
    }
}

#[test]
fn record_inventories_and_function_lowering_share_indexes_across_sizes() {
    for size in [2usize, 8, 32, 128] {
        let mut cpp = String::new();
        let mut sidecar = String::from("verifying \"records.cpp\";\n");
        for index in 0..size {
            cpp.push_str(&format!("struct R{index} {{ int value; }}; int read{index}(int x) noexcept {{ R{index} local{{x}}; return local.value; }}\n"));
            sidecar.push_str(&format!("int32 read{index}(int32 x) {{ ensures result == x; }} by {{ execute(); simp(); }}\n"));
        }
        cpp.push_str("int relay(int x) noexcept {\n");
        for index in 0..size {
            cpp.push_str(&format!("int y{index} = read{index}(x);\n"));
        }
        cpp.push_str(&format!("return y{}; }}\n", size - 1));
        sidecar
            .push_str("int32 relay(int32 x) { ensures result == x; } by { execute(); simp(); }\n");
        let project = Project::with_fixture("records.cpp", "relay", &cpp);
        refresh_import(&project.config()).unwrap();
        let import = load_import(&project.config()).unwrap();
        assert_eq!(import.export().records.len(), size);
        let (lowered, work) =
            click::instrumentation::measure_deterministic_work(|| lower_import(&import));
        let lowered = lowered.unwrap();
        assert_eq!(lowered.record_layouts().len(), size);
        assert!(
            work >= size && work <= 24 * size + 32,
            "{size} records/functions: {work} work"
        );
        // Small graphs exercise certificates and audit; larger graphs measure the
        // frontend inventory representation without duplicating every proof run.
        if size <= 8 {
            check_return_call_sidecar(&project, &import, &sidecar);
            if size == 2 {
                let false_claim = sidecar.replace(
                    "int32 relay(int32 x) { ensures result == x; }",
                    "int32 relay(int32 x) { requires x == 7; ensures result == 8; }",
                );
                let path = project.directory.join("wrong.click");
                fs::write(&path, &false_claim).unwrap();
                let parsed = read_click_project(&path, &false_claim).unwrap();
                assert!(verify_program_prepared_project(&parsed, &import).is_err());
            }
        }
    }
}

#[test]
fn exporter_reports_named_inventory_budgets_and_keeps_outputs_atomic() {
    let declarations = (0..1025usize)
        .map(|index| {
            if index == 0 {
                "static constexpr long long C0 = 1;\n".to_owned()
            } else {
                format!(
                    "static constexpr long long C{index} = 1 * C{};\n",
                    index - 1
                )
            }
        })
        .collect::<String>();
    let project = Project::with_fixture(
        "budget.cpp",
        "total",
        &format!("{declarations}long long total() noexcept {{ return C1024; }}"),
    );
    let error = refresh_import(&project.config()).unwrap_err();
    assert!(
        error.contains("artifact budget exhausted: constant declarations"),
        "{error}"
    );
    assert!(!project.artifact().exists());
    assert!(!project.lock().exists());
}

#[test]
fn exporter_bounds_record_and_function_discovery_independently() {
    for (size, records, expected) in [
        (257usize, true, "record declarations"),
        (1024, false, "function declarations"),
    ] {
        let mut cpp = String::new();
        for index in 0..size {
            if records {
                cpp.push_str(&format!("struct R{index} {{ int value; }}; int f{index}(int x) noexcept {{ R{index} local{{x}}; return local.value; }}\n"));
            } else {
                cpp.push_str(&format!("int f{index}(int x) noexcept {{ return x; }}\n"));
            }
        }
        cpp.push_str("int relay(int x) noexcept {\n");
        for index in 0..size {
            cpp.push_str(&format!("f{index}(x);\n"));
        }
        cpp.push_str("return x; }");
        let project = Project::with_fixture("budget.cpp", "relay", &cpp);
        let error = refresh_import(&project.config()).unwrap_err();
        assert!(
            error.contains(&format!("artifact budget exhausted: {expected}")),
            "{error}"
        );
        assert!(!project.artifact().exists());
        assert!(!project.lock().exists());
    }
}

#[test]
fn distinct_record_layouts_keep_field_widths_offsets_and_ownership() {
    let project = Project::with_fixture(
        "layouts.cpp",
        "choose",
        "struct First { int value; }; struct Second { int padding; long long value; }; long long choose(First& first, Second& second) noexcept { first.value = 7; return second.value; }",
    );
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    assert_eq!(import.export().records.len(), 2);
    let first = import
        .export()
        .records
        .iter()
        .find(|record| record.name == "First")
        .unwrap();
    let second = import
        .export()
        .records
        .iter()
        .find(|record| record.name == "Second")
        .unwrap();
    assert_eq!(
        (
            first.size_bytes,
            first.fields[0].offset_bytes,
            first.fields[0].size_bytes
        ),
        (4, 0, 4)
    );
    assert_eq!(
        (
            second.size_bytes,
            second.fields[1].offset_bytes,
            second.fields[1].size_bytes
        ),
        (16, 8, 8)
    );
    let sidecar = "verifying \"layouts.cpp\"; int64 choose(struct First* first, struct Second* second) { owns first->value; owns second->value; ensures first->value == 7; ensures result == old(second->value); ensures second->value == old(second->value); } by { execute(); simp(); }";
    check_return_call_sidecar(&project, &import, sidecar);
    let missing_authority = sidecar.replace("owns second->value;", "");
    let path = project.directory.join("wrong.click");
    fs::write(&path, &missing_authority).unwrap();
    let parsed = read_click_project(&path, &missing_authority).unwrap();
    assert!(verify_program_prepared_project(&parsed, &import).is_err());
}
