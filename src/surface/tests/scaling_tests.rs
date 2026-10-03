use super::*;

#[test]
fn execution_target_resource_scope_parsing_is_linear_in_selected_declarations() {
    let samples = [1, 8, 32, 128].map(|count| {
        let mut source = "resource Counter() { field revision: int32; }\n".to_string();
        for index in 0..count {
            source.push_str(&format!("theorem lift{index}(callback: int32 (*)()) executes callback() {{ requires C{index}(callback); ensures C{index}(callback) as {{ cell: k }} by {{ step(C{index}(k)); simp(); }} }}\n"));
        }
        for index in 0..count {
            source.push_str(&format!("contract C{index}(cell: Counter()) for int32() {{ owns cell; ensures result == 0; }}\n"));
        }
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::surface::parse(&source).expect("forward target proof scopes parse")
        });
        (count, work)
    });
    assert!(samples[0].1 > 0);
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1 * (pair[1].0 / pair[0].0),
            "{samples:?}"
        );
    }
}

#[test]
fn nested_conjunction_body_parsing_uses_small_frames_and_linear_work() {
    std::thread::Builder::new()
        .name("small-stack-proof-body-parser".into())
        .stack_size(7 * 256 * 1024)
        .spawn(|| {
            let samples = [2, 4, 8, 16].map(|depth| {
                let mut body = "have 0 == 0 by { normalize(); } normalize();".to_string();
                for _ in 0..depth {
                    body = format!("both {{ {body} }} and {{ normalize(); }}");
                }
                let source = format!("theorem nested() {{ ensures 0 == 0 by {{ {body} }} }}");
                let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                    crate::surface::parse(&source)
                        .expect("nested proof bodies should parse on the ordinary stack")
                });
                work
            });
            for pair in samples.windows(2) {
                assert!(
                    pair[1] <= pair[0].saturating_mul(2).saturating_add(8),
                    "{samples:?}"
                );
            }
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn explicit_constructor_unfold_has_near_linear_nested_match_work() {
    let mut samples = Vec::new();
    for size in [2, 4, 8, 16, 32, 64] {
        let mut body = "n".to_string();
        for index in 0..size {
            body = format!(
                "match Nat::Zero {{ Nat::Zero => {body}, Nat::Succ(unused_{index}) => n, }}"
            );
        }
        let source = format!(
            "function nested(n: Nat) -> Nat {{ {body} }}\n\
            theorem nested_result(n: Nat) {{ ensures nested(n) == n by {{ unfold(nested(n)); normalize(); }} }}"
        );
        if size > parser::MATCH_NESTING_LIMIT {
            let error = verify_click_theorems(&source)
                .expect_err("deep syntax must fail locally, not overflow the stack");
            assert!(
                error
                    .message()
                    .contains("match nesting exceeds Click's supported depth of 16"),
                "{error:?}"
            );
            continue;
        }
        let (result, sample) = scaling_sample(size, || verify_click_theorems(&source));
        result.expect("explicit constructor matches unfold and check");
        samples.push(sample);
    }
    assert_near_linear_scaling("nested constructor unfolding", &samples);
}

#[test]
fn symbolic_integer_match_lowering_has_near_linear_width_work() {
    let mut samples = Vec::new();
    for width in [8, 16, 32, 64] {
        let variants = (0..width)
            .map(|index| format!("V{index}(Integer)"))
            .collect::<Vec<_>>()
            .join(", ");
        let arms = (0..width)
            .map(|index| {
                format!(
                    "Choice::V{index}(value_{index}) => match Box::Wrapped(value_{index}) {{ Box::Empty => 0, Box::Wrapped(inner_{index}) => inner_{index}, }}"
                )
            })
            .collect::<Vec<_>>()
            .join(",\n                ");
        let source = format!(
            "spec enum Box {{ Empty, Wrapped(Integer) }}\n\
             spec enum Choice {{ {variants} }}\n\
             theorem nested(value: Integer) {{\n\
                 ensures match Choice::V0(value) {{\n\
                     {arms}\n\
                 }} == value by {{ normalize(); }}\n\
             }}"
        );
        let (result, sample) = scaling_sample(width, || verify_click_theorems(&source));
        result.unwrap_or_else(|error| {
            panic!(
                "width {width} symbolic Integer match failed: {}",
                error.message()
            )
        });
        samples.push(sample);
    }
    assert_near_linear_scaling("symbolic Integer match lowering", &samples);
}

#[test]
fn symbolic_integer_match_lowering_has_near_linear_nested_depth_work() {
    let mut samples = Vec::new();
    for depth in [2, 4, 8, 16, 32, 64] {
        let mut body = "0".to_string();
        for index in 0..depth {
            body = format!(
                "match Box::Empty {{ Box::Empty => {body}, Box::Wrapped(inner_{index}) => inner_{index}, }}"
            );
        }
        let source = format!(
            "spec enum Box {{ Empty, Wrapped(Integer) }}\n\
             theorem nested() {{ ensures {body} == 0 by {{ normalize(); }} }}"
        );
        if depth > parser::MATCH_NESTING_LIMIT {
            let error = verify_click_theorems(&source)
                .expect_err("deep Integer matches must fail at the parser boundary");
            assert!(
                error
                    .message()
                    .contains("match nesting exceeds Click's supported depth of 16"),
                "{error:?}"
            );
            continue;
        }
        let (result, sample) = scaling_sample(depth, || verify_click_theorems(&source));
        result.unwrap_or_else(|error| {
            panic!(
                "depth {depth} symbolic Integer match failed: {}",
                error.message()
            )
        });
        samples.push(sample);
    }
    assert_near_linear_scaling("symbolic Integer nested-match lowering", &samples);
}

#[test]
fn parametric_theorem_declarations_have_near_linear_checking_work() {
    let mut samples = Vec::new();
    for size in [16, 32, 64, 128] {
        let source = (0..size).map(|index| format!(
            "theorem reflexive_{index}<T>(x: T) {{ ensures x == x by {{ normalize(); }} }}\n"
        )).collect::<String>();
        let (verified, sample) = scaling_sample(size, || verify_click_theorems(&source));
        assert_eq!(
            verified.expect("every unused generic proof checks").len(),
            size
        );
        samples.push(sample);
    }
    assert_near_linear_scaling("parametric declarations", &samples);
}

#[test]
fn transitive_module_chains_prepare_with_near_linear_deterministic_work() {
    let mut samples = Vec::new();
    for size in [4, 8, 16, 32] {
        let mut modules = Vec::new();
        modules.push(ClickModuleSource::new(
            "module_0.click",
            "function value_0(x: int32) -> int32 { x }",
            [],
        ));
        for index in 1..size {
            modules.push(ClickModuleSource::new(
                format!("module_{index}.click"),
                format!(
                    "import \"module_{}.click\"; function value_{index}(x: int32) -> int32 {{ value_{}(x) }}",
                    index - 1,
                    index - 1
                ),
                [format!("module_{}.click", index - 1)],
            ));
        }
        modules.push(ClickModuleSource::new(
            "entry.click",
            format!("import \"module_{}.click\";", size - 1),
            [format!("module_{}.click", size - 1)],
        ));
        let project = ClickProject::new("entry.click", modules);
        let (resolved, sample) = scaling_sample(size, || resolve_click_project(&project, &[]));
        assert_eq!(
            resolved
                .expect("the module chain should resolve")
                .click_function_definitions()
                .len(),
            size
        );
        samples.push(sample);
    }
    assert_near_linear_scaling("transitive Click module chains", &samples);
}

#[test]
fn module_diamonds_prepare_shared_interfaces_once_per_selected_graph() {
    let mut samples = Vec::new();
    for width in [4, 8, 16, 32] {
        let mut modules = vec![ClickModuleSource::new(
            "shared.click",
            "spec enum SharedValue { Value(int32), }",
            [],
        )];
        let mut entry_imports = Vec::new();
        let mut entry_source = String::new();
        for index in 0..width {
            let identity = format!("branch_{index}.click");
            entry_source.push_str(&format!("import \"{identity}\";\n"));
            entry_imports.push(identity.clone());
            modules.push(ClickModuleSource::new(
                identity,
                format!(
                    "import \"shared.click\"; function branch_{index}(x: SharedValue) -> SharedValue {{ x }}"
                ),
                ["shared.click".to_string()],
            ));
        }
        modules.push(ClickModuleSource::new(
            "entry.click",
            entry_source,
            entry_imports,
        ));
        let project = ClickProject::new("entry.click", modules);
        let (resolved, sample) = scaling_sample(width, || resolve_click_project(&project, &[]));
        let resolved = resolved.expect("the module diamond should resolve");
        assert_eq!(resolved.algebraic_type_definitions().len(), 1);
        assert_eq!(resolved.click_function_definitions().len(), width);
        samples.push(sample);
    }
    assert_near_linear_scaling("Click module diamonds", &samples);
}

#[test]
fn shared_imported_proof_bodies_stay_unselected_across_entry_scaling() {
    let mut samples = Vec::new();
    for entries in [2, 4, 8, 16] {
        let (results, sample) = scaling_sample(entries, || {
            super::super::proof::PROVED_THEOREMS.with(|proved| proved.borrow_mut().clear());
            for index in 0..entries {
                let project = ClickProject::new(
                    format!("entry_{index}.click"),
                    [
                        ClickModuleSource::new(
                            "shared.click",
                            "theorem shared_false(x: int32) { ensures x == x + 1 by simp; }",
                            [],
                        ),
                        ClickModuleSource::new(
                            format!("entry_{index}.click"),
                            format!(
                                "import \"shared.click\"; theorem local_{index}(x: int32) {{ ensures x == x + 1 by {{ apply(shared_false(x)); assumption(); }} }}"
                            ),
                            ["shared.click".to_string()],
                        ),
                    ],
                );
                verify_c0_project(&project, &[])?;
            }
            Ok::<_, ClickError>(())
        });
        results.expect("every selected entry should assume the shared theorem statement");
        super::super::proof::PROVED_THEOREMS.with(|proved| {
            let proved = proved.borrow();
            assert_eq!(proved.len(), entries);
            assert!(proved.iter().all(|name| name.starts_with("local_")));
        });
        samples.push(sample);
    }
    assert_near_linear_scaling("shared imported theorem across selected entries", &samples);
}

#[derive(Clone, Debug)]
struct ScalingSample {
    size: usize,
    work: usize,
    named_work: BTreeMap<String, usize>,
}

fn scaling_sample<R>(size: usize, operation: impl FnOnce() -> R) -> (R, ScalingSample) {
    let ((result, work), events) = crate::instrumentation::collect(|| {
        crate::instrumentation::measure_deterministic_work(operation)
    });
    let mut named_work = BTreeMap::<String, usize>::new();
    for event in events {
        let (name, work) = match event {
            crate::instrumentation::VerificationEvent::OperationFinished { name, work, .. } => {
                (format!("operation `{name}`"), work)
            }
            crate::instrumentation::VerificationEvent::TacticFinished { tactic, work, .. } => (
                format!("{} tactic `{}`", tactic.class, tactic.tactic_name),
                work,
            ),
            _ => continue,
        };
        *named_work.entry(name).or_default() += work;
    }
    (
        result,
        ScalingSample {
            size,
            work,
            named_work,
        },
    )
}

fn named_growth_diagnostic(samples: &[ScalingSample]) -> String {
    let mut names = BTreeSet::new();
    for sample in samples {
        names.extend(sample.named_work.keys().cloned());
    }
    let mut curves = names
        .into_iter()
        .map(|name| {
            let work = samples
                .iter()
                .map(|sample| sample.named_work.get(&name).copied().unwrap_or(0))
                .collect::<Vec<_>>();
            (work.last().copied().unwrap_or(0), name, work)
        })
        .filter(|(last, _, _)| *last != 0)
        .collect::<Vec<_>>();
    curves.sort_by(|left, right| right.0.cmp(&left.0).then_with(|| left.1.cmp(&right.1)));
    curves
        .into_iter()
        .take(8)
        .map(|(_, name, work)| format!("{name}: {work:?}"))
        .collect::<Vec<_>>()
        .join(", ")
}

/// Accepts the fixed-cost noise present in a complete verifier transaction
/// while rejecting a sustained quadratic curve. Four geometric sizes give
/// three adjacent ratios; requiring the two largest to stay below 3x catches
/// quadratic growth (4x per doubling) without encoding host timing.
fn near_linear_scaling(samples: &[ScalingSample]) -> bool {
    if samples.len() < 4 {
        return false;
    }
    for pair in samples.windows(2) {
        if pair[1].size != pair[0].size * 2 {
            return false;
        }
    }
    samples
        .windows(2)
        .skip(samples.len().saturating_sub(3))
        .all(|pair| pair[1].work <= pair[0].work.saturating_mul(3))
}

fn assert_near_linear_scaling(axis: &str, samples: &[ScalingSample]) {
    assert!(
        near_linear_scaling(samples),
        "{axis}: deterministic work grows faster than the simple-verification contract: {samples:?}; named work: {}",
        named_growth_diagnostic(samples),
    );
}

#[test]
fn bounded_statement_successor_exclusion_ignores_unrelated_ambient_facts() {
    let (replace_source, caller_source, base_click) =
        super::contract_tests::result_case_split_sources();
    let insertion = "                open(allocated_cell(owner)) {\n                }\n";
    let mut samples = Vec::new();
    let mut exclusion_work = Vec::new();
    for size in [8, 16, 32, 64] {
        let unrelated = (0..size)
            .map(|index| {
                format!(
                    "                have 0 <= {index} by {{\n                    normalize();\n                }}\n"
                )
            })
            .collect::<String>();
        let click_source = base_click.replacen(insertion, &format!("{insertion}{unrelated}"), 1);
        assert_ne!(
            click_source, base_click,
            "the ambient facts were not inserted"
        );
        let (verified, sample) = scaling_sample(size, || {
            verify_c0_sources(
                &click_source,
                &[
                    ("replace_allocated_cell.c", replace_source),
                    ("replace_then_branch.c", caller_source),
                ],
            )
        });
        verified.expect("the bounded successor product should ignore unrelated ambient facts");
        exclusion_work.push(
            sample
                .named_work
                .get("operation `bounded statement-successor exclusion`")
                .copied()
                .unwrap_or(0),
        );
        samples.push(sample);
    }
    assert!(
        exclusion_work.iter().all(|work| *work == exclusion_work[0]),
        "lane-exclusion work changed with unrelated ambient facts: {exclusion_work:?}"
    );
    assert_near_linear_scaling("bounded statement-successor ambient facts", &samples);
}

/// Lowering a specification `if` folds a literally constant condition and
/// otherwise lowers both branches. It reads no ambient fact, so checking a
/// requirement that contains one must cost the same whatever else the caller
/// happens to know. The requirement here is a conditional the caller cannot
/// settle, which is the case a branch-deciding lowering would have searched
/// for.
#[test]
fn specification_conditional_lowering_ignores_unrelated_ambient_facts() {
    let mut samples = Vec::new();
    let mut requirement_work = Vec::new();
    for size in [8, 16, 32, 64] {
        let unrelated = (0..size)
            .map(|index| format!("    have 0 <= {index} by {{\n        normalize();\n    }}\n"))
            .collect::<String>();
        let click_source = format!(
            "verifying \"conditional_callee.c\";\n\
             verifying \"conditional_caller.c\";\n\
             \n\
             int32 conditional_callee(int32 flag, int32 left, int32 right) {{\n    \
                 requires (if flag != 0 {{ left }} else {{ right }}) == 7;\n    \
                 ensures result == 0;\n\
             }} by auto;\n\
             \n\
             int32 conditional_caller(int32 flag, int32 left, int32 right) {{\n    \
                 requires (if flag != 0 {{ left }} else {{ right }}) == 7;\n    \
                 ensures result == 0;\n\
             }} by {{\n{unrelated}    execute();\n    simp();\n}}\n"
        );
        let (verified, sample) = scaling_sample(size, || {
            verify_c0_sources(
                &click_source,
                &[
                    (
                        "conditional_callee.c",
                        "int32 conditional_callee(int32 flag, int32 left, int32 right) {\n    return 0;\n}\n",
                    ),
                    (
                        "conditional_caller.c",
                        "int32 conditional_caller(int32 flag, int32 left, int32 right) {\n    return conditional_callee(flag, left, right);\n}\n",
                    ),
                ],
            )
        });
        verified.expect("a conditional requirement should check under unrelated ambient facts");
        requirement_work.push(
            sample
                .named_work
                .get("operation `verified call requirement checking`")
                .copied()
                .unwrap_or(0),
        );
        samples.push(sample);
    }
    assert!(
        requirement_work[0] > 0,
        "the conditional requirement was never checked at the call site: {requirement_work:?}"
    );
    assert!(
        requirement_work
            .iter()
            .all(|work| *work == requirement_work[0]),
        "conditional requirement checking grew with unrelated ambient facts: {requirement_work:?}"
    );
    assert_near_linear_scaling("specification conditional ambient facts", &samples);
}

/// A verified call publishes its callee's ensures. An ensure written as an
/// implication keeps its premises unless each is exactly available at the
/// call, so what the caller happens to know elsewhere cannot change what that
/// publication costs. The premise here is never available, the case that used
/// to end in the general prover's whole-context fallbacks; the call context
/// really does grow along this axis (9 to 66 condition facts over the four
/// sizes), while ensure publication measures 71 units at every one of them.
#[test]
fn verified_call_ensure_premises_ignore_unrelated_ambient_facts() {
    let mut samples = Vec::new();
    let mut ensure_work = Vec::new();
    for size in [8, 16, 32, 64] {
        let unrelated = (0..size)
            .map(|index| {
                format!(
                    "    have {index} <= count + {index} by {{\n        \
                     arithmetic() using {{\n            0 <= count;\n            \
                     count <= 1000;\n        }}\n    }}\n"
                )
            })
            .collect::<String>();
        let click_source = format!(
            "verifying \"ensure_premise_callee.c\";\n\
             verifying \"ensure_premise_scaling_caller.c\";\n\
             \n\
             int32 ensure_premise_callee(int32 flag, int32* cell) {{\n    \
                 owns cell[0..1];\n    \
                 ensures result == 0;\n    \
                 ensures flag > 0 implies cell[0] == 1;\n\
             }} by {{\n    \
                 if flag > 0 {{\n        execute();\n        simp();\n    \
                 }} else {{\n        execute();\n        simp();\n    }}\n\
             }}\n\
             \n\
             int32 ensure_premise_scaling_caller(int32 count, int32* cell) {{\n    \
                 requires 0 <= count;\n    \
                 requires count <= 1000;\n    \
                 owns cell[0..1];\n    \
                 ensures result == 0;\n\
             }} by {{\n{unrelated}    execute();\n    simp();\n}}\n"
        );
        let (verified, sample) = scaling_sample(size, || {
            verify_c0_sources(
                &click_source,
                &[
                    (
                        "ensure_premise_callee.c",
                        "int32 ensure_premise_callee(int32 flag, int32* cell) {\n    \
                         if (flag > 0) {\n        cell[0] = 1;\n    }\n    return 0;\n}\n",
                    ),
                    (
                        "ensure_premise_scaling_caller.c",
                        "int32 ensure_premise_scaling_caller(int32 count, int32* cell) {\n    \
                         int32 status = ensure_premise_callee(count, cell);\n    \
                         return status;\n}\n",
                    ),
                ],
            )
        });
        verified.unwrap_or_else(|error| {
            panic!(
                "size {size} ensure-premise scaling fixture failed: {}",
                error.message()
            )
        });
        ensure_work.push(
            sample
                .named_work
                .get("operation `verified call ensure lowering`")
                .copied()
                .unwrap_or(0),
        );
        samples.push(sample);
    }
    assert!(
        ensure_work[0] > 0,
        "the callee's ensures were never published at the call site: {ensure_work:?}"
    );
    assert!(
        ensure_work.iter().all(|work| *work == ensure_work[0]),
        "publishing callee ensures grew with unrelated ambient facts: {ensure_work:?}"
    );
    assert_near_linear_scaling("verified call ensure premises", &samples);
}

fn unrelated_identity_project(function_count: usize) -> (Vec<(String, String)>, String) {
    let mut c_sources = Vec::new();
    let mut click_source = String::new();
    for index in 0..function_count {
        let filename = format!("scaling_{index}.c");
        c_sources.push((
            filename.clone(),
            format!("int32 scaling_identity_{index}(int32 x) {{ return x; }}\n"),
        ));
        click_source.push_str(&format!("verifying \"{filename}\";\n"));
    }
    click_source.push('\n');
    for index in 0..function_count {
        click_source.push_str(&format!(
            "int32 scaling_identity_{index}(int32 x) {{\n    ensures result == x;\n}} by {{\n    step();\n    normalize();\n}}\n\n"
        ));
    }
    (c_sources, click_source)
}

fn target_with_unrelated_theorems(theorem_count: usize) -> String {
    let mut click_source = String::from("verifying \"target.c\";\n\n");
    for index in 0..theorem_count {
        click_source.push_str(&format!(
            "theorem unrelated_{index}(x: int32) {{\n    requires x == x;\n    ensures x == x by {{ assumption(); }}\n}}\n\n"
        ));
    }
    click_source.push_str(
        "int32 scaling_target(int32 x) {\n    ensures result == x;\n} by {\n    step();\n    normalize();\n}\n",
    );
    click_source
}

fn straight_line_project(statement_count: usize, snapshot_claim: bool) -> (String, String) {
    let mut c_source = String::from("int32 straight_line(int32 x) {\n");
    for _ in 0..statement_count {
        c_source.push_str("    x = x;\n");
    }
    c_source.push_str("    return x;\n}\n");

    let ensure = if snapshot_claim {
        "result == at(statement(0).entry, x)"
    } else {
        "result == x"
    };
    let mut click_source = format!(
        "verifying \"straight.c\";\n\nint32 straight_line(int32 x) {{\n    ensures {ensure};\n}} by {{\n"
    );
    for _ in 0..=statement_count {
        click_source.push_str("    step();\n");
    }
    click_source.push_str("    normalize();\n}\n");
    (c_source, click_source)
}

#[derive(Clone, Copy, Debug)]
enum LoadAxis {
    /// Each statement loads a new cell: one load variable each.
    DistinctCells,
    /// Every statement reloads `data[0]` from an unchanged memory.
    OneCell,
    /// Every statement reloads `data[0]` and stores `data[1]`: the reload
    /// finds its name again through a store DAG that grows with the proof.
    OneCellAcrossStores,
}

/// A straight line of loads from one array along one [`LoadAxis`].
/// Each statement is an explicit `step()`, so the certificate names each
/// load and the final claim compares the last local against the array cell
/// named at the function exit.
fn load_variable_project(statement_count: usize, axis: LoadAxis) -> (String, String) {
    let mut c_source =
        String::from("int32 load_line(int32 data[], int32 length) {\n    int32 x;\n");
    for index in 0..statement_count {
        match axis {
            LoadAxis::DistinctCells => c_source.push_str(&format!("    x = data[{index}];\n")),
            LoadAxis::OneCell => c_source.push_str("    x = data[0];\n"),
            LoadAxis::OneCellAcrossStores => {
                c_source.push_str("    x = data[0];\n    data[1] = x;\n");
            }
        }
    }
    c_source.push_str("    return x;\n}\n");
    let last = match axis {
        LoadAxis::DistinctCells => statement_count - 1,
        LoadAxis::OneCell | LoadAxis::OneCellAcrossStores => 0,
    };
    let (permission, statements) = match axis {
        LoadAxis::DistinctCells | LoadAxis::OneCell => ("views data[0..length];", statement_count),
        LoadAxis::OneCellAcrossStores => (
            "consumes data[0..length];\n    produces data[0..length];",
            2 * statement_count,
        ),
    };
    let mut click_source = format!(
        "verifying \"load_line.c\";\n\nint32 load_line(int32 data[], int32 length) {{\n    requires {statement_count} <= length;\n    requires 2 <= length;\n    requires ((uint32)length) <= 1073741823u32;\n    {permission}\n    ensures result == data[{last}];\n}} by {{\n"
    );
    let statement_count = statements;
    for _ in 0..=statement_count + 1 {
        click_source.push_str("    step();\n");
    }
    click_source.push_str("    normalize();\n");
    if matches!(axis, LoadAxis::OneCellAcrossStores) {
        // The `produces` claim has no simple closer and takes the one smart
        // tactic in this fixture.
        click_source.push_str("    simp();\n");
    }
    click_source.push_str("}\n");
    (c_source, click_source)
}

fn theorem_with_unrelated_exact_facts(fact_count: usize) -> String {
    let mut parameters = String::from("target: int32");
    let mut requirements = String::from("    requires target == 7;\n");
    for index in 0..fact_count {
        parameters.push_str(&format!(", unrelated_{index}: int32"));
        requirements.push_str(&format!(
            "    requires unrelated_{index} == {};\n",
            index as i32
        ));
    }
    format!(
        "theorem exact_fact_scaling({parameters}) {{\n{requirements}    ensures target == 7 by {{ assumption(); }}\n}}\n"
    )
}

/// A transitive order goal needs exactly two of its ambient conditions, so it
/// reaches the paired-candidate phase of condition-certificate search rather
/// than the single-candidate phase.
fn order_chain_theorem_with_unrelated_conditions(fact_count: usize) -> String {
    let mut parameters = String::from("low: int32, middle: int32, high: int32");
    let mut requirements =
        String::from("    requires low < middle;\n    requires middle < high;\n");
    for index in 0..fact_count {
        parameters.push_str(&format!(", unrelated_{index}: int32"));
        requirements.push_str(&format!(
            "    requires unrelated_{index} < {};\n",
            index as i32 + 1_000
        ));
    }
    format!(
        "theorem order_chain_scaling({parameters}) {{\n{requirements}    ensures low < high by {{ simp(); }}\n}}\n"
    )
}

fn function_with_unrelated_facts(fact_count: usize, proof: &str) -> (String, String) {
    let c_source = "int32 exact_fact_target(int32 target) { return target; }\n".to_string();
    let mut click_source = String::from(
        "verifying \"exact_fact_target.c\";\n\nint32 exact_fact_target(int32 target) {\n    requires target == 7;\n",
    );
    for index in 0..fact_count {
        click_source.push_str(&format!("    requires target != {};\n", index + 100));
    }
    click_source.push_str("    ensures result == 7;\n} by {\n");
    click_source.push_str(proof);
    click_source.push_str("}\n");
    (c_source, click_source)
}

/// Distinct surface forms of one kernel fact, each of constant size, so the
/// source grows linearly with `form_count`. Form `k` wraps `target` in a
/// fixed number of `+ 0` additions and the bits of `k` choose which side each
/// zero is on, so every form up to 32 is a different nesting.
fn theorem_with_many_forms(form_count: usize) -> String {
    const ADDITIONS: usize = 5;
    assert!(form_count <= 1 << ADDITIONS, "forms must stay distinct");
    let mut requirements = String::new();
    for form in 0..form_count {
        let mut expression = "target".to_string();
        for bit in 0..ADDITIONS {
            expression = if form >> bit & 1 == 1 {
                format!("(0 + {expression})")
            } else {
                format!("({expression} + 0)")
            };
        }
        requirements.push_str(&format!("    requires {expression} == 7;\n"));
    }
    format!(
        "theorem surface_form_scaling(target: int32) {{\n{requirements}    ensures target == 7 by {{ assumption(); }}\n}}\n"
    )
}

fn grouped_claim_project(claim_count: usize) -> (String, String) {
    let c_source = "int32 shared_claims(int32 x) { return x; }\n".to_string();
    let mut click_source =
        String::from("verifying \"shared_claims.c\";\n\nint32 shared_claims(int32 x) {\n");
    for _ in 0..claim_count {
        click_source.push_str("    ensures result == x;\n");
    }
    click_source.push_str("} by {\n    step();\n    normalize();\n}\n");
    (c_source, click_source)
}

fn resource_member_project(member_count: usize) -> (String, String) {
    let c_source = "int32 preserve_bundle(int32 p[]) { return 0; }\n".to_string();
    let mut click_source = String::new();
    for index in 0..member_count {
        click_source.push_str(&format!(
            "abstract resource member_{index}(value: int32);\n"
        ));
    }
    click_source.push_str("\nresource bundle(p: int32*) {\n");
    for index in 0..member_count {
        click_source.push_str(&format!("    contains member_{index}({index});\n"));
    }
    click_source.push_str(
        "}\n\nverifying \"preserve_bundle.c\";\n\nint32 preserve_bundle(int32 p[]) {\n    views bundle(p);\n    ensures result == 0;\n} by {\n    step();\n    simp();\n}\n",
    );
    (c_source, click_source)
}

pub(super) fn theorem_with_parenthesized_requirement(depth: usize) -> String {
    let opening = "(".repeat(depth);
    let closing = ")".repeat(depth);
    format!(
        "theorem nested_requirement(x: int32) {{\n    requires {opening}x + 1{closing} == x + 1;\n    ensures x == x by {{ assumption(); }}\n}}\n"
    )
}

#[test]
fn parenthesized_contract_expression_parsing_has_linear_deterministic_work() {
    let samples = [2, 4, 8, 16]
        .into_iter()
        .map(|depth| {
            let source = theorem_with_parenthesized_requirement(depth);
            let (parsed, work) = crate::instrumentation::measure_deterministic_work(|| {
                parser::parse_file_items(&source)
            });
            parsed.unwrap_or_else(|error| {
                panic!(
                    "depth {depth} parenthesized requirement failed: {}",
                    error.message()
                )
            });
            ScalingSample {
                size: depth,
                work,
                named_work: BTreeMap::new(),
            }
        })
        .collect::<Vec<_>>();

    assert_near_linear_scaling("parenthesized contract-expression parsing", &samples);
}

#[test]
fn simple_unrelated_functions_have_a_deterministic_scaling_control() {
    let samples = [4, 8, 16, 32]
        .into_iter()
        .map(|size| {
            let (c_sources, click_source) = unrelated_identity_project(size);
            let source_refs = c_sources
                .iter()
                .map(|(name, source)| (name.as_str(), source.as_str()))
                .collect::<Vec<_>>();
            let (verified, sample) =
                scaling_sample(size, || verify_c0_sources(&click_source, &source_refs));
            let verified = verified.unwrap_or_else(|error| {
                panic!(
                    "size {size} simple scaling fixture failed: {}",
                    error.message()
                )
            });
            assert_eq!(verified.len(), size);
            sample
        })
        .collect::<Vec<_>>();

    assert_near_linear_scaling("unrelated simple functions", &samples);
}

#[test]
fn targeted_simple_verification_does_not_verify_unrelated_theorems() {
    let c_source = "int32 scaling_target(int32 x) { return x; }\n";
    let samples = [4, 8, 16, 32]
        .into_iter()
        .map(|size| {
            let click_source = target_with_unrelated_theorems(size);
            let (verified, sample) = scaling_sample(size, || {
                verify_c0_sources_functions(
                    &click_source,
                    &[("target.c", c_source)],
                    ["scaling_target".to_string()],
                )
            });
            let verified = verified.unwrap_or_else(|error| {
                panic!(
                    "size {size} targeted scaling fixture failed: {}",
                    error.message()
                )
            });
            assert_eq!(verified.len(), 1);
            sample
        })
        .collect::<Vec<_>>();

    assert_near_linear_scaling("target with unrelated theorems", &samples);
    // Whole-source parsing is correctly linear in the unrelated declarations;
    // the selected proof work, not that parse cost, must be independent of them.
    // Comparing total work was accidentally sensitive to whether another test
    // had already initialized the stdlib before this sample's first size.
    assert!(
        samples
            .iter()
            .all(|sample| sample.named_work == samples[0].named_work),
        "selected proof work should be insensitive to unrelated theorems: {samples:?}"
    );
}

#[test]
fn targeted_certification_keeps_an_explicit_theorem_dependency() {
    let c_source = "int32 scaling_target(int32 x) { return x; }\n";
    let click_source = r#"
        theorem equality_symmetric(first: int32, second: int32) {
            requires first == second;
            ensures second == first by { simp(); }
        }

        verifying "target.c";
        int32 scaling_target(int32 x) {
            ensures x == result;
        } by {
            step();
            apply(equality_symmetric(result, x));
            assumption();
        }
    "#;
    verify_c0_sources_functions(
        click_source,
        &[("target.c", c_source)],
        ["scaling_target".to_string()],
    )
    .expect("targeted certification should retain its applied theorem closure");
}

#[test]
fn straight_line_proof_steps_scale_near_linearly_with_retained_snapshots() {
    for snapshot_claim in [false, true] {
        let mut finalization_views = Vec::new();
        let samples = [8, 16, 32, 64]
            .into_iter()
            .map(|size| {
                let (c_source, click_source) = straight_line_project(size, snapshot_claim);
                let ((verified, view_count), sample) = scaling_sample(size, || {
                    proof::count_finalization_view_constructions(|| {
                        verify_c0_sources(&click_source, &[("straight.c", c_source.as_str())])
                    })
                });
                verified.unwrap_or_else(|error| {
                    panic!(
                        "size {size} straight-line fixture (snapshot={snapshot_claim}) failed: {}",
                        error.message()
                    )
                });
                finalization_views.push(view_count);
                sample
            })
            .collect::<Vec<_>>();
        assert!(
            finalization_views[0] > 0,
            "straight-line verification must exercise terminal finalization"
        );
        assert!(
            finalization_views
                .iter()
                .all(|count| *count == finalization_views[0]),
            "terminal-view construction must not grow with explicit steps: {finalization_views:?}"
        );
        assert_near_linear_scaling("straight-line proof steps", &samples);
    }
}

/// Load variables are content-addressed: constructing one, and finding the
/// same variable again for an unwritten cell in a later state, must cost work
/// proportional to the load and the steps it crosses, not to the number of
/// load variables or facts already in the proof.
#[test]
fn load_variable_construction_scales_near_linearly_with_statements() {
    for axis in [
        LoadAxis::DistinctCells,
        LoadAxis::OneCell,
        LoadAxis::OneCellAcrossStores,
    ] {
        let samples = [8, 16, 32, 64]
            .into_iter()
            .map(|size| {
                let (c_source, click_source) = load_variable_project(size, axis);
                let (verified, sample) = scaling_sample(size, || {
                    verify_c0_sources(&click_source, &[("load_line.c", c_source.as_str())])
                });
                verified.unwrap_or_else(|error| {
                    panic!(
                        "size {size} load-line fixture ({axis:?}) failed: {}",
                        error.message()
                    )
                });
                sample
            })
            .collect::<Vec<_>>();
        assert_near_linear_scaling(&format!("load-variable construction ({axis:?})"), &samples);
    }
}

#[test]
fn exact_assumption_scales_near_linearly_with_unrelated_ambient_facts() {
    let samples = [16, 32, 64, 128]
        .into_iter()
        .map(|size| {
            let source = theorem_with_unrelated_exact_facts(size);
            let (verified, sample) = scaling_sample(size, || verify_click_theorems(&source));
            let verified = verified.unwrap_or_else(|error| {
                panic!(
                    "size {size} exact-fact scaling fixture failed: {}",
                    error.message()
                )
            });
            assert_eq!(verified.len(), 1);
            sample
        })
        .collect::<Vec<_>>();

    assert_near_linear_scaling("exact assumption with unrelated facts", &samples);
}

#[test]
fn transitive_order_derivation_scales_near_linearly_with_unrelated_conditions() {
    let samples = [4, 8, 16, 32]
        .into_iter()
        .map(|size| {
            let source = order_chain_theorem_with_unrelated_conditions(size);
            let (verified, sample) = scaling_sample(size, || verify_click_theorems(&source));
            let verified = verified.unwrap_or_else(|error| {
                panic!(
                    "size {size} order-chain scaling fixture failed: {}",
                    error.message()
                )
            });
            assert_eq!(verified.len(), 1);
            sample
        })
        .collect::<Vec<_>>();

    assert_near_linear_scaling("transitive order derivation", &samples);
}

#[test]
fn explicit_step_scales_near_linearly_with_unrelated_ambient_facts() {
    let samples = [8, 16, 32, 64]
        .into_iter()
        .map(|size| {
            let (c_source, click_source) =
                function_with_unrelated_facts(size, "    step();\n    assumption();\n");
            let (verified, sample) = scaling_sample(size, || {
                verify_c0_sources(&click_source, &[("exact_fact_target.c", c_source.as_str())])
            });
            verified.unwrap_or_else(|error| {
                panic!(
                    "size {size} explicit-step scaling fixture failed: {}",
                    error.message()
                )
            });
            sample
        })
        .collect::<Vec<_>>();

    assert_near_linear_scaling("explicit step with unrelated facts", &samples);
}

#[test]
fn explicit_transport_scales_near_linearly_with_unrelated_ambient_facts() {
    let samples = [8, 16, 32, 64]
        .into_iter()
        .map(|size| {
            let (c_source, click_source) = function_with_unrelated_facts(
                size,
                "    step();\n    transport(target == 7, result == 7) using {\n        target == 7;\n    }\n    assumption();\n",
            );
            let (verified, sample) = scaling_sample(size, || {
                verify_c0_sources(
                    &click_source,
                    &[("exact_fact_target.c", c_source.as_str())],
                )
            });
            verified.unwrap_or_else(|error| {
                panic!(
                    "size {size} explicit-transport scaling fixture failed: {}",
                    error.message()
                )
            });
            sample
        })
        .collect::<Vec<_>>();

    assert_near_linear_scaling("explicit transport with unrelated facts", &samples);
}

/// A read of a file-scope array at a symbolic index the facts place inside
/// it is one read of the array's entry run, not a case per element: the
/// split per element recursed once per cell (a thousand elements overflowed
/// the stack) and asked each case again of the cells left. What remains
/// linear in the length is the per-statement collection of the run's slot
/// variables, which a run over a block no variable names still visits slot
/// by slot.
#[test]
fn symbolic_index_into_a_file_scope_array_scales_near_linearly_with_its_length() {
    let samples = [512, 1024, 2048, 4096]
        .into_iter()
        .map(|size| {
            let c_source =
                format!("int32 table[{size}];\nint32 get(int32 i) {{ return table[i]; }}\n");
            let click_source = format!(
                "verifying \"table.c\";\nint32 get(int32 i) {{\n    requires 0 <= i;\n    requires i < {size};\n    requires table[i] == 7;\n    ensures result == 7 by auto;\n}}\n"
            );
            let (verified, sample) = scaling_sample(size, || {
                verify_c0_sources(&click_source, &[("table.c", c_source.as_str())])
            });
            verified.unwrap_or_else(|error| {
                panic!(
                    "size {size} symbolic-index table fixture failed: {}",
                    error.message()
                )
            });
            sample
        })
        .collect::<Vec<_>>();

    assert_near_linear_scaling("symbolic index into a file-scope array", &samples);
}

#[test]
fn same_kernel_fact_with_many_surface_forms_scales_near_linearly() {
    let samples = [4, 8, 16, 32]
        .into_iter()
        .map(|size| {
            let source = theorem_with_many_forms(size);
            let (verified, sample) = scaling_sample(size, || verify_click_theorems(&source));
            verified.unwrap_or_else(|error| {
                panic!(
                    "size {size} surface-form scaling fixture failed: {}",
                    error.message()
                )
            });
            sample
        })
        .collect::<Vec<_>>();

    assert_near_linear_scaling("same kernel fact with many surface forms", &samples);
}

#[test]
fn grouped_claims_share_one_execution_with_near_linear_work() {
    let samples = [8, 16, 32, 64]
        .into_iter()
        .map(|size| {
            let (c_source, click_source) = grouped_claim_project(size);
            let (verified, sample) = scaling_sample(size, || {
                verify_c0_sources(&click_source, &[("shared_claims.c", c_source.as_str())])
            });
            let verified = verified.unwrap_or_else(|error| {
                panic!(
                    "size {size} shared-claim scaling fixture failed: {}",
                    error.message()
                )
            });
            assert_eq!(verified.len(), size);
            sample
        })
        .collect::<Vec<_>>();

    assert_near_linear_scaling("claims sharing one execution", &samples);
}

#[test]
fn composite_definition_members_keep_separation_work_compact() {
    let samples = [8, 16, 32, 64]
        .into_iter()
        .map(|size| {
            let (c_source, click_source) = resource_member_project(size);
            let (verified, sample) = scaling_sample(size, || {
                verify_c0_sources(&click_source, &[("preserve_bundle.c", c_source.as_str())])
            });
            let verified = verified.unwrap_or_else(|error| {
                panic!(
                    "size {size} resource-member scaling fixture failed: {}",
                    error.message()
                )
            });
            assert!(!verified.is_empty());
            sample
        })
        .collect::<Vec<_>>();

    // The aggregate curve also includes fixed parser and certificate costs,
    // so inspect the previously quadratic publisher directly. A zero curve
    // proves that member separation is supplied by the compact composition
    // authority instead of hidden by the fixed overhead.
    let separation_work = samples
        .iter()
        .map(|sample| {
            sample
                .named_work
                .get("operation `derived proposition: resource separate`")
                .copied()
                .unwrap_or(0)
        })
        .collect::<Vec<_>>();
    assert_eq!(
        separation_work,
        vec![0; samples.len()],
        "composite member separation must use compact composition authority, not materialized pairs"
    );
    assert_near_linear_scaling("composite definition members", &samples);
}

/// The issue-named condition-derivation curve: one two-premise order
/// derivation while unrelated condition facts grow. The premise search must
/// not rerun the prover once per candidate pair.
#[test]
fn condition_derivation_scales_near_linearly_with_unrelated_conditions() {
    use crate::kernel::{Bitvector32Term, ConditionTerm, Proposition, Variable};

    let samples = [16, 32, 64, 128]
        .into_iter()
        .map(|size| {
            let x = Bitvector32Term::Variable(Variable(430_000));
            let y = Bitvector32Term::Variable(Variable(430_001));
            let z = Bitvector32Term::Variable(Variable(430_002));
            let mut available = Vec::new();
            for index in 0..size {
                available.push(Proposition::ConditionIs(
                    ConditionTerm::Bitvector32SignedLessThan(
                        Box::new(Bitvector32Term::Variable(Variable(431_000 + index as u64))),
                        Box::new(Bitvector32Term::Constant(1_000 + index as u32)),
                    ),
                    true,
                ));
            }
            available.push(Proposition::ConditionIs(
                ConditionTerm::Bitvector32SignedLessThan(Box::new(x.clone()), Box::new(y.clone())),
                true,
            ));
            available.push(Proposition::ConditionIs(
                ConditionTerm::Bitvector32SignedLessThan(Box::new(y), Box::new(z.clone())),
                true,
            ));
            let goal = Proposition::ConditionIs(
                ConditionTerm::Bitvector32SignedLessThan(Box::new(x), Box::new(z)),
                true,
            );
            let (derivation, work) = crate::instrumentation::measure_deterministic_work(|| {
                search_condition_derivation(&goal, &available)
            });
            let derivation = derivation
                .unwrap_or_else(|error| panic!("size {size} search failed: {}", error.message()))
                .expect("the chained order facts derive the goal");
            assert!(
                !derivation.context_premises().is_empty(),
                "the derivation should name its premises"
            );
            (size, work)
        })
        .collect::<Vec<_>>();
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1.saturating_mul(3),
            "condition derivation search is superlinear: {samples:?}"
        );
    }
}

/// A chain of order facts stated against the context's iteration order,
/// beside unrelated facts. Premise selection indexes the context once and
/// then walks only the chain, so its fact visits are the context plus the
/// chain's own edges, however the links are ordered; growing the component
/// by repeated passes cost the whole context once per link.
#[test]
fn condition_premise_selection_walks_a_reversed_chain_once() {
    use crate::kernel::{Bitvector32Term, ConditionTerm, Proposition, Variable};
    use crate::surface::planning::proposition_search::{
        condition_selection_visits, reset_condition_selection_visits,
    };

    let less = |left: u64, right: u64| {
        Proposition::ConditionIs(
            ConditionTerm::Bitvector32SignedLessThan(
                Box::new(Bitvector32Term::Variable(Variable(left))),
                Box::new(Bitvector32Term::Variable(Variable(right))),
            ),
            true,
        )
    };
    let context = |links: usize, unrelated: usize, broken: Option<usize>, reversed: bool| {
        let mut available = Vec::new();
        for index in 0..unrelated {
            available.push(Proposition::ConditionIs(
                ConditionTerm::Bitvector32SignedLessThan(
                    Box::new(Bitvector32Term::Variable(Variable(441_000 + index as u64))),
                    Box::new(Bitvector32Term::Constant(1_000 + index as u32)),
                ),
                true,
            ));
        }
        let mut chain = (0..links)
            .filter(|link| broken != Some(*link))
            .map(|link| less(440_000 + link as u64, 440_001 + link as u64))
            .collect::<Vec<_>>();
        if reversed {
            chain.reverse();
        }
        available.extend(chain);
        available
    };
    const LINKS: usize = 3;
    let goal = less(440_000, 440_000 + LINKS as u64);
    let samples = [16usize, 32, 64, 128]
        .into_iter()
        .map(|unrelated| {
            let mut visits = Vec::new();
            let mut work = 0;
            for reversed in [false, true] {
                let available = context(LINKS, unrelated, None, reversed);
                reset_condition_selection_visits();
                let (derivation, units) =
                    crate::instrumentation::measure_deterministic_work(|| {
                        search_condition_derivation(&goal, &available)
                    });
                let derivation = derivation
                    .unwrap_or_else(|error| panic!("search failed: {}", error.message()))
                    .expect("the chained order facts derive the goal");
                // The certificate cites the chain and none of the unrelated
                // facts.
                assert_eq!(derivation.context_premises().len(), LINKS);
                visits.push(condition_selection_visits());
                work = work.max(units);
            }
            assert_eq!(
                visits[0], visits[1],
                "selection cost depends on the order the chain was stated in"
            );
            // A missing link leaves the goal underivable.
            let broken = context(LINKS, unrelated, Some(1), true);
            assert!(
                search_condition_derivation(&goal, &broken)
                    .unwrap_or_else(|error| panic!("search failed: {}", error.message()))
                    .is_none()
            );
            (unrelated, visits[0], work)
        })
        .collect::<Vec<_>>();
    // The search selects premises for a fixed number of trial contexts.
    // Each added unrelated fact is visited once per selection that sees it,
    // for the index, and never again while the chain is walked.
    for pair in samples.windows(2) {
        let added = pair[1].0 - pair[0].0;
        let visits = pair[1].1 - pair[0].1;
        assert_eq!(
            visits % added,
            0,
            "selection visits are not linear: {samples:?}"
        );
        assert!(
            visits / added <= 3,
            "selection walked the context more than once per trial: {samples:?}"
        );
    }
    for pair in samples.windows(2) {
        assert!(
            pair[1].2 <= pair[0].2.saturating_mul(3),
            "chained condition derivation is superlinear: {samples:?}"
        );
    }
}

/// One loadability goal beside growing numbers of loadability facts about
/// other objects. Source selection reads the goal's own block from the
/// kernel's index, so it examines the same candidates at every size; a scan
/// of the whole family visited every unrelated fact and tried each one.
#[test]
fn loadable_candidate_selection_ignores_facts_about_other_objects() {
    use crate::kernel::{
        Bitvector32Term, CMemory, Pointer, PointerOffsetTerm, Proposition, PureFactContext,
        Variable,
    };
    use crate::surface::planning::proposition_search::{
        PropositionSearch, candidate_visits, reset_candidate_visits,
    };

    let memory = CMemory::new();
    let at = |block: &str, element: u32| {
        Pointer {
            block: block.into(),
            offset: PointerOffsetTerm::Variable(Variable(450_000)),
        }
        .offset_by_bytes(4 * element)
    };
    let loadable = |base: Pointer, bytes: u32| Proposition::CMemoryLoadable {
        memory: memory.clone(),
        base,
        bytes: Bitvector32Term::Constant(bytes),
    };
    // (sources stated about the goal's object, goal, premises the
    // certificate must cite; none when the goal must stay unproved)
    let cases = [
        (
            "one covering range",
            vec![loadable(at("goal", 0), 16)],
            loadable(at("goal", 1), 4),
            Some(1),
        ),
        (
            "two adjacent ranges",
            vec![loadable(at("goal", 0), 8), loadable(at("goal", 2), 8)],
            loadable(at("goal", 0), 16),
            Some(2),
        ),
        (
            "a gap between ranges",
            vec![loadable(at("goal", 0), 8), loadable(at("goal", 3), 4)],
            loadable(at("goal", 0), 16),
            None,
        ),
    ];
    for (name, sources, goal, cited) in cases {
        let samples = [16usize, 32, 64, 128]
            .into_iter()
            .map(|unrelated| {
                let mut context = PureFactContext::new();
                for index in 0..unrelated {
                    // The same shape as a real source, about another object.
                    context =
                        context.assume_proposition(loadable(at(&format!("other{index}"), 0), 16));
                }
                for source in &sources {
                    context = context.assume_proposition(source.clone());
                }
                reset_candidate_visits();
                let (derivation, work) = crate::instrumentation::measure_deterministic_work(|| {
                    context.derive_atomic_proposition(&goal)
                });
                match cited {
                    Some(cited) => {
                        let derivation =
                            derivation.unwrap_or_else(|| panic!("{name}: goal not derived"));
                        assert_eq!(
                            derivation.context_premises().len(),
                            cited,
                            "{name}: the certificate names its source facts"
                        );
                    }
                    None => assert!(derivation.is_none(), "{name}: goal derived"),
                }
                (unrelated, candidate_visits(), work)
            })
            .collect::<Vec<_>>();
        for pair in samples.windows(2) {
            assert_eq!(
                pair[0].1, pair[1].1,
                "{name}: candidate visits grew with unrelated facts: {samples:?}"
            );
            assert!(
                pair[1].2 <= pair[0].2.saturating_mul(3),
                "{name}: derivation work is superlinear: {samples:?}"
            );
        }
        assert!(samples[0].1 <= 2 * sources.len(), "{name}: {samples:?}");
    }

    // Unrelated ranges of the goal's own block are candidates, but only as
    // single sources: a goal no pair concatenates to is refused without
    // trying every pair of them.
    let samples = [16u32, 32, 64, 128]
        .into_iter()
        .map(|unrelated| {
            let mut context = PureFactContext::new()
                .assume_proposition(loadable(at("goal", 0), 8))
                .assume_proposition(loadable(at("goal", 3), 4));
            for index in 0..unrelated {
                context = context.assume_proposition(loadable(at("goal", 1_000 + 8 * index), 4));
            }
            let goal = loadable(at("goal", 0), 16);
            let (derivation, work) = crate::instrumentation::measure_deterministic_work(|| {
                context.derive_atomic_proposition(&goal)
            });
            assert!(derivation.is_none());
            (unrelated, work)
        })
        .collect::<Vec<_>>();
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1.saturating_mul(3),
            "same-block refusal is superlinear: {samples:?}"
        );
    }
}

/// Read-defined and separation goals try the sources indexed for the goal
/// before the rest of their family: a goal those sources justify examines
/// the same candidates however many unrelated facts of the family exist.
#[test]
fn read_defined_and_separation_selection_try_indexed_sources_first() {
    use crate::kernel::{
        Bitvector32Term, CMemory, CMemoryRange, CResource, CType, ConditionTerm, Pointer,
        PointerOffsetTerm, Proposition, PureFactContext, Variable,
    };
    use crate::surface::planning::proposition_search::{
        PropositionSearch, candidate_visits, reset_candidate_visits,
    };

    let memory = CMemory::new().with_block("goal", 64);
    let read_defined = |pointer: Pointer| Proposition::CMemoryReadDefined {
        memory: memory.clone(),
        pointer,
        value_type: CType::Int32,
    };
    let at = |block: String, variable: u64| Pointer {
        block: block.as_str().into(),
        offset: PointerOffsetTerm::Variable(Variable(variable)),
    };
    let range = |base: Pointer, start: u32, end: u32| {
        CResource::Memory(CMemoryRange::new(
            base,
            Bitvector32Term::Constant(start),
            Bitvector32Term::Constant(end),
        ))
    };
    let separate =
        |block: String, variable: u64, start: u32, end: u32| Proposition::CResourceSeparate {
            left: range(at(block.clone(), variable), start, end),
            right: range(at(block, variable + 1), start, end),
        };
    let address = Pointer {
        block: "goal".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let alias = Pointer::symbolic(Variable(460_000));
    let cases: [(
        &str,
        Vec<Proposition>,
        Proposition,
        &dyn Fn(usize) -> Proposition,
    ); 2] = [
        (
            "a read defined at an alias",
            vec![
                read_defined(address.clone()),
                Proposition::ConditionIs(
                    ConditionTerm::pointer_equal(alias.clone(), address),
                    true,
                ),
            ],
            read_defined(alias),
            &|index| {
                read_defined(Pointer {
                    block: format!("other{index}").as_str().into(),
                    offset: PointerOffsetTerm::Constant(0),
                })
            },
        ),
        (
            "a separation of contained ranges",
            vec![separate("goal".to_string(), 461_000, 0, 4)],
            separate("goal".to_string(), 461_000, 1, 2),
            &|index| separate(format!("other{index}"), 462_000 + 2 * index as u64, 0, 4),
        ),
    ];
    for (name, sources, goal, unrelated_fact) in cases {
        let samples = [16usize, 32, 64, 128]
            .into_iter()
            .map(|unrelated| {
                let mut context = PureFactContext::new();
                for index in 0..unrelated {
                    context = context.assume_proposition(unrelated_fact(index));
                }
                for source in &sources {
                    context = context.assume_proposition(source.clone());
                }
                reset_candidate_visits();
                let derivation = context
                    .derive_atomic_proposition(&goal)
                    .unwrap_or_else(|| panic!("{name}: goal not derived"));
                assert!(
                    derivation
                        .context_premises()
                        .iter()
                        .all(|premise| sources.contains(premise)),
                    "{name}: the certificate cites an unrelated fact"
                );
                (unrelated, candidate_visits())
            })
            .collect::<Vec<_>>();
        for pair in samples.windows(2) {
            assert_eq!(
                pair[0].1, pair[1].1,
                "{name}: candidate visits grew with unrelated facts: {samples:?}"
            );
        }
        assert!(samples[0].1 >= 1, "{name}: the indexed route was not taken");
    }
}

/// A memory goal proved from one source cites that source and the condition
/// facts connected to it, not every ambient condition: the certificate is
/// the same size however many unrelated conditions the context holds.
#[test]
fn atomic_memory_evidence_cites_only_connected_conditions() {
    use crate::kernel::{
        Bitvector32Term, CMemory, ConditionTerm, Pointer, PointerOffsetTerm, Proposition,
        PureFactContext, Variable,
    };
    use crate::surface::planning::proposition_search::PropositionSearch;

    let memory = CMemory::new();
    // The address of element `variable` of the goal's array.
    let at = |variable: u64| Pointer {
        block: "goal".into(),
        offset: PointerOffsetTerm::Int32Scaled {
            value: Box::new(Bitvector32Term::Variable(Variable(variable))),
            byte_width: 4,
        },
    };
    let loadable = |base: Pointer, bytes: u32| Proposition::CMemoryLoadable {
        memory: memory.clone(),
        base,
        bytes: Bitvector32Term::Constant(bytes),
    };
    let equal = |left: u64, right: u64| {
        Proposition::ConditionIs(
            ConditionTerm::Bitvector32Equal(
                Box::new(Bitvector32Term::Variable(Variable(left))),
                Box::new(Bitvector32Term::Variable(Variable(right))),
            ),
            true,
        )
    };
    // (sources, goal, premises the certificate cites; none when unproved)
    let cases = [
        (
            "a covering range",
            vec![loadable(at(470_000), 16)],
            loadable(at(470_000).offset_by_bytes(4), 4),
            Some(1),
        ),
        (
            "a range at an equal index",
            vec![loadable(at(470_001), 16), equal(470_000, 470_001)],
            loadable(at(470_000), 16),
            Some(2),
        ),
        (
            "a range at an index not known equal",
            vec![loadable(at(470_001), 16)],
            loadable(at(470_000), 16),
            None,
        ),
    ];
    for (name, sources, goal, cited) in cases {
        let samples = [16usize, 32, 64, 128]
            .into_iter()
            .map(|unrelated| {
                let mut context = PureFactContext::new();
                for index in 0..unrelated as u64 {
                    context = context
                        .assume_proposition(equal(471_000 + 2 * index, 471_001 + 2 * index))
                        .assume_proposition(Proposition::CMemoryLoadable {
                            memory: memory.clone(),
                            base: Pointer {
                                block: format!("other{index}").as_str().into(),
                                offset: PointerOffsetTerm::Constant(0),
                            },
                            bytes: Bitvector32Term::Constant(16),
                        });
                }
                for source in &sources {
                    context = context.assume_proposition(source.clone());
                }
                let (derivation, work) = crate::instrumentation::measure_deterministic_work(|| {
                    context.derive_atomic_proposition(&goal)
                });
                let premises = match (cited, derivation) {
                    (Some(cited), Some(derivation)) => {
                        let premises = derivation.context_premises();
                        assert_eq!(premises.len(), cited, "{name}: {premises:?}");
                        assert!(premises.iter().all(|premise| sources.contains(premise)));
                        premises.len()
                    }
                    (None, None) => 0,
                    (cited, derivation) => panic!(
                        "{name}: expected {cited:?} cited premises, derived {}",
                        derivation.is_some()
                    ),
                };
                (unrelated, premises, work)
            })
            .collect::<Vec<_>>();
        for pair in samples.windows(2) {
            assert!(
                pair[1].2 <= pair[0].2.saturating_mul(3),
                "{name}: derivation work is superlinear: {samples:?}"
            );
        }
    }
}

/// A goal no single source decides is proved from the facts connected to it
/// and cites only those: here a quantified fact and the bound its
/// instantiation needs, beside unrelated conditions and memory facts. This
/// goal used to be proved from, and cite, the whole context.
#[test]
fn atomic_evidence_without_one_source_cites_connected_facts() {
    use crate::kernel::{
        Bitvector32Term, CMemory, ConditionTerm, LoadKind, Pointer, PointerOffsetTerm, Proposition,
        PureFactContext, Sort, Variable,
    };
    use crate::surface::planning::proposition_search::PropositionSearch;

    let memory = CMemory::new();
    let load = |offset: PointerOffsetTerm| {
        Bitvector32Term::MemoryLoad(
            crate::kernel::intern_c_memory_ref(&memory),
            Box::new(Pointer {
                block: "data".into(),
                offset,
            }),
            LoadKind::Bits32,
        )
    };
    let equal = |left: Bitvector32Term, right: Bitvector32Term| {
        Proposition::ConditionIs(
            ConditionTerm::Bitvector32Equal(Box::new(left), Box::new(right)),
            true,
        )
    };
    let less = |left: Bitvector32Term, right: Bitvector32Term, holds: bool| {
        Proposition::ConditionIs(
            ConditionTerm::Bitvector32SignedLessThan(Box::new(left), Box::new(right)),
            holds,
        )
    };
    let variable = |id: u64| Bitvector32Term::Variable(Variable(id));
    let index = Variable(480_000);
    // forall index. index < exit ==> data[index] == index
    let quantified = Proposition::ForAll {
        var: index,
        sort: Sort::CInt32,
        body: Box::new(Proposition::Implies(
            Box::new(less(variable(480_000), variable(480_001), true)),
            Box::new(equal(
                load(PointerOffsetTerm::Int32Scaled {
                    value: Box::new(variable(480_000)),
                    byte_width: 4,
                }),
                variable(480_000),
            )),
        )),
    };
    // not (exit < 3), so index 2 is below exit.
    let bound = less(variable(480_001), Bitvector32Term::Constant(3), false);
    let goal = equal(
        load(PointerOffsetTerm::Constant(8)),
        Bitvector32Term::Constant(2),
    );
    let context = |unrelated: u64, with_bound: bool| {
        let mut context = PureFactContext::new();
        for index in 0..unrelated {
            context = context
                .assume_proposition(less(
                    variable(481_000 + 2 * index),
                    variable(481_001 + 2 * index),
                    true,
                ))
                .assume_proposition(Proposition::CMemoryLoadable {
                    memory: memory.clone(),
                    base: Pointer {
                        block: format!("other{index}").as_str().into(),
                        offset: PointerOffsetTerm::Int32Scaled {
                            value: Box::new(variable(482_000 + index)),
                            byte_width: 4,
                        },
                    },
                    bytes: Bitvector32Term::Constant(16),
                });
        }
        context = context.assume_proposition(quantified.clone());
        if with_bound {
            context = context.assume_proposition(bound.clone());
        }
        context
    };
    let samples = [16u64, 32, 64, 128]
        .into_iter()
        .map(|unrelated| {
            let (derivation, work) = crate::instrumentation::measure_deterministic_work(|| {
                context(unrelated, true).derive_atomic_proposition(&goal)
            });
            let derivation = derivation.expect("the instantiated fact derives the goal");
            let premises = derivation.context_premises();
            assert_eq!(premises.len(), 2, "{premises:?}");
            assert!(premises.contains(&quantified) && premises.contains(&bound));
            // Without the bound the instantiation's guard is not known.
            assert!(
                context(unrelated, false)
                    .derive_atomic_proposition(&goal)
                    .is_none()
            );
            (unrelated, work)
        })
        .collect::<Vec<_>>();
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1.saturating_mul(3),
            "derivation work is superlinear: {samples:?}"
        );
    }
}

#[test]
fn scaling_assertion_rejects_a_quadratic_curve() {
    let quadratic = [16, 32, 64, 128]
        .into_iter()
        .map(|size| ScalingSample {
            size,
            work: size * size,
            named_work: BTreeMap::from([(
                "operation `quadratic reference`".to_string(),
                size * size,
            )]),
        })
        .collect::<Vec<_>>();
    assert!(!near_linear_scaling(&quadratic));
    assert!(named_growth_diagnostic(&quadratic).contains("quadratic reference"));
}

/// The change history is one node per recorded snapshot. Dropping a long
/// history through the derived `Drop` recursed once per node and overflowed
/// `click verify`'s 8 MB main thread at about 6,000 recorded steps. A history
/// far longer than any budgeted proof records is dropped here on a 256 KB
/// thread, and dropped twice more with a shared suffix, since a node another
/// version still holds must stop the walk rather than be unlinked from under
/// it.
#[test]
fn recorded_snapshot_history_drops_without_recursing() {
    let build = |size: usize| {
        let mut snapshots = RecordedSnapshots::new();
        for index in 0..size {
            snapshots.insert(
                SnapshotSelector::Mark(format!("step-{index:06}")),
                CState::new(),
            );
        }
        snapshots
    };
    std::thread::Builder::new()
        .name("recorded-snapshot-history-drop".into())
        .stack_size(256 * 1024)
        .spawn(move || {
            drop(build(200_000));
            let shared = build(100_000);
            let mut longer = shared.clone();
            longer.insert(SnapshotSelector::Mark("tip".to_string()), CState::new());
            drop(longer);
            assert!(shared.contains_key(&SnapshotSelector::Mark("step-000000".to_string())));
            drop(shared);
        })
        .expect("thread")
        .join()
        .expect("dropping a recorded snapshot history must not recurse per node");
}

#[test]
fn recorded_snapshot_branch_merge_visits_only_fork_local_changes() {
    let mark_selector = |name: String| SnapshotSelector::Mark(name);
    let common_selector = mark_selector("common".to_string());
    let left_only = mark_selector("left-only".to_string());
    let right_only = mark_selector("right-only".to_string());
    let common_state = CState::new();
    let mut samples = Vec::new();

    for size in [16_usize, 64, 256, 1024, 4096] {
        let mut ancestor = RecordedSnapshots::new();
        for index in 0..size {
            ancestor.insert(mark_selector(format!("ambient-{index:05}")), CState::new());
        }
        let mut left = ancestor.clone();
        let mut right = ancestor.clone();
        left.insert(common_selector.clone(), common_state.clone());
        right.insert(common_selector.clone(), common_state.clone());
        left.insert(left_only.clone(), CState::new());
        right.insert(right_only.clone(), CState::new());

        let before = recorded_snapshot_node_allocations();
        let merged = left
            .common_descendant(&right, &ancestor)
            .expect("fork siblings should have an exact persistent ancestor");
        let allocations = recorded_snapshot_node_allocations() - before;
        samples.push((
            size,
            (usize::BITS - size.leading_zeros()) as usize,
            allocations,
        ));

        assert_eq!(merged.get(&common_selector), Some(&common_state));
        assert!(merged.get(&left_only).is_none());
        assert!(merged.get(&right_only).is_none());
        assert_eq!(
            merged.get(&mark_selector(format!("ambient-{:05}", size / 2))),
            Some(&CState::new())
        );
        assert_eq!(ancestor.iter().count(), size);

        let unrelated = RecordedSnapshots::new();
        assert!(left.common_descendant(&right, &unrelated).is_none());
    }

    let (_, base_height, base_allocations) = samples[0];
    for (size, height, allocations) in samples {
        let bound = base_allocations + 8 * (height - base_height);
        assert!(
            allocations <= bound,
            "size {size} recorded-snapshot merge allocated {allocations} nodes (logarithmic bound {bound})"
        );
    }
}

/// A ranked loop's back-edge bundle cites its arithmetic premises, so the
/// ranking members cost the same whatever else is in scope. Growing the
/// function's unrelated inequalities must not grow the work of checking that
/// the measure is nonnegative and decreases.
fn ranked_loop_with_unrelated_inequalities(fact_count: usize) -> (String, String) {
    let c_source = "int32 ranked_drain(int32 n) {\n    while (n > 0) {\n        n = n - 1;\n    }\n    return n;\n}\n".to_string();
    let mut click_source = String::from(
        "verifying \"ranked_drain.c\";\n\nint32 ranked_drain(int32 n) {\n    requires n >= 0;\n",
    );
    for index in 0..fact_count {
        click_source.push_str(&format!("    requires n != 0 - {};\n", index + 1));
    }
    click_source.push_str(
        "    ensures result == 0;\n\
         } by {\n\
         \x20   loop {\n\
         \x20       decreases n;\n\
         \x20       invariant n >= 0;\n\
         \x20       initialize by simp;\n\
         \x20       preserve by {\n\
         \x20           have 0 <= n - 1 by {\n\
         \x20               apply(int32_positive_predecessor_is_nonnegative(n)) using { n > 0; }\n\
         \x20           }\n\
         \x20           step();\n\
         \x20           close_invariants by {\n\
         \x20               both { arithmetic() using { 0 <= n; } }\n\
         \x20               and {\n\
         \x20                   both { arithmetic() using { 0 <= n; } }\n\
         \x20                   and { arithmetic() using { 0 <= n; } }\n\
         \x20               }\n\
         \x20           }\n\
         \x20       }\n\
         \x20   }\n\
         \x20   step();\n\
         \x20   simp();\n\
         }\n",
    );
    (c_source, click_source)
}

#[test]
fn ranked_loop_bundle_scales_near_linearly_with_unrelated_inequalities() {
    let samples = [8, 16, 32, 64]
        .into_iter()
        .map(|size| {
            let (c_source, click_source) = ranked_loop_with_unrelated_inequalities(size);
            let sources = [("ranked_drain.c", c_source.as_str())];
            let (verified, sample) =
                scaling_sample(size, || verify_c0_sources(&click_source, &sources));
            verified.unwrap_or_else(|error| {
                panic!(
                    "size {size} ranked-loop scaling fixture failed: {}",
                    error.message()
                )
            });
            sample
        })
        .collect::<Vec<_>>();

    assert_near_linear_scaling("ranked loop bundle with unrelated inequalities", &samples);
}

/// The same ranked loop closed by the smart `close_invariants()` planner.
/// The planner's candidate premises are the loop head's clauses and the
/// contract's own requirements, so growing the function's unrelated
/// inequalities must grow the closure's work no faster than the clauses it
/// has to classify: a scan of the ambient fact context would not stay here.
fn smart_ranked_loop_with_unrelated_inequalities(fact_count: usize) -> (String, String) {
    let c_source = "int32 ranked_drain(int32 n) {\n    while (n > 0) {\n        n = n - 1;\n    }\n    return n;\n}\n".to_string();
    let mut click_source = String::from(
        "verifying \"ranked_drain.c\";\n\nint32 ranked_drain(int32 n) {\n    requires n >= 0;\n",
    );
    for index in 0..fact_count {
        click_source.push_str(&format!("    requires n != 0 - {};\n", index + 1));
    }
    click_source.push_str(
        "    ensures result == 0;\n\
         } by {\n\
         \x20   loop {\n\
         \x20       decreases n;\n\
         \x20       invariant n >= 0;\n\
         \x20       initialize by simp;\n\
         \x20       preserve by {\n\
         \x20           have 0 <= n - 1 by {\n\
         \x20               apply(int32_positive_predecessor_is_nonnegative(n)) using { n > 0; }\n\
         \x20           }\n\
         \x20           step();\n\
         \x20           close_invariants();\n\
         \x20       }\n\
         \x20   }\n\
         \x20   step();\n\
         \x20   simp();\n\
         }\n",
    );
    (c_source, click_source)
}

#[test]
fn smart_ranked_loop_bundle_scales_near_linearly_with_unrelated_inequalities() {
    let samples = [8, 16, 32, 64]
        .into_iter()
        .map(|size| {
            let (c_source, click_source) = smart_ranked_loop_with_unrelated_inequalities(size);
            let sources = [("ranked_drain.c", c_source.as_str())];
            let (verified, sample) =
                scaling_sample(size, || verify_c0_sources(&click_source, &sources));
            verified.unwrap_or_else(|error| {
                panic!(
                    "size {size} smart ranked-loop scaling fixture failed: {}",
                    error.message()
                )
            });
            sample
        })
        .collect::<Vec<_>>();

    assert_near_linear_scaling(
        "smart ranked loop bundle with unrelated inequalities",
        &samples,
    );
}

/// A loop whose one invariant declaration has `conjuncts` members, each an
/// `int32` addition under a definedness guard. The back-edge bundle is those
/// guards introduced over the member chain, beside the ranking pair; the body
/// states every member, so each leaf closes by a direct step.
fn guarded_member_bundle(conjuncts: usize) -> (String, String) {
    let c_source = "int32 guarded_bundle(int32 n) {\n    int32 i = 0;\n\n    while (i < n) {\n        i = i + 1;\n    }\n    return i;\n}\n".to_string();
    let members = (1..=conjuncts)
        .map(|k| format!("(i <= n or {k} + i == 0)"))
        .collect::<Vec<_>>()
        .join(" and\n            ");
    let facts = (1..=conjuncts)
        .map(|k| format!("            have i <= n or {k} + i == 0 by {{ left(); }}\n"))
        .collect::<String>();
    let click_source = format!(
        "verifying \"guarded_bundle.c\";\n\n\
         int32 guarded_bundle(int32 n) {{\n\
         \x20   requires 0 <= n;\n\
         \x20   ensures result == n;\n\
         }} by {{\n\
         \x20   step();\n\
         \x20   step();\n\
         \x20   loop {{\n\
         \x20       decreases n - i;\n\
         \x20       invariant 0 <= i and i <= n;\n\
         \x20       invariant {members};\n\
         \x20       initialize by simp;\n\
         \x20       preserve by {{\n\
         \x20           mark iteration;\n\
         \x20           have 0 <= at(iteration, i) by {{ simp(); }}\n\
         \x20           step();\n\
         \x20           have 0 <= i by {{ simp(); }}\n\
         \x20           have i <= n by {{ simp(); }}\n\
         \x20           have 0 <= i and i <= n by {{ split(); }}\n\
         {facts}\
         \x20           have 0 <= n - at(iteration, i) - 1 by {{\n\
         \x20               arithmetic() using {{\n\
         \x20                   0 <= at(iteration, i);\n\
         \x20                   at(iteration, i) < at(iteration, n);\n\
         \x20                   0 <= n;\n\
         \x20               }}\n\
         \x20           }}\n\
         \x20           have n - at(iteration, i) - 1 < n - at(iteration, i) by {{\n\
         \x20               arithmetic() using {{\n\
         \x20                   0 <= at(iteration, i);\n\
         \x20                   at(iteration, i) < at(iteration, n);\n\
         \x20                   0 <= n;\n\
         \x20               }}\n\
         \x20           }}\n\
         \x20           close_invariants();\n\
         \x20       }}\n\
         \x20   }}\n\
         \x20   step();\n\
         \x20   simp();\n\
         }}\n"
    );
    (c_source, click_source)
}

/// `close_invariants()` closes a bundle whose conjuncts sit under guards with
/// the direct logical steps alone, so its work follows the bundle's size.
/// Before, the closer ran the premise-selecting and rewriting strategies over
/// the whole bundle and every suffix of it first, and four guarded members
/// already exhausted the smart budget.
#[test]
fn smart_guarded_member_bundle_scales_near_linearly_with_conjuncts() {
    let samples = [2, 4, 8, 16]
        .into_iter()
        .map(|size| {
            let (c_source, click_source) = guarded_member_bundle(size);
            let sources = [("guarded_bundle.c", c_source.as_str())];
            let (verified, sample) =
                scaling_sample(size, || verify_c0_sources(&click_source, &sources));
            verified.unwrap_or_else(|error| {
                panic!(
                    "size {size} guarded-member bundle fixture failed: {}",
                    error.message()
                )
            });
            sample
        })
        .collect::<Vec<_>>();
    assert_near_linear_scaling("guarded invariant members", &samples);
    let closer = samples
        .iter()
        .map(|sample| ScalingSample {
            size: sample.size,
            work: sample
                .named_work
                .get("smart tactic `close_invariants`")
                .copied()
                .unwrap_or(0),
            named_work: BTreeMap::new(),
        })
        .collect::<Vec<_>>();
    assert!(closer.iter().all(|sample| sample.work > 0), "{closer:?}");
    assert_near_linear_scaling("smart close_invariants over guarded members", &closer);
    // Far below the smart budget of 2,000,000 units, which four members
    // alone exhausted before the closer tried its direct steps first.
    assert!(closer.last().unwrap().work < 20_000, "{closer:?}");
}

/// A caller with growing unrelated facts calling a callee whose precondition
/// has logical structure.
///
/// The kernel's exact routes do not cover the disjunction, so the call raises
/// it as a required verification condition on every size. The point of the
/// measurement is that raising and discharging it costs what the requirement
/// and the one cited arm cost, not what the caller's fact context costs.
fn call_with_structured_precondition(fact_count: usize) -> (String, String) {
    let c_source =
        "int32 structured_precondition_caller(int32 x, int32 y) {\n    int32 result;\n    result = either_positive(x, y);\n    return result;\n}\n"
            .to_string();
    let mut click_source = String::from(
        "verifying \"structured_precondition_caller.c\";\n\nextern int32 either_positive(int32 x, int32 y) {\n    requires x > 0 or y > 0;\n    ensures result == 0;\n}\n\nint32 structured_precondition_caller(int32 x, int32 y) {\n    requires x > 0;\n",
    );
    for index in 0..fact_count {
        click_source.push_str(&format!("    requires y != {};\n", index + 100));
    }
    click_source.push_str("    ensures result == 0;\n}\n");
    (c_source, click_source)
}

#[test]
fn call_requirement_checking_scales_near_linearly_with_unrelated_caller_facts() {
    let samples = [8, 16, 32, 64]
        .into_iter()
        .map(|size| {
            let (c_source, click_source) = call_with_structured_precondition(size);
            let (verified, sample) = scaling_sample(size, || {
                verify_c0_sources(
                    &click_source,
                    &[("structured_precondition_caller.c", c_source.as_str())],
                )
            });
            verified.unwrap_or_else(|error| {
                panic!(
                    "size {size} call-requirement scaling fixture failed: {}",
                    error.message()
                )
            });
            sample
        })
        .collect::<Vec<_>>();

    assert_near_linear_scaling(
        "call requirement checking with unrelated caller facts",
        &samples,
    );
}

/// A project written entirely in explicit simple tactics must verify in work
/// approximately linear in its own source while unrelated ambient facts grow
/// alongside it.
///
/// This is package 15's acceptance regression. Before the proposition search
/// left the kernel, every miss in an authoritative kernel route ran the
/// general prover, whose whole-context fallbacks (the inconsistency scan and
/// singleton substitution) read every ambient fact on every failed query. A
/// project like this one -- `size` statements, each closed by its own
/// `step()`, under `size` unrelated requirements the proof never cites --
/// grew both axes at once, so that scan was charged once per query per fact.
/// The retained exact routes read the index the goal names and nothing else.
#[test]
fn explicit_simple_tactics_scale_with_source_while_ambient_facts_grow() {
    let samples = [8, 16, 32, 64]
        .into_iter()
        .map(|size| {
            let (c_source, click_source) = explicit_simple_project_with_ambient_facts(size);
            let (verified, sample) = scaling_sample(size, || {
                verify_c0_sources(&click_source, &[("straight.c", c_source.as_str())])
            });
            verified.unwrap_or_else(|error| {
                panic!(
                    "size {size} explicit simple-tactic project failed: {}",
                    error.message()
                )
            });
            sample
        })
        .collect::<Vec<_>>();

    assert_near_linear_scaling(
        "explicit simple tactics with growing source and ambient facts",
        &samples,
    );
}

/// `size` assignments closed by one explicit `step()` each, under `size`
/// unrelated `requires` the proof never mentions. Both the selected source
/// and the ambient fact set grow with `size`.
fn explicit_simple_project_with_ambient_facts(size: usize) -> (String, String) {
    let (c_source, base_click) = straight_line_project(size, false);
    // Unrelated ambient facts: true of the argument, never cited by the
    // proof, and disjoint from the equality the claim needs.
    let unrelated = (0..size)
        .map(|index| format!("    requires x != {};\n", index + 1000))
        .collect::<String>();
    let click_source = base_click.replacen(
        "    ensures result == x;\n",
        &format!("{unrelated}    ensures result == x;\n"),
        1,
    );
    assert_ne!(
        click_source, base_click,
        "the ambient facts were not inserted"
    );
    (c_source, click_source)
}

/// An N-constructor execution `match` must cost its N arms.
///
/// A wide match is joined by a chain of two-way group splits, so a deferred
/// post-execution operation reaches the join as a nested `if` tree whose
/// conditions select constructor subsets. Serializing that tree back into the
/// lexical arms only recognized the two-constructor selector, so every wider
/// match cloned the complete N-leaf tree into each of its N arms. The retained
/// certificate was therefore quadratic in the width, and it was rebuilt and
/// then structurally compared once per certified path and claim, which grew a
/// debug `click verify` about thirteen times per doubling.
#[test]
fn wide_execution_match_join_has_near_linear_width_work() {
    let mut samples = Vec::new();
    let mut certificate_sizes = Vec::new();
    for width in [4, 8, 16, 32] {
        let (click_source, c_source) = wide_execution_match_project(width);
        let (verified, sample) = scaling_sample(width, || {
            verify_c0_sources(&click_source, &[("read.c", c_source.as_str())])
        });
        let verified = verified.unwrap_or_else(|error| {
            panic!(
                "width {width} execution match failed: {}",
                error.message().replace('\n', " ")
            )
        });
        let certificate = verified
            .first()
            .and_then(|theorem| theorem.expanded_proof.as_ref())
            .unwrap_or_else(|| panic!("width {width} retained no certificate"));
        // Every certified path and claim retains the one certificate this
        // proof produced. Rebuilding it per theorem instead made both the
        // clone and the later theorem-set comparison pay its full size.
        assert!(
            verified.iter().all(|theorem| theorem
                .expanded_proof
                .as_ref()
                .is_some_and(|retained| retained.shares_steps_with(certificate))),
            "width {width} rebuilt the retained certificate per theorem"
        );
        certificate_sizes.push((width, certificate_step_count(certificate.steps())));
        samples.push(sample);
    }
    // The certificate is this join's own output, and one arm's operations
    // belong to that arm alone, so the whole match stays linear in its
    // constructor count: doubling the width may double the certificate, never
    // square it.
    for pair in certificate_sizes.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1 * 5 / 2,
            "the retained certificate grows faster than the constructor count: {certificate_sizes:?}"
        );
    }
    assert_near_linear_scaling("wide execution match join", &samples);
}

/// Counts every step of a certificate, including those its structured steps
/// own, so a certificate that re-emits a join tree inside each arm is
/// distinguishable from one that does not.
fn certificate_step_count(steps: &[ProofStep]) -> usize {
    fn nested(step: &ProofStep) -> usize {
        1 + match step {
            ProofStep::Match { arms, .. } => arms
                .iter()
                .map(|arm| certificate_step_count(arm.proof.steps()))
                .sum(),
            ProofStep::CloseInvariantsBy(proof) => certificate_step_count(proof.steps()),
            ProofStep::Both {
                left_proof,
                right_proof,
            }
            | ProofStep::Cases {
                left_proof,
                right_proof,
                ..
            } => {
                certificate_step_count(left_proof.steps())
                    + certificate_step_count(right_proof.steps())
            }
            ProofStep::If {
                then_proof,
                else_proof,
                ..
            }
            | ProofStep::Branch {
                then_proof,
                else_proof,
                ..
            } => {
                certificate_step_count(then_proof.steps())
                    + certificate_step_count(else_proof.steps())
            }
            ProofStep::Have { proof, .. } | ProofStep::Open { proof, .. } => {
                certificate_step_count(proof.steps())
            }
            _ => 0,
        }
    }
    steps.iter().map(nested).sum()
}

/// A `width`-constructor model over one cell, read by one C load, proved by a
/// proof `match` whose arms are identical up to the constant each constructor
/// carries. Only the constructor count varies with `width`: the C source, the
/// contract shape, and each arm's proof are fixed.
fn wide_execution_match_project(width: usize) -> (String, String) {
    let variants = (0..width)
        .map(|index| format!("V{index}"))
        .collect::<Vec<_>>()
        .join(", ");
    let code_arms = (0..width)
        .map(|index| format!("        Wide::V{index} => {index},\n"))
        .collect::<String>();
    let resource_arms = (0..width)
        .map(|index| {
            format!("        Wide::V{index} => {{ owns p[0..1]; fact p[0] == {index}; }},\n")
        })
        .collect::<String>();
    let proof_arms = (0..width)
        .map(|index| {
            format!(
                "        Wide::V{index} => {{\n\
                 \x20           unfold(c);\n\
                 \x20           execute();\n\
                 \x20           let c = fold(cell(p), {{ model: Wide::V{index} }}, {{}});\n\
                 \x20           have wide_code(old(c.model)) == {index} by {{\n\
                 \x20               rewrite(old(c.model) == Wide::V{index});\n\
                 \x20               unfold(wide_code(Wide::V{index}));\n\
                 \x20               normalize();\n\
                 \x20           }}\n\
                 \x20           simp();\n\
                 \x20       }},\n"
            )
        })
        .collect::<String>();
    let click_source = format!(
        "verifying \"read.c\";\n\
         \n\
         spec enum Wide {{ {variants} }}\n\
         \n\
         function wide_code(q: Wide) -> int32 {{\n\
         \x20   match q {{\n{code_arms}\x20   }}\n\
         }}\n\
         \n\
         resource cell(p: int32*) {{\n\
         \x20   field model: Wide;\n\
         \x20   match model {{\n{resource_arms}\x20   }}\n\
         }}\n\
         \n\
         int32 read(int32* p) {{\n\
         \x20   owns c: cell(p);\n\
         \x20   ensures c.model == old(c.model);\n\
         \x20   ensures result == wide_code(old(c.model));\n\
         }} by {{\n\
         \x20   match c.model {{\n{proof_arms}\x20   }}\n\
         }}\n"
    );
    (
        click_source,
        "int32 read(int32* p) { return *p; }".to_string(),
    )
}

#[test]
fn outcome_haves_and_resource_folds_do_not_reimport_ambient_facts() {
    let c_source = "int32 identity(int32 x) { return x; }";
    let mut samples = Vec::new();
    for size in [8_usize, 16, 32, 64] {
        let requirements = (0..size)
            .map(|i| format!("requires x != {i};"))
            .collect::<String>();
        let mut baseline = None;
        for operations in [0_usize, 1, 4, 16] {
            let body = (0..operations)
                .map(|i| {
                    format!(
                        "have {} == {} by {{ normalize(); }} unfold(marker(x)); fold(marker(x));",
                        1000 + i,
                        1000 + i,
                    )
                })
                .collect::<String>();
            let source = format!(
                r#"
                resource marker(x: int32) {{ fact x == x; }}
                verifying "identity.c";
                int32 identity(int32 x) {{
                    {requirements}
                    owns marker(x);
                    ensures result == x;
                }} by {{ execute(); {body} simp(); }}
            "#
            );
            crate::kernel::proof::take_fact_entry_counts();
            verify_c0_sources(&source, &[("identity.c", c_source)]).unwrap_or_else(|error| {
                panic!("ambient {size}, operations {operations}: {error:?}")
            });
            let (indexed, materialized) = crate::kernel::proof::take_fact_entry_counts();
            let (base_indexed, base_materialized) =
                *baseline.get_or_insert((indexed, materialized));
            samples.push((
                size,
                operations,
                indexed - base_indexed,
                materialized - base_materialized,
            ));
        }
    }
    for operations in [1, 4, 16] {
        let curve = samples
            .iter()
            .filter(|sample| sample.1 == operations)
            .collect::<Vec<_>>();
        assert!(
            curve[0].2 > 0,
            "the regression must exercise checked fact production"
        );
        for sample in &curve[1..] {
            assert_eq!(
                (sample.2, sample.3),
                (curve[0].2, curve[0].3),
                "unrelated input facts changed the cost of the outcome operations: {samples:?}"
            );
        }
    }
    let unit = samples
        .iter()
        .find(|sample| sample.0 == 8 && sample.1 == 1)
        .unwrap();
    for sample in samples
        .iter()
        .filter(|sample| sample.0 == 8 && sample.1 > 0)
    {
        assert!(
            sample.2 <= unit.2 * sample.1 && sample.3 <= unit.3 * sample.1,
            "outcome operation history grew faster than its produced deltas: {samples:?}"
        );
    }
}

/// A maybe-throwing call is the shared control-flow boundary used by the C++
/// cleanup lowering.  The returned arm advances through the selected cleanup
/// chain; the thrown arm must retain its exceptional outcome without executing
/// the normal-only tail.  The unrelated declarations and requirements make
/// sure the boundary is charged for its selected frontier, not for every
/// function, scope, or fact in the enclosing verification.
fn exceptional_cleanup_chain_project(
    cleanup_count: usize,
    unrelated_function_count: usize,
    unrelated_fact_count: usize,
) -> (String, String) {
    let mut c_source = String::from("int32 helper(int32 x) { return x; }\n\n");
    for index in 0..cleanup_count {
        c_source.push_str(&format!("int32 cleanup_{index}(int32 x) {{ return x; }}\n"));
    }
    for index in 0..unrelated_function_count {
        c_source.push_str(&format!(
            "int32 unrelated_{index}(int32 x) {{ return x; }}\n"
        ));
    }
    c_source.push_str("\nint32 cleanup_caller(int32 x) {\n    int32 result = helper(x);\n");
    for index in 0..cleanup_count {
        c_source.push_str(&format!("    result = cleanup_{index}(result);\n"));
    }
    c_source.push_str("    return result;\n}\n");

    let mut click_source = String::from("verifying \"cleanup.c\";\n\n");
    click_source.push_str(
        "int32 helper(int32 x) throws int32 {\n    ensures result == x;\n    exceptional ensures exception == 7;\n}\n\n",
    );
    for index in 0..cleanup_count {
        click_source.push_str(&format!(
            "int32 cleanup_{index}(int32 x) {{\n    ensures result == x;\n}}\n\n"
        ));
    }
    for index in 0..unrelated_function_count {
        click_source.push_str(&format!(
            "int32 unrelated_{index}(int32 x) {{ ensures result == x; }}\n\n"
        ));
    }
    click_source.push_str("int32 cleanup_caller(int32 x) throws int32 {\n");
    for index in 0..unrelated_fact_count {
        click_source.push_str(&format!("    requires x != {};\n", 10_000 + index));
    }
    click_source.push_str("    ensures result == x;\n    exceptional ensures exception == 7;\n}\n");
    (c_source, click_source)
}

/// The C++ importer currently emits a bounded cleanup list, but its cleanup
/// calls use the same checked outcome frontier as this growing C model.  This
/// acceptance regression keeps that shared engine honest while the selected
/// cleanup-edge count grows from 2 through 16 and unrelated scopes/functions/
/// facts grow with it.
#[test]
fn exceptional_cleanup_edges_scale_near_linearly_with_unrelated_context() {
    const CALL_WORK: &str = "operation `verification statement: call assign`";
    let mut samples = Vec::new();
    let mut cleanup_work = Vec::new();
    for size in [2, 4, 8, 16] {
        let (c_source, click_source) = exceptional_cleanup_chain_project(size, size, size);
        let (verified, sample) = scaling_sample(size, || {
            verify_c0_sources(&click_source, &[("cleanup.c", c_source.as_str())])
        });
        verified.unwrap_or_else(|error| {
            panic!(
                "size {size} exceptional cleanup scaling fixture failed: {}",
                error.message()
            )
        });
        cleanup_work.push(sample.named_work.get(CALL_WORK).copied().unwrap_or(0));
        samples.push(sample);
    }
    assert!(
        cleanup_work[0] > 0,
        "the scaling fixture never checked the exceptional frontier: {cleanup_work:?}"
    );
    assert_near_linear_scaling("exceptional cleanup edges", &samples);
    assert_near_linear_scaling(
        "exceptional cleanup call frontier",
        &samples
            .iter()
            .map(|sample| ScalingSample {
                size: sample.size,
                work: *sample.named_work.get(CALL_WORK).unwrap_or(&0),
                named_work: BTreeMap::new(),
            })
            .collect::<Vec<_>>(),
    );

    // Hold the selected edge and cleanup count fixed while unrelated function
    // scopes and facts grow. The named call work must not inspect those
    // unrelated declarations to re-check the same frontier.
    let mut fixed_cleanup_work = Vec::new();
    for unrelated in [4, 8, 16, 32] {
        let (c_source, click_source) = exceptional_cleanup_chain_project(8, unrelated, unrelated);
        let (verified, sample) = scaling_sample(8, || {
            verify_c0_sources(&click_source, &[("cleanup.c", c_source.as_str())])
        });
        verified.unwrap_or_else(|error| {
            panic!(
                "unrelated context {unrelated} fixed-frontier fixture failed: {}",
                error.message()
            )
        });
        fixed_cleanup_work.push(sample.named_work.get(CALL_WORK).copied().unwrap_or(0));
    }
    assert!(
        fixed_cleanup_work
            .iter()
            .all(|work| *work == fixed_cleanup_work[0]),
        "fixed cleanup frontier work changed with unrelated context: {fixed_cleanup_work:?}"
    );
}

/// One project with `statement_count` local stores between two uses of the
/// same fact about an array the stores cannot touch.
fn array_fact_across_local_stores(statement_count: usize) -> (String, String) {
    let mut c_source = String::from("void bump(int32 a[], int32 n) {\n    int32 i;\n    i = 0;\n");
    for _ in 0..statement_count {
        c_source.push_str("    i = i + 1;\n");
    }
    c_source.push_str("}\n");

    let mut click_source = String::from(
        "verifying \"bump.c\";\n\nfunction icount(p: int32[], lo: int32, hi: int32) -> Integer {\n    (lo..hi).fold(0, |acc, k| { acc + to_integer(p[k]) })\n}\n\nvoid bump(int32 a[], int32 n) {\n    requires 0 < n;\n    requires viewable(a[0..n]);\n    views a[0..n];\n} by {\n    step();\n    step();\n    have 0 <= 0 by { simp(); }\n    have icount(a, 0, 0) == 0 by {\n        unfold(icount(a, 0, 0)) using { 0 <= 0; }\n        normalize();\n    }\n",
    );
    // One use of the fact after every step: the walk is asked from a fresh
    // snapshot each time, which is the shape that goes quadratic when an
    // epoch walk cannot reuse the answer it computed one snapshot ago.
    for _ in 0..statement_count {
        click_source.push_str("    step();\n");
        click_source.push_str("    have icount(a, 0, 0) == 0 by { simp(); }\n");
    }
    click_source.push_str("    execute();\n    simp();\n}\n");
    (c_source, click_source)
}

/// One project with `statement_count` bare declarations between two uses of
/// the same fact about an array no declaration can touch.
fn array_fact_across_declarations(statement_count: usize) -> (String, String) {
    let mut c_source = String::from("void bump(int32 a[], int32 n) {\n");
    for index in 0..statement_count {
        c_source.push_str(&format!("    int32 t{index};\n"));
    }
    c_source.push_str("}\n");

    let mut click_source = String::from(
        "verifying \"bump.c\";\n\nfunction icount(p: int32[], lo: int32, hi: int32) -> Integer {\n    (lo..hi).fold(0, |acc, k| { acc + to_integer(p[k]) })\n}\n\nvoid bump(int32 a[], int32 n) {\n    requires 0 < n;\n    requires viewable(a[0..n]);\n    views a[0..n];\n} by {\n    have 0 <= 0 by { simp(); }\n    have icount(a, 0, 0) == 0 by {\n        unfold(icount(a, 0, 0)) using { 0 <= 0; }\n        normalize();\n    }\n",
    );
    for _ in 0..statement_count {
        click_source.push_str("    step();\n");
        click_source.push_str("    have icount(a, 0, 0) == 0 by { simp(); }\n");
    }
    click_source.push_str("    execute();\n    simp();\n}\n");
    (c_source, click_source)
}

/// One project with `statement_count` calls that may write only another
/// object, between two uses of the same fact about `h`.
fn array_fact_across_calls(statement_count: usize) -> (String, String) {
    let mut c_source = String::from(
        "int32 g[4];\nint32 h[4];\n\nvoid touch_g() {\n    g[0] = 1;\n}\n\nint32 keep_h() {\n",
    );
    for _ in 0..statement_count {
        c_source.push_str("    touch_g();\n");
    }
    c_source.push_str("    return h[0];\n}\n");

    let mut click_source = String::from(
        "verifying \"keep_h.c\";\n\nfunction icount(p: int32[], lo: int32, hi: int32) -> Integer {\n    (lo..hi).fold(0, |acc, k| { acc + to_integer(p[k]) })\n}\n\nvoid touch_g() {\n    owns g[0..1];\n} by {\n    execute();\n    simp();\n}\n\nint32 keep_h() {\n    requires h[0] == 5;\n    owns g[0..1];\n    views h[0..1];\n    ensures result == 5;\n} by {\n    have 0 <= 0 by { simp(); }\n    have icount(h, 0, 0) == 0 by {\n        unfold(icount(h, 0, 0)) using { 0 <= 0; }\n        normalize();\n    }\n",
    );
    for _ in 0..statement_count {
        click_source.push_str("    step();\n");
        click_source.push_str("    have icount(h, 0, 0) == 0 by { simp(); }\n");
    }
    click_source.push_str("    execute();\n    simp();\n}\n");
    (c_source, click_source)
}

/// The block epoch walk's own work over one fixture family, for the sizes
/// given. A missing entry means the fixture stopped exercising the walk, which
/// would make an assertion about its shape vacuous.
fn block_epoch_walk_curve(
    label: &str,
    file: &str,
    fixture: impl Fn(usize) -> (String, String),
) -> Vec<ScalingSample> {
    const WALK: &str = "operation `array-ref block epoch walk`";
    [4, 8, 16, 32]
        .into_iter()
        .map(|size| {
            let (c_source, click_source) = fixture(size);
            let (verified, sample) = scaling_sample(size, || {
                verify_c0_sources(&click_source, &[(file, c_source.as_str())])
            });
            verified.unwrap_or_else(|error| {
                panic!("size {size} {label} fixture failed: {}", error.message())
            });
            ScalingSample {
                size: sample.size,
                work: *sample
                    .named_work
                    .get(WALK)
                    .unwrap_or_else(|| panic!("fixture did not reach the epoch walk: {sample:?}")),
                named_work: BTreeMap::new(),
            }
        })
        .collect()
}

/// The two steps a whole-array fact learned to cross scale like the store it
/// always crossed: linear in the number of steps, not quadratic.
///
/// A declaration and a call are the interesting shapes because the walk crosses
/// them with different evidence -- one object proven distinct for a
/// declaration, a whole checked write set for a call -- and because a call's
/// arrival at a fresh snapshot per step is exactly the shape that goes
/// quadratic when the epoch walk cannot reuse the answer it computed one
/// snapshot ago.
#[test]
fn an_array_fact_carried_across_declarations_and_calls_scales_linearly() {
    assert_near_linear_scaling(
        "array-ref block epoch walk across declarations",
        &block_epoch_walk_curve("array-fact-across-declarations", "bump.c", |size| {
            array_fact_across_declarations(size)
        }),
    );
    assert_near_linear_scaling(
        "array-ref block epoch walk across calls",
        &block_epoch_walk_curve("array-fact-across-calls", "keep_h.c", |size| {
            array_fact_across_calls(size)
        }),
    );
}

/// Carrying one array fact across N steps that cannot touch the array costs
/// work linear in N, not quadratic.
///
/// The array argument names a block epoch, and the epoch is a walk back along
/// the derivation edges to the last one that could have changed the block. Run
/// per step with no memo, that walk is N hops at the Nth step and the proof
/// costs N^2; memoized per interned snapshot and block it is one hop per new
/// snapshot. This is the regression that tells those two apart.
#[test]
fn an_array_fact_carried_across_local_stores_scales_linearly() {
    let samples = [4, 8, 16, 32]
        .into_iter()
        .map(|size| {
            let (c_source, click_source) = array_fact_across_local_stores(size);
            let (verified, sample) = scaling_sample(size, || {
                verify_c0_sources(&click_source, &[("bump.c", c_source.as_str())])
            });
            verified.unwrap_or_else(|error| {
                panic!(
                    "size {size} array-fact scaling fixture failed: {}",
                    error.message()
                )
            });
            sample
        })
        .collect::<Vec<_>>();

    assert_near_linear_scaling("array fact across unrelated local stores", &samples);

    // The walk itself is the part at risk, and it is a small share of a
    // proof's work, so assert on its own measured work rather than on the
    // total it hides inside. A missing entry means the fixture stopped
    // exercising the walk at all, which would make the rest vacuous.
    const WALK: &str = "operation `array-ref block epoch walk`";
    let walk = samples
        .iter()
        .map(|sample| ScalingSample {
            size: sample.size,
            work: *sample
                .named_work
                .get(WALK)
                .unwrap_or_else(|| panic!("fixture did not reach the epoch walk: {sample:?}")),
            named_work: BTreeMap::new(),
        })
        .collect::<Vec<_>>();
    assert_near_linear_scaling("array-ref block epoch walk", &walk);
}

/// One project with `size` stores made while `size` owned ranges are held, so
/// that every store's per-cell drop is asked about a composition with `size`
/// members.
///
/// This is the shape that pays for
/// `memory_provenance::owned_composition_store_separated_evidence`: it runs
/// per surviving cell per store, and looks each side up in the composition's
/// own block bucket, so a context holding many owned ranges is exactly where
/// a per-member scan would show.
fn stores_beside_many_owned_ranges(size: usize) -> (String, String) {
    let mut c_source = String::from(
        "int32* read_acquired(int32* (*acquire)(), int32* value) {\n    int32* cell = acquire();\n    if (cell != 0) {\n",
    );
    for index in 0..size {
        c_source.push_str(&format!("        value[{index}] = *cell;\n"));
    }
    c_source.push_str("    }\n    return cell;\n}\n");

    let mut click_source = String::from(
        "resource MaybeRaw(p: int32*) {\n    if p != 0 {\n        owns p[0..1];\n    }\n}\nresource Cell(p: int32*) {\n    owns p[0..1];\n}\nresource MaybeCell(p: int32*) {\n    if p != 0 { owns Cell(p); }\n}\ncontract int32* Raw() {\n    produces MaybeRaw(result);\n}\ncontract int32* Boxed() {\n    produces MaybeCell(result);\n}\ntheorem lift(acquire: int32* (*)()) executes acquire() {\n    requires Raw(acquire);\n    ensures Boxed(acquire) by {\n        step(Raw);\n        if result != 0 {\n            unfold(MaybeRaw(result));\n            fold(Cell(result));\n            fold(MaybeCell(result));\n            simp();\n        } else {\n            unfold(MaybeRaw(result));\n            fold(MaybeCell(result));\n            simp();\n        }\n    }\n}\nverifying \"acquire.c\";\nint32* read_acquired(int32* (*acquire)(), int32* value) {\n    requires Raw(acquire);\n",
    );
    click_source.push_str(&format!("    owns value[0..{size}];\n"));
    // One claim, not one per store: the fixture is here to measure the
    // per-store composition query, and `size` claims about `size` stores
    // would be quadratic before the query is ever reached.
    click_source.push_str(
        "    produces MaybeCell(result);\n    ensures result != 0 implies value[0] == result[0];\n} by {\n    apply(lift(acquire));\n    step();\n    step(Boxed);\n    if c(cell) != 0 {\n        unfold(MaybeCell(c(cell)));\n        unfold(Cell(c(cell)));\n        execute();\n        fold(Cell(result));\n        fold(MaybeCell(result));\n        simp();\n    } else {\n        unfold(MaybeCell(c(cell)));\n        execute();\n        fold(MaybeCell(result));\n        simp();\n    }\n}\n",
    );
    (c_source, click_source)
}

/// The cost contract for the composition disjunct on the store path
/// (`docs/internals/verification-efficiency.md`): stores and held owned
/// ranges grow together, and the work must not turn over into their product.
#[test]
fn stores_beside_many_owned_ranges_scale_near_linearly() {
    let samples = [2, 4, 8, 16]
        .into_iter()
        .map(|size| {
            let (c_source, click_source) = stores_beside_many_owned_ranges(size);
            let (verified, sample) = scaling_sample(size, || {
                verify_c0_sources(&click_source, &[("acquire.c", c_source.as_str())])
            });
            verified.unwrap_or_else(|error| {
                panic!(
                    "size {size} owned-range store fixture failed: {}",
                    error.message()
                )
            });
            sample
        })
        .collect::<Vec<_>>();

    assert_near_linear_scaling("stores beside many owned ranges", &samples);

    // And on the query's own measured work, so a regression in it cannot hide
    // inside the proof's total. A missing entry would mean the fixture stopped
    // reaching the query, which would make the assertion above vacuous.
    const QUERY: &str = "operation `composition-owned store separation`";
    let query = samples
        .iter()
        .map(|sample| ScalingSample {
            size: sample.size,
            work: *sample.named_work.get(QUERY).unwrap_or_else(|| {
                panic!("fixture did not reach the composition query: {sample:?}")
            }),
            named_work: BTreeMap::new(),
        })
        .collect::<Vec<_>>();
    assert_near_linear_scaling("composition-owned store separation", &query);
}

/// The frozen byte-representation round trip
/// (`mdtests/byte_representation_roundtrip.md`) beside `unrelated` live heap
/// allocations, each null-checked with every failure path freeing the earlier
/// ones, written once, and freed at the end. `extra_copies` repeats the fixed
/// second `memcpy`.
fn roundtrip_with_unrelated_allocations(unrelated: usize, extra_copies: usize) -> String {
    let mut c = String::from(
        "void *malloc(unsigned long size);\nvoid free(void *ptr);\nvoid *memcpy(void *dest, const void *src, unsigned long n);\n\nstruct record {\n    unsigned int tag;\n    int *target;\n};\n\nint f(void) {\n",
    );
    for index in 0..unrelated {
        c.push_str(&format!(
            "    int *u{index} = malloc(sizeof(int));\n    if (u{index} == 0) {{\n"
        ));
        for previous in 0..index {
            c.push_str(&format!("        free(u{previous});\n"));
        }
        c.push_str(&format!(
            "        return -1;\n    }}\n    *u{index} = {index};\n"
        ));
    }
    let cleanup = (0..unrelated)
        .map(|index| format!("        free(u{index});\n"))
        .collect::<String>();
    c.push_str(
        &"    int *pointee = malloc(sizeof(int));
    if (pointee == 0) {
        return -1;
    }
    struct record *src = malloc(sizeof(struct record));
    if (src == 0) {
        free(pointee);
        return -1;
    }
    unsigned char *buf = malloc(16);
    if (buf == 0) {
        free(pointee);
        free(src);
        return -1;
    }
    struct record *dst = malloc(sizeof(struct record));
    if (dst == 0) {
        free(pointee);
        free(src);
        free(buf);
        return -1;
    }
    *pointee = 7;
    src->tag = 11u;
    src->target = pointee;
    memcpy(buf, (unsigned char *)(void *)src, sizeof(struct record));
    memcpy((unsigned char *)(void *)dst, buf, sizeof(struct record));
"
        .replace(
            "        return -1;\n",
            &format!("{cleanup}        return -1;\n"),
        ),
    );
    for _ in 0..extra_copies {
        c.push_str("    memcpy((unsigned char *)(void *)dst, buf, sizeof(struct record));\n");
    }
    c.push_str(
        "    int out = dst->tag + *dst->target;
    free(pointee);
    free(src);
    free(buf);
    free(dst);
",
    );
    for index in 0..unrelated {
        c.push_str(&format!("    free(u{index});\n"));
    }
    c.push_str("    return out;\n}\n");
    c
}

const ROUNDTRIP_CLICK: &str = "verifying \"rep_copy.c\";\n\nint f() {\n    ensures result == 18 or result == -1;\n} by {\n    execute();\n    simp();\n}\n";

fn roundtrip_sample(unrelated: usize, extra_copies: usize) -> ScalingSample {
    std::thread::Builder::new()
        .name(format!("roundtrip-{unrelated}-{extra_copies}"))
        .stack_size(64 << 20)
        .spawn(move || roundtrip_sample_on_this_thread(unrelated, extra_copies))
        .expect("spawn a sample thread")
        .join()
        .expect("sample thread")
}

fn roundtrip_sample_on_this_thread(unrelated: usize, extra_copies: usize) -> ScalingSample {
    let c = roundtrip_with_unrelated_allocations(unrelated, extra_copies);
    let (verified, sample) = scaling_sample(unrelated, || {
        verify_c0_sources(ROUNDTRIP_CLICK, &[("rep_copy.c", c.as_str())])
    });
    verified.unwrap_or_else(|error| {
        panic!(
            "round trip beside {unrelated} allocations with {extra_copies} extra copies failed: {}",
            error.message()
        )
    });
    sample
}

/// One extra fixed `memcpy` in the frozen byte-representation round trip
/// costs nearly the same deterministic work beside 2, 4, 8, or 16 unrelated
/// live heap allocations.
///
/// Every sample runs on its own thread after one warm-up verification, so no
/// sample pays the once-per-process standard-library setup. Measured
/// marginals on 2026-09-23: 3226, 3268, 3324, and 3468 units. They were
/// 3232, 3276, 3336, and 3488 (and 3752 at 32 allocations, too slow for a
/// debug-build unit test) while whole-function finalization still visited
/// the grouped proof's shared execution once per path theorem. Before snapshot
/// sharing they were about 33,000 at N = 8 and 58,000 at N = 16: every later
/// free compared the copy's facts, whose embedded snapshots were equal but
/// separately stored, entry by entry. Before resource validity read only
/// indexed candidates they were 3236, 3288, 3364, and 3548: each call's
/// ensured-resource composition swept every block the caller owned.
///
/// This guards those collapses; it is not the logarithmic contract, which
/// the expanded proof meets (see the next test). The remaining growth, about
/// 17 units per unrelated allocation, is mostly the
/// smart `execute` planner's condition-premise search over its listed pure
/// facts and that search's simp checkpoints (about 12 per allocation); the
/// rest is re-derived snapshot comparison relative to a base and more
/// composition separation-candidate projections. The kernel call path is
/// flat here: `ensured resource composition` and `verified call return
/// resource evaluation` charge the same work at every size.
#[test]
fn roundtrip_extra_copy_stays_nearly_flat_beside_unrelated_allocations() {
    const SIZES: [usize; 4] = [2, 4, 8, 16];
    let _ = roundtrip_sample(1, 0);
    let handles = SIZES
        .iter()
        .flat_map(|&size| [(size, 0), (size, 1)])
        .map(|(size, extra)| {
            std::thread::Builder::new()
                .name(format!("roundtrip-{size}-{extra}"))
                .stack_size(64 << 20)
                .spawn(move || roundtrip_sample_on_this_thread(size, extra).work)
                .expect("spawn a sample thread")
        })
        .collect::<Vec<_>>();
    let work = handles
        .into_iter()
        .map(|handle| handle.join().expect("sample thread"))
        .collect::<Vec<_>>();
    let marginal = work
        .chunks(2)
        .map(|pair| pair[1] as i64 - pair[0] as i64)
        .collect::<Vec<_>>();
    eprintln!("extra-copy marginal work beside {SIZES:?} allocations: {marginal:?}");
    assert!(marginal[0] > 0, "{marginal:?}");
    let allowed = marginal[0] + marginal[0] / 8;
    assert!(
        marginal.iter().all(|work| *work <= allowed),
        "one extra memcpy grew with unrelated allocations beyond {allowed}: {marginal:?}"
    );
}

/// The largest unrelated-allocation count whose expanded round trip fits the
/// checked proof drivers' nesting bound: every null check becomes one nested
/// proof `if`, and the round trip adds four of its own to the eleven allowed.
const EXPANDED_ROUNDTRIP_MAX_UNRELATED: usize = 7;

/// Expands the round trip's `execute(); simp();` proof beside `unrelated`
/// allocations to explicit simple tactics, outside the measurement, and
/// returns the C source length with the expanded proof's verification work.
fn expanded_roundtrip_sample(unrelated: usize, extra_copies: usize) -> (usize, ScalingSample) {
    std::thread::Builder::new()
        .name(format!("expanded-roundtrip-{unrelated}-{extra_copies}"))
        .stack_size(64 << 20)
        .spawn(move || {
            let c = roundtrip_with_unrelated_allocations(unrelated, extra_copies);
            let sources = [("rep_copy.c", c.as_str())];
            let expanded =
                expand_c0_claim_source(ROUNDTRIP_CLICK, &sources, "f", CProofClaim::Grouped)
                    .unwrap_or_else(|error| {
                        panic!(
                            "round trip beside {unrelated} allocations with {extra_copies} extra copies should expand: {}",
                            error.message()
                        )
                    });
            assert!(!expanded.contains("execute()"), "{expanded}");
            assert!(!expanded.contains("simp()"), "{expanded}");
            let (verified, sample) =
                scaling_sample(unrelated, || verify_c0_sources(&expanded, &sources));
            verified.unwrap_or_else(|error| {
                panic!(
                    "expanded round trip beside {unrelated} allocations with {extra_copies} extra copies failed: {}\n{expanded}",
                    error.message()
                )
            });
            (c.len(), sample)
        })
        .expect("spawn a sample thread")
        .join()
        .expect("sample thread")
}

/// Samples the expanded round trip at `sizes`, each with and without the
/// extra copy, every one on its own thread after one warm-up verification.
fn expanded_roundtrip_samples(sizes: &[usize]) -> Vec<[(usize, ScalingSample); 2]> {
    assert!(
        sizes
            .iter()
            .all(|size| *size <= EXPANDED_ROUNDTRIP_MAX_UNRELATED)
    );
    let _ = roundtrip_sample(1, 0);
    let handles = sizes
        .iter()
        .map(|&size| {
            [0, 1].map(|extra| {
                std::thread::Builder::new()
                    .name(format!("expanded-roundtrip-driver-{size}-{extra}"))
                    .spawn(move || expanded_roundtrip_sample(size, extra))
                    .expect("spawn a sample driver")
            })
        })
        .collect::<Vec<_>>();
    handles
        .into_iter()
        .map(|pair| pair.map(|handle| handle.join().expect("sample driver")))
        .collect()
}

/// One extra fixed `memcpy` in the frozen byte-representation round trip,
/// under its expanded proof of explicit simple tactics, costs at most a
/// logarithm more beside 1, 2, 4, or 7 unrelated live heap allocations.
///
/// This is the contract the smart test above does not meet: both variants'
/// `execute(); simp();` proofs are expanded outside the measurement, and only
/// the two expanded proofs' verification is compared. Seven allocations is
/// the largest family member the checked proof drivers' nesting bound admits
/// (see [`EXPANDED_ROUNDTRIP_MAX_UNRELATED`]). Measured marginals on
/// 2026-09-23 for 1 through 7 allocations: 912, 912, 912, 912, 916, 920, and
/// 920 units. The only growth is two `CMemory::eq_relative_to` comparisons
/// at each path's end (`proof completion`, re-deriving the memory without
/// the function's local block), whose persistent-map walk deepens with the
/// heap. Before finalization visited a grouped proof's shared execution once,
/// the marginals were 917, 918, 919, 920, 925, 930, and 931, one more unit
/// per allocation: the extra copy's composition carrier was re-inserted into
/// a fresh fact context once per theorem, and a grouped proof issues one
/// theorem per path.
#[test]
fn expanded_roundtrip_extra_copy_is_logarithmic_beside_unrelated_allocations() {
    const SIZES: [usize; 4] = [1, 2, 4, EXPANDED_ROUNDTRIP_MAX_UNRELATED];
    let marginal = expanded_roundtrip_samples(&SIZES)
        .iter()
        .map(|[(_, without), (_, with)]| with.work as i64 - without.work as i64)
        .collect::<Vec<_>>();
    eprintln!("expanded extra-copy marginal work beside {SIZES:?} allocations: {marginal:?}");
    assert!(marginal[0] > 0, "{marginal:?}");
    for (size, work) in SIZES.iter().zip(&marginal) {
        // Four units per doubling of the unrelated allocations; the measured
        // curve rises eight units by seven allocations, and a single unit
        // per allocation would exceed this by seven.
        let allowed = marginal[0] as f64 + 4.0 * (*size as f64 / SIZES[0] as f64).log2();
        assert!(
            *work as f64 <= allowed,
            "one extra memcpy under the expanded proof grew beyond {allowed} beside {size} allocations: {marginal:?}"
        );
    }
}

/// The whole expanded round trip costs deterministic work per C source byte
/// that grows at most logarithmically in the source beside 1, 2, 4, or 7
/// unrelated allocations.
///
/// The source is quadratic in the allocations, since every failure path
/// frees the earlier ones, and so is the checked path structure: each
/// failure path steps its own frees. Measured on 2026-09-23 for 1 through 7
/// allocations: 8449, 10068, 11842, 13779, 15885, 18154, and 20590 units over
/// 1193, 1389, 1603, 1835, 2085, 2353, and 2639 bytes, or 7.08, 7.25, 7.39,
/// 7.51, 7.62, 7.72, and 7.80 units per byte. The rise per doubling of the
/// source falls from 0.76 to 0.52 units per byte as the quadratic terms,
/// about 82 units against 9 bytes per squared allocation, take over.
#[test]
fn expanded_roundtrip_work_per_source_byte_is_logarithmic() {
    const SIZES: [usize; 4] = [1, 2, 4, EXPANDED_ROUNDTRIP_MAX_UNRELATED];
    let samples = expanded_roundtrip_samples(&SIZES);
    let per_byte = samples
        .iter()
        .map(|[(bytes, without), _]| (*bytes, without.work, without.work as f64 / *bytes as f64))
        .collect::<Vec<_>>();
    eprintln!(
        "expanded round trip (bytes, work, work per byte) beside {SIZES:?} allocations: {per_byte:?}"
    );
    let (first_bytes, _, first_ratio) = per_byte[0];
    assert!(first_ratio > 0.0, "{per_byte:?}");
    for (size, (bytes, _, ratio)) in SIZES.iter().zip(&per_byte) {
        // One unit per byte per doubling of the source.
        let allowed = first_ratio + (*bytes as f64 / first_bytes as f64).log2();
        assert!(
            *ratio <= allowed,
            "expanded round trip work per source byte grew beyond {allowed:.3} beside {size} allocations: {per_byte:?}; named work: {}",
            named_growth_diagnostic(
                &samples
                    .iter()
                    .map(|[(_, without), _]| without.clone())
                    .collect::<Vec<_>>()
            )
        );
    }
}

/// C source with one checked allocation and `returns` early returns after it,
/// so `returns + 2` paths each carry the same few resource facts.
fn early_return_fan_out(returns: usize) -> String {
    let mut c = String::from(
        "void *malloc(unsigned long size);\nvoid free(void *ptr);\n\nint g(int a) {\n    int *p = malloc(sizeof(int));\n    if (p == 0) {\n        return -1;\n    }\n    *p = a;\n    free(p);\n",
    );
    for index in 0..returns {
        c.push_str(&format!(
            "    if (a == {index}) {{\n        return {index};\n    }}\n"
        ));
    }
    c.push_str("    return -1;\n}\n");
    c
}

/// Whole-function finalization reads each path of a grouped proof's checked
/// execution once, however many paths the proof issues theorems for.
///
/// A grouped proof issues one theorem per path and claim, all over one
/// shared execution. The implicit empty-effect check used to walk every path
/// of that execution once per theorem, rebuilding each path's fact context
/// each time, so its work was quadratic in the path count. Measured
/// `implicit empty effect check` work on 2026-09-23 at 4, 8, 16, and 32 early
/// returns: 5, 9, 17, and 33 units, one per composition carrier inserted into
/// a path's fact context. Visiting the execution once per theorem measured
/// 30, 90, 306, and 1122.
///
/// Every context build is now charged a unit per fact, and path `k` of this
/// fan-out holds the `k` conditions before it, so building each path's
/// context charged 37, 87, 235, and 723. The check now builds a path's
/// context only when a write could reach storage that predates the call,
/// which this function's heap cell cannot, and charges one unit per path it
/// reads instead: 6, 10, 18, and 34 on 2026-09-27.
#[test]
fn grouped_proof_finalization_reads_each_path_once() {
    std::thread::Builder::new()
        .name("grouped-finalization-fan-out".into())
        .stack_size(64 << 20)
        .spawn(|| {
            let _ = roundtrip_sample(1, 0);
            const CHECK: &str = "operation `implicit empty effect check`";
            let click = "verifying \"fan_out.c\";\n\nint g(int a) {\n    ensures result == a or result == -1;\n} by {\n    execute();\n    simp();\n}\n";
            let samples = [4, 8, 16, 32]
                .map(|returns| {
                    let c = early_return_fan_out(returns);
                    let (verified, sample) = scaling_sample(returns, || {
                        verify_c0_sources(click, &[("fan_out.c", c.as_str())])
                    });
                    verified.unwrap_or_else(|error| {
                        panic!("fan-out of {returns} returns failed: {}", error.message())
                    });
                    ScalingSample {
                        size: returns,
                        work: *sample.named_work.get(CHECK).unwrap_or_else(|| {
                            panic!("fan-out did not reach the implicit empty-effect check: {sample:?}")
                        }),
                        named_work: BTreeMap::new(),
                    }
                })
                .to_vec();
            eprintln!("implicit empty-effect check work: {samples:?}");
            assert_near_linear_scaling("implicit empty-effect check over paths", &samples);
        })
        .expect("spawn the fan-out thread")
        .join()
        .expect("fan-out thread");
}

/// A fixed one-store proof verified after an unrelated proof in the same
/// sidecar. Everything a proof unit builds in the session (interned snapshots,
/// load names, memo tables) outlives it, so this is where a later proof can
/// end up walking an earlier one's history. The naming cache once returned
/// load names minted by the earlier function without refreshing their origin,
/// and the later store's pointer transport walked the earlier function's DAG
/// from that origin: 30,000 units alone became over a million, and the
/// arena's `arena_write` failed its budget only when `arena_init` ran first.
#[test]
fn a_fixed_store_proof_costs_the_same_after_a_growing_unrelated_proof() {
    const RESOURCES: &str = "resource box_state(b: struct box*) {
    field len: int32;
    owns &b->data;
    owns b->len;
    owns b->data[0..len];
    fact b->len == len;
    fact 0 <= len;
    fact separate(memory(object(b)), memory(b->data[0..b->len]));
}

resource holder_state(h: struct holder*) {
    field start: int32;
    owns object(h);
    fact h->start == start;
    fact 0 <= start;
}
";
    const FIXED_C: &str = "void one(struct holder* h, int32 i) {
    struct box* b;

    b = h->box;
    b->data[h->start + i] = 1;
}
";
    const FIXED_PROOF: &str = "void one(struct holder* h, int32 i) {
    owns r: holder_state(h);
    owns st: box_state(h->box);
    requires 0 <= i;
    requires defined(r.start + i) and r.start + i < st.len;
    ensures st.len == old(st.len);
} by {
    let { len: l } = unfold(st);
    let { start: s } = unfold(r);
    have defined(s + i) by {
        simp() using {
            defined(s + i) and s + i < l;
        }
    }
    have s + i < l by {
        simp() using {
            defined(s + i) and s + i < l;
        }
    }
    have s <= s + i by {
        apply(int32_add_nonnegative_right_is_at_least_left(s, i)) using {
            0 <= i;
            defined(s + i);
        }
    }
    have s + i + 1 <= l by {
        apply(int32_increment_upper_bound(s + i, l)) using {
            s + i < l;
        }
    }
    have h->start == s by {
        assumption();
    }
    have defined(h->start + i) by {
        rewrite(h->start == s);
        assumption();
    }
    have h->start <= h->start + i by {
        rewrite(h->start == s);
        assumption();
    }
    have h->start + i + 1 <= l by {
        rewrite(h->start == s);
        assumption();
    }
    execute();
    let r = fold(holder_state(h), { start: s });
    let st = fold(box_state(h->box), { len: l });
    simp();
}
";
    const STRUCTS: &str = "struct box {
    int32* data;
    int32 len;
};

struct holder {
    struct box* box;
    int32 start;
};
";
    // The work of the fixed proof's own tactics, and whether it verified.
    let fixed_proof_work = |unrelated_stores: Option<usize>| {
        let (big_c, big_proof) = match unrelated_stores {
            None => (String::new(), String::new()),
            Some(stores) => (
                format!(
                    "void big(struct box* b) {{\n{}}}\n\n",
                    (0..stores)
                        .map(|index| format!("    b->data[{index}] = 0;\n"))
                        .collect::<String>()
                ),
                format!(
                    "void big(struct box* b) {{
    owns st: box_state(b);
    requires {stores} <= st.len;
    ensures st.len == old(st.len);
}} by {{
    let {{ len: l }} = unfold(st);
    execute();
    let st = fold(box_state(b), {{ len: l }});
    simp();
}}

"
                ),
            ),
        };
        let c_source = format!("{STRUCTS}\n{big_c}{FIXED_C}");
        let click_source =
            format!("{RESOURCES}\nverifying \"order.c\";\n\n{big_proof}{FIXED_PROOF}");
        let (result, events) = crate::instrumentation::collect(|| {
            verify_c0_sources(&click_source, &[("order.c", &c_source)])
        });
        result.unwrap_or_else(|error| {
            panic!(
                "the fixed proof after {unrelated_stores:?} unrelated stores should verify: {}",
                error.message()
            )
        });
        events
            .into_iter()
            .filter_map(|event| match event {
                crate::instrumentation::VerificationEvent::TacticFinished {
                    tactic, work, ..
                } if tactic.claim.starts_with("one.") => Some(work),
                _ => None,
            })
            .sum::<usize>()
    };
    let alone = fixed_proof_work(None);
    assert!(alone > 0);
    let samples = [4, 8, 16, 32].map(|stores| (stores, fixed_proof_work(Some(stores))));
    for &(stores, work) in &samples {
        // Constant plus a logarithmic allowance for indexed session tables.
        let allowance = 64 * (usize::BITS - stores.leading_zeros()) as usize;
        assert!(
            work <= alone + allowance,
            "the fixed proof's work must not depend on the unrelated proof before it: \
             alone {alone}, after (stores, work) {samples:?}"
        );
    }
}

/// A loop that marks `arena->occupied[i]` for `i` in `[start, end)` and
/// frames `cells` constant cells below `start`, one invariant per cell.
/// The explicit back-edge closure cites each cell's frame fact after
/// introducing the preceding written invariant clauses. Logical reads do
/// not add viewability goals or introductions to that certificate.
fn framed_field_cells_loop(cells: usize) -> (String, String) {
    let c_source = "struct arena {\n    int32* data;\n    int32* occupied;\n    int32 capacity;\n};\n\n\
        void mark_tail(struct arena* arena, int32 start, int32 end) {\n    int32 i;\n    i = start;\n    \
        while (i < end) {\n        arena->occupied[i] = 1;\n        i = i + 1;\n    }\n}\n"
        .to_string();
    let ranking = "arithmetic() using { 0 <= at(statement(3).entry, i); \
        at(statement(3).entry, i) < at(statement(3).entry, end); end <= 1000000; }";
    let mut members = vec!["simp();".to_string()];
    for cell in 0..cells {
        members.push(format!(
            "{}arithmetic_certificate signed_int32 {{ premise 0: arena->occupied[{cell}] == \
             old(arena->occupied[{cell}]) => arena->occupied[{cell}] == \
             old(arena->occupied[{cell}]); conclusion 0; }}",
            "intro(); ".repeat(1 + cell)
        ));
    }
    members.push(ranking.to_string());
    members.push(ranking.to_string());
    let closure = members
        .iter()
        .rev()
        .skip(1)
        .fold(members.last().unwrap().clone(), |rest, member| {
            format!("both {{ {member} }} and {{ {rest} }}")
        });
    let invariants = (0..cells)
        .map(|cell| {
            format!("        invariant arena->occupied[{cell}] == old(arena->occupied[{cell}]);\n")
        })
        .collect::<String>();
    let click_source = format!(
        "verifying \"mark_tail.c\";\n\n\
         void mark_tail(struct arena* arena, int32 start, int32 end) {{\n\
         \x20   owns object(arena);\n\
         \x20   owns arena->occupied[0..arena->capacity];\n\
         \x20   requires separate(\n\
         \x20       memory(object(arena)),\n\
         \x20       memory(arena->occupied[0..arena->capacity])\n\
         \x20   );\n\
         \x20   requires 0 <= start;\n\
         \x20   requires {cells} <= start;\n\
         \x20   requires start <= end;\n\
         \x20   requires end <= arena->capacity;\n\
         \x20   requires end <= 1000000;\n\
         }} by {{\n\
         \x20   step();\n\
         \x20   step();\n\
         \x20   loop {{\n\
         \x20       owns arena->occupied[0..arena->capacity];\n\
         \x20       invariant start <= i;\n\
         {invariants}\
         \x20       decreases end - i;\n\
         \x20       initialize by simp;\n\
         \x20       preserve by {{\n\
         \x20           have 0 <= i by {{ simp(); }}\n\
         \x20           step();\n\
         \x20           step();\n\
         \x20           close_invariants by {{ {closure} }}\n\
         \x20       }}\n\
         \x20   }}\n\
         \x20   execute();\n\
         \x20   simp();\n\
         }}\n"
    );
    (c_source, click_source)
}

/// The number of simple steps in `framed_field_cells_loop`'s explicit
/// back-edge closure: one `both` per member but the last, the members'
/// closing steps, and the preceding-clause introductions each cell makes.
fn framed_field_cells_closure_steps(cells: usize) -> usize {
    let members = 1 + cells + 2;
    let introductions = (0..cells).map(|cell| 1 + cell).sum::<usize>();
    (members - 1) + members + introductions
}

/// Framing `N` cells of a map read through a struct field costs work in
/// proportion to the explicit back-edge closure. Each cell's member is guarded
/// by every earlier clause, so the closure itself has a quadratic number of
/// introductions; the work must follow that certificate, not outgrow it.
/// Before, a later member was guarded by each earlier member whole, so the
/// bundle doubled with every declaration.
///
/// The remaining excess over the certificate is the order-fact fallback that
/// matches a condition against every stated condition fact
/// (`has_condition_fact`), which the growing set of framed-cell facts feeds.
#[test]
fn framed_field_cells_back_edge_closure_follows_its_certificate() {
    let samples = [1, 2, 4, 8]
        .into_iter()
        .map(|size| {
            let (c_source, click_source) = framed_field_cells_loop(size);
            let sources = [("mark_tail.c", c_source.as_str())];
            let (verified, sample) =
                scaling_sample(size, || verify_c0_sources(&click_source, &sources));
            verified.unwrap_or_else(|error| {
                panic!(
                    "size {size} framed field cells fixture failed: {}",
                    error.message()
                )
            });
            sample
        })
        .collect::<Vec<_>>();
    for pair in samples.windows(2) {
        let steps = framed_field_cells_closure_steps(pair[1].size) as f64
            / framed_field_cells_closure_steps(pair[0].size) as f64;
        let work = pair[1].work as f64 / pair[0].work as f64;
        assert!(
            work <= 1.5 * steps,
            "framed field cells: work grew {work:.2}x against a {steps:.2}x larger closure: \
             {samples:?}; named work: {}",
            named_growth_diagnostic(&samples),
        );
    }
}

/// A counting loop with `clauses` pure invariant declarations beside its
/// bound, closed by the smart `close_invariants()`.
fn many_clause_loop(clauses: usize) -> (String, String) {
    let c_source =
        "void count(int32 n) {\n    int32 i;\n    i = 0;\n    while (i < n) {\n        i = i + 1;\n    }\n}\n"
            .to_string();
    let invariants = (0..clauses)
        .map(|clause| format!("        invariant 0 - {clause} <= i;\n"))
        .collect::<String>();
    let click_source = format!(
        "verifying \"count.c\";\n\n\
         void count(int32 n) {{\n\
         \x20   requires 0 <= n;\n\
         \x20   requires n <= 1000;\n\
         \x20   ensures 0 == 0;\n\
         }} by {{\n\
         \x20   step();\n\
         \x20   step();\n\
         \x20   loop {{\n\
         \x20       invariant 0 <= i;\n\
         {invariants}\
         \x20       decreases n - i;\n\
         \x20       initialize by simp;\n\
         \x20       preserve by {{\n\
         \x20           step();\n\
         \x20           close_invariants();\n\
         \x20       }}\n\
         \x20   }}\n\
         \x20   execute();\n\
         \x20   simp();\n\
         }}\n"
    );
    (c_source, click_source)
}

/// The back-edge bundle guards each clause by the clauses declared before
/// it, bare. Guarding by the earlier members whole doubled the bundle with
/// every declaration: sixteen clauses exhausted the smart closer's budget.
/// The guards now grow by one clause per declaration, so the bundle and the
/// closer's work stay within a quadratic curve in the declarations.
#[test]
fn many_clause_bundle_grows_at_most_quadratically() {
    let samples = [2, 4, 8, 16]
        .into_iter()
        .map(|size| {
            let (c_source, click_source) = many_clause_loop(size);
            let sources = [("count.c", c_source.as_str())];
            let (verified, sample) =
                scaling_sample(size, || verify_c0_sources(&click_source, &sources));
            verified.unwrap_or_else(|error| {
                panic!(
                    "size {size} many-clause fixture failed: {}",
                    error.message()
                )
            });
            sample
        })
        .collect::<Vec<_>>();
    for pair in samples.windows(2) {
        assert!(
            pair[1].work <= pair[0].work.saturating_mul(9) / 2,
            "many invariant clauses: work more than quadrupled per doubling: {samples:?}; \
             named work: {}",
            named_growth_diagnostic(&samples),
        );
    }
}

/// `simp` closes `x0 == xN` from the chain `x0 == x1`, ..., `x(N-1) == xN`
/// in one step, with work linear in the chain; a query about two unrelated
/// equal terms costs the same whatever chain sits beside it.
#[test]
fn simp_equality_chain_is_linear_and_unrelated_queries_are_flat() {
    let simp_work = |sample: &ScalingSample| {
        sample
            .named_work
            .iter()
            .filter(|(name, _)| name.ends_with("tactic `simp`"))
            .map(|(_, work)| *work)
            .sum::<usize>()
    };
    let sources = |size: usize, goal: &str| {
        let c_parameters = (0..=size)
            .map(|index| format!("int x{index}"))
            .chain(["int y".into(), "int z".into(), "int w".into()])
            .collect::<Vec<_>>()
            .join(", ");
        let parameters = (0..=size)
            .map(|index| format!("int32 x{index}"))
            .chain(["int32 y".into(), "int32 z".into(), "int32 w".into()])
            .collect::<Vec<_>>()
            .join(", ");
        let requires = (0..size)
            .map(|index| format!("    requires x{index} == x{};\n", index + 1))
            .collect::<String>();
        (
            format!("int chain({c_parameters}) {{\n    return 0;\n}}\n"),
            format!(
                "verifying \"chain.c\";\n\nint32 chain({parameters}) {{\n{requires}    requires y == z;\n    requires z == w;\n    ensures {goal};\n}} by {{\n    execute();\n    simp();\n}}\n"
            ),
        )
    };
    let mut chain = Vec::new();
    let mut unrelated = Vec::new();
    for size in [4, 8, 16, 32] {
        for (goal, samples) in [
            (format!("x0 == x{size}"), &mut chain),
            ("y == w".to_string(), &mut unrelated),
        ] {
            let (c_source, click_source) = sources(size, &goal);
            let (verified, sample) = scaling_sample(size, || {
                verify_c0_sources(&click_source, &[("chain.c", c_source.as_str())])
            });
            verified.unwrap_or_else(|error| panic!("`{goal}` closes: {}", error.message()));
            samples.push(simp_work(&sample));
        }
    }
    assert!(chain[0] > 0 && unrelated[0] > 0, "{chain:?} {unrelated:?}");
    for pair in chain.windows(2) {
        assert!(
            pair[1] <= pair[0].saturating_mul(3),
            "chain work grew faster than linear: {chain:?}"
        );
    }
    for work in &unrelated {
        assert!(
            *work <= unrelated[0].saturating_add(unrelated[0] / 4),
            "an unrelated query grew with the chain: {unrelated:?}"
        );
    }
}

/// A simplifier goal no case split can decide does not pay for case splits
/// over disjunctions about other variables: each call outcome in a long
/// proof (`result == 0 or result == 1`) used to be split, nested, before the
/// derivation failed. The split skips a disjunction sharing no variable with
/// the goal, so the failing derivation's work stays flat as they grow.
#[test]
fn failing_simp_derivation_ignores_unrelated_disjunctions() {
    use crate::kernel::{Bitvector32Term, ConditionTerm, Proposition, PureFactContext, Variable};
    use crate::surface::planning::proposition_search::PropositionSearch;

    let equal = |variable: u64, value: u32| {
        Proposition::ConditionIs(
            ConditionTerm::Bitvector32Equal(
                Box::new(Bitvector32Term::Variable(Variable(variable))),
                Box::new(Bitvector32Term::Constant(value)),
            ),
            true,
        )
    };
    let samples = [2, 4, 6, 8]
        .into_iter()
        .map(|size| {
            let mut context = PureFactContext::new();
            for index in 0..size {
                let variable = 432_000 + index as u64;
                context = context.assume_proposition(Proposition::Or(
                    Box::new(equal(variable, 0)),
                    Box::new(equal(variable, 1)),
                ));
            }
            let goal = Proposition::ConditionIs(
                ConditionTerm::Bitvector32SignedLessThan(
                    Box::new(Bitvector32Term::Variable(Variable(433_000))),
                    Box::new(Bitvector32Term::Constant(5)),
                ),
                true,
            );
            let (derivation, work) = crate::instrumentation::measure_deterministic_work(|| {
                context.derive_simp_proposition(&goal)
            });
            assert!(derivation.is_none(), "nothing bounds the goal's variable");
            (size, work)
        })
        .collect::<Vec<_>>();
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1.saturating_mul(2).saturating_add(64),
            "unrelated disjunctions were split: {samples:?}"
        );
    }
}

fn branching_grouped_claim_project(claim_count: usize) -> (String, String) {
    let c_source = "int32 branching_claims(int32 a) {\n    int32 x;\n    if (a == 0) {\n        return 0;\n    }\n    x = a;\n    return x;\n}\n"
        .to_string();
    let mut click_source = String::from(
        "verifying \"branching_claims.c\";\n\nint32 branching_claims(int32 a) {\n    requires 0 <= a;\n    requires a <= 10;\n",
    );
    for _ in 0..claim_count {
        click_source.push_str("    ensures result == a;\n");
    }
    click_source.push_str(
        "} by {\n    step();\n    branch {\n        then {\n            execute();\n            simp();\n        }\n        else {}\n    }\n    step();\n    have x == a by {\n        simp();\n    }\n    execute();\n    simp();\n}\n",
    );
    (c_source, click_source)
}

/// A grouped proof issues one theorem per path and claim. Each used to carry
/// its own copy of the function block, which holds the whole grouped proof,
/// and of the proof's tactics, and finishing compared every new theorem with
/// every earlier one field by field, so finishing cost the proof's size times
/// the number of theorems (twice that number squared for the comparisons).
/// None of that is deterministic work, so the curve alone cannot see it: the
/// theorems must share one proof text at every size.
#[test]
fn grouped_proof_theorems_share_one_proof_text() {
    let samples = [8, 16, 32, 64]
        .into_iter()
        .map(|size| {
            let (c_source, click_source) = branching_grouped_claim_project(size);
            let (verified, sample) = scaling_sample(size, || {
                verify_c0_sources(&click_source, &[("branching_claims.c", c_source.as_str())])
            });
            let verified = verified.unwrap_or_else(|error| {
                panic!(
                    "size {size} branching grouped-claim fixture failed: {}",
                    error.message()
                )
            });
            assert!(
                verified.len() >= size,
                "size {size}: every claim should be issued: {} theorems",
                verified.len()
            );
            let first = &verified[0];
            let first_tactics = first
                .proof_tactics
                .as_ref()
                .expect("a grouped script theorem retains its proof tactics");
            for theorem in &verified {
                assert!(
                    std::sync::Arc::ptr_eq(&theorem.function_block, &first.function_block),
                    "size {size}: a theorem carries its own copy of the function block"
                );
                assert!(
                    theorem
                        .proof_tactics
                        .as_ref()
                        .is_some_and(|tactics| std::sync::Arc::ptr_eq(tactics, first_tactics)),
                    "size {size}: a theorem carries its own copy of the proof tactics"
                );
            }
            sample
        })
        .collect::<Vec<_>>();
    assert_near_linear_scaling("theorems of one branching grouped proof", &samples);
}

/// One project whose caller makes `call_count` plain `step()`s over a callee
/// that advances one counter field of an owned object and keeps its other
/// field. Every call's equality ensures name a load at the previous call's
/// snapshot, so the counter's constant after normalization runs through the
/// whole prior call chain -- the `arena_free` shape (`after.live ==
/// old(st.live) - 1`, `region->start == old(r.start)`).
fn counter_call_chain(call_count: usize) -> (String, String) {
    let mut c_source = String::from(
        "struct range {\n    int32 start;\n    int32 end;\n};\n\nvoid touch(struct range* r) {\n    r->end = r->end + 1;\n}\n\nvoid drive(struct range* r) {\n",
    );
    for _ in 0..call_count {
        c_source.push_str("    touch(r);\n");
    }
    c_source.push_str("}\n");
    let mut click_source = String::from(
        "verifying \"drive.c\";\n\nvoid touch(struct range* r) {\n    owns object(r);\n    requires r->end < 1000000;\n    ensures r->end == old(r->end) + 1;\n    ensures r->start == old(r->start);\n} by {\n    execute();\n    simp();\n}\n\n",
    );
    click_source.push_str(&format!(
        "void drive(struct range* r) {{\n    owns object(r);\n    requires r->end == 0;\n    ensures r->end == {call_count};\n}} by {{\n"
    ));
    for _ in 0..call_count {
        click_source.push_str("    step();\n");
    }
    click_source.push_str("    execute();\n    simp();\n}\n");
    (c_source, click_source)
}

/// A simple `step()` over a call lowers the callee's equality ensures in work
/// proportional to that call, not to the caller's prior call chain.
///
/// Normalizing an ensured term to its constant used to re-walk every earlier
/// call's ensures, deep-comparing each same-address load at another snapshot:
/// the Nth call cost O(N^2) and the proof O(N^3). The constant is now a class
/// lookup maintained as each fact is inserted, so the last call's lowering is
/// flat in N and the whole proof is near-linear.
#[test]
fn counter_call_chain_ensure_lowering_stays_flat_per_call() {
    const LOWERING: &str = "verified call provisional ensure lowering";
    let mut last_lowering = Vec::new();
    let mut totals = Vec::new();
    for size in [8, 16, 32, 64] {
        let (c_source, click_source) = counter_call_chain(size);
        let ((verified, work), events) = crate::instrumentation::collect(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                verify_c0_sources(&click_source, &[("drive.c", c_source.as_str())])
            })
        });
        verified.unwrap_or_else(|error| {
            panic!("size {size} counter call chain failed: {}", error.message())
        });
        let lowerings = events
            .iter()
            .filter_map(|event| match event {
                crate::instrumentation::VerificationEvent::OperationFinished {
                    function,
                    name,
                    work,
                    ..
                } if name == LOWERING && function == "touch" => Some(*work),
                _ => None,
            })
            .collect::<Vec<_>>();
        // Verification lowers each call's ensures once in execution order;
        // certificate checking lowers them again, so read the costliest call
        // rather than a position.
        assert!(
            lowerings.len() >= size,
            "every call must lower its ensures: {lowerings:?}"
        );
        last_lowering.push((size, lowerings.iter().copied().max().unwrap()));
        totals.push(ScalingSample {
            size,
            work,
            named_work: BTreeMap::new(),
        });
    }
    let (_, smallest) = last_lowering[0];
    let (_, largest) = *last_lowering.last().unwrap();
    // Constant plus a logarithmic index factor: eight times the calls may
    // not even double the costliest call's lowering.
    assert!(
        largest <= smallest.max(1) * 2,
        "a call's ensure lowering must not grow with the prior call chain: {last_lowering:?}"
    );
    assert_near_linear_scaling("counter call chain", &totals);
}

/// One `step()` over a call whose external contract has `N` ensures lowers
/// them in work linear in `N`.
///
/// Each ensure is lowered under the call's context plus every fact already
/// published, and that context used to be rebuilt from the whole growing
/// fact list for every ensure: quadratic wall time (0.05 s, 0.23 s, 0.92 s
/// at 100, 200, 400 ensures; 25 s at 1,000) while the counter, which does not
/// charge a context rebuild, reported linear work. The context is now
/// extended by each ensure's own facts. The test pins both the charged
/// lowering work and the entries the verification's context rebuilds assume
/// (`context_rebuild_entries`), which a return of the per-ensure rebuild
/// makes quadratic.
#[test]
fn call_ensure_lowering_is_linear_in_the_ensure_count() {
    const SPANS: [&str; 2] = [
        "operation `verified call provisional ensure lowering`",
        "operation `verified call ensure lowering`",
    ];
    let mut samples = Vec::new();
    let mut lowering = Vec::new();
    let mut rebuilds = Vec::new();
    for size in [32, 64, 128, 256] {
        let ensures = (1..=size)
            .map(|k| format!("    ensures result != {k};\n"))
            .collect::<String>();
        let click_source = format!(
            "verifying \"many_ensures.c\";\n\n\
             extern int32 g(int32 x) {{\n{ensures}}}\n\n\
             int32 caller(int32 x) {{\n    ensures result != 1;\n}} by {{\n    \
             step();\n    step();\n    simp();\n}}\n"
        );
        let rebuilds_before = crate::kernel::reasoning::path_facts::context_rebuild_entries();
        let (verified, sample) = scaling_sample(size, || {
            verify_c0_sources(
                &click_source,
                &[(
                    "many_ensures.c",
                    "int32 g(int32 x);\n\nint32 caller(int32 x) {\n    return g(x);\n}\n",
                )],
            )
        });
        rebuilds.push(
            crate::kernel::reasoning::path_facts::context_rebuild_entries() - rebuilds_before,
        );
        verified.unwrap_or_else(|error| {
            panic!("size {size} many-ensures call failed: {}", error.message())
        });
        lowering.push(
            SPANS
                .iter()
                .map(|span| sample.named_work.get(*span).copied().unwrap_or(0))
                .sum::<usize>(),
        );
        samples.push(sample);
    }
    assert!(
        lowering[0] > 0,
        "the ensures were never lowered: {lowering:?}"
    );
    // Linear with a small allowance: each doubling of the ensures at most
    // 2.2 times the lowering work (a quadratic rebuild is 4 times).
    for pair in lowering.windows(2) {
        assert!(
            pair[1] * 10 <= pair[0] * 22,
            "call ensure lowering grows faster than the ensure count: {lowering:?}"
        );
    }
    for pair in rebuilds.windows(2) {
        assert!(
            pair[1] * 10 <= pair[0] * 22,
            "the call's context rebuilds grow faster than the ensure count: {rebuilds:?}"
        );
    }
    assert_near_linear_scaling("call ensure count", &samples);
}

/// One `step()` over a call whose external contract has `N` requirements,
/// each discharged by the caller's one order fact, checks them in work
/// linear in `N`.
///
/// Three costs grew with the requirements already checked: the requirement
/// context was rebuilt from every earlier requirement per requirement, the
/// memory-resolution fact match scanned every condition fact of that growing
/// context, and each new context's order facts were collected by scanning
/// every condition fact. The counter reported 10.5k, 38.5k, and 147k units
/// at 50, 100, and 200 requirements. The context is now extended, the match
/// reads the condition-match index, and the order facts are an index of
/// their own.
#[test]
fn call_requirement_checking_is_linear_in_the_requirement_count() {
    const SPAN: &str = "operation `verified call requirement checking`";
    let mut samples = Vec::new();
    let mut checking = Vec::new();
    let mut rebuilds = Vec::new();
    for size in [32, 64, 128, 256] {
        let requires = (1..=size)
            .map(|k| format!("    requires x != {k};\n"))
            .collect::<String>();
        let click_source = format!(
            "verifying \"many_requires.c\";\n\n\
             extern int32 g(int32 x) {{\n{requires}    ensures result == x;\n}}\n\n\
             int32 caller(int32 x) {{\n    requires x > {size};\n    ensures result == x;\n}} by {{\n    \
             step();\n    step();\n    simp();\n}}\n"
        );
        let rebuilds_before = crate::kernel::reasoning::path_facts::context_rebuild_entries();
        let (verified, sample) = scaling_sample(size, || {
            verify_c0_sources(
                &click_source,
                &[(
                    "many_requires.c",
                    "int32 g(int32 x);\n\nint32 caller(int32 x) {\n    return g(x);\n}\n",
                )],
            )
        });
        verified.unwrap_or_else(|error| {
            panic!("size {size} many-requires call failed: {}", error.message())
        });
        rebuilds.push(
            crate::kernel::reasoning::path_facts::context_rebuild_entries() - rebuilds_before,
        );
        checking.push(sample.named_work.get(SPAN).copied().unwrap_or(0));
        samples.push(sample);
    }
    assert!(
        checking[0] > 0,
        "the requirements were never checked: {checking:?}"
    );
    // Linear with a small allowance: each doubling of the requirements at
    // most 2.2 times the checking work (the quadratic was nearly 4 times).
    for pair in checking.windows(2) {
        assert!(
            pair[1] * 10 <= pair[0] * 22,
            "call requirement checking grows faster than the requirement count: {checking:?}"
        );
    }
    for pair in rebuilds.windows(2) {
        assert!(
            pair[1] * 10 <= pair[0] * 22,
            "the call's context rebuilds grow faster than the requirement count: {rebuilds:?}"
        );
    }
    assert_near_linear_scaling("call requirement count", &samples);
}

/// `execute()` runs an early-return fan-out on the checked `Proof` in work
/// near linear in its length.
///
/// The main path of an early-return fan-out learns one condition per `if`,
/// so its facts grow with its length. The function opens with a null check
/// on a fresh `malloc` result, which `execute()` used to hand to the planner;
/// the planner then built its own fact contexts along the path, 136, 248,
/// 472, and 920 entries at 4, 8, 16, and 32 returns on 2026-09-27. The
/// branch now splits on the `Proof`, which extends the goal's indexed facts
/// and builds no path context of its own. Measured on 2026-10-02 at the same
/// sizes: 1630, 2730, 5506, and 13362 units of `execute` work, against 3678,
/// 5946, 11058, and 23586 through the planner.
///
/// The whole verification's context builds are not asserted: finalization
/// reads every path's facts, which the checked execution stores whole per
/// path, so they grow with the square of the path on either route (75, 159,
/// 423, and 1335 entries here).
#[test]
fn executing_a_fan_out_is_near_linear_in_its_length() {
    std::thread::Builder::new()
        .name("fan-out-execute".into())
        .stack_size(64 << 20)
        .spawn(|| {
            let _ = roundtrip_sample(1, 0);
            const EXECUTE: &str = "smart tactic `execute`";
            let click = "verifying \"fan_out.c\";\n\nint g(int a) {\n    ensures result == a or result == -1;\n} by {\n    execute();\n    simp();\n}\n";
            let mut execute = Vec::new();
            for returns in [4, 8, 16, 32] {
                let c = early_return_fan_out(returns);
                let (verified, sample) = scaling_sample(returns, || {
                    verify_c0_sources(click, &[("fan_out.c", c.as_str())])
                });
                verified.unwrap_or_else(|error| {
                    panic!("fan-out of {returns} returns failed: {}", error.message())
                });
                execute.push(ScalingSample {
                    size: returns,
                    work: *sample.named_work.get(EXECUTE).unwrap_or_else(|| {
                        panic!("the fan-out was not run by `execute`: {sample:?}")
                    }),
                    named_work: BTreeMap::new(),
                });
            }
            eprintln!("fan-out execute work: {execute:?}");
            assert_near_linear_scaling("executing a fan-out's paths", &execute);
        })
        .expect("spawn the fan-out thread")
        .join()
        .expect("fan-out thread");
}

/// A copy loop whose preservation `simp` reaches a fact transport the
/// explicit-premise planner cannot view: the element just stored is named
/// `dst[k]` under `k == i - 1`, so `old(src[k]) == old(src[k])` does not
/// transport to it until `k` is rewritten. Each unrelated `requires` joins
/// the planner's candidate list. The planner decides the complete list
/// before it grows a prefix, so the failing plan costs the same number of
/// checks (six) at every size. It used to check once per growing prefix,
/// about 15k units per unrelated fact in each preservation attempt; the
/// remaining linear cost of lowering and offering a candidate is about 1k.
fn copy_loop_with_unrelated_requirements(fact_count: usize) -> String {
    let unrelated = (0..fact_count)
        .map(|index| format!("    requires length != {};\n", index + 100_000))
        .collect::<String>();
    format!(
        "verifying \"transport_copy.c\";\n\
         \n\
         int32 transport_copy(int32 dst[], int32 src[], int32 length) {{\n    \
             requires 0 <= length;\n    \
             requires ((uint32)length) <= 1073741823u32;\n    \
             owns dst[0..length];\n    \
             views src[0..length];\n    \
             requires separate(memory(dst[0..length]), memory(src[0..length]));\n\
         {unrelated}    \
             ensures result == length;\n\
         }} by {{\n    \
             step();\n    \
             step();\n    \
             loop {{\n        \
                 decreases length - i;\n        \
                 invariant 0 <= i;\n        \
                 invariant i <= length;\n        \
                 invariant forall (k: int32) {{ 0 <= k and k < i implies dst[k] == old(src[k]) }};\n        \
                 owns dst[0..length];\n        \
                 initialize by {{\n            \
                     have 0 <= i by {{\n                normalize();\n            }}\n            \
                     have i <= length by {{\n                assumption();\n            }}\n            \
                     have forall (k: int32) {{ 0 <= k and k < i implies dst[k] == old(src[k]) }} by {{\n                \
                         intro();\n                \
                         intro();\n                \
                         extract(0 <= k);\n                \
                         extract(k < i);\n                \
                         have i == 0 by {{\n                    normalize();\n                }}\n                \
                         have not (0 <= k) by {{\n                    \
                             arithmetic() using {{\n                        k < i;\n                        i == 0;\n                    }}\n                \
                         }}\n                \
                         contradiction(0 <= k);\n            \
                     }}\n        \
                 }}\n        \
                 preserve by {{\n            step();\n            step();\n            simp();\n        }}\n    \
             }}\n    \
             have i == length by {{\n        \
                 apply(int32_le_and_not_lt_implies_eq(at(loop(0).exit, i), at(loop(0).exit, length))) using {{\n            \
                     at(loop(0).exit, i) <= at(loop(0).exit, length);\n            \
                     not at(loop(0).exit, i) < at(loop(0).exit, length);\n        \
                 }}\n        \
                 assumption();\n    \
             }}\n    \
             step();\n    \
             simp();\n\
         }}\n"
    )
}

#[test]
fn failing_fact_transport_plan_ignores_unrelated_candidates() {
    const COPY_SOURCE: &str = "int32 transport_copy(int32 dst[], int32 src[], int32 length) {\n    \
                               int32 i;\n    i = 0;\n    while (i < length) {\n        \
                               dst[i] = src[i];\n        i = i + 1;\n    }\n    return i;\n}\n";
    let mut samples = Vec::new();
    let mut plan_checks = Vec::new();
    let mut simp_work = Vec::new();
    for size in [6, 12, 24, 48] {
        let click_source = copy_loop_with_unrelated_requirements(size);
        let ((verified, work), events) = crate::instrumentation::collect(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                verify_c0_sources(&click_source, &[("transport_copy.c", COPY_SOURCE)])
            })
        });
        verified.unwrap_or_else(|error| {
            panic!(
                "size {size} fact-transport scaling fixture failed: {}",
                error.message()
            )
        });
        let mut named_work = BTreeMap::<String, usize>::new();
        let mut checks = 0;
        let mut simp = 0;
        for event in events {
            match event {
                crate::instrumentation::VerificationEvent::OperationFinished {
                    name, work, ..
                } => {
                    if name == "explicit fact transport: premise check" {
                        checks += 1;
                    }
                    *named_work.entry(format!("operation `{name}`")).or_default() += work;
                }
                crate::instrumentation::VerificationEvent::TacticFinished {
                    tactic, work, ..
                } => {
                    if tactic.tactic_name == "simp" {
                        simp += work;
                    }
                    *named_work
                        .entry(format!("{} tactic `{}`", tactic.class, tactic.tactic_name))
                        .or_default() += work;
                }
                _ => {}
            }
        }
        plan_checks.push(checks);
        simp_work.push(simp);
        samples.push(ScalingSample {
            size,
            work,
            named_work,
        });
    }
    assert!(
        plan_checks[0] > 0,
        "the preservation simp never planned a fact transport: {plan_checks:?}"
    );
    assert!(
        plan_checks.iter().all(|checks| *checks == plan_checks[0]),
        "fact-transport planning checked once per unrelated candidate: {plan_checks:?}; \
         named work: {}",
        named_growth_diagnostic(&samples)
    );
    // Each unrelated requirement is still read, lowered, and offered as a
    // candidate, which is linear; a check per candidate cost an order of
    // magnitude more per fact.
    let per_fact = (simp_work[3] - simp_work[0]) / (48 - 6);
    assert!(
        per_fact <= 4_000,
        "simp work grew by {per_fact} units per unrelated requirement: {simp_work:?}"
    );
    assert_near_linear_scaling("fact-transport plan unrelated candidates", &samples);
}

/// Explicit fold read framing along a straight line of endpoint stores: each
/// store is followed by one `transport` of the prefix count, which crosses
/// exactly that store. Total work stays near linear in the number of stores,
/// and so does the framing rule's own named work, rather than rescanning the
/// history once per transport.
#[test]
fn explicit_fold_read_transport_along_a_store_sequence_is_near_linear() {
    let mut samples = Vec::new();
    let mut framing = Vec::new();
    for size in [4usize, 8, 16, 32] {
        let stores = (0..size)
            .map(|index| format!("    v[i] = {index};\n"))
            .collect::<String>();
        let c_source = format!("void mark(int32 *v, int32 i) {{\n{stores}}}\n");
        let steps = (0..size)
            .map(|index| {
                format!(
                    "    mark m{index};\n    step();\n    have zeros(v, 0, i) == 0 by {{\n        transport(\n            at(m{index}, zeros(v, 0, i)) == 0,\n            zeros(v, 0, i) == 0\n        ) using {{\n            at(m{index}, zeros(v, 0, i)) == 0;\n        }}\n        assumption();\n    }}\n"
                )
            })
            .collect::<String>();
        let click_source = format!(
            "verifying \"mark.c\";\n\n\
             function zeros(v: int32[], lo: int32, hi: int32) -> Integer {{\n    \
                 (lo..hi).fold(0, |acc, k| {{ acc + to_integer(if v[k] == 0 {{ 1 }} else {{ 0 }}) }})\n\
             }}\n\n\
             void mark(int32 *v, int32 i) {{\n    \
                 requires 0 <= i;\n    \
                 requires i < 1000;\n    \
                 requires zeros(v, 0, i) == 0;\n    \
                 owns v[i..(i + 1)];\n    \
                 ensures zeros(v, 0, i) == 0;\n\
             }} by {{\n{steps}    execute();\n    simp();\n}}\n"
        );
        let (verified, sample) = scaling_sample(size, || {
            verify_c0_sources(&click_source, &[("mark.c", c_source.as_str())])
        });
        verified.unwrap_or_else(|error| {
            panic!(
                "{size} framed endpoint stores should verify: {}",
                error.message()
            )
        });
        framing.push(
            sample
                .named_work
                .get("operation `explicit fact transport: fold read frame`")
                .copied()
                .unwrap_or(0),
        );
        samples.push(sample);
    }
    eprintln!(
        "fold read transport along stores: total {:?}, framing {framing:?}",
        samples.iter().map(|sample| sample.work).collect::<Vec<_>>()
    );
    assert!(
        framing[0] > 0,
        "the fold read frame did not run: {framing:?}"
    );
    for pair in framing.windows(2) {
        assert!(
            pair[1] <= pair[0].saturating_mul(3),
            "fold read framing work is not near linear in the store count: {framing:?}"
        );
    }
    assert_near_linear_scaling("explicit fold read transport along stores", &samples);
}

/// Collecting the variables of a state's memory reads the snapshot's counts,
/// kept once per session from its derivation base's, so a proof beside a
/// global array visits each of the array's cells once however many steps
/// collect the state's variables. Walking the live memory whole on every
/// collection visited them eight times for a one-statement body and 22 for
/// an eight-statement one (2020 and 5562 visits beside 250 elements, 8020
/// and 22062 beside 1000); a global array of 100000 elements exhausted the
/// wall-clock limit.
#[test]
fn collecting_a_states_variables_visits_a_global_array_once() {
    let c_source = |length: u64, statements: usize| {
        format!(
            "int32 g[{length}];\n\nint32 inc(int32 x) {{\n    int32 y = x;\n{}    return y;\n}}\n",
            "    y = y + 1;\n".repeat(statements)
        )
    };
    let click_source = |statements: usize| {
        format!(
            "verifying \"inc.c\";\n\nint32 inc(int32 x) {{\n    requires x < 100;\n    ensures result == x + {statements};\n}} by {{\n    execute();\n    simp();\n}}\n"
        )
    };
    let samples = [
        (250u64, 1usize),
        (250, 8),
        (500, 1),
        (500, 8),
        (1_000, 1),
        (1_000, 8),
    ]
    .map(|(length, statements)| {
        let (verified, visits) = crate::kernel::count_cells_collected(|| {
            verify_c0_sources(
                &click_source(statements),
                &[("inc.c", &c_source(length, statements))],
            )
        });
        verified.unwrap_or_else(|error| {
            panic!(
                "a body of {statements} statements beside a global array of {length} \
                     elements should verify: {}",
                error.message()
            )
        });
        (length, statements, visits)
    });
    for (length, statements, visits) in samples {
        let length = usize::try_from(length).expect("small length");
        assert!(
            visits <= length + 4 * statements + 16,
            "collection visits each element of the global array at most once: {samples:?}"
        );
    }
    for pair in samples.chunks(2) {
        let [(_, _, short), (_, _, long)] = pair else {
            unreachable!("samples come in pairs");
        };
        assert!(
            long - short <= 64,
            "more statements must not revisit the array: {samples:?}"
        );
    }
}

/// A constant range is one run of seeded cells, so a proof over it costs the
/// same whatever the range's length. Before runs, every element was a stored
/// cell and each load scanned all of them: `views a[0..100000]` exhausted
/// the simple-tactic budget, and `views a[0..1000000]` minted enough load
/// identities to collide.
#[test]
fn a_constant_view_costs_the_same_whatever_its_length() {
    let c_source = "int32 get(int32 *a, int32 i) { return a[i]; }\n";
    let click_source = |length: u64| {
        format!(
            "verifying \"get.c\";\n\nint32 get(int32 *a, int32 i) {{\n    views a[0..{length}];\n    requires 0 <= i;\n    requires i < {length};\n    ensures result == a[i];\n}} by {{\n    execute();\n    simp();\n}}\n"
        )
    };
    // One unmeasured verification first: what the first verification on a
    // thread pays once (parsing the prelude, filling shared caches) is not
    // a cost of the range.
    verify_c0_sources(&click_source(8), &[("get.c", c_source)]).expect("warm-up verifies");
    let samples = [8u64, 1_000, 1_000_000, 1_000_000_000].map(|length| {
        let measure = || {
            let (verified, work) = crate::instrumentation::measure_deterministic_work(|| {
                verify_c0_sources(&click_source(length), &[("get.c", c_source)])
            });
            verified.unwrap_or_else(|error| {
                panic!(
                    "a view of {length} elements should verify: {}",
                    error.message()
                )
            });
            work
        };
        let work = measure();
        // The work is the build profile's too: a debug build's self-checks
        // (at most `CHECKED_RUN_SLOTS` slots, so only the short views) must
        // not leave a later charged read cheaper than a release build finds
        // it. A length-8 view once cost 1796 in release and 1718 in debug:
        // contract entry named every element of a view of at most 64 to ask
        // whether each was loadable, and in debug a check had already named
        // them uncharged.
        let release_work = crate::instrumentation::without_debug_checks(measure);
        assert_eq!(
            work, release_work,
            "a view of {length} elements costs {work} with debug checks and {release_work} without"
        );
        (length, work)
    });
    let least = samples
        .iter()
        .map(|(_, work)| *work)
        .min()
        .expect("samples");
    let most = samples
        .iter()
        .map(|(_, work)| *work)
        .max()
        .expect("samples");
    assert!(least > 0, "{samples:?}");
    // Flat, not merely sublinear: the samples may differ by a few units of
    // fixed work, and the bound only has to rule out any growth with the
    // length.
    assert!(
        most - least <= 4,
        "deterministic work depends on the range's length: {samples:?}"
    );
}

/// A smart `close_invariants()` whose quantified invariant is not restated
/// at the back edge closes it from the loop head's own universal, not by
/// whole-bundle simplification. `search_terminates_by_unmarked_count.md`
/// transports the quantified `next` bound explicitly before closing; the
/// same proof without that transport must cost a small multiple of it.
/// Before the direct member pass, the variant's two closes spent about 300k
/// units (whole-bundle simplification failed, then the member planner
/// succeeded) against about 19k for the explicit proof.
#[test]
fn close_invariants_without_the_explicit_transport_costs_a_small_multiple() {
    let markdown = include_str!("../../../mdtests/search_terminates_by_unmarked_count.md");
    let mdtest = crate::cli::parse_mdtest(
        std::path::Path::new("search_terminates_by_unmarked_count.md"),
        markdown,
    )
    .unwrap();
    let explicit = mdtest.click_source.as_deref().unwrap().replace(
        "import \"unmarked_count_lemmas.click\";",
        include_str!("../../../mdtests/unmarked_count_lemmas.click"),
    );
    let c_sources = mdtest
        .c_sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    let transport = "            have forall (k: int32) {\n                0 <= k and k < n implies 0 <= next[k] and next[k] < n\n            } by {\n                transport(";
    let start = explicit
        .find(transport)
        .expect("the fixture transports the quantified bound explicitly");
    let end = start
        + explicit[start..]
            .find("            transport(\n                forall (k: int32) { 0 <= k and k < n implies at(iter, next[k]) == at(iter, next[k]) },")
            .expect("the next explicit proof step follows the transport");
    let implicit = format!("{}{}", &explicit[..start], &explicit[end..]);
    let measure = |source: &str| {
        let (verified, work) = crate::instrumentation::measure_deterministic_work(|| {
            verify_c0_sources(source, &c_sources)
        });
        verified.unwrap_or_else(|error| panic!("{}", error.message()));
        work
    };
    // The first verification on a thread fills shared caches once.
    measure(&explicit);
    let explicit_work = measure(&explicit);
    let implicit_work = measure(&implicit);
    assert!(
        implicit_work <= explicit_work.saturating_mul(3) / 2,
        "closing without the explicit transport costs {implicit_work} units against {explicit_work}"
    );
}

/// One quantified frame case: `stores` stores into the owned `visited`, a
/// quantified body of `conjuncts` framed reads of the viewed `left`, and
/// `facts` unrelated requirements in the context.
fn quantified_frame_project(stores: usize, conjuncts: usize, facts: usize) -> (String, String) {
    // Each store writes its own cell `visited[c{index}]`: repeated stores to
    // one cell collapse into one recorded step.
    let indices = (0..stores)
        .map(|index| format!(", int32 c{index}"))
        .collect::<String>();
    let store_lines = (0..stores)
        .map(|index| format!("    visited[c{index}] = {index};\n"))
        .collect::<String>();
    let signature = format!("void mark(int32 *left, int32 *visited, int32 n, int32 x{indices})");
    let c_source = format!("{signature} {{\n{store_lines}}}\n");
    let bounds = (0..stores)
        .map(|index| format!("    requires 0 <= c{index};\n    requires c{index} < n;\n"))
        .collect::<String>();
    let unrelated = (0..facts)
        .map(|index| format!("    requires x != {index};\n"))
        .collect::<String>();
    let body = |now: &str| vec![format!("{now}(left[k]) == old(left[k])"); conjuncts].join(" and ");
    let source = format!(
        "forall (k: int32) {{ 0 <= k and k < n implies {} }}",
        body("old")
    );
    let target = format!(
        "forall (k: int32) {{ 0 <= k and k < n implies {} }}",
        body("")
    );
    let steps = "    step();\n".repeat(stores);
    let click_source = format!(
        "verifying \"mark.c\";\n\n\
         {signature} {{\n{bounds}{unrelated}    \
             views left[0..n];\n    \
             owns visited[0..n];\n    \
             ensures {target};\n\
         }} by {{\n{steps}    transport({source}, {target}) using {{ {source}; }};\n    \
             execute();\n    simp();\n}}\n"
    );
    (c_source, click_source)
}

fn quantified_frame_samples(
    axis: &str,
    project: impl Fn(usize) -> (String, String),
) -> Vec<ScalingSample> {
    let mut samples = Vec::new();
    let mut framing = Vec::new();
    for size in [4usize, 8, 16, 32] {
        let (c_source, click_source) = project(size);
        let (verified, sample) = scaling_sample(size, || {
            verify_c0_sources(&click_source, &[("mark.c", c_source.as_str())])
        });
        verified.unwrap_or_else(|error| {
            panic!("{axis} at size {size} should verify: {}", error.message())
        });
        framing.push(
            sample
                .named_work
                .get("operation `explicit fact transport: quantified frame`")
                .copied()
                .unwrap_or(0),
        );
        samples.push(sample);
    }
    eprintln!(
        "{axis}: total {:?}, framing {framing:?}; named work: {}",
        samples.iter().map(|sample| sample.work).collect::<Vec<_>>(),
        named_growth_diagnostic(&samples)
    );
    assert!(
        framing[0] > 0,
        "{axis}: the quantified frame did not run: {framing:?}"
    );
    for pair in framing.windows(2) {
        assert!(
            pair[1] <= pair[0].saturating_mul(3),
            "{axis}: quantified frame work is not near linear: {framing:?}"
        );
    }
    samples
}

/// A quantified fact about a separated array crosses a straight line of
/// stores into the owned array. The frame walks each read's history once, so
/// its own work is near linear in the stores, and so is the whole
/// verification: each store's refusal to keep the earlier cell it may alias
/// reads only the order facts filed under the two indices
/// (`stores_to_bounded_unordered_indices_are_near_linear`), where it used to
/// scan every index's bounds (40,117 to 142,848 units at 4 to 32 stores).
#[test]
fn quantified_frame_is_near_linear_in_crossed_stores() {
    let samples = quantified_frame_samples("quantified frame across stores", |size| {
        quantified_frame_project(size, 1, 0)
    });
    assert_near_linear_scaling("quantified frame across stores", &samples);
}

/// The quantified body grows by one framed conjunct per step: one leaf and
/// one read question each, so near linear in the body.
#[test]
fn quantified_frame_is_near_linear_in_its_body() {
    let samples = quantified_frame_samples("quantified frame over its body", |size| {
        quantified_frame_project(2, size, 0)
    });
    assert_near_linear_scaling("quantified frame over its body", &samples);
}

/// Unrelated requirements join the context the frame reads, but it reads it
/// only by indexed lookup, so they cost the frame nothing beyond the
/// context's own construction.
#[test]
fn quantified_frame_is_near_linear_in_unrelated_facts() {
    let samples = quantified_frame_samples("quantified frame with unrelated facts", |size| {
        quantified_frame_project(2, 1, size)
    });
    assert_near_linear_scaling("quantified frame with unrelated facts", &samples);
}

/// A function whose contract views `size` arrays over one shared length and
/// owns one more, with a body that touches none of them.
fn many_viewed_arrays(size: usize, owned: bool) -> (String, String) {
    let params = (0..size)
        .map(|index| format!("int32 *a{index}"))
        .chain(owned.then(|| "int32 *out".to_string()))
        .chain(std::iter::once("int32 n".to_string()))
        .collect::<Vec<_>>()
        .join(", ");
    let c_source = format!("int32 f({params}) {{\n    return n;\n}}\n");
    let mut click_source = format!("verifying \"f.c\";\nint32 f({params}) {{\n");
    for index in 0..size {
        click_source.push_str(&format!("    views a{index}[0..n];\n"));
    }
    if owned {
        click_source.push_str("    owns out[0..1];\n");
    }
    click_source.push_str("    ensures result == n by auto;\n}\n");
    (c_source, click_source)
}

/// The entry of a contract with `N` views beside one owner
/// (`docs/internals/verification-efficiency.md`). The entry partition states
/// `N` owner/view separations, and each of the `N` derived `viewable` facts
/// looks for a held range covering it. That lookup used to ask every held
/// range of the parameters' shared block, and each asked the
/// explicit-separation veto first, which walks every separation: `N^3` at
/// entry (1,542,282 units at `N = 32`, against 140,617 now).
///
/// The veto's curve is pinned near-linear: it is now asked only of a pair
/// another route covers. Each `viewable` fact a proof starts from is one the
/// contract entry states outright, so no coverage lookup runs for it. The total is
/// held under a quadratic ceiling: installing borrowed inputs still asks
/// every held view of the block once per view
/// (`ResourceContext::view_occurrences_for_fact`, which must see every
/// candidate to refuse an ambiguous binding), so the total is not yet linear.
/// Its owner check (`ResourceContext::directly_supporting_owned_entry`) asks
/// only the block's owned ranges when no projection support is recorded, so
/// it no longer adds a second `N^2` term.
#[test]
fn contract_entry_with_many_views_beside_an_owner_is_not_cubic() {
    let samples = [4, 8, 16, 32]
        .into_iter()
        .map(|size| {
            let (c_source, click_source) = many_viewed_arrays(size, true);
            let (verified, sample) = scaling_sample(size, || {
                verify_c0_sources(&click_source, &[("f.c", c_source.as_str())])
            });
            verified.unwrap_or_else(|error| {
                panic!("size {size} many-views fixture failed: {}", error.message())
            });
            sample
        })
        .collect::<Vec<_>>();

    let curve = |name: &str| {
        samples
            .iter()
            .map(|sample| ScalingSample {
                size: sample.size,
                work: sample.named_work.get(name).copied().unwrap_or(0),
                named_work: BTreeMap::new(),
            })
            .collect::<Vec<_>>()
    };
    assert_near_linear_scaling(
        "explicit-separation veto beside many views",
        &curve("operation `memory range coverage: explicit separation`"),
    );
    // A quadratic curve quadruples per doubling and a cubic one multiplies
    // by eight; 4.5 separates them with room for fixed-cost noise.
    assert!(
        samples
            .windows(2)
            .skip(1)
            .all(|pair| pair[1].work.saturating_mul(2) <= pair[0].work.saturating_mul(9)),
        "many-views contract entry grows faster than quadratically: {samples:?}; named work: {}",
        named_growth_diagnostic(&samples),
    );
}

/// Unfolding a composite resource whose body holds a constant range exposes
/// its cells as one run, so the proof costs the same whatever the range's
/// length, for scalar elements and for pointer elements (whose cells keep
/// the word their load names). Before, each element was a named cell: at
/// 1000 elements a store after the unfold exhausted the smart budget.
#[test]
fn an_unfolded_constant_composite_range_costs_the_same_whatever_its_length() {
    let c_source = "int32 put(int32 *a) {\n    a[3] = 5;\n    return a[3];\n}\n\nvoid put_pointer(int32 **p, int32 *q) {\n    p[1] = q;\n}\n";
    let click_source = |length: u64| {
        format!(
            "verifying \"put.c\";\n\nresource block(p: int32*) {{ owns p[0..{length}]; }}\nresource pointers(p: int32**) {{ owns p[0..{length}]; }}\n\nint32 put(int32 *a) {{\n    consumes block(a);\n    produces block(a);\n    ensures result == 5;\n    ensures a[4] == old(a[4]);\n}} by {{\n    unfold(block(a));\n    execute();\n    fold(block(a));\n    simp();\n}}\n\nvoid put_pointer(int32 **p, int32 *q) {{\n    consumes pointers(p);\n    produces pointers(p);\n    ensures p[2] == old(p[2]);\n    ensures p[1] == q;\n}} by {{\n    unfold(pointers(p));\n    execute();\n    fold(pointers(p));\n    simp();\n}}\n"
        )
    };
    verify_c0_sources(&click_source(8), &[("put.c", c_source)]).expect("warm-up verifies");
    let samples = [64u64, 1_000, 1_000_000, 1_000_000_000].map(|length| {
        let (verified, work) = crate::instrumentation::measure_deterministic_work(|| {
            verify_c0_sources(&click_source(length), &[("put.c", c_source)])
        });
        verified.unwrap_or_else(|error| {
            panic!(
                "a composite range of {length} elements should verify: {}",
                error.message()
            )
        });
        (length, work)
    });
    let least = samples
        .iter()
        .map(|(_, work)| *work)
        .min()
        .expect("samples");
    let most = samples
        .iter()
        .map(|(_, work)| *work)
        .max()
        .expect("samples");
    assert!(least > 0, "{samples:?}");
    // Flat across seven orders of magnitude of length: the samples differ
    // by a few dozen units of fixed work that read the length's constant
    // (about 6k units in all), while one unit per element would be 10^9.
    // At 10^9 pointer elements the range's byte count overflows, so that
    // entry gains one fact, `false`. The typed pointer-read candidate index
    // charges that fixed fact and its lookup keys too. Allow at most 64
    // fixed units across all sizes, including that extra overflow fact;
    // this still excludes any per-element work (6124, 6156, 6156, 6180).
    assert!(
        most - least <= 64,
        "deterministic work depends on the composite range's length: {samples:?}"
    );
}

/// `N` stores `a[ck] = k`, each index bounded by `0 <= ck < n` and none
/// ordered against another, then a claim about the last one.
fn bounded_index_stores(stores: usize) -> (String, String) {
    let indices = (0..stores)
        .map(|index| format!(", int32 c{index}"))
        .collect::<String>();
    let signature = format!("void mark(int32 *a, int32 n{indices})");
    let store_lines = (0..stores)
        .map(|index| format!("    a[c{index}] = {index};\n"))
        .collect::<String>();
    let c_source = format!("{signature} {{\n{store_lines}}}\n");
    let bounds = (0..stores)
        .map(|index| format!("    requires 0 <= c{index};\n    requires c{index} < n;\n"))
        .collect::<String>();
    let last = stores - 1;
    let steps = "    step();\n".repeat(stores);
    let click_source = format!(
        "verifying \"mark.c\";\n\n{signature} {{\n{bounds}    owns a[0..n];\n    \
         ensures a[c{last}] == {last};\n}} by {{\n{steps}    execute();\n    simp();\n}}\n"
    );
    (c_source, click_source)
}

/// A straight line of `N` stores to indices that facts bound but do not
/// order. Each store drops the earlier cell it may alias, and deciding that
/// asks whether its index is below or above the cell's; both refusals walk
/// the order facts from the two indices to their shared bound `n`. The walk
/// used to compare every node it reached with every order and condition fact
/// of the context, which holds `2N` bounds, so each store cost the context
/// and the line cost `N^2`: the store rule's work was 2,294, 7,902, 28,334,
/// 106,062 and 408,974 units at 4 to 64 stores, almost all of it offset
/// cancellation. The walk now reads the edges filed under each node
/// (`OrderWalkIndex`), so a store's refusal costs the same beside any number
/// of other indices' bounds: 990, 2,162, 4,506, 9,194 and 18,570 units.
#[test]
fn stores_to_bounded_unordered_indices_are_near_linear() {
    const STORE_WORK: &str = "operation `verification statement: store`";
    let samples = [4, 8, 16, 32, 64]
        .into_iter()
        .map(|size| {
            let (c_source, click_source) = bounded_index_stores(size);
            let (verified, sample) = scaling_sample(size, || {
                verify_c0_sources(&click_source, &[("mark.c", c_source.as_str())])
            });
            verified.unwrap_or_else(|error| {
                panic!(
                    "{size} bounded-index stores should verify: {}",
                    error.message()
                )
            });
            sample
        })
        .collect::<Vec<_>>();
    let store_work = samples
        .iter()
        .map(|sample| {
            let work = sample.named_work.get(STORE_WORK).copied().unwrap_or(0);
            assert!(work > 0, "the stores did not run: {sample:?}");
            work
        })
        .collect::<Vec<_>>();
    // A linear curve doubles per doubling; a quadratic one quadruples. The
    // store rule is asked 9/4 at most over the three largest doublings, and
    // the whole verification the same, which the old walk exceeded at every
    // size (3.4 to 3.9 per doubling).
    let within = |low: usize, high: usize| high.saturating_mul(4) <= low.saturating_mul(9);
    assert!(
        store_work
            .windows(2)
            .skip(1)
            .all(|pair| within(pair[0], pair[1])),
        "the store rule's work over bounded unordered indices is not near linear: {store_work:?}; named work: {}",
        named_growth_diagnostic(&samples)
    );
    assert!(
        samples
            .windows(2)
            .skip(1)
            .all(|pair| within(pair[0].work, pair[1].work)),
        "stores to bounded unordered indices are not near linear: {samples:?}; named work: {}",
        named_growth_diagnostic(&samples)
    );
}

/// `N` stores `a[k] = k` to constant indices of one owned array, then a claim
/// about the first, which every later store has to keep.
fn constant_index_stores(stores: usize) -> (String, String) {
    let signature = "void mark(int32 *a)";
    let store_lines = (0..stores)
        .map(|index| format!("    a[{index}] = {index};\n"))
        .collect::<String>();
    let c_source = format!("{signature} {{\n{store_lines}}}\n");
    let steps = "    step();\n".repeat(stores);
    let click_source = format!(
        "verifying \"mark.c\";\n\n{signature} {{\n    owns a[0..{stores}];\n    \
         ensures a[0] == 0;\n}} by {{\n{steps}    execute();\n    simp();\n}}\n"
    );
    (c_source, click_source)
}

/// `N` stores `a[ck] = k` to indices one chain of order facts separates,
/// `0 <= c0 < c1 < … < n`, then a claim about the first.
fn chain_ordered_index_stores(stores: usize) -> (String, String) {
    chain_ordered_index_stores_in(stores, false)
}

/// [`chain_ordered_index_stores`] with the stores in the order `a[cN-1]`
/// first, down to `a[c0]` last, which is the index the claim names.
fn chain_ordered_index_stores_descending(stores: usize) -> (String, String) {
    chain_ordered_index_stores_in(stores, true)
}

fn chain_ordered_index_stores_in(stores: usize, descending: bool) -> (String, String) {
    let indices = (0..stores)
        .map(|index| format!(", int32 c{index}"))
        .collect::<String>();
    let signature = format!("void mark(int32 *a, int32 n{indices})");
    let mut order = (0..stores).collect::<Vec<_>>();
    if descending {
        order.reverse();
    }
    let store_lines = order
        .into_iter()
        .map(|index| format!("    a[c{index}] = {index};\n"))
        .collect::<String>();
    let c_source = format!("{signature} {{\n{store_lines}}}\n");
    let mut bounds = "    requires 0 <= c0;\n".to_string();
    for index in 1..stores {
        bounds.push_str(&format!("    requires c{} < c{index};\n", index - 1));
    }
    bounds.push_str(&format!("    requires c{} < n;\n", stores - 1));
    let steps = "    step();\n".repeat(stores);
    let click_source = format!(
        "verifying \"mark.c\";\n\n{signature} {{\n{bounds}    owns a[0..n];\n    \
         ensures a[c0] == 0;\n}} by {{\n{steps}    execute();\n    simp();\n}}\n"
    );
    (c_source, click_source)
}

fn store_line_samples(
    label: &str,
    fixture: impl Fn(usize) -> (String, String),
) -> Vec<ScalingSample> {
    [4, 8, 16, 32, 64]
        .into_iter()
        .map(|size| {
            let (c_source, click_source) = fixture(size);
            let (verified, sample) = scaling_sample(size, || {
                verify_c0_sources(&click_source, &[("mark.c", c_source.as_str())])
            });
            verified.unwrap_or_else(|error| {
                panic!("{size} {label} stores should verify: {}", error.message())
            });
            sample
        })
        .collect()
}

/// The store rule's work in each sample, which has to be nonzero.
fn store_rule_work(samples: &[ScalingSample]) -> Vec<usize> {
    samples
        .iter()
        .map(|sample| {
            let work = sample
                .named_work
                .get("operation `verification statement: store`")
                .copied()
                .unwrap_or(0);
            assert!(work > 0, "the stores did not run: {sample:?}");
            work
        })
        .collect()
}

/// Whether every one of the three largest doublings of `work` grows by at
/// most `numerator / denominator`.
fn doublings_within(work: &[usize], numerator: usize, denominator: usize) -> bool {
    work.windows(2)
        .skip(1)
        .all(|pair| pair[1].saturating_mul(denominator) <= pair[0].saturating_mul(numerator))
}

/// A straight line of `N` stores `a[k] = k` to constant indices. Each store
/// keeps every earlier cell, and it used to ask each one whether it may
/// alias: `N^2/2` questions, 445, 1,225, 3,761, 12,705 and 46,017 units of
/// store work at 4 to 64 stores. A cell whose offset shares the store's
/// anchor and whose constant byte gap clears both accesses is now kept
/// without being asked (`reasoning::store_gap`), so a store visits only the
/// cells within eight bytes of its own: 477, 1,155, 2,587, 5,483 and 11,339
/// units in a debug build, whose check re-asks a few skipped cells per store
/// (467 to 8,959 in release). The claim reads `a[0]`, so every store has to
/// keep it.
#[test]
fn stores_to_constant_indices_are_near_linear() {
    let samples = store_line_samples("constant-index", constant_index_stores);
    let store_work = store_rule_work(&samples);
    // Linear doubles per doubling; the old curve rose 3.1 to 3.6.
    assert!(
        doublings_within(&store_work, 9, 4),
        "the store rule's work over constant indices is not near linear: {store_work:?}; named work: {}",
        named_growth_diagnostic(&samples)
    );
}

/// A straight line of `N` stores `a[ck] = k` whose indices one chain of
/// order facts separates, `0 <= c0 < c1 < … < n`. Each store asks every
/// earlier cell, and each question walks the order chain between its two
/// indices, so the line cost `N^3`: 830, 3,582, 20,494, 139,342 and
/// 1,032,462 units of store work at 4 to 64 stores. The walk now shares what
/// it learns across the questions toward one index (`OrderReachMemo`), so a
/// question costs a constant beyond the first, a store is linear in the
/// cells it keeps, and the line is the `N^2/2` questions themselves: 738,
/// 2,394, 8,506, 31,898 and 123,290 in order, and 900 to 149,372 with the
/// stores in reverse order. A cubic curve multiplies by eight per doubling;
/// the bound admits the quadratic four and rejects that.
#[test]
fn stores_to_chain_ordered_indices_are_quadratic_not_cubic() {
    for (label, fixture) in [
        (
            "chain-ordered",
            chain_ordered_index_stores as fn(usize) -> (String, String),
        ),
        (
            "reverse chain-ordered",
            chain_ordered_index_stores_descending,
        ),
    ] {
        let samples = store_line_samples(label, fixture);
        let store_work = store_rule_work(&samples);
        assert!(
            doublings_within(&store_work, 17, 4),
            "the store rule's work over {label} indices grows faster than quadratically: {store_work:?}; named work: {}",
            named_growth_diagnostic(&samples)
        );
    }
}

#[test]
fn resource_reference_entry_setup_has_near_linear_work() {
    let samples = [16, 64, 256].map(|count| {
        let mut source = String::from(
            "resource cell() { field revision: int32; }\n\
             resource record(target: cell()) { field revision: int32; }\n\
             void f() { owns target: cell();\n",
        );
        for index in 0..count {
            source.push_str(&format!("owns r{index}: record(target);\n"));
        }
        source.push_str("}\n");
        let file = parser::parse(&source).unwrap();
        let ((context, work), persistent_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                crate::surface::lowering::resource_context_from_requirements(
                    file.function_blocks()[0].requires(),
                    &[],
                    &[],
                    &crate::kernel::CState::new(),
                )
                .unwrap()
            })
        });
        assert_eq!(context.facts().len(), count + 1);
        (count, work, persistent_work)
    });
    assert!(samples[0].1 > 0, "entry setup must be metered: {samples:?}");
    for pair in samples.windows(2) {
        assert!(pair[1].1 <= pair[0].1 * 4, "{samples:?}");
        assert!(
            pair[1].2 <= pair[0].2 * 6,
            "persistent indexes: {samples:?}"
        );
    }
}

/// `arithmetic() using` over a chain of listed order facts adds the premises
/// once each, so its work grows with the chain and not with its square.
/// Both a signed and an unsigned chain are measured at several lengths.
#[test]
fn listed_order_chain_arithmetic_is_near_linear_in_the_chain() {
    for (value_type, bound) in [("int32", "4"), ("uint32", "4u32")] {
        let samples = [8usize, 16, 32].map(|edges| {
            let names = (0..edges).map(|index| format!("v{index}")).collect::<Vec<_>>();
            let parameters = names
                .iter()
                .map(|name| format!("{name}: {value_type}"))
                .collect::<Vec<_>>()
                .join(", ");
            let mut facts = names
                .windows(2)
                .map(|pair| format!("{} <= {}", pair[0], pair[1]))
                .collect::<Vec<_>>();
            facts.push(format!("{} < {bound}", names[edges - 1]));
            let requires = facts
                .iter()
                .map(|fact| format!("requires {fact}; "))
                .collect::<String>();
            let listed = facts
                .iter()
                .map(|fact| format!("{fact}; "))
                .collect::<String>();
            let source = format!(
                "theorem chained({parameters}) {{ {requires}ensures v0 < {bound} by {{ arithmetic() using {{ {listed}}} }} }}"
            );
            let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                verify_c0_sources(&source, &[])
            });
            result.unwrap_or_else(|error| panic!("{edges}-edge chain: {}", error.message()));
            (edges, work)
        });
        eprintln!("{value_type} chain work: {samples:?}");
        for pair in samples.windows(2) {
            assert!(
                pair[1].1 <= pair[0].1.saturating_mul(3),
                "{value_type}: {samples:?}"
            );
        }
    }
}

/// A `step()` written in a loop's `preserve` body is its own simple tactic:
/// it has its own work event and its own simple budget, like a `step()`
/// anywhere else. The preservation driver used to apply it with no tactic
/// open, so every C statement of every path through the body was charged to
/// the enclosing `loop`, whose single budget then capped the whole proof
/// however small each step was. The loop's own work must not grow with what
/// its body steps through.
#[test]
fn preserve_body_steps_are_charged_to_themselves_not_to_the_loop() {
    let sample = |stores: usize| {
        let c_source = format!(
            "void fill(int32 *p, int32 n) {{\n    int32 i = 0;\n    while (i < n) {{\n{}        i = i + 1;\n    }}\n}}\n",
            (0..stores)
                .map(|index| format!("        p[0] = {index};\n"))
                .collect::<String>()
        );
        let click_source = format!(
            "verifying \"fill.c\";

void fill(int32* p, int32 n) {{
    owns p[0..1];
    requires n >= 0;
}} by {{
    step();
    step();
    loop {{
        decreases n - i;
        invariant i >= 0;

        initialize by simp;
        preserve by {{
{}        }}
    }}
    step();
    simp();
}}
",
            "            step();\n".repeat(stores + 1)
        );
        let (result, events) = crate::instrumentation::collect(|| {
            verify_c0_sources(&click_source, &[("fill.c", &c_source)])
        });
        result.unwrap_or_else(|error| {
            panic!("the {stores}-store loop should verify: {}", error.message())
        });
        let finished = |name: &str| {
            events
                .iter()
                .filter_map(|event| match event {
                    crate::instrumentation::VerificationEvent::TacticFinished {
                        tactic,
                        work,
                        ..
                    } if tactic.tactic_name == name => Some(*work),
                    _ => None,
                })
                .collect::<Vec<_>>()
        };
        let loop_work = finished("loop").into_iter().max().unwrap_or(0);
        (stores, finished("step").len(), loop_work)
    };
    let samples = [2, 8, 32].map(sample);
    let (_, base_steps, base_loop_work) = samples[0];
    for &(stores, steps, loop_work) in &samples {
        // The proof is checked the same number of times at every size, so
        // the step events grow by that many per added body statement.
        assert!(
            steps >= base_steps + (stores - 2),
            "every `step()` in the preserve body must report its own work: \
             (stores, step events, loop work) {samples:?}"
        );
        // A few units of frontier bookkeeping per statement, never the
        // statement's own execution.
        assert!(
            loop_work <= base_loop_work + 16 * (stores - 2),
            "the loop must not be charged for the statements its body steps through: \
             (stores, step events, loop work) {samples:?}"
        );
    }
}

/// One loop with `exits` ways out, all holding the same binder: a balanced
/// tree of case splits over `k`, each leaf writing the binder's cell,
/// refolding it, and leaving through a `break`. With `c_branches` the tree is
/// the C's own nested `if`s, so the exits are C paths; without it the C is
/// one store and one `break`, and the exits are the proof's case splits, as
/// in the rbtree insert fixup.
fn loop_with_break_exits(exits: usize, c_branches: bool) -> (String, String) {
    fn c_tree(low: usize, high: usize, indent: usize) -> String {
        let pad = " ".repeat(indent);
        if high - low == 1 {
            return format!("{pad}p->shade = {};\n{pad}break;\n", low % 2);
        }
        let middle = (low + high) / 2;
        format!(
            "{pad}if (k < {middle}) {{\n{}{pad}}} else {{\n{}{pad}}}\n",
            c_tree(low, middle, indent + 4),
            c_tree(middle, high, indent + 4)
        )
    }
    fn proof_tree(low: usize, high: usize, c_branches: bool) -> String {
        if high - low == 1 {
            let color = if !c_branches || low.is_multiple_of(2) {
                "Red"
            } else {
                "Black"
            };
            return format!(
                "step();\nlet c = fold(painted(p), {{ color: Color::{color} }});\nstep();\n"
            );
        }
        let middle = (low + high) / 2;
        let enter = if c_branches { "step();\n" } else { "" };
        format!(
            "if k < {middle} {{\n{enter}{}}} else {{\n{enter}{}}}\n",
            proof_tree(low, middle, c_branches),
            proof_tree(middle, high, c_branches)
        )
    }
    let body = if c_branches {
        c_tree(0, exits, 8)
    } else {
        "        p->shade = 0;\n        break;\n".to_string()
    };
    let c_source = format!(
        "struct node {{ int32 shade; }};\n\nvoid paint(struct node* p, int32 k) {{\n    while (true) {{\n{body}    }}\n}}\n"
    );
    let click_source = format!(
        "verifying \"paint.c\";

spec enum Color {{ Red, Black }}

resource painted(p: struct node*) {{
    field color: Color;
    match color {{
        Color::Red => {{ owns p->shade; fact p->shade == 0; }},
        Color::Black => {{ owns p->shade; fact p->shade == 1; }},
    }}
}}

void paint(struct node* p, int32 k) {{
    owns c: painted(p);
    requires c.color == Color::Black;
}} by {{
    loop {{
        decreases 0;
        owns c: painted(p);
        invariant c.color == Color::Black;

        preserve by {{
            unfold(c);
{}        }}
    }}
    step();
    simp();
}}
",
        proof_tree(0, exits, c_branches)
    );
    (c_source, click_source)
}

fn loop_with_break_exits_work(exits: usize, c_branches: bool) -> usize {
    let (c_source, click_source) = loop_with_break_exits(exits, c_branches);
    let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
        verify_c0_sources(&click_source, &[("paint.c", &c_source)])
    });
    result.unwrap_or_else(|error| {
        panic!(
            "the loop with {exits} exits should verify: {}",
            error.message()
        )
    });
    work
}

/// Joining a loop's `break` exits costs work proportional to the exits and
/// what each states, not to their pairs. Two steps used to compare every exit
/// with every other and were not charged at all: the exit join's disjunction
/// asked each fact of each exit against every fact of every earlier exit, and
/// the proof layer recorded each exit after comparing it with every exit
/// recorded before it. Each is now a keyed lookup that charges what it reads,
/// so counted work follows the real cost and quadruples, no more, when the
/// exits do.
///
/// Every proof-level case split in the body also read its path's certificate,
/// which walked the proof's whole history back to the root, sibling arms
/// included. Each node now remembers the lineage that ends at it, so a split
/// reads only the nodes added since the last walk that passed, and the walk
/// is charged.
///
/// The bound is on each fourfold step rather than on the whole range, because
/// at these sizes a pairwise term is still a small part of the total: with the
/// exits recorded pairwise again the last step is 4.75 times, and with the
/// history walked in full again it is 9.5 times, against 3.97.
#[test]
fn loop_break_exit_join_work_is_near_linear_in_the_exits() {
    let samples =
        [32usize, 128, 512].map(|exits| (exits, loop_with_break_exits_work(exits, false)));
    for pair in samples.windows(2) {
        let ((_, smaller), (_, larger)) = (pair[0], pair[1]);
        assert!(
            larger * 100 <= smaller * 430,
            "loop exit work must be near linear in the exits: (exits, work) {samples:?}"
        );
    }
    // The same exits as paths of the C's own nested branches. Their counted
    // work is the tactics' and is proportional already; what was quadratic
    // there was the uncharged source layout of the branch tree, which this
    // only exercises.
    let branches = [16usize, 64].map(|exits| (exits, loop_with_break_exits_work(exits, true)));
    assert!(
        branches[1].1 * 100 <= branches[0].1 * 430,
        "loop exit work over C branches must be near linear in the exits: {branches:?}"
    );
}
