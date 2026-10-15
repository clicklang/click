// Scaling tests of `src/languages/cpp/budget.rs` (module `tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn function_budgets_count_both_arms_and_catch_bindings_without_environment_copies() {
    use super::super::super::schema::*;
    let span = fixture(vec![]).span;
    let place = CppPlace {
        declaration_id: "local".into(),
        name: "local".into(),
        value_type: CppType::Integer {
            bits: 32,
            signed: true,
            is_const: false,
            source_aliases: vec![],
        },
        span: span.clone(),
    };
    let value = CppExpression::IntegerLiteral {
        value: "0".into(),
        value_type: place.value_type.clone(),
        span: span.clone(),
    };
    let declaration = CppStatement::Declare {
        local: place.clone(),
        initializer: CppInitializer::Value {
            value: value.clone(),
        },
        span: span.clone(),
    };
    for size in [4, 32, 256, MAX_LOCAL_DECLARATIONS] {
        let mut function = fixture(vec![declaration.clone(); size]);
        let (result, work) =
            crate::instrumentation::measure_deterministic_work(|| check_function(&function));
        result.unwrap();
        assert_eq!(work, size);
        function.body.push(CppStatement::TryCatchInt32 {
            try_body: vec![],
            binding: place.clone(),
            handler: vec![],
            span: span.clone(),
        });
        if size == MAX_LOCAL_DECLARATIONS {
            assert!(
                check_function(&function)
                    .unwrap_err()
                    .contains("local declarations per function")
            );
        } else {
            check_function(&function).unwrap();
        }
    }
    let scope = CppStatement::Scope {
        body: vec![declaration.clone()],
        cleanups: vec![],
        span: span.clone(),
    };
    for size in [4, 16, 64, MAX_CLEANUP_SCOPES] {
        let function = fixture(vec![scope.clone(); size]);
        let (result, work) =
            crate::instrumentation::measure_deterministic_work(|| check_function(&function));
        result.unwrap();
        assert_eq!(work, 2 * size);
    }
    let both_arms = CppStatement::If {
        condition: value.into(),
        then_branch: vec![scope.clone(); MAX_CLEANUP_SCOPES / 2],
        else_branch: vec![scope; MAX_CLEANUP_SCOPES / 2 + 1],
        span: span.clone(),
    };
    assert!(
        check_function(&fixture(vec![both_arms]))
            .unwrap_err()
            .contains("cleanup scopes per function")
    );
    let nested = CppStatement::Scope {
        body: vec![declaration; MAX_LOCAL_DECLARATIONS + 1],
        cleanups: vec![],
        span,
    };
    assert!(
        check_function(&fixture(vec![nested]))
            .unwrap_err()
            .contains("local declarations per function")
    );
}

#[test]
fn serialized_budget_work_is_linear_in_input_bytes() {
    for size in [8, 32, 128, 512] {
        let input = format!("[{}]", "{},".repeat(size));
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            check_serialized(input.as_bytes())
        });
        result.unwrap();
        assert_eq!(work, input.len());
    }
}
