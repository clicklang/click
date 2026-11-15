//! Typed specification lambdas elaborate to the existing value language.
//! Applications introduce typed lexical lets, preserving simultaneous argument
//! binding and capture avoidance without adding higher-order kernel search.
use super::*;

pub(super) fn signature(parameters: &[(String, ClickType)], result: &ClickType) -> ClickType {
    ClickType::Function {
        parameters: parameters.iter().map(|(_, ty)| ty.clone()).collect(),
        result: Box::new(result.clone()),
    }
}

/// Read the explicit result carrier without erasing the caller's Integer
/// scope. Full argument/body checking belongs to scoped expression typing.
pub(super) fn application_result_type(function: &ContractExpression) -> Result<ClickType, String> {
    if let ContractExpression::Lambda { result, .. } = function {
        return Ok(result.clone());
    }
    if let Some(reduced) = reduce_head(function)? {
        return application_result_type(&reduced);
    }
    Err("application expects a specification lambda value".into())
}

/// Only a literal closure has an executable body in this first slice.
/// Function parameters and opaque function results are a later extension.
pub(super) fn reduce_head(
    expression: &ContractExpression,
) -> Result<Option<ContractExpression>, String> {
    match expression {
        ContractExpression::Let {
            name,
            click_type,
            value,
            body,
        } if matches!(value.as_ref(), ContractExpression::Lambda { .. }) => {
            let ContractExpression::Lambda {
                parameters, result, ..
            } = value.as_ref()
            else {
                unreachable!()
            };
            if let Some(expected) = click_type {
                let actual = signature(parameters, result);
                if expected != &actual {
                    return Err(format!(
                        "let binding `{name}` expects {}, got {}",
                        validation::describe_click_type(expected),
                        validation::describe_click_type(&actual)
                    ));
                }
            }
            lowering::substitute_contract_expression(
                body,
                &BTreeMap::from([(name.clone(), value.as_ref().clone())]),
            )
            .map(Some)
        }
        ContractExpression::Apply {
            function,
            arguments,
        } => {
            let reduced = reduce_head(function)?;
            let function = reduced.as_ref().unwrap_or(function);
            let ContractExpression::Lambda {
                parameters,
                result,
                body,
            } = function
            else {
                if reduced.is_some() {
                    return Ok(Some(ContractExpression::Apply {
                        function: Box::new(function.clone()),
                        arguments: arguments.clone(),
                    }));
                }
                return Err("application expects a specification lambda value".into());
            };
            if parameters.len() != arguments.len() {
                return Err(format!(
                    "lambda expects {} arguments, got {}",
                    parameters.len(),
                    arguments.len()
                ));
            }
            let mut used = BTreeSet::new();
            lowering::collect_contract_expression_referenced_names(body, &mut used);
            lowering::collect_contract_expression_binding_names(body, &mut used);
            for argument in arguments {
                lowering::collect_contract_expression_referenced_names(argument, &mut used);
                lowering::collect_contract_expression_binding_names(argument, &mut used);
            }
            let mut next = 0;
            let mut fresh = || loop {
                let name = format!("__lambda_{next}");
                next += 1;
                if used.insert(name.clone()) {
                    break name;
                }
            };
            let bindings = parameters
                .iter()
                .map(|(name, ty)| (name.clone(), fresh(), ty.clone()))
                .collect::<Vec<_>>();
            let result_name = fresh();
            let replacements = bindings
                .iter()
                .map(|(old, new, _)| (old.clone(), ContractExpression::Binding(new.clone())))
                .collect::<BTreeMap<_, _>>();
            let body = lowering::substitute_contract_expression(body, &replacements)?;
            let mut applied = ContractExpression::Let {
                name: result_name.clone(),
                click_type: Some(result.clone()),
                value: Box::new(body),
                body: Box::new(ContractExpression::Binding(result_name)),
            };
            for ((_, name, ty), argument) in bindings.into_iter().zip(arguments).rev() {
                applied = ContractExpression::Let {
                    name,
                    click_type: Some(ty),
                    value: Box::new(argument.clone()),
                    body: Box::new(applied),
                };
            }
            Ok(Some(applied))
        }
        _ => Ok(None),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn typed_lambdas_reject_invalid_signatures_and_applications() {
        for (expression, diagnostic) in [
            (
                "(|x: Integer| -> Integer { x })(1, 2)",
                "lambda expects 1 arguments",
            ),
            ("(|x: Integer| -> Integer { x })(1u64)", "expects Integer"),
            (
                "(|x: uint64| -> uint64 { x })(to_integer(1))",
                "expects uint64",
            ),
            (
                "(|x: Integer, x: Integer| -> Integer { x })(1, 2)",
                "duplicate lambda parameter",
            ),
            ("(|x| -> Integer { x })(1)", "expected `:`"),
            ("(1)(2)", "application expects a specification lambda"),
            (
                "(|x: int32*| -> int32 { 0 })(0)",
                "lambda parameters and results",
            ),
            (
                "(|x: int32| -> int32 { x })()",
                "lambda expects 1 arguments",
            ),
            (
                "let f = |x: Integer| -> Integer { x }; f",
                "fn(Integer) -> Integer",
            ),
            (
                "let f = |x: int32| -> int32 { 1u64 }; 0",
                "lambda result expects int32",
            ),
            (
                "let f: fn(int32) -> int32 = |x: Integer| -> Integer { x }; 0",
                "expects fn(int32) -> int32",
            ),
        ] {
            let result = if expression.starts_with("(|x: uint64|") {
                "uint64"
            } else {
                "int32"
            };
            let source = format!("function test() -> {result} {{ {expression} }}");
            let error = parser::parse(&source).expect_err(&source);
            assert!(
                error.message().contains(diagnostic),
                "{source}: {}",
                error.message()
            );
        }
    }

    #[test]
    fn typed_lambdas_reject_memory_reads_even_when_unused() {
        let source =
            "function test(p: int32*) -> int32 { let f = |x: int32| -> int32 { p[x] }; 0 }";
        let error = parser::parse(source)
            .expect_err("memory reads require an explicit future lambda contract");
        assert!(
            error.message().contains("lambdas cannot read memory"),
            "{}",
            error.message()
        );
    }

    #[test]
    fn typed_lambda_expansion_rechecks_without_search() {
        let source =
            "theorem expand() { ensures (|x: Integer| -> Integer { x + 1 })(3) == 4 by solve(); }";
        let verified = verify_click_theorems(source).unwrap();
        let expanded = verified[0].expanded_proof_source().unwrap();
        assert!(!expanded.contains("solve("), "{expanded}");
        let rechecked = source.replace("by solve();", &expanded);
        verify_click_theorems(&rechecked)
            .unwrap_or_else(|error| panic!("{rechecked}: {}", error.report()));
    }

    #[test]
    fn typed_lambda_application_does_not_prove_a_false_result() {
        let source = "theorem false_result() { ensures (|x: Integer| -> Integer { x + 1 })(3) == 5 by solve(); }";
        let error =
            verify_click_theorems(source).expect_err("beta application preserves the lambda body");
        assert_eq!(error.kind(), ClickErrorKind::Proof, "{}", error.report());
    }

    #[test]
    fn typed_lambdas_reject_function_values_used_as_scalars_in_unused_bodies() {
        for (body, diagnostic) in [
            (
                "(|x: int32| -> int32 { x }) + 1",
                "cannot be arithmetic operands",
            ),
            ("~(|x: int32| -> int32 { x })", "cannot be bitwise operands"),
            (
                "identity(|x: int32| -> int32 { x })",
                "got a specification function",
            ),
        ] {
            let source = format!(
                "function identity(x: int32) -> int32 {{ x }} function test() -> int32 {{ let unused = |x: int32| -> int32 {{ {body} }}; 0 }}"
            );
            let error = parser::parse(&source).expect_err("unused lambda bodies remain typed");
            assert!(
                error.message().contains(diagnostic)
                    || error.message().contains("lambda is not a scalar"),
                "{}",
                error.message()
            );
        }
    }

    #[test]
    fn typed_lambdas_reject_indirect_memory_reads() {
        let source = "function read(p: int32*) -> int32 { p[0] } function test(p: int32*) -> int32 { let f = |x: int32| -> int32 { read(p) }; 0 }";
        let error = parser::parse(source).expect_err("memory dependence follows named calls");
        assert!(
            error.message().contains("memory-dependent function `read`"),
            "{}",
            error.message()
        );
    }

    #[test]
    fn typed_lambda_printing_round_trips() {
        let source = "function test(n: Integer) -> Integer { let f: fn(Integer) -> Integer = |x: Integer| -> Integer { x + n }; f(3) }";
        let file = parser::parse(source).unwrap();
        let body = diagnostics::describe_contract_expression(
            file.click_function_definitions()[0].body().unwrap(),
        );
        let reparsed = parser::parse(&format!(
            "function test(n: Integer) -> Integer {{ {body} }}"
        ))
        .unwrap();
        assert_eq!(
            file.click_function_definitions()[0].body(),
            reparsed.click_function_definitions()[0].body()
        );
    }
}
