//! The contracts Click supplies for the Rust core methods an import calls:
//! each states the method's result with the library's specification function
//! of the same path, `ensures result == click::rust::u32::min(a, b);`. They
//! are assumptions, as an `extern fn` contract is.
use super::schema::{RustExport, Type};

/// The `extern fn` contract of each core method `export` declares.
pub(super) fn contracts(export: &RustExport) -> String {
    let mut source = String::new();
    for function in &export.functions {
        let Some(specification) = &function.core_method else {
            continue;
        };
        let spell = |ty: &Type| -> String {
            match ty.scalar_name() {
                Some(name) => name.into(),
                // An `Option` result is of the parameters' type.
                None => format!(
                    "Option<{}>",
                    function.parameters[0]
                        .value_type
                        .scalar_name()
                        .expect("a core method takes integers")
                ),
            }
        };
        let parameters = function
            .parameters
            .iter()
            .map(|parameter| format!("{}: {}", parameter.name, spell(&parameter.value_type)))
            .collect::<Vec<_>>()
            .join(", ");
        let arguments = function
            .parameters
            .iter()
            .map(|parameter| parameter.name.as_str())
            .collect::<Vec<_>>()
            .join(", ");
        source.push_str(&format!(
            "\nextern fn {}({parameters}) -> {} {{\n    ensures result == {specification}({arguments});\n}}\n",
            function.name,
            spell(&function.return_type),
        ));
    }
    source
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::languages::rust::schema::{Function, Place, Span};
    use std::collections::BTreeSet;

    /// The library's core-method module of each integer type.
    const MODULES: &[(&str, bool, &str)] = &[
        ("i8", true, include_str!("../../../library/rust/i8.click")),
        ("i16", true, include_str!("../../../library/rust/i16.click")),
        ("i32", true, include_str!("../../../library/rust/i32.click")),
        ("i64", true, include_str!("../../../library/rust/i64.click")),
        (
            "isize",
            true,
            include_str!("../../../library/rust/isize.click"),
        ),
        ("u8", false, include_str!("../../../library/rust/u8.click")),
        (
            "u16",
            false,
            include_str!("../../../library/rust/u16.click"),
        ),
        (
            "u32",
            false,
            include_str!("../../../library/rust/u32.click"),
        ),
        (
            "u64",
            false,
            include_str!("../../../library/rust/u64.click"),
        ),
        (
            "usize",
            false,
            include_str!("../../../library/rust/usize.click"),
        ),
    ];

    fn functions(source: &str) -> BTreeSet<&str> {
        source
            .lines()
            .filter_map(|line| line.strip_prefix("function "))
            .map(|rest| rest.split('(').next().unwrap())
            .collect()
    }

    #[test]
    fn every_integer_type_has_the_same_core_methods() {
        let unsigned = functions(MODULES[5].2);
        for (name, signed, source) in MODULES {
            let mut expected = unsigned.clone();
            if *signed {
                expected.insert("unsigned_abs");
            }
            assert_eq!(functions(source), expected, "{name}");
        }
    }

    #[test]
    fn a_core_method_contract_states_its_result_with_the_library_function() {
        let span = Span { line: 1, column: 1 };
        let place = |name: &str| Place {
            name: name.into(),
            value_type: Type::U32,
            span: span.clone(),
        };
        let export = RustExport {
            schema: super::super::schema::SCHEMA,
            compiler_commit: String::new(),
            target: String::new(),
            edition: String::new(),
            overflow_checks: true,
            panic: String::new(),
            mir_opt_level: 0,
            logical_source: String::new(),
            records: vec![],
            enums: vec![],
            functions: vec![Function {
                name: "__rust_q_I3_u32_I11_checked_add".into(),
                return_type: Type::Enum {
                    name: "Option<u32>".into(),
                },
                parameters: vec![place("a"), place("b")],
                body: vec![],
                mir: None,
                external: true,
                captures: 0,
                implements: None,
                instance_of: None,
                core_method: Some("click::rust::u32::checked_add".into()),
                span,
            }],
        };
        assert_eq!(
            contracts(&export),
            "\nextern fn __rust_q_I3_u32_I11_checked_add(a: u32, b: u32) -> Option<u32> {\n    \
             ensures result == click::rust::u32::checked_add(a, b);\n}\n"
        );
    }
}
