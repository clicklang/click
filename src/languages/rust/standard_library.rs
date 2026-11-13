//! The contracts Click supplies for the Rust core methods an import calls.
//! They are assumptions, as an `extern fn` contract is. The `Vec`, slice,
//! slice-iterator, `ChunksExact`, `Option::unwrap` and `Result::unwrap`
//! methods are generic `extern fn` blocks in `library/rust/core.click`,
//! written out at each instance as a sidecar's generic functions are. The
//! integer methods are one-line `extern fn` contracts in
//! `library/rust/integers.click`, `u32::min`, each stating its result with
//! the library's specification function of the same path. This file keeps
//! only the name tables.
use super::schema::{RustExport, Type};
use std::collections::BTreeSet;

/// The `core_method` of `<[T]>::swap`, whose contract states its effect on
/// the slice rather than a result.
pub(super) const SLICE_SWAP: &str = "slice::swap";

/// The prefix of the `core_method` of each `Vec` method, `Vec::push`.
pub(super) const VEC: &str = "Vec::";

/// The Click library file that states the core methods it models as
/// generic `extern fn` blocks over their type parameters.
const CORE_LIBRARY: &str = include_str!("../../../library/rust/core.click");

/// The core methods the Click library states as generic functions: the path
/// of each library generic function and its file. A core method whose
/// importer name is one of these paths with type arguments is an instance of
/// that function, written out at the types its name carries, `Vec::push<u32>`
/// of `Vec::push<T>`.
const LIBRARY_FUNCTIONS: &[(&[&str], &str)] = &[
    (&["Vec", "new"], CORE_LIBRARY),
    (&["Vec", "with_capacity"], CORE_LIBRARY),
    (&["Vec", "push"], CORE_LIBRARY),
    (&["Vec", "len"], CORE_LIBRARY),
    (&["Vec", "index"], CORE_LIBRARY),
    (&["slice", "swap"], CORE_LIBRARY),
    (&["Option", "unwrap"], CORE_LIBRARY),
    (&["Option", "expect"], CORE_LIBRARY),
    (&["Option", "unwrap_or"], CORE_LIBRARY),
    (&["Result", "unwrap"], CORE_LIBRARY),
    (&["Result", "expect"], CORE_LIBRARY),
    (&["Result", "unwrap_or"], CORE_LIBRARY),
    (&["slice", "as_ptr"], CORE_LIBRARY),
    (&["slice", "len"], CORE_LIBRARY),
    (&["SliceIter", "iter"], CORE_LIBRARY),
    (&["SliceIter", "next"], CORE_LIBRARY),
    (&["ChunksExact", "new"], CORE_LIBRARY),
    (&["ChunksExact", "next"], CORE_LIBRARY),
    (&["ChunksExact", "remainder"], CORE_LIBRARY),
    (&["ChunksExact", "remainder_ptr"], CORE_LIBRARY),
    (&["ChunksExact", "remainder_len"], CORE_LIBRARY),
    (&["ChunksExact", "len"], CORE_LIBRARY),
    (&["ChunksExact", "item_ptr"], CORE_LIBRARY),
    (&["ChunksExact", "item_len"], CORE_LIBRARY),
    (&["ChunksExact", "after_next"], CORE_LIBRARY),
];

/// The Click library file that states the integer core methods, one
/// single-line `extern fn` per method and type, `u32::min`.
const INTEGER_LIBRARY: &str = include_str!("../../../library/rust/integers.click");

/// The integer types whose core methods [`INTEGER_LIBRARY`] states.
const INTEGER_TYPES: &[&str] = &[
    "i8", "i16", "i32", "i64", "isize", "u8", "u16", "u32", "u64", "usize",
];

/// The integer core methods [`INTEGER_LIBRARY`] states at each type of
/// [`INTEGER_TYPES`], `unsigned_abs` at the signed types only.
const INTEGER_METHODS: &[&str] = &[
    "min",
    "max",
    "wrapping_add",
    "wrapping_sub",
    "wrapping_mul",
    "saturating_add",
    "saturating_sub",
    "checked_add",
    "checked_sub",
    "abs_diff",
    "unsigned_abs",
];

/// The library contract of the integer core method whose importer name is
/// `name`, `u32::min`: its `extern fn` line in [`INTEGER_LIBRARY`]. Only
/// the methods an import calls are appended, since a contract at a type
/// the import never names, `Option<i8>`, would not resolve.
fn integer_contract(name: &str) -> Option<&'static str> {
    let (ty, method) = INTEGER_TYPES.iter().find_map(|ty| {
        INTEGER_METHODS
            .iter()
            .find(|method| super::names::qualified_name([*ty, **method]) == name)
            .map(|method| (*ty, *method))
    })?;
    let head = format!("extern fn {ty}::{method}(");
    INTEGER_LIBRARY.lines().find(|line| line.starts_with(&head))
}

/// The library generic function the core method `function` is an instance
/// of, by importer name, with the library file stating it.
fn library_function(function: &super::schema::Function) -> Option<(String, &'static str)> {
    function.core_method.as_ref()?;
    let (generic, arguments) = super::names::split_type_arguments(&function.name);
    if arguments.is_empty() {
        return None;
    }
    LIBRARY_FUNCTIONS
        .iter()
        .find(|(path, _)| super::names::path_name(path) == generic)
        .map(|(_, library)| (generic, *library))
}

/// The library generic function a core method is an instance of, by
/// importer name ([`library_function`]).
pub(super) fn library_generic(function: &super::schema::Function) -> Option<String> {
    library_function(function).map(|(generic, _)| generic)
}

/// Whether `generic`, a function's importer name, is a Click library
/// generic function: no import has it, only the instances its calls name,
/// so its block is dropped once they are written out.
pub(crate) fn is_library_generic(generic: &str) -> bool {
    LIBRARY_FUNCTIONS
        .iter()
        .any(|(path, _)| super::names::path_name(path) == generic)
}

/// The `core_method` of `Result::unwrap` and `Result::expect`, which Rust
/// panics on at `Err`.
pub(super) const RESULT_UNWRAP: &str = "result::unwrap";

/// The `core_method` of `Result::unwrap_or`.
pub(super) const RESULT_UNWRAP_OR: &str = "click::result::unwrap_or";

/// The `core_method` of `Option::unwrap` and `Option::expect`, which Rust
/// panics on at `None`.
pub(super) const OPTION_UNWRAP: &str = "option::unwrap";

/// The prefix of the `core_method` of each `ChunksExact` operation the
/// library-iterator model calls, `ChunksExact::new`.
pub(super) const CHUNKS_EXACT: &str = "ChunksExact::";

/// The name of the external function for the `ChunksExact` operation
/// `operation` over bytes.
pub(super) fn chunks_exact_function(operation: &str) -> String {
    let mut name = super::names::qualified_name(["ChunksExact", operation]);
    super::names::push_type_argument(&mut name, "u8");
    name
}

/// Declares the external functions a `chunks_exact` iterator's operations
/// call, when the export has one: an iterator is a value of its Click
/// library type, read through that library's contract.
pub(super) fn declare_iterator_operations(export: &mut RustExport) {
    use super::schema::{Function, Place, Span};
    if export.library_iterators {
        declare_slice_iter_operations(export);
    }
    let has_chunks = export.functions.iter().any(|function| {
        function.mir.as_ref().is_some_and(|mir| {
            mir.locals
                .iter()
                .any(|local| local.value_type == Type::ChunkIterator)
        })
    });
    if !has_chunks {
        return;
    }
    if export.library_iterators {
        declare_library_chunk_operations(export);
        return;
    }
    let bytes = || Type::ByteSlice { mutable: false };
    let byte_pointer = || Type::Reference {
        mutable: false,
        pointee: Box::new(Type::U8),
    };
    let iterator = || ("it", Type::ChunkIterator);
    let operations: [(&str, Vec<(&str, Type)>, Type); 7] = [
        (
            "new",
            vec![("s", bytes()), ("n", Type::Usize)],
            Type::ChunkIterator,
        ),
        ("remainder_ptr", vec![iterator()], byte_pointer()),
        ("remainder_len", vec![iterator()], Type::Usize),
        ("len", vec![iterator()], Type::Usize),
        ("item_ptr", vec![iterator()], byte_pointer()),
        ("item_len", vec![iterator()], Type::Usize),
        ("after_next", vec![iterator()], Type::ChunkIterator),
    ];
    for (operation, parameters, return_type) in operations {
        export.functions.push(Function {
            name: chunks_exact_function(operation),
            return_type,
            parameters: parameters
                .into_iter()
                .map(|(name, value_type)| Place {
                    name: name.into(),
                    value_type,
                    span: Span { line: 1, column: 1 },
                })
                .collect(),
            body: vec![],
            mir: None,
            external: true,
            captures: 0,
            implements: None,
            instance_of: None,
            core_method: Some(format!("{CHUNKS_EXACT}{operation}")),
            span: Span { line: 1, column: 1 },
        });
    }
}

/// The importer's name for the library's `Slice<u8>`, Rust's `&[u8]` as one
/// value: the chunk `ChunksExact::next` returns and its `remainder()`.
pub(super) fn byte_slice_value_name() -> String {
    let mut name = "Slice".to_string();
    super::names::push_type_argument(&mut name, "u8");
    name
}

/// The importer's name for Rust `Option<&[u8]>`, which
/// `ChunksExact::next` returns.
pub(super) fn option_byte_slice_name() -> String {
    super::names::option_type_name("&[u8]")
}

/// Declares a `chunks_exact` iterator's operations as Rust has them:
/// `ChunksExact::new`, which `<[T]>::chunks_exact` calls, `Iterator::next`,
/// which takes the iterator by `&mut` and returns an `Option<&[u8]>`, and
/// `ChunksExact::remainder`, which returns a `&[u8]`. A returned slice is
/// one value of the library's `Slice<u8>`.
fn declare_library_chunk_operations(export: &mut RustExport) {
    use super::schema::{Enum, Function, Place, Span, Variant};
    let slice_value = byte_slice_value_name();
    let option = option_byte_slice_name();
    let slice_type = || Type::Enum {
        name: slice_value.clone(),
    };
    if !export
        .enums
        .iter()
        .any(|declared| declared.name == slice_value)
    {
        export.enums.push(Enum {
            name: slice_value.clone(),
            generic: Some("Slice".into()),
            arguments: vec![Type::U8],
            variants: vec![Variant {
                name: "Slice".into(),
                field_names: Vec::new(),
                fields: vec![
                    Type::Reference {
                        mutable: false,
                        pointee: Box::new(Type::U8),
                    },
                    Type::Usize,
                ],
            }],
        });
    }
    if !export.enums.iter().any(|declared| declared.name == option) {
        export.enums.push(Enum {
            name: option.clone(),
            generic: Some("Option".into()),
            arguments: vec![slice_type()],
            variants: vec![
                Variant {
                    name: "None".into(),
                    field_names: Vec::new(),
                    fields: Vec::new(),
                },
                Variant {
                    name: "Some".into(),
                    field_names: Vec::new(),
                    fields: vec![slice_type()],
                },
            ],
        });
    }
    let reference = |mutable| Type::Reference {
        mutable,
        pointee: Box::new(Type::ChunkIterator),
    };
    let operations: [(&str, Vec<(&str, Type)>, Type); 5] = [
        (
            "new",
            vec![
                ("s", Type::ByteSlice { mutable: false }),
                ("n", Type::Usize),
            ],
            Type::ChunkIterator,
        ),
        (
            "next",
            vec![("it", reference(true))],
            Type::Enum {
                name: option.clone(),
            },
        ),
        ("remainder", vec![("it", reference(false))], slice_type()),
        // A returned slice is read as the body reads a slice, its data and
        // its length, through Rust's own `<[T]>::as_ptr` and `<[T]>::len`.
        (
            "as_ptr",
            vec![("s", slice_type())],
            Type::Reference {
                mutable: false,
                pointee: Box::new(Type::U8),
            },
        ),
        ("len", vec![("s", slice_type())], Type::Usize),
    ];
    for (operation, parameters, return_type) in operations {
        let (name, core_method) = match operation {
            "as_ptr" | "len" => (
                byte_slice_function(operation),
                format!("{SLICE_VALUE}{operation}"),
            ),
            _ => (
                chunks_exact_function(operation),
                format!("{CHUNKS_EXACT}{operation}"),
            ),
        };
        export.functions.push(Function {
            name,
            return_type,
            parameters: parameters
                .into_iter()
                .map(|(name, value_type)| Place {
                    name: name.into(),
                    value_type,
                    span: Span { line: 1, column: 1 },
                })
                .collect(),
            body: vec![],
            mir: None,
            external: true,
            captures: 0,
            implements: None,
            instance_of: None,
            core_method: Some(core_method),
            span: Span { line: 1, column: 1 },
        });
    }
}

/// The prefix of the `core_method` of a method of Rust's `[u8]` read from a
/// slice value: `Slice::as_ptr`, `Slice::len`.
pub(super) const SLICE_VALUE: &str = "Slice::";

/// The name of the external function for the `[u8]` method `operation`
/// over a slice value.
pub(super) fn byte_slice_function(operation: &str) -> String {
    let mut name = super::names::qualified_name(["slice", operation]);
    super::names::push_type_argument(&mut name, "u8");
    name
}

/// The prefix of the `core_method` of each slice iterator operation the
/// library-iterator model calls, `SliceIter::new`.
pub(super) const SLICE_ITER: &str = "SliceIter::";

/// The name of the external function for the slice iterator operation
/// `operation` over elements spelled `element`: `SliceIter::next::<u8>`.
pub(super) fn slice_iter_function(operation: &str, element: &str) -> String {
    let mut name = super::names::qualified_name(["SliceIter", operation]);
    super::names::push_type_argument(&mut name, element);
    name
}

/// The importer's name for Rust `Option<&element>`, the library's
/// `spec enum Option<T>` at a reference to `element`: the value a slice
/// iterator's `next()` returns.
pub(super) fn option_reference_name(element: &str) -> String {
    super::names::option_type_name(&format!("&{element}"))
}

/// Declares a slice iterator's operations as Rust has them, once for each
/// element type the export iterates over: `<[T]>::iter`, which builds the
/// iterator, and `Iterator::next`, which takes it by `&mut` and returns an
/// `Option<&T>`. Each is a call whose contract is stated over the library's
/// `SliceIter`, as `Vec`'s methods are over `Vec`. The `Option<&T>` is
/// declared as an instance of the library's `Option`.
fn declare_slice_iter_operations(export: &mut RustExport) {
    use super::schema::{Enum, Function, Place, Span, Variant};
    let mut elements: Vec<Type> = Vec::new();
    for function in &export.functions {
        for local in function.mir.iter().flat_map(|mir| &mir.locals) {
            if let Type::SharedArrayIterator { element } = &local.value_type
                && !elements.contains(element)
            {
                elements.push(element.as_ref().clone());
            }
        }
    }
    for element in elements {
        let Some(spelling) = element.scalar_name() else {
            continue;
        };
        let reference = Type::Reference {
            mutable: false,
            pointee: Box::new(element.clone()),
        };
        let option = option_reference_name(spelling);
        if !export.enums.iter().any(|declared| declared.name == option) {
            export.enums.push(Enum {
                name: option.clone(),
                generic: Some("Option".into()),
                arguments: vec![reference.clone()],
                variants: vec![
                    Variant {
                        name: "None".into(),
                        field_names: Vec::new(),
                        fields: Vec::new(),
                    },
                    Variant {
                        name: "Some".into(),
                        field_names: Vec::new(),
                        fields: vec![reference.clone()],
                    },
                ],
            });
        }
        let iterator = || Type::SharedArrayIterator {
            element: Box::new(element.clone()),
        };
        let operations: [(&str, Vec<(&str, Type)>, Type); 2] = [
            (
                "iter",
                vec![("p", reference.clone()), ("n", Type::Usize)],
                iterator(),
            ),
            (
                "next",
                vec![(
                    "it",
                    Type::Reference {
                        mutable: true,
                        pointee: Box::new(iterator()),
                    },
                )],
                Type::Enum {
                    name: option.clone(),
                },
            ),
        ];
        for (operation, parameters, return_type) in operations {
            export.functions.push(Function {
                name: slice_iter_function(operation, spelling),
                return_type,
                parameters: parameters
                    .into_iter()
                    .map(|(name, value_type)| Place {
                        name: name.into(),
                        value_type,
                        span: Span { line: 1, column: 1 },
                    })
                    .collect(),
                body: vec![],
                mir: None,
                external: true,
                captures: 0,
                implements: None,
                instance_of: None,
                core_method: Some(format!("{SLICE_ITER}{operation}")),
                span: Span { line: 1, column: 1 },
            });
        }
    }
}

/// The `extern fn` contracts of the core methods `export` calls, with the
/// name of each function they declare: the Click library files stating the
/// library's generic functions an import's core methods are instances of,
/// and the library line of each integer method an import calls.
pub(super) fn contracts(export: &RustExport) -> (String, BTreeSet<String>) {
    let mut source = String::new();
    let mut models = BTreeSet::new();
    let mut libraries = Vec::new();
    for function in &export.functions {
        let Some(specification) = &function.core_method else {
            continue;
        };
        // A library function's instance is written out from its file.
        if let Some((_, library)) = library_function(function) {
            models.insert(function.name.clone());
            if !libraries.contains(&library) {
                libraries.push(library);
            }
            continue;
        }
        // An integer method's contract is its line of the library's.
        let contract = integer_contract(&function.name)
            .unwrap_or_else(|| panic!("core method `{specification}` has no library contract"));
        source.push('\n');
        source.push_str(contract);
        source.push('\n');
        models.insert(function.name.clone());
    }
    source.push_str(&libraries.concat());
    (source, models)
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

    /// Each integer method the name table maps has exactly one one-line
    /// contract in the library file, and the file states no other.
    #[test]
    fn every_integer_method_has_one_library_line() {
        let mut expected = BTreeSet::new();
        for (ty, signed, _) in MODULES {
            for method in INTEGER_METHODS {
                if *method == "unsigned_abs" && !signed {
                    continue;
                }
                let name = super::super::names::qualified_name([*ty, *method]);
                let line = integer_contract(&name).unwrap_or_else(|| panic!("{ty}::{method}"));
                assert!(line.ends_with(" }"), "{line}");
                assert!(
                    line.contains(&format!("ensures result == click::rust::{ty}::{method}(")),
                    "{line}"
                );
                expected.insert(line);
            }
        }
        let declared = INTEGER_LIBRARY
            .lines()
            .filter(|line| line.starts_with("extern "))
            .collect::<BTreeSet<_>>();
        assert_eq!(declared, expected);
    }

    #[test]
    fn a_core_method_contract_is_its_library_line() {
        let span = Span { line: 1, column: 1 };
        let place = |name: &str| Place {
            name: name.into(),
            value_type: Type::U32,
            span: span.clone(),
        };
        let export = RustExport {
            library_iterators: false,
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
        let (source, models) = contracts(&export);
        assert_eq!(
            source,
            "\nextern fn u32::checked_add(a: u32, b: u32) -> Option<u32> { \
             ensures result == click::rust::u32::checked_add(a, b); }\n"
        );
        assert_eq!(
            models,
            BTreeSet::from(["__rust_q_I3_u32_I11_checked_add".to_string()])
        );
    }
}
