//! The contracts Click supplies for the Rust core methods an import calls:
//! each states the method's result with the library's specification function
//! of the same path, `ensures result == click::rust::u32::min(a, b);`. They
//! are assumptions, as an `extern fn` contract is.
use super::schema::{RustExport, Type};
use std::collections::BTreeSet;

/// The `core_method` of `<[T]>::swap`, whose contract states its effect on
/// the slice rather than a result.
pub(super) const SLICE_SWAP: &str = "slice::swap";

/// `<[T]>::swap(s, a, b)`'s contract: it owns the slice, Rust panics unless
/// both indices are in bounds, and the two elements are exchanged while
/// every other element is unchanged.
fn slice_swap_contract(function: &super::schema::Function) -> String {
    let element = match &function.parameters[0].value_type {
        Type::ScalarSlice { element, .. } => element.scalar_name().expect("an integer element"),
        Type::ByteSlice { .. } => "u8",
        _ => unreachable!("checked by the importer"),
    };
    format!(
        "\nextern fn {}(s: &mut [{element}], a: usize, b: usize) {{\n    owns *s;\n    requires a < s.len();\n    requires b < s.len();\n    ensures s[a] == old(s[b]);\n    ensures s[b] == old(s[a]);\n    ensures forall (k: usize) {{ k < s.len() and k != a and k != b implies s[k] == old(s[k]) }};\n}}\n",
        function.name
    )
}

/// The prefix of the `core_method` of each `Vec` method, `Vec::push`.
pub(super) const VEC: &str = "Vec::";

/// The largest length a `Vec` reaches before `push` panics: a vector of
/// `u8` holds at most `isize::MAX` elements, and a longer element fewer.
/// The model bounds every vector by the length `vec::len` can state,
/// `u64::MAX`, and `push` requires room below it; the program's own bound
/// is the smaller, so a proof that meets this requirement is sound for it
/// only up to Rust's allocation limit, which aborts rather than returns.
const VEC_LENGTH_LIMIT: &str = "18446744073709551615u64";

/// The contract of the `Vec` method `function`, `Vec::push<u32>`: the
/// call's effect on the library's `Vec<T>` values.
fn vec_contract(function: &super::schema::Function, method: &str) -> String {
    let element_of = |ty: &Type| match ty {
        Type::Vec { element } => element.scalar_name(),
        Type::Reference { pointee, .. } => match pointee.as_ref() {
            Type::Vec { element } => element.scalar_name(),
            _ => None,
        },
        _ => None,
    };
    let element = element_of(&function.return_type)
        .or_else(|| {
            function
                .parameters
                .first()
                .and_then(|parameter| element_of(&parameter.value_type))
        })
        .expect("a `Vec` method names its element type");
    let name = &function.name;
    let vector = format!("Vec<{element}>");
    let body = match method {
        "new" => format!(
            "extern fn {name}() -> {vector} {{\n    ensures click::rust::vec::len(result) == 0u64;\n}}"
        ),
        // The capacity is outside the model: the vector is empty.
        "with_capacity" => format!(
            "extern fn {name}(capacity: usize) -> {vector} {{\n    ensures click::rust::vec::len(result) == 0u64;\n}}"
        ),
        // The new value, and what the library's axioms say of it, so a
        // caller reads the length and elements without citing them.
        "push" => format!(
            "extern fn {name}(v: &mut {vector}, x: {element}) {{\n    owns *v;\n    requires click::rust::vec::len(*v) < {VEC_LENGTH_LIMIT};\n    ensures *v == click::rust::vec::push(old(*v), x);\n    ensures click::rust::vec::len(*v) == click::rust::vec::len(old(*v)) + 1;\n    ensures click::rust::vec::get(*v, click::rust::vec::len(old(*v))) == x;\n    ensures forall (k: usize) {{ k < click::rust::vec::len(old(*v)) implies click::rust::vec::get(*v, k) == click::rust::vec::get(old(*v), k) }};\n}}"
        ),
        "len" => format!(
            "extern fn {name}(v: &{vector}) -> usize {{\n    views *v;\n    ensures result == click::rust::vec::len(old(*v));\n}}"
        ),
        // Rust panics unless the index is in bounds.
        "index" => format!(
            "extern fn {name}(v: &{vector}, i: usize) -> {element} {{\n    views *v;\n    requires i < click::rust::vec::len(*v);\n    ensures result == click::rust::vec::get(old(*v), i);\n}}"
        ),
        _ => unreachable!("checked by the importer"),
    };
    format!("\n{body}\n")
}

/// The `core_method` of `Result::unwrap` and `Result::expect`, which Rust
/// panics on at `Err`.
pub(super) const RESULT_UNWRAP: &str = "result::unwrap";

/// The `core_method` of `Result::unwrap_or`.
pub(super) const RESULT_UNWRAP_OR: &str = "click::result::unwrap_or";

/// The sidecar spelling of the `Result` instance `ty`, `Result<u32, u8>`.
fn result_spelling(ty: &Type) -> String {
    let Type::Enum { name } = ty else {
        unreachable!("a result is an enum")
    };
    let (_, arguments) = super::names::split_type_arguments(name);
    format!("Result<{}>", arguments.join(", "))
}

/// `Result::unwrap(r)`'s contract: Rust panics unless `r` is `Ok`, whose
/// payload is the result.
fn result_unwrap_contract(function: &super::schema::Function) -> String {
    let result = result_spelling(&function.parameters[0].value_type);
    let payload = function
        .return_type
        .scalar_name()
        .expect("a scalar payload");
    format!(
        "\nextern fn {}(r: {result}) -> {payload} {{\n    requires exists (value: {payload}) {{ r == {result}::Ok(value) }};\n    ensures r == {result}::Ok(result);\n}}\n",
        function.name,
    )
}

/// `Result::unwrap_or(r, d)`'s contract, the library's `result::unwrap_or`.
fn result_unwrap_or_contract(function: &super::schema::Function) -> String {
    let result = result_spelling(&function.parameters[0].value_type);
    let payload = function
        .return_type
        .scalar_name()
        .expect("a scalar payload");
    format!(
        "\nextern fn {}(r: {result}, d: {payload}) -> {payload} {{\n    ensures result == {RESULT_UNWRAP_OR}(r, d);\n}}\n",
        function.name,
    )
}

/// The `core_method` of `Option::unwrap` and `Option::expect`, which Rust
/// panics on at `None`.
pub(super) const OPTION_UNWRAP: &str = "option::unwrap";

/// `Option::unwrap(o)`'s contract: Rust panics unless `o` is `Some`, whose
/// payload is the result.
fn option_unwrap_contract(function: &super::schema::Function) -> String {
    let payload = function
        .return_type
        .scalar_name()
        .expect("a scalar payload");
    format!(
        "\nextern fn {}(o: Option<{payload}>) -> {payload} {{\n    requires o != Option<{payload}>::None;\n    ensures o == Option<{payload}>::Some(result);\n}}\n",
        function.name
    )
}

/// The `extern fn` contract of each core method `export` declares.
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

/// The contract of the `[u8]` method `operation` over a slice value.
fn byte_slice_contract(function: &super::schema::Function, operation: &str) -> Option<String> {
    const SLICE: &str = "click::rust::slice";
    let name = &function.name;
    let body = match operation {
        "as_ptr" => format!(
            "extern fn {name}(s: Slice<u8>) -> &u8 {{\n    ensures result == {SLICE}::as_ptr(s);\n}}"
        ),
        "len" => format!(
            "extern fn {name}(s: Slice<u8>) -> usize {{\n    ensures result == {SLICE}::len(s);\n}}"
        ),
        _ => return None,
    };
    Some(format!("\n{body}\n"))
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

/// The contract of the slice iterator operation `operation` at the element
/// type the function is declared at. `iter` builds the library value of the
/// slice; `next` is the next law over `old(*it)` and `*it`. Where the
/// remaining slice starts after one `next()` needs the element's size, so it
/// is stated here, at the type, and not as a generic axiom.
fn slice_iter_contract(function: &super::schema::Function, operation: &str) -> Option<String> {
    const LIBRARY: &str = "click::rust::slice_iter";
    let name = &function.name;
    let element = function
        .parameters
        .iter()
        .map(|parameter| &parameter.value_type)
        .chain(std::iter::once(&function.return_type))
        .find_map(|ty| match ty {
            Type::SharedArrayIterator { element } => element.scalar_name(),
            Type::Reference { pointee, .. } => match pointee.as_ref() {
                Type::SharedArrayIterator { element } => element.scalar_name(),
                _ => None,
            },
            _ => None,
        })?;
    let iterator = format!("SliceIter<{element}>");
    let option = format!("Option<&{element}>");
    const SLICE: &str = "click::rust::slice";
    let len = |it: &str| format!("{LIBRARY}::len({it})");
    let data = |it: &str| format!("{SLICE}::as_ptr({LIBRARY}::as_slice({it}))");
    let count = |it: &str| format!("{SLICE}::len({LIBRARY}::as_slice({it}))");
    let has = format!("0u64 < {}", len("old(*it)"));
    let empty = format!("{} == 0u64", len("old(*it)"));
    let body = match operation {
        "iter" => format!(
            "extern fn {name}(p: &{element}, n: usize) -> {iterator} {{\n    ensures result == {LIBRARY}::iter(Slice<{element}>::Slice(p, n));\n    ensures {} == p;\n    ensures {} == n;\n    ensures {} == n;\n}}",
            data("result"),
            count("result"),
            len("result"),
        ),
        "next" => format!(
            "extern fn {name}(it: &mut {iterator}) -> {option} {{\n    owns *it;\n    ensures {empty} implies result == {option}::None;\n    ensures {empty} implies *it == old(*it);\n    ensures {has} implies result == {option}::Some({old_data});\n    ensures {has} implies *it == {LIBRARY}::after_next(old(*it));\n    ensures {has} implies {new_data} == {old_data} + 1u64;\n    ensures {has} implies {new_count} == {old_count} - 1u64;\n    ensures {has} implies {new_len} == {old_len} - 1u64;\n}}",
            old_data = data("old(*it)"),
            new_data = data("*it"),
            old_count = count("old(*it)"),
            new_count = count("*it"),
            old_len = len("old(*it)"),
            new_len = len("*it"),
        ),
        _ => return None,
    };
    Some(format!("\n{body}\n"))
}

/// The contract of the `ChunksExact` operation `operation`: the call stated
/// with the library's `click::rust::chunks_exact`. A slice is still a
/// pointer and a length in the importer's model, so a chunk and the
/// remainder are each read as their data and their length.
fn chunks_exact_contract(function: &super::schema::Function, operation: &str) -> String {
    const LIBRARY: &str = "click::rust::chunks_exact";
    const SLICE: &str = "click::rust::slice";
    let name = &function.name;
    let iterator = "ChunksExact<u8>";
    let body = match operation {
        // Rust panics on a zero chunk size.
        "new" => format!(
            "extern fn {name}(s: &[u8], n: usize) -> {iterator} {{\n    requires n != 0u64;\n    ensures result == {LIBRARY}::chunks_exact(Slice<u8>::Slice(s, s.len()), n);\n}}"
        ),
        "remainder_ptr" => format!(
            "extern fn {name}(it: {iterator}) -> &u8 {{\n    ensures result == {SLICE}::as_ptr({LIBRARY}::remainder(it));\n}}"
        ),
        "remainder_len" => format!(
            "extern fn {name}(it: {iterator}) -> usize {{\n    ensures result == {SLICE}::len({LIBRARY}::remainder(it));\n}}"
        ),
        "len" => format!(
            "extern fn {name}(it: {iterator}) -> usize {{\n    ensures result == {LIBRARY}::len(it);\n}}"
        ),
        "item_ptr" => format!(
            "extern fn {name}(it: {iterator}) -> &u8 {{\n    requires 0u64 < {LIBRARY}::len(it);\n    ensures result == {SLICE}::as_ptr({LIBRARY}::nth(it, 0u64));\n}}"
        ),
        "item_len" => format!(
            "extern fn {name}(it: {iterator}) -> usize {{\n    requires 0u64 < {LIBRARY}::len(it);\n    ensures result == {SLICE}::len({LIBRARY}::nth(it, 0u64));\n}}"
        ),
        "after_next" => format!(
            "extern fn {name}(it: {iterator}) -> {iterator} {{\n    requires 0u64 < {LIBRARY}::len(it);\n    ensures result == {LIBRARY}::after_next(it);\n}}"
        ),
        // Rust's `Iterator::next` over the library value: the first chunk
        // still to come, and the iterator after it.
        "next" => {
            let option = "Option<&[u8]>";
            let len = format!("{LIBRARY}::len(old(*it))");
            format!(
                "extern fn {name}(it: &mut {iterator}) -> {option} {{\n    owns *it;\n    ensures {len} == 0u64 implies result == {option}::None;\n    ensures {len} == 0u64 implies *it == old(*it);\n    ensures 0u64 < {len} implies result == {option}::Some({LIBRARY}::nth(old(*it), 0u64));\n    ensures 0u64 < {len} implies *it == {LIBRARY}::after_next(old(*it));\n}}"
            )
        }
        "remainder" => format!(
            "extern fn {name}(it: &{iterator}) -> Slice<u8> {{\n    views *it;\n    ensures result == {LIBRARY}::remainder(old(*it));\n}}"
        ),
        _ => unreachable!("declared by `declare_iterator_operations`"),
    };
    format!("\n{body}\n")
}

/// The `extern fn` contracts of the core methods `export` calls, with the
/// name of each function they declare.
pub(super) fn contracts(export: &RustExport) -> (String, BTreeSet<String>) {
    let mut source = String::new();
    let mut models = BTreeSet::new();
    for function in &export.functions {
        let Some(specification) = &function.core_method else {
            continue;
        };
        if let Some(contract) = core_method_contract(function, specification) {
            source.push_str(&contract);
            models.insert(function.name.clone());
        }
    }
    (source, models)
}

/// The contract of the core method `function`, whose specification path
/// is `specification`, if Click states one.
fn core_method_contract(function: &super::schema::Function, specification: &str) -> Option<String> {
    if let Some(method) = specification.strip_prefix(VEC) {
        return Some(vec_contract(function, method));
    }
    if specification == SLICE_SWAP {
        return Some(slice_swap_contract(function));
    }
    if let Some(operation) = specification.strip_prefix(SLICE_VALUE) {
        return byte_slice_contract(function, operation);
    }
    if let Some(operation) = specification.strip_prefix(CHUNKS_EXACT) {
        return Some(chunks_exact_contract(function, operation));
    }
    if let Some(operation) = specification.strip_prefix(SLICE_ITER) {
        return slice_iter_contract(function, operation);
    }
    if specification == OPTION_UNWRAP {
        return Some(option_unwrap_contract(function));
    }
    if specification == RESULT_UNWRAP {
        return Some(result_unwrap_contract(function));
    }
    if specification == RESULT_UNWRAP_OR {
        return Some(result_unwrap_or_contract(function));
    }
    // An `Option` is of the type of the method's scalar parameter:
    // `checked_add`'s operands, `unwrap_or`'s default.
    let payload = function
        .parameters
        .iter()
        .find_map(|parameter| parameter.value_type.scalar_name())
        .expect("a core method takes a scalar");
    let spell = |ty: &Type| -> String {
        match ty.scalar_name() {
            Some(name) => name.into(),
            None => format!("Option<{payload}>"),
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
    Some(format!(
        "\nextern fn {}({parameters}) -> {} {{\n    ensures result == {specification}({arguments});\n}}\n",
        function.name,
        spell(&function.return_type),
    ))
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
        assert_eq!(
            contracts(&export).0,
            "\nextern fn __rust_q_I3_u32_I11_checked_add(a: u32, b: u32) -> Option<u32> {\n    \
             ensures result == click::rust::u32::checked_add(a, b);\n}\n"
        );
    }
}
