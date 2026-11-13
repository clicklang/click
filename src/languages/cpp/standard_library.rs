//! The axiomatic C++ standard-library boundary: model accessors that name a
//! standard type's abstract state, and the contracts Click supplies for the
//! standard functions a program calls.
//!
//! A proof states a standard-library type's state through model accessors,
//! such as `std_span_data(s)` and `std_span_size(s)`, never through a
//! library's private fields. Each accessor is a spelling for one field path,
//! and the binding below for the library that was parsed is the only place
//! that names those fields. The parser rewrites an accessor application into
//! its field path, so the result is checked like any written field access.

use std::collections::{BTreeMap, BTreeSet};

use crate::languages::c::syntax::C0StructLayout;

/// One model accessor bound to a field path in one library's record.
struct AccessorBinding {
    /// The prefix of the record's name, which names its template.
    record_prefix: &'static str,
    accessor: &'static str,
    path: &'static [&'static str],
}

/// libstdc++: `std::span<T>` holds `_M_ptr` and an extent storage whose
/// dynamic value is `_M_extent_value`. libc++: a dynamic-extent
/// `std::span<T>` holds `__data_` and `__size_`.
const BINDINGS: &[AccessorBinding] = &[
    AccessorBinding {
        record_prefix: "span__",
        accessor: "std_span_data",
        path: &["_M_ptr"],
    },
    AccessorBinding {
        record_prefix: "span__",
        accessor: "std_span_size",
        path: &["_M_extent", "_M_extent_value"],
    },
    AccessorBinding {
        record_prefix: "span__",
        accessor: "std_span_data",
        path: &["__data_"],
    },
    AccessorBinding {
        record_prefix: "span__",
        accessor: "std_span_size",
        path: &["__size_"],
    },
    // `std::array<T, N>` holds its elements in `T _M_elems[N]` (libstdc++)
    // or `T __elems_[N]` (libc++).
    AccessorBinding {
        record_prefix: "array__",
        accessor: "std_array_data",
        path: &["_M_elems"],
    },
    AccessorBinding {
        record_prefix: "array__",
        accessor: "std_array_data",
        path: &["__elems_"],
    },
];

/// The model accessors the parsed records support, each with its field path.
/// An accessor is available when some record of its template has a bound
/// path; a library whose layout matches no binding binds none, and records
/// that match more than one binding of an accessor bind it to neither, so an
/// accessor is never misbound.
pub(crate) fn model_accessors(
    layouts: &BTreeMap<String, C0StructLayout>,
) -> BTreeMap<&'static str, &'static [&'static str]> {
    let mut accessors = BTreeMap::new();
    let mut ambiguous = Vec::new();
    for binding in BINDINGS {
        let bound = layouts.iter().any(|(name, layout)| {
            name.starts_with(binding.record_prefix) && has_path(layouts, layout, binding.path)
        });
        if bound && accessors.insert(binding.accessor, binding.path).is_some() {
            ambiguous.push(binding.accessor);
        }
    }
    for accessor in ambiguous {
        accessors.remove(accessor);
    }
    accessors
}

fn has_path(
    layouts: &BTreeMap<String, C0StructLayout>,
    layout: &C0StructLayout,
    path: &[&str],
) -> bool {
    let Some((first, rest)) = path.split_first() else {
        return true;
    };
    let Some(field) = layout.field(first) else {
        return false;
    };
    if rest.is_empty() {
        return true;
    }
    field
        .struct_name()
        .and_then(|name| layouts.get(name))
        .is_some_and(|inner| has_path(layouts, inner, rest))
}

/// An element type the library's class templates are written out at.
struct SpanElement {
    /// The element as Clang spells it in a qualified name.
    name: &'static str,
    /// The element as Clang spells it in a canonical signature.
    signature: &'static str,
    /// `sizeof` the element.
    bytes: u64,
}

const SPAN_ELEMENTS: &[SpanElement] = &[
    SpanElement {
        name: "int",
        signature: "int",
        bytes: 4,
    },
    SpanElement {
        name: "unsigned int",
        signature: "unsigned int",
        bytes: 4,
    },
    SpanElement {
        name: "unsigned char",
        signature: "unsigned char",
        bytes: 1,
    },
    SpanElement {
        name: "std::byte",
        signature: "enum std::byte",
        bytes: 1,
    },
    SpanElement {
        name: "const int",
        signature: "const int",
        bytes: 4,
    },
    SpanElement {
        name: "const unsigned int",
        signature: "const unsigned int",
        bytes: 4,
    },
    SpanElement {
        name: "const unsigned char",
        signature: "const unsigned char",
        bytes: 1,
    },
    SpanElement {
        name: "const std::byte",
        signature: "const enum std::byte",
        bytes: 1,
    },
];

/// The Click library file that states the `std::span<T>` and
/// `std::span<T, N>` contracts, as template methods a sidecar writes.
pub(crate) const SPAN_LIBRARY: &str = include_str!("../../../library/cpp/span.click");

/// The Click library file that states the `std::array<T, N>` contracts.
pub(crate) const ARRAY_LIBRARY: &str = include_str!("../../../library/cpp/array.click");

/// The Click library file that states `std::as_writable_bytes`, a function
/// template written `std::as_writable_bytes<T, N>` by its element and
/// extent.
pub(crate) const AS_WRITABLE_BYTES_LIBRARY: &str =
    include_str!("../../../library/cpp/as_writable_bytes.click");

/// The standard function templates outside a class that the Click library
/// states: each instance's qualified name and canonical signature as Clang
/// spells them, the library template's path, and its file. An axiom
/// matching one is an instance of that template, written out at the
/// template arguments its own path names.
const LIBRARY_FUNCTIONS: &[(&str, &str, &[&str], &str)] = &[(
    "std::as_writable_bytes",
    "class std::span<enum std::byte> (class std::span<int>) noexcept",
    &["std", "as_writable_bytes<T, N>"],
    AS_WRITABLE_BYTES_LIBRARY,
)];

/// The methods of `std::span<T>` and `std::span<T, N>` that
/// [`SPAN_LIBRARY`] states, each with its canonical signature as Clang
/// spells it, `{T}` the element there: both extents' signatures are the
/// same, since a static extent's subviews by a runtime count are dynamic.
/// An axiom matching one is an instance of the library's method
/// `std::span<T>::name` or `std::span<T, N>::name`, written out at its
/// element and extent.
const SPAN_METHODS: &[(&str, &str)] = &[
    ("size", "unsigned long (void) const noexcept"),
    ("size_bytes", "unsigned long (void) const noexcept"),
    ("data", "{T} *(void) const noexcept"),
    ("front", "{T} &(void) const noexcept"),
    ("back", "{T} &(void) const noexcept"),
    ("operator[]", "{T} &(unsigned long) const noexcept"),
    (
        "first",
        "class std::span<{T}> (unsigned long) const noexcept",
    ),
    (
        "last",
        "class std::span<{T}> (unsigned long) const noexcept",
    ),
    (
        "subspan",
        "class std::span<{T}> (unsigned long, unsigned long) const noexcept",
    ),
];

/// The methods of `std::array<T, N>` that [`ARRAY_LIBRARY`] states. Its
/// element accessors are each a mutable and a `const` overload, which the
/// library writes as two template methods at one path.
const ARRAY_METHODS: &[(&str, &str)] = &[
    ("size", "unsigned long (void) const noexcept"),
    ("data", "{T} *(void) noexcept"),
    ("data", "const {T} *(void) const noexcept"),
    ("operator[]", "{T} &(unsigned long) noexcept"),
    ("operator[]", "const {T} &(unsigned long) const noexcept"),
    ("front", "{T} &(void) noexcept"),
    ("front", "const {T} &(void) const noexcept"),
    ("back", "{T} &(void) noexcept"),
    ("back", "const {T} &(void) const noexcept"),
];

/// A class template the Click library states: its name in the importer's
/// qualified names, its library template with a dynamic and a static
/// extent (`None` where it has no such form), its methods and its file.
struct LibraryClass {
    class: &'static str,
    dynamic: Option<&'static str>,
    fixed: Option<&'static str>,
    methods: &'static [(&'static str, &'static str)],
    /// Whether a `const` element is one the library states: an array's
    /// elements are its own objects, which a `const` element type makes
    /// immutable, and the library states only mutable ones.
    const_elements: bool,
    library: &'static str,
}

const LIBRARY_CLASSES: &[LibraryClass] = &[
    LibraryClass {
        class: "span",
        dynamic: Some("span<T>"),
        fixed: Some("span<T, N>"),
        methods: SPAN_METHODS,
        const_elements: true,
        library: SPAN_LIBRARY,
    },
    LibraryClass {
        class: "array",
        dynamic: None,
        fixed: Some("array<T, N>"),
        methods: ARRAY_METHODS,
        const_elements: false,
        library: ARRAY_LIBRARY,
    },
];

/// The library method an axiom is an instance of, by importer name, with
/// the library file stating it, when the Click library states it for the
/// axiom's template arguments: for `std::span<unsigned int>::size`,
/// `std::span<T>::size`, and for `std::array<int, 4>::data`,
/// `std::array<T, N>::data`, whichever overload the signature is. An
/// element outside [`SPAN_ELEMENTS`], a signature the library does not
/// state, an extent the class does not take, `std::dynamic_extent` as a
/// static extent, or one whose byte size does not fit a `uint64`, is no
/// instance, so a call is refused by name.
fn library_method(axiom: &super::schema::CppAxiom) -> Option<(String, &'static str)> {
    if let Some((_, _, path, library)) =
        LIBRARY_FUNCTIONS
            .iter()
            .find(|(qualified_name, signature, _, _)| {
                *qualified_name == axiom.qualified_name && *signature == axiom.signature
            })
    {
        return Some((super::names::path_name(path), library));
    }
    let (class, rest) = axiom
        .qualified_name
        .strip_prefix("std::")?
        .split_once('<')?;
    let class = LIBRARY_CLASSES
        .iter()
        .find(|candidate| candidate.class == class)?;
    let (arguments, method) = rest.rsplit_once(">::")?;
    let (element, extent) = match arguments.rsplit_once(", ") {
        Some((element, extent)) => (element, Some(extent.parse::<u64>().ok()?)),
        None => (arguments, None),
    };
    if !class.const_elements && element.starts_with("const ") {
        return None;
    }
    let element = SPAN_ELEMENTS
        .iter()
        .find(|candidate| candidate.name == element)?;
    if let Some(extent) = extent
        && (extent == u64::MAX || extent.checked_mul(element.bytes).is_none())
    {
        return None;
    }
    let template = if extent.is_some() {
        class.fixed
    } else {
        class.dynamic
    }?;
    class
        .methods
        .iter()
        .find(|(name, signature)| {
            *name == method && signature.replace("{T}", element.signature) == axiom.signature
        })
        .map(|(name, _)| {
            (
                super::names::path_name(&["std", template, name]),
                class.library,
            )
        })
}

/// The library method an axiom is an instance of, by importer name
/// ([`library_method`]).
pub(super) fn library_generic(axiom: &super::schema::CppAxiom) -> Option<String> {
    library_method(axiom).map(|(generic, _)| generic)
}

/// Whether `generic`, a method's importer name, is a Click library
/// template's method: such a template has no generic method in the import,
/// only the instances its axioms are.
pub(crate) fn is_library_generic(generic: &str) -> bool {
    LIBRARY_FUNCTIONS
        .iter()
        .any(|(_, _, path, _)| super::names::path_name(path) == generic)
        || LIBRARY_CLASSES.iter().any(|class| {
            [class.dynamic, class.fixed]
                .into_iter()
                .flatten()
                .any(|template| {
                    class.methods.iter().any(|(name, _)| {
                        super::names::path_name(&["std", template, name]) == generic
                    })
                })
        })
}

/// The Click library files stating the axioms an import reaches: the
/// library's templates, whose instances the axioms are. An axiom that is
/// none gets no contract, so a caller is refused unless the sidecar states
/// one itself. Returns the text and the name of each function it states.
pub(super) fn contracts(
    export: &super::CppExport,
    names: &super::names::ResolvedNames,
) -> Result<(String, BTreeSet<String>), String> {
    let mut models = BTreeSet::new();
    let mut libraries = Vec::new();
    for function in &export.reachable_functions {
        let Some((_, library)) = function.axiom.as_ref().and_then(library_method) else {
            continue;
        };
        models.insert(names.require(&function.declaration_id)?.to_string());
        if !libraries.contains(&library) {
            libraries.push(library);
        }
    }
    Ok((libraries.concat(), models))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::languages::c::syntax::{C0Type, LongRank};

    fn record(fields: &[(&str, C0Type, Option<&str>, u32, u32)]) -> C0StructLayout {
        C0StructLayout::from_explicit_fields_with_structs(
            fields
                .iter()
                .map(|(name, kind, nested, offset, width)| {
                    (
                        name.to_string(),
                        *kind,
                        nested.map(str::to_string),
                        *offset,
                        *width,
                    )
                })
                .collect(),
            16,
            8,
            &BTreeMap::from([(
                "__extent_storage".to_string(),
                C0StructLayout::from_explicit_fields(
                    vec![(
                        "_M_extent_value".to_string(),
                        C0Type::UInt64(LongRank::Long),
                        0,
                        8,
                    )],
                    8,
                    8,
                )
                .unwrap(),
            )]),
        )
        .unwrap()
    }

    fn accessors(span: C0StructLayout) -> BTreeMap<&'static str, &'static [&'static str]> {
        let mut layouts = BTreeMap::from([("span__unsigned_char".to_string(), span)]);
        layouts.insert(
            "__extent_storage".to_string(),
            C0StructLayout::from_explicit_fields(
                vec![(
                    "_M_extent_value".to_string(),
                    C0Type::UInt64(LongRank::Long),
                    0,
                    8,
                )],
                8,
                8,
            )
            .unwrap(),
        );
        model_accessors(&layouts)
    }

    #[test]
    fn libstdcxx_and_libcxx_span_layouts_bind_the_same_accessors() {
        let libstdcxx = accessors(record(&[
            ("_M_ptr", C0Type::UInt8Pointer, None, 0, 8),
            ("_M_extent", C0Type::Int32, Some("__extent_storage"), 8, 8),
        ]));
        assert_eq!(libstdcxx["std_span_data"], &["_M_ptr"]);
        assert_eq!(
            libstdcxx["std_span_size"],
            &["_M_extent", "_M_extent_value"]
        );
        let libcxx = accessors(record(&[
            ("__data_", C0Type::UInt8Pointer, None, 0, 8),
            ("__size_", C0Type::UInt64(LongRank::Long), None, 8, 8),
        ]));
        assert_eq!(libcxx["std_span_data"], &["__data_"]);
        assert_eq!(libcxx["std_span_size"], &["__size_"]);
    }

    #[test]
    fn an_unknown_or_ambiguous_span_layout_binds_no_accessor() {
        let unknown = accessors(record(&[
            ("pointer", C0Type::UInt8Pointer, None, 0, 8),
            ("length", C0Type::UInt64(LongRank::Long), None, 8, 8),
        ]));
        assert!(unknown.is_empty(), "{unknown:?}");
        let ambiguous = accessors(record(&[
            ("_M_ptr", C0Type::UInt8Pointer, None, 0, 8),
            ("__data_", C0Type::UInt8Pointer, None, 8, 8),
        ]));
        assert!(!ambiguous.contains_key("std_span_data"), "{ambiguous:?}");
    }

    #[test]
    fn span_methods_are_library_instances_over_supported_elements_only() {
        let axiom = |qualified_name: &str, signature: &str| super::super::schema::CppAxiom {
            qualified_name: qualified_name.into(),
            signature: signature.into(),
        };
        let generic = library_generic(&axiom(
            "std::span<std::byte>::size_bytes",
            "unsigned long (void) const noexcept",
        ))
        .unwrap();
        assert!(is_library_generic(&generic));
        assert_eq!(
            crate::languages::cpp::names::cpp_display_name(&generic).unwrap(),
            "std::span<T>::size_bytes"
        );
        assert!(
            library_generic(&axiom(
                "std::span<unsigned int>::data",
                "unsigned int *(void) const noexcept"
            ))
            .is_some()
        );
        // The signature must spell the same element as the name.
        assert!(
            library_generic(&axiom(
                "std::span<unsigned int>::data",
                "int *(void) const noexcept"
            ))
            .is_none()
        );
        // An element the library cannot state has none.
        assert!(
            library_generic(&axiom(
                "std::span<long>::size",
                "unsigned long (void) const noexcept"
            ))
            .is_none()
        );
        // A static extent is an instance of `std::span<T, N>`, unless it is
        // `std::dynamic_extent` or its byte size does not fit.
        let size = |extent: &str| {
            library_generic(&axiom(
                &format!("std::span<int, {extent}>::size"),
                "unsigned long (void) const noexcept",
            ))
        };
        assert_eq!(
            crate::languages::cpp::names::cpp_display_name(&size("4").unwrap()).unwrap(),
            "std::span<T, N>::size"
        );
        assert!(is_library_generic(&size("4").unwrap()));
        assert!(size("18446744073709551615").is_none());
        assert!(size("4611686018427387904").is_none());
    }

    // Both overloads of an array's element accessor are instances of the
    // library's method at its path; a `const` element, or an extent whose
    // byte size does not fit, is none.
    #[test]
    fn array_overloads_are_library_instances_over_mutable_elements_only() {
        let front = |element: &str, extent: &str, signature: &str| {
            library_generic(&super::super::schema::CppAxiom {
                qualified_name: format!("std::array<{element}, {extent}>::front"),
                signature: signature.into(),
            })
        };
        let mutable = front("int", "4", "int &(void) noexcept").unwrap();
        assert_eq!(
            front("int", "4", "const int &(void) const noexcept"),
            Some(mutable.clone())
        );
        assert_eq!(
            crate::languages::cpp::names::cpp_display_name(&mutable).unwrap(),
            "std::array<T, N>::front"
        );
        assert!(is_library_generic(&mutable));
        assert!(front("const int", "4", "const int &(void) noexcept").is_none());
        assert!(front("int", "4611686018427387904", "int &(void) noexcept").is_none());
    }

    // `std::as_writable_bytes` is an instance of the library's function
    // template at the one signature the name table states.
    #[test]
    fn as_writable_bytes_is_a_library_instance_at_its_one_signature() {
        let axiom = |signature: &str| super::super::schema::CppAxiom {
            qualified_name: "std::as_writable_bytes".into(),
            signature: signature.into(),
        };
        let generic = library_generic(&axiom(
            "class std::span<enum std::byte> (class std::span<int>) noexcept",
        ))
        .unwrap();
        assert!(is_library_generic(&generic));
        assert_eq!(
            crate::languages::cpp::names::cpp_display_name(&generic).unwrap(),
            "std::as_writable_bytes<T, N>"
        );
        assert!(
            library_generic(&axiom(
                "class std::span<enum std::byte> (class std::span<long>) noexcept"
            ))
            .is_none()
        );
    }
}
