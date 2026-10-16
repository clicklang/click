//! The names the Rust importer gives items, and their Rust spelling.
//!
//! The importer names an item at a path `quad::walk` by `__rust_q` and each
//! segment with its length, `__rust_q_I4_quad_I4_walk`, and an inherent
//! method by its module, then `_T` and its type's own name, then the method:
//! `__rust_q_I6_adler2_T29___rust_q_I6_adler2_I7_Adler32_I3_new`
//! (`path_name`, `inherent_method_name`).
//! A sidecar writes the path, `adler2::Adler32::new`, and a diagnostic prints
//! it the same way. The encoding is self-delimiting, so decoding needs no
//! import.
//!
//! An operator-trait method is named by its type, the method, and the
//! trait's type argument (`rhs_name` in
//! `src/languages/rust/charon/assignment_operators.rs`):
//! `__rust_q_I6_adler2_I4_algo_I5_U32X4_mul_assign_u32`, and `Default` by its
//! type and `_default`. These print in Rust's qualified form,
//! `<adler2::algo::U32X4 as MulAssign<u32>>::mul_assign` and
//! `<adler2::Adler32 as Default>::default`. A name with any other suffix
//! keeps the importer's spelling.
//!
//! A crate trait's method implementation is named by its type, `_R` and the
//! trait's own importer name with its length, and the method
//! (`trait_method_name`), and prints as `<traits::Square as
//! traits::Shape>::area`.

use std::borrow::Cow;

const PREFIX: &str = "__rust_q";

/// Appends one path segment to an importer name: `_I`, its length, `_`, and
/// the segment. A closure, `{closure#0}` as rustc names it, is `_K` and its
/// index.
pub(crate) fn push_path_segment(encoded: &mut String, segment: &str) {
    match closure_index(segment) {
        Some(index) => encoded.push_str(&format!("_K{index}")),
        None => encoded.push_str(&format!("_I{}_{segment}", segment.len())),
    }
}

/// The index of a closure segment, `{closure#0}`.
fn closure_index(segment: &str) -> Option<u32> {
    let digits = segment.strip_prefix("{closure#")?.strip_suffix('}')?;
    (!digits.is_empty() && digits.bytes().all(|byte| byte.is_ascii_digit()))
        .then(|| digits.parse().ok())
        .flatten()
}

/// The function that creates an instance of the closure named `closure`:
/// it takes the captured values and returns the callable value. No path
/// segment ends in `_instance`, so the name is no item's.
pub(crate) fn closure_instance_name(closure: &str) -> String {
    format!("{closure}_instance")
}

/// The rustc spelling of the closure with index `index`, `{closure#0}`.
pub(crate) fn closure_segment(index: u32) -> String {
    format!("{{closure#{index}}}")
}

/// Appends the type an inherent method's `impl` block names: `_T`, the
/// type's own importer name's length, `_`, and that name.
pub(crate) fn push_impl_type(encoded: &mut String, type_name: &str) {
    encoded.push_str(&format!("_T{}_{type_name}", type_name.len()));
}

/// The name of crate trait `trait_name`'s method `method` implemented for
/// the type named `type_name`: the type, the trait, and the method,
/// `<traits::Square as traits::Shape>::area`. A type implements a trait
/// once, so the `impl` block's module is not needed.
pub(crate) fn trait_method_name(type_name: &str, trait_name: &str, method: &str) -> String {
    let mut encoded = PREFIX.to_string();
    push_impl_type(&mut encoded, type_name);
    encoded.push_str(&format!("_R{}_{trait_name}", trait_name.len()));
    push_path_segment(&mut encoded, method);
    encoded
}

/// Whether `name` is a Rust importer name.
pub(crate) fn is_rust_name(name: &str) -> bool {
    name.starts_with(PREFIX)
}

/// Whether `name` is a function the importer places where a crate struct
/// reference becomes a crate trait's object, or back:
/// `<S as Trait>::__pack` or `<S as Trait>::__unpack`.
pub(crate) fn is_object_coercion(name: &str) -> bool {
    name.starts_with(PREFIX)
        && name.contains("_R")
        && (name.ends_with("_I6___pack") || name.ends_with("_I8___unpack"))
}

/// The importer name of the item at a path, `quad::walk` or
/// `adler2::algo::U32X4`: the prefix and each segment
/// (`__rust_q_I4_quad_I4_walk`).
pub(crate) fn qualified_name<'s>(segments: impl IntoIterator<Item = &'s str>) -> String {
    let mut encoded = PREFIX.to_string();
    for segment in segments {
        push_path_segment(&mut encoded, segment);
    }
    encoded
}

/// The name a sidecar's path of segments denotes: a single segment is the
/// name itself, a longer path its [`qualified_name`].
pub(crate) fn path_name(segments: &[&str]) -> String {
    match segments {
        [name] => (*name).to_string(),
        _ => qualified_name(segments.iter().copied()),
    }
}

/// The name of an inherent method of the type named `impl_type`, whose
/// `impl` block is in the type's own module. A type named by a path has
/// the importer's qualified method name, its module, then the `impl` type,
/// then the method; any other is `Type_method`.
pub(crate) fn inherent_method_name(
    impl_module: Option<&str>,
    impl_type: &str,
    method: &str,
) -> String {
    // An item inside the method, `compute::LIMIT`, arrives with its path
    // segments already written after the method's own name
    // ([`method_path_name`]); the length the importer writes is the
    // method's alone.
    let (own, inside) = method.split_at(method.find("_I").unwrap_or(method.len()));
    match impl_module {
        Some(module) => {
            let mut encoded = module.to_string();
            push_impl_type(&mut encoded, impl_type);
            push_path_segment(&mut encoded, own);
            encoded.push_str(inside);
            encoded
        }
        None => format!("{impl_type}_{method}"),
    }
}

/// A method's name as written in an `impl` block, `compute` or
/// `compute::LIMIT`: the method's own name, then each further segment as
/// the importer writes a path segment.
pub(crate) fn method_path_name(path: &[&str]) -> String {
    let mut name = path[0].to_string();
    for segment in &path[1..] {
        push_path_segment(&mut name, segment);
    }
    name
}

/// The path `name` stands for, `quad::walk`, when it is a whole importer
/// name; `None` for any other name.
pub fn rust_display_name(name: &str) -> Option<String> {
    let (path, rest) = decode(name)?;
    if rest.is_empty() {
        return Some(path);
    }
    operator_method_display(&path, rest)
}

/// The operator-trait methods the importer names after their type, by method
/// name, with the trait each belongs to.
const OPERATOR_METHODS: [(&str, &str); 10] = [
    ("add_assign", "AddAssign"),
    ("sub_assign", "SubAssign"),
    ("mul_assign", "MulAssign"),
    ("div_assign", "DivAssign"),
    ("rem_assign", "RemAssign"),
    ("bitand_assign", "BitAndAssign"),
    ("bitor_assign", "BitOrAssign"),
    ("bitxor_assign", "BitXorAssign"),
    ("shl_assign", "ShlAssign"),
    ("shr_assign", "ShrAssign"),
];

/// The scalar types an operator trait's argument may name directly.
const SCALARS: [&str; 6] = ["i32", "u8", "u16", "u32", "usize", "bool"];

/// The qualified form of the method of type `type_path` whose importer name
/// continues with `suffix`: `_default`, or `_<method>_<argument>` for an
/// operator trait. `None` for any other suffix.
fn operator_method_display(type_path: &str, suffix: &str) -> Option<String> {
    let suffix = suffix.strip_prefix('_')?;
    if suffix == "default" {
        return Some(format!("<{type_path} as Default>::default"));
    }
    OPERATOR_METHODS.iter().find_map(|(method, trait_name)| {
        let argument = suffix.strip_prefix(method)?.strip_prefix('_')?;
        let argument = trait_argument_display(argument)?;
        Some(format!(
            "<{type_path} as {trait_name}<{argument}>>::{method}"
        ))
    })
}

/// The Rust spelling of an operator trait's type argument as the importer
/// encodes it: a scalar by name, a record by value as
/// `value_<length><name>`, and a reference as `ref_` or `ref_mut_` and what
/// it refers to.
fn trait_argument_display(argument: &str) -> Option<String> {
    if let Some(referent) = argument.strip_prefix("ref_mut_") {
        return Some(format!("&mut {}", type_display(referent)?));
    }
    if let Some(referent) = argument.strip_prefix("ref_") {
        return Some(format!("&{}", type_display(referent)?));
    }
    if let Some(value) = argument.strip_prefix("value_") {
        let digits = value.bytes().take_while(u8::is_ascii_digit).count();
        let length = value[..digits].parse::<usize>().ok()?;
        let name = value.get(digits..)?;
        return (name.len() == length).then(|| type_display(name)).flatten();
    }
    SCALARS.contains(&argument).then(|| argument.to_string())
}

/// A type name the importer wrote whole: a scalar, an importer path, or a
/// type at the crate root by its bare name.
fn type_display(name: &str) -> Option<String> {
    if SCALARS.contains(&name) {
        return Some(name.to_string());
    }
    match decode(name) {
        Some((path, "")) => Some(path),
        Some(_) => None,
        None => (!name.is_empty()
            && !name.starts_with(PREFIX)
            && name
                .bytes()
                .all(|byte| byte.is_ascii_alphanumeric() || byte == b'_'))
        .then(|| name.to_string()),
    }
}

/// Decodes the importer name at the start of `text`: its path and the text
/// after it.
fn decode(text: &str) -> Option<(String, &str)> {
    let mut rest = text.strip_prefix(PREFIX)?;
    let mut segments: Vec<String> = Vec::new();
    while let Some(tail) = rest.strip_prefix('_') {
        if let Some(closure) = tail.strip_prefix('K') {
            let digits = closure.bytes().take_while(u8::is_ascii_digit).count();
            let Ok(index) = closure[..digits].parse::<u32>() else {
                break;
            };
            if !(closure[digits..].is_empty() || closure[digits..].starts_with('_')) {
                break;
            }
            segments.push(closure_segment(index));
            rest = &closure[digits..];
            continue;
        }
        let (kind, tail) = match tail.as_bytes().first() {
            Some(b'I') => ('I', &tail[1..]),
            Some(b'T') => ('T', &tail[1..]),
            Some(b'R') => ('R', &tail[1..]),
            _ => break,
        };
        let digits = tail.bytes().take_while(u8::is_ascii_digit).count();
        if digits == 0 {
            break;
        }
        let Ok(length) = tail[..digits].parse::<usize>() else {
            break;
        };
        let Some(segment_start) = tail[digits..].strip_prefix('_') else {
            break;
        };
        let Some(segment) = segment_start.get(..length) else {
            break;
        };
        if kind == 'R' {
            // The trait an `impl` block for the type before it implements.
            let (Some((trait_path, "")), [type_path]) = (decode(segment), segments.as_slice())
            else {
                break;
            };
            segments = vec![format!("<{type_path} as {trait_path}>")];
        } else if kind == 'T' {
            // A type is named by its own path, which includes its module:
            // the method's module is not written again.
            let Some((type_path, "")) = decode(segment) else {
                // A type at the crate root is its bare name.
                segments.push(segment.to_string());
                rest = &segment_start[length..];
                continue;
            };
            segments = vec![type_path];
        } else {
            if !segment
                .bytes()
                .all(|byte| byte.is_ascii_alphanumeric() || byte == b'_')
            {
                break;
            }
            segments.push(segment.to_string());
        }
        rest = &segment_start[length..];
    }
    if segments.len() < 2 && !segments.iter().any(|segment| segment.contains("::")) {
        return None;
    }
    Some((segments.join("::"), rest))
}

/// `text` with every whole importer name it contains spelled as its path.
pub fn display_rust_names(text: &str) -> Cow<'_, str> {
    if !text.contains(PREFIX) {
        return Cow::Borrowed(text);
    }
    let mut output = String::with_capacity(text.len());
    let mut rest = text;
    while let Some(start) = rest.find(PREFIX) {
        let preceded_by_identifier = rest[..start]
            .bytes()
            .last()
            .is_some_and(|byte| byte.is_ascii_alphanumeric() || byte == b'_');
        output.push_str(&rest[..start]);
        let candidate = &rest[start..];
        let end = candidate
            .bytes()
            .position(|byte| !(byte.is_ascii_alphanumeric() || byte == b'_'))
            .unwrap_or(candidate.len());
        let identifier = &candidate[..end];
        match (!preceded_by_identifier)
            .then(|| rust_display_name(identifier))
            .flatten()
        {
            Some(path) => output.push_str(&path),
            None => output.push_str(identifier),
        }
        rest = &candidate[end..];
    }
    output.push_str(rest);
    Cow::Owned(output)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::languages::claim_label_matches;

    #[test]
    fn importer_names_read_as_their_paths() {
        assert_eq!(
            rust_display_name("__rust_q_I4_quad_I4_walk").as_deref(),
            Some("quad::walk")
        );
        assert_eq!(
            rust_display_name("__rust_q_I6_adler2_I4_algo_I5_U32X4").as_deref(),
            Some("adler2::algo::U32X4")
        );
        assert_eq!(
            rust_display_name("__rust_q_I6_adler2_T29___rust_q_I6_adler2_I7_Adler32_I3_new")
                .as_deref(),
            Some("adler2::Adler32::new")
        );
        assert_eq!(
            rust_display_name(
                "__rust_q_I6_adler2_I4_algo_T29___rust_q_I6_adler2_I7_Adler32_I7_compute_I3_MOD"
            )
            .as_deref(),
            Some("adler2::Adler32::compute::MOD")
        );
        assert_eq!(
            rust_display_name(&trait_method_name(
                "__rust_q_I6_traits_I6_Square",
                "__rust_q_I6_traits_I5_Shape",
                "area"
            ))
            .as_deref(),
            Some("<traits::Square as traits::Shape>::area")
        );
        // A suffix that is no operator method keeps the importer's spelling.
        assert_eq!(
            rust_display_name("__rust_q_I6_adler2_I4_algo_I5_U32X4_frobnicate_u32"),
            None
        );
        assert_eq!(
            rust_display_name("__rust_q_I6_adler2_I4_algo_I5_U32X4_mul_assign_f99"),
            None
        );
        assert_eq!(rust_display_name("walk"), None);
        assert_eq!(rust_display_name("__rust_q_I9_short"), None);
    }

    #[test]
    fn closure_names_read_as_rustc_spells_them() {
        let name = path_name(&["closures", "choose", "{closure#1}"]);
        assert_eq!(name, "__rust_q_I8_closures_I6_choose_K1");
        assert_eq!(
            rust_display_name(&name).as_deref(),
            Some("closures::choose::{closure#1}")
        );
        // A segment that only resembles a closure is an ordinary segment.
        assert_eq!(closure_index("{closure#}"), None);
        assert_eq!(closure_index("{closure#1x}"), None);
        assert_eq!(rust_display_name("__rust_q_I8_closures_K1x"), None);
    }

    #[test]
    fn operator_methods_read_as_qualified_trait_methods() {
        let lanes = "__rust_q_I6_adler2_I4_algo_I5_U32X4";
        let cases = [
            (
                format!("{lanes}_mul_assign_u32"),
                "<adler2::algo::U32X4 as MulAssign<u32>>::mul_assign",
            ),
            (
                format!("{lanes}_add_assign_value_{}{lanes}", lanes.len()),
                "<adler2::algo::U32X4 as AddAssign<adler2::algo::U32X4>>::add_assign",
            ),
            (
                format!("{lanes}_add_assign_ref_{lanes}"),
                "<adler2::algo::U32X4 as AddAssign<&adler2::algo::U32X4>>::add_assign",
            ),
            (
                format!("{lanes}_rem_assign_ref_mut_{lanes}"),
                "<adler2::algo::U32X4 as RemAssign<&mut adler2::algo::U32X4>>::rem_assign",
            ),
            (
                format!("{lanes}_sub_assign_ref_u16"),
                "<adler2::algo::U32X4 as SubAssign<&u16>>::sub_assign",
            ),
            (
                format!("{lanes}_shl_assign_value_5Lanes"),
                "<adler2::algo::U32X4 as ShlAssign<Lanes>>::shl_assign",
            ),
            (
                "__rust_q_I6_adler2_I7_Adler32_default".to_string(),
                "<adler2::Adler32 as Default>::default",
            ),
        ];
        for (name, display) in cases {
            assert_eq!(rust_display_name(&name).as_deref(), Some(display), "{name}");
            let label = format!("{name}.contract");
            assert_eq!(display_rust_names(&label), format!("{display}.contract"));
            assert!(claim_label_matches(&label, &format!("{display}.contract")));
            assert!(claim_label_matches(&label, &label));
        }
        for (method, trait_name) in OPERATOR_METHODS {
            assert_eq!(
                rust_display_name(&format!("{lanes}_{method}_bool")),
                Some(format!(
                    "<adler2::algo::U32X4 as {trait_name}<bool>>::{method}"
                ))
            );
        }
        // A by-value record's length must cover its whole name.
        assert_eq!(
            rust_display_name(&format!("{lanes}_add_assign_value_4{lanes}")),
            None
        );
        assert_eq!(rust_display_name(&format!("{lanes}_default_u32")), None);
    }

    #[test]
    fn a_message_prints_paths_for_importer_names() {
        assert_eq!(
            display_rust_names(
                "`__rust_q_I4_quad_I4_walk.contract` path 0: x___rust_q_I4_quad_I4_walk stays"
            ),
            "`quad::walk.contract` path 0: x___rust_q_I4_quad_I4_walk stays"
        );
        assert!(matches!(
            display_rust_names("plain"),
            Cow::Borrowed("plain")
        ));
        assert!(claim_label_matches(
            "__rust_q_I4_quad_I4_walk.contract",
            "quad::walk.contract"
        ));
        assert!(claim_label_matches(
            "__rust_q_I4_quad_I4_walk.contract",
            "__rust_q_I4_quad_I4_walk.contract"
        ));
        assert!(!claim_label_matches(
            "__rust_q_I4_quad_I4_walk.contract",
            "quad::other.contract"
        ));
    }
}
