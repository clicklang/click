//! Resolve proof names once from compiler identities, independently of spelling.

use std::collections::BTreeMap;
use std::fmt::Write;

/// Clang's stable declaration identity from the checked capture. Keeping it
/// separate from the C++ path preserves overloads with the same proof types.
#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
struct DeclarationId(String);

impl std::borrow::Borrow<str> for DeclarationId {
    fn borrow(&self) -> &str {
        &self.0
    }
}

#[derive(Clone, Debug)]
pub(super) struct ResolvedNames(BTreeMap<DeclarationId, String>);

impl ResolvedNames {
    pub(super) fn new<'a>(
        declarations: impl IntoIterator<Item = (&'a str, &'a str)>,
    ) -> Result<Self, String> {
        let mut by_id = BTreeMap::new();
        let mut counts = BTreeMap::<&str, usize>::new();
        for (id, path) in declarations {
            crate::instrumentation::record_deterministic_work(1);
            if id.is_empty()
                || path.is_empty()
                || by_id.insert(DeclarationId(id.into()), path).is_some()
            {
                return Err(format!(
                    "invalid or duplicate C++ declaration identity `{id}`"
                ));
            }
            *counts.entry(path).or_default() += 1;
        }
        let mut resolved = BTreeMap::new();
        for (id, path) in by_id {
            crate::instrumentation::record_deterministic_work(1);
            let name = if counts[path] == 1
                && super::import::is_identifier(path)
                && !is_declaration_key(path)
            {
                path.to_owned()
            } else {
                declaration_key(path, &id)
            };
            resolved.insert(id, name);
        }
        Ok(Self(resolved))
    }

    pub(super) fn get(&self, id: &str) -> Option<&str> {
        self.0.get(id).map(String::as_str)
    }

    pub(super) fn require(&self, id: &str) -> Result<&str, String> {
        self.get(id)
            .ok_or_else(|| format!("unresolved C++ declaration identity `{id}`"))
    }
}

/// The prefix of a C++ importer name that encodes a path.
const PATH_PREFIX: &str = "__cpp_q";

/// The importer name of the C++ declaration at `path`, `Square::area` as
/// `["Square", "area"]`, as a Rust item's is named
/// (`crate::languages::rust::names`): `__cpp_q` and each segment with its
/// length, `__cpp_q_I6_Square_I4_area`. A segment that is no identifier,
/// `operator+=`, `~Rec`, `Stored<long long>`, `(lambda#0)` or `choose<true>`,
/// is written as `_X`, its length in bytes, `_`, and its bytes in hex. A
/// single identifier is the name itself, as a free function's is. The
/// encoding is self-delimiting, so decoding needs no import.
pub fn path_name<S: AsRef<str>>(path: &[S]) -> String {
    match path {
        [single] if super::import::is_identifier(single.as_ref()) => single.as_ref().to_owned(),
        _ => {
            let mut encoded = String::from(PATH_PREFIX);
            for segment in path {
                crate::instrumentation::record_deterministic_work(1);
                let segment = segment.as_ref();
                if super::import::is_identifier(segment) {
                    write!(encoded, "_I{}_{segment}", segment.len()).expect("writing to String");
                } else {
                    encode_component(&mut encoded, 'X', segment);
                }
            }
            encoded
        }
    }
}

fn encode_component(encoded: &mut String, kind: char, value: &str) {
    write!(encoded, "_{kind}{}_", value.len()).expect("writing to String");
    for byte in value.bytes() {
        crate::instrumentation::record_deterministic_work(1);
        write!(encoded, "{byte:02x}").expect("writing to String");
    }
}

/// The shared verifier's string key for an overload. It carries the C++ path
/// for display and the unchanged Clang declaration identity for equality.
/// The identity component is never part of the displayed path.
fn declaration_key(path: &str, id: &DeclarationId) -> String {
    let display = decode(path).and_then(|(display, rest, declaration)| {
        (rest.is_empty() && !declaration).then_some(display)
    });
    let mut encoded = String::from(PATH_PREFIX);
    encode_component(&mut encoded, 'X', display.as_deref().unwrap_or(path));
    encode_component(&mut encoded, 'D', &id.0);
    encoded
}

/// The checked declaration at a written lambda expression. The regular
/// C++ codec keeps the complete proof spelling in one path component.
pub(crate) fn lambda_name(
    owner: &str,
    statements: &[usize],
    argument: Option<(usize, usize)>,
) -> String {
    let mut path = owner.to_owned();
    for statement in statements {
        write!(path, ".statement({statement})").expect("writing to String");
    }
    if let Some((call, argument)) = argument {
        write!(path, ".call({call}).argument({argument})").expect("writing to String");
    } else {
        path.push_str(".initializer");
    }
    path_name(&[path])
}

/// Decodes the importer name at the start of `text`: its C++ path, and the
/// text after it.
fn decode(text: &str) -> Option<(String, &str, bool)> {
    let mut rest = text.strip_prefix(PATH_PREFIX)?;
    let mut segments = Vec::new();
    let mut declaration = false;
    while let Some(tail) = rest.strip_prefix('_') {
        let Some(kind @ (b'I' | b'X' | b'D')) = tail.bytes().next() else {
            break;
        };
        let tail = &tail[1..];
        let hex = kind != b'I';
        let digits = tail.bytes().take_while(u8::is_ascii_digit).count();
        let Some(length) = (digits > 0)
            .then(|| tail[..digits].parse::<usize>().ok())
            .flatten()
        else {
            break;
        };
        let Some(body) = tail[digits..].strip_prefix('_') else {
            break;
        };
        let width = if hex { length.checked_mul(2)? } else { length };
        let Some(written) = body.get(..width) else {
            break;
        };
        let segment = if hex {
            let bytes = (0..length)
                .map(|index| u8::from_str_radix(written.get(2 * index..2 * index + 2)?, 16).ok())
                .collect::<Option<Vec<_>>>()?;
            String::from_utf8(bytes).ok()?
        } else if super::import::is_identifier(written) {
            written.to_string()
        } else {
            break;
        };
        rest = &body[width..];
        if kind == b'D' {
            if segments.is_empty() || segment.is_empty() {
                return None;
            }
            declaration = true;
            break;
        }
        segments.push(segment);
    }
    (!segments.is_empty()).then(|| (segments.join("::"), rest, declaration))
}

/// Whether a verifier key selects a declaration more precisely than its
/// displayed path. A bare path must not select this key in CLI claim lookup.
pub(crate) fn is_declaration_key(name: &str) -> bool {
    name.contains("_D")
        && decode(name).is_some_and(|(_, rest, declaration)| declaration && rest.is_empty())
}

/// The C++ spelling `name` stands for, `Square::area`, when it is a whole
/// importer name; `None` for any other name.
pub fn cpp_display_name(name: &str) -> Option<String> {
    let (path, rest, _) = decode(name)?;
    rest.is_empty().then_some(path)
}

/// `text` with every whole C++ importer name it contains spelled as C++
/// spells it.
pub fn display_cpp_names(text: &str) -> std::borrow::Cow<'_, str> {
    match display_function_names(text) {
        std::borrow::Cow::Borrowed(text) => display_record_names(text),
        std::borrow::Cow::Owned(text) => {
            std::borrow::Cow::Owned(display_record_names(&text).into_owned())
        }
    }
}

/// The C++ path of each record whose importer layout name differs from it,
/// `Box__int__bool_false` for `Box<int, false>`, by layout name. A layout
/// name is no encoding a diagnostic can decode, so each prepared import
/// records its own here ([`register_record_display`]).
static RECORD_DISPLAY: std::sync::RwLock<std::collections::BTreeMap<String, String>> =
    std::sync::RwLock::new(std::collections::BTreeMap::new());

/// Records that layout name `layout` prints as C++ path `path`.
pub(crate) fn register_record_display(layout: &str, path: &str) {
    if layout == path {
        return;
    }
    let mut table = RECORD_DISPLAY
        .write()
        .unwrap_or_else(|error| error.into_inner());
    if table.get(layout).map(String::as_str) != Some(path) {
        table.insert(layout.to_string(), path.to_string());
    }
}

/// `text` with each registered record layout name, `struct
/// Box__int__bool_false` or bare, written as its C++ path, `Box<int, false>`.
fn display_record_names(text: &str) -> std::borrow::Cow<'_, str> {
    let table = RECORD_DISPLAY
        .read()
        .unwrap_or_else(|error| error.into_inner());
    if table.is_empty() {
        return std::borrow::Cow::Borrowed(text);
    }
    let mut output = String::with_capacity(text.len());
    let mut changed = false;
    let mut rest = text;
    while let Some(start) = rest.find(|c: char| c.is_ascii_alphabetic() || c == '_') {
        crate::instrumentation::record_deterministic_work(1);
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
            .then(|| table.get(identifier))
            .flatten()
        {
            Some(path) => {
                // C++ writes the record by its path alone.
                if output.ends_with("struct ") {
                    output.truncate(output.len() - "struct ".len());
                }
                output.push_str(path);
                changed = true;
            }
            None => output.push_str(identifier),
        }
        rest = &candidate[end..];
    }
    output.push_str(rest);
    if changed {
        std::borrow::Cow::Owned(output)
    } else {
        std::borrow::Cow::Borrowed(text)
    }
}

/// `text` with each importer function name written as its C++ path.
fn display_function_names(text: &str) -> std::borrow::Cow<'_, str> {
    if !text.contains(PATH_PREFIX) {
        return std::borrow::Cow::Borrowed(text);
    }
    let mut output = String::with_capacity(text.len());
    let mut rest = text;
    while let Some(start) = rest.find(PATH_PREFIX) {
        crate::instrumentation::record_deterministic_work(1);
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
            .then(|| cpp_display_name(identifier))
            .flatten()
        {
            Some(path) => output.push_str(&path),
            None => output.push_str(identifier),
        }
        rest = &candidate[end..];
    }
    output.push_str(rest);
    std::borrow::Cow::Owned(output)
}

#[cfg(test)]
mod path_tests {
    use super::*;

    #[test]
    fn importer_names_read_as_cpp_spells_them() {
        for path in [
            &["Square", "area"][..],
            &["Rec", "operator+="],
            &["Rec", "~Rec"],
            &["Stored<long long>", "Read"],
            &["caller", "(lambda#0)"],
            &["choose<true>"],
            &["ns", "inner", "f"],
        ] {
            let name = path_name(path);
            assert!(super::super::import::is_identifier(&name), "{name}");
            assert_eq!(cpp_display_name(&name), Some(path.join("::")));
            assert_eq!(
                display_cpp_names(&format!("`{name}.ensures_0` and {name}_suffix")),
                format!("`{}.ensures_0` and {name}_suffix", path.join("::"))
            );
        }
        assert_eq!(path_name(&["total"]), "total");
        assert_eq!(path_name(&["Square", "area"]), "__cpp_q_I6_Square_I4_area");
        assert_eq!(cpp_display_name("total"), None);
        assert_eq!(cpp_display_name("__cpp_q_I9_short"), None);
        assert_eq!(cpp_display_name("__cpp_q_X2_zz"), None);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn names_are_injective_and_independent_of_traversal_order() {
        let path = path_name(&["C", "same"]);
        let declarations = [
            ("a", path.as_str()),
            ("b", path.as_str()),
            ("c", "ordinary"),
            ("d", "__click_cpp_decl_61"),
            ("e", "(anonymous namespace)_helper"),
        ];
        let forward = ResolvedNames::new(declarations).unwrap();
        let backward = ResolvedNames::new(declarations.into_iter().rev()).unwrap();
        assert_eq!(forward.0, backward.0);
        assert_eq!(forward.get("c"), Some("ordinary"));
        assert_eq!(forward.get("d"), Some("__click_cpp_decl_61"));
        for id in ["a", "b"] {
            let key = forward.require(id).unwrap();
            assert_eq!(cpp_display_name(key).as_deref(), Some("C::same"));
            assert_eq!(crate::languages::source_display_name(key), None);
            assert!(!crate::languages::claim_label_matches(
                &format!("{key}.ensures_0"),
                "C::same.ensures_0",
            ));
        }
        assert_eq!(
            forward
                .0
                .values()
                .collect::<std::collections::BTreeSet<_>>()
                .len(),
            5
        );
        assert!(forward.require("unknown").is_err());
        assert!(ResolvedNames::new([("a", "one"), ("a", "two")]).is_err());
    }

    #[cfg(test)]
    mod scaling_tests {
        include!("../../scaling_tests/languages/cpp/names/tests.rs");
    }
}

/// Nominal exception sorts are distinct from generic type parameters with the
/// same identifier. Their name is an existing, parseable elaborated type.
pub(crate) fn opaque_exception_type(record: &str) -> crate::kernel::TypeParameterName {
    crate::kernel::TypeParameterName::intern(&format!("struct {record}"))
}
