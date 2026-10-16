//! Resolve proof names once from compiler identities, independently of spelling.

use std::collections::BTreeMap;
use std::fmt::Write;

const RESERVED_PREFIX: &str = "__click_cpp_decl_";

#[derive(Clone, Debug)]
pub(super) struct ResolvedNames(BTreeMap<String, String>);

impl ResolvedNames {
    pub(super) fn new<'a>(
        declarations: impl IntoIterator<Item = (&'a str, &'a str)>,
    ) -> Result<Self, String> {
        let mut by_id = BTreeMap::new();
        let mut counts = BTreeMap::<&str, usize>::new();
        for (id, name) in declarations {
            crate::instrumentation::record_deterministic_work(1);
            if id.is_empty() || name.is_empty() || by_id.insert(id, name).is_some() {
                return Err(format!(
                    "invalid or duplicate C++ declaration identity `{id}`"
                ));
            }
            *counts.entry(name).or_default() += 1;
        }
        let mut resolved = BTreeMap::new();
        for (id, name) in by_id {
            crate::instrumentation::record_deterministic_work(1);
            let name = if counts[name] == 1
                && !name.starts_with(RESERVED_PREFIX)
                && super::import::is_identifier(name)
            {
                name.to_owned()
            } else {
                // Full byte encoding is injective, unlike a truncated digest. Reserving
                // the prefix also excludes collisions with ordinary source spellings.
                let mut encoded = String::from(RESERVED_PREFIX);
                for byte in id.bytes() {
                    crate::instrumentation::record_deterministic_work(1);
                    write!(encoded, "{byte:02x}").expect("writing to String");
                }
                encoded
            };
            resolved.insert(id.to_owned(), name);
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
                    write!(encoded, "_X{}_", segment.len()).expect("writing to String");
                    for byte in segment.bytes() {
                        write!(encoded, "{byte:02x}").expect("writing to String");
                    }
                }
            }
            encoded
        }
    }
}

/// Decodes the importer name at the start of `text`: its C++ path, and the
/// text after it.
fn decode(text: &str) -> Option<(String, &str)> {
    let mut rest = text.strip_prefix(PATH_PREFIX)?;
    let mut segments = Vec::new();
    while let Some(tail) = rest.strip_prefix('_') {
        let (hex, tail) = match tail.as_bytes().first() {
            Some(b'I') => (false, &tail[1..]),
            Some(b'X') => (true, &tail[1..]),
            _ => break,
        };
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
                .map(|index| u8::from_str_radix(&written[2 * index..2 * index + 2], 16).ok())
                .collect::<Option<Vec<_>>>()?;
            String::from_utf8(bytes).ok()?
        } else if super::import::is_identifier(written) {
            written.to_string()
        } else {
            break;
        };
        segments.push(segment);
        rest = &body[width..];
    }
    (!segments.is_empty()).then(|| (segments.join("::"), rest))
}

/// The C++ spelling `name` stands for, `Square::area`, when it is a whole
/// importer name; `None` for any other name.
pub fn cpp_display_name(name: &str) -> Option<String> {
    let (path, rest) = decode(name)?;
    rest.is_empty().then_some(path)
}

/// `text` with every whole C++ importer name it contains spelled as C++
/// spells it.
pub fn display_cpp_names(text: &str) -> std::borrow::Cow<'_, str> {
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

/// The function the importer places where a reference to `derived` becomes
/// a reference to its polymorphic base `base`: it makes the base class's
/// object, whose state the sidecar declares, from the derived class's memory.
pub(crate) fn object_pack_name(derived: &str, base: &str) -> String {
    format!("{derived}__click_pack__{base}")
}

/// The function the importer places after such a call, returning the
/// derived class's memory.
pub(crate) fn object_unpack_name(derived: &str, base: &str) -> String {
    format!("{derived}__click_unpack__{base}")
}

/// Whether `name` is one of those functions.
pub(crate) fn is_object_coercion(name: &str) -> bool {
    name.contains("__click_pack__") || name.contains("__click_unpack__")
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
                display_cpp_names(&format!("`{name}.ensures_0` and {name}_iface")),
                format!("`{}.ensures_0` and {name}_iface", path.join("::"))
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
        let declarations = [
            ("a", "same"),
            ("b", "same"),
            ("c", "ordinary"),
            ("d", "__click_cpp_decl_61"),
            ("e", "(anonymous namespace)_helper"),
        ];
        let forward = ResolvedNames::new(declarations).unwrap();
        let backward = ResolvedNames::new(declarations.into_iter().rev()).unwrap();
        assert_eq!(forward.0, backward.0);
        assert_eq!(forward.get("c"), Some("ordinary"));
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
