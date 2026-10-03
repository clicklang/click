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

    #[test]
    fn collision_resolution_work_scales_with_declarations_and_identity_bytes() {
        for size in [8, 32, 128, 512] {
            let ids = (0..size)
                .map(|i| format!("scope_{i:04}"))
                .collect::<Vec<_>>();
            let (names, work) = crate::instrumentation::measure_deterministic_work(|| {
                ResolvedNames::new(ids.iter().map(|id| (id.as_str(), "same")))
            });
            let names = names.unwrap();
            assert_eq!(
                names
                    .0
                    .values()
                    .collect::<std::collections::BTreeSet<_>>()
                    .len(),
                size
            );
            let bytes = ids.iter().map(String::len).sum::<usize>();
            assert!(
                work >= bytes && work <= bytes + 3 * size,
                "size {size}: {work}"
            );
        }
    }
}
