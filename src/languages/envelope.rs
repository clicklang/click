//! The common shape of a unit's entry in `click.project.lock.json`. Every
//! language records the same fields: the digest of the unit's description,
//! the front end that prepared it, and for each logical source its input
//! digests, its artifact, and its import identity. What only one language
//! needs is in a section named for the language. One identity covers all of
//! it, so a change to any recorded field changes the identity.

use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};

use super::inputs::hex_digest;

/// The envelope's schema; an entry of another shape is refused.
pub(crate) const ENVELOPE_SCHEMA: u32 = 1;

/// The front end that prepared a unit: its name and the digest that pins it.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct Frontend {
    pub name: String,
    pub identity: String,
}

/// A prepared artifact: its path relative to the project directory, and its
/// digest and size.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct Artifact {
    pub path: String,
    pub sha256: String,
    pub bytes: usize,
}

/// One logical source: the digests of the inputs it was prepared from,
/// keyed by path, its artifact, and its import identity.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct Source {
    pub inputs: BTreeMap<String, String>,
    pub artifact: Artifact,
    pub identity: String,
}

/// A unit's entry. Exactly one language section is present.
#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct Entry {
    pub envelope: u32,
    pub unit: String,
    pub frontend: Frontend,
    pub sources: BTreeMap<String, Source>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub c: Option<serde_json::Value>,
    #[serde(default, rename = "c++", skip_serializing_if = "Option::is_none")]
    pub cpp: Option<serde_json::Value>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub rust: Option<serde_json::Value>,
}

/// A source before its identity is computed.
pub(crate) struct SourceParts {
    pub inputs: BTreeMap<String, String>,
    pub artifact: Artifact,
}

impl Entry {
    /// The entry for `language` with each source's identity computed.
    pub(crate) fn new(
        language: &str,
        unit: String,
        frontend: Frontend,
        sources: BTreeMap<String, SourceParts>,
        section: serde_json::Value,
    ) -> Self {
        let mut entry = Self {
            envelope: ENVELOPE_SCHEMA,
            unit,
            frontend,
            sources: BTreeMap::new(),
            c: None,
            cpp: None,
            rust: None,
        };
        *entry.section_slot(language) = Some(section);
        for (logical, parts) in sources {
            let identity = entry.identity_of(language, &logical, &parts.inputs, &parts.artifact);
            entry.sources.insert(
                logical,
                Source {
                    inputs: parts.inputs,
                    artifact: parts.artifact,
                    identity,
                },
            );
        }
        entry
    }

    /// Reads a unit's entry, refusing one in an earlier shape or for another
    /// language.
    pub(crate) fn parse(
        language: &str,
        unit_name: &str,
        value: &serde_json::Value,
    ) -> Result<Self, String> {
        if value.get("envelope").is_none() {
            return Err(format!(
                "the project lock entry for unit `{unit_name}` is in an earlier format; run `click import lock` to prepare it again"
            ));
        }
        let entry = Self::deserialize(value).map_err(|error| {
            format!("parse the project lock entry for unit `{unit_name}`: {error}")
        })?;
        if entry.envelope != ENVELOPE_SCHEMA {
            return Err(format!(
                "the project lock entry for unit `{unit_name}` has envelope schema {}, not {ENVELOPE_SCHEMA}; run `click import lock` to prepare it again",
                entry.envelope
            ));
        }
        let present = [entry.c.is_some(), entry.cpp.is_some(), entry.rust.is_some()]
            .iter()
            .filter(|present| **present)
            .count();
        if present != 1 || entry.section(language).is_none() {
            return Err(format!(
                "the project lock entry for unit `{unit_name}` needs exactly its `{language}` section"
            ));
        }
        Ok(entry)
    }

    /// The language section.
    pub(crate) fn section(&self, language: &str) -> Option<&serde_json::Value> {
        match language {
            "c" => self.c.as_ref(),
            "c++" => self.cpp.as_ref(),
            "rust" => self.rust.as_ref(),
            _ => None,
        }
    }

    fn section_slot(&mut self, language: &str) -> &mut Option<serde_json::Value> {
        match language {
            "c" => &mut self.c,
            "c++" => &mut self.cpp,
            "rust" => &mut self.rust,
            _ => unreachable!("an envelope language is C, C++ or Rust"),
        }
    }

    /// The identity of one source: a digest over the envelope schema, the
    /// language, the unit's description digest, the front end, the source's
    /// inputs and artifact, and the whole language section.
    fn identity_of(
        &self,
        language: &str,
        logical: &str,
        inputs: &BTreeMap<String, String>,
        artifact: &Artifact,
    ) -> String {
        let data = serde_json::to_vec(&serde_json::json!({
            "envelope": ENVELOPE_SCHEMA,
            "language": language,
            "unit": self.unit,
            "frontend": self.frontend,
            "source": logical,
            "inputs": inputs,
            "artifact": artifact,
            "section": self.section(language),
        }))
        .expect("a lock entry serializes");
        hex_digest(&data)
    }

    /// The recorded identity of `logical`, after checking it against the
    /// entry's fields. Loading checks it after the inputs and artifact, so a
    /// changed input is named before a mismatched identity.
    pub(crate) fn checked_identity(&self, language: &str, logical: &str) -> Result<String, String> {
        let source = self.sources.get(logical).ok_or_else(|| {
            format!("the project lock has no source `{logical}`; run `click import lock`")
        })?;
        if source.identity != self.identity_of(language, logical, &source.inputs, &source.artifact)
        {
            return Err(format!(
                "the import identity of `{logical}` does not match its locked inputs"
            ));
        }
        Ok(source.identity.clone())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn entry() -> Entry {
        Entry::new(
            "c",
            "unit".into(),
            Frontend {
                name: "gcc".into(),
                identity: "toolchain".into(),
            },
            BTreeMap::from([(
                "a.c".to_string(),
                SourceParts {
                    inputs: BTreeMap::from([("a.c".to_string(), "1".to_string())]),
                    artifact: Artifact {
                        path: ".click/u/a.c.i".into(),
                        sha256: "2".into(),
                        bytes: 3,
                    },
                },
            )]),
            serde_json::json!({"target": "x86_64-unknown-linux-gnu"}),
        )
    }

    #[test]
    fn every_recorded_field_is_covered_by_the_identity() {
        let original = entry();
        original.checked_identity("c", "a.c").unwrap();
        let mut changes: Vec<Box<dyn Fn(&mut Entry)>> = vec![
            Box::new(|entry| entry.unit = "other".into()),
            Box::new(|entry| entry.frontend.identity = "other".into()),
            Box::new(|entry| {
                entry
                    .sources
                    .get_mut("a.c")
                    .unwrap()
                    .inputs
                    .insert("b.h".into(), "4".into());
            }),
            Box::new(|entry| entry.sources.get_mut("a.c").unwrap().artifact.bytes = 4),
            Box::new(|entry| entry.sources.get_mut("a.c").unwrap().artifact.path = "x".into()),
            Box::new(|entry| entry.c = Some(serde_json::json!({"target": "other"}))),
        ];
        for change in changes.drain(..) {
            let mut changed = original.clone();
            change(&mut changed);
            assert!(changed.checked_identity("c", "a.c").is_err());
        }
    }

    #[test]
    fn an_entry_in_an_earlier_shape_or_for_another_language_is_refused() {
        let value = serde_json::to_value(entry()).unwrap();
        Entry::parse("c", "u", &value).unwrap();
        let error = Entry::parse("rust", "u", &value).unwrap_err();
        assert!(error.contains("exactly its `rust` section"), "{error}");
        let error = Entry::parse("c", "u", &serde_json::json!({"schema": 3})).unwrap_err();
        assert!(
            error.contains("earlier format; run `click import lock`"),
            "{error}"
        );
    }
}
