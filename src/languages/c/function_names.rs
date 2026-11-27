//! C linkage identities. Only the common verifier's string-keyed function
//! interfaces need a textual key for a translation-unit-local declaration.

use crate::kernel::LocalFunctionId;

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub(crate) enum FunctionName {
    External(String),
    TranslationUnit {
        identity: LocalFunctionId,
        qualified: String,
    },
}

impl FunctionName {
    pub(super) fn translation_unit(identity: LocalFunctionId) -> Self {
        let (source, name) = identity.source_and_name();
        let qualified = format!("{:?}::{name}", source.unwrap_or_default());
        Self::TranslationUnit {
            identity,
            qualified,
        }
    }

    pub(super) fn execution_key(&self) -> &str {
        match self {
            Self::External(symbol) => symbol,
            Self::TranslationUnit { qualified, .. } => qualified,
        }
    }

    pub(super) fn into_string(self) -> String {
        match self {
            Self::External(symbol) => symbol,
            Self::TranslationUnit { qualified, .. } => qualified,
        }
    }
}

/// A bare name in a proof selects the callee at the current call site. A
/// qualified key selects the exact translation unit.
pub(crate) fn source_spelling(key: &str) -> &str {
    translation_unit_spelling(key).unwrap_or(key)
}

pub(super) fn translation_unit_spelling(key: &str) -> Option<&str> {
    let (_, name) = key.strip_prefix('"')?.rsplit_once("\"::")?;
    let mut chars = name.bytes();
    let first = chars.next()?;
    ((first.is_ascii_alphabetic() || first == b'_')
        && chars.all(|byte| byte.is_ascii_alphanumeric() || byte == b'_'))
    .then_some(name)
}
