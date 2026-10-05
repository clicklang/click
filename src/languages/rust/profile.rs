//! The compiled-in extraction and semantic profile. Changes to interpretation
//! must version its named semantic entry; existing lock byte order is stable.
use serde::Deserialize;
use std::sync::OnceLock;

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct Profile {
    schema: u32,
    pub identity: String,
    pub extractor_revision: String,
    pub extractor_version: String,
    pub compiler_commit: String,
    pub toolchain: String,
    pub extraction: String,
    pub flags: Vec<String>,
    semantics: Vec<String>,
}
impl Profile {
    pub fn semantic_identity(&self) -> String {
        format!(
            "{}\n{}\n{}",
            self.extractor_revision,
            self.compiler_commit,
            self.semantics.join("\n")
        )
    }
}
pub(super) fn get() -> &'static Profile {
    static PROFILE: OnceLock<Profile> = OnceLock::new();
    PROFILE.get_or_init(|| {
        let p: Profile = serde_json::from_str(include_str!("charon-profile.json"))
            .expect("checked-in Charon profile must decode");
        assert_eq!(p.schema, 1, "unsupported Charon profile schema");
        p
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use sha2::{Digest, Sha256};
    #[test]
    fn charon_profile_pins_semantic_identity_and_matches_dependency_pin() {
        let p = get();
        assert_eq!(
            format!("{:x}", Sha256::digest(p.semantic_identity().as_bytes())),
            "674c3be0c2379700f835bf5408a6fa6a9496df4d590f42420b4a3f00f07b7611"
        );
        assert!(
            include_str!("../../../Cargo.toml")
                .contains(&format!("rev = \"{}\"", p.extractor_revision))
        );
        assert_eq!(
            p.semantics.len(),
            p.semantics
                .iter()
                .collect::<std::collections::BTreeSet<_>>()
                .len()
        );
    }
}
