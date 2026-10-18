//! Portable project locks. A lock and the artifacts it pins name a project's
//! own files by a label for the root they lie under (`$unit`, `$project`)
//! rather than by the absolute path of the checkout that prepared them, so a
//! lock committed on one machine reads the same on a fresh clone at another
//! path, and preparing it again from another checkout changes nothing.

use std::path::Path;

/// Absolute roots and the labels that stand for them in recorded text.
#[derive(Clone, Debug)]
pub(crate) struct PathLabels {
    /// Longest root first, so a root nested in another is replaced before
    /// the root containing it.
    roots: Vec<(&'static str, String)>,
}

impl PathLabels {
    /// Labels each of `roots`, absolute. A root must be a plain path, which
    /// JSON spells without escapes, so the text replacement is exact.
    pub(crate) fn new(roots: &[(&'static str, &Path)]) -> Result<Self, String> {
        let mut labelled = Vec::with_capacity(roots.len());
        for (label, root) in roots {
            debug_assert!(label.starts_with('$'));
            let text = root.to_string_lossy().trim_end_matches('/').to_string();
            if !root.is_absolute()
                || text.is_empty()
                || !text.bytes().all(|byte| {
                    byte.is_ascii_alphanumeric() || matches!(byte, b'/' | b'.' | b'_' | b'-' | b'+')
                })
            {
                return Err(format!(
                    "`{}` must be a plain absolute path to be recorded portably in a project lock",
                    root.display()
                ));
            }
            labelled.push((*label, text));
        }
        // A stable sort keeps the given order between equal roots, so the
        // first label given wins for a root named twice.
        labelled.sort_by_key(|(_, root)| std::cmp::Reverse(root.len()));
        Ok(Self { roots: labelled })
    }

    /// Replaces each JSON string that is a root, or starts with one followed
    /// by `/`, with the root's label.
    pub(crate) fn to_portable(&self, text: &str) -> String {
        let mut text = text.to_string();
        for (label, root) in &self.roots {
            text = text
                .replace(&format!("\"{root}/"), &format!("\"{label}/"))
                .replace(&format!("\"{root}\""), &format!("\"{label}\""));
        }
        text
    }

    /// Replaces each JSON string that is a label, or starts with one followed
    /// by `/`, with the label's root. A label this set does not name stays.
    pub(crate) fn to_absolute(&self, text: &str) -> String {
        let mut text = text.to_string();
        for (label, root) in &self.roots {
            text = text
                .replace(&format!("\"{label}/"), &format!("\"{root}/"))
                .replace(&format!("\"{label}\""), &format!("\"{root}\""));
        }
        text
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn labels_replace_whole_roots_and_nested_roots_first() {
        let labels = PathLabels::new(&[
            ("$project", Path::new("/work/project")),
            ("$unit", Path::new("/work/project/vendor/lib")),
        ])
        .unwrap();
        let text = r#"["/work/project", "/work/project/a.h", "/work/project/vendor/lib/b.h", "/work/projectile/c.h", "-I/work/project/x"]"#;
        let portable = labels.to_portable(text);
        assert_eq!(
            portable,
            r#"["$project", "$project/a.h", "$unit/b.h", "/work/projectile/c.h", "-I/work/project/x"]"#
        );
        let moved = PathLabels::new(&[
            ("$project", Path::new("/elsewhere/p")),
            ("$unit", Path::new("/elsewhere/p/vendor/lib")),
        ])
        .unwrap();
        assert_eq!(
            moved.to_absolute(&portable),
            r#"["/elsewhere/p", "/elsewhere/p/a.h", "/elsewhere/p/vendor/lib/b.h", "/work/projectile/c.h", "-I/work/project/x"]"#
        );
    }

    #[test]
    fn the_first_label_given_wins_for_a_root_named_twice() {
        let labels = PathLabels::new(&[
            ("$unit", Path::new("/work/p")),
            ("$project", Path::new("/work/p")),
        ])
        .unwrap();
        assert_eq!(labels.to_portable(r#""/work/p/a.h""#), r#""$unit/a.h""#);
        assert_eq!(
            labels.to_absolute(r#"["$unit/a.h", "$project/b.h"]"#),
            r#"["/work/p/a.h", "/work/p/b.h"]"#
        );
    }

    #[test]
    fn a_root_json_would_escape_is_refused() {
        assert!(PathLabels::new(&[("$unit", Path::new("/work/my project"))]).is_err());
        assert!(PathLabels::new(&[("$unit", Path::new("relative"))]).is_err());
    }
}
