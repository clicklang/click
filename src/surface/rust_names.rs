//! The Rust spelling of the names the Rust importer gives items.
//!
//! The importer names an item at a path `quad::walk` by `__rust_q` and each
//! segment with its length, `__rust_q_I4_quad_I4_walk`, and an inherent
//! method by its module, then `_T` and its type's own name, then the method:
//! `__rust_q_I6_adler2_T29___rust_q_I6_adler2_I7_Adler32_I3_new`
//! ([`super::parser::rust_path_name`], [`super::parser::rust_inherent_method_name`]).
//! A sidecar writes the path, `adler2::Adler32::new`, and a diagnostic prints
//! it the same way. The encoding is self-delimiting, so decoding needs no
//! import; a name with a part the importer does not length-prefix (an
//! operator method's `_mul_assign_u32`) keeps the importer's spelling.

use std::borrow::Cow;

const PREFIX: &str = "__rust_q";

/// The path `name` stands for, `quad::walk`, when it is a whole importer
/// name; `None` for any other name.
pub fn rust_display_name(name: &str) -> Option<String> {
    let (path, rest) = decode(name)?;
    rest.is_empty().then_some(path)
}

/// Decodes the importer name at the start of `text`: its path and the text
/// after it.
fn decode(text: &str) -> Option<(String, &str)> {
    let mut rest = text.strip_prefix(PREFIX)?;
    let mut segments: Vec<String> = Vec::new();
    while let Some(tail) = rest.strip_prefix('_') {
        let (kind, tail) = match tail.as_bytes().first() {
            Some(b'I') => ('I', &tail[1..]),
            Some(b'T') => ('T', &tail[1..]),
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
        if kind == 'T' {
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

/// Whether the claim label `label` is the one `requested` names, as the
/// importer spells it or as its Rust path.
pub fn claim_label_matches(label: &str, requested: &str) -> bool {
    label == requested || (requested.contains("::") && display_rust_names(label) == requested)
}

#[cfg(test)]
mod tests {
    use super::*;

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
        // An operator method's suffix is not length-prefixed; the name keeps
        // the importer's spelling.
        assert_eq!(
            rust_display_name("__rust_q_I6_adler2_I4_algo_I5_U32X4_mul_assign_u32"),
            None
        );
        assert_eq!(rust_display_name("walk"), None);
        assert_eq!(rust_display_name("__rust_q_I9_short"), None);
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
