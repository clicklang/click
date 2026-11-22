//! The value of a C or Rust struct in a contract: a datatype of one
//! constructor, named for the struct, whose fields are the struct's in
//! declaration order. `*p` at `struct pair*` is `pair(p->x, p->y)`, and two
//! struct values are equal when every field is.
//!
//! The kernel's datatype keeps its fields' types, not their names, so the
//! names are recorded here when the parser forms the type, for printing a
//! value back: as `*p` when its fields are `p`'s own, else as a literal
//! the parser reads, `(struct pair){ .x = a, .y = b }` in C and
//! `crate_name::Pair { x: a, y: b }` in Rust.

use std::collections::BTreeMap;
use std::sync::Mutex;

struct StructValue {
    fields: Vec<String>,
    rust: bool,
}

/// Struct value types by name. Names are a function of the program's
/// struct declarations alone, so one table serves the whole process.
static STRUCT_VALUES: Mutex<BTreeMap<String, StructValue>> = Mutex::new(BTreeMap::new());

pub(in crate::surface) fn register(name: &str, fields: Vec<String>, rust: bool) {
    let mut values = STRUCT_VALUES.lock().expect("struct value types");
    if !values.contains_key(name) {
        values.insert(name.to_string(), StructValue { fields, rust });
    }
}

/// The field names of struct value type `name`, in its constructor's order,
/// when `name` is one.
pub(in crate::surface) fn field_names(name: &str) -> Option<Vec<String>> {
    STRUCT_VALUES
        .lock()
        .expect("struct value types")
        .get(name)
        .map(|value| value.fields.clone())
}

/// How a value of struct value type `name` is spelled from its fields'
/// spellings: `*p` when each field is `p->field` (or `p.field`) for one `p`,
/// with any `old(...)` or `at(...)` around them all outside it, else a
/// literal. `None` when `name` is no struct value type.
pub(in crate::surface) fn spell(name: &str, spelled_fields: &[String]) -> Option<String> {
    let (fields, rust) = {
        let values = STRUCT_VALUES.lock().expect("struct value types");
        let value = values.get(name)?;
        (value.fields.clone(), value.rust)
    };
    if fields.len() != spelled_fields.len() {
        return None;
    }
    if let Some(place) = common_place(&fields, spelled_fields) {
        return Some(place);
    }
    let display = crate::languages::rust::names::display_rust_names(name);
    let display = display.strip_prefix("struct ").unwrap_or(&display);
    Some(if rust {
        format!(
            "{display} {{ {} }}",
            fields
                .iter()
                .zip(spelled_fields)
                .map(|(field, value)| format!("{field}: {value}"))
                .collect::<Vec<_>>()
                .join(", ")
        )
    } else {
        format!(
            "(struct {display}){{ {} }}",
            fields
                .iter()
                .zip(spelled_fields)
                .map(|(field, value)| format!(".{field} = {value}"))
                .collect::<Vec<_>>()
                .join(", ")
        )
    })
}

/// `*p` (inside one shared `old(...)`, `exact(...)` or `at(point, ...)`)
/// when each spelled field is `p->field` or `p.field` in order.
fn common_place(fields: &[String], spelled_fields: &[String]) -> Option<String> {
    let wrapper = |spelled: &str| -> (String, String) {
        for prefix in ["old(", "exact("] {
            if let Some(inner) = spelled.strip_prefix(prefix)
                && let Some(inner) = inner.strip_suffix(')')
            {
                return (prefix.to_string(), inner.to_string());
            }
        }
        if let Some(rest) = spelled.strip_prefix("at(")
            && let Some(rest) = rest.strip_suffix(')')
            && let Some((point, inner)) = rest.split_once(", ")
        {
            return (format!("at({point}, "), inner.to_string());
        }
        (String::new(), spelled.to_string())
    };
    let mut common: Option<(String, String)> = None;
    for (field, spelled) in fields.iter().zip(spelled_fields) {
        let (wrap, inner) = wrapper(spelled);
        // An embedded struct's value is itself `*p->inner`.
        let inner = inner.strip_prefix('*').unwrap_or(&inner).to_string();
        let base = inner
            .strip_suffix(field.as_str())
            .and_then(|base| base.strip_suffix("->").or_else(|| base.strip_suffix('.')))?
            .to_string();
        if base.is_empty() {
            return None;
        }
        match &common {
            None => common = Some((wrap, base)),
            Some(known) if *known == (wrap.clone(), base.clone()) => {}
            Some(_) => return None,
        }
    }
    let (wrap, base) = common?;
    let place = format!("*{}", parenthesized(&base));
    Some(if wrap.is_empty() {
        place
    } else {
        format!("{wrap}{place})")
    })
}

/// `base` as an operand of a prefix `*`: a name or a field place stays as it
/// is, anything else is parenthesized.
fn parenthesized(base: &str) -> String {
    if base
        .chars()
        .all(|c| c.is_ascii_alphanumeric() || matches!(c, '_' | '.' | ':' | '>' | '-'))
        && !base.starts_with('-')
    {
        base.to_string()
    } else {
        format!("({base})")
    }
}
