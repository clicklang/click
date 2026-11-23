//! The type resources of a Rust sidecar's box and option-of-box places,
//! written into its tokens after its derived authority.
//!
//! A type resource is the resource a value of a type holds: the library
//! declares `Box<T>`'s, `type Box<T> { owns allocation(self, sizeof(T)); owns
//! *self; }`, and an option of a box, stored as the box's address or null,
//! holds the box's when it is `Some`. Each is an ordinary resource,
//! written out at each struct a sidecar boxes, `Box<boxed::Cell>` and
//! `Option<Box<boxed::Cell>>` named by the generic resource instance names:
//!
//! - holding a struct field that holds a box or an option of one, `owns
//!   self.slot;`, holds its value's type resource too, `owns
//!   Option<Box<box_fields::Cell>>(self.slot);`, with the clause's own
//!   access;
//! - a sidecar names a type resource as that type applied to the value,
//!   `unfold(Option<Box<box_fields::Cell>>(self.slot))`;
//! - each one named is defined: `Box<R>` by the library's clauses at `R`,
//!   and `Option<Box<R>>` as `if p != 0 { owns Box<R>(p); }`.
//!
//! Every other token is kept, with its position.

use super::rust_reference_authority::{inherent_impl_at, path_type_name, type_resource_clauses};
use super::rust_trait_objects::{Spanned, is_ident, matching};
use super::*;
use crate::languages::interface::RecordLayout;

/// The type resource of a box of the struct `record`, or of an option of
/// one: its resource name.
fn resource_name(record: &str, optional: bool) -> String {
    let boxed = rust_generic_resources::instance_name("Box", &[record.to_string()]);
    if optional {
        rust_generic_resources::instance_name("Option", &[boxed])
    } else {
        boxed
    }
}

/// A written type resource at the cursor, `Box<R>(` or `Option<Box<R>>(`:
/// the struct `R`, whether it is an option, and the index of its `(`.
fn written_type_resource(
    source: &[Spanned],
    index: usize,
    struct_layouts: &BTreeMap<String, RecordLayout>,
) -> Option<(String, bool, usize)> {
    let token = |at: usize| source.get(at).map(|(token, _)| token);
    let (optional, mut at) = if is_ident(source.get(index), "Option")
        && token(index + 1) == Some(&Token::LessThan)
        && is_ident(source.get(index + 2), "Box")
        && token(index + 3) == Some(&Token::LessThan)
    {
        (true, index + 4)
    } else if is_ident(source.get(index), "Box") && token(index + 1) == Some(&Token::LessThan) {
        (false, index + 2)
    } else {
        return None;
    };
    let start = at;
    while matches!(token(at), Some(Token::Ident(_) | Token::ColonColon)) {
        at += 1;
    }
    let path = source[start..at]
        .iter()
        .map(|(token, _)| token.clone())
        .collect::<Vec<_>>();
    let record = path_type_name(&path).filter(|name| struct_layouts.contains_key(name))?;
    // `>` once for a box, twice (or one `>>`) for an option of one.
    match (optional, token(at)) {
        (false, Some(Token::GreaterThan)) => at += 1,
        (true, Some(Token::ShiftRight)) => at += 1,
        (true, Some(Token::GreaterThan)) if token(at + 1) == Some(&Token::GreaterThan) => at += 2,
        _ => return None,
    }
    (token(at) == Some(&Token::LParen)).then_some((record, optional, at))
}

/// `Option<Box<R>>::None` or `Option<Box<R>>::Some` at the cursor: whether
/// it is `Some`, and the index of the variant's name. An option of a box is
/// the box's address, or null, so `None` is `0` and `Some(b)` is `(b)`.
fn option_box_variant(source: &[Spanned], index: usize) -> Option<(bool, usize)> {
    let token = |at: usize| source.get(at).map(|(token, _)| token);
    if !(is_ident(source.get(index), "Option")
        && token(index + 1) == Some(&Token::LessThan)
        && is_ident(source.get(index + 2), "Box")
        && token(index + 3) == Some(&Token::LessThan))
    {
        return None;
    }
    // The boxed type may have arguments of its own, `Node<T>`: read to the
    // `>` that closes `Option`.
    let mut at = index + 4;
    let mut depth = 2usize;
    while depth > 0 {
        match token(at)? {
            Token::LessThan => depth += 1,
            Token::GreaterThan => depth -= 1,
            Token::ShiftRight => depth = depth.checked_sub(2)?,
            Token::Ident(_) | Token::ColonColon | Token::Comma => {}
            _ => return None,
        }
        at += 1;
    }
    if token(at) != Some(&Token::ColonColon) {
        return None;
    }
    let some = match token(at + 1) {
        Some(Token::Ident(variant)) if variant == "None" => false,
        Some(Token::Ident(variant)) if variant == "Some" => {
            if token(at + 2) != Some(&Token::LParen) {
                return None;
            }
            true
        }
        _ => return None,
    };
    Some((some, at + 1))
}

/// Whether the struct `record` holds no box of its own: its box's type
/// resource is then its allocation and its bytes. A struct that holds a box,
/// a list's node, needs its own type resource, which is not derived yet.
fn flat_record(record: &str, struct_layouts: &BTreeMap<String, RecordLayout>) -> bool {
    struct_layouts.get(record).is_some_and(|layout| {
        layout
            .fields()
            .values()
            .all(|field| field.boxed().is_none())
    })
}

/// `access self.field;` at the cursor, where the receiver's field holds a
/// box or an option of one: the access, the field, the box's struct and
/// whether it is an option, and the index of the `;`.
fn owned_box_field(
    source: &[Spanned],
    index: usize,
    receiver: Option<&RecordLayout>,
    struct_layouts: &BTreeMap<String, RecordLayout>,
) -> Option<(String, String, String, bool, usize)> {
    let Some((Token::Ident(access), _)) = source.get(index) else {
        return None;
    };
    if !matches!(access.as_str(), "owns" | "views" | "consumes" | "produces") {
        return None;
    }
    let (
        Some((Token::Ident(base), _)),
        Some((Token::Dot, _)),
        Some((Token::Ident(field), _)),
        Some((Token::Semicolon, _)),
    ) = (
        source.get(index + 1),
        source.get(index + 2),
        source.get(index + 3),
        source.get(index + 4),
    )
    else {
        return None;
    };
    if base != "self" {
        return None;
    }
    let boxed = receiver?.field(field)?.boxed()?;
    if !flat_record(&boxed.record, struct_layouts) {
        return None;
    }
    Some((
        access.clone(),
        field.clone(),
        boxed.record.clone(),
        boxed.optional,
        index + 4,
    ))
}

pub(super) fn write_type_resources(
    tokens: Vec<Token>,
    positions: Vec<SourcePosition>,
    written: BTreeSet<usize>,
    struct_layouts: &BTreeMap<String, RecordLayout>,
) -> Result<(Vec<Token>, Vec<SourcePosition>, BTreeSet<usize>), ClickError> {
    let source: Vec<Spanned> = tokens.into_iter().zip(positions).collect();
    let mut output: Vec<Spanned> = Vec::with_capacity(source.len());
    let mut moved = BTreeSet::new();
    // The type resources named, by struct: whether the box's and whether the
    // option's is named.
    let mut named = BTreeMap::<String, (bool, bool)>::new();
    let mut note = |record: &str, optional: bool| {
        let entry = named.entry(record.to_string()).or_default();
        entry.0 = true;
        entry.1 |= optional;
    };
    // The receiver of the inherent `impl` block the cursor is in, until its
    // closing brace.
    let mut receiver: Option<(String, usize)> = None;
    let mut index = 0;
    while index < source.len() {
        crate::instrumentation::record_deterministic_work(1);
        if receiver.as_ref().is_some_and(|(_, close)| index > *close) {
            receiver = None;
        }
        if inherent_impl_at(&source, index)
            && let Some(open) = (index..source.len()).find(|&at| source[at].0 == Token::LBrace)
            && let Some(close) = matching(&source, open)
        {
            // Finding the block's braces reads its header and its body once.
            crate::instrumentation::record_deterministic_work(close - index);
            let path = source[index + 1..open]
                .iter()
                .map(|(token, _)| token.clone())
                .collect::<Vec<_>>();
            receiver = path_type_name(&path).map(|name| (name, close));
        }
        if let Some((some, variant)) = option_box_variant(&source, index) {
            if !some {
                output.push((Token::Number(0), source[index].1.clone()));
            }
            // `Some`'s parenthesized payload is kept.
            index = variant + 1;
            continue;
        }
        if let Some((record, optional, open)) =
            written_type_resource(&source, index, struct_layouts)
        {
            note(&record, optional);
            let position = source[index].1.clone();
            output.push((Token::Ident(resource_name(&record, optional)), position));
            index = open;
            continue;
        }
        if let Some((access, field, record, optional, semicolon)) = owned_box_field(
            &source,
            index,
            receiver
                .as_ref()
                .and_then(|(name, _)| struct_layouts.get(name)),
            struct_layouts,
        ) {
            for (at, token) in source.iter().enumerate().take(semicolon + 1).skip(index) {
                if written.contains(&at) {
                    moved.insert(output.len());
                }
                output.push(token.clone());
            }
            note(&record, optional);
            let position = source[index].1.clone();
            // The type resource is the value's, so a place owned across the
            // call gives up its entry value's and gets its exit value's.
            let accesses = if access == "owns" {
                vec!["consumes".to_string(), "produces".to_string()]
            } else {
                vec![access]
            };
            for access in accesses {
                for token in [
                    Token::Ident(access.clone()),
                    Token::Ident(resource_name(&record, optional)),
                    Token::LParen,
                    Token::Ident("self".into()),
                    Token::Dot,
                    Token::Ident(field.clone()),
                    Token::RParen,
                    Token::Semicolon,
                ] {
                    output.push((token, position.clone()));
                }
            }
            index = semicolon + 1;
            continue;
        }
        if written.contains(&index) {
            moved.insert(output.len());
        }
        output.push(source[index].clone());
        index += 1;
    }
    // Each type resource named, defined at its struct.
    let Some(position) = output.last().map(|(_, position)| position.clone()) else {
        return Ok((Vec::new(), Vec::new(), moved));
    };
    let text = |text: String| -> Result<Vec<Token>, ClickError> {
        Ok(tokenizer::tokenize(&text, None)?.0)
    };
    for (record, (_, optional)) in named {
        let spelled = crate::languages::rust::names::display_rust_names(&record);
        let record_tokens = text(spelled.to_string())?;
        let clauses = type_resource_clauses(
            "Box",
            std::slice::from_ref(&record_tokens),
            &[Token::Ident("p".into())],
        )
        .ok_or_else(|| ClickError::new("the Click library declares no `type Box<T>`"))?;
        let boxed = resource_name(&record, false);
        let mut definition = text(format!("resource {boxed}(p: *mut {spelled}) {{"))?;
        for clause in clauses {
            definition.extend(clause);
            definition.push(Token::Semicolon);
        }
        definition.push(Token::RBrace);
        if optional {
            definition.extend(text(format!(
                "resource {}(p: *mut {spelled}) {{ if p != 0 {{ owns {boxed}(p); }} }}",
                resource_name(&record, true)
            ))?);
        }
        output.extend(
            definition
                .into_iter()
                .map(|token| (token, position.clone())),
        );
    }
    let (tokens, positions) = output.into_iter().unzip();
    Ok((tokens, positions, moved))
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/surface/parser/rust_type_resources/tests.rs");
}
