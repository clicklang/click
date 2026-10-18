//! A Rust sidecar's generic crate traits, written by rewriting the sidecar's
//! tokens before its trait object state is, as the object state is.
//!
//! A block naming a trait's type parameters, `trait traits::Scale<T> { ... }`,
//! states every instance's interface; a block naming an instance's scalar
//! types, `trait traits::Scale<i32> { ... }`, adds clauses at that instance.
//! Each instance the import declares, or that has a block of its own, is
//! written out as one instance block: the generic block with the instance's
//! types for its parameters, each method's clauses followed by the instance
//! block's for that method. The instance blocks then read as any trait
//! block, their object state included.
//!
//! Every other token is kept, with its position.

use super::rust_trait_objects::{Spanned, error_at, is_ident, matching};
use super::*;

/// The scalar types a generic crate trait's instance is taken at, as the
/// importer takes them.
pub(super) const INSTANCE_SCALARS: [&str; 6] = ["i32", "u8", "u16", "u32", "usize", "bool"];

/// A top-level `trait p::Name<...> { ... }` block.
struct Block {
    /// The index of its `trait` token, and the index after its closing brace.
    range: std::ops::Range<usize>,
    /// The index of its `<`.
    arguments_open: usize,
    arguments: Vec<String>,
}

/// Writes out each instance of the sidecar's generic crate traits, by the
/// trait's importer name, at the instances the import declares.
pub(super) fn expand_generic_traits(
    tokens: Vec<Token>,
    positions: Vec<SourcePosition>,
    instances: &BTreeMap<String, BTreeSet<Vec<String>>>,
) -> Result<(Vec<Token>, Vec<SourcePosition>), ClickError> {
    let mut source: Vec<Spanned> = Vec::with_capacity(tokens.len());
    // `>>` closing a type argument list and the type parameters around it,
    // `<B: traits::Bag<i32>>(`, is two `>`.
    for (index, (token, position)) in tokens.iter().zip(positions).enumerate() {
        if *token == Token::ShiftRight
            && matches!(
                index.checked_sub(1).map(|at| &tokens[at]),
                Some(Token::Ident(_))
            )
            && tokens.get(index + 1) == Some(&Token::LParen)
        {
            source.push((Token::GreaterThan, position.clone()));
            source.push((Token::GreaterThan, position));
            continue;
        }
        source.push((token.clone(), position));
    }
    let mut generic = BTreeMap::<String, Block>::new();
    let mut written = BTreeMap::<(String, Vec<String>), Block>::new();
    let mut depth = 0i32;
    let mut index = 0;
    while index < source.len() {
        if depth == 0
            && is_ident(source.get(index), "trait")
            && let Some(block) = block_at(&source, index)?
        {
            let (segments, _) = trait_path(&source, index + 1);
            let trait_name = crate::languages::rust::names::path_name(
                &segments.iter().map(String::as_str).collect::<Vec<_>>(),
            );
            let position = &source[index].1;
            let scalars = block
                .arguments
                .iter()
                .filter(|argument| INSTANCE_SCALARS.contains(&argument.as_str()))
                .count();
            index = block.range.end;
            if scalars == block.arguments.len() {
                if written
                    .insert((trait_name, block.arguments.clone()), block)
                    .is_some()
                {
                    return Err(error_at(
                        position,
                        "a crate trait's instance has two `trait` blocks",
                    ));
                }
            } else if scalars == 0
                && block.arguments.iter().collect::<BTreeSet<_>>().len() == block.arguments.len()
            {
                if generic.insert(trait_name, block).is_some() {
                    return Err(error_at(
                        position,
                        "a generic crate trait has two `trait` blocks",
                    ));
                }
            } else {
                return Err(error_at(
                    position,
                    "a crate trait's `trait` block names its type parameters, `trait \
                     crate_name::Scale<T>`, or an instance's scalar types, `trait \
                     crate_name::Scale<i32>`",
                ));
            }
            continue;
        }
        match source[index].0 {
            Token::LBrace | Token::LParen | Token::LBracket => depth += 1,
            Token::RBrace | Token::RParen | Token::RBracket => depth -= 1,
            _ => {}
        }
        index += 1;
    }
    if generic.is_empty() && written.is_empty() {
        let (tokens, positions) = source.into_iter().unzip();
        return Ok((tokens, positions));
    }
    let mut targets = BTreeSet::new();
    for (trait_name, block) in &generic {
        for arguments in instances.get(trait_name).into_iter().flatten() {
            if arguments.len() == block.arguments.len() {
                targets.insert((trait_name.clone(), arguments.clone()));
            }
        }
    }
    targets.extend(written.keys().cloned());
    // The instance blocks take the place of the first block removed.
    let removed = generic
        .values()
        .chain(written.values())
        .map(|block| block.range.clone())
        .collect::<Vec<_>>();
    let first = removed.iter().map(|range| range.start).min().unwrap_or(0);
    let mut expanded = Vec::new();
    for (trait_name, arguments) in &targets {
        let generic_block = generic.get(trait_name);
        let instance_block = written.get(&(trait_name.clone(), arguments.clone()));
        expanded.extend(instance(&source, generic_block, instance_block, arguments)?);
    }
    let mut output = Vec::with_capacity(source.len() + expanded.len());
    let mut expanded = Some(expanded);
    for (index, spanned) in source.into_iter().enumerate() {
        if index == first
            && let Some(expanded) = expanded.take()
        {
            output.extend(expanded);
        }
        if removed.iter().any(|range| range.contains(&index)) {
            continue;
        }
        output.push(spanned);
    }
    let (tokens, positions) = output.into_iter().unzip();
    Ok((tokens, positions))
}

/// The trait's path after `trait`, and the index after it.
fn trait_path(source: &[Spanned], start: usize) -> (Vec<String>, usize) {
    let mut segments = Vec::new();
    let mut index = start;
    while let Some((Token::Ident(segment), _)) = source.get(index) {
        segments.push(segment.clone());
        index += 1;
        if source.get(index).map(|(token, _)| token) != Some(&Token::ColonColon) {
            break;
        }
        index += 1;
    }
    (segments, index)
}

/// The `trait` block at `start` when its path names type arguments.
fn block_at(source: &[Spanned], start: usize) -> Result<Option<Block>, ClickError> {
    let (segments, open) = trait_path(source, start + 1);
    if segments.len() < 2 || source.get(open).map(|(token, _)| token) != Some(&Token::LessThan) {
        return Ok(None);
    }
    let position = &source[start].1;
    let shape = || {
        error_at(
            position,
            "a `trait` block's type arguments are names, `<T>`",
        )
    };
    let close = matching(source, open).ok_or_else(shape)?;
    let mut arguments = Vec::new();
    for (at, (token, _)) in source[open + 1..close].iter().enumerate() {
        match (at % 2, token) {
            (0, Token::Ident(argument)) => arguments.push(argument.clone()),
            (1, Token::Comma) => {}
            _ => return Err(shape()),
        }
    }
    if arguments.is_empty() || source.get(close + 1).map(|(token, _)| token) != Some(&Token::LBrace)
    {
        return Err(shape());
    }
    let end = matching(source, close + 1)
        .ok_or_else(|| error_at(position, "unterminated `trait` block"))?
        + 1;
    Ok(Some(Block {
        range: start..end,
        arguments_open: open,
        arguments,
    }))
}

/// The items of a `trait` block, each with the name it declares: a `fn`
/// interface's method, or a `function`'s name, and its tokens.
fn items(source: &[Spanned], block: &Block) -> Vec<(String, Vec<Spanned>)> {
    let open = (block.arguments_open..block.range.end)
        .find(|&index| source[index].0 == Token::LBrace)
        .expect("a `trait` block");
    let mut items = Vec::new();
    let mut index = open + 1;
    while index + 1 < block.range.end {
        let start = index;
        let name = match source.get(index + 1) {
            Some((Token::Ident(name), _)) => name.clone(),
            _ => String::new(),
        };
        // A `function` declaration ends at its `;`; a `fn` interface at its
        // clause block's closing brace.
        let mut depth = 0usize;
        let mut end = None;
        while index < block.range.end - 1 {
            match source[index].0 {
                Token::LParen | Token::LessThan => depth += 1,
                Token::RParen | Token::GreaterThan => depth = depth.saturating_sub(1),
                Token::Semicolon if depth == 0 => {
                    end = Some(index);
                    break;
                }
                Token::LBrace if depth == 0 => {
                    end = matching(source, index);
                    break;
                }
                _ => {}
            }
            index += 1;
        }
        let end = end.unwrap_or(block.range.end - 2);
        items.push((name, source[start..=end].to_vec()));
        index = end + 1;
    }
    items
}

/// The instance block of a trait at `arguments`: the generic block's items
/// at those types, each `fn`'s clauses then the instance block's for it,
/// and the instance block's other items.
fn instance(
    source: &[Spanned],
    generic: Option<&Block>,
    written: Option<&Block>,
    arguments: &[String],
) -> Result<Vec<Spanned>, ClickError> {
    let header = generic.or(written).expect("an instance has a block");
    let position = source[header.range.start].1.clone();
    let mut tokens = source[header.range.start..header.arguments_open].to_vec();
    tokens.push((Token::LessThan, position.clone()));
    for (at, argument) in arguments.iter().enumerate() {
        if at > 0 {
            tokens.push((Token::Comma, position.clone()));
        }
        tokens.push((Token::Ident(argument.clone()), position.clone()));
    }
    tokens.push((Token::GreaterThan, position.clone()));
    tokens.push((Token::LBrace, position.clone()));
    let mut body = generic
        .map(|block| {
            let substitution = block
                .arguments
                .iter()
                .zip(arguments)
                .collect::<BTreeMap<_, _>>();
            items(source, block)
                .into_iter()
                .map(|(name, item)| {
                    let item = item
                        .into_iter()
                        .map(|(token, position)| match token {
                            Token::Ident(word) if substitution.contains_key(&word) => {
                                (Token::Ident(substitution[&word].clone()), position)
                            }
                            token => (token, position),
                        })
                        .collect::<Vec<_>>();
                    (name, item)
                })
                .collect::<Vec<_>>()
        })
        .unwrap_or_default();
    for (name, item) in written
        .map(|block| items(source, block))
        .unwrap_or_default()
    {
        let shared = is_ident(item.first(), "fn")
            .then(|| {
                body.iter_mut().find(|(generic, generic_item)| {
                    *generic == name && is_ident(generic_item.first(), "fn")
                })
            })
            .flatten();
        match shared {
            Some((_, generic_item)) => {
                let open = item
                    .iter()
                    .position(|(token, _)| *token == Token::LBrace)
                    .ok_or_else(|| {
                        error_at(&item[0].1, "a trait method's interface has clauses")
                    })?;
                let close = generic_item
                    .iter()
                    .rposition(|(token, _)| *token == Token::RBrace)
                    .ok_or_else(|| {
                        error_at(&item[0].1, "a trait method's interface has clauses")
                    })?;
                let own = item[open + 1..item.len() - 1].to_vec();
                generic_item.splice(close..close, own);
            }
            None => body.push((name, item)),
        }
    }
    for (_, item) in body {
        tokens.extend(item);
    }
    tokens.push((Token::RBrace, position));
    Ok(tokens)
}
