//! A Rust sidecar's generic resources, written out at each type argument
//! list the sidecar names them at, by rewriting the sidecar's tokens as its
//! generic functions are.
//!
//! A generic resource, `resource cell<T: Copy>(c: *mut cells::Cell<T>) {
//! ... }`, describes memory for every type `T`. Each use names its type
//! arguments, `cell<T>(cell)` in a generic function's contract and
//! `cell<i32>(cell)` in its instance at `i32`, and each distinct list is a
//! resource of its own, `cell` with the arguments encoded in its name, whose
//! parameters and body are the generic one's at those types. Writing it out
//! gives each instance its struct layouts, as a generic function's instances
//! have theirs: `cells::Cell<i32>` is laid out as its fields are. An abstract
//! argument stays abstract in its instance, which binds it.
//!
//! Every other token is kept, with its position.

use super::rust_generic_traits::INSTANCE_SCALARS;
use super::rust_trait_objects::{Spanned, error_at, is_ident, matching};
use super::*;

/// A top-level generic `resource` block.
struct Block {
    /// The index of its `resource` keyword.
    start: usize,
    /// The index after its body.
    end: usize,
    /// The indices of its type parameter list's `<` and `>`.
    parameters: (usize, usize),
    /// Its type parameters' names.
    names: Vec<String>,
}

/// The name a generic resource's instance at `arguments` is written out as.
fn instance_name(resource: &str, arguments: &[String]) -> String {
    let mut name = resource.to_string();
    for argument in arguments {
        crate::languages::rust::names::push_type_argument(&mut name, argument);
    }
    name
}

/// Writes out each generic resource at its own type parameters and at each
/// type argument list a use names, in place of its block, and renames each
/// use, `cell<i32>(...)`, to the instance it names. `written`, the indices
/// of the written function instances' tokens, is returned at their new
/// indices.
#[allow(clippy::type_complexity)]
pub(super) fn expand_generic_resources(
    tokens: Vec<Token>,
    positions: Vec<SourcePosition>,
    written: BTreeSet<usize>,
) -> Result<(Vec<Token>, Vec<SourcePosition>, BTreeSet<usize>), ClickError> {
    let source: Vec<Spanned> = tokens.into_iter().zip(positions).collect();
    let mut blocks = BTreeMap::<String, Block>::new();
    let mut depth = 0i32;
    for index in 0..source.len() {
        if depth == 0
            && is_ident(source.get(index), "resource")
            && let Some((name, block)) = block_at(&source, index)?
            && blocks.insert(name.clone(), block).is_some()
        {
            return Err(error_at(
                &source[index].1,
                format!("duplicate generic resource `{name}`"),
            ));
        }
        match source[index].0 {
            Token::LBrace | Token::LParen | Token::LBracket => depth += 1,
            Token::RBrace | Token::RParen | Token::RBracket => depth -= 1,
            _ => {}
        }
    }
    if blocks.is_empty() {
        let (tokens, positions) = source.into_iter().unzip();
        return Ok((tokens, positions, written));
    }
    // Each generic resource is written at its own parameters, which checks
    // its body once for every type, and at each list a use names.
    let mut instances = blocks
        .iter()
        .map(|(name, block)| (name.clone(), BTreeSet::from([block.names.clone()])))
        .collect::<BTreeMap<_, _>>();
    let inside_block = |index: usize| {
        blocks
            .values()
            .any(|block| block.start <= index && index < block.end)
    };
    let mut uses = BTreeMap::<usize, (String, Vec<String>, usize)>::new();
    for index in 0..source.len() {
        let Some((name, arguments, after)) = use_at(&source, index, &blocks) else {
            continue;
        };
        if blocks[&name].names.len() != arguments.len() {
            return Err(error_at(
                &source[index].1,
                format!(
                    "the generic resource `{name}` takes {} type arguments",
                    blocks[&name].names.len()
                ),
            ));
        }
        if !inside_block(index) {
            instances
                .get_mut(&name)
                .expect("a use names a generic resource")
                .insert(arguments.clone());
        }
        uses.insert(index, (name, arguments, after));
    }
    // A body's use of a generic resource is at the instance's arguments,
    // so each instance written may need another, until none is new.
    let mut pending = instances
        .iter()
        .flat_map(|(name, lists)| lists.iter().map(move |list| (name.clone(), list.clone())))
        .collect::<Vec<_>>();
    while let Some((name, arguments)) = pending.pop() {
        let block = &blocks[&name];
        let substitution = block
            .names
            .iter()
            .zip(&arguments)
            .collect::<BTreeMap<_, _>>();
        for (_, (used, used_arguments, _)) in uses.range(block.start..block.end) {
            let used_arguments = used_arguments
                .iter()
                .map(|argument| substitution.get(argument).map_or(argument, |a| a).clone())
                .collect::<Vec<_>>();
            if instances
                .get_mut(used)
                .expect("a use names a generic resource")
                .insert(used_arguments.clone())
            {
                pending.push((used.clone(), used_arguments));
            }
        }
    }
    let mut output = Vec::with_capacity(source.len());
    let mut moved = BTreeSet::new();
    let mut index = 0;
    while index < source.len() {
        if written.contains(&index) {
            moved.insert(output.len());
        }
        if let Some((name, block)) = blocks.iter().find(|(_, block)| block.start == index) {
            for arguments in &instances[name] {
                output.extend(instance(&source, block, name, arguments, &uses));
            }
            index = block.end;
            continue;
        }
        if let Some((name, arguments, after)) = uses.get(&index) {
            output.push((
                Token::Ident(instance_name(name, arguments)),
                source[index].1.clone(),
            ));
            index = *after;
            continue;
        }
        output.push(source[index].clone());
        index += 1;
    }
    let (tokens, positions) = output.into_iter().unzip();
    Ok((tokens, positions, moved))
}

/// The generic `resource` block at `start`, with its name, when it has a
/// type parameter list of abstract types, `<T>` or `<T: Copy>`.
fn block_at(source: &[Spanned], start: usize) -> Result<Option<(String, Block)>, ClickError> {
    let Some((Token::Ident(name), _)) = source.get(start + 1) else {
        return Ok(None);
    };
    let open = start + 2;
    if source.get(open).map(|(token, _)| token) != Some(&Token::LessThan) {
        return Ok(None);
    }
    let position = &source[start].1;
    let close = matching(source, open)
        .ok_or_else(|| error_at(position, "unterminated resource type parameters"))?;
    let names = abstract_parameters(source, open, close).ok_or_else(|| {
        error_at(
            position,
            "a generic resource's type parameters are abstract types, `<T>` or `<T: Copy>`",
        )
    })?;
    if source.get(close + 1).map(|(token, _)| token) != Some(&Token::LParen) {
        return Err(error_at(
            position,
            "expected `(` after a resource's type parameters",
        ));
    }
    let unterminated = || error_at(position, "unterminated `resource` block");
    let parameters_end = matching(source, close + 1).ok_or_else(unterminated)?;
    if source.get(parameters_end + 1).map(|(token, _)| token) != Some(&Token::LBrace) {
        return Err(error_at(position, "expected a generic resource's body"));
    }
    let end = matching(source, parameters_end + 1).ok_or_else(unterminated)? + 1;
    Ok(Some((
        name.clone(),
        Block {
            start,
            end,
            parameters: (open, close),
            names,
        },
    )))
}

/// The names of the type parameters between `<` at `open` and `>` at
/// `close`, when each is abstract: a name bound by `Copy` and `Clone` only.
fn abstract_parameters(source: &[Spanned], open: usize, close: usize) -> Option<Vec<String>> {
    let mut names = Vec::new();
    let mut at = open + 1;
    while at < close {
        let Some((Token::Ident(name), _)) = source.get(at) else {
            return None;
        };
        if INSTANCE_SCALARS.contains(&name.as_str()) {
            return None;
        }
        names.push(name.clone());
        at += 1;
        if source[at].0 == Token::Colon {
            at += 1;
            while at < close && source[at].0 != Token::Comma {
                if !is_ident(source.get(at), "Copy")
                    && !is_ident(source.get(at), "Clone")
                    && source[at].0 != Token::Plus
                {
                    return None;
                }
                at += 1;
            }
        }
        if at < close && source[at].0 == Token::Comma {
            at += 1;
        }
    }
    Some(names)
}

/// A use of a generic resource at `index`, `cell<i32>(`, with the resource,
/// its type arguments and the index after its `>`.
fn use_at(
    source: &[Spanned],
    index: usize,
    blocks: &BTreeMap<String, Block>,
) -> Option<(String, Vec<String>, usize)> {
    let (Token::Ident(name), _) = source.get(index)? else {
        return None;
    };
    let block = blocks.get(name)?;
    if index == block.start + 1 {
        return None;
    }
    if source.get(index + 1)?.0 != Token::LessThan {
        return None;
    }
    let close = matching(source, index + 1)?;
    if source.get(close + 1)?.0 != Token::LParen {
        return None;
    }
    let mut arguments = Vec::new();
    let mut at = index + 2;
    while at < close {
        let (Token::Ident(argument), _) = &source[at] else {
            return None;
        };
        arguments.push(argument.clone());
        at += 1;
        if at < close && source[at].0 == Token::Comma {
            at += 1;
        }
    }
    Some((name.clone(), arguments, close + 1))
}

/// The generic resource `block`, `name`, written out at `arguments`: its
/// parameters and body with each type parameter read as its argument, and
/// its abstract arguments bound, `resource cell_A1_T<T>(...)`.
fn instance(
    source: &[Spanned],
    block: &Block,
    name: &str,
    arguments: &[String],
    uses: &BTreeMap<usize, (String, Vec<String>, usize)>,
) -> Vec<Spanned> {
    let position = source[block.start].1.clone();
    let substitution = block
        .names
        .iter()
        .zip(arguments)
        .collect::<BTreeMap<_, _>>();
    let substituted = |word: &String| -> String {
        substitution
            .get(word)
            .map_or(word, |argument| argument)
            .clone()
    };
    let mut tokens = vec![
        source[block.start].clone(),
        (
            Token::Ident(instance_name(name, arguments)),
            position.clone(),
        ),
    ];
    let abstract_arguments = arguments
        .iter()
        .filter(|argument| !INSTANCE_SCALARS.contains(&argument.as_str()))
        .collect::<BTreeSet<_>>();
    if !abstract_arguments.is_empty() {
        tokens.push((Token::LessThan, position.clone()));
        for (at, argument) in abstract_arguments.into_iter().enumerate() {
            if at > 0 {
                tokens.push((Token::Comma, position.clone()));
            }
            tokens.push((Token::Ident(argument.clone()), position.clone()));
        }
        tokens.push((Token::GreaterThan, position));
    }
    let mut index = block.parameters.1 + 1;
    while index < block.end {
        // A use of a generic resource in the body is at the substituted
        // arguments.
        if let Some((used, used_arguments, after)) = uses.get(&index) {
            let used_arguments = used_arguments.iter().map(substituted).collect::<Vec<_>>();
            tokens.push((
                Token::Ident(instance_name(used, &used_arguments)),
                source[index].1.clone(),
            ));
            index = *after;
            continue;
        }
        tokens.push(match &source[index] {
            (Token::Ident(word), position) => (Token::Ident(substituted(word)), position.clone()),
            spanned => spanned.clone(),
        });
        index += 1;
    }
    tokens
}
