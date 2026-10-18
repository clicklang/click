//! A Rust sidecar's generic functions, written out at each instance the
//! import declares, by rewriting the sidecar's tokens as its generic crate
//! traits are.
//!
//! A generic function's block, `fn cells::read<T: Copy>(cell: &cells::Cell<T>)
//! -> T { ... } by { ... }`, is verified once with `T` abstract. Each instance
//! a call names, `cells::read<i32>`, has the same contract at its types: the
//! instance block is the generic block's signature and clauses with the
//! instance's types for its parameters, and no proof. Writing it out, rather
//! than reading the generic contract at other types, gives each instance its
//! own struct layouts: `cells::Cell<i32>` is laid out as its fields are.
//!
//! Every other token is kept, with its position.

use super::rust_generic_traits::INSTANCE_SCALARS;
use super::rust_trait_objects::{Spanned, error_at, is_ident, matching};
use super::*;

/// A top-level generic `fn` block.
struct Block {
    /// The index after its proof, or after its clause block when it has
    /// none.
    end: usize,
    /// The index of its path's first segment.
    path_start: usize,
    /// The indices of its type parameter list's `<` and `>`.
    parameters: (usize, usize),
    /// The index of its clause block's closing brace.
    clauses_end: usize,
    /// Its type parameters' names.
    names: Vec<String>,
}

/// Writes out each instance of the sidecar's generic functions, by the
/// function's importer name, at the type arguments the import declares,
/// after the generic block.
/// Returns the tokens with the index of each written instance's `fn`.
#[allow(clippy::type_complexity)]
///
/// A generic struct's `impl<T: Copy> cells::Cell<T> { ... }` block is written
/// out the same way at each instance of the struct whose methods a call
/// names, `impl cells::Cell<i32> { extern fn get(&self) -> i32 { ... } }`,
/// by the struct's importer name in `impl_instances`; the written `impl`
/// token's index is returned with the `fn` ones.
pub(super) fn expand_generic_functions(
    tokens: Vec<Token>,
    positions: Vec<SourcePosition>,
    instances: &BTreeMap<String, BTreeSet<Vec<String>>>,
    impl_instances: &BTreeMap<String, BTreeSet<Vec<String>>>,
) -> Result<(Vec<Token>, Vec<SourcePosition>, BTreeSet<usize>), ClickError> {
    let mut written = BTreeSet::new();
    let source: Vec<Spanned> = tokens.into_iter().zip(positions).collect();
    let mut output = Vec::with_capacity(source.len());
    let mut depth = 0i32;
    let mut index = 0;
    while index < source.len() {
        if depth == 0
            && is_ident(source.get(index), "fn")
            && let Some((name, block)) = block_at(&source, index)?
        {
            output.extend(source[index..block.end].iter().cloned());
            for arguments in instances.get(&name).into_iter().flatten() {
                if arguments.len() == block.names.len() {
                    // After its `extern`.
                    written.insert(output.len() + 1);
                    output.extend(instance(&source, index, &block, arguments));
                }
            }
            index = block.end;
            continue;
        }
        if depth == 0
            && is_ident(source.get(index), "impl")
            && let Some((name, block)) = impl_block_at(&source, index)?
        {
            output.extend(source[index..block.end].iter().cloned());
            for arguments in impl_instances.get(&name).into_iter().flatten() {
                if arguments.len() == block.arguments.len() {
                    written.insert(output.len());
                    output.extend(impl_instance(&source, index, &block, arguments));
                }
            }
            index = block.end;
            continue;
        }
        match source[index].0 {
            Token::LBrace | Token::LParen | Token::LBracket => depth += 1,
            Token::RBrace | Token::RParen | Token::RBracket => depth -= 1,
            _ => {}
        }
        output.push(source[index].clone());
        index += 1;
    }
    let (tokens, positions) = output.into_iter().unzip();
    Ok((tokens, positions, written))
}

/// The generic `fn` block at `start`, with the function's importer name,
/// when its type parameters are all abstract, `<T>` or `<T: Copy>`.
fn block_at(source: &[Spanned], start: usize) -> Result<Option<(String, Block)>, ClickError> {
    let path_start = start + 1;
    let mut segments = Vec::new();
    let mut index = path_start;
    while let Some((Token::Ident(segment), _)) = source.get(index) {
        segments.push(segment.clone());
        index += 1;
        if source.get(index).map(|(token, _)| token) != Some(&Token::ColonColon) {
            break;
        }
        index += 1;
    }
    let open = index;
    if segments.is_empty() || source.get(open).map(|(token, _)| token) != Some(&Token::LessThan) {
        return Ok(None);
    }
    let Some(close) = matching(source, open) else {
        return Ok(None);
    };
    let Some(names) = abstract_parameters(source, open, close) else {
        return Ok(None);
    };
    let position = &source[start].1;
    if source.get(close + 1).map(|(token, _)| token) != Some(&Token::LParen) {
        return Ok(None);
    }
    let unterminated = || error_at(position, "unterminated `fn` block");
    let mut clauses_open = matching(source, close + 1).ok_or_else(unterminated)?;
    while source
        .get(clauses_open)
        .is_some_and(|(token, _)| *token != Token::LBrace && *token != Token::Semicolon)
    {
        clauses_open += 1;
    }
    if source.get(clauses_open).map(|(token, _)| token) != Some(&Token::LBrace) {
        return Ok(None);
    }
    let clauses_end = matching(source, clauses_open).ok_or_else(unterminated)?;
    let mut end = clauses_end + 1;
    if is_ident(source.get(end), "by")
        && source.get(end + 1).map(|(token, _)| token) == Some(&Token::LBrace)
    {
        end = matching(source, end + 1).ok_or_else(unterminated)? + 1;
    }
    let name = crate::languages::rust::names::path_name(
        &segments.iter().map(String::as_str).collect::<Vec<_>>(),
    );
    Ok(Some((
        name,
        Block {
            end,
            path_start,
            parameters: (open, close),
            clauses_end,
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

/// A top-level generic struct's `impl` block.
struct ImplBlock {
    /// The index after its closing brace.
    end: usize,
    /// The indices of its path's first segment and of the `<` after it.
    path: (usize, usize),
    /// The struct's type arguments: the block's parameters, `T` of
    /// `Cell<T>`, in the struct's order.
    arguments: Vec<String>,
    /// Each method's `fn` index and its clause block's closing brace.
    methods: Vec<(usize, usize)>,
}

/// The generic struct's `impl<T: Copy> path::Cell<T> { ... }` block at
/// `start`, with the struct's importer name: an inherent block whose type's
/// arguments are its abstract parameters.
fn impl_block_at(
    source: &[Spanned],
    start: usize,
) -> Result<Option<(String, ImplBlock)>, ClickError> {
    let open = start + 1;
    if source.get(open).map(|(token, _)| token) != Some(&Token::LessThan) {
        return Ok(None);
    }
    let Some(close) = matching(source, open) else {
        return Ok(None);
    };
    let Some(parameters) = abstract_parameters(source, open, close) else {
        return Ok(None);
    };
    let path_start = close + 1;
    let mut segments = Vec::new();
    let mut index = path_start;
    while let Some((Token::Ident(segment), _)) = source.get(index) {
        segments.push(segment.clone());
        index += 1;
        if source.get(index).map(|(token, _)| token) != Some(&Token::ColonColon) {
            break;
        }
        index += 1;
    }
    let arguments_open = index;
    if segments.len() < 2
        || source.get(arguments_open).map(|(token, _)| token) != Some(&Token::LessThan)
    {
        return Ok(None);
    }
    let Some(arguments_close) = matching(source, arguments_open) else {
        return Ok(None);
    };
    let mut arguments = Vec::new();
    for (at, (token, _)) in source[arguments_open + 1..arguments_close]
        .iter()
        .enumerate()
    {
        match (at % 2, token) {
            (0, Token::Ident(argument)) if parameters.contains(argument) => {
                arguments.push(argument.clone())
            }
            (1, Token::Comma) => {}
            _ => return Ok(None),
        }
    }
    if arguments.len() != parameters.len()
        || source.get(arguments_close + 1).map(|(token, _)| token) != Some(&Token::LBrace)
    {
        return Ok(None);
    }
    let position = &source[start].1;
    let unterminated = || error_at(position, "unterminated `impl` block");
    let body_close = matching(source, arguments_close + 1).ok_or_else(unterminated)?;
    let mut methods = Vec::new();
    let mut at = arguments_close + 2;
    while at < body_close {
        if !is_ident(source.get(at), "fn") {
            return Ok(None);
        }
        let mut clauses_open = at;
        let mut parentheses = 0usize;
        while clauses_open < body_close {
            match source[clauses_open].0 {
                Token::LParen => parentheses += 1,
                Token::RParen => parentheses = parentheses.saturating_sub(1),
                Token::LBrace if parentheses == 0 => break,
                _ => {}
            }
            clauses_open += 1;
        }
        let clauses_end = matching(source, clauses_open).ok_or_else(unterminated)?;
        // A method with type parameters of its own is not written out.
        if source.get(at + 2).map(|(token, _)| token) != Some(&Token::LessThan) {
            methods.push((at, clauses_end));
        }
        at = clauses_end + 1;
        if is_ident(source.get(at), "by")
            && source.get(at + 1).map(|(token, _)| token) == Some(&Token::LBrace)
        {
            at = matching(source, at + 1).ok_or_else(unterminated)? + 1;
        }
    }
    let name = crate::languages::rust::names::path_name(
        &segments.iter().map(String::as_str).collect::<Vec<_>>(),
    );
    Ok(Some((
        name,
        ImplBlock {
            end: body_close + 1,
            path: (path_start, arguments_open),
            arguments,
            methods,
        },
    )))
}

/// The instance block of the generic struct `impl` block at `start` at
/// `arguments`: `impl path::Cell<i32> { extern fn ... }`, each method's
/// signature and clauses with each type parameter read as its argument.
fn impl_instance(
    source: &[Spanned],
    start: usize,
    block: &ImplBlock,
    arguments: &[String],
) -> Vec<Spanned> {
    let position = source[start].1.clone();
    let substitution = block
        .arguments
        .iter()
        .zip(arguments)
        .collect::<BTreeMap<_, _>>();
    let substituted = |range: std::ops::RangeInclusive<usize>| {
        source[range].iter().map(|(token, position)| match token {
            Token::Ident(word) if substitution.contains_key(word) => {
                (Token::Ident(substitution[word].clone()), position.clone())
            }
            token => (token.clone(), position.clone()),
        })
    };
    let mut tokens = vec![source[start].clone()];
    tokens.extend(source[block.path.0..block.path.1].iter().cloned());
    tokens.push((Token::LessThan, position.clone()));
    for (at, argument) in arguments.iter().enumerate() {
        if at > 0 {
            tokens.push((Token::Comma, position.clone()));
        }
        tokens.push((Token::Ident(argument.clone()), position.clone()));
    }
    tokens.push((Token::GreaterThan, position.clone()));
    tokens.push((Token::LBrace, position.clone()));
    for &(method, clauses_end) in &block.methods {
        tokens.push((Token::Ident("extern".into()), source[method].1.clone()));
        tokens.extend(substituted(method..=clauses_end));
    }
    tokens.push((Token::RBrace, position));
    tokens
}

/// The instance block of the generic `fn` block at `start` at `arguments`:
/// `extern fn path<i32>(...) -> ... { ... }`, its signature and clauses with
/// each type parameter read as its argument.
fn instance(source: &[Spanned], start: usize, block: &Block, arguments: &[String]) -> Vec<Spanned> {
    let position = source[start].1.clone();
    let substitution = block
        .names
        .iter()
        .zip(arguments)
        .collect::<BTreeMap<_, _>>();
    // The instance has no body of its own: its contract is an `extern fn`'s.
    let mut tokens = vec![
        (Token::Ident("extern".into()), position.clone()),
        source[start].clone(),
    ];
    tokens.extend(source[block.path_start..block.parameters.0].iter().cloned());
    tokens.push((Token::LessThan, position.clone()));
    for (at, argument) in arguments.iter().enumerate() {
        if at > 0 {
            tokens.push((Token::Comma, position.clone()));
        }
        tokens.push((Token::Ident(argument.clone()), position.clone()));
    }
    tokens.push((Token::GreaterThan, position));
    tokens.extend(
        source[block.parameters.1 + 1..=block.clauses_end]
            .iter()
            .map(|(token, position)| match token {
                Token::Ident(word) if substitution.contains_key(word) => {
                    (Token::Ident(substitution[word].clone()), position.clone())
                }
                token => (token.clone(), position.clone()),
            }),
    );
    tokens
}
