//! A C++ sidecar's methods of generic class templates, written out at each
//! instance the import declares, by rewriting the sidecar's tokens as a Rust
//! sidecar's generic functions are.
//!
//! `template<class T> void Cell<T>::set(T v) { ... } by { ... }` states a
//! method of a class template the project verifies once for every type
//! argument: its body is checked with `T` abstract. Each instance a call
//! names, `Cell<int>::set`, has the same contract at its type arguments: the
//! instance block is the generic block's head and clauses with each type
//! parameter spelled as its argument, `extern void Cell<int>::set(int v) {
//! ... }`, and no proof. Writing it out gives each instance its own record
//! layouts: `Cell<int>` is laid out as Clang lays it out.
//!
//! Every other token is kept, with its position.

use super::cpp_syntax::cpp_path_at;
use super::rust_trait_objects::{Spanned, error_at, is_ident, matching};
use super::*;

/// A top-level `template<...>` method block.
struct Block {
    /// The index after its proof, or after its clause block when it has
    /// none.
    end: usize,
    /// The index after the template parameter list's `>`.
    head_start: usize,
    /// The index of its clause block's closing brace.
    clauses_end: usize,
    /// Its type parameters' names.
    names: Vec<String>,
}

/// Writes out each instance of the sidecar's generic methods, by the
/// generic method's importer name, at the type arguments the import
/// declares, after the generic block. Returns the tokens with the index of
/// each written instance's `extern`.
#[allow(clippy::type_complexity)]
pub(super) fn expand_generic_methods(
    tokens: Vec<Token>,
    positions: Vec<SourcePosition>,
    instances: &BTreeMap<String, BTreeSet<Vec<String>>>,
) -> Result<(Vec<Token>, Vec<SourcePosition>, BTreeSet<usize>), ClickError> {
    let mut written = BTreeSet::new();
    let source: Vec<Spanned> = tokens.into_iter().zip(positions).collect();
    let plain = source
        .iter()
        .map(|(token, _)| token.clone())
        .collect::<Vec<_>>();
    let mut output = Vec::with_capacity(source.len());
    let mut depth = 0i32;
    let mut index = 0;
    while index < source.len() {
        if depth == 0
            && is_ident(source.get(index), "template")
            && let Some((name, block)) = block_at(&source, &plain, index)?
        {
            output.extend(source[index..block.end].iter().cloned());
            for arguments in instances.get(&name).into_iter().flatten() {
                if arguments.len() != block.names.len() {
                    return Err(error_at(
                        &source[index].1,
                        format!(
                            "the generic method takes {} type arguments and its instance {}",
                            block.names.len(),
                            arguments.len()
                        ),
                    ));
                }
                written.insert(output.len());
                output.extend(instance(&source, index, &block, arguments));
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

/// The generic method block at `start`, `template<class T> ... { ... } by
/// { ... }`, with the method's importer name.
fn block_at(
    source: &[Spanned],
    plain: &[Token],
    start: usize,
) -> Result<Option<(String, Block)>, ClickError> {
    let open = start + 1;
    if source.get(open).map(|(token, _)| token) != Some(&Token::LessThan) {
        return Ok(None);
    }
    let position = &source[start].1;
    let close = matching(source, open)
        .ok_or_else(|| error_at(position, "unterminated template parameters"))?;
    let names = template_parameters(source, open, close).ok_or_else(|| {
        error_at(
            position,
            "a generic method's template parameters are types, `template<class T>`",
        )
    })?;
    let head_start = close + 1;
    let Some(parameters_open) = (head_start..source.len())
        .find(|&at| {
            matches!(
                source[at].0,
                Token::LParen | Token::LBrace | Token::Semicolon
            )
        })
        .filter(|&at| source[at].0 == Token::LParen)
    else {
        return Err(error_at(
            position,
            "expected a method head after `template<...>`",
        ));
    };
    // The method's path is the declarator just before its parameters: the
    // tokens before it are its return type.
    let Some(segments) = (head_start..parameters_open).find_map(|at| {
        cpp_path_at(plain, at)
            .filter(|(_, end)| *end == parameters_open)
            .map(|(segments, _)| segments)
    }) else {
        return Err(error_at(
            position,
            "expected a method path before its parameters",
        ));
    };
    let unterminated = || error_at(position, "unterminated generic method block");
    let mut clauses_open = matching(source, parameters_open).ok_or_else(unterminated)?;
    while source
        .get(clauses_open)
        .is_some_and(|(token, _)| *token != Token::LBrace && *token != Token::Semicolon)
    {
        clauses_open += 1;
    }
    if source.get(clauses_open).map(|(token, _)| token) != Some(&Token::LBrace) {
        return Err(error_at(position, "a generic method states its contract"));
    }
    let clauses_end = matching(source, clauses_open).ok_or_else(unterminated)?;
    let mut end = clauses_end + 1;
    if is_ident(source.get(end), "by")
        && source.get(end + 1).map(|(token, _)| token) == Some(&Token::LBrace)
    {
        end = matching(source, end + 1).ok_or_else(unterminated)? + 1;
    }
    Ok(Some((
        crate::languages::cpp::names::path_name(&segments),
        Block {
            end,
            head_start,
            clauses_end,
            names,
        },
    )))
}

/// The names of the type parameters between `<` at `open` and `>` at
/// `close`, each `class T` or `typename T`.
pub(super) fn template_parameters(
    source: &[Spanned],
    open: usize,
    close: usize,
) -> Option<Vec<String>> {
    let mut names = Vec::new();
    let mut at = open + 1;
    while at < close {
        if !is_ident(source.get(at), "class") && !is_ident(source.get(at), "typename") {
            return None;
        }
        let Some((Token::Ident(name), _)) = source.get(at + 1) else {
            return None;
        };
        if names.contains(name) {
            return None;
        }
        names.push(name.clone());
        at += 2;
        if at < close {
            if source[at].0 != Token::Comma {
                return None;
            }
            at += 1;
        }
    }
    (!names.is_empty()).then_some(names)
}

/// The instance block of the generic method block at `start` at
/// `arguments`: `extern` and its head and clauses with each type parameter
/// spelled as its argument, `unsigned long` as two words.
fn instance(source: &[Spanned], start: usize, block: &Block, arguments: &[String]) -> Vec<Spanned> {
    let position = source[start].1.clone();
    let substitution = block
        .names
        .iter()
        .zip(arguments)
        .collect::<BTreeMap<_, _>>();
    let mut tokens = vec![(Token::Ident("extern".into()), position)];
    for (token, position) in &source[block.head_start..=block.clauses_end] {
        match token {
            Token::Ident(word) if substitution.contains_key(word) => {
                for part in substitution[word].split_whitespace() {
                    tokens.push((Token::Ident(part.to_string()), position.clone()));
                }
            }
            token => tokens.push((token.clone(), position.clone())),
        }
    }
    tokens
}

/// The type arguments of the class template instance whose method
/// `instance` is, `["int"]` for `Cell<int>::set`, as Clang prints them.
pub(super) fn instance_arguments(instance: &str) -> Option<Vec<String>> {
    let display = crate::languages::cpp::names::cpp_display_name(instance)?;
    let (record, _) = display.rsplit_once("::")?;
    let open = record.find('<')?;
    let inner = record.get(open + 1..record.len().checked_sub(1)?)?;
    record
        .ends_with('>')
        .then(|| inner.split(", ").map(str::to_string).collect::<Vec<_>>())
}
