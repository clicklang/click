//! Trait object state in a Rust sidecar, written by rewriting the sidecar's
//! tokens before it is parsed.
//!
//! A crate trait may declare model functions of its object, `function
//! size(self) -> i32;`, and each implementation defines them, `function
//! size(self) -> i32 { self.side }`. The trait's object is then an abstract
//! resource whose fields are those functions, `trait_methods::Shape::object`:
//!
//! - A trait method whose receiver is a reference, and a parameter `x: &T`
//!   for `T: Trait` or `x: &dyn Trait`, holds the object: its contract owns
//!   `__object_x: Trait::object(x)`, a shared reference keeps its fields, and
//!   `size(x)` reads its field `size`.
//! - An implementation's method is verified on the object's memory: it owns
//!   `*self`, `size(self)` is the implementation's definition, and it inherits
//!   the interface's clauses read the same way. Its `requires` must follow
//!   from the interface's so read, which the `contract fn` named for it with
//!   `_iface` states, and which verification checks.
//!
//! Every other token is kept, with its position.

use super::*;

pub(super) type Spanned = (Token, SourcePosition);

/// A crate trait whose object carries state.
struct ObjectTrait {
    family: String,
    functions: Vec<(String, Vec<Spanned>)>,
    methods: BTreeMap<String, Interface>,
}

/// A trait method's interface, as its `fn` in the `trait` block writes it.
struct Interface {
    parameters: Vec<String>,
    clauses: Vec<Vec<Spanned>>,
}

/// One parameter of a `fn` head: its name, whether it is the receiver and
/// how (`Some(mutable)`), and its type's tokens.
struct Parameter {
    name: String,
    receiver: Option<bool>,
    tokens: Vec<Spanned>,
}

/// The name of the abstract resource that is crate trait `trait_name`'s
/// object.
pub(crate) fn object_family(trait_name: &str) -> String {
    let mut family = trait_name.to_string();
    crate::languages::rust::names::push_path_segment(&mut family, "object");
    family
}

/// The handle a function's contract gives the object a parameter holds.
pub(super) fn handle(parameter: &str) -> String {
    format!("__object_{parameter}")
}

/// The `contract fn` that states an implementation's interface on its own
/// object's memory, which the implementation must refine.
pub(crate) fn implementation_interface_contract(implementation: &str) -> String {
    format!("{implementation}_iface")
}

/// Rewrites the trait object state of a Rust sidecar, and returns the crate
/// traits, by importer name, whose objects carry it.
pub(super) fn rewrite_trait_objects(
    tokens: Vec<Token>,
    positions: Vec<SourcePosition>,
) -> Result<(Vec<Token>, Vec<SourcePosition>, BTreeSet<String>), ClickError> {
    let source: Vec<Spanned> = tokens.into_iter().zip(positions).collect();
    let traits = object_traits(&source)?;
    if traits.is_empty() {
        let (tokens, positions) = source.into_iter().unzip();
        return Ok((tokens, positions, BTreeSet::new()));
    }
    let mut output = Vec::with_capacity(source.len());
    let mut index = 0;
    while index < source.len() {
        index = rewrite_item(&source, index, &traits, &mut output)?;
    }
    let names = traits.keys().cloned().collect();
    let (tokens, positions) = output.into_iter().unzip();
    Ok((tokens, positions, names))
}

pub(super) fn is_ident(token: Option<&Spanned>, word: &str) -> bool {
    matches!(token, Some((Token::Ident(found), _)) if found == word)
}

pub(super) fn error_at(position: &SourcePosition, message: impl Into<String>) -> ClickError {
    ClickError::new(format!("{position}: {}", message.into())).with_kind(ClickErrorKind::Syntax)
}

/// The index of the token closing the bracket opened at `open`.
pub(super) fn matching(source: &[Spanned], open: usize) -> Option<usize> {
    let (opening, closing) = match source.get(open)?.0 {
        Token::LBrace => (Token::LBrace, Token::RBrace),
        Token::LParen => (Token::LParen, Token::RParen),
        Token::LBracket => (Token::LBracket, Token::RBracket),
        Token::LessThan => (Token::LessThan, Token::GreaterThan),
        _ => return None,
    };
    let mut depth = 0usize;
    for (index, (token, _)) in source.iter().enumerate().skip(open) {
        if *token == opening {
            depth += 1;
        } else if *token == closing {
            depth -= 1;
            if depth == 0 {
                return Some(index);
            }
        }
    }
    None
}

/// A path at `start`, `a::b::c`, as its segments and the index after it.
fn path_at(source: &[Spanned], start: usize) -> Option<(Vec<String>, usize)> {
    let Some((Token::Ident(first), _)) = source.get(start) else {
        return None;
    };
    let mut segments = vec![first.clone()];
    let mut index = start + 1;
    while source.get(index).map(|(token, _)| token) == Some(&Token::ColonColon) {
        let Some((Token::Ident(next), _)) = source.get(index + 1) else {
            break;
        };
        segments.push(next.clone());
        index += 2;
    }
    Some((segments, index))
}

fn path_name(segments: &[String]) -> String {
    crate::languages::rust::names::path_name(
        &segments.iter().map(String::as_str).collect::<Vec<_>>(),
    )
}

/// Splits `body` into its clauses at the semicolons outside brackets,
/// without the semicolons.
pub(super) fn split_clauses(body: &[Spanned]) -> Vec<Vec<Spanned>> {
    let mut clauses = Vec::new();
    let mut clause = Vec::new();
    let mut depth = 0i32;
    for spanned in body {
        match spanned.0 {
            Token::LParen | Token::LBrace | Token::LBracket => depth += 1,
            Token::RParen | Token::RBrace | Token::RBracket => depth -= 1,
            Token::Semicolon if depth == 0 => {
                if !clause.is_empty() {
                    clauses.push(std::mem::take(&mut clause));
                }
                continue;
            }
            _ => {}
        }
        clause.push(spanned.clone());
    }
    if !clause.is_empty() {
        clauses.push(clause);
    }
    clauses
}

/// The parameters of a `fn` head, between its parentheses.
fn parameters(list: &[Spanned]) -> Vec<Parameter> {
    let mut parameters = Vec::new();
    let mut current: Vec<Spanned> = Vec::new();
    let mut depth = 0i32;
    let mut finish = |current: &mut Vec<Spanned>| {
        let tokens = std::mem::take(current);
        if tokens.is_empty() {
            return;
        }
        if is_ident(tokens.last(), "self")
            && tokens[..tokens.len() - 1].iter().all(|(token, _)| {
                matches!(token, Token::Amp | Token::Lifetime(_))
                    || matches!(token, Token::Ident(word) if word == "mut")
            })
        {
            let reference = tokens.iter().any(|(token, _)| *token == Token::Amp);
            let mutable = tokens
                .iter()
                .any(|(token, _)| matches!(token, Token::Ident(word) if word == "mut"));
            parameters.push(Parameter {
                name: "self".into(),
                receiver: reference.then_some(mutable),
                tokens,
            });
            return;
        }
        let name = match tokens.first() {
            Some((Token::Ident(name), _)) => name.clone(),
            _ => String::new(),
        };
        parameters.push(Parameter {
            name,
            receiver: None,
            tokens,
        });
    };
    for spanned in list {
        match spanned.0 {
            Token::LParen | Token::LBracket | Token::LessThan => depth += 1,
            Token::RParen | Token::RBracket | Token::GreaterThan => depth -= 1,
            Token::Comma if depth == 0 => {
                finish(&mut current);
                continue;
            }
            _ => {}
        }
        current.push(spanned.clone());
    }
    finish(&mut current);
    parameters
}

/// The crate trait whose object a parameter holds: `x: &T` for a type
/// parameter `T` a crate trait bounds, or `x: &dyn Trait`, by the trait's
/// importer name, with whether the reference is shared.
fn object_parameter(
    parameter: &Parameter,
    bounds: &BTreeMap<String, String>,
    traits: &BTreeMap<String, ObjectTrait>,
) -> Option<(String, bool)> {
    let tokens = &parameter.tokens;
    let colon = tokens
        .iter()
        .position(|(token, _)| *token == Token::Colon)?;
    let mut index = colon + 1;
    if tokens.get(index).map(|(token, _)| token) != Some(&Token::Amp) {
        return None;
    }
    index += 1;
    if matches!(tokens.get(index), Some((Token::Lifetime(_), _))) {
        index += 1;
    }
    let mutable = is_ident(tokens.get(index), "mut");
    if mutable {
        index += 1;
    }
    let trait_name = if is_ident(tokens.get(index), "dyn") {
        let (segments, end) = path_at(tokens, index + 1)?;
        (end == tokens.len()).then(|| path_name(&segments))?
    } else {
        let Some((Token::Ident(name), _)) = tokens.get(index) else {
            return None;
        };
        (index + 1 == tokens.len()).then(|| bounds.get(name).cloned())??
    };
    traits
        .contains_key(&trait_name)
        .then_some((trait_name, !mutable))
}

/// `function(x)` for each of `functions`, replaced by what `replace` gives
/// for the function's name, reading each function at entry, `old(...)`, outside
/// an `old(...)` already written, when `kept` says a shared reference keeps
/// the object's functions through an `ensures`: the same value, which a
/// proof need not carry across the call.
pub(super) fn rewrite_calls(
    clause: &[Spanned],
    parameter: &str,
    functions: &[(String, Vec<Spanned>)],
    kept: bool,
    replace: &dyn Fn(&str, &SourcePosition) -> Vec<Spanned>,
) -> Vec<Spanned> {
    let at_entry = kept && is_ident(clause.first(), "ensures");
    let mut old_until: Vec<usize> = Vec::new();
    let mut output = Vec::with_capacity(clause.len());
    let mut index = 0;
    while index < clause.len() {
        old_until.retain(|&close| index <= close);
        if is_ident(clause.get(index), "old")
            && clause.get(index + 1).map(|(token, _)| token) == Some(&Token::LParen)
            && let Some(close) = matching(clause, index + 1)
        {
            old_until.push(close);
        }
        if at_entry
            && old_until.is_empty()
            && let (
                Some((Token::Ident(function), position)),
                Some((Token::LParen, _)),
                Some((Token::Ident(argument), _)),
                Some((Token::RParen, _)),
            ) = (
                clause.get(index),
                clause.get(index + 1),
                clause.get(index + 2),
                clause.get(index + 3),
            )
            && argument == parameter
            && functions.iter().any(|(name, _)| name == function)
            && !matches!(
                index.checked_sub(1).and_then(|before| clause.get(before)),
                Some((Token::Dot, _))
            )
        {
            output.extend(at(position, vec![ident("old"), Token::LParen]));
            output.extend(replace(function, position));
            output.push((Token::RParen, position.clone()));
            index += 4;
            continue;
        }
        if let (
            Some((Token::Ident(function), position)),
            Some((Token::LParen, _)),
            Some((Token::Ident(argument), _)),
            Some((Token::RParen, _)),
        ) = (
            clause.get(index),
            clause.get(index + 1),
            clause.get(index + 2),
            clause.get(index + 3),
        ) && argument == parameter
            && functions.iter().any(|(name, _)| name == function)
            && !matches!(
                index.checked_sub(1).and_then(|before| clause.get(before)),
                Some((Token::Dot, _))
            )
        {
            output.extend(replace(function, position));
            index += 4;
            continue;
        }
        output.push(clause[index].clone());
        index += 1;
    }
    output
}

/// Each identifier of `map` not after a `.`, renamed.
pub(super) fn rename(clause: &[Spanned], map: &BTreeMap<String, String>) -> Vec<Spanned> {
    clause
        .iter()
        .enumerate()
        .map(|(index, (token, position))| match token {
            Token::Ident(name)
                if map.contains_key(name)
                    && !matches!(
                        index.checked_sub(1).map(|before| &clause[before].0),
                        Some(Token::Dot)
                    ) =>
            {
                (Token::Ident(map[name].clone()), position.clone())
            }
            _ => (token.clone(), position.clone()),
        })
        .collect()
}

pub(super) fn same_tokens(left: &[Spanned], right: &[Spanned]) -> bool {
    left.len() == right.len()
        && left
            .iter()
            .zip(right)
            .all(|(left, right)| left.0 == right.0)
}

pub(super) fn at(position: &SourcePosition, tokens: Vec<Token>) -> Vec<Spanned> {
    tokens
        .into_iter()
        .map(|token| (token, position.clone()))
        .collect()
}

pub(super) fn ident(word: &str) -> Token {
    Token::Ident(word.to_string())
}

/// The handle read `__object_x.f`.
pub(super) fn field_read(
    parameter: &str,
    function: &str,
    position: &SourcePosition,
) -> Vec<Spanned> {
    at(
        position,
        vec![ident(&handle(parameter)), Token::Dot, ident(function)],
    )
}

/// The clauses that make a function hold the object of `parameter`: it owns
/// the object, and keeps its fields when the reference is shared.
fn object_clauses(
    parameter: &str,
    object: &ObjectTrait,
    shared: bool,
    position: &SourcePosition,
) -> (Vec<Spanned>, Vec<Spanned>) {
    let mut owns = at(
        position,
        vec![
            ident("owns"),
            ident(&handle(parameter)),
            Token::Colon,
            ident(&object.family),
            Token::LParen,
            ident(parameter),
            Token::RParen,
            Token::Semicolon,
        ],
    );
    let mut keeps = Vec::new();
    if shared {
        for (function, _) in &object.functions {
            keeps.extend(at(position, vec![ident("ensures")]));
            keeps.extend(field_read(parameter, function, position));
            keeps.extend(at(
                position,
                vec![Token::EqualEqual, ident("old"), Token::LParen],
            ));
            keeps.extend(field_read(parameter, function, position));
            keeps.extend(at(position, vec![Token::RParen, Token::Semicolon]));
        }
    }
    owns.shrink_to_fit();
    (owns, keeps)
}

/// Finds the crate traits that declare model functions, with their methods'
/// interfaces.
fn object_traits(source: &[Spanned]) -> Result<BTreeMap<String, ObjectTrait>, ClickError> {
    let mut traits = BTreeMap::new();
    let mut depth = 0i32;
    let mut index = 0;
    while index < source.len() {
        match source[index].0 {
            Token::LBrace => depth += 1,
            Token::RBrace => depth -= 1,
            _ => {}
        }
        if depth == 0
            && is_ident(source.get(index), "trait")
            && let Some((segments, open)) = path_at(source, index + 1)
            && source.get(open).map(|(token, _)| token) == Some(&Token::LBrace)
        {
            let close = matching(source, open)
                .ok_or_else(|| error_at(&source[open].1, "unterminated `trait` block"))?;
            let name = path_name(&segments);
            let mut functions = Vec::new();
            let mut methods = BTreeMap::new();
            let mut item = open + 1;
            while item < close {
                if is_ident(source.get(item), "function") {
                    let end = (item..close)
                        .find(|&at| source[at].0 == Token::Semicolon)
                        .ok_or_else(|| {
                            error_at(&source[item].1, "a trait `function` ends with `;`")
                        })?;
                    let (Some((Token::Ident(function), _)), Some((Token::LParen, _))) =
                        (source.get(item + 1), source.get(item + 2))
                    else {
                        return Err(error_at(
                            &source[item].1,
                            "a trait `function` is written `function name(self) -> T;`",
                        ));
                    };
                    let arrow = (item..end).find(|&at| source[at].0 == Token::Arrow).ok_or_else(|| {
                        error_at(&source[item].1, "a trait `function` names its result type, `function name(self) -> T;`")
                    })?;
                    if !(source
                        .get(item + 3)
                        .is_some_and(|(token, _)| *token == ident("self"))
                        && source
                            .get(item + 4)
                            .is_some_and(|(token, _)| *token == Token::RParen)
                        && arrow == item + 5)
                    {
                        return Err(error_at(
                            &source[item].1,
                            "a trait `function` takes only `self`: `function name(self) -> T;`",
                        ));
                    }
                    functions.push((function.clone(), source[arrow + 1..end].to_vec()));
                    item = end + 1;
                    continue;
                }
                if is_ident(source.get(item), "fn")
                    && let Some((Token::Ident(method), _)) = source.get(item + 1)
                    && let Some(list_open) =
                        (item + 2..close).find(|&at| source[at].0 == Token::LParen)
                    && let Some(list_close) = matching(source, list_open)
                    && let Some(body_open) =
                        (list_close..close).find(|&at| source[at].0 == Token::LBrace)
                    && let Some(body_close) = matching(source, body_open)
                {
                    methods.insert(
                        method.clone(),
                        Interface {
                            parameters: parameters(&source[list_open + 1..list_close])
                                .into_iter()
                                .map(|parameter| parameter.name)
                                .collect(),
                            clauses: split_clauses(&source[body_open + 1..body_close]),
                        },
                    );
                    item = body_close + 1;
                    // A default method's proof is no part of the interface.
                    if is_ident(source.get(item), "by")
                        && source.get(item + 1).map(|(token, _)| token) == Some(&Token::LBrace)
                        && let Some(proof_close) = matching(source, item + 1)
                    {
                        item = proof_close + 1;
                    }
                    continue;
                }
                item += 1;
            }
            if !functions.is_empty() {
                traits.insert(
                    name.clone(),
                    ObjectTrait {
                        family: object_family(&name),
                        functions,
                        methods,
                    },
                );
            }
            index = close + 1;
            depth = 0;
            continue;
        }
        index += 1;
    }
    Ok(traits)
}

/// Rewrites the item at `index` into `output`, returning the index after it.
fn rewrite_item(
    source: &[Spanned],
    index: usize,
    traits: &BTreeMap<String, ObjectTrait>,
    output: &mut Vec<Spanned>,
) -> Result<usize, ClickError> {
    if is_ident(source.get(index), "trait")
        && let Some((segments, open)) = path_at(source, index + 1)
        && source.get(open).map(|(token, _)| token) == Some(&Token::LBrace)
        && let Some(object) = traits.get(&path_name(&segments))
    {
        let close = matching(source, open).expect("checked when the traits were found");
        output.extend(object_declaration(object, &source[index].1));
        output.extend(source[index..=open].iter().cloned());
        let mut item = open + 1;
        while item < close {
            if is_ident(source.get(item), "function") {
                item = (item..close)
                    .find(|&at| source[at].0 == Token::Semicolon)
                    .map_or(close, |end| end + 1);
                continue;
            }
            if is_ident(source.get(item), "fn") {
                item = rewrite_function(source, item, traits, Some(object), output)?;
                continue;
            }
            output.push(source[item].clone());
            item += 1;
        }
        output.push(source[close].clone());
        return Ok(close + 1);
    }
    if is_ident(source.get(index), "impl")
        && let Some((trait_segments, after_trait)) = path_at(source, index + 1)
        && is_ident(source.get(after_trait), "for")
        && let Some((type_segments, open)) = path_at(source, after_trait + 1)
        && source.get(open).map(|(token, _)| token) == Some(&Token::LBrace)
        && let Some(object) = traits.get(&path_name(&trait_segments))
    {
        return rewrite_implementation(
            source,
            index,
            open,
            object,
            &path_name(&trait_segments),
            &type_segments,
            traits,
            output,
        );
    }
    if is_ident(source.get(index), "fn")
        && matches!(source.get(index + 1), Some((Token::Ident(_), _)))
    {
        return rewrite_function(source, index, traits, None, output);
    }
    output.push(source[index].clone());
    Ok(index + 1)
}

/// `abstract resource Family(object: *const i32) { field f: T; ... }`.
fn object_declaration(object: &ObjectTrait, position: &SourcePosition) -> Vec<Spanned> {
    let mut tokens = at(
        position,
        vec![
            ident("abstract"),
            ident("resource"),
            ident(&object.family),
            Token::LParen,
            ident("object"),
            Token::Colon,
            Token::Star,
            ident("const"),
            ident("i32"),
            Token::RParen,
            Token::LBrace,
        ],
    );
    for (function, result) in &object.functions {
        tokens.extend(at(
            position,
            vec![ident("field"), ident(function), Token::Colon],
        ));
        tokens.extend(result.iter().cloned());
        tokens.extend(at(position, vec![Token::Semicolon]));
    }
    tokens.extend(at(position, vec![Token::RBrace]));
    tokens
}

/// The type parameters a crate trait bounds, `<T: crate::Trait>`, by name.
fn bounds(source: &[Spanned], open: usize, close: usize) -> BTreeMap<String, String> {
    let mut bounds = BTreeMap::new();
    let mut index = open + 1;
    while index < close {
        if let Some((Token::Ident(name), _)) = source.get(index)
            && source.get(index + 1).map(|(token, _)| token) == Some(&Token::Colon)
            && let Some((segments, end)) = path_at(source, index + 2)
            && segments.len() > 1
        {
            bounds.insert(name.clone(), path_name(&segments));
            index = end;
            continue;
        }
        index += 1;
    }
    bounds
}

/// A `fn` whose parameters hold trait objects: its contract owns each
/// object and reads the trait's functions of it as the object's fields.
/// `receiver_trait` is the trait whose `trait` block holds the `fn`, whose
/// reference receiver holds that trait's object.
fn rewrite_function(
    source: &[Spanned],
    index: usize,
    traits: &BTreeMap<String, ObjectTrait>,
    receiver_trait: Option<&ObjectTrait>,
    output: &mut Vec<Spanned>,
) -> Result<usize, ClickError> {
    let Some((_, mut after_name)) = path_at(source, index + 1) else {
        output.push(source[index].clone());
        return Ok(index + 1);
    };
    let mut generic_bounds = BTreeMap::new();
    if source.get(after_name).map(|(token, _)| token) == Some(&Token::LessThan)
        && let Some(close) = matching(source, after_name)
    {
        generic_bounds = bounds(source, after_name, close);
        after_name = close + 1;
    }
    let Some(list_close) = (source.get(after_name).map(|(token, _)| token) == Some(&Token::LParen))
        .then(|| matching(source, after_name))
        .flatten()
    else {
        output.push(source[index].clone());
        return Ok(index + 1);
    };
    let Some(body_open) = (list_close..source.len())
        .find(|&at| matches!(source[at].0, Token::LBrace | Token::Semicolon))
        .filter(|&at| source[at].0 == Token::LBrace)
    else {
        output.push(source[index].clone());
        return Ok(index + 1);
    };
    let body_close = matching(source, body_open)
        .ok_or_else(|| error_at(&source[body_open].1, "unterminated `fn` contract"))?;
    let objects = parameters(&source[after_name + 1..list_close])
        .into_iter()
        .filter_map(|parameter| match (parameter.receiver, receiver_trait) {
            (Some(mutable), Some(object)) => Some((parameter.name, object, !mutable)),
            _ => object_parameter(&parameter, &generic_bounds, traits)
                .map(|(name, shared)| (parameter.name, &traits[&name], shared)),
        })
        .collect::<Vec<_>>();
    if objects.is_empty() {
        output.extend(source[index..=body_close].iter().cloned());
        return Ok(body_close + 1);
    }
    let position = &source[body_open].1;
    output.extend(source[index..=body_open].iter().cloned());
    let mut keeps = Vec::new();
    for (parameter, object, shared) in &objects {
        let (owns, keep) = object_clauses(parameter, object, *shared, position);
        output.extend(owns);
        keeps.extend(keep);
    }
    for clause in split_clauses(&source[body_open + 1..body_close]) {
        let mut clause = clause;
        for (parameter, object, shared) in &objects {
            clause = rewrite_calls(
                &clause,
                parameter,
                &object.functions,
                *shared,
                &|function, position| field_read(parameter, function, position),
            );
        }
        let end = clause
            .last()
            .map(|(_, position)| position.clone())
            .unwrap_or_else(|| position.clone());
        output.extend(clause);
        output.push((Token::Semicolon, end));
    }
    output.extend(keeps);
    output.push(source[body_close].clone());
    Ok(body_close + 1)
}

/// `impl Trait for Type { ... }` of a trait whose object carries state: each
/// method is verified on the object's memory, and inherits the interface's
/// clauses read the same way; a `contract fn` states that interface for the
/// refinement check.
#[allow(clippy::too_many_arguments)]
fn rewrite_implementation(
    source: &[Spanned],
    index: usize,
    open: usize,
    object: &ObjectTrait,
    trait_name: &str,
    type_segments: &[String],
    traits: &BTreeMap<String, ObjectTrait>,
    output: &mut Vec<Spanned>,
) -> Result<usize, ClickError> {
    let close = matching(source, open)
        .ok_or_else(|| error_at(&source[open].1, "unterminated `impl` block"))?;
    // The implementation's definitions of the trait's functions.
    let mut definitions = BTreeMap::new();
    let mut item = open + 1;
    while item < close {
        if is_ident(source.get(item), "function")
            && let Some((Token::Ident(function), _)) = source.get(item + 1)
            && let Some(body_open) = (item..close).find(|&at| source[at].0 == Token::LBrace)
            && let Some(body_close) = matching(source, body_open)
        {
            definitions.insert(function.clone(), source[body_open + 1..body_close].to_vec());
            item = body_close + 1;
            continue;
        }
        item += 1;
    }
    let type_name = path_name(type_segments);
    for (function, _) in &object.functions {
        if !definitions.contains_key(function) {
            return Err(error_at(
                &source[index].1,
                format!(
                    "`impl` of a trait with `function {function}` defines it for its type: `function {function}(self) -> T {{ ... }}`"
                ),
            ));
        }
    }
    let functions = object
        .functions
        .iter()
        .map(|(function, _)| (function.clone(), definitions[function].clone()))
        .collect::<Vec<_>>();
    let on_memory = |clause: &[Spanned], kept: bool| {
        rewrite_calls(clause, "self", &functions, kept, &|function, position| {
            let mut tokens = vec![(Token::LParen, position.clone())];
            tokens.extend(definitions[function].iter().cloned());
            tokens.push((Token::RParen, position.clone()));
            tokens
        })
    };
    output.extend(source[index..=open].iter().cloned());
    let mut interfaces = Vec::new();
    let mut item = open + 1;
    while item < close {
        if is_ident(source.get(item), "function")
            && let Some(body_open) = (item..close).find(|&at| source[at].0 == Token::LBrace)
            && let Some(body_close) = matching(source, body_open)
        {
            item = body_close + 1;
            continue;
        }
        let Some((method, list_open, list_close, body_open, body_close)) =
            method_at(source, item, close)
        else {
            output.push(source[item].clone());
            item += 1;
            continue;
        };
        let method = &method;
        let position = source[body_open].1.clone();
        let own = parameters(&source[list_open + 1..list_close]);
        let receiver = own.first().and_then(|parameter| parameter.receiver);
        let interface = object.methods.get(method);
        let renames = interface
            .filter(|interface| interface.parameters.len() == own.len())
            .map(|interface| {
                interface
                    .parameters
                    .iter()
                    .zip(&own)
                    .filter(|(from, to)| *from != &to.name)
                    .map(|(from, to)| (from.clone(), to.name.clone()))
                    .collect::<BTreeMap<_, _>>()
            })
            .unwrap_or_default();
        let memory = receiver.map(|_| {
            at(
                &position,
                vec![ident("owns"), Token::Star, ident("self"), Token::Semicolon],
            )
        });
        let own_clauses = split_clauses(&source[body_open + 1..body_close])
            .iter()
            .map(|clause| on_memory(clause, receiver == Some(false)))
            .collect::<Vec<_>>();
        let writes_requires = own_clauses
            .iter()
            .any(|clause| is_ident(clause.first(), "requires"));
        // The interface read on this object's memory: its own clauses, then
        // that a shared receiver keeps the functions' values.
        let mut interface_clauses = Vec::new();
        let mut ensures = 0usize;
        for clause in interface.map_or(&[][..], |interface| &interface.clauses) {
            let clause = on_memory(&rename(clause, &renames), receiver == Some(false));
            if is_ident(clause.first(), "ensures") {
                let named = matches!(clause.get(1), Some((Token::Ident(_), _)))
                    && clause.get(2).map(|(token, _)| token) == Some(&Token::Colon);
                let mut labeled = vec![clause[0].clone()];
                if named {
                    let Some((Token::Ident(name), label_position)) = clause.get(1) else {
                        unreachable!()
                    };
                    labeled.push((ident(&format!("interface_{name}")), label_position.clone()));
                    labeled.extend(clause[2..].iter().cloned());
                } else {
                    labeled.push((
                        ident(&format!("interface_ensures_{ensures}")),
                        clause[0].1.clone(),
                    ));
                    labeled.push((Token::Colon, clause[0].1.clone()));
                    labeled.extend(clause[1..].iter().cloned());
                }
                ensures += 1;
                interface_clauses.push((clause, labeled));
            } else {
                interface_clauses.push((clause.clone(), clause));
            }
        }
        if receiver == Some(false) {
            for (function, _) in &object.functions {
                let definition = &definitions[function];
                let mut clause = at(
                    &position,
                    vec![
                        ident("ensures"),
                        ident(&format!("interface_keeps_{function}")),
                        Token::Colon,
                        Token::LParen,
                    ],
                );
                clause.extend(definition.iter().cloned());
                clause.extend(at(
                    &position,
                    vec![
                        Token::RParen,
                        Token::EqualEqual,
                        ident("old"),
                        Token::LParen,
                        Token::LParen,
                    ],
                ));
                clause.extend(definition.iter().cloned());
                clause.extend(at(&position, vec![Token::RParen, Token::RParen]));
                interface_clauses.push((clause.clone(), clause));
            }
        }
        // The method's own contract on the object's memory, with the
        // interface's clauses it does not already state.
        output.extend(source[item..=body_open].iter().cloned());
        if let Some(memory) = &memory {
            output.extend(memory.iter().cloned());
        }
        for clause in &own_clauses {
            output.extend(clause.iter().cloned());
            output.push((Token::Semicolon, position.clone()));
        }
        for (plain, labeled) in &interface_clauses {
            let requires = is_ident(plain.first(), "requires");
            if (requires && writes_requires)
                || own_clauses.iter().any(|own| same_tokens(own, plain))
            {
                continue;
            }
            output.extend(labeled.iter().cloned());
            output.push((Token::Semicolon, position.clone()));
        }
        output.push(source[body_close].clone());
        // The interface as a `contract fn` of this implementation's
        // parameters, with a receiver of this type.
        let implementation =
            crate::languages::rust::names::trait_method_name(&type_name, trait_name, method);
        let mut contract = at(
            &position,
            vec![
                ident("contract"),
                ident("fn"),
                ident(&implementation_interface_contract(&implementation)),
                Token::LParen,
            ],
        );
        for (number, parameter) in own.iter().enumerate() {
            if number > 0 {
                contract.push((Token::Comma, position.clone()));
            }
            match parameter.receiver {
                Some(mutable) => {
                    contract.extend(at(&position, vec![ident("self"), Token::Colon, Token::Amp]));
                    if mutable {
                        contract.push((ident("mut"), position.clone()));
                    }
                    for (segment_index, segment) in type_segments.iter().enumerate() {
                        if segment_index > 0 {
                            contract.push((Token::ColonColon, position.clone()));
                        }
                        contract.push((ident(segment), position.clone()));
                    }
                }
                None => contract.extend(parameter.tokens.iter().cloned()),
            }
        }
        contract.extend(source[list_close..=body_open].iter().cloned());
        if let Some(memory) = &memory {
            contract.extend(memory.iter().cloned());
        }
        for (plain, _) in &interface_clauses {
            contract.extend(plain.iter().cloned());
            contract.push((Token::Semicolon, position.clone()));
        }
        contract.push((Token::RBrace, position.clone()));
        if interface.is_some() {
            interfaces.push(contract);
        }
        item = body_close + 1;
    }
    output.push(source[close].clone());
    for contract in interfaces {
        output.extend(contract);
    }
    output.extend(coercion_contracts(
        object,
        trait_name,
        &type_name,
        type_segments,
        &functions,
        &source[index].1,
    ));
    // A method's other parameters may hold objects too.
    let _ = traits;
    Ok(close + 1)
}

/// The `fn` at `item` before `close`: its name, its parameter list's
/// parentheses, and its contract's braces.
fn method_at(
    source: &[Spanned],
    item: usize,
    close: usize,
) -> Option<(String, usize, usize, usize, usize)> {
    if !is_ident(source.get(item), "fn") {
        return None;
    }
    let Some((Token::Ident(method), _)) = source.get(item + 1) else {
        return None;
    };
    let list_open = (item + 2..close).find(|&at| source[at].0 == Token::LParen)?;
    let list_close = matching(source, list_open)?;
    let body_open = (list_close..close).find(|&at| source[at].0 == Token::LBrace)?;
    let body_close = matching(source, body_open)?;
    Some((method.clone(), list_open, list_close, body_open, body_close))
}

/// The trusted contracts of the functions the importer places where a
/// reference to this type becomes the trait's object, and back:
/// `<Type as Trait>::__pack` consumes the struct's memory and produces the
/// object, whose fields are the type's definitions of the trait's functions
/// on that memory; `__unpack` returns the memory, whose definitions are the
/// object's fields.
fn coercion_contracts(
    object: &ObjectTrait,
    trait_name: &str,
    type_name: &str,
    type_segments: &[String],
    definitions: &[(String, Vec<Spanned>)],
    position: &SourcePosition,
) -> Vec<Spanned> {
    let receiver = BTreeMap::from([("self".to_string(), "object".to_string())]);
    let handle = handle("object");
    let head = |name: &str| {
        let mut tokens = at(
            position,
            vec![
                ident("extern"),
                ident("fn"),
                ident(name),
                Token::LParen,
                ident("object"),
                Token::Colon,
                Token::Amp,
            ],
        );
        for (index, segment) in type_segments.iter().enumerate() {
            if index > 0 {
                tokens.push((Token::ColonColon, position.clone()));
            }
            tokens.push((ident(segment), position.clone()));
        }
        tokens.extend(at(position, vec![Token::RParen, Token::LBrace]));
        tokens
    };
    let instance = |verb: &str| {
        at(
            position,
            vec![
                ident(verb),
                ident(&handle),
                Token::Colon,
                ident(&object.family),
                Token::LParen,
                ident("object"),
                Token::RParen,
                Token::Semicolon,
            ],
        )
    };
    let memory = |verb: &str| {
        at(
            position,
            vec![ident(verb), Token::Star, ident("object"), Token::Semicolon],
        )
    };
    let pack = crate::languages::rust::names::trait_method_name(type_name, trait_name, "__pack");
    let unpack =
        crate::languages::rust::names::trait_method_name(type_name, trait_name, "__unpack");
    let mut tokens = head(&pack);
    tokens.extend(memory("consumes"));
    tokens.extend(instance("produces"));
    for (function, definition) in definitions {
        tokens.push((ident("ensures"), position.clone()));
        tokens.extend(field_read("object", function, position));
        tokens.extend(at(
            position,
            vec![
                Token::EqualEqual,
                ident("old"),
                Token::LParen,
                Token::LParen,
            ],
        ));
        tokens.extend(rename(definition, &receiver));
        tokens.extend(at(
            position,
            vec![Token::RParen, Token::RParen, Token::Semicolon],
        ));
    }
    tokens.push((Token::RBrace, position.clone()));
    tokens.extend(head(&unpack));
    tokens.extend(instance("consumes"));
    tokens.extend(memory("produces"));
    for (function, definition) in definitions {
        tokens.extend(at(position, vec![ident("ensures"), Token::LParen]));
        tokens.extend(rename(definition, &receiver));
        tokens.extend(at(
            position,
            vec![
                Token::RParen,
                Token::EqualEqual,
                ident("old"),
                Token::LParen,
            ],
        ));
        tokens.extend(field_read("object", function, position));
        tokens.extend(at(position, vec![Token::RParen, Token::Semicolon]));
    }
    tokens.push((Token::RBrace, position.clone()));
    tokens
}
