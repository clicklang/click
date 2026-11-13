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
//! layouts: `Cell<int>` is laid out as Clang lays it out. An instance's
//! parameters take the instance's own names, by position, as Clang names
//! them there: a standard library names `std::span<int>::first`'s count
//! `__count`, which the template need not spell.
//!
//! A non-type parameter, `template<class T, std::size_t N>`, is an extent:
//! an instance writes its argument as a `uint64` literal, `4u64`, and as
//! Clang prints it, `4`, in a template argument list, `std::span<int, 4>`.
//!
//! The Click library's templates (`library/cpp/`) state standard methods
//! whose generic method no import has: only their instances are written,
//! and the template itself is dropped.
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
    /// Its template parameters.
    names: Vec<TemplateParameter>,
    /// Its method's parameters' names, by position, `None` for one the head
    /// does not name.
    parameters: Vec<Option<String>>,
    /// Whether its head is `const`, `T* Box<T>::get() const`.
    constant: bool,
}

/// Each instance's parameters' names after its receiver, by whether its
/// receiver is `const` and its type arguments: a `const` method's instances
/// are written from its `const` overload.
pub(super) type Instances = BTreeMap<(bool, Vec<String>), Vec<String>>;

/// Writes out each instance of the sidecar's generic methods, by the
/// generic method's importer name, at the type arguments the import
/// declares, after the generic block. Returns the tokens with the index of
/// each written instance's `extern`.
#[allow(clippy::type_complexity)]
pub(super) fn expand_generic_methods(
    tokens: Vec<Token>,
    positions: Vec<SourcePosition>,
    instances: &BTreeMap<String, Instances>,
) -> Result<(Vec<Token>, Vec<SourcePosition>, BTreeSet<usize>), ClickError> {
    let mut written = BTreeSet::new();
    let source: Vec<Spanned> = tokens.into_iter().zip(positions).collect();
    let plain = source
        .iter()
        .map(|(token, _)| token.clone())
        .collect::<Vec<_>>();
    let mut output = Vec::with_capacity(source.len());
    // The generic methods written out, by path and constness: overloads
    // that differ otherwise are not told apart.
    let mut expanded = BTreeSet::new();
    let mut depth = 0i32;
    let mut index = 0;
    while index < source.len() {
        if depth == 0
            && is_ident(source.get(index), "template")
            && let Some((name, block)) = block_at(&source, &plain, index)?
        {
            if !crate::languages::cpp::standard_library::is_library_generic(&name) {
                output.extend(source[index..block.end].iter().cloned());
            }
            let mut block_instances = instances
                .get(&name)
                .into_iter()
                .flatten()
                .filter(|((constant, _), _)| *constant == block.constant)
                .peekable();
            if block_instances.peek().is_some() && !expanded.insert((name.clone(), block.constant))
            {
                return Err(error_at(
                    &source[index].1,
                    "a generic method's overloads are told apart by their receiver's constness \
                     alone",
                ));
            }
            for ((_, arguments), parameters) in block_instances {
                if arguments.len() != block.names.len() {
                    return Err(error_at(
                        &source[index].1,
                        format!(
                            "the generic method takes {} template arguments and its instance {}",
                            block.names.len(),
                            arguments.len()
                        ),
                    ));
                }
                written.insert(output.len());
                output.extend(instance(&source, index, &block, arguments, parameters)?);
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
            "a generic method's template parameters are types, `class T`, or extents, \
             `std::size_t N`",
        )
    })?;
    // A generic method's named contract is stated once for every type, and
    // has no instances.
    if is_ident(source.get(close + 1), "contract") {
        return Ok(None);
    }
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
    let parameters_close = matching(source, parameters_open).ok_or_else(unterminated)?;
    let parameters = parameter_names(source, parameters_open, parameters_close);
    let mut clauses_open = parameters_close;
    while source
        .get(clauses_open)
        .is_some_and(|(token, _)| *token != Token::LBrace && *token != Token::Semicolon)
    {
        clauses_open += 1;
    }
    if source.get(clauses_open).map(|(token, _)| token) != Some(&Token::LBrace) {
        return Err(error_at(position, "a generic method states its contract"));
    }
    let constant = is_ident(source.get(parameters_close + 1), "const");
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
            parameters,
            constant,
        },
    )))
}

/// The name each parameter between `(` at `open` and `)` at `close`
/// declares: the word ending it, `None` for one ending otherwise.
fn parameter_names(source: &[Spanned], open: usize, close: usize) -> Vec<Option<String>> {
    let mut names = Vec::new();
    let mut depth = 0i32;
    let mut last = None;
    let mut empty = true;
    for (token, _) in &source[open + 1..close] {
        match token {
            Token::Comma if depth == 0 => {
                names.push(last.take());
                empty = true;
                continue;
            }
            Token::LParen | Token::LBracket | Token::LessThan => depth += 1,
            Token::RParen | Token::RBracket | Token::GreaterThan => depth -= 1,
            _ => {}
        }
        empty = false;
        last = match token {
            Token::Ident(word) if depth == 0 => Some(word.clone()),
            _ => None,
        };
    }
    // `()` and `(void)` declare no parameter.
    if !empty && !(names.is_empty() && last.as_deref() == Some("void")) {
        names.push(last);
    }
    names
}

/// A template parameter: a type, or a `uint64` value.
pub(super) struct TemplateParameter {
    pub(super) name: String,
    pub(super) value: bool,
}

/// The template parameters between `<` at `open` and `>` at `close`, each
/// `class T` or `typename T`, or a value `std::size_t N`, `size_t N` or
/// `unsigned long N`.
pub(super) fn template_parameters(
    source: &[Spanned],
    open: usize,
    close: usize,
) -> Option<Vec<TemplateParameter>> {
    let mut parameters = Vec::<TemplateParameter>::new();
    let mut at = open + 1;
    while at < close {
        let word = |offset: usize, word: &str| is_ident(source.get(at + offset), word);
        let (value, kind) = if word(0, "class") || word(0, "typename") || word(0, "size_t") {
            (word(0, "size_t"), 1)
        } else if word(0, "unsigned") && word(1, "long") {
            (true, 2)
        } else if word(0, "std")
            && source.get(at + 1).map(|(token, _)| token) == Some(&Token::ColonColon)
            && word(2, "size_t")
        {
            (true, 3)
        } else {
            return None;
        };
        at += kind;
        let Some((Token::Ident(name), _)) = source.get(at) else {
            return None;
        };
        if parameters.iter().any(|parameter| &parameter.name == name) {
            return None;
        }
        parameters.push(TemplateParameter {
            name: name.clone(),
            value,
        });
        at += 1;
        if at < close {
            if source[at].0 != Token::Comma {
                return None;
            }
            at += 1;
        }
    }
    (!parameters.is_empty()).then_some(parameters)
}

/// The instance block of the generic method block at `start` at
/// `arguments`: `extern` and its head and clauses with each type parameter
/// spelled as its argument, `unsigned long` as two words and `std::byte`
/// as a path, each value parameter as its `uint64` literal, and each
/// parameter renamed to the instance's `parameters`.
fn instance(
    source: &[Spanned],
    start: usize,
    block: &Block,
    arguments: &[String],
    parameters: &[String],
) -> Result<Vec<Spanned>, ClickError> {
    let position = source[start].1.clone();
    let mut substitution = BTreeMap::new();
    let mut values = BTreeMap::new();
    for (parameter, argument) in block.names.iter().zip(arguments) {
        if !parameter.value {
            substitution.insert(&parameter.name, argument);
            continue;
        }
        let value = argument.parse::<u64>().map_err(|_| {
            error_at(
                &position,
                format!(
                    "the instance's argument `{argument}` for `{}` is not an extent",
                    parameter.name
                ),
            )
        })?;
        // Clang prints an extent in a template argument list as a number.
        let (printed, _) = tokenizer::tokenize(argument, None)?;
        values.insert(parameter.name.as_str(), (value, printed));
    }
    // The indices inside a template argument list, `Buf<T, N>`, where a
    // value is written as Clang prints it.
    let plain = source[..=block.clauses_end]
        .iter()
        .map(|(token, _)| token.clone())
        .collect::<Vec<_>>();
    let mut in_arguments = BTreeSet::new();
    if !values.is_empty() {
        for at in block.head_start..block.clauses_end {
            if matches!(plain[at], Token::Ident(_))
                && plain[at + 1] == Token::LessThan
                && let Some((_, end)) =
                    super::cpp_syntax::template_arguments_at(&plain, at + 1, true)
            {
                in_arguments.extend(at + 2..end);
            }
        }
    }
    // A head restates its declaration's parameter names, which an instance
    // may name otherwise; a count that differs is the signature check's.
    let renaming = if block.parameters.len() == parameters.len() {
        block
            .parameters
            .iter()
            .zip(parameters)
            .filter_map(|(generic, instance)| {
                generic
                    .as_ref()
                    .filter(|generic| *generic != instance)
                    .map(|generic| (generic.as_str(), instance.as_str()))
            })
            .collect::<BTreeMap<_, _>>()
    } else {
        BTreeMap::new()
    };
    let mut tokens = vec![(Token::Ident("extern".into()), position.clone())];
    // A pure virtual method's generic block is already `extern`.
    let head_start =
        block.head_start + usize::from(is_ident(source.get(block.head_start), "extern"));
    for (at, (token, position)) in source
        .iter()
        .enumerate()
        .take(block.clauses_end + 1)
        .skip(head_start)
    {
        // A member or path segment of a parameter's spelling is not the
        // parameter.
        let member = matches!(
            source.get(at.wrapping_sub(1)).map(|(token, _)| token),
            Some(Token::Dot | Token::Arrow | Token::ColonColon)
        );
        match token {
            Token::Ident(word) if !member && values.contains_key(word.as_str()) => {
                let (value, printed) = &values[word.as_str()];
                if in_arguments.contains(&at) {
                    tokens.extend(
                        printed
                            .iter()
                            .map(|token| (token.clone(), position.clone())),
                    );
                } else {
                    tokens.push((Token::UInt64Number(*value), position.clone()));
                }
            }
            Token::Ident(word) if substitution.contains_key(word) => {
                for (index, part) in substitution[word].split("::").enumerate() {
                    if index > 0 {
                        tokens.push((Token::ColonColon, position.clone()));
                    }
                    for word in part.split_whitespace() {
                        tokens.push((Token::Ident(word.to_string()), position.clone()));
                    }
                }
            }
            Token::Ident(word) if !member && renaming.contains_key(word.as_str()) => {
                tokens.push((
                    Token::Ident(renaming[word.as_str()].into()),
                    position.clone(),
                ));
            }
            Token::Ident(word)
                if !member
                    && renaming.values().any(|name| name == word)
                    && !renaming.contains_key(word.as_str()) =>
            {
                return Err(error_at(
                    position,
                    format!(
                        "the instance names a parameter `{word}`, which the generic method's \
                         contract already uses; rename that parameter in the contract"
                    ),
                ));
            }
            token => tokens.push((token.clone(), position.clone())),
        }
    }
    Ok(tokens)
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

#[cfg(test)]
mod tests {
    use super::*;

    fn expand(source: &str, generic: &[&str], arguments: &[&str], parameters: &[&str]) -> String {
        let (tokens, positions) = tokenizer::tokenize(source, None).unwrap();
        let generic_name = crate::languages::cpp::names::path_name(generic);
        // The instance's receiver is `const` when the source's last head is.
        let constant = source
            .rsplit("template<")
            .next()
            .is_some_and(|head| head.split('{').next().unwrap().ends_with(") const "));
        let instances = BTreeMap::from([(
            generic_name,
            BTreeMap::from([(
                (
                    constant,
                    arguments.iter().map(|a| a.to_string()).collect::<Vec<_>>(),
                ),
                parameters.iter().map(|p| p.to_string()).collect::<Vec<_>>(),
            )]),
        )]);
        let (tokens, _, written) = expand_generic_methods(tokens, positions, &instances).unwrap();
        let start = *written.iter().next().unwrap();
        tokens[start..]
            .iter()
            .map(|token| match token {
                Token::Ident(word) => word.clone(),
                token => token.describe(),
            })
            .collect::<Vec<_>>()
            .join(" ")
    }

    // An instance's parameters take its own names by position, and a
    // member of the same spelling keeps its name; `std::byte` is written
    // as a path.
    #[test]
    fn an_instance_takes_its_parameter_names_and_spells_its_arguments() {
        let written = expand(
            "template<class T> void Cell<T>::set(T v) { ensures this->v == v; }",
            &["Cell<T>", "set"],
            &["std::byte"],
            &["__value"],
        );
        assert_eq!(
            written,
            "extern void Cell `<` std `::` byte `>` `::` set `(` std `::` byte __value `)` `{` \
             ensures this `->` v `==` __value `;` `}`"
        );
    }

    // A value parameter is an extent: a `uint64` literal in the contract,
    // and a number as Clang prints it in the instance's path.
    #[test]
    fn an_instance_writes_an_extent_as_a_literal() {
        let written = expand(
            "template<class T, unsigned long N> unsigned long Buf<T, N>::get(unsigned long i) \
             const { requires i < N; ensures result == N * sizeof(T); }",
            &["Buf<T, N>", "get"],
            &["int", "4"],
            &["i"],
        );
        assert_eq!(
            written,
            "extern unsigned long Buf `<` int `,` number `4` `>` `::` get `(` unsigned long i \
             `)` const `{` requires i `<` uint64 number `4u64` `;` ensures result `==` \
             uint64 number `4u64` `*` sizeof `(` int `)` `;` `}`"
        );
    }

    // Overloads of a method are told apart by their receiver's constness:
    // a `const` instance is written from the `const` head.
    #[test]
    fn a_const_instance_is_written_from_the_const_overload() {
        let written = expand(
            "template<class T> T& Box<T>::get() { ensures &result == &this->v; } \
             template<class T> const T& Box<T>::get() const { ensures &result == &this->v; }",
            &["Box<T>", "get"],
            &["int"],
            &[],
        );
        assert_eq!(
            written,
            "extern const int `&` Box `<` int `>` `::` get `(` `)` const `{` ensures `&` result \
             `==` `&` this `->` v `;` `}`"
        );
    }
}
