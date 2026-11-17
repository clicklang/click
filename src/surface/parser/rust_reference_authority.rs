//! Authority that a Rust reference parameter's type grants, written into the
//! sidecar's tokens before it is parsed.
//!
//! In safe Rust, holding `x: &mut T` means holding the only live access path
//! to `*x` for the call, and `x: &T` means reading `*x` while nothing writes
//! it. A function's contract therefore holds that memory without a clause:
//!
//! - `x: &mut T` owns `*x`, `x: &mut [T]` owns `x[0..x.len()]`, and
//!   `x: &mut [T; N]` owns `x[0..N]`;
//! - `x: &T`, `x: &[T]` and `x: &[T; N]` view the same.
//!
//! The derived clause is exactly the one a sidecar would write, so the callee
//! is still checked against it and every caller still has to hold it.
//!
//! A sidecar that writes its own `owns`, `views`, `consumes` or `produces`
//! clause naming the parameter states that parameter's authority itself, and
//! nothing is derived for it. A narrower clause is a stronger guarantee to
//! the caller, such as `views parent.right` for a field the callee does not
//! write. A clause that exceeds the type is refused: `owns` through a shared
//! reference claims more than `&T` gives.
//!
//! The rule covers free functions and inherent methods' parameters whose
//! referent is a scalar, a slice or array of scalars, or a crate struct of
//! scalar fields. Receivers, trait methods and their implementations (whose
//! object the trait-object rule holds), generic functions and their
//! instances, `extern` and `contract` declarations, and other referent types
//! keep their written clauses only.

use super::rust_trait_objects::{Spanned, at, error_at, ident, is_ident, matching, split_clauses};
use super::*;
use crate::languages::interface::RecordLayout;

/// What a reference parameter's type grants.
#[derive(Clone, Debug, Eq, PartialEq)]
enum Referent {
    /// One value, `*x`.
    Value,
    /// A slice's elements, `x[0..x.len()]`.
    Slice,
    /// A fixed array's elements, `x[0..N]`, with the length's tokens.
    Array(Vec<Token>),
}

/// A parameter whose type grants authority over its referent.
struct ReferenceParameter {
    name: String,
    mutable: bool,
    referent: Referent,
    position: SourcePosition,
}

pub(super) fn derive_reference_authority(
    tokens: Vec<Token>,
    positions: Vec<SourcePosition>,
    struct_layouts: &BTreeMap<String, RecordLayout>,
    enum_types: &BTreeMap<String, crate::kernel::TypeParameterName>,
) -> Result<(Vec<Token>, Vec<SourcePosition>), ClickError> {
    let source: Vec<Spanned> = tokens.into_iter().zip(positions).collect();
    let mut output = Vec::with_capacity(source.len());
    let mut index = 0;
    while index < source.len() {
        // A trait block and a trait implementation hold their object by the
        // trait-object rule; a generic `impl` is written out at its instances.
        if (is_ident(source.get(index), "trait") || is_ident(source.get(index), "impl"))
            && !inherent_impl_at(&source, index)
            && let Some(open) = (index..source.len())
                .find(|&at| matches!(source[at].0, Token::LBrace | Token::Semicolon))
                .filter(|&at| source[at].0 == Token::LBrace)
            && let Some(close) = matching(&source, open)
        {
            output.extend(source[index..=close].iter().cloned());
            index = close + 1;
            continue;
        }
        let declared_elsewhere = index > 0
            && (is_ident(source.get(index - 1), "extern")
                || is_ident(source.get(index - 1), "contract"));
        if is_ident(source.get(index), "fn")
            && !declared_elsewhere
            && let Some(next) =
                rewrite_function(&source, index, struct_layouts, enum_types, &mut output)?
        {
            index = next;
            continue;
        }
        output.push(source[index].clone());
        index += 1;
    }
    Ok(output.into_iter().unzip())
}

/// `impl Type {`: an inherent `impl` block, which names no trait and no
/// type parameters.
fn inherent_impl_at(source: &[Spanned], index: usize) -> bool {
    if !is_ident(source.get(index), "impl") {
        return false;
    }
    let mut at = index + 1;
    while let Some((token, _)) = source.get(at) {
        match token {
            Token::Ident(word) if word == "for" => return false,
            Token::Ident(_) | Token::ColonColon => at += 1,
            Token::LBrace => return true,
            _ => return false,
        }
    }
    false
}

/// Writes the `fn` item at `index` with the clauses its reference
/// parameters' types grant, returning the index after its clause block; or
/// `None`, with nothing written, for an item the rule does not cover.
fn rewrite_function(
    source: &[Spanned],
    index: usize,
    struct_layouts: &BTreeMap<String, RecordLayout>,
    enum_types: &BTreeMap<String, crate::kernel::TypeParameterName>,
    output: &mut Vec<Spanned>,
) -> Result<Option<usize>, ClickError> {
    // The name, a plain path: a generic function and a written instance
    // name type arguments with `<`.
    let mut after_name = index + 1;
    if !matches!(source.get(after_name), Some((Token::Ident(_), _))) {
        return Ok(None);
    }
    after_name += 1;
    while source.get(after_name).map(|(token, _)| token) == Some(&Token::ColonColon) {
        if !matches!(source.get(after_name + 1), Some((Token::Ident(_), _))) {
            return Ok(None);
        }
        after_name += 2;
    }
    if source.get(after_name).map(|(token, _)| token) != Some(&Token::LParen) {
        return Ok(None);
    }
    let Some(list_close) = matching(source, after_name) else {
        return Ok(None);
    };
    let Some(body_open) = (list_close..source.len())
        .find(|&at| matches!(source[at].0, Token::LBrace | Token::Semicolon))
        .filter(|&at| source[at].0 == Token::LBrace)
    else {
        return Ok(None);
    };
    let body_close = matching(source, body_open)
        .ok_or_else(|| error_at(&source[body_open].1, "unterminated `fn` contract"))?;
    let parameters = reference_parameters(
        &source[after_name + 1..list_close],
        struct_layouts,
        enum_types,
    );
    if parameters.is_empty() {
        return Ok(None);
    }
    let clauses = split_clauses(&source[body_open + 1..body_close]);
    let mut derived = Vec::new();
    for parameter in &parameters {
        let mut written = false;
        for clause in clauses.iter().filter(|clause| resource_clause(clause)) {
            if !names(clause, &parameter.name) {
                continue;
            }
            written = true;
            if !parameter.mutable
                && let Some(position) = owned_place_of(clause, &parameter.name)
            {
                return Err(error_at(
                    position,
                    format!(
                        "`{name}` is a shared reference, which grants `views` of what it \
                         refers to, not `owns`; take `&mut` or write `views`",
                        name = parameter.name
                    ),
                ));
            }
        }
        if !written {
            derived.extend(clause_for(parameter));
        }
    }
    output.extend(source[index..=body_open].iter().cloned());
    output.extend(derived);
    output.extend(source[body_open + 1..=body_close].iter().cloned());
    Ok(Some(body_close + 1))
}

/// The parameters, in a `fn` head's list, whose type grants authority.
fn reference_parameters(
    list: &[Spanned],
    struct_layouts: &BTreeMap<String, RecordLayout>,
    enum_types: &BTreeMap<String, crate::kernel::TypeParameterName>,
) -> Vec<ReferenceParameter> {
    let mut parameters = Vec::new();
    let mut depth = 0i32;
    let mut start = 0;
    for (at, (token, _)) in list.iter().enumerate() {
        match token {
            Token::LParen | Token::LBracket | Token::LessThan => depth += 1,
            Token::RParen | Token::RBracket | Token::GreaterThan => depth -= 1,
            Token::Comma if depth == 0 => {
                parameters.extend(reference_parameter(
                    &list[start..at],
                    struct_layouts,
                    enum_types,
                ));
                start = at + 1;
            }
            _ => {}
        }
    }
    parameters.extend(reference_parameter(
        &list[start..],
        struct_layouts,
        enum_types,
    ));
    parameters
}

/// `name: &'a mut T` for a referent the rule covers.
fn reference_parameter(
    tokens: &[Spanned],
    struct_layouts: &BTreeMap<String, RecordLayout>,
    enum_types: &BTreeMap<String, crate::kernel::TypeParameterName>,
) -> Option<ReferenceParameter> {
    let [
        (Token::Ident(name), position),
        (Token::Colon, _),
        (Token::Amp, _),
        rest @ ..,
    ] = tokens
    else {
        return None;
    };
    if name == "self" {
        return None;
    }
    let rest = match rest {
        [(Token::Lifetime(_), _), rest @ ..] => rest,
        rest => rest,
    };
    let (mutable, rest) = match rest {
        [(Token::Ident(word), _), rest @ ..] if word == "mut" => (true, rest),
        rest => (false, rest),
    };
    let referent = match rest {
        [(Token::Ident(scalar), _)] if rust_syntax::rust_scalar_type(scalar).is_some() => {
            Referent::Value
        }
        [
            (Token::LBracket, _),
            (Token::Ident(scalar), _),
            (Token::RBracket, _),
        ] if rust_syntax::rust_scalar_type(scalar).is_some() => Referent::Slice,
        [
            (Token::LBracket, _),
            (Token::Ident(scalar), _),
            (Token::Semicolon, _),
            length @ ..,
            (Token::RBracket, _),
        ] if rust_syntax::rust_scalar_type(scalar).is_some() && !length.is_empty() => {
            Referent::Array(length.iter().map(|(token, _)| token.clone()).collect())
        }
        path => {
            let segments = path
                .iter()
                .enumerate()
                .map(|(at, (token, _))| match (at % 2, token) {
                    (0, Token::Ident(segment)) => Some(Some(segment.as_str())),
                    (1, Token::ColonColon) => Some(None),
                    _ => None,
                })
                .collect::<Option<Vec<_>>>()?
                .into_iter()
                .flatten()
                .collect::<Vec<_>>();
            if segments.is_empty() || path.len() % 2 == 0 {
                return None;
            }
            let struct_name = crate::languages::rust::names::path_name(&segments);
            if enum_types.contains_key(&struct_name) {
                return None;
            }
            scalar_record(struct_layouts.get(&struct_name)?).then_some(Referent::Value)?
        }
    };
    Some(ReferenceParameter {
        name: name.clone(),
        mutable,
        referent,
        position: position.clone(),
    })
}

/// A struct whose every field is one scalar value: `*x` names all of it.
fn scalar_record(layout: &RecordLayout) -> bool {
    !layout.fields().is_empty()
        && layout.fields().values().all(|field| {
            !field.interface_type().is_pointer()
                && field.struct_name().is_none()
                && field.enum_name().is_none()
                && field.union_name().is_none()
                && field.function_pointer_signature().is_none()
                && field.array_element_width().is_none()
                && field.array_shape().is_none()
        })
}

/// A clause that holds a resource: memory or a declared resource.
fn resource_clause(clause: &[Spanned]) -> bool {
    clause.iter().any(|(token, _)| {
        matches!(token, Token::Ident(word)
            if matches!(word.as_str(), "owns" | "views" | "consumes" | "produces"))
    })
}

/// Whether `clause` names `parameter` anywhere.
fn names(clause: &[Spanned], parameter: &str) -> bool {
    clause
        .iter()
        .any(|(token, _)| matches!(token, Token::Ident(word) if word == parameter))
}

/// The position of an `owns` of a place reached through `parameter`, `owns
/// *x`, `owns x.f` or `owns x[a..b]`, in `clause`.
fn owned_place_of<'a>(clause: &'a [Spanned], parameter: &str) -> Option<&'a SourcePosition> {
    clause.windows(3).find_map(|window| {
        let [(Token::Ident(owns), position), first, second] = window else {
            return None;
        };
        if owns != "owns" {
            return None;
        }
        let through = match (&first.0, &second.0) {
            (Token::Star, Token::Ident(name)) => name == parameter,
            (Token::Ident(name), Token::Dot | Token::LBracket) => name == parameter,
            _ => false,
        };
        through.then_some(position)
    })
}

/// The clause the parameter's type grants: `owns *x;` or `views x[0..x.len()];`.
fn clause_for(parameter: &ReferenceParameter) -> Vec<Spanned> {
    let access = if parameter.mutable { "owns" } else { "views" };
    let mut tokens = vec![ident(access)];
    match &parameter.referent {
        Referent::Value => {
            tokens.extend([Token::Star, ident(&parameter.name)]);
        }
        Referent::Slice => tokens.extend([
            ident(&parameter.name),
            Token::LBracket,
            Token::Number(0),
            Token::DotDot,
            ident(&parameter.name),
            Token::Dot,
            ident("len"),
            Token::LParen,
            Token::RParen,
            Token::RBracket,
        ]),
        Referent::Array(length) => {
            tokens.extend([
                ident(&parameter.name),
                Token::LBracket,
                Token::Number(0),
                Token::DotDot,
                Token::LParen,
            ]);
            tokens.extend(length.iter().cloned());
            tokens.extend([Token::RParen, Token::RBracket]);
        }
    }
    tokens.push(Token::Semicolon);
    at(&parameter.position, tokens)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The sidecar `source` with its reference parameters' authority
    /// derived, as text, one token per word.
    fn derived(source: &str) -> Result<String, ClickError> {
        let (tokens, positions) = tokenize(source, None)?;
        let (tokens, _) =
            derive_reference_authority(tokens, positions, &BTreeMap::new(), &BTreeMap::new())?;
        Ok(tokens
            .iter()
            .map(|token| match token {
                Token::Ident(word) => word.clone(),
                Token::Number(value) => value.to_string(),
                Token::Star => "*".into(),
                Token::Dot => ".".into(),
                Token::DotDot => "..".into(),
                Token::Semicolon => ";".into(),
                Token::LBrace => "{".into(),
                Token::RBrace => "}".into(),
                Token::LParen => "(".into(),
                Token::RParen => ")".into(),
                Token::LBracket => "[".into(),
                Token::RBracket => "]".into(),
                Token::Colon => ":".into(),
                Token::Comma => ",".into(),
                Token::Amp => "&".into(),
                Token::EqualEqual => "==".into(),
                Token::LessThan => "<".into(),
                Token::GreaterThan => ">".into(),
                other => format!("{other:?}"),
            })
            .collect::<Vec<_>>()
            .join(" "))
    }

    #[test]
    fn a_reference_parameter_holds_its_referent() {
        assert_eq!(
            derived("fn f(x: &mut i32, y: &u8, n: i32) { ensures *x == n; }").unwrap(),
            "fn f ( x : & mut i32 , y : & u8 , n : i32 ) { owns * x ; views * y ; \
             ensures * x == n ; }"
        );
    }

    #[test]
    fn a_slice_parameter_holds_its_elements() {
        assert_eq!(
            derived("fn f(a: &'s mut [u32], b: &[u8]) { }").unwrap(),
            "fn f ( a : & Lifetime(\"s\") mut [ u32 ] , b : & [ u8 ] ) { owns a [ 0 .. a . len \
             ( ) ] ; views b [ 0 .. b . len ( ) ] ; }"
        );
    }

    #[test]
    fn an_array_parameter_holds_its_elements() {
        assert_eq!(
            derived("fn f(a: &mut [u32; 4], b: &[u8; 1 + 2]) { }").unwrap(),
            "fn f ( a : & mut [ u32 ; 4 ] , b : & [ u8 ; 1 Plus 2 ] ) { owns a \
             [ 0 .. ( 4 ) ] ; views b [ 0 .. ( 1 Plus 2 ) ] ; }"
        );
    }

    #[test]
    fn a_written_clause_states_its_parameter_s_authority() {
        // Narrower than the type: the callee promises not to write `x`.
        assert_eq!(
            derived("fn f(x: &mut i32, y: &mut i32) { views *x; }").unwrap(),
            "fn f ( x : & mut i32 , y : & mut i32 ) { owns * y ; views * x ; }"
        );
        let unchanged = "fn f ( b : & [ u8 ] ) { views b [ 0 .. 4 ] ; }";
        assert_eq!(derived(unchanged).unwrap(), unchanged);
    }

    #[test]
    fn owning_through_a_shared_reference_is_refused() {
        let error = derived("fn f(x: &i32) { owns *x; }").unwrap_err();
        assert!(error.to_string().contains("grants `views`"), "{error}");
        assert!(derived("fn f(b: &[u8]) { owns b[0..1]; }").is_err());
    }

    #[test]
    fn declarations_the_rule_does_not_cover_are_unchanged() {
        for source in [
            "extern fn f ( x : & mut i32 ) { }",
            "contract fn f ( x : & mut i32 ) { }",
            "fn f < T > ( x : & mut T ) { }",
            "fn f ( x : & mut Unknown ) { }",
            "fn f ( x : & mut & mut i32 ) { }",
            "trait S { fn f ( & mut self , x : & mut i32 ) ; }",
            "impl S for T { fn f ( & mut self , x : & mut i32 ) { } }",
        ] {
            assert_eq!(derived(source).unwrap(), source, "{source}");
        }
        assert_eq!(
            derived("impl S { fn f(&mut self, x: &mut i32) { } }").unwrap(),
            "impl S { fn f ( & mut self , x : & mut i32 ) { owns * x ; } }"
        );
    }
}
