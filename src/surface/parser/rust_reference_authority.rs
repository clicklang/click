//! Authority that a Rust reference parameter's type grants, written into the
//! sidecar's tokens before it is parsed.
//!
//! In safe Rust, holding `x: &mut T` means holding the only live access path
//! to `*x` for the call, and `x: &T` means reading `*x` while nothing writes
//! it. A function's contract therefore holds that memory without a clause:
//!
//! - `x: &mut T` owns `*x` and `x: &T` views it, for a scalar, an `Option`
//!   of one, a crate enum, or a struct of scalar (or such struct) fields; an
//!   inherent method's `&mut self` and `&self` likewise;
//! - `x: &mut [T]` and `x: &[T]` own or view `x[0..x.len()]`, and
//!   `x: &[T; N]` views `x[0..N]`;
//! - a box moved in, `b: Box<R>`, consumes `allocation(b, sizeof(R))` and
//!   `*b`; a box moved out, `-> Box<R>`, produces the same of `result`.
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
//! Trait methods and their implementations (whose object the trait-object
//! rule holds), generic functions and their instances, `extern` and
//! `contract` declarations, options of boxes, structs holding boxes,
//! pointers or arrays, and other types keep their written clauses only.

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
    grant: Grant,
    position: SourcePosition,
}

/// What a parameter's (or the result's) type grants.
enum Grant {
    /// A reference: `owns` (`&mut`) or `views` (`&`) of its referent.
    Reference { mutable: bool, referent: Referent },
    /// A box moved in or out, `Box<R>`: its allocation of `sizeof(R)` and
    /// the record in it, consumed from the caller or produced for it.
    Box { record: Vec<Token> },
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
    // The type an inherent `impl` block's receivers refer to, until the
    // block's closing brace.
    let mut receiver: Option<(Vec<Token>, usize)> = None;
    while index < source.len() {
        if receiver.as_ref().is_some_and(|(_, close)| index > *close) {
            receiver = None;
        }
        if inherent_impl_at(&source, index)
            && let Some(open) = (index..source.len()).find(|&at| source[at].0 == Token::LBrace)
            && let Some(close) = matching(&source, open)
        {
            let path = source[index + 1..open]
                .iter()
                .map(|(token, _)| token.clone())
                .collect();
            receiver = Some((path, close));
            output.extend(source[index..=open].iter().cloned());
            index = open + 1;
            continue;
        }
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
            && let Some(next) = rewrite_function(
                &source,
                index,
                Types {
                    structs: struct_layouts,
                    enums: enum_types,
                    receiver: receiver.as_ref().map(|(path, _)| path.as_slice()),
                },
                &mut output,
            )?
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
    types: Types<'_>,
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
    let mut parameters = reference_parameters(&source[after_name + 1..list_close], types);
    // A box result, `-> Box<R>`, is produced for the caller.
    if source.get(list_close + 1).map(|(token, _)| token) == Some(&Token::Arrow)
        && let Some(record) = boxed_record(
            &source[list_close + 2..body_open]
                .iter()
                .take_while(|(token, _)| !matches!(token, Token::Ident(word) if word == "diverges"))
                .cloned()
                .collect::<Vec<_>>(),
            types,
        )
    {
        parameters.push(ReferenceParameter {
            name: "result".into(),
            grant: Grant::Box { record },
            position: source[list_close + 1].1.clone(),
        });
    }
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
            if let Grant::Reference { mutable: false, .. } = parameter.grant
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

/// The struct, enum and receiver types a sidecar's parameters may name.
#[derive(Clone, Copy)]
struct Types<'a> {
    structs: &'a BTreeMap<String, RecordLayout>,
    enums: &'a BTreeMap<String, crate::kernel::TypeParameterName>,
    /// The type of `self` in an inherent `impl` block.
    receiver: Option<&'a [Token]>,
}

/// The parameters, in a `fn` head's list, whose type grants authority.
fn reference_parameters(list: &[Spanned], types: Types<'_>) -> Vec<ReferenceParameter> {
    let mut parameters = Vec::new();
    let mut depth = 0i32;
    let mut start = 0;
    for (at, (token, _)) in list.iter().enumerate() {
        match token {
            Token::LParen | Token::LBracket | Token::LessThan => depth += 1,
            Token::RParen | Token::RBracket | Token::GreaterThan => depth -= 1,
            Token::Comma if depth == 0 => {
                parameters.extend(reference_parameter(&list[start..at], types));
                start = at + 1;
            }
            _ => {}
        }
    }
    parameters.extend(reference_parameter(&list[start..], types));
    parameters
}

/// `name: &'a mut T`, `&self`, `&mut self` or `name: Box<R>` for a type the
/// rule covers.
fn reference_parameter(tokens: &[Spanned], types: Types<'_>) -> Option<ReferenceParameter> {
    // A receiver, `&'a mut self`, refers to a value of the block's type.
    if let Some((self_token, prefix)) = tokens.split_last()
        && matches!(&self_token.0, Token::Ident(word) if word == "self")
        && let [(Token::Amp, position), rest @ ..] = prefix
    {
        let rest = match rest {
            [(Token::Lifetime(_), _), rest @ ..] => rest,
            rest => rest,
        };
        let mutable = match rest {
            [] => false,
            [(Token::Ident(word), _)] if word == "mut" => true,
            _ => return None,
        };
        let receiver = types.receiver?;
        let referent = record_referent(receiver, types)?;
        return Some(ReferenceParameter {
            name: "self".into(),
            grant: Grant::Reference { mutable, referent },
            position: position.clone(),
        });
    }
    let [(Token::Ident(name), position), (Token::Colon, _), rest @ ..] = tokens else {
        return None;
    };
    if name == "self" {
        return None;
    }
    if let Some(record) = boxed_record(rest, types) {
        return Some(ReferenceParameter {
            name: name.clone(),
            grant: Grant::Box { record },
            position: position.clone(),
        });
    }
    let [(Token::Amp, _), rest @ ..] = rest else {
        return None;
    };
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
        // An option of a scalar is one value of the library's `Option<T>`.
        [
            (Token::Ident(option), _),
            (Token::LessThan, _),
            (Token::Ident(scalar), _),
            (Token::GreaterThan, _),
        ] if option == "Option" && rust_syntax::rust_scalar_type(scalar).is_some() => {
            Referent::Value
        }
        path => record_referent(
            &path
                .iter()
                .map(|(token, _)| token.clone())
                .collect::<Vec<_>>(),
            types,
        )?,
    };
    Some(ReferenceParameter {
        name: name.clone(),
        grant: Grant::Reference { mutable, referent },
        position: position.clone(),
    })
}

/// The importer name of a plain path type, `a::b::C`.
fn path_type_name(path: &[Token]) -> Option<String> {
    let segments = path
        .iter()
        .enumerate()
        .map(|(at, token)| match (at % 2, token) {
            (0, Token::Ident(segment)) => Some(Some(segment.as_str())),
            (1, Token::ColonColon) => Some(None),
            _ => None,
        })
        .collect::<Option<Vec<_>>>()?
        .into_iter()
        .flatten()
        .collect::<Vec<_>>();
    if segments.is_empty() || path.len().is_multiple_of(2) {
        return None;
    }
    Some(crate::languages::rust::names::path_name(&segments))
}

/// A crate enum, or a struct of scalar fields, at `path`: `*x` names all of
/// a value of it.
fn record_referent(path: &[Token], types: Types<'_>) -> Option<Referent> {
    let name = path_type_name(path)?;
    if types.enums.contains_key(&name) {
        return Some(Referent::Value);
    }
    scalar_record(types.structs.get(&name)?, types.structs).then_some(Referent::Value)
}

/// `Box<R>` for a struct `R` of scalar fields: the tokens of `R`.
fn boxed_record(tokens: &[Spanned], types: Types<'_>) -> Option<Vec<Token>> {
    let [
        (Token::Ident(boxed), _),
        (Token::LessThan, _),
        record @ ..,
        (Token::GreaterThan, _),
    ] = tokens
    else {
        return None;
    };
    if boxed != "Box" {
        return None;
    }
    let record = record
        .iter()
        .map(|(token, _)| token.clone())
        .collect::<Vec<_>>();
    let name = path_type_name(&record)?;
    scalar_record(types.structs.get(&name)?, types.structs).then_some(record)
}

/// A struct whose every field is one scalar value or an embedded struct of
/// them: `*x` names all of it.
fn scalar_record(layout: &RecordLayout, structs: &BTreeMap<String, RecordLayout>) -> bool {
    !layout.fields().is_empty()
        && layout.fields().values().all(|field| {
            !field.interface_type().is_pointer()
                && field.enum_name().is_none()
                && field.union_name().is_none()
                && field.function_pointer_signature().is_none()
                && field.array_element_width().is_none()
                && field.array_shape().is_none()
                && field.struct_name().is_none_or(|name| {
                    structs
                        .get(name)
                        .is_some_and(|inner| scalar_record(inner, structs))
                })
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

/// The clauses the parameter's type grants: `owns *x;`, `views
/// x[0..x.len()];`, or a box's `consumes allocation(b, sizeof(R)); consumes
/// *b;` (`produces` for the result).
fn clause_for(parameter: &ReferenceParameter) -> Vec<Spanned> {
    let name = || ident(&parameter.name);
    let mut tokens = Vec::new();
    match &parameter.grant {
        Grant::Box { record } => {
            let access = if parameter.name == "result" {
                "produces"
            } else {
                "consumes"
            };
            tokens.extend([
                ident(access),
                ident("allocation"),
                Token::LParen,
                name(),
                Token::Comma,
                ident("sizeof"),
                Token::LParen,
            ]);
            tokens.extend(record.iter().cloned());
            tokens.extend([
                Token::RParen,
                Token::RParen,
                Token::Semicolon,
                ident(access),
                Token::Star,
                name(),
            ]);
        }
        Grant::Reference { mutable, referent } => {
            tokens.push(ident(if *mutable { "owns" } else { "views" }));
            match referent {
                Referent::Value => tokens.extend([Token::Star, name()]),
                Referent::Slice => tokens.extend([
                    name(),
                    Token::LBracket,
                    Token::Number(0),
                    Token::DotDot,
                    name(),
                    Token::Dot,
                    ident("len"),
                    Token::LParen,
                    Token::RParen,
                    Token::RBracket,
                ]),
                Referent::Array(length) => {
                    tokens.extend([
                        name(),
                        Token::LBracket,
                        Token::Number(0),
                        Token::DotDot,
                        Token::LParen,
                    ]);
                    tokens.extend(length.iter().cloned());
                    tokens.extend([Token::RParen, Token::RBracket]);
                }
            }
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
        let cell = RecordLayout::from_explicit_fields(
            vec![(
                "value".into(),
                crate::languages::interface::InterfaceType::UInt32,
                0,
                4,
            )],
            4,
            4,
        )
        .unwrap();
        let path = |segments: &[&str]| crate::languages::rust::names::path_name(segments);
        let structs = BTreeMap::from([(path(&["m", "Cell"]), cell)]);
        let enums = BTreeMap::from([(
            path(&["m", "Shape"]),
            crate::kernel::TypeParameterName::intern(&path(&["m", "Shape"])),
        )]);
        let (tokens, positions) = tokenize(source, None)?;
        let (tokens, _) = derive_reference_authority(tokens, positions, &structs, &enums)?;
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
                Token::ColonColon => "::".into(),
                Token::Arrow => "->".into(),
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
    fn an_enum_or_option_reference_holds_one_value() {
        assert_eq!(
            derived("fn f(o: &mut Option<u32>, s: &m::Shape) { }").unwrap(),
            "fn f ( o : & mut Option < u32 > , s : & m :: Shape ) { owns * o ; views * s ; }"
        );
    }

    #[test]
    fn an_inherent_method_receiver_holds_its_value() {
        assert_eq!(
            derived("impl m::Cell { fn get(&self) -> u32 { } fn set(&mut self, v: u32) { } }")
                .unwrap(),
            "impl m :: Cell { fn get ( & self ) -> u32 { views * self ; } fn set ( & mut self \
             , v : u32 ) { owns * self ; } }"
        );
        // Outside the block, `self` names nothing the rule knows.
        let unchanged = "impl m :: Cell { } fn f ( & self ) { }";
        assert_eq!(derived(unchanged).unwrap(), unchanged);
    }

    #[test]
    fn a_box_moved_in_or_out_holds_its_allocation_and_record() {
        assert_eq!(
            derived("fn f(b: Box<m::Cell>) -> Box<m::Cell> { }").unwrap(),
            "fn f ( b : Box < m :: Cell > ) -> Box < m :: Cell > { consumes allocation ( b , \
             sizeof ( m :: Cell ) ) ; consumes * b ; produces allocation ( result , sizeof ( m \
             :: Cell ) ) ; produces * result ; }"
        );
        let written = "fn f ( b : Box < m :: Cell > ) { consumes * b ; }";
        assert_eq!(derived(written).unwrap(), written);
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
