//! The C++ spelling of a function head: qualified member names,
//! constructors, destructors, `operator` names, and the implicit `this` of a
//! member function, admitted when a `verifying` source is C++.

use super::*;

/// A declaration signature uses the same path as a contract head and the
/// canonical C++ parameter types. The lookup never relies on execution widths.
#[derive(Clone, Default)]
pub(in crate::surface) struct DeclarationSignatures(
    BTreeMap<SignatureKey, Option<DeclarationTarget>>,
);

#[derive(Clone)]
struct DeclarationTarget {
    key: String,
    written: String,
    addressable: bool,
}

#[derive(Clone, Eq, Ord, PartialEq, PartialOrd)]
struct SignatureKey {
    path: String,
    parameters: Vec<String>,
    constant: bool,
}

fn declaration_path_at(tokens: &[Token], start: usize) -> Option<(String, usize)> {
    let (segments, end) = cpp_path(tokens, start, true)?;
    lambda_path_at(tokens, end, &segments)
        .or_else(|| Some((crate::languages::cpp::names::path_name(&segments), end)))
}

fn signature_at(tokens: &[Token], start: usize) -> Option<(SignatureKey, usize)> {
    let (path, open) = declaration_path_at(tokens, start)?;
    if tokens.get(open) != Some(&Token::LParen) {
        return None;
    }
    let mut depth = 1;
    let first = open + 1;
    let close = tokens[first..].iter().position(|token| {
        match token {
            Token::LParen => depth += 1,
            Token::RParen => depth -= 1,
            _ => {}
        }
        depth == 0
    })? + first;
    let constant = matches!(tokens.get(close + 1), Some(Token::Ident(name)) if name == "const");
    let parameters = tokens[first..close].iter().map(Token::describe).collect();
    Some((
        SignatureKey {
            path,
            parameters,
            constant,
        },
        close + 1 + usize::from(constant),
    ))
}

impl DeclarationSignatures {
    pub(in crate::surface) fn insert(&mut self, signature: &str, key: &str, addressable: bool) {
        let Ok((tokens, _)) = super::tokenizer::tokenize(signature, None) else {
            return;
        };
        if let Some((reference, end)) = signature_at(&tokens, 0)
            && end == tokens.len()
        {
            self.0
                .entry(reference)
                .and_modify(|entry| *entry = None)
                .or_insert_with(|| {
                    Some(DeclarationTarget {
                        key: key.to_owned(),
                        written: signature.to_owned(),
                        addressable,
                    })
                });
        }
    }
}

impl Parser {
    pub(super) fn parse_termination_function_reference(&mut self) -> Result<String, ClickError> {
        if !self.verifies_cpp() {
            return self.expect_string("function name");
        }
        if let Some(Token::Ident(name) | Token::String(name)) = self.peek()
            && let Some(path) = crate::languages::cpp::names::cpp_display_name(name)
        {
            return Err(self.error(format!(
                "write the C++ function reference for `{path}` using its source name or signature"
            )));
        }
        if matches!(self.peek(), Some(Token::String(_))) {
            return self.expect_string("function name");
        }
        let (path, end) = declaration_path_at(&self.tokens, self.position)
            .ok_or_else(|| self.error("expected a C++ function reference"))?;
        if self.tokens.get(end) == Some(&Token::LParen) {
            return self
                .parse_cpp_signature_reference(false)
                .map(|(key, _)| key);
        }
        self.position = end;
        Ok(path)
    }

    pub(super) fn has_cpp_overloaded_address(&self) -> bool {
        declaration_path_at(&self.tokens, self.position + 1).is_some_and(|(path, end)| {
            self.cpp_overloads.contains_key(&path) && self.tokens.get(end) == Some(&Token::LParen)
        })
    }

    pub(super) fn parse_cpp_signature_reference(
        &mut self,
        address: bool,
    ) -> Result<(String, String), ClickError> {
        let Some((reference, end)) = signature_at(&self.tokens, self.position) else {
            return Err(self.error("expected a C++ function signature"));
        };
        let Some(Some(function)) = self.cpp_signatures.0.get(&reference) else {
            return Err(self.error(format!(
                "no unique C++ declaration for this signature of `{}`",
                crate::languages::display_source_names(&reference.path)
            )));
        };
        if address && !function.addressable {
            return Err(self.error("this C++ member function has no ordinary function pointer"));
        }
        self.position = end;
        Ok((function.key.clone(), function.written.clone()))
    }
}

/// A C++ head's declarator, resolved to the name the C++ importer gives the
/// declaration at its path: `Rec::m`, `Rec::Rec`, `Rec::~Rec`,
/// `Rec::operator+=`, `ns::f`, `Stored<long long>::Read`, `choose<true>`, and
/// a lambda at `caller.statement(0).call(0).argument(0)`.
pub(super) struct CppDeclarator {
    pub(super) name: String,
    /// The record of a non-static member function, whose implicit `this`
    /// the head does not write.
    pub(super) receiver: Option<String>,
    /// A constructor or destructor, which has no return type.
    pub(super) returnless: bool,
}

impl Parser {
    pub(super) fn verifies_cpp(&self) -> bool {
        self.language == SourceLanguage::Cpp
    }

    /// Whether a constructor or destructor declarator, which has no return
    /// type, starts here: `Rec::Rec(` or `Rec::~Rec(`.
    pub(super) fn cpp_returnless_declarator_follows(&self) -> bool {
        let mut index = self.position;
        let mut segments = Vec::new();
        loop {
            match self.tokens.get(index) {
                Some(Token::Ident(name)) => {
                    segments.push((false, name));
                    index += 1;
                    // A class template instance's arguments, `Stored<long long>`.
                    if self.tokens.get(index) == Some(&Token::LessThan) {
                        match template_arguments_at(&self.tokens, index, false) {
                            Some((_, end)) => index = end,
                            None => return false,
                        }
                    }
                }
                Some(Token::Tilde) => match self.tokens.get(index + 1) {
                    Some(Token::Ident(name)) => {
                        segments.push((true, name));
                        index += 2;
                    }
                    _ => return false,
                },
                _ => return false,
            }
            match self.tokens.get(index) {
                Some(Token::ColonColon) => index += 1,
                Some(Token::LParen) => break,
                _ => return false,
            }
        }
        let [.., (false, record), (_, member)] = segments.as_slice() else {
            return false;
        };
        record == member
    }

    /// Template arguments at `<`, as Clang prints them, `<long long, true>`.
    /// `None` when no `<` follows.
    fn parse_cpp_template_arguments(&mut self) -> Result<Option<String>, ClickError> {
        if self.peek() != Some(&Token::LessThan) {
            return Ok(None);
        }
        let Some((printed, end)) = template_arguments_at(&self.tokens, self.position, false) else {
            return Err(self.error(
                "C++ template arguments close with `>` before `(` or `::`, \
                 and spell types, values and `true` or `false`",
            ));
        };
        self.position = end;
        Ok(Some(printed))
    }

    /// A record type written by its C++ path, `std::span<int>`,
    /// `Stored<long long>` or `ns::Rec`, as its layout name, with the path
    /// consumed. `None`, with nothing consumed, for any other type, a single
    /// identifier included.
    pub(super) fn parse_cpp_record_type(&mut self) -> Option<String> {
        let mut segments = Vec::new();
        let mut index = self.position;
        loop {
            let Some(Token::Ident(name)) = self.tokens.get(index) else {
                return None;
            };
            index += 1;
            let mut segment = name.clone();
            if self.tokens.get(index) == Some(&Token::LessThan) {
                let (arguments, end) = template_arguments_at(&self.tokens, index, true)?;
                segment.push_str(&arguments);
                index = end;
            }
            segments.push(segment);
            if self.tokens.get(index) != Some(&Token::ColonColon) {
                break;
            }
            index += 1;
        }
        if segments.len() < 2 && !segments[0].contains('<') {
            return None;
        }
        let record = self.cpp_record(&segments.join("::"))?;
        self.position = index;
        Some(record)
    }

    /// Whether a C++ record type starts here, `Node` or `Stored<int>`, as a
    /// specification's binder may write one: `p: Node*`.
    pub(super) fn at_cpp_record_type(&mut self) -> bool {
        if !self.verifies_cpp() {
            return false;
        }
        if let Some(Token::Ident(name)) = self.tokens.get(self.position)
            && self.cpp_record(name).is_some()
        {
            return true;
        }
        let start = self.position;
        let record = self.parse_cpp_record_type().is_some();
        self.position = start;
        record
    }

    /// The layout name of the record a head's qualifier spells, `Rec` or
    /// `Stored<long long>`.
    fn cpp_record(&self, spelling: &str) -> Option<String> {
        if self.struct_layouts.contains_key(spelling) {
            return Some(spelling.to_string());
        }
        self.record_spellings.get(spelling).cloned()
    }

    /// The declarator of a C++ head, after its return type: its C++ path,
    /// named as the importer names the declaration at that path
    /// ([`crate::languages::cpp::names::path_name`]).
    pub(super) fn parse_cpp_declarator(
        &mut self,
        is_static: bool,
    ) -> Result<CppDeclarator, ClickError> {
        // Each segment, with the plain name of a record template instance.
        let mut path = Vec::new();
        let mut plain = Vec::new();
        // A namespace that shares a Click library module's name, as in
        // `list::append`, reaches here joined; its segments are as written.
        let written = self.expect_c_declaration_ident("function name")?;
        let mut segments = written.split("::").map(str::to_string).collect::<Vec<_>>();
        let first = segments.pop().expect("a name has a last segment");
        for segment in segments {
            path.push(segment.clone());
            plain.push(segment);
        }
        let mut arguments = self.parse_cpp_template_arguments()?;
        path.push(format!("{first}{}", arguments.clone().unwrap_or_default()));
        plain.push(first);
        let mut special_member = None;
        while self.peek() == Some(&Token::ColonColon) {
            self.position += 1;
            if self.peek() == Some(&Token::Tilde) {
                self.position += 1;
                let name = self.expect_ident("destructor name")?;
                let record = plain.last().expect("a path has a first segment");
                if &name != record {
                    return Err(self.error(format!(
                        "a destructor of `{record}` is named `{record}::~{record}`"
                    )));
                }
                path.push(format!("~{name}"));
                special_member = Some(true);
                break;
            }
            if self.peek_ident() == Some("operator") {
                self.position += 1;
                let (operator, tokens) = match (self.peek(), self.peek_next()) {
                    (Some(Token::Equal), _) => ("operator=", 1),
                    (Some(Token::Plus), Some(Token::Equal)) => ("operator+=", 2),
                    (Some(Token::Minus), Some(Token::Equal)) => ("operator-=", 2),
                    (Some(Token::LBracket), Some(Token::RBracket)) => ("operator[]", 2),
                    _ => {
                        return Err(self.error(
                            "the supported C++ operator methods are `operator=`, \
                             `operator+=`, `operator-=` and `operator[]`",
                        ));
                    }
                };
                self.position += tokens;
                path.push(operator.to_string());
                special_member = Some(false);
                break;
            }
            let segment = self.expect_ident("function name")?;
            arguments = self.parse_cpp_template_arguments()?;
            path.push(format!(
                "{segment}{}",
                arguments.clone().unwrap_or_default()
            ));
            plain.push(segment);
        }
        if special_member.is_none()
            && let Some((name, end)) = lambda_path_at(&self.tokens, self.position, &path)
        {
            if is_static {
                return Err(self.error("a lambda contract selects its written expression"));
            }
            self.position = end;
            return Ok(CppDeclarator {
                name,
                receiver: None,
                returnless: false,
            });
        }
        if plain
            .last()
            .is_some_and(|name| name.starts_with("(lambda#"))
        {
            return Err(self.error(
                "select a lambda by its written expression, such as `caller.statement(0).call(0).argument(0)`",
            ));
        }
        let name = crate::languages::cpp::names::path_name(&path);
        let qualifier = (path.len() >= 2).then(|| path[path.len() - 2].clone());
        let record = qualifier
            .as_deref()
            .and_then(|qualifier| self.cpp_record(qualifier));
        let returnless = match special_member {
            Some(destructor) => {
                if record.is_none() {
                    return Err(self.error(format!(
                        "`{}` is not a record of the verified source",
                        qualifier.unwrap_or_default()
                    )));
                }
                destructor
            }
            None => {
                // `static` marks only a member function, so its qualifier is
                // the record even when the program's layouts omit one whose
                // fields no verified code reads.
                if record.is_none() && !is_static {
                    return Ok(CppDeclarator {
                        name,
                        receiver: None,
                        returnless: false,
                    });
                }
                if is_static && qualifier.is_none() {
                    return Err(
                        self.error("`static` declares a static member function, written `Rec::f`")
                    );
                }
                plain.len() >= 2 && plain[plain.len() - 1] == plain[plain.len() - 2]
            }
        };
        if is_static && returnless {
            return Err(self.error("a constructor or destructor is not `static`"));
        }
        Ok(CppDeclarator {
            name,
            receiver: if is_static { None } else { record },
            returnless,
        })
    }
}

/// A C++ sidecar's references to functions by their C++ paths, written as
/// the importer names them: `&FeeFrac::EvaluateFeeDown`, the callee of
/// `step(FeeFrac::IsEmpty(...), ...)`, and the target of `executes
/// FeeFrac::EvaluateFeeDown(...)` each become one name, as a head's
/// declarator does. A single identifier is kept as written.
pub(super) fn rewrite_function_references(
    tokens: Vec<Token>,
    positions: Vec<SourcePosition>,
) -> (Vec<Token>, Vec<SourcePosition>) {
    let mut out_tokens = Vec::with_capacity(tokens.len());
    let mut out_positions = Vec::with_capacity(positions.len());
    let mut index = 0;
    while index < tokens.len() {
        let reference = match (
            index.checked_sub(1).map(|at| &tokens[at]),
            index.checked_sub(2).map(|at| &tokens[at]),
        ) {
            // An address, `&f`, follows an operator or a delimiter; a
            // reference return type, `int32& Cell::get()`, follows a type.
            (Some(Token::Amp), before) => (!matches!(
                before,
                None | Some(
                    Token::Ident(_)
                        | Token::GreaterThan
                        | Token::Star
                        | Token::Amp
                        | Token::RParen
                        | Token::RBracket
                        | Token::Semicolon
                        | Token::RBrace
                        | Token::LBrace
                )
            ))
            .then_some(false),
            (Some(Token::Ident(word)), _) if word == "executes" => Some(false),
            (Some(Token::LParen), Some(Token::Ident(word))) if word == "step" => Some(true),
            _ => None,
        };
        if let Some(allow_terminal_template) = reference
            && let Some((segments, end)) = cpp_path(&tokens, index, allow_terminal_template)
            && let Some((name, end)) = lambda_path_at(&tokens, end, &segments).or_else(|| {
                (segments.len() > 1 || segments[0].contains('<'))
                    .then(|| (crate::languages::cpp::names::path_name(&segments), end))
            })
        {
            out_tokens.push(Token::Ident(name));
            out_positions.push(positions[index].clone());
            index = end;
            continue;
        }
        out_tokens.push(tokens[index].clone());
        out_positions.push(positions[index].clone());
        index += 1;
    }
    (out_tokens, out_positions)
}

/// Read the same expression path in a head and in a reference to a lambda.
fn lambda_path_at(tokens: &[Token], mut index: usize, owner: &[String]) -> Option<(String, usize)> {
    let step = |index, name| match tokens.get(index..index + 5)? {
        [
            Token::Dot,
            Token::Ident(found),
            Token::LParen,
            Token::Number(value),
            Token::RParen,
        ] if found == name => Some(*value as usize),
        _ => None,
    };
    let mut statements = Vec::new();
    while let Some(statement) = step(index, "statement") {
        statements.push(statement);
        index += 5;
    }
    if statements.is_empty() {
        return None;
    }
    let argument = if matches!(
        tokens.get(index..index + 2)?,
        [Token::Dot, Token::Ident(name)] if name == "initializer"
    ) {
        index += 2;
        None
    } else {
        let call = step(index, "call")?;
        let argument = step(index + 5, "argument")?;
        index += 10;
        Some((call, argument))
    };
    Some((
        crate::languages::cpp::names::lambda_name(&owner.join("::"), &statements, argument),
        index,
    ))
}

/// The C++ path at `start`, `Rec::m`, `Rec::~Rec`, `Rec::operator+=`,
/// `Stored<long long>::Read` or `choose<true>`, as its segments, and the
/// index after it.
pub(super) fn cpp_path_at(tokens: &[Token], start: usize) -> Option<(Vec<String>, usize)> {
    cpp_path(tokens, start, false)
}

fn cpp_path(
    tokens: &[Token],
    start: usize,
    allow_terminal_template: bool,
) -> Option<(Vec<String>, usize)> {
    let mut segments = Vec::new();
    let mut index = start;
    loop {
        let segment = match (
            tokens.get(index),
            tokens.get(index + 1),
            tokens.get(index + 2),
        ) {
            (Some(Token::Tilde), Some(Token::Ident(name)), _) if !segments.is_empty() => {
                index += 2;
                format!("~{name}")
            }
            (Some(Token::Ident(word)), Some(Token::Equal), _)
                if word == "operator" && !segments.is_empty() =>
            {
                index += 2;
                "operator=".to_string()
            }
            (Some(Token::Ident(word)), Some(Token::Plus), Some(Token::Equal))
                if word == "operator" && !segments.is_empty() =>
            {
                index += 3;
                "operator+=".to_string()
            }
            (Some(Token::Ident(word)), Some(Token::Minus), Some(Token::Equal))
                if word == "operator" && !segments.is_empty() =>
            {
                index += 3;
                "operator-=".to_string()
            }
            (Some(Token::Ident(word)), Some(Token::LBracket), Some(Token::RBracket))
                if word == "operator" && !segments.is_empty() =>
            {
                index += 3;
                "operator[]".to_string()
            }
            (Some(Token::Ident(name)), _, _) => {
                index += 1;
                let mut segment = name.clone();
                if tokens.get(index) == Some(&Token::LessThan)
                    && let Some((arguments, end)) =
                        template_arguments_at(tokens, index, allow_terminal_template)
                {
                    segment.push_str(&arguments);
                    index = end;
                }
                segment
            }
            _ => return None,
        };
        segments.push(segment);
        if tokens.get(index) == Some(&Token::ColonColon) {
            index += 1;
            continue;
        }
        return Some((segments, index));
    }
}

/// Template arguments at `<`, as Clang prints them, and the index after
/// the closing `>`; `None` unless they close before a `(` or `::`, or, in a
/// type, anywhere.
pub(super) fn template_arguments_at(
    tokens: &[Token],
    open: usize,
    in_type: bool,
) -> Option<(String, usize)> {
    let mut printed = String::from("<");
    let mut depth = 1usize;
    let mut word_before = false;
    let mut index = open + 1;
    while let Some(token) = tokens.get(index) {
        index += 1;
        match token {
            Token::LessThan => {
                depth += 1;
                printed.push('<');
                word_before = false;
            }
            Token::GreaterThan => {
                depth -= 1;
                printed.push('>');
                if depth == 0 {
                    return (in_type
                        || matches!(tokens.get(index), Some(Token::LParen | Token::ColonColon)))
                    .then_some((printed, index));
                }
                word_before = false;
            }
            Token::Comma => {
                printed.push_str(", ");
                word_before = false;
            }
            Token::ColonColon => {
                printed.push_str("::");
                word_before = false;
            }
            Token::Minus => {
                printed.push('-');
                word_before = false;
            }
            Token::Star => {
                printed.push_str(" *");
                word_before = false;
            }
            Token::Ident(word) => {
                if word_before {
                    printed.push(' ');
                }
                printed.push_str(word);
                word_before = true;
            }
            // A number, such as a static extent, of any width.
            token => {
                let number = match token {
                    Token::Number(number) => number.to_string(),
                    Token::UnsuffixedInt64(number) => number.to_string(),
                    Token::UnsuffixedUInt64(number) => number.to_string(),
                    _ => return None,
                };
                if word_before {
                    printed.push(' ');
                }
                printed.push_str(&number);
                word_before = true;
            }
        }
    }
    None
}
