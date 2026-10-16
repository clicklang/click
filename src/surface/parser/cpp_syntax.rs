//! The C++ spelling of a function head: qualified member names,
//! constructors, destructors, `operator` names, and the implicit `this` of a
//! member function, admitted when a `verifying` source is C++.

use super::*;

/// A C++ head's declarator, resolved to the name the C++ importer gives the
/// declaration at its path: `Rec::m`, `Rec::Rec`, `Rec::~Rec`,
/// `Rec::operator+=`, `ns::f`, `Stored<long long>::Read`, `choose<true>`, and
/// the first lambda in `caller`, `caller::(lambda#0)`.
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
                        match template_arguments_at(&self.tokens, index) {
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
        let Some((printed, end)) = template_arguments_at(&self.tokens, self.position) else {
            return Err(self.error(
                "C++ template arguments close with `>` before `(` or `::`, \
                 and spell types, values and `true` or `false`",
            ));
        };
        self.position = end;
        Ok(Some(printed))
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
        let first = self.expect_ident("function name")?;
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
                let operator = match (self.peek(), self.peek_next()) {
                    (Some(Token::Plus), Some(Token::Equal)) => "operator+=",
                    (Some(Token::Minus), Some(Token::Equal)) => "operator-=",
                    (Some(Token::LBracket), Some(Token::RBracket)) => "operator[]",
                    _ => {
                        return Err(self.error(
                            "the supported C++ operator methods are `operator+=`, \
                             `operator-=` and `operator[]`",
                        ));
                    }
                };
                self.position += 2;
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
        let name = crate::languages::cpp::names::path_name(&path);
        // `caller::(lambda#0)`: the lambda named after its enclosing
        // function and its index there.
        if special_member.is_none()
            && plain
                .last()
                .is_some_and(|segment| segment.starts_with("(lambda#"))
        {
            if is_static || path.len() < 2 {
                return Err(self.error(
                    "a C++ lambda is named by its enclosing function, `caller::(lambda#0)`",
                ));
            }
            return Ok(CppDeclarator {
                name,
                receiver: None,
                returnless: false,
            });
        }
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
        let after_marker = match (
            index.checked_sub(1).map(|at| &tokens[at]),
            index.checked_sub(2).map(|at| &tokens[at]),
        ) {
            // An address, `&f`, follows an operator or a delimiter; a
            // reference return type, `int32& Cell::get()`, follows a type.
            (Some(Token::Amp), before) => !matches!(
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
            ),
            (Some(Token::Ident(word)), _) if word == "executes" => true,
            (Some(Token::LParen), Some(Token::Ident(word))) if word == "step" => true,
            _ => false,
        };
        if after_marker
            && let Some((segments, end)) = cpp_path_at(&tokens, index)
            && (segments.len() > 1 || segments[0].contains('<'))
        {
            out_tokens.push(Token::Ident(crate::languages::cpp::names::path_name(
                &segments,
            )));
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

/// The C++ path at `start`, `Rec::m`, `Rec::~Rec`, `Rec::operator+=`,
/// `Stored<long long>::Read` or `choose<true>`, as its segments, and the
/// index after it.
fn cpp_path_at(tokens: &[Token], start: usize) -> Option<(Vec<String>, usize)> {
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
                    && let Some((arguments, end)) = template_arguments_at(tokens, index)
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
/// the closing `>`; `None` unless they close before a `(` or `::`.
fn template_arguments_at(tokens: &[Token], open: usize) -> Option<(String, usize)> {
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
                    return matches!(tokens.get(index), Some(Token::LParen | Token::ColonColon))
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
            Token::Number(number) => {
                if word_before {
                    printed.push(' ');
                }
                printed.push_str(&number.to_string());
                word_before = true;
            }
            _ => return None,
        }
    }
    None
}
