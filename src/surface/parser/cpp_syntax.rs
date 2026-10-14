//! The C++ spelling of a function head: qualified member names,
//! constructors, destructors, `operator` names, and the implicit `this` of a
//! member function, admitted when a `verifying` source is C++.

use super::*;

/// A C++ head's declarator, resolved to the name the C++ importer gives the
/// function: `Rec::m` is `Rec_m`, `Rec::Rec` is `Rec_constructor`,
/// `Rec::~Rec` is `Rec_destructor`, `Rec::operator+=` is
/// `Rec_operator_add_assign`, and a free `ns::f` is `ns_f`.
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

    /// A function template instance's arguments, `<false>`, as the suffix
    /// the importer appends to its name, `__bool_false`. Only `bool`
    /// arguments are spelled in a head.
    fn parse_cpp_template_arguments(&mut self) -> Result<String, ClickError> {
        if self.peek() != Some(&Token::LessThan) {
            return Ok(String::new());
        }
        self.position += 1;
        let mut suffix = String::new();
        loop {
            match self.peek_ident() {
                Some(value @ ("true" | "false")) => {
                    suffix.push_str(&format!("__bool_{value}"));
                    self.position += 1;
                }
                _ => {
                    return Err(self
                        .error("a C++ head spells only `bool` template arguments, as `f<true>`"));
                }
            }
            match self.peek() {
                Some(Token::Comma) => self.position += 1,
                Some(Token::GreaterThan) => {
                    self.position += 1;
                    return Ok(suffix);
                }
                _ => return Err(self.error("expected `,` or `>` in template arguments")),
            }
        }
    }

    /// The declarator of a C++ head, after its return type.
    pub(super) fn parse_cpp_declarator(
        &mut self,
        is_static: bool,
    ) -> Result<CppDeclarator, ClickError> {
        let mut path = vec![self.expect_ident("function name")?];
        let mut special_member = None;
        while self.peek() == Some(&Token::ColonColon) {
            self.position += 1;
            if self.peek() == Some(&Token::Tilde) {
                self.position += 1;
                let name = self.expect_ident("destructor name")?;
                let record = path.last().expect("a path has a first segment");
                if &name != record {
                    return Err(self.error(format!(
                        "a destructor of `{record}` is named `{record}::~{record}`"
                    )));
                }
                special_member = Some("destructor");
                break;
            }
            if self.peek_ident() == Some("operator") {
                self.position += 1;
                let operator = match (self.peek(), self.peek_next()) {
                    (Some(Token::Plus), Some(Token::Equal)) => "operator_add_assign",
                    (Some(Token::Minus), Some(Token::Equal)) => "operator_subtract_assign",
                    (Some(Token::LBracket), Some(Token::RBracket)) => "operator_index",
                    _ => {
                        return Err(self.error(
                            "the supported C++ operator methods are `operator+=`, \
                             `operator-=` and `operator[]`",
                        ));
                    }
                };
                self.position += 2;
                special_member = Some(operator);
                break;
            }
            path.push(self.expect_ident("function name")?);
        }
        let suffix = if special_member.is_none() {
            self.parse_cpp_template_arguments()?
        } else {
            String::new()
        };
        let member_of = |parser: &Self, record: &str| {
            parser
                .struct_layouts
                .contains_key(record)
                .then(|| record.to_string())
        };
        let (record, member, returnless) = match special_member {
            Some(member) => {
                let record = path.last().expect("a path has a first segment");
                let Some(record) = member_of(self, record) else {
                    return Err(
                        self.error(format!("`{record}` is not a record of the verified source"))
                    );
                };
                (record, member.to_string(), member == "destructor")
            }
            // `static` marks only a member function, so its qualifier is the
            // record even when the program's layouts omit one whose fields
            // no verified code reads.
            None => match path.as_slice() {
                [.., record, member] if is_static || member_of(self, record).is_some() => {
                    let constructor = member == record;
                    let suffix = if constructor { "constructor" } else { member };
                    (record.clone(), suffix.to_string(), constructor)
                }
                _ => {
                    if is_static {
                        return Err(self.error(
                            "`static` declares a static member function, written `Rec::f`",
                        ));
                    }
                    return Ok(CppDeclarator {
                        name: path.join("_") + &suffix,
                        receiver: None,
                        returnless: false,
                    });
                }
            },
        };
        if is_static && returnless {
            return Err(self.error("a constructor or destructor is not `static`"));
        }
        Ok(CppDeclarator {
            name: format!("{record}_{member}{suffix}"),
            receiver: (!is_static).then_some(record),
            returnless,
        })
    }
}
