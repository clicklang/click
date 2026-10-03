//! The checked dependency-closure projection of a compiler-preprocessed
//! translation unit.
//!
//! A preprocessed kernel translation unit carries thousands of header
//! declarations that the functions it defines never use. The projection
//! keeps the function definitions written in the unit's own source file
//! and, transitively, every file-scope declaration that defines a name they
//! mention. Everything kept is parsed and lowered as usual, so an
//! unsupported construct inside the closure is still rejected with its
//! original location. Declarations outside the closure are not parsed and
//! nothing is claimed about them.
//!
//! The projection is deliberately narrow. It works on file-scope items: a
//! declaration ending at a file-scope `;`, or a function definition ending
//! at its body's closing brace. An item is kept when it defines a name a
//! kept item mentions, with one exception: an exact `extern typeof(f) f;`
//! redeclaration, which repeats `f`'s own type and adds nothing, is never
//! needed to type a use of `f`. The Linux `EXPORT_SYMBOL` macro emits one
//! per exported function. A program whose omitted items include a
//! `constructor` or `destructor` function is refused, because such a
//! function runs without being named.
//!
//! Omitted items are blanked in place, preserving every line break, so
//! physical line numbers and the compiler source map stay valid.

use std::collections::{BTreeSet, HashMap};

use super::provenance::CSourceMap;
use crate::source::SourcePosition;

/// The import option that selects this projection.
pub(crate) const DEPENDENCY_CLOSURE: &str = "dependency-closure";

/// The projected text and what was left out.
#[derive(Debug)]
pub(crate) struct Projection {
    pub text: String,
    /// The number of file-scope items kept and omitted.
    #[cfg_attr(not(test), allow(dead_code))]
    pub kept: usize,
    #[cfg_attr(not(test), allow(dead_code))]
    pub omitted: usize,
    /// Units of work spent, for the scaling regression: tokens scanned plus
    /// references followed.
    #[cfg_attr(not(test), allow(dead_code))]
    pub work: usize,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Token<'a> {
    Ident(&'a str),
    Punct(u8),
}

struct Item<'a> {
    start: usize,
    end: usize,
    /// The physical line of the item's first token.
    line: usize,
    tokens: Vec<Token<'a>>,
    function_definition: bool,
}

/// Projects `source`, the marker-free preprocessed text whose compiler
/// line markers `map` decodes, onto the dependency closure of the function
/// definitions in its primary source file.
pub(crate) fn project_dependency_closure(
    source: &str,
    map: &CSourceMap,
) -> Result<Projection, String> {
    let primary = map
        .primary_file()
        .ok_or("the preprocessed translation unit names no primary source file")?;
    let (items, mut work) = file_scope_items(source)?;

    // Which items define each name. Struct, union, and enum tags have their
    // own namespace.
    let mut definers: HashMap<(bool, &str), Vec<usize>> = HashMap::new();
    let mut defined_by_item = Vec::with_capacity(items.len());
    for (index, item) in items.iter().enumerate() {
        let defined = defined_names(&item.tokens);
        if !is_typeof_redeclaration(&item.tokens) {
            for key in &defined {
                definers.entry(*key).or_default().push(index);
            }
        }
        defined_by_item.push(defined);
    }

    let mut kept = vec![false; items.len()];
    let mut worklist = Vec::new();
    for (index, item) in items.iter().enumerate() {
        if item.function_definition && origin_file(map, item.line).as_deref() == Some(primary) {
            kept[index] = true;
            worklist.push(index);
        }
    }
    if worklist.is_empty() {
        return Err(format!(
            "the dependency-closure projection found no function definition in `{primary}`"
        ));
    }
    let mut followed: BTreeSet<(bool, &str)> = BTreeSet::new();
    while let Some(index) = worklist.pop() {
        for key in referenced_names(&items[index].tokens) {
            work += 1;
            if defined_by_item[index].contains(&key) || !followed.insert(key) {
                continue;
            }
            for &definer in definers.get(&key).map(Vec::as_slice).unwrap_or(&[]) {
                if !kept[definer] {
                    kept[definer] = true;
                    worklist.push(definer);
                }
            }
        }
    }

    let mut text = String::with_capacity(source.len());
    let mut cursor = 0;
    let mut omitted = 0;
    for (index, item) in items.iter().enumerate() {
        if kept[index] {
            continue;
        }
        if let Some(name) = item.tokens.iter().find_map(|token| match token {
            Token::Ident(
                name @ ("constructor" | "__constructor__" | "destructor" | "__destructor__"),
            ) => Some(*name),
            _ => None,
        }) {
            return Err(format!(
                "{}: a declaration outside the dependency closure has the `{name}` attribute, which runs it without being named; the projection cannot omit it",
                map.lookup(SourcePosition::new(item.line, 1))
            ));
        }
        omitted += 1;
        text.push_str(&source[cursor..item.start]);
        text.extend(
            source[item.start..item.end]
                .chars()
                .map(|character| if character == '\n' { '\n' } else { ' ' }),
        );
        cursor = item.end;
    }
    text.push_str(&source[cursor..]);
    Ok(Projection {
        text,
        kept: items.len() - omitted,
        omitted,
        work,
    })
}

fn origin_file(map: &CSourceMap, line: usize) -> Option<String> {
    map.lookup(SourcePosition::new(line, 1))
        .origin
        .map(|origin| origin.filename.to_string())
}

/// Splits marker-free preprocessed C into file-scope items. Returns the
/// items and the number of bytes scanned.
fn file_scope_items(source: &str) -> Result<(Vec<Item<'_>>, usize), String> {
    let bytes = source.as_bytes();
    let mut items = Vec::new();
    let mut tokens = Vec::new();
    let (mut start, mut depth, mut index) = (0usize, 0usize, 0usize);
    // The current physical line, and the line of the open item's first
    // token, which is set when that token is scanned.
    let mut line = 1usize;
    let mut item_line: Option<usize> = None;
    let mut last_significant = b' ';
    let mut function_body = false;
    while index < bytes.len() {
        let byte = bytes[index];
        if byte == b'\n' {
            line += 1;
        } else if !byte.is_ascii_whitespace() && item_line.is_none() {
            item_line = Some(line);
        }
        match byte {
            b'"' | b'\'' => {
                index += 1;
                while index < bytes.len() && bytes[index] != byte {
                    if bytes[index] == b'\\' {
                        index += 1;
                    }
                    index += 1;
                }
                if index >= bytes.len() {
                    return Err("unterminated literal in preprocessed C".into());
                }
                last_significant = byte;
                index += 1;
                continue;
            }
            b'A'..=b'Z' | b'a'..=b'z' | b'_' => {
                let begin = index;
                while index < bytes.len()
                    && (bytes[index].is_ascii_alphanumeric() || bytes[index] == b'_')
                {
                    index += 1;
                }
                tokens.push(Token::Ident(&source[begin..index]));
                last_significant = b'a';
                continue;
            }
            b'0'..=b'9' => {
                while index < bytes.len()
                    && (bytes[index].is_ascii_alphanumeric() || matches!(bytes[index], b'.' | b'_'))
                {
                    index += 1;
                }
                last_significant = b'0';
                continue;
            }
            _ => {}
        }
        if !byte.is_ascii_whitespace() {
            tokens.push(Token::Punct(byte));
        }
        match byte {
            b'(' | b'[' => depth += 1,
            b')' | b']' => {
                depth = depth
                    .checked_sub(1)
                    .ok_or("unbalanced brackets in preprocessed C")?
            }
            b'{' => {
                if depth == 0 {
                    function_body = last_significant == b')';
                }
                depth += 1;
            }
            b'}' => {
                depth = depth
                    .checked_sub(1)
                    .ok_or("unbalanced braces in preprocessed C")?;
                if depth == 0 && function_body {
                    items.push(Item {
                        start,
                        end: index + 1,
                        line: item_line.take().unwrap_or(line),
                        tokens: std::mem::take(&mut tokens),
                        function_definition: true,
                    });
                    start = index + 1;
                    function_body = false;
                }
            }
            b';' if depth == 0 => {
                items.push(Item {
                    start,
                    end: index + 1,
                    line: item_line.take().unwrap_or(line),
                    tokens: std::mem::take(&mut tokens),
                    function_definition: false,
                });
                start = index + 1;
            }
            _ => {}
        }
        if !byte.is_ascii_whitespace() {
            last_significant = byte;
        }
        index += 1;
    }
    if depth != 0 {
        return Err("unbalanced brackets in preprocessed C".into());
    }
    if !tokens.is_empty() {
        return Err("preprocessed C ends inside a declaration".into());
    }
    Ok((items, bytes.len()))
}

fn is_keyword(name: &str) -> bool {
    matches!(
        name,
        "auto"
            | "break"
            | "case"
            | "char"
            | "const"
            | "continue"
            | "default"
            | "do"
            | "double"
            | "else"
            | "enum"
            | "extern"
            | "float"
            | "for"
            | "goto"
            | "if"
            | "inline"
            | "int"
            | "long"
            | "register"
            | "restrict"
            | "return"
            | "short"
            | "signed"
            | "sizeof"
            | "static"
            | "struct"
            | "switch"
            | "typedef"
            | "union"
            | "unsigned"
            | "void"
            | "volatile"
            | "while"
            | "_Bool"
            | "_Static_assert"
            | "_Alignof"
            | "_Alignas"
            | "_Noreturn"
            | "_Generic"
            | "__attribute__"
            | "__inline__"
            | "__inline"
            | "__extension__"
            | "__restrict"
            | "__restrict__"
            | "__signed__"
            | "__volatile__"
            | "__const__"
            | "asm"
            | "__asm__"
            | "__asm"
            | "typeof"
            | "__typeof__"
            | "__typeof"
            | "__alignof__"
            | "__builtin_va_list"
            | "__int128"
    )
}

/// `extern typeof(f) f;`, exactly.
fn is_typeof_redeclaration(tokens: &[Token<'_>]) -> bool {
    matches!(
        tokens,
        [
            Token::Ident("extern"),
            Token::Ident("typeof" | "__typeof__"),
            Token::Punct(b'('),
            Token::Ident(inner),
            Token::Punct(b')'),
            Token::Ident(outer),
            Token::Punct(b';'),
        ] if inner == outer
    )
}

/// The names an item defines: its declarators at file scope, the tags it
/// defines or forward-declares, and its enumeration constants. The `bool`
/// is true for a tag.
fn defined_names<'a>(tokens: &[Token<'a>]) -> BTreeSet<(bool, &'a str)> {
    let mut defined = BTreeSet::new();
    // Tags: `struct X {` and the forward declaration `struct X;`.
    for window in tokens.windows(3) {
        if let [
            Token::Ident("struct" | "union" | "enum"),
            Token::Ident(tag),
            Token::Punct(next),
        ] = window
            && (*next == b'{' || (*next == b';' && tokens.len() == 3))
        {
            defined.insert((true, *tag));
        }
    }
    // Enumeration constants: the first identifier of each enumerator.
    let mut index = 0;
    while index < tokens.len() {
        if tokens[index] == Token::Ident("enum") {
            let open = tokens[index..]
                .iter()
                .position(|token| *token == Token::Punct(b'{'))
                .map(|offset| index + offset);
            if let Some(open) = open
                && tokens[index + 1..open]
                    .iter()
                    .all(|token| matches!(token, Token::Ident(_)))
            {
                let mut depth = 0usize;
                let mut expect_name = true;
                for token in &tokens[open..] {
                    match token {
                        Token::Punct(b'{' | b'(' | b'[') => depth += 1,
                        Token::Punct(b'}' | b')' | b']') => {
                            depth -= 1;
                            if depth == 0 {
                                break;
                            }
                        }
                        Token::Punct(b',') if depth == 1 => expect_name = true,
                        Token::Ident(name) if depth == 1 && expect_name => {
                            defined.insert((false, *name));
                            expect_name = false;
                        }
                        _ => {}
                    }
                }
            }
        }
        index += 1;
    }
    // Declarators: at file scope, the last ordinary identifier before `=`,
    // `,`, `;`, `[`, or a parameter list, or the name in `(*name)`.
    let mut depth = 0usize;
    let mut last: Option<&'a str> = None;
    let mut index = 0;
    while index < tokens.len() {
        let token = tokens[index];
        match token {
            Token::Ident(
                "__attribute__" | "asm" | "__asm__" | "__asm" | "typeof" | "__typeof__"
                | "__typeof" | "_Alignas" | "__alignof__" | "_Static_assert",
            ) if depth == 0 => {
                index = skip_parenthesized(tokens, index + 1);
                continue;
            }
            Token::Ident(name) if depth == 0 && !is_keyword(name) => last = Some(name),
            Token::Punct(b'(') if depth == 0 => {
                if let Some(name) = last.take() {
                    // A parameter list follows the declared name.
                    defined.insert((false, name));
                    index = skip_parenthesized(tokens, index);
                    continue;
                }
                // `(*name)` or `(name)` names the declarator inside.
                if let [Token::Punct(b'*'), Token::Ident(name), ..]
                | [Token::Ident(name), Token::Punct(b')'), ..] = &tokens[index + 1..]
                    && !is_keyword(name)
                {
                    defined.insert((false, *name));
                }
                index = skip_parenthesized(tokens, index);
                continue;
            }
            Token::Punct(b'{') if depth == 0 => {
                // A tag or initializer body, or a function body: nothing in
                // it is a file-scope declarator.
                index = skip_braced(tokens, index);
                continue;
            }
            Token::Punct(b'=' | b',' | b';' | b'[') if depth == 0 => {
                if let Some(name) = last.take() {
                    defined.insert((false, name));
                }
                if token == Token::Punct(b'=') {
                    // Skip the initializer to the next declarator.
                    while index < tokens.len()
                        && !matches!(tokens[index], Token::Punct(b',' | b';'))
                    {
                        index = match tokens[index] {
                            Token::Punct(b'(' | b'[') => skip_parenthesized(tokens, index),
                            Token::Punct(b'{') => skip_braced(tokens, index),
                            _ => index + 1,
                        };
                    }
                    continue;
                }
                if token == Token::Punct(b'[') {
                    index = skip_parenthesized(tokens, index);
                    continue;
                }
            }
            Token::Punct(b'(' | b'[') => depth += 1,
            Token::Punct(b')' | b']') => depth = depth.saturating_sub(1),
            _ => {}
        }
        index += 1;
    }
    defined
}

/// Skips a balanced `(...)` or `[...]` group starting at or after `index`.
fn skip_parenthesized(tokens: &[Token<'_>], mut index: usize) -> usize {
    while index < tokens.len() && !matches!(tokens[index], Token::Punct(b'(' | b'[')) {
        if matches!(tokens[index], Token::Punct(b';' | b',' | b'=')) {
            return index;
        }
        index += 1;
    }
    let mut depth = 0usize;
    while index < tokens.len() {
        match tokens[index] {
            Token::Punct(b'(' | b'[') => depth += 1,
            Token::Punct(b')' | b']') => {
                depth -= 1;
                if depth == 0 {
                    return index + 1;
                }
            }
            _ => {}
        }
        index += 1;
    }
    index
}

fn skip_braced(tokens: &[Token<'_>], mut index: usize) -> usize {
    let mut depth = 0usize;
    while index < tokens.len() {
        match tokens[index] {
            Token::Punct(b'{') => depth += 1,
            Token::Punct(b'}') => {
                depth -= 1;
                if depth == 0 {
                    return index + 1;
                }
            }
            _ => {}
        }
        index += 1;
    }
    index
}

/// Every name an item mentions: each ordinary identifier, and each tag
/// after `struct`, `union`, or `enum`.
fn referenced_names<'a, 'b>(tokens: &'b [Token<'a>]) -> impl Iterator<Item = (bool, &'a str)> + 'b {
    tokens
        .iter()
        .enumerate()
        .filter_map(|(index, token)| match token {
            Token::Ident(name) if !is_keyword(name) => {
                let tag = index > 0
                    && matches!(tokens[index - 1], Token::Ident("struct" | "union" | "enum"));
                Some((tag, *name))
            }
            _ => None,
        })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn project(source: &str) -> Result<Projection, String> {
        let (text, map) = CSourceMap::decode(source).expect("line markers");
        project_dependency_closure(&text, &map)
    }

    const HEADER: &str = "# 1 \"lib/unit.c\"\n# 1 \"include/h.h\" 1\n";
    const BODY: &str = "# 2 \"lib/unit.c\" 2\n";

    #[test]
    fn keeps_what_the_unit_functions_name_and_blanks_the_rest() {
        let source = format!(
            "{HEADER}struct node {{ struct node *left; }};\nstruct unused {{ int x; }};\ntypedef unsigned long word;\nenum color {{ RED, BLACK = 2 }};\nstatic inline int helper(struct node *n) {{ return n != 0; }}\nstatic inline int stray(int x) {{ asm volatile(\"cli\"); return x; }}\nint (*callback)(int);\nextern int table[4], other;\n{BODY}int run(struct node *n, word w) {{ return helper(n) + BLACK + table[0]; }}\nextern typeof(run) run;\nasm(\".section x\");\n"
        );
        let projection = project(&source).expect("project");
        let kept = projection.text;
        for expected in [
            "struct node",
            "typedef unsigned long word",
            "enum color",
            "helper(struct",
            "extern int table[4], other",
            "int run(",
        ] {
            assert!(kept.contains(expected), "{expected} missing:\n{kept}");
        }
        for omitted in [
            "struct unused",
            "stray",
            "callback",
            "typeof(run)",
            ".section",
        ] {
            assert!(!kept.contains(omitted), "{omitted} kept:\n{kept}");
        }
        assert_eq!(kept.lines().count(), source.lines().count());
        assert_eq!(projection.kept, 6);
        assert_eq!(projection.omitted, 5);
    }

    #[test]
    fn a_needed_redeclaration_with_attributes_is_kept() {
        let source = format!(
            "{HEADER}int target(int x);\nint target(int x) __attribute__((weak));\n{BODY}int run(int x) {{ return target(x); }}\n"
        );
        let kept = project(&source).expect("project").text;
        assert!(kept.contains("__attribute__((weak))"), "{kept}");
    }

    #[test]
    fn an_omitted_constructor_refuses_the_projection() {
        let source = format!(
            "{HEADER}static void setup(void) __attribute__((constructor));\n{BODY}int run(int x) {{ return x; }}\n"
        );
        let error = project(&source).expect_err("constructor");
        assert!(error.contains("include/h.h:1"), "{error}");
        assert!(error.contains("`constructor`"), "{error}");
    }

    #[test]
    fn a_unit_without_function_definitions_is_refused() {
        let source = format!("{HEADER}int x;\n{BODY}extern int y;\n");
        assert!(project(&source).is_err());
    }

    #[test]
    fn projection_work_is_linear_in_the_unit() {
        let unit = |copies: usize| {
            let mut source = String::from(HEADER);
            for index in 0..copies {
                source.push_str(&format!(
                    "struct s{index} {{ int a; }};\nstatic inline int h{index}(struct s{index} *p) {{ return p->a; }}\nint unused{index}(int x);\n"
                ));
            }
            source.push_str(BODY);
            source.push_str("int run(int x) {\n");
            for index in 0..copies {
                source.push_str(&format!("x = x + h{index}(0);\n"));
            }
            source.push_str("return x; }\n");
            source
        };
        let work = |copies: usize| project(&unit(copies)).expect("project").work;
        let base = work(250);
        for factor in [2, 4, 8] {
            let scaled = work(250 * factor);
            // Longer generated names make the text grow a little faster
            // than the item count; a tenth of headroom covers that.
            assert!(
                scaled <= base * factor * 11 / 10,
                "work {scaled} at {factor}x exceeds linear growth from {base}"
            );
        }
    }
}
