//! Qualified Click library names: `click::list::append`, `list::append`
//! when the module is in scope, and `append` after
//! `import click::list::{append};`, resolved to the library declaration
//! before parsing.

use super::parser::{Token, tokenizer};
use super::*;

/// The top-level declaration names of each Click library module, read from
/// its tokens once per process. The library's parsed declarations are not
/// used: library modules are themselves parsed through this resolution.
fn library_declaration_names() -> &'static BTreeMap<&'static str, BTreeSet<String>> {
    static NAMES: std::sync::OnceLock<BTreeMap<&'static str, BTreeSet<String>>> =
        std::sync::OnceLock::new();
    NAMES.get_or_init(|| {
        let mut names = BTreeMap::new();
        for (identity, source) in super::CLICK_LIBRARY_MODULES {
            let Ok((tokens, _)) = tokenizer::tokenize(source, None) else {
                continue;
            };
            names.insert(*identity, top_level_declaration_names(&tokens));
        }
        names
    })
}

/// Each Click library theorem's bare name and its qualified identity,
/// `click::module::name`, which the verifier uses for it: a file theorem of
/// the same name is a different theorem, and built-in tactics name library
/// theorems by this identity.
pub(in crate::surface) fn library_theorem_identities() -> &'static BTreeMap<String, String> {
    static THEOREMS: std::sync::OnceLock<BTreeMap<String, String>> = std::sync::OnceLock::new();
    THEOREMS.get_or_init(|| {
        let mut theorems = BTreeMap::new();
        for (identity, source) in super::CLICK_LIBRARY_MODULES {
            let Ok((tokens, _)) = tokenizer::tokenize(source, None) else {
                continue;
            };
            let path = crate::surface::library_module_path(identity);
            for name in top_level_theorem_names(&tokens) {
                theorems.insert(name.clone(), format!("{path}::{name}"));
            }
        }
        theorems
    })
}

/// The theorems a file declares at top level.
pub(super) fn top_level_theorem_names(tokens: &[Token]) -> BTreeSet<String> {
    let mut names = BTreeSet::new();
    let mut depth = 0usize;
    for (index, token) in tokens.iter().enumerate() {
        match token {
            Token::LBrace | Token::LParen | Token::LBracket => depth += 1,
            Token::RBrace | Token::RParen | Token::RBracket => {
                depth = depth.saturating_sub(1);
            }
            Token::Ident(word) if depth == 0 && word == "theorem" => {
                if let Some(Token::Ident(name)) = tokens.get(index + 1) {
                    names.insert(name.clone());
                }
            }
            _ => {}
        }
    }
    names
}

fn top_level_declaration_names(tokens: &[Token]) -> BTreeSet<String> {
    let mut names = BTreeSet::new();
    let mut depth = 0usize;
    for (index, token) in tokens.iter().enumerate() {
        match token {
            Token::LBrace | Token::LParen | Token::LBracket => depth += 1,
            Token::RBrace | Token::RParen | Token::RBracket => {
                depth = depth.saturating_sub(1);
            }
            Token::Ident(word) if depth == 0 => match word.as_str() {
                "theorem" | "function" | "predicate" | "resource" | "enum" => {
                    if let Some(Token::Ident(name)) = tokens.get(index + 1) {
                        names.insert(name.clone());
                    }
                }
                // `extern <return type> name(...)`: the name precedes the
                // parameter list.
                "extern" => {
                    let open = tokens[index..]
                        .iter()
                        .position(|token| *token == Token::LParen)
                        .map(|offset| index + offset);
                    if let Some(open) = open
                        && let Some(Token::Ident(name)) = tokens.get(open.wrapping_sub(1))
                    {
                        names.insert(name.clone());
                    }
                }
                _ => {}
            },
            _ => {}
        }
    }
    names
}

/// The Click library modules whose functions and predicates, not only
/// theorems, have qualified verifier identities. A module joins when its
/// names drop their prefixes and its uses move to paths.
const QUALIFIED_MODULES: &[&str] = &[
    "library/nat.click",
    "library/list.click",
    "library/bytes.click",
    "library/cstr.click",
    "library/permutation.click",
];

/// The qualified identity a bare theorem citation names: a library theorem
/// of a module that still accepts bare citations. A theorem of a qualified
/// module is cited by its path or after a selective import, both rewritten
/// before parsing.
pub(in crate::surface) fn bare_theorem_citation(name: &str) -> Option<&'static String> {
    let identity = library_theorem_identities().get(name)?;
    let qualified = QUALIFIED_MODULES.iter().any(|module| {
        identity
            .strip_prefix(&crate::surface::library_module_path(module))
            .is_some_and(|rest| rest.starts_with("::"))
    });
    (!qualified).then_some(identity)
}

/// The in-scope spelling `m::name` of a full path `click::m::name` to a
/// declaration of a qualified module, whose bare name does not resolve
/// without a selective import.
pub(in crate::surface) fn qualified_module_spelling(path: &str) -> Option<String> {
    QUALIFIED_MODULES.iter().find_map(|module| {
        let name = path
            .strip_prefix(&crate::surface::library_module_path(module))?
            .strip_prefix("::")?;
        (!name.contains("::")).then(|| format!("{}::{name}", short_module_name(module)))
    })
}

/// Whether the library declaration `name` in module `identity` is known to
/// the verifier by its qualified identity.
pub(in crate::surface) fn is_qualified_declaration(identity: &str, name: &str) -> bool {
    let path = crate::surface::library_module_path(identity);
    library_theorem_identities().get(name) == Some(&format!("{path}::{name}"))
        || (QUALIFIED_MODULES.contains(&identity)
            && library_functions_and_predicates()
                .get(identity)
                .is_some_and(|names| names.contains(name)))
}

/// The pure functions and predicates of each Click library module. Types,
/// constructors and resources keep their bare names.
fn library_functions_and_predicates() -> &'static BTreeMap<&'static str, BTreeSet<String>> {
    static NAMES: std::sync::OnceLock<BTreeMap<&'static str, BTreeSet<String>>> =
        std::sync::OnceLock::new();
    NAMES.get_or_init(|| {
        let mut names = BTreeMap::new();
        for (identity, source) in super::CLICK_LIBRARY_MODULES {
            let Ok((tokens, _)) = tokenizer::tokenize(source, None) else {
                continue;
            };
            let mut declared = BTreeSet::new();
            let mut depth = 0usize;
            for (index, token) in tokens.iter().enumerate() {
                match token {
                    Token::LBrace | Token::LParen | Token::LBracket => depth += 1,
                    Token::RBrace | Token::RParen | Token::RBracket => {
                        depth = depth.saturating_sub(1);
                    }
                    Token::Ident(word)
                        if depth == 0 && matches!(word.as_str(), "function" | "predicate") =>
                    {
                        if let Some(Token::Ident(name)) = tokens.get(index + 1) {
                            declared.insert(name.clone());
                        }
                    }
                    _ => {}
                }
            }
            names.insert(*identity, declared);
        }
        names
    })
}

/// Whether Click library module `identity` declares `name` at top level.
pub(super) fn module_declares(identity: &str, name: &str) -> bool {
    library_declaration_names()
        .get(identity)
        .is_some_and(|names| names.contains(name))
}

/// The identity of the Click library module whose source is `file`.
fn module_identity_of_file(file: &str) -> Option<&'static str> {
    super::CLICK_LIBRARY_MODULES
        .iter()
        .map(|(module, _)| *module)
        .find(|module| *module == file)
}

/// The `library/` identity of a module path such as `["c", "string"]`.
fn module_identity(segments: &[&str]) -> Option<&'static str> {
    let identity = format!("library/{}.click", segments.join("/"));
    super::CLICK_LIBRARY_MODULES
        .iter()
        .map(|(module, _)| *module)
        .find(|module| *module == identity)
}

/// Rewrites each qualified library name to the declaration it names.
///
/// `click::m::name` names `name` in module `click::m` and needs no import;
/// its module joins the returned set, which the file adds to its library
/// imports. `m::name` names the same declaration when module `m` is in scope:
/// an implicit module, or one the file imports. A path whose last segment is
/// not a declaration of that module is left alone, so constructor paths such
/// as `Nat::Zero` parse as before. Inside library module `file`, the module
/// is in scope by its own short name, and a path to it brings nothing.
pub(super) struct ResolvedLibraryTokens {
    pub(super) tokens: Vec<Token>,
    pub(super) positions: Vec<SourcePosition>,
    pub(super) path_modules: BTreeSet<&'static str>,
    pub(super) symbols: FileSymbols,
}

pub(super) fn resolve_library_paths(
    tokens: Vec<Token>,
    positions: Vec<SourcePosition>,
    file: Option<&str>,
) -> Result<ResolvedLibraryTokens, ClickError> {
    if !tokens.contains(&Token::ColonColon) {
        let scope = FileSymbols::from_tokens(&tokens, &positions, file)?;
        return Ok(ResolvedLibraryTokens {
            tokens,
            positions,
            path_modules: BTreeSet::new(),
            symbols: scope,
        });
    }
    let names = library_declaration_names();
    let scope = FileSymbols::from_tokens(&tokens, &positions, file)?;
    let FileSymbols {
        in_scope,
        selected,
        import_spans,
        own,
        ..
    } = &scope;
    let mut resolved_tokens = Vec::with_capacity(tokens.len());
    let mut resolved_positions = Vec::with_capacity(positions.len());
    let mut path_modules = BTreeSet::new();
    let mut index = 0;
    while index < tokens.len() {
        if let Some(&end) = import_spans.get(&index) {
            for skipped in index..end {
                resolved_tokens.push(tokens[skipped].clone());
                resolved_positions.push(positions[skipped].clone());
            }
            index = end;
            continue;
        }
        if let Token::Ident(name) = &tokens[index]
            && let Some(resolved) = selected.get(name)
            && is_reference_position(&tokens, index)
        {
            resolved_tokens.push(Token::Ident(resolved.clone()));
            resolved_positions.push(positions[index].clone());
            index += 1;
            continue;
        }
        if let Some((name, consumed, module)) =
            library_path_at(&tokens, index, names, in_scope, &positions)?
        {
            if let Some(module) = module
                && Some(module) != *own
            {
                path_modules.insert(module);
            }
            resolved_tokens.push(Token::Ident(name));
            resolved_positions.push(positions[index].clone());
            index += consumed;
            continue;
        }
        resolved_tokens.push(tokens[index].clone());
        resolved_positions.push(positions[index].clone());
        index += 1;
    }
    Ok(ResolvedLibraryTokens {
        tokens: resolved_tokens,
        positions: resolved_positions,
        path_modules,
        symbols: scope,
    })
}

/// Whether the identifier at `index` names a declaration rather than a
/// variable: it is applied, `name(...)` or `name<T>(...)`, or it is the
/// argument of `unfold(name)`.
fn is_reference_position(tokens: &[Token], index: usize) -> bool {
    tokens.get(index + 1) == Some(&Token::LParen)
        || (tokens.get(index + 1) == Some(&Token::LessThan)
            && matches!(tokens.get(index + 2), Some(Token::Ident(_)))
            && matches!(
                tokens.get(index + 3),
                Some(Token::GreaterThan | Token::Comma | Token::LessThan)
            ))
        || (index >= 2
            && tokens[index - 1] == Token::LParen
            && tokens[index - 2] == Token::Ident("unfold".to_string()))
}

fn short_module_name(identity: &str) -> &str {
    identity
        .strip_prefix("library/")
        .and_then(|path| path.strip_suffix(".click"))
        .and_then(|path| path.rsplit('/').next())
        .unwrap_or(identity)
}

/// The declaration a qualified library name at `start` names, the number of
/// tokens it spans, and, for a full `click::` path, the module it brings.
fn library_path_at(
    tokens: &[Token],
    start: usize,
    names: &BTreeMap<&'static str, BTreeSet<String>>,
    in_scope: &BTreeMap<String, &'static str>,
    positions: &[SourcePosition],
) -> Result<Option<(String, usize, Option<&'static str>)>, ClickError> {
    let Some(Token::Ident(first)) = tokens.get(start) else {
        return Ok(None);
    };
    if tokens.get(start + 1) != Some(&Token::ColonColon) {
        return Ok(None);
    }
    let mut segments = vec![first.as_str()];
    let mut cursor = start + 1;
    while tokens.get(cursor) == Some(&Token::ColonColon) {
        let Some(Token::Ident(segment)) = tokens.get(cursor + 1) else {
            break;
        };
        segments.push(segment.as_str());
        cursor += 2;
    }
    let (declaration, module_path) = segments.split_last().expect("a path has segments");
    let consumed = segments.len() * 2 - 1;
    if first == "click" {
        let Some(identity) = module_identity(&module_path[1..]) else {
            return Ok(None);
        };
        if !names[identity].contains(*declaration) {
            return Err(path_error(
                positions,
                start,
                format!(
                    "`{}` names no declaration of Click library module `{}`",
                    segments.join("::"),
                    module_path.join("::")
                ),
            ));
        }
        return Ok(Some((
            resolved_name(identity, declaration),
            consumed,
            Some(identity),
        )));
    }
    let [module] = module_path else {
        return Ok(None);
    };
    if let Some(identity) = in_scope.get(*module) {
        if names[identity].contains(*declaration) {
            return Ok(Some((resolved_name(identity, declaration), consumed, None)));
        }
        return Ok(None);
    }
    // A module the file has not imported: say which import or path names it.
    let unimported = super::CLICK_LIBRARY_MODULES
        .iter()
        .map(|(identity, _)| *identity)
        .find(|identity| {
            short_module_name(identity) == *module && names[identity].contains(*declaration)
        });
    if let Some(identity) = unimported {
        let path = crate::surface::library_module_path(identity);
        return Err(path_error(
            positions,
            start,
            format!(
                "`{module}::{declaration}` names Click library module `{path}`, which this file does not import; add `import {path};` or write `{path}::{declaration}`"
            ),
        ));
    }
    Ok(None)
}

/// The name a path to `declaration` in module `identity` resolves to: a
/// theorem's qualified identity, and any other declaration's bare name.
fn resolved_name(identity: &str, declaration: &str) -> String {
    if is_qualified_declaration(identity, declaration) {
        format!(
            "{}::{declaration}",
            crate::surface::library_module_path(identity)
        )
    } else {
        declaration.to_string()
    }
}

fn path_error(positions: &[SourcePosition], index: usize, message: String) -> ClickError {
    match positions.get(index) {
        Some(position) => ClickError::new(format!("{position}: {message}")),
        None => ClickError::new(message),
    }
    .with_kind(ClickErrorKind::Syntax)
}

/// File-level declaration and import bindings shared by lowering and source
/// spelling. Canonical library identities never depend on printed text.
#[derive(Clone, Debug, Default)]
pub(super) struct FileSymbols {
    in_scope: BTreeMap<String, &'static str>,
    selected: BTreeMap<String, String>,
    import_spans: BTreeMap<usize, usize>,
    own: Option<&'static str>,
    local_theorems: BTreeSet<String>,
    explicit_paths: BTreeSet<String>,
}

impl FileSymbols {
    fn from_tokens(
        tokens: &[Token],
        positions: &[SourcePosition],
        file: Option<&str>,
    ) -> Result<Self, ClickError> {
        // Modules in scope by their last path segment: the implicit modules and
        // the file's own `import click::...;` lines.
        let mut in_scope = BTreeMap::<String, &'static str>::new();
        let own = file.and_then(module_identity_of_file);
        for identity in crate::surface::validation::implicit_library_modules().chain(own) {
            in_scope.insert(short_module_name(identity).to_string(), identity);
        }
        // Names a selective import brings, and the token ranges of the import
        // statements, which are left as written.
        let mut selected = BTreeMap::<String, String>::new();
        let mut import_spans = BTreeMap::new();
        let local = top_level_declaration_names(tokens);
        for (index, token) in tokens.iter().enumerate() {
            if *token != Token::Ident("import".to_string())
                || tokens.get(index + 1) != Some(&Token::Ident("click".to_string()))
            {
                continue;
            }
            let mut segments = Vec::new();
            let mut cursor = index + 2;
            while tokens.get(cursor) == Some(&Token::ColonColon) {
                let Some(Token::Ident(segment)) = tokens.get(cursor + 1) else {
                    break;
                };
                segments.push(segment.as_str());
                cursor += 2;
            }
            let Some(identity) = module_identity(&segments) else {
                continue;
            };
            in_scope.insert(short_module_name(identity).to_string(), identity);
            if tokens.get(cursor) == Some(&Token::ColonColon)
                && tokens.get(cursor + 1) == Some(&Token::LBrace)
            {
                cursor += 2;
                while let Some(Token::Ident(name)) = tokens.get(cursor) {
                    if local.contains(name) {
                        return Err(path_error(
                            positions,
                            cursor,
                            format!(
                                "`{name}` is imported from `{}` and also declared in this file; drop the import, rename the declaration, or write the library's by its path",
                                crate::surface::library_module_path(identity)
                            ),
                        ));
                    }
                    let resolved = resolved_name(identity, name);
                    if let Some(previous) = selected.insert(name.clone(), resolved.clone())
                        && previous != resolved
                    {
                        return Err(path_error(
                            positions,
                            cursor,
                            format!("`{name}` is imported twice, as `{previous}` and `{resolved}`"),
                        ));
                    }
                    cursor += 1;
                    if tokens.get(cursor) == Some(&Token::Comma) {
                        cursor += 1;
                    }
                }
            }
            let end = tokens[index..]
                .iter()
                .position(|token| *token == Token::Semicolon)
                .map_or(tokens.len(), |offset| index + offset);
            import_spans.insert(index, end);
        }

        let mut explicit_paths = BTreeSet::new();
        for start in 0..tokens.len() {
            if tokens[start] != Token::Ident("click".to_string()) {
                continue;
            }
            let mut path = String::from("click");
            let mut cursor = start + 1;
            while tokens.get(cursor) == Some(&Token::ColonColon) {
                let Some(Token::Ident(segment)) = tokens.get(cursor + 1) else {
                    break;
                };
                path.push_str("::");
                path.push_str(segment);
                cursor += 2;
            }
            explicit_paths.insert(path);
        }
        Ok(Self {
            in_scope,
            selected,
            import_spans,
            own,
            local_theorems: if file.is_some_and(|file| file.starts_with("library/")) {
                BTreeSet::new()
            } else {
                top_level_theorem_names(tokens)
            },
            explicit_paths,
        })
    }

    pub(super) fn theorem_identity(&self, name: String) -> String {
        if self.local_theorems.contains(&name) {
            name
        } else {
            bare_theorem_citation(&name).cloned().unwrap_or(name)
        }
    }

    pub(super) fn for_source(source: &str) -> Result<Self, ClickError> {
        let (tokens, positions) = tokenizer::tokenize(source, None)?;
        Self::from_tokens(&tokens, &positions, None)
    }

    pub(super) fn visible_modules(&self) -> Vec<String> {
        self.in_scope
            .values()
            .map(|identity| identity.to_string())
            .collect()
    }

    /// Choose a spelling with exactly the canonical identity the parser sees.
    pub(super) fn spelling<'a>(&self, path: &'a str) -> std::borrow::Cow<'a, str> {
        crate::instrumentation::record_deterministic_work(1);
        let bare = path.rsplit("::").next().unwrap_or(path);
        if self.explicit_paths.contains(path) {
            return path.into();
        }
        if self
            .selected
            .get(bare)
            .is_some_and(|selected| selected == path)
        {
            return bare.into();
        }
        if let Some(short) = qualified_module_spelling(path) {
            let module = path.rsplit_once("::").expect("qualified path").0;
            if self
                .in_scope
                .get(module.rsplit("::").next().unwrap_or(module))
                .is_some_and(|identity| crate::surface::library_module_path(identity) == module)
            {
                return short.into();
            }
        } else if !self.local_theorems.contains(bare)
            && bare_theorem_citation(bare).is_some_and(|identity| identity == path)
        {
            return bare.into();
        }
        path.into()
    }
}

/// The qualified identity of the Click library theorem `name`: `name`
/// itself when it is already qualified or names no library theorem. Built-in
/// tactics name library theorems through this.
pub(in crate::surface) fn library_theorem_identity(name: &str) -> String {
    library_theorem_identities()
        .get(name)
        .cloned()
        .unwrap_or_else(|| name.to_string())
}
