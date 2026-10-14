//! Qualified Click library names: `click::list::list_append`, and
//! `list::list_append` when the module is in scope, resolved to the library
//! declaration before parsing.

use super::*;

/// The top-level declaration names of each Click library module, read from
/// its tokens once per process. The library's parsed declarations are not
/// used: library modules are themselves parsed through this resolution.
fn library_declaration_names() -> &'static BTreeMap<&'static str, BTreeSet<String>> {
    static NAMES: std::sync::OnceLock<BTreeMap<&'static str, BTreeSet<String>>> =
        std::sync::OnceLock::new();
    NAMES.get_or_init(|| {
        let mut names = BTreeMap::new();
        for (identity, source) in super::super::CLICK_LIBRARY_MODULES {
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
        for (identity, source) in super::super::CLICK_LIBRARY_MODULES {
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

/// The `library/` identity of a module path such as `["c", "string"]`.
fn module_identity(segments: &[&str]) -> Option<&'static str> {
    let identity = format!("library/{}.click", segments.join("/"));
    super::super::CLICK_LIBRARY_MODULES
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
/// as `Nat::Zero` parse as before.
pub(super) fn resolve_library_paths(
    tokens: Vec<Token>,
    positions: Vec<SourcePosition>,
) -> Result<(Vec<Token>, Vec<SourcePosition>, BTreeSet<&'static str>), ClickError> {
    if !tokens.contains(&Token::ColonColon) {
        return Ok((tokens, positions, BTreeSet::new()));
    }
    let names = library_declaration_names();
    // Modules in scope by their last path segment: the implicit modules and
    // the file's own `import click::...;` lines.
    let mut in_scope = BTreeMap::<String, &'static str>::new();
    for identity in crate::surface::validation::implicit_library_modules() {
        in_scope.insert(short_module_name(identity).to_string(), identity);
    }
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
        if let Some(identity) = module_identity(&segments) {
            in_scope.insert(short_module_name(identity).to_string(), identity);
        }
    }

    let mut resolved_tokens = Vec::with_capacity(tokens.len());
    let mut resolved_positions = Vec::with_capacity(positions.len());
    let mut path_modules = BTreeSet::new();
    let mut index = 0;
    while index < tokens.len() {
        let after_import = index > 0 && tokens[index - 1] == Token::Ident("import".to_string());
        if !after_import
            && let Some((name, consumed, module)) =
                library_path_at(&tokens, index, names, &in_scope, &positions)?
        {
            if let Some(module) = module {
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
    Ok((resolved_tokens, resolved_positions, path_modules))
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
    let unimported = super::super::CLICK_LIBRARY_MODULES
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
    let path = crate::surface::library_module_path(identity);
    let qualified = format!("{path}::{declaration}");
    if library_theorem_identities().get(declaration) == Some(&qualified) {
        qualified
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
