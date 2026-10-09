use std::ops::Range;
use std::sync::Arc;

use super::validation::tactic_name;
use super::*;
use crate::languages::c::target::CTarget;
use crate::languages::c::thread_runtime::CThreadRuntime;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CProofClaim {
    Ensure(usize),
    ExceptionalEnsure(usize),
    Grouped,
}

impl CProofClaim {
    /// The claim as a diagnostic names it: the zero-based source clause, or
    /// the function's one grouped proof.
    pub fn describe(&self) -> String {
        match self {
            Self::Ensure(index) => format!("`ensures` clause {index}"),
            Self::ExceptionalEnsure(index) => format!("`exceptional ensures` clause {index}"),
            Self::Grouped => "grouped contract proof".to_string(),
        }
    }
}

pub fn verifying_source_paths(click_source: &str) -> Result<Vec<String>, ClickError> {
    let tokens = scan_source_tokens(click_source)?;
    let mut paths = Vec::new();
    for window in tokens.windows(2) {
        if window[0].text == "verifying"
            && window[1].text.starts_with('"')
            && window[1].text.ends_with('"')
        {
            paths.push(window[1].text[1..window[1].text.len() - 1].to_string());
        }
    }
    Ok(paths)
}

/// Rewrites the path literal of every `verifying "..."` declaration whose
/// current spelling selects a rebased file, keeping all other source text
/// byte-identical. Callers supply the mapping: `None` keeps a declaration
/// unchanged, and the caller guarantees the mapped spelling resolves to the
/// same source from its own loading rules.
pub fn map_verifying_source_paths(
    click_source: &str,
    map: impl Fn(&str) -> Option<String>,
) -> Result<String, ClickError> {
    let tokens = scan_source_tokens(click_source)?;
    let mut replacements = Vec::new();
    for window in tokens.windows(2) {
        if window[0].text == "verifying"
            && window[1].text.starts_with('"')
            && window[1].text.ends_with('"')
        {
            let declared = &window[1].text[1..window[1].text.len() - 1];
            let Some(rebased) = map(declared) else {
                continue;
            };
            if rebased.contains('\\') || rebased.contains('"') {
                return Err(ClickError::new(format!(
                    "rebased verifying declaration `{rebased}` is not a supported path literal"
                )));
            }
            replacements.push((window[1].span.clone(), format!("\"{rebased}\"")));
        }
    }
    let mut rebased = String::with_capacity(click_source.len());
    let mut cursor = 0;
    for (Range { start, end }, spelled) in replacements {
        rebased.push_str(&click_source[cursor..start]);
        rebased.push_str(&spelled);
        cursor = end;
    }
    rebased.push_str(&click_source[cursor..]);
    Ok(rebased)
}

/// Finds the top-level `target "..."` directive that selects the C
/// implementation target, before any C source is preprocessed. Include
/// expansion needs the target, and expansion happens before the sidecar is
/// parsed, so this scan and the parser share one accepted-name registry.
/// Absent directive selects the default target.
pub fn selected_c_target(click_source: &str) -> Result<CTarget, ClickError> {
    Ok(declared_c_target(click_source)?.unwrap_or(CTarget::SUPPORTED))
}

/// Scans the explicit runtime selector before the full sidecar is parsed.
/// Incremental sessions use it to refuse a changed runtime identity.
pub fn selected_thread_runtime(click_source: &str) -> Result<CThreadRuntime, ClickError> {
    let tokens = scan_source_tokens(click_source)?;
    let mut selected = None;
    let mut depth = 0usize;
    for window in tokens.windows(3) {
        match window[0].text.as_str() {
            "{" => depth += 1,
            "}" => depth = depth.saturating_sub(1),
            _ => {}
        }
        if depth > 0
            || window[0].text != "runtime"
            || !window[1].text.starts_with('"')
            || !window[1].text.ends_with('"')
            || window[1].text.len() < 2
            || window[2].text != ";"
        {
            continue;
        }
        let name = &window[1].text[1..window[1].text.len() - 1];
        let runtime = CThreadRuntime::from_name(name)
            .ok_or_else(|| ClickError::new(format!("unknown C runtime `{name}`")))?;
        if selected.replace(runtime).is_some() {
            return Err(ClickError::new(
                "a Click file declares more than one `runtime`",
            ));
        }
    }
    Ok(selected.unwrap_or_default())
}

pub fn selected_project_thread_runtime(
    project: &ClickProject,
) -> Result<CThreadRuntime, ClickError> {
    let mut selected = CThreadRuntime::None;
    for module in project.modules() {
        let runtime = selected_thread_runtime(module.source())?;
        if runtime != CThreadRuntime::None {
            if selected != CThreadRuntime::None && selected != runtime {
                return Err(ClickError::new(
                    "project modules select different C runtimes",
                ));
            }
            selected = runtime;
        }
    }
    if let Some(configured) = project.c_profile().and_then(|profile| profile.runtime) {
        if selected != CThreadRuntime::None && selected != configured {
            return Err(ClickError::new(
                "Click project config conflicts with a module `runtime` directive",
            ));
        }
        return Ok(configured);
    }
    Ok(selected)
}

/// The C implementation target one project selects. Modules may restate the
/// same target, but a project has exactly one preprocessing and proof-artifact
/// target, so two different declarations are an error.
pub fn selected_project_c_target(project: &ClickProject) -> Result<CTarget, ClickError> {
    let mut modules = project.modules().iter().collect::<Vec<_>>();
    modules.sort_by_key(|module| module.identity());
    let mut selected: Option<(&str, CTarget)> = None;
    for module in modules {
        let Some(declared) = declared_c_target(module.source())? else {
            continue;
        };
        match selected {
            Some((previous_identity, previous)) if previous != declared => {
                return Err(ClickError::new(format!(
                    "module `{}` selects C target `{}`, but module `{previous_identity}` selects `{}`",
                    module.identity(),
                    declared.name(),
                    previous.name()
                )));
            }
            _ => selected = Some((module.identity(), declared)),
        }
    }
    if let Some(configured) = project.c_profile().and_then(|profile| profile.target) {
        if let Some((identity, declared)) = selected
            && declared != configured
        {
            return Err(ClickError::new(format!(
                "Click project config selects C target `{}`, but module `{identity}` selects `{}`",
                configured.name(),
                declared.name()
            )));
        }
        return Ok(configured);
    }
    Ok(selected.map_or(CTarget::SUPPORTED, |(_, target)| target))
}

fn declared_c_target(click_source: &str) -> Result<Option<CTarget>, ClickError> {
    let tokens = scan_source_tokens(click_source)?;
    let mut selected = None;
    let mut depth = 0usize;
    for window in tokens.windows(3) {
        // The directive is a file item, so only brace depth zero can hold one.
        // A deeper `target "..."` spelling is not a directive here and must
        // not be one for the parser either.
        match window[0].text.as_str() {
            "{" => depth += 1,
            "}" => depth = depth.saturating_sub(1),
            _ => {}
        }
        if depth > 0
            || window[0].text != "target"
            || !window[1].text.starts_with('"')
            || !window[1].text.ends_with('"')
            || window[1].text.len() < 2
            || window[2].text != ";"
        {
            continue;
        }
        let name = &window[1].text[1..window[1].text.len() - 1];
        let target = CTarget::from_name(name).ok_or_else(|| {
            ClickError::new(format!(
                "unknown C target `{name}`; accepted targets are {}",
                CTarget::accepted_names()
            ))
        })?;
        if selected.is_some() {
            return Err(ClickError::new(
                "a Click file declares more than one `target`".to_string(),
            ));
        }
        selected = Some(target);
    }
    Ok(selected)
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ClickImportSite {
    pub path: String,
    pub position: SourcePosition,
}

/// Finds top-level import declarations for the filesystem graph loader. Full
/// syntax and interface validation still happens in the shared parser.
pub fn click_import_sites(click_source: &str) -> Result<Vec<ClickImportSite>, ClickError> {
    let tokens = scan_source_tokens(click_source)?;
    let mut sites = Vec::new();
    for window in tokens.windows(2) {
        if window[0].text == "import"
            && window[1].text.starts_with('"')
            && window[1].text.ends_with('"')
        {
            sites.push(ClickImportSite {
                path: window[1].text[1..window[1].text.len() - 1].to_string(),
                position: position_at_offset(click_source, window[0].span.start),
            });
        }
    }
    Ok(sites)
}

/// Expands one claim and returns the rewritten source.
///
/// The caller is responsible for verifying the returned sidecar.
pub fn expand_c0_claim_source(
    click_source: &str,
    c_sources: &[(&str, &str)],
    function_name: &str,
    claim: CProofClaim,
) -> Result<String, ClickError> {
    let tokens = scan_source_tokens(click_source)?;
    let function = find_function(&tokens, function_name)?;
    let file = parse_source_with_c_layouts(click_source, c_sources)?;
    let function_block = proof_function_blocks(&file)
        .find(|function| function.signature().name() == function_name)
        .ok_or_else(|| ClickError::new(format!("unknown function `{function_name}`")))?;
    let claim = covering_claim(function_block, claim);
    let edit = if claim == CProofClaim::Grouped {
        find_grouped_proof_edit(&tokens, &function, function_block)?
    } else {
        find_claim_proof_edit(&tokens, &function, function_block, claim)?
    };
    let target = position_at_offset(click_source, edit.selector());
    let verified = verify_c0_sources_at(click_source, c_sources, target.line, target.column)?;
    let theorem = select_expansion_theorem(&verified, function_name, claim)?;
    let replacement = claim_expansion_source(theorem)?;
    let span = edit.span();
    let replacement = indent_replacement(click_source, span.start, &replacement);
    let replacement = match edit {
        ProofSourceEdit::Explicit(_) => replacement,
        ProofSourceEdit::DefaultTerminator { .. } => {
            let separator = click_source[..span.start]
                .chars()
                .next_back()
                .is_some_and(|character| !character.is_whitespace());
            format!("{}{replacement}", if separator { " " } else { "" })
        }
        ProofSourceEdit::OmittedLoopPhase { .. } => {
            unreachable!("function claim edits are never loop phases")
        }
    };
    Ok(splice_source(click_source, &tokens, span, &replacement))
}

fn expand_c0_project_claim_source(
    project: &ClickProject,
    c_sources: &[(&str, &str)],
    function_name: &str,
    claim: CProofClaim,
) -> Result<String, ClickError> {
    let click_source = project
        .entry_source()
        .ok_or_else(|| ClickError::new(format!("missing entry module `{}`", project.entry())))?;
    let sources = CSourceContext::bundle(c_sources).with_click_project(project);
    let file = resolve_click_project_context(project, &sources)?;
    let tokens = scan_source_tokens(click_source)?;
    let function = find_function(&tokens, function_name)?;
    let function_block = proof_function_blocks(&file)
        .find(|function| function.signature().name() == function_name)
        .ok_or_else(|| ClickError::new(format!("unknown function `{function_name}`")))?;
    let claim = covering_claim(function_block, claim);
    let edit = if claim == CProofClaim::Grouped {
        find_grouped_proof_edit(&tokens, &function, function_block)?
    } else {
        find_claim_proof_edit(&tokens, &function, function_block, claim)?
    };
    let target = position_at_offset(click_source, edit.selector());
    let verified = verify_c0_project_at(project, c_sources, target.line, target.column)?;
    let theorem = select_expansion_theorem(&verified, function_name, claim)?;
    let replacement = claim_expansion_source(theorem)?;
    let span = edit.span();
    let replacement = indent_replacement(click_source, span.start, &replacement);
    let replacement = match edit {
        ProofSourceEdit::Explicit(_) => replacement,
        ProofSourceEdit::DefaultTerminator { .. } => {
            let separator = click_source[..span.start]
                .chars()
                .next_back()
                .is_some_and(|character| !character.is_whitespace());
            format!("{}{replacement}", if separator { " " } else { "" })
        }
        ProofSourceEdit::OmittedLoopPhase { .. } => unreachable!(),
    };
    Ok(splice_source(click_source, &tokens, span, &replacement))
}

fn expand_c0_prepared_project_claim_source(
    project: &ClickProject,
    imports: &[crate::languages::c::compiler_import::PreparedCImport],
    function_name: &str,
    claim: CProofClaim,
) -> Result<String, ClickError> {
    let click_source = project
        .entry_source()
        .ok_or_else(|| ClickError::new(format!("missing entry module `{}`", project.entry())))?;
    let sources = CSourceContext::prepared(imports).with_click_project(project);
    let file = resolve_click_project_context(project, &sources)?;
    let tokens = scan_source_tokens(click_source)?;
    let function = find_function(&tokens, function_name)?;
    let function_block = proof_function_blocks(&file)
        .find(|function| function.signature().name() == function_name)
        .ok_or_else(|| ClickError::new(format!("unknown function `{function_name}`")))?;
    let claim = covering_claim(function_block, claim);
    let edit = if claim == CProofClaim::Grouped {
        find_grouped_proof_edit(&tokens, &function, function_block)?
    } else {
        find_claim_proof_edit(&tokens, &function, function_block, claim)?
    };
    let target = position_at_offset(click_source, edit.selector());
    let verified = verify_c0_prepared_project_at(project, imports, target.line, target.column)?;
    let theorem = select_expansion_theorem(&verified, function_name, claim)?;
    let replacement = claim_expansion_source(theorem)?;
    let span = edit.span();
    let replacement = indent_replacement(click_source, span.start, &replacement);
    let replacement = match edit {
        ProofSourceEdit::Explicit(_) => replacement,
        ProofSourceEdit::DefaultTerminator { .. } => {
            let separator = click_source[..span.start]
                .chars()
                .next_back()
                .is_some_and(|character| !character.is_whitespace());
            format!("{}{replacement}", if separator { " " } else { "" })
        }
        ProofSourceEdit::OmittedLoopPhase { .. } => unreachable!(),
    };
    Ok(splice_source(click_source, &tokens, span, &replacement))
}

fn expand_c0_prepared_claim_source(
    click_source: &str,
    imports: &[crate::languages::c::compiler_import::PreparedCImport],
    function_name: &str,
    claim: CProofClaim,
) -> Result<String, ClickError> {
    let sources = CSourceContext::prepared(imports);
    let tokens = scan_source_tokens(click_source)?;
    let function = find_function(&tokens, function_name)?;
    let file = parse_source_with_c_layouts_context(click_source, &sources)?;
    let function_block = proof_function_blocks(&file)
        .find(|function| function.signature().name() == function_name)
        .ok_or_else(|| ClickError::new(format!("unknown function `{function_name}`")))?;
    let claim = covering_claim(function_block, claim);
    let edit = if claim == CProofClaim::Grouped {
        find_grouped_proof_edit(&tokens, &function, function_block)?
    } else {
        find_claim_proof_edit(&tokens, &function, function_block, claim)?
    };
    let target = position_at_offset(click_source, edit.selector());
    let verified =
        verify_c0_prepared_sources_at(click_source, imports, target.line, target.column)?;
    let theorem = select_expansion_theorem(&verified, function_name, claim)?;
    let replacement = claim_expansion_source(theorem)?;
    let span = edit.span();
    let replacement = indent_replacement(click_source, span.start, &replacement);
    let replacement = match edit {
        ProofSourceEdit::Explicit(_) => replacement,
        ProofSourceEdit::DefaultTerminator { .. } => {
            let separator = click_source[..span.start]
                .chars()
                .next_back()
                .is_some_and(|character| !character.is_whitespace());
            format!("{}{replacement}", if separator { " " } else { "" })
        }
        ProofSourceEdit::OmittedLoopPhase { .. } => unreachable!(),
    };
    Ok(splice_source(click_source, &tokens, span, &replacement))
}

/// Use the same claim labels for every source/import route. A selected
/// exceptional ensure must remain exceptional through lookup; covering_claim
/// subsequently selects the grouped proof when that is its producer.
fn function_expansion_claim_by_label(
    function: &FunctionBlock,
    claim_label: &str,
) -> Option<CProofClaim> {
    let name = function.signature().name();
    if claim_label == format!("{name}.contract") && function.covering_proof().is_some() {
        return Some(CProofClaim::Grouped);
    }
    for (clauses, prefix, claim) in [
        (
            function.ensures(),
            "ensures",
            CProofClaim::Ensure as fn(usize) -> CProofClaim,
        ),
        (
            function.exceptional_ensures(),
            "exceptional_ensures",
            CProofClaim::ExceptionalEnsure as fn(usize) -> CProofClaim,
        ),
    ] {
        for (index, ensure) in clauses.iter().enumerate() {
            let label = ensure.name().map_or_else(
                || format!("{name}.{prefix}_{index}"),
                |label| format!("{name}.{label}"),
            );
            if label == claim_label {
                return Some(claim(index));
            }
        }
    }
    None
}

/// Expands one function claim selected by the same stable label used by
/// profiling and diagnostics.
pub fn expand_c0_claim_source_by_label(
    click_source: &str,
    c_sources: &[(&str, &str)],
    claim_label: &str,
) -> Result<String, ClickError> {
    let file = parse_source_with_c_layouts(click_source, c_sources)?;
    for theorem in file.theorem_definitions() {
        for (index, ensure) in theorem.ensures().iter().enumerate() {
            let label = ensure.name().map_or_else(
                || format!("{}.ensures_{index}", theorem.name()),
                |name| format!("{}.{name}", theorem.name()),
            );
            if label == claim_label {
                return expand_pure_theorem_source(click_source, c_sources, theorem.name(), index);
            }
        }
    }
    for function in proof_function_blocks(&file) {
        if let Some(claim) = function_expansion_claim_by_label(function, claim_label) {
            return expand_c0_claim_source(
                click_source,
                c_sources,
                function.signature().name(),
                claim,
            );
        }
    }
    Err(ClickError::new(format!(
        "could not locate function claim `{claim_label}`"
    )))
}

pub fn expand_c0_project_claim_source_by_label(
    project: &ClickProject,
    c_sources: &[(&str, &str)],
    claim_label: &str,
) -> Result<String, ClickError> {
    project
        .entry_source()
        .ok_or_else(|| ClickError::new(format!("missing entry module `{}`", project.entry())))?;
    let sources = CSourceContext::bundle(c_sources).with_click_project(project);
    let file = resolve_click_project_context(project, &sources)?;
    for theorem in file.theorem_definitions() {
        if !file.theorem_is_selected(theorem.name()) {
            continue;
        }
        for (index, ensure) in theorem.ensures().iter().enumerate() {
            let label = ensure.name().map_or_else(
                || format!("{}.ensures_{index}", theorem.name()),
                |name| format!("{}.{name}", theorem.name()),
            );
            if label == claim_label {
                return expand_project_pure_theorem_source(
                    project,
                    c_sources,
                    theorem.name(),
                    index,
                );
            }
        }
    }
    for function in proof_function_blocks(&file) {
        if let Some(claim) = function_expansion_claim_by_label(function, claim_label) {
            return expand_c0_project_claim_source(
                project,
                c_sources,
                function.signature().name(),
                claim,
            );
        }
    }
    Err(ClickError::new(format!(
        "could not locate function claim `{claim_label}`"
    )))
}

pub fn expand_c0_prepared_claim_source_by_label(
    click_source: &str,
    imports: &[crate::languages::c::compiler_import::PreparedCImport],
    claim_label: &str,
) -> Result<String, ClickError> {
    let sources = CSourceContext::prepared(imports);
    let file = parse_source_with_c_layouts_context(click_source, &sources)?;
    for theorem in file.theorem_definitions() {
        for (index, ensure) in theorem.ensures().iter().enumerate() {
            let label = ensure.name().map_or_else(
                || format!("{}.ensures_{index}", theorem.name()),
                |name| format!("{}.{name}", theorem.name()),
            );
            if label == claim_label {
                return expand_pure_theorem_source_context(
                    click_source,
                    &sources,
                    theorem.name(),
                    index,
                );
            }
        }
    }
    for function in proof_function_blocks(&file) {
        if let Some(claim) = function_expansion_claim_by_label(function, claim_label) {
            return expand_c0_prepared_claim_source(
                click_source,
                imports,
                function.signature().name(),
                claim,
            );
        }
    }
    Err(ClickError::new(format!(
        "could not locate function claim `{claim_label}`"
    )))
}

pub fn expand_c0_prepared_project_claim_source_by_label(
    project: &ClickProject,
    imports: &[crate::languages::c::compiler_import::PreparedCImport],
    claim_label: &str,
) -> Result<String, ClickError> {
    let sources = CSourceContext::prepared(imports).with_click_project(project);
    let file = resolve_click_project_context(project, &sources)?;
    for theorem in file.theorem_definitions() {
        if !file.theorem_is_selected(theorem.name()) {
            continue;
        }
        for (index, ensure) in theorem.ensures().iter().enumerate() {
            let label = ensure.name().map_or_else(
                || format!("{}.ensures_{index}", theorem.name()),
                |name| format!("{}.{name}", theorem.name()),
            );
            if label == claim_label {
                return expand_prepared_project_pure_theorem_source(
                    project,
                    imports,
                    theorem.name(),
                    index,
                );
            }
        }
    }
    for function in proof_function_blocks(&file) {
        if let Some(claim) = function_expansion_claim_by_label(function, claim_label) {
            return expand_c0_prepared_project_claim_source(
                project,
                imports,
                function.signature().name(),
                claim,
            );
        }
    }
    Err(ClickError::new(format!(
        "could not locate function claim `{claim_label}`"
    )))
}

pub fn expand_program_prepared_claim_source_by_label(
    click_source: &str,
    import: &impl crate::languages::PreparedProgramSource,
    claim_label: &str,
) -> Result<String, ClickError> {
    expand_program_prepared_claim_source_by_label_context(None, click_source, import, claim_label)
}

pub fn expand_program_prepared_project_claim_source_by_label(
    project: &ClickProject,
    import: &impl crate::languages::PreparedProgramSource,
    claim_label: &str,
) -> Result<String, ClickError> {
    let click_source = project
        .entry_source()
        .ok_or_else(|| ClickError::new(format!("missing entry module `{}`", project.entry())))?;
    expand_program_prepared_claim_source_by_label_context(
        Some(project),
        click_source,
        import,
        claim_label,
    )
}

fn expand_program_prepared_claim_source_by_label_context(
    project: Option<&ClickProject>,
    click_source: &str,
    import: &impl crate::languages::PreparedProgramSource,
    claim_label: &str,
) -> Result<String, ClickError> {
    let sources = match project {
        Some(project) => CSourceContext::program(import)?.with_click_project(project),
        None => CSourceContext::program(import)?,
    };
    let file = match project {
        Some(project) => resolve_click_project_context(project, &sources)?,
        None => parse_source_with_c_layouts_context(click_source, &sources)?,
    };
    for theorem in file.theorem_definitions() {
        if project.is_some() && !file.theorem_is_selected(theorem.name()) {
            continue;
        }
        for (index, ensure) in theorem.ensures().iter().enumerate() {
            let label = ensure.name().map_or_else(
                || format!("{}.ensures_{index}", theorem.name()),
                |name| format!("{}.{name}", theorem.name()),
            );
            if label == claim_label {
                let verified = match project {
                    Some(project) => {
                        verify_click_project_theorem_context(project, &sources, theorem.name())?
                    }
                    None => verify_click_theorems_with_context(click_source, &sources)?,
                };
                return rewrite_verified_pure_theorem(
                    click_source,
                    &verified,
                    theorem.name(),
                    index,
                );
            }
        }
    }
    for function in proof_function_blocks(&file) {
        if let Some(claim) = function_expansion_claim_by_label(function, claim_label) {
            return expand_program_prepared_claim_source_context(
                project,
                click_source,
                import,
                function.signature().name(),
                claim,
            );
        }
    }
    Err(ClickError::new(format!(
        "could not locate compiler-imported function claim `{claim_label}`"
    )))
}

fn expand_program_prepared_claim_source_context(
    project: Option<&ClickProject>,
    click_source: &str,
    import: &impl crate::languages::PreparedProgramSource,
    function_name: &str,
    claim: CProofClaim,
) -> Result<String, ClickError> {
    let sources = match project {
        Some(project) => CSourceContext::program(import)?.with_click_project(project),
        None => CSourceContext::program(import)?,
    };
    let file = match project {
        Some(project) => resolve_click_project_context(project, &sources)?,
        None => parse_source_with_c_layouts_context(click_source, &sources)?,
    };
    let tokens = scan_source_tokens(click_source)?;
    let function = find_function(&tokens, function_name)?;
    let function_block = proof_function_blocks(&file)
        .find(|function| function.signature().name() == function_name)
        .ok_or_else(|| ClickError::new(format!("unknown function `{function_name}`")))?;
    let claim = covering_claim(function_block, claim);
    let edit = if claim == CProofClaim::Grouped {
        find_grouped_proof_edit(&tokens, &function, function_block)?
    } else {
        find_claim_proof_edit(&tokens, &function, function_block, claim)?
    };
    let target = position_at_offset(click_source, edit.selector());
    let verified = match project {
        Some(project) => {
            verify_program_prepared_project_at(project, import, target.line, target.column)?
        }
        None => {
            verify_program_prepared_sources_at(click_source, import, target.line, target.column)?
        }
    };
    let theorem = select_expansion_theorem(&verified, function_name, claim)?;
    let replacement = claim_expansion_source(theorem)?;
    let span = edit.span();
    let replacement = indent_replacement(click_source, span.start, &replacement);
    let replacement = match edit {
        ProofSourceEdit::Explicit(_) => replacement,
        ProofSourceEdit::DefaultTerminator { .. } => {
            let separator = click_source[..span.start]
                .chars()
                .next_back()
                .is_some_and(|character| !character.is_whitespace());
            format!("{}{replacement}", if separator { " " } else { "" })
        }
        ProofSourceEdit::OmittedLoopPhase { .. } => unreachable!(),
    };
    Ok(splice_source(click_source, &tokens, span, &replacement))
}

pub use crate::source::SourcePosition;

/// One source-selectable smart tactic in a parsed `.click` sidecar.
///
/// This inventory is purely syntactic: producing it does not execute or verify
/// any proof. `source_index` uses the same pre-order indexing as tactic timing
/// and individual source expansion. Tactics inside a `have` share its
/// claim-level index; `position` identifies each selectable nested site.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SmartTacticSourceSite {
    pub claim_label: String,
    pub source_index: usize,
    pub tactic_name: String,
    /// Exact source position, including tactics nested inside a `have` body.
    pub position: SourcePosition,
}

/// Inventories every source-selectable smart tactic without running proofs.
pub fn c0_smart_tactic_source_sites(
    click_source: &str,
    c_sources: &[(&str, &str)],
) -> Result<Vec<SmartTacticSourceSite>, ClickError> {
    let sources = CSourceContext::bundle(c_sources);
    c0_smart_tactic_source_sites_context(click_source, &sources)
}

pub fn c0_prepared_smart_tactic_source_sites(
    click_source: &str,
    imports: &[crate::languages::c::compiler_import::PreparedCImport],
) -> Result<Vec<SmartTacticSourceSite>, ClickError> {
    let sources = CSourceContext::prepared(imports);
    c0_smart_tactic_source_sites_context(click_source, &sources)
}

pub fn program_prepared_smart_tactic_source_sites(
    click_source: &str,
    import: &impl crate::languages::PreparedProgramSource,
) -> Result<Vec<SmartTacticSourceSite>, ClickError> {
    let sources = CSourceContext::program(import)?;
    c0_smart_tactic_source_sites_context(click_source, &sources)
}

pub fn c0_project_smart_tactic_source_sites(
    project: &ClickProject,
    c_sources: &[(&str, &str)],
) -> Result<Vec<SmartTacticSourceSite>, ClickError> {
    let sources = CSourceContext::bundle(c_sources).with_click_project(project);
    let file = resolve_click_project_context(project, &sources)?;
    c0_smart_tactic_source_sites_file(
        project.entry_source().expect("resolved entry source"),
        &file,
    )
}

pub fn c0_prepared_project_smart_tactic_source_sites(
    project: &ClickProject,
    imports: &[crate::languages::c::compiler_import::PreparedCImport],
) -> Result<Vec<SmartTacticSourceSite>, ClickError> {
    let sources = CSourceContext::prepared(imports).with_click_project(project);
    let file = resolve_click_project_context(project, &sources)?;
    c0_smart_tactic_source_sites_file(
        project.entry_source().expect("resolved entry source"),
        &file,
    )
}

pub fn program_prepared_project_smart_tactic_source_sites(
    project: &ClickProject,
    import: &impl crate::languages::PreparedProgramSource,
) -> Result<Vec<SmartTacticSourceSite>, ClickError> {
    let sources = CSourceContext::program(import)?.with_click_project(project);
    let file = resolve_click_project_context(project, &sources)?;
    c0_smart_tactic_source_sites_file(
        project.entry_source().expect("resolved entry source"),
        &file,
    )
}

fn c0_smart_tactic_source_sites_context(
    click_source: &str,
    sources: &CSourceContext<'_>,
) -> Result<Vec<SmartTacticSourceSite>, ClickError> {
    let file = parse_source_with_c_layouts_context(click_source, sources)?;
    c0_smart_tactic_source_sites_file(click_source, &file)
}

fn c0_smart_tactic_source_sites_file(
    click_source: &str,
    file: &ClickFile,
) -> Result<Vec<SmartTacticSourceSite>, ClickError> {
    let mut sites = Vec::new();
    let mut ordered = Vec::new();
    let mut seen = BTreeSet::new();
    for entry in source_tactic_entries(click_source, file)? {
        if !entry.smart {
            continue;
        }
        let EntrySelection::Located(located) = entry.selection else {
            continue;
        };
        // A smart container owns its body's expansion. Its written child
        // aliases select that same site and must not be counted again.
        if seen.insert((
            entry.claim_label.clone(),
            located.source_index,
            located.nested,
        )) {
            ordered.push((entry.anchor, sites.len()));
            sites.push(SmartTacticSourceSite {
                claim_label: entry.claim_label,
                source_index: located.source_index,
                tactic_name: entry.tactic_name,
                position: SourcePosition::new(1, 1),
            });
        }
    }
    ordered.sort_unstable();
    // Walk characters once, including Unicode columns. Rescanning the whole
    // prefix at every anchor would make a one-line certificate quadratic.
    let mut next = 0;
    let mut line = 1;
    let mut column = 1;
    for (offset, character) in click_source
        .char_indices()
        .chain(std::iter::once((click_source.len(), '\0')))
    {
        while ordered
            .get(next)
            .is_some_and(|(wanted, _)| *wanted == offset)
        {
            sites[ordered[next].1].position = SourcePosition::new(line, column);
            next += 1;
        }
        if next == ordered.len() {
            break;
        }
        if character == '\n' {
            line += 1;
            column = 1;
        } else {
            column += 1;
        }
    }
    if next != ordered.len() {
        return Err(ClickError::new(
            "smart tactic anchor is not a source character boundary",
        ));
    }
    Ok(sites)
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum VerificationTarget {
    Function(String),
    Functions(BTreeSet<String>),
    Theorem(String),
}

pub(super) fn verification_target_at(
    click_source: &str,
    c_sources: &[(&str, &str)],
    line: usize,
    column: usize,
) -> Result<VerificationTarget, ClickError> {
    let sources = CSourceContext::bundle(c_sources);
    verification_target_at_context(click_source, &sources, line, column)
}

pub(super) fn verification_target_at_context(
    click_source: &str,
    c_sources: &CSourceContext<'_>,
    line: usize,
    column: usize,
) -> Result<VerificationTarget, ClickError> {
    let file = parse_source_with_c_layouts_context(click_source, c_sources)?;
    verification_target_at_file(click_source, &file, line, column)
}

pub(in crate::surface) fn verification_target_at_file(
    click_source: &str,
    file: &ClickFile,
    line: usize,
    column: usize,
) -> Result<VerificationTarget, ClickError> {
    let wanted = offset_at_position(click_source, line, column)?;
    let tokens = scan_source_tokens(click_source)?;
    for theorem in file.theorem_definitions() {
        if !file.theorem_is_selected(theorem.name()) {
            continue;
        }
        let source = find_theorem(&tokens, theorem.name())?;
        if tokens[source.body_open].span.start <= wanted
            && wanted <= tokens[source.body_close].span.end
        {
            return Ok(VerificationTarget::Theorem(theorem.name().to_string()));
        }
    }
    for function in proof_function_blocks(file) {
        let function_name = function.signature().name();
        let source = find_function(&tokens, function_name)?;
        let in_body = tokens[source.body_open].span.start <= wanted
            && wanted <= tokens[source.body_close].span.end;
        let in_grouped_proof = function.grouped_proof().is_some()
            && find_grouped_proof_span(&tokens, &source)?.contains(&wanted);
        if in_body || in_grouped_proof {
            return Ok(VerificationTarget::Function(function_name.to_string()));
        }
    }
    Err(ClickError::new(format!(
        "no theorem or C function proof contains source location {line}:{column}"
    )))
}

/// The diagnostic spellings `describe_pointer` falls back to when a kernel
/// pointer has no source form. None of them is Click syntax, so an expansion
/// that renders one cannot parse; expansion has to say which name it is
/// missing instead of handing the parse error on.
const UNSPELLABLE_POINTER_FORMS: [&str; 6] = [
    // The ellipsis `describe_pointer` prints for a heap, temporary or
    // symbolic block no source names.
    "…",
    "symbolic-pointer:",
    "symbolic-function-pointer:",
    "heap-allocation:",
    "arg-memory",
    "string:",
];

/// Reports why a rendered expansion is not Click. A composite resource's
/// existential witness may have no usable source spelling in this scope.
/// When no checked alias names that pointer, report the missing witness
/// name rather than the parse error from diagnostic-only pointer text.
fn unparseable_expansion_error(
    click_source: &str,
    sources: &CSourceContext<'_>,
    replacement: &str,
    parse_error: ClickError,
) -> ClickError {
    let file = parse_source_with_c_layouts_context(click_source, sources).ok();
    unparseable_expansion_error_for_file(replacement, parse_error, file.as_ref())
}

fn unparseable_expansion_error_for_file(
    replacement: &str,
    parse_error: ClickError,
    file: Option<&ClickFile>,
) -> ClickError {
    if !UNSPELLABLE_POINTER_FORMS
        .iter()
        .any(|form| replacement.contains(form))
    {
        return parse_error.with_context("the expansion did not parse as Click");
    }
    let witnesses = file
        .map(|file| {
            file.resource_definitions()
                .iter()
                .filter_map(|definition| {
                    let body = definition.composite_body()?;
                    Some(
                        body.witnesses()
                            .iter()
                            .map(|witness| {
                                format!("`{}` of `{}`", witness.name(), definition.name())
                            })
                            .collect::<Vec<_>>(),
                    )
                })
                .flatten()
                .collect::<Vec<_>>()
        })
        .unwrap_or_default();
    let named = match witnesses.as_slice() {
        [] => "a value the kernel introduced".to_string(),
        [only] => format!("the witness {only}"),
        several => format!("one of the witnesses {}", several.join(", ")),
    };
    ClickError::new(format!(
        "the expansion needs a name for {named}, which has no surface spelling"
    ))
}

/// Rejects a rendered expansion that is not Click before it reaches the
/// caller's verification, so the reported failure is the missing name rather
/// than the parse error the unparseable text produces.
fn checked_expanded_source(
    click_source: &str,
    sources: &CSourceContext<'_>,
    replacement: &str,
    expanded: String,
) -> Result<String, ClickError> {
    match parse_source_with_c_layouts_context(&expanded, sources) {
        Ok(_) => Ok(expanded),
        Err(error) => Err(unparseable_expansion_error(
            click_source,
            sources,
            replacement,
            error,
        )),
    }
}

/// Expands one tactic and returns the rewritten source.
///
/// Certificate capture verifies the selected proof prefix. The caller is
/// responsible for verifying the returned sidecar and its proof suffix.
pub fn expand_c0_tactic_source_at(
    click_source: &str,
    c_sources: &[(&str, &str)],
    line: usize,
    column: usize,
) -> Result<String, ClickError> {
    expand_c0_tactic_source_at_context(None, click_source, c_sources, line, column)
}

pub fn expand_c0_project_tactic_source_at(
    project: &ClickProject,
    c_sources: &[(&str, &str)],
    line: usize,
    column: usize,
) -> Result<String, ClickError> {
    let click_source = project
        .entry_source()
        .ok_or_else(|| ClickError::new(format!("missing entry module `{}`", project.entry())))?;
    expand_c0_tactic_source_at_context(Some(project), click_source, c_sources, line, column)
}

fn expand_c0_tactic_source_at_context(
    project: Option<&ClickProject>,
    click_source: &str,
    c_sources: &[(&str, &str)],
    line: usize,
    column: usize,
) -> Result<String, ClickError> {
    let selected = if let Some(project) = project {
        let sources = CSourceContext::bundle(c_sources).with_click_project(project);
        let file = resolve_click_project_context(project, &sources)?;
        locate_source_tactic_file(click_source, &file, line, column)?
    } else {
        locate_source_tactic(click_source, c_sources, line, column)?
    };
    if let ProofSite::TheoremEnsure {
        theorem_name,
        ensure_index,
    } = &selected.site
    {
        return if let Some(project) = project {
            expand_project_pure_theorem_source(project, c_sources, theorem_name, *ensure_index)
        } else {
            expand_pure_theorem_source(click_source, c_sources, theorem_name, *ensure_index)
        };
    }
    if let (
        ProofSite::FunctionClaim {
            function_name,
            claim,
        },
        TacticSourceEdit::WholeProof(_),
    ) = (&selected.site, &selected.edit)
    {
        return if let Some(project) = project {
            expand_c0_project_claim_source(project, c_sources, function_name, *claim)
        } else {
            expand_c0_claim_source(click_source, c_sources, function_name, *claim)
        };
    }
    let replacement_tactics = match &selected.edit {
        TacticSourceEdit::Partial(_) | TacticSourceEdit::PartialProofClause(_) => {
            if let Some(project) = project {
                super::proof::capture_c0_project_tactic_expansion(
                    project,
                    c_sources,
                    selected.site.clone(),
                    selected.source_index,
                    &selected.nested,
                )?
            } else {
                super::proof::capture_c0_tactic_expansion(
                    click_source,
                    c_sources,
                    selected.site.clone(),
                    selected.source_index,
                    &selected.nested,
                )?
            }
        }
        TacticSourceEdit::WholeProof(_) => {
            if let Some(project) = project {
                super::proof::capture_c0_project_proof_site_expansion(
                    project,
                    c_sources,
                    selected.site.clone(),
                )?
            } else {
                super::proof::capture_c0_proof_site_expansion(
                    click_source,
                    c_sources,
                    selected.site.clone(),
                )?
            }
        }
    };
    let (span, replacement) = match selected.edit.clone() {
        TacticSourceEdit::Partial(span) => (
            selected.replaced_span(span),
            super::printing::format_partial_tactic_sequence(&replacement_tactics),
        ),
        TacticSourceEdit::PartialProofClause(span) => {
            let certificate =
                ProofCertificate::from_proof_tactics(&replacement_tactics).map_err(|error| {
                    ClickError::new(format!(
                        "selected tactic did not produce a surface certificate: its expansion still contains {}",
                        error.message()
                    ))
                })?;
            (
                span,
                super::printing::format_proof_certificate(&certificate),
            )
        }
        TacticSourceEdit::WholeProof(edit) => {
            let certificate =
                ProofCertificate::from_proof_tactics(&replacement_tactics).map_err(|error| {
                    ClickError::new(format!(
                        "selected tactic did not produce a surface certificate: its expansion still contains {}",
                        error.message()
                    ))
                })?;
            let replacement = super::printing::format_proof_certificate(&certificate);
            let span = edit.span().clone();
            let replacement = match edit {
                ProofSourceEdit::Explicit(_) => replacement,
                ProofSourceEdit::DefaultTerminator { .. } => {
                    let separator = click_source[..span.start]
                        .chars()
                        .next_back()
                        .is_some_and(|character| !character.is_whitespace());
                    format!("{}{replacement}", if separator { " " } else { "" })
                }
                ProofSourceEdit::OmittedLoopPhase { phase, .. } => {
                    let replacement = replacement.replace('\n', "\n    ");
                    format!("    {phase} {replacement}\n")
                }
            };
            (span, replacement)
        }
    };
    // A tactic that contributed no step is removed, but a `by { ... }` block
    // must hold at least one tactic. When it is the only tactic of its
    // block, the block keeps `assumption();`, the step a phase with nothing
    // to prove is checked by.
    let replacement = if replacement.is_empty()
        && click_source[..span.start].trim_end().ends_with('{')
        && click_source[span.end..].trim_start().starts_with('}')
    {
        "assumption();".to_string()
    } else {
        replacement
    };
    // An empty replacement removes the selected tactic: take its whole line
    // when nothing else shares it, so the rewrite leaves no blank residue.
    let span = if replacement.is_empty() {
        let line_start = click_source[..span.start]
            .rfind('\n')
            .map_or(0, |index| index + 1);
        let line_end = click_source[span.end..]
            .find('\n')
            .map_or(click_source.len(), |index| span.end + index + 1);
        if click_source[line_start..span.start].trim().is_empty()
            && click_source[span.end..line_end].trim().is_empty()
        {
            line_start..line_end
        } else {
            span
        }
    } else {
        span
    };
    let replacement = indent_replacement(click_source, span.start, &replacement);
    let expanded = splice_source(
        click_source,
        &scan_source_tokens(click_source)?,
        &span,
        &replacement,
    );
    if let Some(project) = project {
        let rewritten = project.with_entry_source(expanded.clone());
        let sources = CSourceContext::bundle(c_sources).with_click_project(&rewritten);
        match resolve_click_project_context(&rewritten, &sources) {
            Ok(_) => Ok(expanded),
            Err(error) => {
                let original_sources =
                    CSourceContext::bundle(c_sources).with_click_project(project);
                let original = resolve_click_project_context(project, &original_sources).ok();
                Err(unparseable_expansion_error_for_file(
                    &replacement,
                    error,
                    original.as_ref(),
                ))
            }
        }
    } else {
        checked_expanded_source(
            click_source,
            &CSourceContext::bundle(c_sources),
            &replacement,
            expanded,
        )
    }
}

/// Expands one tactic using compiler-prepared translation units throughout
/// location, capture, and certificate verification.
pub fn expand_c0_prepared_tactic_source_at(
    click_source: &str,
    imports: &[crate::languages::c::compiler_import::PreparedCImport],
    line: usize,
    column: usize,
) -> Result<String, ClickError> {
    expand_c0_prepared_tactic_source_at_context(None, click_source, imports, line, column)
}

pub fn expand_c0_prepared_project_tactic_source_at(
    project: &ClickProject,
    imports: &[crate::languages::c::compiler_import::PreparedCImport],
    line: usize,
    column: usize,
) -> Result<String, ClickError> {
    let click_source = project
        .entry_source()
        .ok_or_else(|| ClickError::new(format!("missing entry module `{}`", project.entry())))?;
    expand_c0_prepared_tactic_source_at_context(Some(project), click_source, imports, line, column)
}

pub fn expand_program_prepared_tactic_source_at(
    click_source: &str,
    import: &impl crate::languages::PreparedProgramSource,
    line: usize,
    column: usize,
) -> Result<String, ClickError> {
    expand_program_prepared_tactic_source_at_context(None, click_source, import, line, column)
}

pub fn expand_program_prepared_project_tactic_source_at(
    project: &ClickProject,
    import: &impl crate::languages::PreparedProgramSource,
    line: usize,
    column: usize,
) -> Result<String, ClickError> {
    let click_source = project
        .entry_source()
        .ok_or_else(|| ClickError::new(format!("missing entry module `{}`", project.entry())))?;
    expand_program_prepared_tactic_source_at_context(
        Some(project),
        click_source,
        import,
        line,
        column,
    )
}

fn expand_program_prepared_tactic_source_at_context(
    project: Option<&ClickProject>,
    click_source: &str,
    import: &impl crate::languages::PreparedProgramSource,
    line: usize,
    column: usize,
) -> Result<String, ClickError> {
    let sources = match project {
        Some(project) => CSourceContext::program(import)?.with_click_project(project),
        None => CSourceContext::program(import)?,
    };
    let file = match project {
        Some(project) => resolve_click_project_context(project, &sources)?,
        None => parse_source_with_c_layouts_context(click_source, &sources)?,
    };
    let selected = locate_source_tactic_file(click_source, &file, line, column)?;
    if let ProofSite::TheoremEnsure {
        theorem_name,
        ensure_index,
    } = &selected.site
    {
        let verified = match project {
            Some(project) => verify_click_project_theorem_context(project, &sources, theorem_name)?,
            None => verify_click_theorems_with_context(click_source, &sources)?,
        };
        return rewrite_verified_pure_theorem(click_source, &verified, theorem_name, *ensure_index);
    }
    if let (
        ProofSite::FunctionClaim {
            function_name,
            claim,
        },
        TacticSourceEdit::WholeProof(_),
    ) = (&selected.site, &selected.edit)
    {
        return expand_program_prepared_claim_source_context(
            project,
            click_source,
            import,
            function_name,
            *claim,
        );
    }
    let reference_result = match &selected.site {
        ProofSite::FunctionClaim { function_name, .. }
        | ProofSite::LoopPhase { function_name, .. } => proof_function_blocks(&file)
            .find(|block| block.signature().name() == function_name)
            .is_some_and(|block| block.signature().returns_reference()),
        ProofSite::TheoremEnsure { .. } => false,
    };
    let _reference_result_source =
        super::diagnostics::ReferenceResultSourceScope::enter(reference_result);
    let replacement_tactics = match &selected.edit {
        TacticSourceEdit::Partial(_) | TacticSourceEdit::PartialProofClause(_) => {
            if let Some(project) = project {
                super::proof::capture_program_prepared_project_tactic_expansion(
                    project,
                    import,
                    selected.site.clone(),
                    selected.source_index,
                    &selected.nested,
                )?
            } else {
                super::proof::capture_program_prepared_tactic_expansion(
                    click_source,
                    import,
                    selected.site.clone(),
                    selected.source_index,
                    &selected.nested,
                )?
            }
        }
        TacticSourceEdit::WholeProof(_) => {
            if let Some(project) = project {
                super::proof::capture_program_prepared_project_proof_site_expansion(
                    project,
                    import,
                    selected.site.clone(),
                )?
            } else {
                super::proof::capture_program_prepared_proof_site_expansion(
                    click_source,
                    import,
                    selected.site.clone(),
                )?
            }
        }
    };
    let (span, replacement) = match selected.edit.clone() {
        TacticSourceEdit::Partial(span) => (
            selected.replaced_span(span),
            super::printing::format_partial_tactic_sequence(&replacement_tactics),
        ),
        TacticSourceEdit::PartialProofClause(span) => {
            let certificate =
                ProofCertificate::from_proof_tactics(&replacement_tactics).map_err(|error| {
                    ClickError::new(format!(
                        "selected tactic did not produce a surface certificate: its expansion still contains {}",
                        error.message()
                    ))
                })?;
            (
                span,
                super::printing::format_proof_certificate(&certificate),
            )
        }
        TacticSourceEdit::WholeProof(edit) => {
            let certificate =
                ProofCertificate::from_proof_tactics(&replacement_tactics).map_err(|error| {
                    ClickError::new(format!(
                        "selected tactic did not produce a surface certificate: its expansion still contains {}",
                        error.message()
                    ))
                })?;
            let replacement = super::printing::format_proof_certificate(&certificate);
            let span = edit.span().clone();
            let replacement = match edit {
                ProofSourceEdit::Explicit(_) => replacement,
                ProofSourceEdit::DefaultTerminator { .. } => {
                    let separator = click_source[..span.start]
                        .chars()
                        .next_back()
                        .is_some_and(|character| !character.is_whitespace());
                    format!("{}{replacement}", if separator { " " } else { "" })
                }
                ProofSourceEdit::OmittedLoopPhase { phase, .. } => {
                    format!("    {phase} {}\n", replacement.replace('\n', "\n    "))
                }
            };
            (span, replacement)
        }
    };
    let expanded = splice_source(
        click_source,
        &scan_source_tokens(click_source)?,
        &span,
        &replacement,
    );
    checked_expanded_source(click_source, &sources, &replacement, expanded)
}

fn expand_c0_prepared_tactic_source_at_context(
    project: Option<&ClickProject>,
    click_source: &str,
    imports: &[crate::languages::c::compiler_import::PreparedCImport],
    line: usize,
    column: usize,
) -> Result<String, ClickError> {
    let sources = CSourceContext::prepared(imports);
    let selected = if let Some(project) = project {
        let project_sources = CSourceContext::prepared(imports).with_click_project(project);
        let file = resolve_click_project_context(project, &project_sources)?;
        locate_source_tactic_file(click_source, &file, line, column)?
    } else {
        locate_source_tactic_context(click_source, &sources, line, column)?
    };
    if let ProofSite::TheoremEnsure {
        theorem_name,
        ensure_index,
    } = &selected.site
    {
        return if let Some(project) = project {
            expand_prepared_project_pure_theorem_source(
                project,
                imports,
                theorem_name,
                *ensure_index,
            )
        } else {
            expand_pure_theorem_source_context(click_source, &sources, theorem_name, *ensure_index)
        };
    }
    if let (
        ProofSite::FunctionClaim {
            function_name,
            claim,
        },
        TacticSourceEdit::WholeProof(_),
    ) = (&selected.site, &selected.edit)
    {
        return if let Some(project) = project {
            expand_c0_prepared_project_claim_source(project, imports, function_name, *claim)
        } else {
            expand_c0_prepared_claim_source(click_source, imports, function_name, *claim)
        };
    }
    let replacement_tactics = match &selected.edit {
        TacticSourceEdit::Partial(_) | TacticSourceEdit::PartialProofClause(_) => {
            if let Some(project) = project {
                super::proof::capture_c0_prepared_project_tactic_expansion(
                    project,
                    imports,
                    selected.site.clone(),
                    selected.source_index,
                    &selected.nested,
                )?
            } else {
                super::proof::capture_c0_prepared_tactic_expansion(
                    click_source,
                    imports,
                    selected.site.clone(),
                    selected.source_index,
                    &selected.nested,
                )?
            }
        }
        TacticSourceEdit::WholeProof(_) => {
            if let Some(project) = project {
                super::proof::capture_c0_prepared_project_proof_site_expansion(
                    project,
                    imports,
                    selected.site.clone(),
                )?
            } else {
                super::proof::capture_c0_prepared_proof_site_expansion(
                    click_source,
                    imports,
                    selected.site.clone(),
                )?
            }
        }
    };
    let (span, replacement) = match selected.edit.clone() {
        TacticSourceEdit::Partial(span) => (
            selected.replaced_span(span),
            super::printing::format_partial_tactic_sequence(&replacement_tactics),
        ),
        TacticSourceEdit::PartialProofClause(span) => {
            let certificate =
                ProofCertificate::from_proof_tactics(&replacement_tactics).map_err(|error| {
                    ClickError::new(format!(
                        "selected tactic did not produce a surface certificate: its expansion still contains {}",
                        error.message()
                    ))
                })?;
            (
                span,
                super::printing::format_proof_certificate(&certificate),
            )
        }
        TacticSourceEdit::WholeProof(edit) => {
            let certificate =
                ProofCertificate::from_proof_tactics(&replacement_tactics).map_err(|error| {
                    ClickError::new(format!(
                        "selected tactic did not produce a surface certificate: its expansion still contains {}",
                        error.message()
                    ))
                })?;
            let replacement = super::printing::format_proof_certificate(&certificate);
            let span = edit.span().clone();
            let replacement = match edit {
                ProofSourceEdit::Explicit(_) => replacement,
                ProofSourceEdit::DefaultTerminator { .. } => {
                    let separator = click_source[..span.start]
                        .chars()
                        .next_back()
                        .is_some_and(|character| !character.is_whitespace());
                    format!("{}{replacement}", if separator { " " } else { "" })
                }
                ProofSourceEdit::OmittedLoopPhase { phase, .. } => {
                    format!("    {phase} {}\n", replacement.replace('\n', "\n    "))
                }
            };
            (span, replacement)
        }
    };
    let expanded = splice_source(
        click_source,
        &scan_source_tokens(click_source)?,
        &span,
        &replacement,
    );
    if let Some(project) = project {
        let rewritten = project.with_entry_source(expanded.clone());
        let project_sources = CSourceContext::prepared(imports).with_click_project(&rewritten);
        match resolve_click_project_context(&rewritten, &project_sources) {
            Ok(_) => Ok(expanded),
            Err(error) => {
                let original_sources =
                    CSourceContext::prepared(imports).with_click_project(project);
                let original = resolve_click_project_context(project, &original_sources).ok();
                Err(unparseable_expansion_error_for_file(
                    &replacement,
                    error,
                    original.as_ref(),
                ))
            }
        }
    } else {
        checked_expanded_source(click_source, &sources, &replacement, expanded)
    }
}

fn expand_pure_theorem_source(
    click_source: &str,
    c_sources: &[(&str, &str)],
    theorem_name: &str,
    ensure_index: usize,
) -> Result<String, ClickError> {
    let sources = CSourceContext::bundle(c_sources);
    expand_pure_theorem_source_context(click_source, &sources, theorem_name, ensure_index)
}

fn expand_project_pure_theorem_source(
    project: &ClickProject,
    c_sources: &[(&str, &str)],
    theorem_name: &str,
    ensure_index: usize,
) -> Result<String, ClickError> {
    let click_source = project
        .entry_source()
        .ok_or_else(|| ClickError::new(format!("missing entry module `{}`", project.entry())))?;
    let verified = verify_click_project_theorem(project, c_sources, theorem_name)?;
    rewrite_verified_pure_theorem(click_source, &verified, theorem_name, ensure_index)
}

fn expand_prepared_project_pure_theorem_source(
    project: &ClickProject,
    imports: &[crate::languages::c::compiler_import::PreparedCImport],
    theorem_name: &str,
    ensure_index: usize,
) -> Result<String, ClickError> {
    let click_source = project
        .entry_source()
        .ok_or_else(|| ClickError::new(format!("missing entry module `{}`", project.entry())))?;
    let verified = verify_click_prepared_project_theorem(project, imports, theorem_name)?;
    rewrite_verified_pure_theorem(click_source, &verified, theorem_name, ensure_index)
}

fn expand_pure_theorem_source_context(
    click_source: &str,
    sources: &CSourceContext<'_>,
    theorem_name: &str,
    ensure_index: usize,
) -> Result<String, ClickError> {
    let verified = verify_click_theorems_with_context(click_source, sources)?;
    rewrite_verified_pure_theorem(click_source, &verified, theorem_name, ensure_index)
}

fn rewrite_verified_pure_theorem(
    click_source: &str,
    verified: &[VerifiedPureTheorem],
    theorem_name: &str,
    ensure_index: usize,
) -> Result<String, ClickError> {
    let tokens = scan_source_tokens(click_source)?;
    let theorem = verified
        .iter()
        .find(|theorem| {
            theorem.theorem_definition.name() == theorem_name
                && theorem.ensure_index == ensure_index
        })
        .ok_or_else(|| {
            ClickError::new(format!(
                "verified theorem `{theorem_name}` has no ensure {ensure_index}"
            ))
        })?;
    let replacement = theorem.expanded_proof_source()?;
    let source = find_theorem(&tokens, theorem_name)?;
    let edit = find_ensure_proof_edit(&tokens, source.body_open, source.body_close, ensure_index)?;
    let span = edit.span();
    let replacement = indent_replacement(click_source, span.start, &replacement);
    let replacement = match edit {
        ProofSourceEdit::Explicit(_) => replacement,
        ProofSourceEdit::DefaultTerminator { .. } => {
            let separator = click_source[..span.start]
                .chars()
                .next_back()
                .is_some_and(|character| !character.is_whitespace());
            format!("{}{replacement}", if separator { " " } else { "" })
        }
        ProofSourceEdit::OmittedLoopPhase { .. } => {
            unreachable!("theorem ensure edits are never loop phases")
        }
    };
    Ok(splice_source(click_source, &tokens, span, &replacement))
}

/// Spells the checked certificate that replaces a whole claim proof.
/// Written nesting is not a driver bound: terminal cases can be processed
/// iteratively. As with tactic expansion, the caller verifies the rewrite.
fn claim_expansion_source(theorem: &VerifiedCTheorem) -> Result<String, ClickError> {
    let _reference_result_source = super::diagnostics::ReferenceResultSourceScope::enter(
        theorem.function_block.signature().returns_reference(),
    );
    let certificate = theorem.expanded_proof_certificate()?;
    if !theorem.function_block.is_tactic_procedure() {
        return Ok(super::printing::format_proof_certificate(&certificate));
    }
    // A tactic's proof is checked with a fixed ending on every path: one
    // step over the empty procedure's `return`, then an `assumption` per
    // claim. That ending is supplied by the checker and cannot be written in
    // a tactic's proof, which runs no code, so the expansion leaves it out.
    let mut tactics = certificate.to_proof_tactics();
    let ending = 1 + theorem.function_block.ensures().len();
    remove_tactic_procedure_ending(&mut tactics, ending).map_err(|()| {
        ClickError::new(format!(
            "the expanded proof of tactic `{}` does not end in the step and {} closing assumption(s) its check supplies",
            theorem.function_block.signature().name(),
            ending - 1
        ))
    })?;
    Ok(super::printing::format_proof_block(&tactics))
}

/// Removes the `ending` tactics the checker appends where each path of a
/// tactic's proof ends: at the end of the script, or of each arm of a final
/// proof `match`.
fn remove_tactic_procedure_ending(tactics: &mut Vec<ProofTactic>, ending: usize) -> Result<(), ()> {
    if let Some(ProofTactic::Match(proof_match)) = tactics.last_mut() {
        for arm in &mut std::sync::Arc::make_mut(proof_match).arms {
            remove_tactic_procedure_ending(&mut arm.tactics, ending)?;
        }
        return Ok(());
    }
    let kept = tactics.len().checked_sub(ending).ok_or(())?;
    let supplied = matches!(tactics[kept], ProofTactic::Step)
        && tactics[kept + 1..]
            .iter()
            .all(|tactic| matches!(tactic, ProofTactic::Assumption));
    if !supplied {
        return Err(());
    }
    tactics.truncate(kept);
    Ok(())
}

fn select_expansion_theorem<'a>(
    verified: &'a [VerifiedCTheorem],
    function_name: &str,
    claim: CProofClaim,
) -> Result<&'a VerifiedCTheorem, ClickError> {
    let matches_function =
        |theorem: &&VerifiedCTheorem| theorem.function_block.signature().name() == function_name;
    let selected = match claim {
        CProofClaim::Ensure(index) => verified.iter().find(|theorem| {
            matches_function(theorem)
                && matches!(theorem.claim, VerifiedClaim::Ensure { index: found, .. } if found == index)
        }),
        CProofClaim::ExceptionalEnsure(index) => verified.iter().find(|theorem| {
            matches_function(theorem)
                && matches!(theorem.claim, VerifiedClaim::ExceptionalEnsure { index: found, .. } if found == index)
        }),
        CProofClaim::Grouped => verified
            .iter()
            .find(|theorem| {
                matches_function(theorem)
                    && match &theorem.claim {
                        VerifiedClaim::Ensure { clause, .. }
                        | VerifiedClaim::ExceptionalEnsure { clause, .. } => {
                            theorem.function_block.covers_claim_proof(clause.proof())
                        }
                    }
            })
            .or_else(|| verified.iter().find(matches_function)),
    };
    selected.ok_or_else(|| {
        ClickError::new(format!(
            "verified function `{function_name}` has no verified {}",
            claim.describe()
        ))
    })
}

#[derive(Clone, Debug)]
struct SourceToken {
    text: String,
    span: Range<usize>,
}

#[derive(Clone, Copy)]
struct FunctionSource {
    body_open: usize,
    body_close: usize,
}

fn scan_source_tokens(source: &str) -> Result<Vec<SourceToken>, ClickError> {
    let mut tokens = Vec::new();
    let mut index = 0;
    while index < source.len() {
        let character = source[index..]
            .chars()
            .next()
            .expect("index is maintained at a character boundary");
        if character.is_whitespace() {
            index += character.len_utf8();
            continue;
        }
        if character == '#' {
            index += source[index..].find('\n').unwrap_or(source.len() - index);
            continue;
        }
        let start = index;
        if character.is_ascii_alphabetic() || character == '_' {
            index += character.len_utf8();
            while index < source.len() {
                let next = source[index..]
                    .chars()
                    .next()
                    .expect("index is maintained at a character boundary");
                if !next.is_ascii_alphanumeric() && next != '_' {
                    break;
                }
                index += next.len_utf8();
            }
        } else if character.is_ascii_digit() {
            index += character.len_utf8();
            while index < source.len() {
                let next = source[index..]
                    .chars()
                    .next()
                    .expect("index is maintained at a character boundary");
                if !next.is_ascii_digit() {
                    break;
                }
                index += next.len_utf8();
            }
        } else if matches!(character, '"' | '\'') {
            let quote = character;
            index += character.len_utf8();
            let mut terminated = false;
            while index < source.len() {
                let next = source[index..]
                    .chars()
                    .next()
                    .expect("index is maintained at a character boundary");
                index += next.len_utf8();
                if next == '\\' {
                    if index < source.len() {
                        let escaped = source[index..]
                            .chars()
                            .next()
                            .expect("index is maintained at a character boundary");
                        index += escaped.len_utf8();
                    }
                } else if next == quote {
                    terminated = true;
                    break;
                }
            }
            if !terminated {
                return Err(ClickError::new(
                    "unterminated literal while locating proof source",
                ));
            }
        } else {
            index += character.len_utf8();
        }
        tokens.push(SourceToken {
            text: source[start..index].to_string(),
            span: start..index,
        });
    }
    with_implicit_proof_blocks(tokens)
}

/// A proof written as one tactic, `by T(args);`, is the block
/// `by { T(args); }` without its braces. Every reader below addresses a
/// proof's tactics through the block that holds them, so the scan supplies
/// the missing pair as zero-width tokens at the tactic's two ends. Their
/// spans are exact source positions, and [`splice_source`] writes the braces
/// out whenever a rewrite lands inside one.
fn with_implicit_proof_blocks(
    mut tokens: Vec<SourceToken>,
) -> Result<Vec<SourceToken>, ClickError> {
    let mut index = 0;
    while index + 2 < tokens.len() {
        let starts_tactic_call = tokens[index].text == "by"
            && tokens[index + 1]
                .text
                .starts_with(|character: char| character.is_ascii_alphabetic() || character == '_')
            && tokens[index + 2].text == "(";
        if !starts_tactic_call {
            index += 1;
            continue;
        }
        let first = index + 1;
        let last = tactic_end_token(&tokens, first, tokens.len())?;
        let open = tokens[first].span.start;
        let close = tokens[last].span.end;
        tokens.insert(
            last + 1,
            SourceToken {
                text: "}".to_string(),
                span: close..close,
            },
        );
        tokens.insert(
            first,
            SourceToken {
                text: "{".to_string(),
                span: open..open,
            },
        );
        // Continue inside the tactic: it may hold a nested one-tactic proof.
        index = first + 1;
    }
    Ok(tokens)
}

/// `source` with `span` replaced by `replacement`. A span inside an implicit
/// proof block (see [`with_implicit_proof_blocks`]) gets that block's braces
/// written out, since the replacement may be more than one tactic.
fn splice_source(
    source: &str,
    tokens: &[SourceToken],
    span: &Range<usize>,
    replacement: &str,
) -> String {
    let mut open_blocks = Vec::new();
    let mut enclosing: Option<Range<usize>> = None;
    for token in tokens.iter().filter(|token| token.span.is_empty()) {
        if token.text == "{" {
            open_blocks.push(token.span.start);
        } else if let Some(open) = open_blocks.pop()
            && open <= span.start
            && span.end <= token.span.start
            && enclosing
                .as_ref()
                .is_none_or(|outer| outer.start <= open && token.span.start <= outer.end)
        {
            // Blocks close innermost first, so the first match is the
            // innermost and later, wider ones are skipped.
            if enclosing.is_none() {
                enclosing = Some(open..token.span.start);
            }
        }
    }
    let whole_block_rewritten_as_a_block = enclosing.as_ref().is_some_and(|block| {
        block.start == span.start
            && block.end == span.end
            && replacement.trim_start().starts_with('{')
    });
    let mut spliced = String::with_capacity(source.len() + replacement.len() + 4);
    match enclosing {
        Some(block) if !whole_block_rewritten_as_a_block => {
            spliced.push_str(&source[..block.start]);
            spliced.push_str("{ ");
            spliced.push_str(&source[block.start..span.start]);
            spliced.push_str(replacement);
            spliced.push_str(&source[span.end..block.end]);
            spliced.push_str(" }");
            spliced.push_str(&source[block.end..]);
        }
        _ => {
            spliced.push_str(&source[..span.start]);
            spliced.push_str(replacement);
            spliced.push_str(&source[span.end..]);
        }
    }
    spliced
}

/// Every block whose proof the expansion tools address: the C function
/// blocks, then each user-defined tactic, whose `by` script is its contract's
/// one grouped proof. A tactic is declared before any proof applies it, so
/// [`find_function`] reaches its declaration first.
fn proof_function_blocks(file: &ClickFile) -> impl Iterator<Item = &FunctionBlock> {
    file.function_blocks().iter().chain(
        file.tactic_definitions()
            .iter()
            .map(TacticDefinition::function_block),
    )
}

/// The token after a Rust signature's return type, `-> T` or `-> ()`, when
/// one starts at `index`; `index` itself otherwise.
fn after_rust_return_type(tokens: &[SourceToken], index: usize) -> usize {
    let text = |at: usize| tokens.get(at).map(|token| token.text.as_str());
    if text(index) != Some("-") || text(index + 1) != Some(">") {
        return index;
    }
    if text(index + 2) == Some("(") {
        index + 4
    } else {
        index + 3
    }
}

/// The token range of the `impl Type { ... }` or `impl Trait for Type { ... }`
/// block whose methods are the functions `Type_name`, and the method's own
/// name, when `name` is such a function.
fn rust_impl_method<'a>(
    tokens: &[SourceToken],
    name: &'a str,
) -> Result<Option<(Range<usize>, &'a str)>, ClickError> {
    let mut index = 0;
    while index < tokens.len() {
        if tokens[index].text != "impl" {
            index += 1;
            continue;
        }
        let Some(open) = (index..tokens.len()).find(|at| tokens[*at].text == "{") else {
            return Ok(None);
        };
        let close = matching_delimiter(tokens, open, "{", "}")?;
        let impl_type = tokens[open - 1].text.as_str();
        if let Some(method) = name
            .strip_prefix(impl_type)
            .and_then(|rest| rest.strip_prefix('_'))
        {
            return Ok(Some((open + 1..close, method)));
        }
        index = close + 1;
    }
    Ok(None)
}

fn find_function(tokens: &[SourceToken], name: &str) -> Result<FunctionSource, ClickError> {
    if let Some((block, method)) = rust_impl_method(tokens, name)? {
        let found = find_function(&tokens[block.clone()], method)?;
        return Ok(FunctionSource {
            body_open: found.body_open + block.start,
            body_close: found.body_close + block.start,
        });
    }
    for (index, token) in tokens.iter().enumerate() {
        if token.text != name || tokens.get(index + 1).map(|token| token.text.as_str()) != Some("(")
        {
            continue;
        }
        let parameters_close = matching_delimiter(tokens, index + 1, "(", ")")?;
        let mut body_open = after_rust_return_type(tokens, parameters_close + 1);
        if tokens.get(body_open).map(|token| token.text.as_str()) == Some("throws") {
            body_open += 2;
        }
        if tokens.get(body_open).map(|token| token.text.as_str()) == Some("diverges") {
            body_open += 1;
        }
        if tokens.get(body_open).map(|token| token.text.as_str()) != Some("{") {
            continue;
        }
        let body_close = matching_delimiter(tokens, body_open, "{", "}")?;
        return Ok(FunctionSource {
            body_open,
            body_close,
        });
    }
    Err(ClickError::new(format!(
        "could not locate Click function block `{name}`"
    )))
}

/// The `tactic name(...) { ... }` declaration of `name`. Only the declaration
/// has the `tactic` keyword before the name; an application `name(..., { ... })`
/// inside a proof is never matched.
fn find_tactic(tokens: &[SourceToken], name: &str) -> Result<FunctionSource, ClickError> {
    for (index, token) in tokens.iter().enumerate() {
        if token.text != "tactic"
            || tokens.get(index + 1).map(|token| token.text.as_str()) != Some(name)
            || tokens.get(index + 2).map(|token| token.text.as_str()) != Some("(")
        {
            continue;
        }
        let parameters_close = matching_delimiter(tokens, index + 2, "(", ")")?;
        let body_open = parameters_close + 1;
        if tokens.get(body_open).map(|token| token.text.as_str()) != Some("{") {
            continue;
        }
        let body_close = matching_delimiter(tokens, body_open, "{", "}")?;
        return Ok(FunctionSource {
            body_open,
            body_close,
        });
    }
    Err(ClickError::new(format!(
        "could not locate Click tactic `{name}`"
    )))
}

fn find_theorem(tokens: &[SourceToken], name: &str) -> Result<FunctionSource, ClickError> {
    for (index, token) in tokens.iter().enumerate() {
        if token.text != "theorem"
            || tokens.get(index + 1).map(|token| token.text.as_str()) != Some(name)
        {
            continue;
        }
        let mut parameters_open = index + 2;
        if tokens.get(parameters_open).map(|token| token.text.as_str()) == Some("<") {
            parameters_open = matching_delimiter(tokens, parameters_open, "<", ">")? + 1;
        }
        if tokens.get(parameters_open).map(|token| token.text.as_str()) != Some("(") {
            continue;
        }
        let parameters_close = matching_delimiter(tokens, parameters_open, "(", ")")?;
        let mut body_open = parameters_close + 1;
        if tokens.get(body_open).map(|token| token.text.as_str()) == Some("executes") {
            let arguments_open = body_open + 2;
            body_open = matching_delimiter(tokens, arguments_open, "(", ")")? + 1;
        }
        if tokens.get(body_open).map(|token| token.text.as_str()) != Some("{") {
            continue;
        }
        let body_close = matching_delimiter(tokens, body_open, "{", "}")?;
        return Ok(FunctionSource {
            body_open,
            body_close,
        });
    }
    Err(ClickError::new(format!(
        "could not locate Click theorem `{name}`"
    )))
}

fn find_ensure_proof_edit(
    tokens: &[SourceToken],
    body_open: usize,
    body_close: usize,
    wanted: usize,
) -> Result<ProofSourceEdit, ClickError> {
    let mut depth = 0;
    let mut found = 0;
    let mut index = body_open + 1;
    while index < body_close {
        match tokens[index].text.as_str() {
            "{" => depth += 1,
            "}" => depth -= 1,
            "ensures"
                if depth == 0
                    && tokens
                        .get(index.wrapping_sub(1))
                        .map(|token| token.text.as_str())
                        != Some("exceptional") =>
            {
                if found == wanted {
                    return find_proof_edit_after(tokens, index, body_close);
                }
                found += 1;
            }
            "owns" | "produces" if depth == 0 => {
                if found == wanted {
                    return find_proof_edit_after(tokens, index, body_close);
                }
                found += 1;
            }
            _ => {}
        }
        index += 1;
    }
    Err(ClickError::new(format!(
        "could not locate source ensure {wanted}"
    )))
}

fn find_exceptional_ensure_proof_edit(
    tokens: &[SourceToken],
    body_open: usize,
    body_close: usize,
    wanted: usize,
) -> Result<ProofSourceEdit, ClickError> {
    let mut depth = 0;
    let mut found = 0;
    let mut index = body_open + 1;
    while index < body_close {
        match tokens[index].text.as_str() {
            "{" => depth += 1,
            "}" => depth -= 1,
            "exceptional"
                if depth == 0
                    && tokens.get(index + 1).map(|token| token.text.as_str())
                        == Some("ensures") =>
            {
                if found == wanted {
                    return find_proof_edit_after(tokens, index + 1, body_close);
                }
                found += 1;
            }
            _ => {}
        }
        index += 1;
    }
    Err(ClickError::new(format!(
        "could not locate source exceptional ensure {wanted}"
    )))
}

fn find_proof_edit_after(
    tokens: &[SourceToken],
    clause_start: usize,
    limit: usize,
) -> Result<ProofSourceEdit, ClickError> {
    let mut cursor = clause_start + 1;
    let mut nested = 0;
    while cursor < limit {
        match tokens[cursor].text.as_str() {
            "{" | "(" | "[" => nested += 1,
            "}" | ")" | "]" => nested -= 1,
            "by" if nested == 0 => {
                return Ok(ProofSourceEdit::Explicit(proof_span(tokens, cursor)?));
            }
            ";" if nested == 0 => {
                return Ok(ProofSourceEdit::DefaultTerminator {
                    span: tokens[cursor].span.clone(),
                    selector: tokens[clause_start].span.start,
                });
            }
            _ => {}
        }
        cursor += 1;
    }
    Err(ClickError::new("could not locate source proof terminator"))
}

/// A claim without its own `by` is proved by the function's covering proof,
/// so selecting it selects that grouped proof.
fn covering_claim(function_block: &FunctionBlock, claim: CProofClaim) -> CProofClaim {
    let clause = match claim {
        CProofClaim::Grouped => return claim,
        CProofClaim::Ensure(index) => function_block.ensures().get(index),
        CProofClaim::ExceptionalEnsure(index) => function_block.exceptional_ensures().get(index),
    };
    if clause.is_some_and(|clause| function_block.covers_claim_proof(clause.proof())) {
        CProofClaim::Grouped
    } else {
        claim
    }
}

/// The written grouped proof's span, or, for the implicit `auto` that
/// covers omitted claim proofs, an insertion after the contract block.
fn find_grouped_proof_edit(
    tokens: &[SourceToken],
    function: &FunctionSource,
    function_block: &FunctionBlock,
) -> Result<ProofSourceEdit, ClickError> {
    if function_block.grouped_proof().is_some() || function_block.covering_proof().is_none() {
        return Ok(ProofSourceEdit::Explicit(find_grouped_proof_span(
            tokens, function,
        )?));
    }
    let close = &tokens[function.body_close].span;
    Ok(ProofSourceEdit::DefaultTerminator {
        span: close.end..close.end,
        selector: close.start,
    })
}

fn find_grouped_proof_span(
    tokens: &[SourceToken],
    function: &FunctionSource,
) -> Result<Range<usize>, ClickError> {
    let by = function.body_close + 1;
    if tokens.get(by).map(|token| token.text.as_str()) != Some("by") {
        return Err(ClickError::new(
            "function uses grouped verification but has no source `by` clause",
        ));
    }
    proof_span(tokens, by)
}

fn find_claim_proof_span(
    tokens: &[SourceToken],
    function: &FunctionSource,
    function_block: &FunctionBlock,
    claim: CProofClaim,
) -> Result<Range<usize>, ClickError> {
    match find_claim_proof_edit(tokens, function, function_block, claim)? {
        ProofSourceEdit::Explicit(span) => Ok(span),
        ProofSourceEdit::DefaultTerminator { .. } => Err(ClickError::new(format!(
            "selected {} uses a default proof and has no explicit source tactic",
            claim.describe()
        ))),
        ProofSourceEdit::OmittedLoopPhase { .. } => {
            unreachable!("function claim edits are never loop phases")
        }
    }
}

#[derive(Clone, Debug)]
enum ProofSourceEdit {
    Explicit(Range<usize>),
    DefaultTerminator {
        span: Range<usize>,
        selector: usize,
    },
    OmittedLoopPhase {
        span: Range<usize>,
        selector: usize,
        phase: &'static str,
    },
}

impl ProofSourceEdit {
    fn span(&self) -> &Range<usize> {
        match self {
            Self::Explicit(span)
            | Self::DefaultTerminator { span, .. }
            | Self::OmittedLoopPhase { span, .. } => span,
        }
    }

    fn selector(&self) -> usize {
        match self {
            Self::Explicit(span) => span.start,
            Self::DefaultTerminator { selector, .. } | Self::OmittedLoopPhase { selector, .. } => {
                *selector
            }
        }
    }
}

fn find_claim_proof_edit(
    tokens: &[SourceToken],
    function: &FunctionSource,
    function_block: &FunctionBlock,
    claim: CProofClaim,
) -> Result<ProofSourceEdit, ClickError> {
    match claim {
        // The source is searched by written clause; a flattened aggregate
        // clause gives several ensures one written clause.
        CProofClaim::Ensure(index) => find_ensure_proof_edit(
            tokens,
            function.body_open,
            function.body_close,
            function_block.ensure_source_clause(index),
        ),
        CProofClaim::ExceptionalEnsure(index) => find_exceptional_ensure_proof_edit(
            tokens,
            function.body_open,
            function.body_close,
            index,
        ),
        CProofClaim::Grouped => Err(ClickError::new(format!(
            "could not locate the source clause for the {}",
            claim.describe()
        ))),
    }
}

/// An explicit expansion request threaded through one verification run.
///
/// Verification fills in `result` for the selected proof site as it goes;
/// nothing about verification's own control flow or execution state depends on
/// the capture being present. This replaces the old thread-local expansion
/// probe and its abort-by-sentinel-error protocol: expansion is now one
/// ordinary verification plus a lookup.
#[derive(Clone, Debug)]
pub(super) struct ExpansionCapture {
    pub(super) site: ProofSite,
    /// `Some` selects one source tactic; `None` requests the whole proof at
    /// the site.
    pub(super) source_index: Option<usize>,
    /// The selected occurrence has been reached; used to route sibling-branch
    /// and deferred finalization bookkeeping for the same occurrence.
    pub(super) active: bool,
    /// First completed capture wins; site-certificate recorders additionally
    /// require agreement across proof obligations.
    pub(super) result: Option<Result<Vec<ProofTactic>, String>>,
    /// The selected occurrence was found inside a C branch arm the kernel
    /// proved infeasible, so checked execution dropped that arm without
    /// running the tactic. This is the fallback answer only: an occurrence
    /// that also runs on a feasible path fills in `result` and that wins.
    pub(super) dropped_path_occurrence: bool,
    /// A selected tactic written inside the body of the `have` at
    /// `source_index` (possibly in an `if` or `cases` arm there), which the
    /// flat source numbering does not reach.
    /// `source_index` still names that enclosing `have`, so the ordinary
    /// occurrence bookkeeping runs unchanged; the answer is the nested
    /// tactic's own checked delta recorded here.
    pub(super) nested: Option<Arc<NestedTacticCapture>>,
    pub(super) replaces_from: Option<usize>,
    /// A partial selection shares one verification. Persistent recorder state
    /// keeps speculative driver clones independent without copying all sites.
    pub(super) batch: Option<Box<BatchExpansionCapture>>,
}

#[derive(Clone, Debug)]
pub(super) struct BatchExpansionCapture {
    pub(super) targets: imbl::OrdMap<usize, ExpansionCapture>,
    pub(super) active_source: Option<usize>,
}

impl ExpansionCapture {
    pub(super) fn for_tactic(site: ProofSite, source_index: usize) -> Self {
        Self {
            site,
            source_index: Some(source_index),
            active: false,
            result: None,
            dropped_path_occurrence: false,
            nested: None,
            batch: None,
            replaces_from: None,
        }
    }

    /// Selects the tactic at `nested_path` below the claim-level tactic at
    /// `source_index`, spelled as a proof step's source path continues: one
    /// written position inside each `have` body, and an arm then a written
    /// position inside each `if` or `cases` arm. An empty path selects the
    /// claim-level tactic itself.
    pub(super) fn for_nested_tactic(
        site: ProofSite,
        source_index: usize,
        nested_path: &[usize],
    ) -> Self {
        let mut capture = Self::for_tactic(site.clone(), source_index);
        if !nested_path.is_empty() {
            let mut path = Vec::with_capacity(nested_path.len() + 1);
            path.push(source_index);
            path.extend_from_slice(nested_path);
            capture.nested = Some(Arc::new(NestedTacticCapture::new(site, path)));
        }
        capture
    }

    pub(super) fn for_site(site: ProofSite) -> Self {
        Self {
            site,
            source_index: None,
            active: false,
            result: None,
            dropped_path_occurrence: false,
            nested: None,
            batch: None,
            replaces_from: None,
        }
    }

    pub(super) fn for_tactics(site: ProofSite, targets: &[(usize, Vec<usize>)]) -> Self {
        let mut capture = Self::for_site(site.clone());
        let mut grouped = BTreeMap::<usize, Vec<Vec<usize>>>::new();
        for (index, path) in targets {
            grouped.entry(*index).or_default().push(path.clone());
        }
        let mut nested = BTreeMap::new();
        let targets = grouped
            .into_iter()
            .map(|(index, paths)| {
                let mut target = Self::for_tactic(site.clone(), index);
                let mut children = BTreeMap::new();
                for path in paths.into_iter().filter(|path| !path.is_empty()) {
                    let mut full = vec![index];
                    full.extend(path);
                    let recorder = Arc::new(NestedTacticCapture::new(site.clone(), full.clone()));
                    children.insert(full.clone(), recorder.clone());
                    nested.insert(full, recorder);
                }
                if !children.is_empty() {
                    target.nested = Some(Arc::new(NestedTacticCapture::collection(
                        site.clone(),
                        children,
                    )));
                }
                (index, target)
            })
            .collect();
        capture.batch = Some(Box::new(BatchExpansionCapture {
            targets,
            active_source: None,
        }));
        if !nested.is_empty() {
            capture.nested = Some(Arc::new(NestedTacticCapture::collection(site, nested)));
        }
        capture
    }

    pub(super) fn selects(&self, site: &ProofSite, index: usize) -> bool {
        self.site == *site
            && self
                .batch
                .as_ref()
                .map_or(self.source_index == Some(index), |batch| {
                    batch.targets.contains_key(&index)
                })
    }

    pub(super) fn target_mut(&mut self, index: usize) -> Option<&mut Self> {
        if self.batch.is_some() {
            self.batch.as_mut()?.targets.get_mut(&index)
        } else if self.source_index == Some(index) {
            Some(self)
        } else {
            None
        }
    }

    pub(super) fn active_target_mut(&mut self) -> Option<&mut Self> {
        if self.batch.is_some() {
            let batch = self.batch.as_mut()?;
            batch.targets.get_mut(&batch.active_source?)
        } else {
            Some(self)
        }
    }

    /// The nested-tactic recorder that proofs checking `site` carry, if this
    /// capture selects a tactic inside a `have` body of that proof.
    pub(super) fn nested_for_site(
        &self,
        site: Option<&ProofSite>,
    ) -> Option<Arc<NestedTacticCapture>> {
        self.nested
            .as_ref()
            .filter(|nested| site == Some(&nested.site))
            .cloned()
    }
}

/// The recorder for one selected tactic written inside a `have` body.
///
/// Proofs checking the selected site carry it in their shared constants. The
/// linear body runner compares each written tactic's source path with `path`
/// and records the checked certificate delta of the matching tactic. It is
/// presentation metadata only: recording never changes what a step checks.
#[derive(Debug)]
pub(in crate::surface) struct NestedTacticCapture {
    pub(in crate::surface) site: ProofSite,
    /// The selected tactic's source path: the claim-level source index of
    /// the outermost enclosing `have`, then the written position inside each
    /// nested `have` body, or the arm and the written position inside each
    /// `if` or `cases` arm.
    pub(in crate::surface) path: Vec<usize>,
    state: std::sync::Mutex<NestedTacticCaptureState>,
    children: BTreeMap<Vec<usize>, Arc<NestedTacticCapture>>,
}

#[derive(Debug, Default)]
struct NestedTacticCaptureState {
    /// The selected tactic is being checked now. A smart closure run inside
    /// it addresses its generated steps by the same block positions, so no
    /// inner occurrence may claim the recorder while the outer one holds it.
    active: bool,
    result: Option<Result<Vec<ProofTactic>, String>>,
}

impl NestedTacticCapture {
    fn new(site: ProofSite, path: Vec<usize>) -> Self {
        Self {
            site,
            path,
            state: std::sync::Mutex::new(NestedTacticCaptureState::default()),
            children: BTreeMap::new(),
        }
    }

    fn collection(site: ProofSite, children: BTreeMap<Vec<usize>, Arc<Self>>) -> Self {
        Self {
            site,
            path: Vec::new(),
            state: std::sync::Mutex::default(),
            children,
        }
    }

    pub(in crate::surface) fn at_path(self: &Arc<Self>, path: &[usize]) -> Option<Arc<Self>> {
        if self.path == path {
            Some(self.clone())
        } else {
            self.children.get(path).cloned()
        }
    }

    fn state(&self) -> std::sync::MutexGuard<'_, NestedTacticCaptureState> {
        self.state
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
    }

    /// Claims the recorder for one occurrence of the selected tactic.
    pub(in crate::surface) fn try_begin(&self) -> bool {
        let mut state = self.state();
        if state.active {
            return false;
        }
        state.active = true;
        true
    }

    /// Records one checked occurrence. Every occurrence (one per C path or
    /// outcome that checks the body) must expand identically; the first
    /// disagreement is the answer.
    pub(in crate::surface) fn finish(&self, occurrence: Result<Vec<ProofTactic>, String>) {
        let mut state = self.state();
        state.active = false;
        match (&state.result, occurrence) {
            (None, occurrence) => state.result = Some(occurrence),
            (Some(Ok(existing)), Ok(tactics)) if *existing == tactics => {}
            (Some(Ok(_)), Ok(_)) => {
                state.result = Some(Err(
                    "selected tactic expands differently across proof obligations".to_string(),
                ));
            }
            (Some(Ok(_)), Err(error)) => state.result = Some(Err(error)),
            (Some(Err(_)), _) => {}
        }
    }

    /// Releases the recorder after an occurrence that did not complete.
    pub(in crate::surface) fn abandon(&self) {
        self.state().active = false;
    }

    pub(in crate::surface) fn result(&self) -> Option<Result<Vec<ProofTactic>, String>> {
        self.state().result.clone()
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum ProofSite {
    FunctionClaim {
        function_name: String,
        claim: CProofClaim,
    },
    TheoremEnsure {
        theorem_name: String,
        ensure_index: usize,
    },
    LoopPhase {
        function_name: String,
        loop_index: usize,
        phase: &'static str,
    },
}

impl ProofSite {
    pub(super) fn description(&self) -> String {
        match self {
            Self::FunctionClaim {
                function_name,
                claim,
            } => format!("function `{function_name}` {}", claim.describe()),
            Self::TheoremEnsure {
                theorem_name,
                ensure_index,
            } => format!("theorem `{theorem_name}` ensure {ensure_index}"),
            Self::LoopPhase {
                function_name,
                loop_index,
                phase,
            } => format!("`{function_name}.loop({loop_index}).{phase}`"),
        }
    }
}

#[derive(Clone, Debug)]
enum TacticSourceEdit {
    Partial(Range<usize>),
    PartialProofClause(Range<usize>),
    WholeProof(ProofSourceEdit),
}

#[derive(Clone, Debug)]
struct LocatedSourceTactic {
    site: ProofSite,
    /// The claim-level source index: the selected tactic's own, or that of
    /// the outermost `have` whose body contains it.
    source_index: usize,
    /// The rest of the source path, outermost first: the written position
    /// inside each nested `have` body, or the arm and then the written
    /// position inside each `if` or `cases` arm; empty for a claim-level
    /// tactic.
    nested: Vec<usize>,
    edit: TacticSourceEdit,
    /// Where each claim-level tactic of this site starts in the source, by
    /// source index: an expansion that stands for a run of tactics ending at
    /// the selected one replaces from an earlier one of these.
    sibling_starts: Vec<(usize, usize)>,
}

thread_local! {
    /// The claim-level source index an expansion replaces from, when the
    /// recorded tactics stand for more than the selected tactic.
    static EXPANSION_REPLACES_FROM: std::cell::Cell<Option<usize>> =
        const { std::cell::Cell::new(None) };
}

/// Records that the expansion captured for the selected tactic also stands
/// for the tactics written before it, back to `source_index`. A closer of a
/// loop phase shared by several invariants expands to one step per
/// invariant, each holding the whole shared script; the written tactics
/// before the closer are part of what it replaces.
pub(in crate::surface) fn note_expansion_replaces_from(source_index: usize) {
    EXPANSION_REPLACES_FROM.with(|from| from.set(Some(source_index)));
}

pub(in crate::surface) fn take_expansion_replaces_from() -> Option<usize> {
    EXPANSION_REPLACES_FROM.with(std::cell::Cell::take)
}

/// A selected rewrite and the emitted regions in its Click source. Audit
/// uses these regions to check its fixed point without expanding unselected
/// automation between them.
#[derive(Clone, Debug)]
pub struct SelectedTacticExpansion {
    pub source: String,
    pub replacement_spans: Vec<Range<usize>>,
}

impl SelectedTacticExpansion {
    fn whole_rewrite(original: &str, source: String) -> Self {
        let prefix = original
            .chars()
            .zip(source.chars())
            .take_while(|(a, b)| a == b)
            .map(|(c, _)| c.len_utf8())
            .sum::<usize>();
        let suffix = original[prefix..]
            .chars()
            .rev()
            .zip(source[prefix..].chars().rev())
            .take_while(|(a, b)| a == b)
            .map(|(c, _)| c.len_utf8())
            .sum::<usize>();
        let replacement_spans = std::iter::once(prefix..source.len() - suffix).collect();
        Self {
            source,
            replacement_spans,
        }
    }
}

/// Expands just the requested sites of one claim in a shared verification.
pub fn expand_c0_tactics_source_at(
    source: &str,
    c_sources: &[(&str, &str)],
    positions: &[SourcePosition],
) -> Result<SelectedTacticExpansion, ClickError> {
    expand_selected_tactics_context(None, source, &CSourceContext::bundle(c_sources), positions)
}

pub fn expand_c0_project_tactics_source_at(
    project: &ClickProject,
    c_sources: &[(&str, &str)],
    positions: &[SourcePosition],
) -> Result<SelectedTacticExpansion, ClickError> {
    let source = project
        .entry_source()
        .ok_or_else(|| ClickError::new("missing entry source"))?;
    expand_selected_tactics_context(
        Some(project),
        source,
        &CSourceContext::bundle(c_sources).with_click_project(project),
        positions,
    )
}

pub fn expand_c0_prepared_tactics_source_at(
    source: &str,
    imports: &[crate::languages::c::compiler_import::PreparedCImport],
    positions: &[SourcePosition],
) -> Result<SelectedTacticExpansion, ClickError> {
    expand_selected_tactics_context(None, source, &CSourceContext::prepared(imports), positions)
}

pub fn expand_c0_prepared_project_tactics_source_at(
    project: &ClickProject,
    imports: &[crate::languages::c::compiler_import::PreparedCImport],
    positions: &[SourcePosition],
) -> Result<SelectedTacticExpansion, ClickError> {
    let source = project
        .entry_source()
        .ok_or_else(|| ClickError::new("missing entry source"))?;
    expand_selected_tactics_context(
        Some(project),
        source,
        &CSourceContext::prepared(imports).with_click_project(project),
        positions,
    )
}

pub fn expand_program_prepared_tactics_source_at(
    source: &str,
    import: &impl crate::languages::PreparedProgramSource,
    positions: &[SourcePosition],
) -> Result<SelectedTacticExpansion, ClickError> {
    expand_selected_tactics_context(None, source, &CSourceContext::program(import)?, positions)
}

pub fn expand_program_prepared_project_tactics_source_at(
    project: &ClickProject,
    import: &impl crate::languages::PreparedProgramSource,
    positions: &[SourcePosition],
) -> Result<SelectedTacticExpansion, ClickError> {
    let source = project
        .entry_source()
        .ok_or_else(|| ClickError::new("missing entry source"))?;
    expand_selected_tactics_context(
        Some(project),
        source,
        &CSourceContext::program(import)?.with_click_project(project),
        positions,
    )
}

fn expand_selected_tactics_context(
    project: Option<&ClickProject>,
    source: &str,
    inputs: &CSourceContext<'_>,
    positions: &[SourcePosition],
) -> Result<SelectedTacticExpansion, ClickError> {
    if positions.is_empty() {
        return Ok(SelectedTacticExpansion {
            source: source.to_string(),
            replacement_spans: Vec::new(),
        });
    }
    let file = match project {
        Some(project) => resolve_click_project_context(project, inputs)?,
        None => parse_source_with_c_layouts_context(source, inputs)?,
    };
    let wanted = positions
        .iter()
        .map(|p| (p.line, p.column))
        .collect::<BTreeSet<_>>();
    let mut offsets = BTreeSet::new();
    let (mut line, mut column) = (1, 1);
    for (offset, character) in source.char_indices() {
        crate::instrumentation::record_deterministic_work(1);
        if offset % 1024 == 0 && crate::instrumentation::deadline_exceeded() {
            return Err(ClickError::new(
                "selected expansion exceeded its time limit",
            ));
        }
        if wanted.contains(&(line, column)) {
            offsets.insert(offset);
        }
        if character == '\n' {
            line += 1;
            column = 1;
        } else {
            column += 1;
        }
    }
    let entries = source_tactic_entries(source, &file)?;
    let mut selected = BTreeMap::<usize, LocatedSourceTactic>::new();
    for entry in &entries {
        if !offsets.contains(&entry.anchor) {
            continue;
        }
        if let EntrySelection::Located(located) = &entry.selection {
            selected
                .entry(entry.anchor)
                .or_insert_with(|| located.clone());
        }
    }
    if selected.len() != wanted.len() {
        return Err(ClickError::new(
            "selected audit locations no longer name proof tactics",
        ));
    }
    let selected = selected.into_values().collect::<Vec<_>>();
    let site = selected[0].site.clone();
    if selected.iter().any(|target| target.site != site) {
        return Err(ClickError::new(
            "batch expansion requires sites from one claim",
        ));
    }
    if let ProofSite::TheoremEnsure {
        theorem_name,
        ensure_index,
    } = &site
    {
        let verified = match project {
            Some(project) => verify_click_project_theorem_context(project, inputs, theorem_name)?,
            None => verify_click_theorems_with_context(source, inputs)?,
        };
        return rewrite_verified_pure_theorem(source, &verified, theorem_name, *ensure_index)
            .map(|rewritten| SelectedTacticExpansion::whole_rewrite(source, rewritten));
    }
    let reference_result = match &site {
        ProofSite::FunctionClaim { function_name, .. }
        | ProofSite::LoopPhase { function_name, .. } => proof_function_blocks(&file)
            .find(|block| block.signature().name() == function_name)
            .is_some_and(|block| block.signature().returns_reference()),
        ProofSite::TheoremEnsure { .. } => false,
    };
    let _reference_result_source =
        super::diagnostics::ReferenceResultSourceScope::enter(reference_result);
    let whole = selected
        .iter()
        .any(|target| matches!(target.edit, TacticSourceEdit::WholeProof(_)));
    let targets = selected
        .iter()
        .map(|t| (t.source_index, t.nested.clone()))
        .collect::<Vec<_>>();
    let mut capture = if whole {
        ExpansionCapture::for_site(site.clone())
    } else {
        ExpansionCapture::for_tactics(site.clone(), &targets)
    };
    take_expansion_replaces_from();
    let whole_function = match &site {
        ProofSite::FunctionClaim {
            function_name,
            claim,
        } if whole => Some((function_name, *claim)),
        _ => None,
    };
    let (verified, _) = instrumentation::with_default_tactic_limits(|| {
        crate::surface::verification::verify_c0_sources_with_context(
            source,
            inputs,
            whole_function.map(|(name, _)| VerificationTarget::Function(name.clone())),
            None,
            if whole_function.is_some() {
                None
            } else {
                Some(&mut capture)
            },
            Some(file),
        )
    })?;
    if let Some((name, claim)) = whole_function {
        let theorem = select_expansion_theorem(&verified, name, claim)?;
        let mut tactics = theorem.expanded_proof_certificate()?.to_proof_tactics();
        if theorem.function_block.is_tactic_procedure() {
            remove_tactic_procedure_ending(
                &mut tactics,
                1 + theorem.function_block.ensures().len(),
            )
            .map_err(|()| ClickError::new("expanded tactic procedure lost its checked ending"))?;
        }
        capture.result = Some(Ok(tactics));
    }
    let sibling_starts = entries
        .iter()
        .filter_map(|entry| match &entry.selection {
            EntrySelection::Located(sibling)
                if sibling.site == site && sibling.nested.is_empty() =>
            {
                Some((sibling.source_index, entry.span.start))
            }
            _ => None,
        })
        .collect::<BTreeMap<_, _>>();
    let edit_span = |target: &LocatedSourceTactic| {
        let mut span = match &target.edit {
            TacticSourceEdit::Partial(span) | TacticSourceEdit::PartialProofClause(span) => {
                span.clone()
            }
            TacticSourceEdit::WholeProof(edit) => edit.span().clone(),
        };
        if let Some(from) = capture
            .batch
            .as_ref()
            .and_then(|batch| batch.targets.get(&target.source_index))
            .and_then(|recorder| recorder.replaces_from)
            .and_then(|index| sibling_starts.get(&index))
        {
            span.start = span.start.min(*from);
        }
        span
    };
    let mut selected = selected;
    selected.sort_by_key(|target| {
        let span = edit_span(target);
        (span.start, std::cmp::Reverse(span.end))
    });
    let mut edits: Vec<(Range<usize>, String)> = Vec::new();
    for target in selected {
        let owned_span = edit_span(&target);
        if edits
            .last()
            .is_some_and(|(span, _)| owned_span.start >= span.start && owned_span.end <= span.end)
        {
            continue;
        }
        crate::instrumentation::record_deterministic_work(1);
        let recorder = capture
            .batch
            .as_ref()
            .and_then(|batch| batch.targets.get(&target.source_index))
            .unwrap_or(&capture);
        let result = if target.nested.is_empty() {
            recorder.result.clone()
        } else {
            let mut path = vec![target.source_index];
            path.extend(&target.nested);
            recorder
                .nested
                .as_ref()
                .and_then(|nested| nested.at_path(&path))
                .and_then(|nested| nested.result())
        };
        let tactics = match result {
            Some(result) => result.map_err(ClickError::new)?,
            None if recorder.dropped_path_occurrence => Vec::new(),
            None => {
                return Err(ClickError::new(format!(
                    "selected {} tactic {} retained no expansion",
                    site.description(),
                    target.source_index
                )));
            }
        };
        let (mut span, replacement) = match target.edit {
            TacticSourceEdit::Partial(span) => (
                span,
                super::printing::format_partial_tactic_sequence(&tactics),
            ),
            TacticSourceEdit::PartialProofClause(span) => (
                span,
                super::printing::format_proof_certificate(
                    &ProofCertificate::from_proof_tactics(&tactics)
                        .map_err(|error| ClickError::new(error.message().to_string()))?,
                ),
            ),
            TacticSourceEdit::WholeProof(edit) => {
                let replacement = super::printing::format_proof_certificate(
                    &ProofCertificate::from_proof_tactics(&tactics)
                        .map_err(|error| ClickError::new(error.message().to_string()))?,
                );
                let span = edit.span().clone();
                let replacement = match edit {
                    ProofSourceEdit::Explicit(_) => replacement,
                    ProofSourceEdit::DefaultTerminator { .. } => format!(" {replacement}"),
                    ProofSourceEdit::OmittedLoopPhase { phase, .. } => {
                        format!("    {phase} {}\n", replacement.replace('\n', "\n    "))
                    }
                };
                (span, replacement)
            }
        };
        if let Some(from) = recorder
            .replaces_from
            .and_then(|index| sibling_starts.get(&index))
        {
            span.start = span.start.min(*from);
        }
        let replacement = if replacement.is_empty()
            && source[..span.start].trim_end().ends_with('{')
            && source[span.end..].trim_start().starts_with('}')
        {
            "assumption();".to_string()
        } else {
            replacement
        };
        edits.push((
            span.clone(),
            indent_replacement(source, span.start, &replacement),
        ));
    }
    // A prefix expansion owns any selected edits within that prefix. Reject
    // crossing ranges rather than constructing an ambiguous rewrite.
    edits.sort_by_key(|(span, _)| (span.start, std::cmp::Reverse(span.end)));
    let mut retained: Vec<(Range<usize>, String)> = Vec::new();
    for (span, replacement) in edits {
        if let Some((previous, _)) = retained.last() {
            if span.end <= previous.end {
                continue;
            }
            if span.start < previous.end {
                return Err(ClickError::new(
                    "selected expansion edits overlap without one owning the other",
                ));
            }
        }
        retained.push((span, replacement));
    }
    let mut rewritten = String::with_capacity(source.len());
    let mut cursor = 0;
    let mut replacement_spans = Vec::new();
    for (span, replacement) in retained {
        rewritten.push_str(&source[cursor..span.start]);
        let replacement_start = rewritten.len();
        rewritten.push_str(&replacement);
        replacement_spans.push(replacement_start..rewritten.len());
        cursor = span.end;
    }
    rewritten.push_str(&source[cursor..]);
    // Removing several no-op occurrences can empty a proof block together.
    // Fill only blocks touched by this rewrite, preserving unrelated syntax.
    let tokens = scan_source_tokens(&rewritten)?;
    let mut region = 0;
    let mut empty_blocks = Vec::new();
    for window in tokens.windows(3) {
        while replacement_spans
            .get(region)
            .is_some_and(|span| span.end < window[1].span.end)
        {
            region += 1;
        }
        if window[0].text == "by"
            && window[1].text == "{"
            && window[2].text == "}"
            && replacement_spans.get(region).is_some_and(|span| {
                span.start <= window[2].span.start && span.end >= window[1].span.end
            })
        {
            empty_blocks.push(window[1].span.end);
        }
    }
    for offset in empty_blocks.into_iter().rev() {
        let filler = " assumption(); ";
        rewritten.insert_str(offset, filler);
        for span in &mut replacement_spans {
            if span.start >= offset {
                span.start += filler.len();
            }
            if span.end >= offset {
                span.end += filler.len();
            }
        }
    }
    if let Some(project) = project {
        let rewritten_project = project.with_entry_source(rewritten.clone());
        resolve_click_project_context(&rewritten_project, inputs)?;
    } else {
        parse_source_with_c_layouts_context(&rewritten, inputs)?;
    }
    Ok(SelectedTacticExpansion {
        source: rewritten,
        replacement_spans,
    })
}

impl LocatedSourceTactic {
    /// `span` widened back to the tactic a recorded
    /// [`note_expansion_replaces_from`] names, if any.
    fn replaced_span(&self, span: Range<usize>) -> Range<usize> {
        let Some(from) = EXPANSION_REPLACES_FROM.with(std::cell::Cell::take) else {
            return span;
        };
        self.sibling_starts
            .iter()
            .find(|(source_index, start)| *source_index == from && *start < span.start)
            .map_or(span.clone(), |(_, start)| *start..span.end)
    }
}

/// One written tactic in the span-indexed side table that source selection
/// consults. Every tactic at every depth is recorded by its source span; the
/// flat claim-level numbering stays exactly the one timing, profiling, and
/// audit use, and a tactic inside a `have` body is addressed by that `have`'s
/// number plus its written positions.
#[derive(Clone, Debug)]
struct SourceTacticEntry {
    span: Range<usize>,
    /// The canonical start the tactic is reported at.
    anchor: usize,
    claim_label: String,
    tactic_name: String,
    smart: bool,
    selection: EntrySelection,
}

#[derive(Clone, Debug)]
enum EntrySelection {
    Located(LocatedSourceTactic),
    /// A smart tactic the expander cannot address separately, and why.
    Unaddressable(String),
}

/// One smart tactic that a source location can select.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SmartTacticCandidate {
    pub claim_label: String,
    pub tactic_name: String,
    /// Where the tactic starts, in the Click source's own coordinates.
    pub position: SourcePosition,
}

/// Why a source location selects no single smart tactic. `candidates` lists
/// the smart tactics the location could have meant, if any.
#[derive(Clone, Debug)]
pub struct SmartTacticSelectionError {
    pub reason: String,
    pub candidates: Vec<SmartTacticCandidate>,
}

impl SmartTacticSelectionError {
    fn from_error(error: ClickError) -> Self {
        Self {
            reason: error.message().to_string(),
            candidates: Vec::new(),
        }
    }

    /// The error in Click source coordinates, for callers without a
    /// container file to report positions in.
    fn into_click_error(self, line: usize, column: Option<usize>) -> ClickError {
        let location =
            column.map_or_else(|| format!("{line}"), |column| format!("{line}:{column}"));
        let mut message = format!("source location {location}: {}", self.reason);
        for candidate in &self.candidates {
            message.push_str(&format!(
                "\n  {}:{} `{}` in `{}`",
                candidate.position.line,
                candidate.position.column,
                candidate.tactic_name,
                candidate.claim_label
            ));
        }
        ClickError::new(message)
    }
}

/// Resolves a source location to the one smart tactic it selects.
///
/// With a column, the location selects the innermost smart tactic whose
/// source span contains it, at any nesting depth. Without one, the line must
/// start exactly one smart tactic. The result's position is the tactic's
/// canonical start, which every location-taking expansion entry point
/// accepts.
pub fn c0_select_smart_tactic(
    click_source: &str,
    c_sources: &[(&str, &str)],
    line: usize,
    column: Option<usize>,
) -> Result<SmartTacticCandidate, SmartTacticSelectionError> {
    let sources = CSourceContext::bundle(c_sources);
    let file = parse_source_with_c_layouts_context(click_source, &sources)
        .map_err(SmartTacticSelectionError::from_error)?;
    select_smart_tactic_file(click_source, &file, line, column)
}

pub fn c0_prepared_select_smart_tactic(
    click_source: &str,
    imports: &[crate::languages::c::compiler_import::PreparedCImport],
    line: usize,
    column: Option<usize>,
) -> Result<SmartTacticCandidate, SmartTacticSelectionError> {
    let sources = CSourceContext::prepared(imports);
    let file = parse_source_with_c_layouts_context(click_source, &sources)
        .map_err(SmartTacticSelectionError::from_error)?;
    select_smart_tactic_file(click_source, &file, line, column)
}

pub fn program_prepared_select_smart_tactic(
    click_source: &str,
    import: &impl crate::languages::PreparedProgramSource,
    line: usize,
    column: Option<usize>,
) -> Result<SmartTacticCandidate, SmartTacticSelectionError> {
    let sources = CSourceContext::program(import).map_err(SmartTacticSelectionError::from_error)?;
    let file = parse_source_with_c_layouts_context(click_source, &sources)
        .map_err(SmartTacticSelectionError::from_error)?;
    select_smart_tactic_file(click_source, &file, line, column)
}

pub fn c0_project_select_smart_tactic(
    project: &ClickProject,
    c_sources: &[(&str, &str)],
    line: usize,
    column: Option<usize>,
) -> Result<SmartTacticCandidate, SmartTacticSelectionError> {
    let sources = CSourceContext::bundle(c_sources).with_click_project(project);
    select_project_smart_tactic(project, &sources, line, column)
}

pub fn c0_prepared_project_select_smart_tactic(
    project: &ClickProject,
    imports: &[crate::languages::c::compiler_import::PreparedCImport],
    line: usize,
    column: Option<usize>,
) -> Result<SmartTacticCandidate, SmartTacticSelectionError> {
    let sources = CSourceContext::prepared(imports).with_click_project(project);
    select_project_smart_tactic(project, &sources, line, column)
}

pub fn program_prepared_project_select_smart_tactic(
    project: &ClickProject,
    import: &impl crate::languages::PreparedProgramSource,
    line: usize,
    column: Option<usize>,
) -> Result<SmartTacticCandidate, SmartTacticSelectionError> {
    let sources = CSourceContext::program(import)
        .map_err(SmartTacticSelectionError::from_error)?
        .with_click_project(project);
    select_project_smart_tactic(project, &sources, line, column)
}

fn select_project_smart_tactic(
    project: &ClickProject,
    sources: &CSourceContext<'_>,
    line: usize,
    column: Option<usize>,
) -> Result<SmartTacticCandidate, SmartTacticSelectionError> {
    let click_source = project.entry_source().ok_or_else(|| {
        SmartTacticSelectionError::from_error(ClickError::new(format!(
            "missing entry module `{}`",
            project.entry()
        )))
    })?;
    let file = resolve_click_project_context(project, sources)
        .map_err(SmartTacticSelectionError::from_error)?;
    select_smart_tactic_file(click_source, &file, line, column)
}

fn select_smart_tactic_file(
    click_source: &str,
    file: &ClickFile,
    line: usize,
    column: Option<usize>,
) -> Result<SmartTacticCandidate, SmartTacticSelectionError> {
    let entries =
        source_tactic_entries(click_source, file).map_err(SmartTacticSelectionError::from_error)?;
    let entry = select_source_tactic_entry(click_source, &entries, line, column)?;
    Ok(smart_tactic_candidate(click_source, entry))
}

fn smart_tactic_candidate(click_source: &str, entry: &SourceTacticEntry) -> SmartTacticCandidate {
    SmartTacticCandidate {
        claim_label: entry.claim_label.clone(),
        tactic_name: entry.tactic_name.clone(),
        position: position_at_offset(click_source, entry.anchor),
    }
}

/// The one smart entry a location selects: with a column, the innermost
/// smart span containing it; without one, the only smart tactic starting on
/// the line.
fn select_source_tactic_entry<'e>(
    click_source: &str,
    entries: &'e [SourceTacticEntry],
    line: usize,
    column: Option<usize>,
) -> Result<&'e SourceTacticEntry, SmartTacticSelectionError> {
    // A smart tactic written inside a smart site that owns it (the `simp`
    // of a smart `have`) is an alias of that site; the line lists the site
    // once.
    let starting_on_line = || {
        let mut starting: Vec<&SourceTacticEntry> = Vec::new();
        for entry in entries.iter().filter(|entry| {
            entry.smart && position_at_offset(click_source, entry.anchor).line == line
        }) {
            if !starting
                .iter()
                .any(|seen| same_selection(&seen.selection, &entry.selection))
            {
                starting.push(entry);
            }
        }
        starting
    };
    let innermost_containing = |wanted: usize| {
        // Spans nest, so the shortest containing span is the innermost;
        // equal spans keep source order.
        entries
            .iter()
            .filter(|entry| entry.smart && (entry.span.contains(&wanted) || entry.anchor == wanted))
            .min_by_key(|entry| entry.span.end - entry.span.start)
    };
    let candidates = |entries: &[&SourceTacticEntry]| {
        entries
            .iter()
            .map(|entry| smart_tactic_candidate(click_source, entry))
            .collect::<Vec<_>>()
    };
    let selected = match column {
        Some(column) => {
            let wanted = offset_at_position(click_source, line, column)
                .map_err(SmartTacticSelectionError::from_error)?;
            match innermost_containing(wanted) {
                Some(entry) => entry,
                None => {
                    let on_line = starting_on_line();
                    return Err(SmartTacticSelectionError {
                        reason: if on_line.is_empty() {
                            "no smart tactic's source contains this location".to_string()
                        } else {
                            "no smart tactic's source contains this location; the smart tactics starting on this line are:".to_string()
                        },
                        candidates: candidates(&on_line),
                    });
                }
            }
        }
        None => match starting_on_line().as_slice() {
            [] => {
                // A line inside a region the expander cannot address says
                // why, as a column there would.
                let line_start = offset_at_position(click_source, line, 1)
                    .map_err(SmartTacticSelectionError::from_error)?;
                let indent = click_source[line_start..]
                    .find(|character: char| !character.is_whitespace() || character == '\n')
                    .unwrap_or(0);
                if let Some(SourceTacticEntry {
                    selection: EntrySelection::Unaddressable(reason),
                    ..
                }) = innermost_containing(line_start + indent)
                {
                    return Err(SmartTacticSelectionError {
                        reason: reason.clone(),
                        candidates: Vec::new(),
                    });
                }
                return Err(SmartTacticSelectionError {
                    reason: "no smart tactic starts on this line".to_string(),
                    candidates: Vec::new(),
                });
            }
            [only] => only,
            several => {
                return Err(SmartTacticSelectionError {
                    reason: format!(
                        "{} smart tactics start on this line; add the column of one of them:",
                        several.len()
                    ),
                    candidates: candidates(several),
                });
            }
        },
    };
    match &selected.selection {
        EntrySelection::Located(_) => Ok(selected),
        EntrySelection::Unaddressable(reason) => Err(SmartTacticSelectionError {
            reason: reason.clone(),
            candidates: Vec::new(),
        }),
    }
}

fn locate_source_tactic(
    click_source: &str,
    c_sources: &[(&str, &str)],
    line: usize,
    column: usize,
) -> Result<LocatedSourceTactic, ClickError> {
    let sources = CSourceContext::bundle(c_sources);
    locate_source_tactic_context(click_source, &sources, line, column)
}

fn locate_source_tactic_context(
    click_source: &str,
    c_sources: &CSourceContext<'_>,
    line: usize,
    column: usize,
) -> Result<LocatedSourceTactic, ClickError> {
    let file = parse_source_with_c_layouts_context(click_source, c_sources)?;
    locate_source_tactic_file(click_source, &file, line, column)
}

/// Whether two entries select the same expansion.
fn same_selection(left: &EntrySelection, right: &EntrySelection) -> bool {
    match (left, right) {
        (EntrySelection::Located(left), EntrySelection::Located(right)) => {
            left.site == right.site
                && left.source_index == right.source_index
                && left.nested == right.nested
        }
        _ => false,
    }
}

fn locate_source_tactic_file(
    click_source: &str,
    file: &ClickFile,
    line: usize,
    column: usize,
) -> Result<LocatedSourceTactic, ClickError> {
    let entries = source_tactic_entries(click_source, file)?;
    // The library entry point also expands a non-smart tactic named by its
    // exact start (a `have` whose explicit body a smart step closes, a whole
    // pure theorem proof); every other location selects the innermost smart
    // tactic containing it.
    let wanted = offset_at_position(click_source, line, column)?;
    let exact = entries
        .iter()
        .filter(|entry| {
            entry.anchor == wanted && matches!(entry.selection, EntrySelection::Located(_))
        })
        .min_by_key(|entry| entry.span.end - entry.span.start);
    let entry = match exact {
        Some(entry) => entry,
        None => select_source_tactic_entry(click_source, &entries, line, Some(column))
            .map_err(|error| error.into_click_error(line, Some(column)))?,
    };
    // A stale note from an earlier expansion on this thread must not widen
    // this one.
    EXPANSION_REPLACES_FROM.with(|from| from.set(None));
    match &entry.selection {
        EntrySelection::Located(located) => {
            let mut located = located.clone();
            located.sibling_starts = entries
                .iter()
                .filter_map(|entry| match &entry.selection {
                    EntrySelection::Located(sibling)
                        if sibling.site == located.site && sibling.nested.is_empty() =>
                    {
                        Some((sibling.source_index, entry.span.start))
                    }
                    _ => None,
                })
                .collect();
            Ok(located)
        }
        EntrySelection::Unaddressable(reason) => Err(ClickError::new(reason.clone())),
    }
}

/// Index top-level declaration bodies once. Proof bodies are skipped as a
/// whole, so a use of a name inside a proof never shadows its declaration.
fn declaration_source_index(
    tokens: &[SourceToken],
) -> Result<std::collections::HashMap<String, FunctionSource>, ClickError> {
    let mut result = std::collections::HashMap::new();
    let mut candidate = None;
    // Inside a Rust `impl` block a method `name` is the function `Type_name`.
    let mut impl_block: Option<(String, usize)> = None;
    let mut index = 0;
    while index < tokens.len() {
        crate::instrumentation::record_deterministic_work(1);
        if impl_block
            .as_ref()
            .is_some_and(|(_, close)| index >= *close)
        {
            impl_block = None;
        }
        match tokens[index].text.as_str() {
            "impl" if impl_block.is_none() && candidate.is_none() => {
                if let Some(open) = (index..tokens.len()).find(|at| tokens[*at].text == "{") {
                    let close = matching_delimiter(tokens, open, "{", "}")?;
                    impl_block = Some((tokens[open - 1].text.clone(), close));
                    index = open + 1;
                    continue;
                }
            }
            "theorem" | "tactic" => {
                candidate = tokens.get(index + 1).map(|token| token.text.clone());
            }
            "(" => {
                if candidate.is_none() {
                    candidate = index
                        .checked_sub(1)
                        .map(|before| tokens[before].text.clone());
                }
                index = matching_delimiter(tokens, index, "(", ")")?;
            }
            "{" => {
                let body_close = matching_delimiter(tokens, index, "{", "}")?;
                if let Some(name) = candidate.take() {
                    let name = match &impl_block {
                        Some((impl_type, _)) => format!("{impl_type}_{name}"),
                        None => name,
                    };
                    result.insert(
                        name,
                        FunctionSource {
                            body_open: index,
                            body_close,
                        },
                    );
                }
                index = body_close;
            }
            ";" => {
                candidate = None;
            }
            _ => {}
        }
        index += 1;
    }
    Ok(result)
}

/// Records every written tactic of every selected proof, keyed by span.
fn source_tactic_entries(
    click_source: &str,
    file: &ClickFile,
) -> Result<Vec<SourceTacticEntry>, ClickError> {
    let tokens = scan_source_tokens(click_source)?;
    let mut entries = Vec::new();
    let declarations = declaration_source_index(&tokens)?;
    for theorem in file.theorem_definitions() {
        if !file.theorem_is_selected(theorem.name()) {
            continue;
        }
        let source = declarations.get(theorem.name()).copied().ok_or_else(|| {
            ClickError::new(format!(
                "could not locate Click theorem `{}`",
                theorem.name()
            ))
        })?;
        let kernel_axiom_name = proof::is_kernel_standard_theorem_name(theorem.name())
            && theorem
                .parameters()
                .iter()
                .all(|parameter| parameter.click_type() == &ClickType::C(C0Type::Int32));
        for (ensure_index, ensure) in theorem.ensures().iter().enumerate() {
            if kernel_axiom_name
                && !matches!(
                    ensure.ensure(),
                    Ensure::Proposition(ClickProposition::PredicateCall { .. })
                )
            {
                continue;
            }
            let edit =
                find_ensure_proof_edit(&tokens, source.body_open, source.body_close, ensure_index)?;
            let label = ensure.name().map_or_else(
                || format!("{}.ensures_{ensure_index}", theorem.name()),
                |name| format!("{}.{name}", theorem.name()),
            );
            let site = ProofSite::TheoremEnsure {
                theorem_name: theorem.name().to_string(),
                ensure_index,
            };
            proof_tactic_entries(&tokens, &edit, ensure.proof(), &site, &label, &mut entries)?;
        }
    }
    for function_block in proof_function_blocks(file) {
        if function_block.is_external() {
            continue;
        }
        let function_name = function_block.signature().name();
        let function = declarations.get(function_name).copied().ok_or_else(|| {
            ClickError::new(format!(
                "could not locate Click function block `{function_name}`"
            ))
        })?;
        for clause in function_block.structural_clauses() {
            if let CodeRegion::Loop(loop_index) = clause.region() {
                for (phase, proof) in [
                    ("initialize", clause.initialize_proof()),
                    ("preserve", clause.preserve_proof()),
                ] {
                    let (selector, proof_span, insertion) =
                        find_loop_phase_proof_span(&tokens, &function, *loop_index, phase)?;
                    let default_proof = SourceProof::Default;
                    let proof = proof.unwrap_or(&default_proof);
                    let edit = proof_span.map_or_else(
                        || ProofSourceEdit::OmittedLoopPhase {
                            span: insertion..insertion,
                            selector,
                            phase,
                        },
                        ProofSourceEdit::Explicit,
                    );
                    proof_tactic_entries(
                        &tokens,
                        &edit,
                        proof,
                        &ProofSite::LoopPhase {
                            function_name: function_name.to_string(),
                            loop_index: *loop_index,
                            phase,
                        },
                        &format!("{function_name}.loop({loop_index}).{phase}"),
                        &mut entries,
                    )?;
                }
            }
            let block = find_structural_clause_block(&tokens, &function, *clause.region())?;
            let edits = structural_item_proof_edits(&tokens, &block)?;
            if edits.len() != clause.items().len() {
                return Err(ClickError::new(format!(
                    "structural source mapping for `{function_name}` {:?} found {} items, expected {}",
                    clause.region(),
                    edits.len(),
                    clause.items().len()
                )));
            }
        }
        if let Some(proof) = function_block.covering_proof() {
            let edit = find_grouped_proof_edit(&tokens, &function, function_block)?;
            proof_tactic_entries(
                &tokens,
                &edit,
                proof,
                &ProofSite::FunctionClaim {
                    function_name: function_name.to_string(),
                    claim: CProofClaim::Grouped,
                },
                &format!("{function_name}.contract"),
                &mut entries,
            )?;
        }
        for (index, ensure) in function_block.ensures().iter().enumerate() {
            if function_block.covers_claim_proof(ensure.proof()) {
                continue;
            }
            let claim = CProofClaim::Ensure(index);
            let edit = find_claim_proof_edit(&tokens, &function, function_block, claim)?;
            let label = ensure.name().map_or_else(
                || format!("{function_name}.ensures_{index}"),
                |name| format!("{function_name}.{name}"),
            );
            proof_tactic_entries(
                &tokens,
                &edit,
                ensure.proof(),
                &ProofSite::FunctionClaim {
                    function_name: function_name.to_string(),
                    claim,
                },
                &label,
                &mut entries,
            )?;
        }
        for (index, ensure) in function_block.exceptional_ensures().iter().enumerate() {
            if function_block.covers_claim_proof(ensure.proof()) {
                continue;
            }
            let claim = CProofClaim::ExceptionalEnsure(index);
            let edit = find_claim_proof_edit(&tokens, &function, function_block, claim)?;
            let label = ensure.name().map_or_else(
                || format!("{function_name}.exceptional_ensures_{index}"),
                |name| format!("{function_name}.{name}"),
            );
            proof_tactic_entries(
                &tokens,
                &edit,
                ensure.proof(),
                &ProofSite::FunctionClaim {
                    function_name: function_name.to_string(),
                    claim,
                },
                &label,
                &mut entries,
            )?;
        }
    }
    Ok(entries)
}

fn proof_tactic_entries(
    tokens: &[SourceToken],
    edit: &ProofSourceEdit,
    proof: &SourceProof,
    site: &ProofSite,
    claim_label: &str,
    entries: &mut Vec<SourceTacticEntry>,
) -> Result<(), ClickError> {
    let whole_proof = |span: Range<usize>, anchor: usize, name: &str| SourceTacticEntry {
        span,
        anchor,
        claim_label: claim_label.to_string(),
        tactic_name: name.to_string(),
        smart: true,
        selection: EntrySelection::Located(LocatedSourceTactic {
            site: site.clone(),
            source_index: 0,
            nested: Vec::new(),
            edit: TacticSourceEdit::WholeProof(edit.clone()),
            sibling_starts: Vec::new(),
        }),
    };
    let omitted_proof_span = || match edit {
        ProofSourceEdit::DefaultTerminator { span, selector } => *selector..span.end,
        _ => tokens
            .iter()
            .find(|token| token.span.start == edit.selector())
            .map_or(edit.selector()..edit.selector() + 1, |token| {
                token.span.clone()
            }),
    };
    match proof {
        SourceProof::Script(tactics) => {
            let ProofSourceEdit::Explicit(source_proof_span) = edit else {
                return Err(ClickError::new(
                    "an explicit proof script has no source `by` clause",
                ));
            };
            let flat = collect_source_tactics(tokens, source_proof_span, tactics)?;
            for (source_index, item) in flat.into_iter().enumerate() {
                let (tactic_name, smart, edit) = match item.tactic {
                    FlatTactic::Written(tactic) => (
                        tactic_name(tactic).to_string(),
                        source_site_kind(tactic) == SourceSiteKind::ExpandableAutomation,
                        TacticSourceEdit::Partial(item.span.clone()),
                    ),
                    FlatTactic::Phase(tactic) => {
                        // A frontier-local loop phase proved by one smart
                        // tactic is rewritten as the whole `by` clause.
                        let by =
                            item.tokens.start.checked_sub(1).filter(|by| {
                                tokens.get(*by).is_some_and(|token| token.text == "by")
                            });
                        let by = by.ok_or_else(|| {
                            ClickError::new("selected nested tactic has no source `by` clause")
                        })?;
                        (
                            smart_tactic_name(tactic).to_string(),
                            true,
                            TacticSourceEdit::PartialProofClause(proof_span(tokens, by)?),
                        )
                    }
                };
                let entry = SourceTacticEntry {
                    span: item.span.clone(),
                    anchor: item.span.start,
                    claim_label: claim_label.to_string(),
                    tactic_name,
                    smart,
                    selection: EntrySelection::Located(LocatedSourceTactic {
                        site: site.clone(),
                        source_index,
                        nested: Vec::new(),
                        edit,
                        sibling_starts: Vec::new(),
                    }),
                };
                entries.push(entry.clone());
                if let FlatTactic::Written(tactic) = item.tactic
                    && smart
                {
                    smart_container_alias_entries(
                        tokens,
                        item.tokens.clone(),
                        tactic,
                        &entry,
                        entries,
                    );
                }
                // A smart `have` is one site: its body belongs to it.
                if let FlatTactic::Written(ProofTactic::Have(have)) = item.tactic
                    && !smart
                {
                    have_body_tactic_entries(
                        tokens,
                        item.tokens.clone(),
                        have,
                        site,
                        claim_label,
                        source_index,
                        &[],
                        entries,
                    )?;
                }
            }
            Ok(())
        }
        SourceProof::Tactic(tactic) => {
            let name = smart_tactic_name(*tactic);
            match edit {
                ProofSourceEdit::Explicit(proof_span) => {
                    let by = tokens
                        .binary_search_by_key(&proof_span.start, |token| token.span.start)
                        .ok()
                        .filter(|index| tokens[*index].text == "by")
                        .ok_or_else(|| ClickError::new("could not locate source `by` clause"))?;
                    let anchor = tokens
                        .get(by + 1)
                        .map_or(proof_span.start, |token| token.span.start);
                    entries.push(whole_proof(proof_span.clone(), anchor, name));
                }
                ProofSourceEdit::DefaultTerminator { .. }
                | ProofSourceEdit::OmittedLoopPhase { .. } => {
                    entries.push(whole_proof(omitted_proof_span(), edit.selector(), name));
                }
            }
            Ok(())
        }
        SourceProof::Default => {
            entries.push(whole_proof(omitted_proof_span(), edit.selector(), "auto"));
            Ok(())
        }
    }
}

fn smart_tactic_name(tactic: SmartTactic) -> &'static str {
    match tactic {
        SmartTactic::Auto => "auto",
        SmartTactic::Simp => "simp",
    }
}

/// Records the tactics written in a non-smart `have` body, addressed by the
/// `have`'s claim-level source index and their written positions.
#[allow(clippy::too_many_arguments)]
fn have_body_tactic_entries(
    tokens: &[SourceToken],
    have_tokens: Range<usize>,
    have: &ProofHave,
    site: &ProofSite,
    claim_label: &str,
    source_index: usize,
    prefix: &[usize],
    entries: &mut Vec<SourceTacticEntry>,
) -> Result<(), ClickError> {
    let SourceProof::Script(body) = &have.proof else {
        return Ok(());
    };
    let mut depth = 0_usize;
    let by = have_tokens
        .clone()
        .find(|&index| {
            match tokens[index].text.as_str() {
                "(" | "[" | "{" => depth += 1,
                ")" | "]" | "}" => depth = depth.saturating_sub(1),
                _ => {}
            }
            depth == 0 && tokens[index].text == "by"
        })
        .ok_or_else(|| ClickError::new("source `have` has no `by` clause"))?;
    let open = by + 1;
    if tokens.get(open).map(|token| token.text.as_str()) != Some("{") {
        return Err(ClickError::new(
            "source `have` script body has no `{ ... }` block",
        ));
    }
    let close = matching_delimiter(tokens, open, "{", "}")?;
    let block = WrittenBlock {
        open,
        close,
        tactics: body,
        prefix,
    };
    block_tactic_entries(tokens, &block, site, claim_label, source_index, entries)
}

/// One written block of tactics below a claim-level tactic: a `have` body
/// or an arm of a structured tactic, with the source path prefix its
/// tactics' positions extend.
struct WrittenBlock<'b> {
    open: usize,
    close: usize,
    tactics: &'b [ProofTactic],
    prefix: &'b [usize],
}

/// Records each tactic written directly in `block` at its source path, the
/// same path the proof step that checks it reports, and descends into the
/// blocks it writes: a non-smart `have` body, and each arm of a proof `if`
/// or `cases`.
fn block_tactic_entries(
    tokens: &[SourceToken],
    block: &WrittenBlock<'_>,
    site: &ProofSite,
    claim_label: &str,
    source_index: usize,
    entries: &mut Vec<SourceTacticEntry>,
) -> Result<(), ClickError> {
    let direct = direct_tactic_token_ranges(tokens, block.open, block.close)?;
    if direct.len() != block.tactics.len() {
        return Err(ClickError::new(format!(
            "source block has {} direct tactic(s), but the parsed block has {}",
            direct.len(),
            block.tactics.len()
        )));
    }
    for (position, (tactic, token_range)) in block.tactics.iter().zip(direct).enumerate() {
        let span = tokens[token_range.start].span.start..tokens[token_range.end - 1].span.end;
        let mut path = block.prefix.to_vec();
        path.push(position);
        let smart = source_site_kind(tactic) == SourceSiteKind::ExpandableAutomation;
        let entry = SourceTacticEntry {
            span: span.clone(),
            anchor: span.start,
            claim_label: claim_label.to_string(),
            tactic_name: tactic_name(tactic).to_string(),
            smart,
            selection: EntrySelection::Located(LocatedSourceTactic {
                site: site.clone(),
                source_index,
                nested: path.clone(),
                edit: TacticSourceEdit::Partial(span.clone()),
                sibling_starts: Vec::new(),
            }),
        };
        entries.push(entry.clone());
        if smart {
            smart_container_alias_entries(tokens, token_range.clone(), tactic, &entry, entries);
            continue;
        }
        let arms: Option<Vec<&[ProofTactic]>> = match tactic {
            ProofTactic::If(proof_if) => Some(vec![&proof_if.then_tactics, &proof_if.else_tactics]),
            ProofTactic::Cases(cases) => {
                Some(cases.arms().iter().map(|arm| arm.tactics()).collect())
            }
            _ => None,
        };
        match (tactic, arms) {
            (ProofTactic::Have(have), _) => have_body_tactic_entries(
                tokens,
                token_range,
                have,
                site,
                claim_label,
                source_index,
                &path,
                entries,
            )?,
            // An arm tactic's path names the arm, then its position there.
            (_, Some(arms)) => {
                let blocks =
                    structured_tactic_arm_blocks(tokens, token_range.start)?.ok_or_else(|| {
                        ClickError::new("could not locate the arms of a source structured tactic")
                    })?;
                for (arm, ((open, close), tactics)) in blocks.into_iter().zip(arms).enumerate() {
                    let mut prefix = path.clone();
                    prefix.push(arm);
                    let arm_block = WrittenBlock {
                        open,
                        close,
                        tactics,
                        prefix: &prefix,
                    };
                    block_tactic_entries(
                        tokens,
                        &arm_block,
                        site,
                        claim_label,
                        source_index,
                        entries,
                    )?;
                }
            }
            // The linear body runner checks no other structured tactic, so a
            // smart tactic written inside one has no checked occurrence of
            // its own. Say so rather than selecting a neighbor.
            _ if tactic_contains_smart_tactic(tactic) => {
                entries.push(SourceTacticEntry {
                    span: span.clone(),
                    anchor: span.start,
                    claim_label: claim_label.to_string(),
                    tactic_name: tactic_name(tactic).to_string(),
                    smart: true,
                    selection: EntrySelection::Unaddressable(format!(
                        "the location is inside a proof `{}` written in a `have` body, which the `have` body checker does not run, so a smart tactic there has no checked occurrence of its own; expand the enclosing claim with `--claim {claim_label}`",
                        tactic_name(tactic)
                    )),
                });
            }
            _ => {}
        }
    }
    Ok(())
}

/// Records each smart tactic written inside a smart site that owns its body
/// (a smart `have`, `both`, or `close_invariants by`) as an alias selecting
/// that site: the body is expanded as part of the site, never on its own.
fn smart_container_alias_entries(
    tokens: &[SourceToken],
    tactic_tokens: Range<usize>,
    tactic: &ProofTactic,
    container: &SourceTacticEntry,
    entries: &mut Vec<SourceTacticEntry>,
) {
    let top_level_by = |range: Range<usize>| {
        let mut depth = 0_usize;
        range.clone().find(|&index| {
            match tokens[index].text.as_str() {
                "(" | "[" | "{" => depth += 1,
                ")" | "]" | "}" => depth = depth.saturating_sub(1),
                _ => {}
            }
            depth == 0 && tokens[index].text == "by"
        })
    };
    let block_after_by = |range: Range<usize>| {
        let by = top_level_by(range)?;
        let open = by + 1;
        (tokens.get(open)?.text == "{").then_some(open)
    };
    let mut blocks: Vec<(usize, &[ProofTactic])> = Vec::new();
    match tactic {
        ProofTactic::Have(have) => match &have.proof {
            SourceProof::Script(body) => {
                if let Some(open) = block_after_by(tactic_tokens) {
                    blocks.push((open, body));
                }
            }
            SourceProof::Tactic(smart) => {
                if let Some(by) = top_level_by(tactic_tokens)
                    && let Some(token) = tokens.get(by + 1)
                {
                    entries.push(SourceTacticEntry {
                        span: token.span.clone(),
                        anchor: token.span.start,
                        tactic_name: smart_tactic_name(*smart).to_string(),
                        ..container.clone()
                    });
                }
            }
            SourceProof::Default => {}
        },
        ProofTactic::CloseInvariantsBy(body) => {
            if let Some(open) = block_after_by(tactic_tokens) {
                blocks.push((open, body));
            }
        }
        ProofTactic::Both(both) => {
            let left = tactic_tokens
                .clone()
                .find(|&index| tokens[index].text == "{");
            if let Some(left) = left
                && let Ok(left_close) = matching_delimiter(tokens, left, "{", "}")
                && tokens
                    .get(left_close + 1)
                    .is_some_and(|token| token.text == "and")
                && tokens
                    .get(left_close + 2)
                    .is_some_and(|token| token.text == "{")
            {
                blocks.push((left, &both.left_tactics));
                blocks.push((left_close + 2, &both.right_tactics));
            }
        }
        _ => {}
    }
    for (open, body) in blocks {
        let Ok(close) = matching_delimiter(tokens, open, "{", "}") else {
            continue;
        };
        let Ok(direct) = direct_tactic_token_ranges(tokens, open, close) else {
            continue;
        };
        if direct.len() != body.len() {
            continue;
        }
        for (inner, range) in body.iter().zip(direct) {
            let span = tokens[range.start].span.start..tokens[range.end - 1].span.end;
            if source_site_kind(inner) == SourceSiteKind::ExpandableAutomation {
                entries.push(SourceTacticEntry {
                    span: span.clone(),
                    anchor: span.start,
                    tactic_name: tactic_name(inner).to_string(),
                    ..container.clone()
                });
            }
            smart_container_alias_entries(tokens, range, inner, container, entries);
        }
    }
}

/// Whether a smart tactic is written anywhere inside `tactic`.
fn tactic_contains_smart_tactic(tactic: &ProofTactic) -> bool {
    fn any(tactics: &[ProofTactic]) -> bool {
        tactics.iter().any(|tactic| {
            source_site_kind(tactic) == SourceSiteKind::ExpandableAutomation
                || tactic_contains_smart_tactic(tactic)
        })
    }
    fn proof(proof: &SourceProof) -> bool {
        match proof {
            SourceProof::Default | SourceProof::Tactic(_) => true,
            SourceProof::Script(tactics) => any(tactics),
        }
    }
    match tactic {
        ProofTactic::CloseInvariantsBy(tactics) => any(tactics),
        ProofTactic::StructuralInduct { arms, .. } => arms.iter().any(|arm| any(&arm.tactics)),
        ProofTactic::Have(have) => proof(&have.proof),
        ProofTactic::Open(open) => any(&open.tactics),
        ProofTactic::If(proof_if) => any(&proof_if.then_tactics) || any(&proof_if.else_tactics),
        ProofTactic::Match(proof_match) => proof_match.arms.iter().any(|arm| any(&arm.tactics)),
        ProofTactic::Cases(cases) => cases.arms().iter().any(|arm| any(arm.tactics())),
        ProofTactic::Both(both) => any(&both.left_tactics) || any(&both.right_tactics),
        ProofTactic::Branch(branch) => any(&branch.then_tactics) || any(&branch.else_tactics),
        ProofTactic::CallOutcomes(outcomes) => {
            any(&outcomes.returned_tactics) || any(&outcomes.threw_tactics)
        }
        ProofTactic::Loop(clause) => {
            clause.initialize_proof().is_none_or(proof) || clause.preserve_proof().is_none_or(proof)
        }
        _ => false,
    }
}

pub fn c0_tactic_source_position(
    click_source: &str,
    c_sources: &[(&str, &str)],
    claim_label: &str,
    source_index: usize,
) -> Result<SourcePosition, ClickError> {
    let sources = CSourceContext::bundle(c_sources);
    c0_tactic_source_position_context(&sources, click_source, claim_label, source_index)
}

pub fn c0_prepared_tactic_source_position(
    click_source: &str,
    imports: &[crate::languages::c::compiler_import::PreparedCImport],
    claim_label: &str,
    source_index: usize,
) -> Result<SourcePosition, ClickError> {
    let sources = CSourceContext::prepared(imports);
    c0_tactic_source_position_context(&sources, click_source, claim_label, source_index)
}

pub fn program_prepared_tactic_source_position(
    click_source: &str,
    import: &impl crate::languages::PreparedProgramSource,
    claim_label: &str,
    source_index: usize,
) -> Result<SourcePosition, ClickError> {
    let sources = CSourceContext::program(import)?;
    c0_tactic_source_position_context(&sources, click_source, claim_label, source_index)
}

/// Where the Click declaration named `name` is written: a function block,
/// a named contract or a theorem. The position is the first token of the
/// line the name is on, so the excerpt starts at the return type or
/// keyword. `None` when the source declares no such name.
///
/// A failure with no tactic or C statement to address, such as a contract
/// that could not be set up at entry, shows this declaration instead. A
/// declaration is the name followed by its parameters or body outside every
/// brace; a use of the name inside a body is not one.
pub fn click_declaration_source_position(click_source: &str, name: &str) -> Option<SourcePosition> {
    let tokens = scan_source_tokens(click_source).ok()?;
    let mut depth = 0usize;
    let declared = tokens.iter().enumerate().find_map(|(index, token)| {
        match token.text.as_str() {
            "{" => depth += 1,
            "}" => depth = depth.saturating_sub(1),
            text if depth == 0 && text == name => {
                // A generic declaration lists its type parameters between
                // the name and the parameter list.
                let mut next = index + 1;
                if tokens.get(next).map(|token| token.text.as_str()) == Some("<") {
                    next = tokens[next..]
                        .iter()
                        .position(|token| token.text == ">")
                        .map_or(next, |close| next + close + 1);
                }
                // A function, contract, resource or theorem is followed by
                // its parameters; a datatype by its body.
                if matches!(
                    tokens.get(next).map(|token| token.text.as_str()),
                    Some("(" | "{")
                ) {
                    return Some(token.span.start);
                }
            }
            _ => {}
        }
        None
    })?;
    let line_start = click_source[..declared]
        .rfind('\n')
        .map_or(0, |newline| newline + 1);
    let first_token = tokens
        .iter()
        .find(|token| token.span.start >= line_start)?
        .span
        .start;
    Some(position_at_offset(click_source, first_token))
}

pub fn c0_project_tactic_source_position(
    project: &ClickProject,
    c_sources: &[(&str, &str)],
    claim_label: &str,
    source_index: usize,
) -> Result<SourcePosition, ClickError> {
    let sources = CSourceContext::bundle(c_sources).with_click_project(project);
    let file = resolve_click_project_context(project, &sources)?;
    c0_tactic_source_position_file(
        &file,
        project.entry_source().expect("resolved entry source"),
        claim_label,
        source_index,
    )
}

pub fn c0_prepared_project_tactic_source_position(
    project: &ClickProject,
    imports: &[crate::languages::c::compiler_import::PreparedCImport],
    claim_label: &str,
    source_index: usize,
) -> Result<SourcePosition, ClickError> {
    let sources = CSourceContext::prepared(imports).with_click_project(project);
    let file = resolve_click_project_context(project, &sources)?;
    c0_tactic_source_position_file(
        &file,
        project.entry_source().expect("resolved entry source"),
        claim_label,
        source_index,
    )
}

pub fn program_prepared_project_tactic_source_position(
    project: &ClickProject,
    import: &impl crate::languages::PreparedProgramSource,
    claim_label: &str,
    source_index: usize,
) -> Result<SourcePosition, ClickError> {
    let sources = CSourceContext::program(import)?.with_click_project(project);
    let file = resolve_click_project_context(project, &sources)?;
    c0_tactic_source_position_file(
        &file,
        project.entry_source().expect("resolved entry source"),
        claim_label,
        source_index,
    )
}

pub fn c0_project_tactic_source_positions(
    project: &ClickProject,
    c_sources: &[(&str, &str)],
    claim_label: &str,
) -> Result<Vec<SourcePosition>, ClickError> {
    let sources = CSourceContext::bundle(c_sources).with_click_project(project);
    let file = resolve_click_project_context(project, &sources)?;
    c0_tactic_source_positions_file(
        &file,
        project.entry_source().expect("resolved entry source"),
        claim_label,
    )
}

pub fn c0_prepared_project_tactic_source_positions(
    project: &ClickProject,
    imports: &[crate::languages::c::compiler_import::PreparedCImport],
    claim_label: &str,
) -> Result<Vec<SourcePosition>, ClickError> {
    let sources = CSourceContext::prepared(imports).with_click_project(project);
    let file = resolve_click_project_context(project, &sources)?;
    c0_tactic_source_positions_file(
        &file,
        project.entry_source().expect("resolved entry source"),
        claim_label,
    )
}

pub fn program_prepared_project_tactic_source_positions(
    project: &ClickProject,
    import: &impl crate::languages::PreparedProgramSource,
    claim_label: &str,
) -> Result<Vec<SourcePosition>, ClickError> {
    let sources = CSourceContext::program(import)?.with_click_project(project);
    let file = resolve_click_project_context(project, &sources)?;
    c0_tactic_source_positions_file(
        &file,
        project.entry_source().expect("resolved entry source"),
        claim_label,
    )
}

fn c0_tactic_source_position_context(
    c_sources: &CSourceContext<'_>,
    click_source: &str,
    claim_label: &str,
    source_index: usize,
) -> Result<SourcePosition, ClickError> {
    let file = parse_source_with_c_layouts_context(click_source, c_sources)?;
    c0_tactic_source_position_file(&file, click_source, claim_label, source_index)
}

fn c0_tactic_source_position_file(
    file: &ClickFile,
    click_source: &str,
    claim_label: &str,
    source_index: usize,
) -> Result<SourcePosition, ClickError> {
    c0_tactic_source_positions_file(file, click_source, claim_label)?
        .get(source_index)
        .cloned()
        .ok_or_else(|| {
            ClickError::new(format!(
                "`{claim_label}` has no source tactic occurrence {source_index}"
            ))
        })
}

/// Resolve many byte offsets with one source walk, preserving request order.
/// In particular, a long line containing many tactics must not be rescanned
/// from its start for each tactic's character column.
fn positions_at_offsets(
    source: &str,
    offsets: impl IntoIterator<Item = usize>,
) -> Vec<SourcePosition> {
    let mut ordered: Vec<_> = offsets.into_iter().enumerate().collect();
    ordered.sort_unstable_by_key(|(_, offset)| *offset);
    let mut positions = vec![SourcePosition::new(1, 1); ordered.len()];
    let mut chars = source.char_indices().peekable();
    let mut line = 1;
    let mut column = 1;
    for (index, offset) in ordered {
        crate::instrumentation::record_deterministic_work(1);
        while let Some(&(at, character)) = chars.peek() {
            if at >= offset {
                break;
            }
            chars.next();
            crate::instrumentation::record_deterministic_work(1);
            if character == '\n' {
                line += 1;
                column = 1;
            } else {
                column += 1;
            }
        }
        positions[index] = SourcePosition::new(line, column);
    }
    positions
}

fn c0_tactic_source_positions_file(
    file: &ClickFile,
    click_source: &str,
    claim_label: &str,
) -> Result<Vec<SourcePosition>, ClickError> {
    let tokens = scan_source_tokens(click_source)?;
    for theorem in file.theorem_definitions() {
        if !file.theorem_is_selected(theorem.name()) {
            continue;
        }
        let source = find_theorem(&tokens, theorem.name())?;
        for (ensure_index, ensure) in theorem.ensures().iter().enumerate() {
            let label = ensure.name().map_or_else(
                || format!("{}.ensures_{ensure_index}", theorem.name()),
                |name| format!("{}.{name}", theorem.name()),
            );
            let execution_claim = theorem.executes.is_some()
                && ensure_index == 0
                && claim_label == format!("{}.contract", theorem.name());
            if label != claim_label && !execution_claim {
                continue;
            }
            let edit =
                find_ensure_proof_edit(&tokens, source.body_open, source.body_close, ensure_index)?;
            return proof_source_positions(
                click_source,
                &tokens,
                match &edit {
                    ProofSourceEdit::Explicit(span) => Some(span),
                    ProofSourceEdit::DefaultTerminator { .. }
                    | ProofSourceEdit::OmittedLoopPhase { .. } => None,
                },
                Some(ensure.proof()),
                edit.selector(),
                claim_label,
            );
        }
    }
    for tactic in file.tactic_definitions() {
        if claim_label != format!("{}.contract", tactic.name()) {
            continue;
        }
        let function = find_tactic(&tokens, tactic.name())?;
        return proof_source_positions(
            click_source,
            &tokens,
            Some(&find_grouped_proof_span(&tokens, &function)?),
            tactic.function_block().grouped_proof(),
            tokens[function.body_close].span.start,
            claim_label,
        );
    }
    for function_block in proof_function_blocks(file) {
        let function_name = function_block.signature().name();
        let function = find_function(&tokens, function_name)?;
        for clause in function_block.structural_clauses() {
            let block = find_structural_clause_block(&tokens, &function, *clause.region())?;
            let edits = structural_item_proof_edits(&tokens, &block)?;
            if edits.len() != clause.items().len() {
                return Err(ClickError::new(format!(
                    "structural source mapping for `{function_name}` {:?} found {} items, expected {}",
                    clause.region(),
                    edits.len(),
                    clause.items().len()
                )));
            }
        }
        if let Some(rest) = claim_label
            .strip_prefix(function_name)
            .and_then(|rest| rest.strip_prefix(".loop("))
            && let Some((loop_index, phase)) = rest.split_once(").")
            && matches!(phase, "initialize" | "preserve")
            && let Ok(loop_index) = loop_index.parse::<usize>()
            && let Some(clause) = function_block
                .structural_clauses()
                .iter()
                .find(|clause| clause.region() == &CodeRegion::Loop(loop_index))
        {
            let proof = if phase == "initialize" {
                clause.initialize_proof()
            } else {
                clause.preserve_proof()
            };
            let (fallback, proof_span, _) =
                find_loop_phase_proof_span(&tokens, &function, loop_index, phase)?;
            return proof_source_positions(
                click_source,
                &tokens,
                proof_span.as_ref(),
                proof,
                fallback,
                claim_label,
            );
        }
        let selected = if claim_label == format!("{function_name}.contract") {
            function_block
                .covering_proof()
                .map(|proof| (CProofClaim::Grouped, proof))
        } else {
            function_block
                .ensures()
                .iter()
                .enumerate()
                .find_map(|(index, ensure)| {
                    let label = ensure.name().map_or_else(
                        || format!("{function_name}.ensures_{index}"),
                        |name| format!("{function_name}.{name}"),
                    );
                    (label == claim_label).then_some((CProofClaim::Ensure(index), ensure.proof()))
                })
                .or_else(|| {
                    function_block
                        .exceptional_ensures()
                        .iter()
                        .enumerate()
                        .find_map(|(index, ensure)| {
                            let label = ensure.name().map_or_else(
                                || format!("{function_name}.exceptional_ensures_{index}"),
                                |name| format!("{function_name}.{name}"),
                            );
                            (label == claim_label)
                                .then_some((CProofClaim::ExceptionalEnsure(index), ensure.proof()))
                        })
                })
        };
        let Some((claim, proof)) = selected else {
            continue;
        };
        let fallback = match claim {
            CProofClaim::Grouped => tokens[function.body_close].span.start,
            CProofClaim::Ensure(_) | CProofClaim::ExceptionalEnsure(_) => {
                find_claim_clause_offset(&tokens, &function, function_block, claim)?
            }
        };
        let proof_span = match claim {
            CProofClaim::Grouped => {
                match find_grouped_proof_edit(&tokens, &function, function_block)? {
                    ProofSourceEdit::Explicit(span) => Some(span),
                    ProofSourceEdit::DefaultTerminator { .. }
                    | ProofSourceEdit::OmittedLoopPhase { .. } => None,
                }
            }
            CProofClaim::Ensure(_) | CProofClaim::ExceptionalEnsure(_) => {
                find_claim_proof_span(&tokens, &function, function_block, claim).ok()
            }
        };
        return proof_source_positions(
            click_source,
            &tokens,
            proof_span.as_ref(),
            Some(proof),
            fallback,
            claim_label,
        );
    }
    Err(ClickError::new(format!(
        "could not locate source proof `{claim_label}`"
    )))
}

fn proof_source_positions(
    click_source: &str,
    tokens: &[SourceToken],
    proof_span: Option<&Range<usize>>,
    proof: Option<&SourceProof>,
    fallback: usize,
    claim_label: &str,
) -> Result<Vec<SourcePosition>, ClickError> {
    if let Some(tactics) = proof.and_then(SourceProof::tactics) {
        let proof_span = proof_span.ok_or_else(|| {
            ClickError::new(format!(
                "`{claim_label}` has no explicit source proof clause"
            ))
        })?;
        let spans = collect_source_tactic_spans(tokens, proof_span, tactics)?;
        return Ok(positions_at_offsets(
            click_source,
            spans.iter().map(|span| span.start),
        ));
    }
    if let Some(proof_span) = proof_span {
        let by = tokens
            .binary_search_by_key(&proof_span.start, |token| token.span.start)
            .ok()
            .filter(|index| tokens[*index].text == "by")
            .ok_or_else(|| ClickError::new("could not locate source `by` clause"))?;
        if let Some(tactic) = tokens.get(by + 1) {
            return Ok(vec![position_at_offset(click_source, tactic.span.start)]);
        }
    }
    Ok(vec![position_at_offset(click_source, fallback)])
}

fn find_claim_clause_offset(
    tokens: &[SourceToken],
    function: &FunctionSource,
    function_block: &FunctionBlock,
    claim: CProofClaim,
) -> Result<usize, ClickError> {
    Ok(find_claim_proof_edit(tokens, function, function_block, claim)?.selector())
}

fn find_loop_phase_proof_span(
    tokens: &[SourceToken],
    function: &FunctionSource,
    wanted_loop: usize,
    phase: &str,
) -> Result<(usize, Option<Range<usize>>, usize), ClickError> {
    let mut depth = 0;
    let mut index = function.body_open + 1;
    while index < function.body_close {
        match tokens[index].text.as_str() {
            "{" => depth += 1,
            "}" => depth -= 1,
            "for"
                if depth == 0
                    && tokens.get(index + 1).map(|token| token.text.as_str()) == Some("loop")
                    && tokens.get(index + 2).map(|token| token.text.as_str()) == Some("(") =>
            {
                let loop_index = tokens
                    .get(index + 3)
                    .and_then(|token| token.text.parse::<usize>().ok());
                let mut open = index + 5;
                if tokens.get(open).map(|token| token.text.as_str()) == Some("as") {
                    open += 2;
                }
                if loop_index == Some(wanted_loop)
                    && tokens.get(index + 4).map(|token| token.text.as_str()) == Some(")")
                    && tokens.get(open).map(|token| token.text.as_str()) == Some("{")
                {
                    let selector = if phase == "initialize" {
                        tokens[index].span.start
                    } else {
                        tokens[index + 1].span.start
                    };
                    let close = matching_delimiter(tokens, open, "{", "}")?;
                    let mut nested = 0;
                    for cursor in open + 1..close {
                        match tokens[cursor].text.as_str() {
                            "{" => nested += 1,
                            "}" => nested -= 1,
                            text if nested == 0 && text == phase => {
                                let by = cursor + 1;
                                if tokens.get(by).map(|token| token.text.as_str()) != Some("by") {
                                    return Err(ClickError::new(format!(
                                        "`{phase}` has no source `by` clause"
                                    )));
                                }
                                return Ok((
                                    selector,
                                    Some(proof_span(tokens, by)?),
                                    tokens[close].span.start,
                                ));
                            }
                            _ => {}
                        }
                    }
                    return Ok((selector, None, tokens[close].span.start));
                }
            }
            _ => {}
        }
        index += 1;
    }
    Err(ClickError::new(format!(
        "could not locate source loop({wanted_loop})"
    )))
}

fn parse_source_with_c_layouts(
    click_source: &str,
    c_sources: &[(&str, &str)],
) -> Result<ClickFile, ClickError> {
    let sources = CSourceContext::bundle(c_sources);
    parse_source_with_c_layouts_context(click_source, &sources)
}

fn parse_source_with_c_layouts_context(
    click_source: &str,
    sources: &CSourceContext<'_>,
) -> Result<ClickFile, ClickError> {
    let (
        struct_layouts,
        union_layouts,
        aggregate_objects,
        aggregate_array_objects,
        global_array_shapes,
        qualified_objects,
        local_struct_pointers,
    ) = parse_c_layouts(click_source, sources)?;
    parser::parse_with_layouts_and_aggregate_objects(
        click_source,
        struct_layouts,
        union_layouts,
        aggregate_objects,
        aggregate_array_objects,
        global_array_shapes,
        qualified_objects,
        local_struct_pointers,
    )
}

fn find_structural_clause_block(
    tokens: &[SourceToken],
    function: &FunctionSource,
    wanted: CodeRegion,
) -> Result<Range<usize>, ClickError> {
    let mut depth = 0;
    let mut index = function.body_open + 1;
    while index < function.body_close {
        match tokens[index].text.as_str() {
            "{" => depth += 1,
            "}" => depth -= 1,
            "for" if depth == 0 => {
                let kind = tokens.get(index + 1).map(|token| token.text.as_str());
                let region = match kind {
                    Some("loop" | "statement")
                        if tokens.get(index + 2).map(|token| token.text.as_str()) == Some("(") =>
                    {
                        let region_index = tokens
                            .get(index + 3)
                            .and_then(|token| token.text.parse::<usize>().ok());
                        if tokens.get(index + 4).map(|token| token.text.as_str()) != Some(")") {
                            None
                        } else {
                            region_index.map(|region_index| {
                                if kind == Some("loop") {
                                    CodeRegion::Loop(region_index)
                                } else {
                                    CodeRegion::Statement(region_index)
                                }
                            })
                        }
                    }
                    _ => None,
                };
                let mut open = index + 5;
                if tokens.get(open).map(|token| token.text.as_str()) == Some("as") {
                    open += 2;
                }
                if region == Some(wanted)
                    && tokens.get(open).map(|token| token.text.as_str()) == Some("{")
                {
                    let close = matching_delimiter(tokens, open, "{", "}")?;
                    return Ok(open..close);
                }
            }
            _ => {}
        }
        index += 1;
    }
    Err(ClickError::new(format!(
        "could not locate structural source block {wanted:?}"
    )))
}

fn structural_item_proof_edits(
    tokens: &[SourceToken],
    block: &Range<usize>,
) -> Result<Vec<ProofSourceEdit>, ClickError> {
    fn token_after_edit(tokens: &[SourceToken], edit: &ProofSourceEdit) -> usize {
        tokens
            .iter()
            .position(|token| token.span.end == edit.span().end)
            .map_or(tokens.len(), |index| index + 1)
    }

    let mut edits = Vec::new();
    let mut cursor = block.start + 1;
    while cursor < block.end {
        match tokens[cursor].text.as_str() {
            "initialize" | "preserve" => {
                let by = cursor + 1;
                if tokens.get(by).map(|token| token.text.as_str()) != Some("by") {
                    return Err(ClickError::new(
                        "loop phase is missing its source `by` clause",
                    ));
                }
                let phase = ProofSourceEdit::Explicit(proof_span(tokens, by)?);
                cursor = token_after_edit(tokens, &phase);
            }
            "invariant" | "assert" | "immutable" | "mutable" => {
                let edit = find_proof_edit_after(tokens, cursor, block.end)?;
                cursor = token_after_edit(tokens, &edit);
                edits.push(edit);
            }
            "step" if tokens.get(cursor + 1).map(|token| token.text.as_str()) == Some("{") => {
                let open = cursor + 1;
                let close = matching_delimiter(tokens, open, "{", "}")?;
                let mut item = open + 1;
                while item < close {
                    if matches!(tokens[item].text.as_str(), "immutable" | "mutable") {
                        let edit = find_proof_edit_after(tokens, item, close)?;
                        item = token_after_edit(tokens, &edit);
                        edits.push(edit);
                    } else {
                        item += 1;
                    }
                }
                cursor = close + 1;
            }
            _ => cursor += 1,
        }
    }
    Ok(edits)
}

fn offset_at_position(source: &str, line: usize, column: usize) -> Result<usize, ClickError> {
    if line == 0 || column == 0 {
        return Err(ClickError::new("source lines and columns are one-based"));
    }
    let mut line_start = 0;
    for current_line in 1..line {
        let Some(newline) = source[line_start..].find('\n') else {
            return Err(ClickError::new(format!("source has no line {line}")));
        };
        line_start += newline + 1;
        if current_line + 1 == line {
            break;
        }
    }
    let line_end = source[line_start..]
        .find('\n')
        .map_or(source.len(), |newline| line_start + newline);
    let line_source = &source[line_start..line_end];
    let byte_in_line = if column == 1 {
        0
    } else {
        line_source
            .char_indices()
            .nth(column - 1)
            .map(|(offset, _)| offset)
            .ok_or_else(|| ClickError::new(format!("line {line} has no column {column}")))?
    };
    Ok(line_start + byte_in_line)
}

/// The written arm blocks, as `(open, close)` token pairs, of a proof `if`,
/// `cases`, or `both` tactic starting at token `start`; `None` for any other
/// tactic.
fn structured_tactic_arm_blocks(
    tokens: &[SourceToken],
    start: usize,
) -> Result<Option<Vec<(usize, usize)>>, ClickError> {
    let kind = tokens[start].text.as_str();
    if !matches!(kind, "if" | "cases" | "both") {
        return Ok(None);
    }
    let end = tactic_end_token(tokens, start, tokens.len())?;
    let range = start..end + 1;
    let (first_open, first_close, second_open, second_close) = match kind {
        "if" => find_if_branch_blocks(tokens, &range)?,
        "cases" => return find_cases_arm_blocks(tokens, &range).map(Some),
        _ => {
            let left_open = (start + 1..range.end)
                .find(|&index| tokens[index].text == "{")
                .ok_or_else(|| ClickError::new("source `both` tactic has no left arm"))?;
            let left_close = matching_delimiter(tokens, left_open, "{", "}")?;
            let right_open = left_close + 2;
            if tokens.get(left_close + 1).map(|token| token.text.as_str()) != Some("and")
                || tokens.get(right_open).map(|token| token.text.as_str()) != Some("{")
            {
                return Err(ClickError::new("source `both` tactic has no right arm"));
            }
            let right_close = matching_delimiter(tokens, right_open, "{", "}")?;
            (left_open, left_close, right_open, right_close)
        }
    };
    Ok(Some(vec![
        (first_open, first_close),
        (second_open, second_close),
    ]))
}

/// Resolve positions inside written `have` and `open` bodies and structured
/// tactic arms. The first position is the enclosing tactic, as reported by
/// the usual claim mapper; the indices then descend as a proof step's source
/// path does: below a `have` or `open`, one index selects a direct tactic in
/// its body; below an `if`, `cases`, or `both`, two indices select an arm
/// and then a direct tactic in it.
pub fn nested_tactic_source_position(
    source: &str,
    outer: &SourcePosition,
    nested_indices: &[usize],
) -> Result<SourcePosition, ClickError> {
    let tokens = scan_source_tokens(source)?;
    let offset = offset_at_position(source, outer.line, outer.column)?;
    let mut current = tokens
        .iter()
        .position(|token| token.span.start == offset)
        .ok_or_else(|| ClickError::new("could not locate enclosing source tactic"))?;
    let mut indices = nested_indices.iter().copied();
    while let Some(index) = indices.next() {
        let kind = tokens[current].text.as_str();
        if let Some(arms) = structured_tactic_arm_blocks(&tokens, current)? {
            let (open, close) = *arms
                .get(index)
                .ok_or_else(|| ClickError::new(format!("source `{kind}` has no arm {index}")))?;
            let position = indices.next().ok_or_else(|| {
                ClickError::new(format!(
                    "source path names arm {index} of `{kind}` without a tactic in it"
                ))
            })?;
            let ranges = direct_tactic_token_ranges(&tokens, open, close)?;
            current = ranges
                .get(position)
                .ok_or_else(|| {
                    ClickError::new(format!("source `{kind}` arm tactic {position} is missing"))
                })?
                .start;
            continue;
        }
        if !matches!(kind, "have" | "open") {
            return Err(ClickError::new(format!(
                "source `{kind}` has no nested `have` or `open` tactic body"
            )));
        }
        let mut depths = [0_usize; 3];
        let mut body_open = None;
        for cursor in current + 1..tokens.len() {
            let token = tokens[cursor].text.as_str();
            if depths == [0; 3] {
                if kind == "have"
                    && token == "by"
                    && tokens.get(cursor + 1).map(|token| token.text.as_str()) == Some("{")
                {
                    body_open = Some(cursor + 1);
                    break;
                }
                if kind == "open" && token == "{" {
                    body_open = Some(cursor);
                    break;
                }
                if token == ";" {
                    break;
                }
            }
            match token {
                "(" => depths[0] += 1,
                ")" => depths[0] = depths[0].saturating_sub(1),
                "[" => depths[1] += 1,
                "]" => depths[1] = depths[1].saturating_sub(1),
                "{" => depths[2] += 1,
                "}" => depths[2] = depths[2].saturating_sub(1),
                _ => {}
            }
        }
        let open = body_open.ok_or_else(|| {
            ClickError::new(format!("could not locate source `{kind}` tactic body"))
        })?;
        let close = matching_delimiter(&tokens, open, "{", "}")?;
        let ranges = direct_tactic_token_ranges(&tokens, open, close)?;
        current = ranges
            .get(index)
            .ok_or_else(|| ClickError::new(format!("nested source tactic {index} is missing")))?
            .start;
    }
    Ok(position_at_offset(source, tokens[current].span.start))
}

/// Return the exact written tactic beginning at a diagnostic source position.
/// The position is resolved by the same source mapper used for proof steps.
pub fn tactic_source_at_position(
    source: &str,
    position: &SourcePosition,
) -> Result<String, ClickError> {
    let tokens = scan_source_tokens(source)?;
    let offset = offset_at_position(source, position.line, position.column)?;
    let start = tokens
        .iter()
        .position(|token| token.span.start == offset)
        .ok_or_else(|| ClickError::new("could not locate source tactic"))?;
    let end = tactic_end_token(&tokens, start, tokens.len())?;
    Ok(source[tokens[start].span.start..tokens[end].span.end].to_string())
}

/// Select the written arm containing a trace target inside a two-arm tactic.
/// Returning `None` means the target lies outside both arms (for example, in
/// the continuation after a completed branch).
pub fn tactic_arm_containing_position(
    source: &str,
    tactic_position: &SourcePosition,
    target_position: &SourcePosition,
) -> Result<Option<usize>, ClickError> {
    let tokens = scan_source_tokens(source)?;
    let tactic_offset = offset_at_position(source, tactic_position.line, tactic_position.column)?;
    let target_offset = offset_at_position(source, target_position.line, target_position.column)?;
    let start = tokens
        .iter()
        .position(|token| token.span.start == tactic_offset)
        .ok_or_else(|| ClickError::new("could not locate trace branch tactic"))?;
    let end = tactic_end_token(&tokens, start, tokens.len())?;
    let range = start..end + 1;
    let pair = |(first_open, first_close, second_open, second_close)| {
        vec![(first_open, first_close), (second_open, second_close)]
    };
    let blocks = match tokens[start].text.as_str() {
        "branch" => pair(find_branch_blocks(&tokens, &range)?),
        "if" => pair(find_if_branch_blocks(&tokens, &range)?),
        "outcomes" => pair(find_outcomes_arm_blocks(&tokens, &range)?),
        "cases" => find_cases_arm_blocks(&tokens, &range)?,
        "both" => {
            let left_open = start + 1;
            if tokens.get(left_open).map(|token| token.text.as_str()) != Some("{") {
                return Ok(None);
            }
            let left_close = matching_delimiter(&tokens, left_open, "{", "}")?;
            let right_open = left_close + 2;
            if tokens.get(left_close + 1).map(|token| token.text.as_str()) != Some("and")
                || tokens.get(right_open).map(|token| token.text.as_str()) != Some("{")
            {
                return Ok(None);
            }
            pair((
                left_open,
                left_close,
                right_open,
                matching_delimiter(&tokens, right_open, "{", "}")?,
            ))
        }
        _ => return Ok(None),
    };
    for (index, (open, close)) in blocks.into_iter().enumerate() {
        if tokens[open].span.start < target_offset && target_offset < tokens[close].span.end {
            return Ok(Some(index));
        }
    }
    Ok(None)
}

/// Whether a selected tactic is inside the proof body of a written `have`.
/// A completed `have` exports its proposition, not the body's intermediate
/// facts; the trace only enters that body when it contains the target.
pub fn tactic_have_body_contains_position(
    source: &str,
    tactic_position: &SourcePosition,
    target_position: &SourcePosition,
) -> Result<bool, ClickError> {
    let tokens = scan_source_tokens(source)?;
    let tactic_offset = offset_at_position(source, tactic_position.line, tactic_position.column)?;
    let target_offset = offset_at_position(source, target_position.line, target_position.column)?;
    let start = tokens
        .iter()
        .position(|token| token.span.start == tactic_offset)
        .ok_or_else(|| ClickError::new("could not locate trace have tactic"))?;
    if tokens[start].text != "have" {
        return Ok(false);
    }
    let end = tactic_end_token(&tokens, start, tokens.len())?;
    let Some(by) = (start..=end).find(|&index| tokens[index].text == "by") else {
        return Ok(false);
    };
    let Some(open) = (by + 1..=end).find(|&index| tokens[index].text == "{") else {
        return Ok(false);
    };
    let close = matching_delimiter(&tokens, open, "{", "}")?;
    Ok(tokens[open].span.start < target_offset && target_offset < tokens[close].span.end)
}

/// Whether another written tactic starts on the same source line. Inspect
/// tactic blocks through the source tokenizer, so semicolons inside a tactic
/// or its nested expressions are not mistaken for sibling tactics.
pub fn tactic_line_has_multiple_starts(
    source: &str,
    position: &SourcePosition,
) -> Result<bool, ClickError> {
    let selected = offset_at_position(source, position.line, position.column)?;
    let mut starts = tactic_starts_on_line(source, position.line)?;
    if !starts.iter().any(|start| start.column == position.column) {
        starts.push(position_at_offset(source, selected));
    }
    if starts.len() <= 1 {
        return Ok(false);
    }
    // A one-line `have ... by { simp(); }` has two lexical tactic starts,
    // but the outer `have` is still the one unambiguous top-level tactic on
    // that line. Keep a column for the nested tactic, or for sibling tactics.
    if starts
        .first()
        .is_none_or(|start| start.column != position.column)
    {
        return Ok(true);
    }
    let tokens = scan_source_tokens(source)?;
    let Some(start) = tokens.iter().position(|token| token.span.start == selected) else {
        return Ok(true);
    };
    let end = tactic_end_token(&tokens, start, tokens.len())?;
    Ok(starts.iter().skip(1).any(|start| {
        offset_at_position(source, start.line, start.column)
            .is_ok_and(|offset| offset >= tokens[end].span.end)
    }))
}

/// Candidate written tactic starts on a Click source line, for selecting a
/// trace target without requiring a column when the line is unambiguous.
pub fn tactic_starts_on_line(source: &str, line: usize) -> Result<Vec<SourcePosition>, ClickError> {
    let tokens = scan_source_tokens(source)?;
    // The line's byte range, found once: asking each tactic start for its
    // line would rescan the source from the top for every tactic in it.
    let mut line_starts = std::iter::once(0).chain(
        source
            .bytes()
            .enumerate()
            .filter_map(|(offset, byte)| (byte == b'\n').then_some(offset + 1)),
    );
    let Some(line_start) = line.checked_sub(1).and_then(|index| line_starts.nth(index)) else {
        return Ok(Vec::new());
    };
    let line_end = line_starts.next().unwrap_or(source.len() + 1);
    // The `then` block of a proof `if` and the arm blocks of `cases` follow
    // a condition, not a keyword; they are found from the tactic that owns
    // them, which the scan reaches first.
    let mut arm_blocks = std::collections::BTreeSet::new();
    let mut starts = std::collections::BTreeSet::new();
    for (open, token) in tokens.iter().enumerate() {
        if token.text != "{" {
            continue;
        }
        let preceding = open.checked_sub(1).and_then(|index| tokens.get(index));
        // A match arm's block follows `=>`, which the scanner emits as the
        // two punctuation tokens `=` and `>`.
        let arm_block = open >= 2 && tokens[open - 2].text == "=" && tokens[open - 1].text == ">";
        let direct_proof_block = arm_block
            || preceding.is_some_and(|token| {
                matches!(token.text.as_str(), "by" | "then" | "else" | "and" | "both")
            });
        let open_tactic_block = preceding.is_some_and(|token| token.text == ")")
            && tokens[..open]
                .iter()
                .rev()
                .take_while(|token| !matches!(token.text.as_str(), ";" | "{" | "}"))
                .any(|token| token.text == "open");
        if !direct_proof_block && !open_tactic_block && !arm_blocks.contains(&open) {
            continue;
        }
        let Ok(close) = matching_delimiter(&tokens, open, "{", "}") else {
            continue;
        };
        let Ok(ranges) = direct_tactic_token_ranges(&tokens, open, close) else {
            continue;
        };
        for range in ranges {
            match tokens[range.start].text.as_str() {
                "if" => {
                    if let Ok((then_open, ..)) = find_if_branch_blocks(&tokens, &range) {
                        arm_blocks.insert(then_open);
                    }
                }
                "cases" => {
                    if let Ok(arms) = find_cases_arm_blocks(&tokens, &range) {
                        arm_blocks.extend(arms.into_iter().map(|(open, _)| open));
                    }
                }
                _ => {}
            }
            let start = tokens[range.start].span.start;
            if (line_start..line_end).contains(&start) {
                starts.insert(start);
            }
        }
    }
    Ok(starts
        .into_iter()
        .map(|start| position_at_offset(source, start))
        .collect())
}

pub(super) fn position_at_offset(source: &str, offset: usize) -> SourcePosition {
    let prefix = &source[..offset];
    let line = prefix.bytes().filter(|byte| *byte == b'\n').count() + 1;
    let line_start = prefix.rfind('\n').map_or(0, |newline| newline + 1);
    let column = source[line_start..offset].chars().count() + 1;
    SourcePosition::new(line, column)
}

fn proof_span(tokens: &[SourceToken], by: usize) -> Result<Range<usize>, ClickError> {
    let start = tokens[by].span.start;
    let body = by + 1;
    let end_token = match tokens.get(body).map(|token| token.text.as_str()) {
        Some("{") => matching_delimiter(tokens, body, "{", "}")?,
        Some("auto" | "simp") => body,
        _ => return Err(ClickError::new("unsupported source proof clause")),
    };
    let semicolon = end_token + 1;
    let end = if tokens.get(semicolon).map(|token| token.text.as_str()) == Some(";") {
        tokens[semicolon].span.end
    } else {
        tokens[end_token].span.end
    };
    Ok(start..end)
}

fn collect_source_tactic_spans(
    tokens: &[SourceToken],
    proof_span: &Range<usize>,
    tactics: &[ProofTactic],
) -> Result<Vec<Range<usize>>, ClickError> {
    Ok(collect_source_tactics(tokens, proof_span, tactics)?
        .into_iter()
        .map(|tactic| tactic.span)
        .collect())
}

/// One claim-level source tactic, in the flat pre-order numbering that
/// timing, profiling, audit, and expansion share.
struct FlatSourceTactic<'t> {
    span: Range<usize>,
    /// The tactic's token range, end exclusive.
    tokens: Range<usize>,
    tactic: FlatTactic<'t>,
}

#[derive(Clone, Copy)]
enum FlatTactic<'t> {
    Written(&'t ProofTactic),
    /// A frontier-local loop phase proved by one smart tactic (`by simp`).
    Phase(SmartTactic),
}

fn collect_source_tactics<'t>(
    tokens: &[SourceToken],
    proof_span: &Range<usize>,
    tactics: &'t [ProofTactic],
) -> Result<Vec<FlatSourceTactic<'t>>, ClickError> {
    let by = tokens
        .binary_search_by_key(&proof_span.start, |token| token.span.start)
        .ok()
        .filter(|index| tokens[*index].text == "by")
        .ok_or_else(|| ClickError::new("could not locate selected source proof"))?;
    let open = by + 1;
    if tokens.get(open).map(|token| token.text.as_str()) != Some("{") {
        return Err(ClickError::new(
            "individual tactic expansion requires an explicit `by { ... }` proof",
        ));
    }
    let close = matching_delimiter(tokens, open, "{", "}")?;
    let mut spans = Vec::new();
    collect_tactic_block_spans(tokens, open, close, tactics, &mut spans)?;
    Ok(spans)
}

fn collect_tactic_block_spans<'t>(
    tokens: &[SourceToken],
    open: usize,
    close: usize,
    tactics: &'t [ProofTactic],
    spans: &mut Vec<FlatSourceTactic<'t>>,
) -> Result<(), ClickError> {
    let direct = direct_tactic_token_ranges(tokens, open, close)?;
    if direct.len() != tactics.len() {
        return Err(ClickError::new(format!(
            "source proof has {} direct tactic(s), but the parsed proof has {}",
            direct.len(),
            tactics.len()
        )));
    }
    for (tactic, token_range) in tactics.iter().zip(direct) {
        spans.push(FlatSourceTactic {
            span: tokens[token_range.start].span.start..tokens[token_range.end - 1].span.end,
            tokens: token_range.clone(),
            tactic: FlatTactic::Written(tactic),
        });
        match tactic {
            ProofTactic::Open(proof_open) => {
                let body_open = (token_range.start + 1..token_range.end)
                    .find(|index| tokens[*index].text == "{")
                    .ok_or_else(|| ClickError::new("source `open` tactic has no body"))?;
                let body_close = matching_delimiter(tokens, body_open, "{", "}")?;
                collect_tactic_block_spans(
                    tokens,
                    body_open,
                    body_close,
                    &proof_open.tactics,
                    spans,
                )?;
            }
            ProofTactic::If(proof_if) => {
                let (then_open, then_close, else_open, else_close) =
                    find_if_branch_blocks(tokens, &token_range)?;
                collect_tactic_block_spans(
                    tokens,
                    then_open,
                    then_close,
                    &proof_if.then_tactics,
                    spans,
                )?;
                collect_tactic_block_spans(
                    tokens,
                    else_open,
                    else_close,
                    &proof_if.else_tactics,
                    spans,
                )?;
            }
            ProofTactic::Branch(proof_branch) => {
                let (then_open, then_close, else_open, else_close) =
                    find_branch_blocks(tokens, &token_range)?;
                collect_tactic_block_spans(
                    tokens,
                    then_open,
                    then_close,
                    &proof_branch.then_tactics,
                    spans,
                )?;
                collect_tactic_block_spans(
                    tokens,
                    else_open,
                    else_close,
                    &proof_branch.else_tactics,
                    spans,
                )?;
            }
            ProofTactic::Cases(proof_cases) => {
                let blocks = find_cases_arm_blocks(tokens, &token_range)?;
                if blocks.len() != proof_cases.arms().len() {
                    return Err(ClickError::new(
                        "source `cases` arms do not match the parsed proof",
                    ));
                }
                for ((open, close), arm) in blocks.into_iter().zip(proof_cases.arms()) {
                    collect_tactic_block_spans(tokens, open, close, arm.tactics(), spans)?;
                }
            }
            ProofTactic::CallOutcomes(outcomes) => {
                let (returned_open, returned_close, threw_open, threw_close) =
                    find_outcomes_arm_blocks(tokens, &token_range)?;
                collect_tactic_block_spans(
                    tokens,
                    returned_open,
                    returned_close,
                    &outcomes.returned_tactics,
                    spans,
                )?;
                collect_tactic_block_spans(
                    tokens,
                    threw_open,
                    threw_close,
                    &outcomes.threw_tactics,
                    spans,
                )?;
            }
            ProofTactic::StructuralInduct { arms, .. } => {
                let arm_blocks = find_structural_induction_arm_blocks(tokens, &token_range)?;
                if arm_blocks.len() != arms.len() {
                    return Err(ClickError::new(format!(
                        "source proof match has {} arm(s), but the parsed tactic has {}",
                        arm_blocks.len(),
                        arms.len()
                    )));
                }
                for (arm, (arm_open, arm_close)) in arms.iter().zip(arm_blocks) {
                    collect_tactic_block_spans(tokens, arm_open, arm_close, &arm.tactics, spans)?;
                }
            }
            ProofTactic::Match(proof_match) => {
                let arms = &proof_match.arms;
                let arm_blocks = find_structural_induction_arm_blocks(tokens, &token_range)?;
                if arm_blocks.len() != arms.len() {
                    return Err(ClickError::new(format!(
                        "source structural induction has {} arm(s), but the parsed tactic has {}",
                        arm_blocks.len(),
                        arms.len()
                    )));
                }
                for (arm, (arm_open, arm_close)) in arms.iter().zip(arm_blocks) {
                    collect_tactic_block_spans(tokens, arm_open, arm_close, &arm.tactics, spans)?;
                }
            }
            ProofTactic::Loop(clause) => {
                let block_open = (token_range.start..token_range.end)
                    .find(|index| tokens[*index].text == "{")
                    .ok_or_else(|| ClickError::new("source `loop` tactic has no body"))?;
                let block_close = matching_delimiter(tokens, block_open, "{", "}")?;
                let block = block_open..block_close;
                for (phase, proof) in [
                    ("initialize", clause.initialize_proof()),
                    ("preserve", clause.preserve_proof()),
                ] {
                    if let Some(proof) = proof {
                        let edit = inline_loop_phase_proof_edit(tokens, &block, phase)?
                            .ok_or_else(|| {
                                ClickError::new(format!(
                                    "parsed frontier-local loop has `{phase}` proof but source block does not"
                                ))
                            })?;
                        collect_nested_proof_spans(tokens, &edit, proof, spans)?;
                    }
                }
                let edits = structural_item_proof_edits(tokens, &block)?;
                if edits.len() != clause.items().len() {
                    return Err(ClickError::new(format!(
                        "frontier-local loop source mapping found {} items, expected {}",
                        edits.len(),
                        clause.items().len()
                    )));
                }
            }
            _ => {}
        }
    }
    Ok(())
}

fn inline_loop_phase_proof_edit(
    tokens: &[SourceToken],
    block: &Range<usize>,
    phase: &str,
) -> Result<Option<ProofSourceEdit>, ClickError> {
    let mut cursor = block.start + 1;
    while cursor < block.end {
        if tokens[cursor].text == phase {
            let by = cursor + 1;
            if tokens.get(by).map(|token| token.text.as_str()) != Some("by") {
                return Err(ClickError::new(format!(
                    "loop phase `{phase}` is missing its source `by` clause"
                )));
            }
            return Ok(Some(ProofSourceEdit::Explicit(proof_span(tokens, by)?)));
        }
        cursor += 1;
    }
    Ok(None)
}

fn collect_nested_proof_spans<'t>(
    tokens: &[SourceToken],
    edit: &ProofSourceEdit,
    proof: &'t SourceProof,
    spans: &mut Vec<FlatSourceTactic<'t>>,
) -> Result<(), ClickError> {
    match proof {
        SourceProof::Default => Ok(()),
        SourceProof::Tactic(smart) => {
            let ProofSourceEdit::Explicit(span) = edit else {
                return Err(ClickError::new(
                    "explicit nested loop tactic has no source `by` clause",
                ));
            };
            let by = tokens
                .iter()
                .position(|token| token.span.start == span.start && token.text == "by")
                .ok_or_else(|| ClickError::new("could not locate nested source `by` clause"))?;
            let tactic = tokens
                .get(by + 1)
                .ok_or_else(|| ClickError::new("nested source `by` clause has no tactic"))?;
            spans.push(FlatSourceTactic {
                span: tactic.span.clone(),
                tokens: by + 1..by + 2,
                tactic: FlatTactic::Phase(*smart),
            });
            Ok(())
        }
        SourceProof::Script(tactics) => {
            let ProofSourceEdit::Explicit(span) = edit else {
                return Err(ClickError::new(
                    "explicit nested loop proof has no source `by` clause",
                ));
            };
            let by = tokens
                .iter()
                .position(|token| token.span.start == span.start && token.text == "by")
                .ok_or_else(|| ClickError::new("could not locate nested source `by` clause"))?;
            let open = by + 1;
            if tokens.get(open).map(|token| token.text.as_str()) != Some("{") {
                return Err(ClickError::new(
                    "nested loop proof script has no source block",
                ));
            }
            let close = matching_delimiter(tokens, open, "{", "}")?;
            collect_tactic_block_spans(tokens, open, close, tactics, spans)
        }
    }
}

fn direct_tactic_token_ranges(
    tokens: &[SourceToken],
    open: usize,
    close: usize,
) -> Result<Vec<Range<usize>>, ClickError> {
    let mut ranges = Vec::new();
    let mut start = open + 1;
    while start < close {
        let end = tactic_end_token(tokens, start, close)?;
        ranges.push(start..end + 1);
        start = end + 1;
    }
    Ok(ranges)
}

fn tactic_end_token(
    tokens: &[SourceToken],
    start: usize,
    close: usize,
) -> Result<usize, ClickError> {
    let mut cursor = start;
    let mut braces = 0_usize;
    let mut parentheses = 0_usize;
    let mut brackets = 0_usize;
    // Quantifiers in a `have` proposition own braces too. Only the block
    // after its top-level `by` can terminate the tactic.
    let mut have_body_started = tokens[start].text != "have";
    loop {
        if cursor >= close {
            return Err(ClickError::new(
                "unterminated tactic in selected source proof",
            ));
        }
        match tokens[cursor].text.as_str() {
            "by" if braces == 0 && parentheses == 0 && brackets == 0 => {
                have_body_started = true;
            }
            "{" => braces += 1,
            "}" => {
                braces = braces.checked_sub(1).ok_or_else(|| {
                    ClickError::new("unbalanced tactic block in selected source proof")
                })?;
                if have_body_started && braces == 0 && parentheses == 0 && brackets == 0 {
                    let continuation = tokens.get(cursor + 1).map(|token| token.text.as_str());
                    // A destructuring proof binding starts with a brace,
                    // but its `}` is followed by `=` rather than ending
                    // the tactic: `let { slot: child } = unfold(parent)`
                    // and `let { binder: instance } = step(...)`.
                    // `branch ensuring { ... } then { ... } else { ... }`
                    // and `if P ensuring { ... } then { ... } else { ... }`
                    // continue past their interface block.
                    if !(matches!(continuation, Some("else" | "by" | "="))
                        || (tokens[start].text == "both" && continuation == Some("and"))
                        || (tokens[start].text == "match" && continuation == Some("{"))
                        || (matches!(tokens[start].text.as_str(), "branch" | "if")
                            && continuation == Some("then")))
                    {
                        let terminator = if continuation == Some(";") {
                            cursor + 1
                        } else {
                            cursor
                        };
                        return Ok(terminator);
                    }
                }
            }
            "(" => parentheses += 1,
            ")" => {
                parentheses = parentheses.checked_sub(1).ok_or_else(|| {
                    ClickError::new("unbalanced tactic call in selected source proof")
                })?;
            }
            "[" => brackets += 1,
            "]" => {
                brackets = brackets.checked_sub(1).ok_or_else(|| {
                    ClickError::new("unbalanced tactic index in selected source proof")
                })?;
            }
            ";" if braces == 0 && parentheses == 0 && brackets == 0 => return Ok(cursor),
            _ => {}
        }
        cursor += 1;
    }
}

fn find_if_branch_blocks(
    tokens: &[SourceToken],
    tactic: &Range<usize>,
) -> Result<(usize, usize, usize, usize), ClickError> {
    let mut depth = 0_usize;
    let mut outer_open = None;
    let mut then_block = None;
    for cursor in tactic.start + 1..tactic.end {
        match tokens[cursor].text.as_str() {
            "{" => {
                if depth == 0 {
                    outer_open = Some(cursor);
                }
                depth += 1;
            }
            "}" => {
                depth = depth
                    .checked_sub(1)
                    .ok_or_else(|| ClickError::new("unbalanced `if` tactic source block"))?;
                if depth == 0
                    && tokens.get(cursor + 1).map(|token| token.text.as_str()) == Some("else")
                {
                    then_block = outer_open.map(|open| (open, cursor));
                }
            }
            _ => {}
        }
    }
    let (then_open, then_close) =
        then_block.ok_or_else(|| ClickError::new("could not locate proof `if` then branch"))?;
    let else_keyword = then_close + 1;
    let else_open = else_keyword + 1;
    if tokens.get(else_open).map(|token| token.text.as_str()) != Some("{") {
        return Err(ClickError::new("could not locate proof `if` else branch"));
    }
    let else_close = matching_delimiter(tokens, else_open, "{", "}")?;
    Ok((then_open, then_close, else_open, else_close))
}

/// The arm blocks of `cases { A => { ... } B => { ... } ... }`, in order.
/// An arm's assumption may hold braces of its own (a quantifier); only a
/// block after `=>` is an arm.
fn find_cases_arm_blocks(
    tokens: &[SourceToken],
    tactic: &Range<usize>,
) -> Result<Vec<(usize, usize)>, ClickError> {
    let outer_open = tactic.start + 1;
    if tokens.get(outer_open).map(|token| token.text.as_str()) != Some("{") {
        return Err(ClickError::new("source `cases` tactic has no arms"));
    }
    let outer_close = matching_delimiter(tokens, outer_open, "{", "}")?;
    let mut arms = Vec::new();
    let mut cursor = outer_open + 1;
    while cursor < outer_close {
        if tokens[cursor].text == "{" {
            let close = matching_delimiter(tokens, cursor, "{", "}")?;
            if cursor >= 2 && tokens[cursor - 2].text == "=" && tokens[cursor - 1].text == ">" {
                arms.push((cursor, close));
            }
            cursor = close + 1;
        } else {
            cursor += 1;
        }
    }
    if arms.len() < 2 {
        return Err(ClickError::new(
            "could not locate the arms of a source `cases`",
        ));
    }
    Ok(arms)
}

fn find_branch_blocks(
    tokens: &[SourceToken],
    tactic: &Range<usize>,
) -> Result<(usize, usize, usize, usize), ClickError> {
    find_named_arm_blocks(tokens, tactic, "then", "else", "branch")
}

/// The `returned` and `threw` arm blocks of
/// `outcomes { returned => { ... } threw => { ... } }`, in that order
/// whichever order they are written in.
fn find_outcomes_arm_blocks(
    tokens: &[SourceToken],
    tactic: &Range<usize>,
) -> Result<(usize, usize, usize, usize), ClickError> {
    let outer_open = tactic.start + 1;
    if tokens.get(outer_open).map(|token| token.text.as_str()) != Some("{") {
        return Err(ClickError::new("source `outcomes` tactic has no arms"));
    }
    let outer_close = matching_delimiter(tokens, outer_open, "{", "}")?;
    let mut returned = None;
    let mut threw = None;
    let mut cursor = outer_open + 1;
    while cursor < outer_close {
        if tokens[cursor].text == "{" {
            let close = matching_delimiter(tokens, cursor, "{", "}")?;
            if cursor >= 3 && tokens[cursor - 2].text == "=" && tokens[cursor - 1].text == ">" {
                match tokens[cursor - 3].text.as_str() {
                    "returned" => returned = Some((cursor, close)),
                    "threw" => threw = Some((cursor, close)),
                    _ => {}
                }
            }
            cursor = close + 1;
        } else {
            cursor += 1;
        }
    }
    match (returned, threw) {
        (Some((returned_open, returned_close)), Some((threw_open, threw_close))) => {
            Ok((returned_open, returned_close, threw_open, threw_close))
        }
        _ => Err(ClickError::new(
            "could not locate the arms of a source `outcomes`",
        )),
    }
}

fn find_named_arm_blocks(
    tokens: &[SourceToken],
    tactic: &Range<usize>,
    first: &str,
    second: &str,
    kind: &str,
) -> Result<(usize, usize, usize, usize), ClickError> {
    // The arms follow the tactic's keyword at its own top level:
    // `branch [ensuring { ... }] then { ... } else { ... }` and
    // `outcomes returned { ... } threw { ... }`.
    let find_named_block = |name: &str| -> Result<(usize, usize), ClickError> {
        let mut depth = 0_usize;
        for keyword in tactic.start + 1..tactic.end {
            match tokens[keyword].text.as_str() {
                "{" => depth += 1,
                "}" => depth = depth.saturating_sub(1),
                text if depth == 0
                    && text == name
                    && tokens.get(keyword + 1).map(|token| token.text.as_str()) == Some("{") =>
                {
                    let open = keyword + 1;
                    return Ok((open, matching_delimiter(tokens, open, "{", "}")?));
                }
                _ => {}
            }
        }
        Err(ClickError::new(format!(
            "could not locate `{kind}` {name} arm"
        )))
    };
    let (then_open, then_close) = find_named_block(first)?;
    let (else_open, else_close) = find_named_block(second)?;
    Ok((then_open, then_close, else_open, else_close))
}

fn find_structural_induction_arm_blocks(
    tokens: &[SourceToken],
    tactic: &Range<usize>,
) -> Result<Vec<(usize, usize)>, ClickError> {
    // The scrutinee may itself contain match/let blocks. The proof arms are
    // the final block, not necessarily the first opening brace in the tactic.
    let outer_close = (tactic.start + 1..tactic.end)
        .rfind(|index| tokens[*index].text == "}")
        .ok_or_else(|| ClickError::new("source constructor tactic has no body"))?;
    let mut depth = 1_usize;
    let outer_open = (tactic.start + 1..outer_close)
        .rev()
        .find(|index| {
            match tokens[*index].text.as_str() {
                "}" => depth += 1,
                "{" => depth -= 1,
                _ => {}
            }
            depth == 0
        })
        .ok_or_else(|| ClickError::new("unbalanced constructor tactic body"))?;
    let mut blocks = Vec::new();
    let mut cursor = outer_open + 1;
    while cursor < outer_close {
        if tokens[cursor].text == "{" {
            let close = matching_delimiter(tokens, cursor, "{", "}")?;
            blocks.push((cursor, close));
            cursor = close + 1;
        } else {
            cursor += 1;
        }
    }
    Ok(blocks)
}

#[cfg(test)]
fn find_tactic_span(
    tokens: &[SourceToken],
    proof_span: &Range<usize>,
    wanted: usize,
) -> Result<Range<usize>, ClickError> {
    let by = tokens
        .binary_search_by_key(&proof_span.start, |token| token.span.start)
        .ok()
        .filter(|index| tokens[*index].text == "by")
        .ok_or_else(|| ClickError::new("could not locate selected source proof"))?;
    let open = by + 1;
    if tokens.get(open).map(|token| token.text.as_str()) != Some("{") {
        return Err(ClickError::new(
            "individual tactic expansion requires an explicit `by { ... }` proof",
        ));
    }
    let close = matching_delimiter(tokens, open, "{", "}")?;
    if let Some(range) = direct_tactic_token_ranges(tokens, open, close)?.get(wanted) {
        return Ok(tokens[range.start].span.start..tokens[range.end - 1].span.end);
    }
    Err(ClickError::new(format!(
        "selected source proof has no tactic {wanted}"
    )))
}

fn matching_delimiter(
    tokens: &[SourceToken],
    open: usize,
    opening: &str,
    closing: &str,
) -> Result<usize, ClickError> {
    let mut depth = 0;
    for (index, token) in tokens.iter().enumerate().skip(open) {
        if token.text == opening {
            depth += 1;
        } else if token.text == closing {
            depth -= 1;
            if depth == 0 {
                return Ok(index);
            }
        }
    }
    Err(ClickError::new(format!(
        "unterminated `{opening}` while locating proof source"
    )))
}

fn indent_replacement(source: &str, start: usize, replacement: &str) -> String {
    let line_start = source[..start].rfind('\n').map_or(0, |index| index + 1);
    let line_prefix = &source[line_start..start];
    let indent_length = line_prefix.len() - line_prefix.trim_start().len();
    let indent = &line_prefix[..indent_length];
    replacement.replace('\n', &format!("\n{indent}"))
}

#[cfg(test)]
mod tests;
