//! Linking several sources of one C++ unit into one program, for a sidecar
//! that verifies them together. Each source is exported and lowered on its
//! own; linking joins their lowered programs. A function one source only
//! declares, as an external interface, is bound to the source that defines
//! it, so a call into another translation unit is checked against the
//! contract the sidecar proves of its body. The one-definition rule is
//! checked, not assumed: two sources that define a function, or lay out a
//! record, differently are refused.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use super::PreparedCppImport;
use crate::languages::c::syntax::C0Function;
use crate::languages::{ExecutionCache, PreparedExecution};

/// Several sources of one C++ unit, verified together by one sidecar.
#[derive(Clone, Debug)]
pub struct LinkedCppProgram {
    inner: Arc<LinkedInner>,
}

#[derive(Debug)]
struct LinkedInner {
    sources: Vec<PreparedCppImport>,
    identity: String,
    execution: ExecutionCache,
}

impl LinkedCppProgram {
    /// The sources, each already named as the sidecar names it.
    pub(crate) fn new(sources: Vec<PreparedCppImport>) -> Self {
        let mut framed = Vec::new();
        for source in &sources {
            for part in [source.logical_source(), source.identity()] {
                framed.extend_from_slice(&(part.len() as u64).to_le_bytes());
                framed.extend_from_slice(part.as_bytes());
            }
        }
        Self {
            inner: Arc::new(LinkedInner {
                identity: crate::languages::inputs::hex_digest(&framed),
                sources,
                execution: ExecutionCache::default(),
            }),
        }
    }

    pub fn logical_sources(&self) -> Vec<&str> {
        self.inner
            .sources
            .iter()
            .map(PreparedCppImport::logical_source)
            .collect()
    }

    pub fn identity(&self) -> &str {
        &self.inner.identity
    }

    /// The source that defines `function`, or, when no linked source does,
    /// the first that declares it.
    pub(crate) fn source_of(&self, function: &str) -> Option<&str> {
        let mut declared = None;
        for source in &self.inner.sources {
            let Ok(execution) = source.prepared_execution() else {
                continue;
            };
            match execution
                .functions
                .iter()
                .find(|candidate| candidate.name() == function)
            {
                Some(found) if found.prelowered_kernel_function().is_some() => {
                    return Some(source.logical_source());
                }
                Some(_) if declared.is_none() => declared = Some(source.logical_source()),
                _ => {}
            }
        }
        declared
    }

    pub(crate) fn prepared_execution(&self) -> Result<Arc<PreparedExecution>, String> {
        self.inner.execution.get_or_lower(|| {
            let parts = self
                .inner
                .sources
                .iter()
                .map(|source| Ok((source.logical_source(), source.prepared_execution()?)))
                .collect::<Result<Vec<_>, String>>()?;
            Ok(Arc::new(link(
                &parts
                    .iter()
                    .map(|(source, execution)| (*source, execution.as_ref()))
                    .collect::<Vec<_>>(),
            )?))
        })
    }
}

/// Joins the lowered programs of `parts`, each named by its source. Work is
/// linear in the functions, layouts and contracts the parts hold.
fn link(parts: &[(&str, &PreparedExecution)]) -> Result<PreparedExecution, String> {
    let mut functions = Vec::<C0Function>::new();
    let mut by_name = BTreeMap::<String, (usize, &str)>::new();
    let mut layouts = BTreeMap::new();
    let mut layout_sources = BTreeMap::<&str, &str>::new();
    let mut record_spellings = BTreeMap::new();
    let mut spelling_sources = BTreeMap::<&str, &str>::new();
    let mut contract_blocks = BTreeSet::new();
    let mut library_contracts = String::new();
    let mut library_models = BTreeSet::new();
    for (source, execution) in parts {
        for function in &execution.functions {
            crate::instrumentation::record_deterministic_work(1);
            let name = function.name().to_string();
            let Some(&(index, first_source)) = by_name.get(&name) else {
                by_name.insert(name, (functions.len(), source));
                functions.push(function.clone());
                continue;
            };
            let kept = &functions[index];
            let display = crate::languages::display_source_names(&name).into_owned();
            match (
                kept.prelowered_kernel_function().is_some(),
                function.prelowered_kernel_function().is_some(),
            ) {
                // An inline definition in a shared header is the same body;
                // a read-only contract is required if any source's caller
                // observes it in an expression.
                (true, true) if kept.same_definition_apart_from_uses(function) => {
                    if function.requires_read_only_contract() {
                        functions[index] = functions[index].clone().with_read_only_contract(true);
                    }
                }
                (true, true) => {
                    return Err(format!(
                        "the C++ sources `{first_source}` and `{source}` define `{display}` differently"
                    ));
                }
                _ if !kept.declares_same_interface(function) => {
                    return Err(format!(
                        "the C++ sources `{first_source}` and `{source}` declare `{display}` differently"
                    ));
                }
                // A definition binds another source's declaration of it.
                (false, true) => {
                    let observed = kept.requires_read_only_contract();
                    functions[index] = function.clone();
                    if observed {
                        functions[index] = functions[index].clone().with_read_only_contract(true);
                    }
                    by_name.insert(name, (index, source));
                }
                (true, false) => {
                    if function.requires_read_only_contract() {
                        functions[index] = functions[index].clone().with_read_only_contract(true);
                    }
                }
                (false, false) => {
                    if function.requires_read_only_contract() {
                        functions[index] = functions[index].clone().with_read_only_contract(true);
                    }
                }
            }
        }
        for (name, layout) in &execution.layouts {
            crate::instrumentation::record_deterministic_work(1);
            if let Some(kept) = layouts.get(name) {
                if kept != layout {
                    let display = crate::languages::display_source_names(name).into_owned();
                    return Err(format!(
                        "the C++ sources `{}` and `{source}` lay out record `{display}` differently",
                        layout_sources[name.as_str()]
                    ));
                }
                continue;
            }
            layouts.insert(name.clone(), layout.clone());
            layout_sources.insert(name, source);
        }
        for (spelling, name) in &execution.record_spellings {
            crate::instrumentation::record_deterministic_work(1);
            if let Some(kept) = record_spellings.get(spelling) {
                if kept != name {
                    return Err(format!(
                        "the C++ sources `{}` and `{source}` name record `{spelling}` differently",
                        spelling_sources[spelling.as_str()]
                    ));
                }
                continue;
            }
            record_spellings.insert(spelling.clone(), name.clone());
            spelling_sources.insert(spelling, source);
        }
        // Each library contract is one `extern` declaration; two sources
        // reaching the same library function supply the same one.
        for block in contract_blocks_of(&execution.library_contracts) {
            crate::instrumentation::record_deterministic_work(1);
            if contract_blocks.insert(block.to_string()) {
                library_contracts.push_str(block);
            }
        }
        library_models.extend(execution.library_models.iter().cloned());
    }
    Ok(PreparedExecution {
        functions,
        layouts,
        library_contracts,
        library_models,
        record_spellings,
    })
}

/// The `extern` declarations of a library contract text, each with its own
/// lines: every declaration starts a line with `extern `.
fn contract_blocks_of(text: &str) -> Vec<&str> {
    let mut starts = text
        .match_indices("extern ")
        .map(|(index, _)| index)
        .filter(|index| *index == 0 || text.as_bytes()[index - 1] == b'\n')
        .collect::<Vec<_>>();
    if starts.first() != Some(&0) {
        starts.insert(0, 0);
    }
    starts
        .iter()
        .zip(starts.iter().skip(1).chain(std::iter::once(&text.len())))
        .map(|(start, end)| &text[*start..*end])
        .filter(|block| !block.trim().is_empty())
        .collect()
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/languages/cpp/link/tests.rs");
}
