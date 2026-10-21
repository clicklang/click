//! An immutable index of a container's proof blocks, shared by every
//! location query in one trace.
use super::parsed_blocks::ParsedBlocks;
use super::*;
use crate::surface::parser::SourceSpans;
use std::collections::HashMap;

thread_local! {
    static TOKENIZATION_WORK: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

pub(super) fn record_tokenization_work(bytes: usize) {
    TOKENIZATION_WORK.with(|work| work.set(work.get().saturating_add(bytes)));
}

#[derive(Default)]
struct IndexedTactic {
    end: usize,
    body: Option<(usize, usize)>,
    arms: Vec<(usize, usize)>,
    arm_ranges: Vec<(usize, usize, usize)>,
}

/// Source positions and proof-block structure for an immutable Click container.
/// Its blocks, tactics and arms are the ones the container's parse recorded.
/// Queries never tokenize or scan source.
pub struct ProofSourceIndex {
    tokens: Vec<SourceToken>,
    characters: Vec<usize>,
    lines: Vec<usize>,
    positions: Vec<SourcePosition>,
    by_offset: HashMap<usize, usize>,
    blocks: HashMap<usize, Vec<usize>>,
    tactics: HashMap<usize, IndexedTactic>,
    starts: Vec<Vec<usize>>,
    /// The resolved project whose entry module this indexes, when built from
    /// its verification parse.
    file: Option<ClickFile>,
}

impl ProofSourceIndex {
    /// Bytes tokenized on this thread, independently of verification budgets.
    /// Scaling regressions use differences to detect repeated whole-file scans.
    pub fn tokenization_work() -> usize {
        TOKENIZATION_WORK.with(std::cell::Cell::get)
    }

    /// The index of a project's entry module. Its proof blocks are the ones
    /// the module's verification parse read, so braced groups that only look
    /// like proofs, such as the arms of a resource's `match`, are not indexed.
    pub fn for_project(
        project: &ClickProject,
        inputs: &ProgramInputs<'_>,
    ) -> Result<Self, ClickError> {
        let sources = CSourceContext::of(inputs)?.with_click_project(project);
        let file = resolve_click_project_context(project, &sources)?;
        let source = project.entry_source().ok_or_else(|| {
            ClickError::new(format!("missing entry module `{}`", project.entry()))
        })?;
        let mut index = Self::build(source, file.source_spans())?;
        index.file = Some(file);
        Ok(index)
    }

    /// The index of a sidecar that is not part of a project, built from its
    /// verification parse as [`Self::for_project`] builds a project's.
    pub fn for_sidecar(click_source: &str, inputs: &ProgramInputs<'_>) -> Result<Self, ClickError> {
        let sources = CSourceContext::of(inputs)?;
        let file = parse_source_with_c_layouts_context(click_source, &sources)?;
        let mut index = Self::build(click_source, file.source_spans())?;
        index.file = Some(file);
        Ok(index)
    }

    /// The index of a Click source parsed on its own, without C layouts.
    #[cfg(test)]
    pub fn new(source: &str) -> Result<Self, ClickError> {
        let spans = parser::parsed_source_spans(source, parser::ProgramLayouts::default())?;
        Self::build(source, &spans)
    }

    pub(super) fn build(source: &str, spans: &SourceSpans) -> Result<Self, ClickError> {
        crate::instrumentation::record_deterministic_work(source.len());
        let tokens = proof_source_tokens(source, &spans.implicit_proofs)?;
        let parsed = ParsedBlocks::new(&tokens, spans);
        let mut characters = Vec::new();
        let mut lines = vec![0];
        for (offset, character) in source.char_indices() {
            characters.push(offset);
            if character == '\n' {
                lines.push(characters.len());
            }
        }
        characters.push(source.len());
        let mut result = Self {
            positions: Vec::with_capacity(tokens.len()),
            by_offset: HashMap::new(),
            starts: vec![Vec::new(); lines.len()],
            tokens,
            characters,
            lines,
            blocks: HashMap::new(),
            tactics: HashMap::new(),
            file: None,
        };
        for index in 0..result.tokens.len() {
            let offset = result.tokens[index].span.start;
            result.positions.push(result.position_at(offset));
            // Synthetic braces share the next written token's offset. A
            // diagnostic position names that written token, not the brace.
            if !result.tokens[index].span.is_empty() {
                result.by_offset.entry(offset).or_insert(index);
            }
        }
        for (open, block) in parsed.iter() {
            let mut children = Vec::new();
            for range in &block.tactics {
                crate::instrumentation::record_deterministic_work(1);
                let start = range.start;
                let tactic = result.describe_tactic(&parsed, range);
                let line = result.positions[start].line - 1;
                result.starts[line].push(result.tokens[start].span.start);
                result.tactics.insert(start, tactic);
                children.push(start);
            }
            result.blocks.insert(open, children);
        }
        for starts in &mut result.starts {
            starts.sort_unstable();
            starts.dedup();
        }
        Ok(result)
    }

    /// The tactic `range` of a parsed block: where it ends, and the proof
    /// blocks it holds as a body or as arms.
    fn describe_tactic(&self, parsed: &ParsedBlocks, range: &Range<usize>) -> IndexedTactic {
        let mut result = IndexedTactic {
            end: range.end - 1,
            ..Default::default()
        };
        match self.tokens[range.start].text.as_str() {
            "have" | "open" => result.body = parsed.child_blocks(range).first().copied(),
            kind @ ("if" | "branch" | "both") => {
                result.arms = parsed
                    .two_arms(range, kind)
                    .map(|arms| arms.to_vec())
                    .unwrap_or_default();
            }
            "cases" | "match" => result.arms = parsed.child_blocks(range),
            "outcomes" => {
                result.arms = parsed
                    .outcomes_arms(&self.tokens, range)
                    .map(|arms| arms.to_vec())
                    .unwrap_or_default();
            }
            _ => {}
        }
        result.arm_ranges = result
            .arms
            .iter()
            .enumerate()
            .map(|(index, &(open, close))| {
                (
                    self.tokens[open].span.start,
                    self.tokens[close].span.end,
                    index,
                )
            })
            .collect();
        result.arm_ranges.sort_unstable();
        result
    }

    fn position_at(&self, offset: usize) -> SourcePosition {
        let character = self.characters.partition_point(|&start| start < offset);
        let line = self.lines.partition_point(|&start| start <= character) - 1;
        SourcePosition::new(line + 1, character - self.lines[line] + 1)
    }

    fn offset(&self, position: &SourcePosition) -> Result<usize, ClickError> {
        let line = position
            .line
            .checked_sub(1)
            .and_then(|i| self.lines.get(i))
            .copied()
            .ok_or_else(|| ClickError::new("source line is missing"))?;
        let character = position
            .column
            .checked_sub(1)
            .and_then(|c| line.checked_add(c))
            .ok_or_else(|| ClickError::new("source column is missing"))?;
        if self
            .lines
            .get(position.line)
            .is_some_and(|&next| character >= next)
        {
            return Err(ClickError::new("source column is missing"));
        }
        self.characters
            .get(character)
            .copied()
            .ok_or_else(|| ClickError::new("source column is missing"))
    }

    fn token(&self, position: &SourcePosition) -> Result<usize, ClickError> {
        self.by_offset
            .get(&self.offset(position)?)
            .copied()
            .ok_or_else(|| ClickError::new("could not locate source tactic"))
    }

    /// Claim roots use the same token stream as nested paths and containment.
    pub fn project_tactic_positions(
        &self,
        project: &ClickProject,
        claim: &str,
    ) -> Result<Vec<SourcePosition>, ClickError> {
        let file = self
            .file
            .as_ref()
            .ok_or_else(|| ClickError::new("the source index has no resolved project"))?;
        c0_tactic_source_positions_with_tokens(
            file,
            project.entry_source().expect("resolved entry source"),
            claim,
            &self.tokens,
        )
    }

    pub fn nested_position(
        &self,
        outer: &SourcePosition,
        nested: &[usize],
    ) -> Result<SourcePosition, ClickError> {
        let mut current = self.token(outer)?;
        let mut indices = nested.iter().copied();
        while let Some(index) = indices.next() {
            crate::instrumentation::record_deterministic_work(1);
            let tactic = self
                .tactics
                .get(&current)
                .ok_or_else(|| ClickError::new("source tactic has no nested body"))?;
            let (open, child) = if matches!(
                self.tokens[current].text.as_str(),
                "if" | "cases" | "both" | "match"
            ) {
                let &(open, _) = tactic
                    .arms
                    .get(index)
                    .ok_or_else(|| ClickError::new("source arm is missing"))?;
                (
                    open,
                    indices
                        .next()
                        .ok_or_else(|| ClickError::new("source arm tactic is missing"))?,
                )
            } else {
                (
                    tactic
                        .body
                        .ok_or_else(|| ClickError::new("source tactic body is missing"))?
                        .0,
                    index,
                )
            };
            current = *self
                .blocks
                .get(&open)
                .and_then(|children| children.get(child))
                .ok_or_else(|| ClickError::new("nested source tactic is missing"))?;
        }
        Ok(self.positions[current].clone())
    }

    /// The written tactic and its indentation, without another source scan.
    pub fn tactic_text<'a>(
        &self,
        source: &'a str,
        position: &SourcePosition,
    ) -> Result<(&'a str, &'a str), ClickError> {
        let start = self.token(position)?;
        let end = self
            .tactics
            .get(&start)
            .ok_or_else(|| ClickError::new("the parser read no tactic at this position"))?
            .end;
        let offset = self.offset(position)?;
        let line_start = self.characters[self.lines[position.line - 1]];
        Ok((
            &source[self.tokens[start].span.start..self.tokens[end].span.end],
            &source[line_start..offset],
        ))
    }

    /// The written tactics that start on one-based `line`, in source order.
    pub fn starts_on_line(&self, line: usize) -> Vec<SourcePosition> {
        line.checked_sub(1)
            .and_then(|index| self.starts.get(index))
            .into_iter()
            .flatten()
            .map(|&offset| self.position_at(offset))
            .collect()
    }

    pub fn line_has_multiple_starts(&self, position: &SourcePosition) -> Result<bool, ClickError> {
        crate::instrumentation::record_deterministic_work(1);
        let selected = self.offset(position)?;
        let starts = &self.starts[position.line - 1];
        let present = starts.binary_search(&selected).is_ok();
        if starts.len() + usize::from(!present) <= 1 {
            return Ok(false);
        }
        if starts.first().copied() != Some(selected) {
            return Ok(true);
        }
        let Some(&start) = self.by_offset.get(&selected) else {
            return Ok(true);
        };
        let end = self.tactics.get(&start).map(|t| t.end);
        let Some(end) = end else {
            return Ok(true);
        };
        // The greatest start suffices: nested starts before this tactic's
        // end do not make the outer tactic's line ambiguous.
        Ok(starts
            .last()
            .is_some_and(|&offset| offset >= self.tokens[end].span.end))
    }

    pub fn arm_containing(
        &self,
        tactic: &SourcePosition,
        target: &SourcePosition,
    ) -> Result<Option<usize>, ClickError> {
        let start = self.token(tactic)?;
        let target = self.offset(target)?;
        let Some(tactic) = self.tactics.get(&start) else {
            return Ok(None);
        };
        let after = tactic.arm_ranges.partition_point(|&(open, _, _)| {
            crate::instrumentation::record_deterministic_work(1);
            open < target
        });
        if let Some(&(open, close, index)) =
            after.checked_sub(1).and_then(|i| tactic.arm_ranges.get(i))
            && open < target
            && target < close
        {
            return Ok(Some(index));
        }
        Ok(None)
    }

    pub fn have_body_contains(
        &self,
        tactic: &SourcePosition,
        target: &SourcePosition,
    ) -> Result<bool, ClickError> {
        crate::instrumentation::record_deterministic_work(1);
        let start = self.token(tactic)?;
        if self.tokens[start].text != "have" {
            return Ok(false);
        }
        let target = self.offset(target)?;
        let Some((open, close)) = self.tactics.get(&start).and_then(|t| t.body) else {
            return Ok(false);
        };
        // The implicit block of `by T();` opens with a zero-width brace at
        // `T` itself, so the tactic there is inside it.
        let open = &self.tokens[open].span;
        let after_open = if open.is_empty() {
            open.start <= target
        } else {
            open.start < target
        };
        Ok(after_open && target < self.tokens[close].span.end)
    }
}
