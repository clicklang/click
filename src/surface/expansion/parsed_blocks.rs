//! The proof blocks a parse recorded, located in a source's tokens. Every
//! brace expansion pairs and every arm it finds is one of these records;
//! nothing here counts braces.
use super::*;
use crate::surface::parser::SourceSpans;

pub(super) struct ParsedBlock {
    pub(super) close: usize,
    /// The token ranges of the block's tactics. They are contiguous, so each
    /// runs from its recorded start to the next one's, or to the `}`.
    pub(super) tactics: Vec<Range<usize>>,
}

/// The proof blocks of one parse, keyed by the token index of their `{`.
#[derive(Default)]
pub(super) struct ParsedBlocks {
    blocks: BTreeMap<usize, ParsedBlock>,
}

impl ParsedBlocks {
    /// Locates each block `spans` recorded in `tokens`. A recorded block
    /// whose braces are not in `tokens`, such as one in a library contract
    /// appended after the entry text, is left out. The implicit block of
    /// `by T();` is the zero-width brace pair `with_implicit_proof_blocks`
    /// inserted around its one tactic.
    pub(super) fn new(tokens: &[SourceToken], spans: &SourceSpans) -> Self {
        let located = DeclarationSources::new(tokens);
        let mut blocks = BTreeMap::new();
        for block in &spans.proof_blocks {
            crate::instrumentation::record_deterministic_work(1);
            let (Some(open), Some(close)) = (
                located.token_at(&block.open, Some("{")),
                located.token_at(&block.close, Some("}")),
            ) else {
                continue;
            };
            let Some(starts) = block
                .tactics
                .iter()
                .map(|start| located.token_at(start, None))
                .collect::<Option<Vec<_>>>()
            else {
                continue;
            };
            let tactics = starts
                .iter()
                .zip(starts.iter().skip(1).copied().chain([close]))
                .map(|(&start, end)| start..end)
                .collect();
            blocks.insert(open, ParsedBlock { close, tactics });
        }
        let mut implicit = Vec::new();
        for (index, token) in tokens.iter().enumerate() {
            if !token.span.is_empty() {
                continue;
            }
            crate::instrumentation::record_deterministic_work(1);
            if token.text == "{" {
                implicit.push(index);
            } else if let Some(open) = implicit.pop() {
                blocks.insert(
                    open,
                    ParsedBlock {
                        close: index,
                        tactics: (open + 1 < index)
                            .then_some(open + 1..index)
                            .into_iter()
                            .collect(),
                    },
                );
            }
        }
        Self { blocks }
    }

    pub(super) fn iter(&self) -> impl Iterator<Item = (usize, &ParsedBlock)> {
        self.blocks.iter().map(|(&open, block)| (open, block))
    }

    pub(super) fn block(&self, open: usize) -> Result<&ParsedBlock, ClickError> {
        self.blocks
            .get(&open)
            .ok_or_else(|| ClickError::new("the parser read no proof block at this brace"))
    }

    /// The proof blocks directly inside the tactic `range`, in source order:
    /// a structured tactic's arms, or the body of `have ... by` and `open`.
    /// A block nested in one of them is not one of them.
    pub(super) fn child_blocks(&self, range: &Range<usize>) -> Vec<(usize, usize)> {
        let mut children: Vec<(usize, usize)> = Vec::new();
        for (&open, block) in self.blocks.range(range.start + 1..range.end) {
            crate::instrumentation::record_deterministic_work(1);
            if children.last().is_some_and(|&(_, close)| open < close) {
                continue;
            }
            children.push((open, block.close));
        }
        children
    }

    /// The two arm blocks of a proof `if`, `branch` or `both`.
    pub(super) fn two_arms(
        &self,
        range: &Range<usize>,
        kind: &str,
    ) -> Result<[(usize, usize); 2], ClickError> {
        <[_; 2]>::try_from(self.child_blocks(range)).map_err(|_| {
            ClickError::new(format!(
                "could not locate the two arms of a source `{kind}`"
            ))
        })
    }

    /// The arm blocks of `cases { A => { ... } B => { ... } ... }`, in order.
    pub(super) fn cases_arms(
        &self,
        range: &Range<usize>,
    ) -> Result<Vec<(usize, usize)>, ClickError> {
        let arms = self.child_blocks(range);
        if arms.len() < 2 {
            return Err(ClickError::new(
                "could not locate the arms of a source `cases`",
            ));
        }
        Ok(arms)
    }

    /// The `returned` and `threw` arm blocks of
    /// `outcomes { returned => { ... } threw => { ... } }`, in that order
    /// whichever order they are written in.
    pub(super) fn outcomes_arms(
        &self,
        tokens: &[SourceToken],
        range: &Range<usize>,
    ) -> Result<[(usize, usize); 2], ClickError> {
        let mut returned = None;
        let mut threw = None;
        for (open, close) in self.child_blocks(range) {
            match open.checked_sub(2).map(|label| tokens[label].text.as_str()) {
                Some("returned") => returned = Some((open, close)),
                Some("threw") => threw = Some((open, close)),
                _ => {}
            }
        }
        match (returned, threw) {
            (Some(returned), Some(threw)) => Ok([returned, threw]),
            _ => Err(ClickError::new(
                "could not locate the arms of a source `outcomes`",
            )),
        }
    }

    /// The single proof block of an `open` or a `have ... by` tactic.
    pub(super) fn body_block(
        &self,
        range: &Range<usize>,
        kind: &str,
    ) -> Result<(usize, usize), ClickError> {
        self.child_blocks(range)
            .first()
            .copied()
            .ok_or_else(|| ClickError::new(format!("source `{kind}` tactic has no body")))
    }
}
