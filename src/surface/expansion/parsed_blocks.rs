//! The proof blocks and proof clauses a parse recorded, located in a
//! source's tokens. Every brace expansion pairs, every arm it finds and every
//! proof clause it edits is one of these records; nothing here counts braces
//! or scans for a `by`.
use super::*;
use crate::surface::parser::{ProofClauseSpan, SourceSpans};
use std::collections::HashMap;

pub(super) struct ParsedBlock {
    pub(super) close: usize,
    /// The token ranges of the block's tactics. They are contiguous, so each
    /// runs from its recorded start to the next one's, or to the `}`.
    pub(super) tactics: Vec<Range<usize>>,
}

/// The proof blocks of one parse, keyed by the token index of their `{`,
/// and its proof clauses.
#[derive(Default)]
pub(super) struct ParsedBlocks {
    blocks: BTreeMap<usize, ParsedBlock>,
    /// The end of each block's tactics, by the tactic's first token.
    tactic_ends: HashMap<usize, usize>,
    pub(super) clauses: ProofClauses,
}

/// One recorded proof clause, located in a source's tokens.
#[derive(Clone, Copy, Debug)]
pub(super) struct ProofClause {
    /// The `by`, or the `;` of a clause left to its default proof.
    pub(super) start: usize,
    /// The `}` or `;` that ends the clause.
    pub(super) last: usize,
}

impl ProofClause {
    pub(super) fn is_default(&self, tokens: &[SourceToken]) -> bool {
        tokens[self.start].text == ";"
    }

    /// The clause's source bytes, `by` through its last token.
    pub(super) fn span(&self, tokens: &[SourceToken]) -> Range<usize> {
        tokens[self.start].span.start..tokens[self.last].span.end
    }
}

/// The proof clauses of one parse, keyed by the token index of their start,
/// and those a reader gave an owner keyword, keyed by that keyword's token.
#[derive(Default)]
pub(super) struct ProofClauses {
    by_start: BTreeMap<usize, ProofClause>,
    by_owner: BTreeMap<usize, ProofClause>,
}

impl ProofClauses {
    pub(super) fn new(tokens: &[SourceToken], spans: &[ProofClauseSpan]) -> Self {
        let located = DeclarationSources::new(tokens);
        let mut clauses = Self::default();
        for span in spans {
            crate::instrumentation::record_deterministic_work(1);
            let (Some(start), Some(last)) = (
                located.token_at(&span.start, None),
                located.token_at(&span.last, None),
            ) else {
                continue;
            };
            let clause = ProofClause { start, last };
            clauses.by_start.insert(start, clause);
            if let Some(owner) = span
                .owner
                .as_ref()
                .and_then(|owner| located.token_at(owner, None))
            {
                clauses.by_owner.insert(owner, clause);
            }
        }
        clauses
    }

    /// The clause starting at token `start`.
    pub(super) fn at(&self, start: usize) -> Result<ProofClause, ClickError> {
        self.by_start
            .get(&start)
            .copied()
            .ok_or_else(|| ClickError::new("the parser read no proof clause here"))
    }

    /// The first clause after token `after` and before `limit`: the proof of
    /// the clause or item whose first token is `after`, since nothing a
    /// claim states holds a proof of its own.
    pub(super) fn after(&self, after: usize, limit: usize) -> Result<ProofClause, ClickError> {
        self.by_start
            .range(after + 1..limit)
            .next()
            .map(|(_, clause)| *clause)
            .ok_or_else(|| ClickError::new("could not locate source proof terminator"))
    }

    /// The clauses owned by a keyword in `range`, with the owner's token.
    pub(super) fn owned_in(
        &self,
        range: Range<usize>,
    ) -> impl Iterator<Item = (usize, ProofClause)> + '_ {
        self.by_owner
            .range(range)
            .map(|(&owner, &clause)| (owner, clause))
    }
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
        let clauses = ProofClauses::new(tokens, &spans.proof_clauses);
        let tactic_ends = blocks
            .values()
            .flat_map(|block| block.tactics.iter().map(|range| (range.start, range.end)))
            .collect();
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
        Self {
            blocks,
            tactic_ends,
            clauses,
        }
    }

    pub(super) fn iter(&self) -> impl Iterator<Item = (usize, &ParsedBlock)> {
        self.blocks.iter().map(|(&open, block)| (open, block))
    }

    pub(super) fn block(&self, open: usize) -> Result<&ParsedBlock, ClickError> {
        self.blocks
            .get(&open)
            .ok_or_else(|| ClickError::new("the parser read no proof block at this brace"))
    }

    /// The token range of the tactic that starts at token `start`.
    pub(super) fn tactic(&self, start: usize) -> Option<Range<usize>> {
        self.tactic_ends.get(&start).map(|&end| start..end)
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
