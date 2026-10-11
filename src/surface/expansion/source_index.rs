//! A shared lexical index for rendering all steps of a proof trace.
use super::*;
use std::cell::RefCell;
use std::collections::BTreeMap;
use std::rc::Rc;

type TacticRanges = Rc<Vec<Range<usize>>>;

/// Source tokens and tactic starts shared by all diagnostic lookups in a file.
/// Construct once per report; positions use character columns, including UTF-8.
pub struct SourceTacticIndex<'a> {
    source: &'a str,
    tokens: Vec<SourceToken>,
    positions: Vec<SourcePosition>,
    delimiters: Vec<Option<usize>>,
    lines: Vec<Vec<usize>>,
    starts: BTreeMap<usize, Vec<usize>>,
    ranges: RefCell<BTreeMap<usize, TacticRanges>>,
}

impl<'a> SourceTacticIndex<'a> {
    pub fn new(source: &'a str) -> Result<Self, ClickError> {
        crate::instrumentation::record_deterministic_work(source.len());
        let tokens = scan_source_tokens(source)?;
        let positions = positions_at_offsets(source, tokens.iter().map(|token| token.span.start));
        let mut delimiters = vec![None; tokens.len()];
        let mut stack = Vec::new();
        for (index, token) in tokens.iter().enumerate() {
            crate::instrumentation::record_deterministic_work(1);
            match token.text.as_str() {
                "(" | "[" | "{" => stack.push(index),
                ")" | "]" | "}" => {
                    if let Some(&open) = stack.last()
                        && matches!(
                            (tokens[open].text.as_str(), token.text.as_str()),
                            ("(", ")") | ("[", "]") | ("{", "}")
                        )
                    {
                        stack.pop();
                        delimiters[open] = Some(index);
                    }
                }
                _ => {}
            }
        }
        let mut lines = vec![Vec::new()];
        for (offset, character) in source.char_indices() {
            lines.last_mut().unwrap().push(offset);
            if character == '\n' {
                lines.push(Vec::new());
            }
        }
        let mut result = Self {
            source,
            tokens,
            positions,
            delimiters,
            lines,
            starts: BTreeMap::new(),
            ranges: RefCell::new(BTreeMap::new()),
        };
        result.index_starts();
        Ok(result)
    }

    fn offset_at_position(&self, line: usize, column: usize) -> Result<usize, ClickError> {
        crate::instrumentation::record_deterministic_work(1);
        if line == 0 || column == 0 {
            return Err(ClickError::new("source lines and columns are one-based"));
        }
        let offsets = self
            .lines
            .get(line - 1)
            .ok_or_else(|| ClickError::new(format!("source has no line {line}")))?;
        if column == 1 {
            return Ok(offsets.first().copied().unwrap_or(self.source.len()));
        }
        offsets
            .get(column - 1)
            .copied()
            .filter(|&offset| self.source.as_bytes()[offset] != b'\n')
            .ok_or_else(|| ClickError::new(format!("line {line} has no column {column}")))
    }

    fn close_token(&self, open: usize) -> Result<usize, ClickError> {
        crate::instrumentation::record_deterministic_work(1);
        self.delimiters[open].ok_or_else(|| ClickError::new("unbalanced source delimiter"))
    }

    fn tactic_end_token(&self, start: usize, limit: usize) -> Result<usize, ClickError> {
        let tokens = &self.tokens;
        let kind = tokens[start].text.as_str();
        let mut have_body_started = kind != "have";
        let mut cursor = start;
        while cursor < limit {
            crate::instrumentation::record_deterministic_work(1);
            match tokens[cursor].text.as_str() {
                "by" => have_body_started = true,
                "(" | "[" => cursor = self.close_token(cursor)?,
                "{" => {
                    cursor = self.close_token(cursor)?;
                    if cursor >= limit {
                        break;
                    }
                    let continuation = tokens.get(cursor + 1).map(|token| token.text.as_str());
                    if have_body_started
                        && !(matches!(continuation, Some("else" | "by" | "="))
                            || (kind == "both" && continuation == Some("and"))
                            || (kind == "match" && continuation == Some("{"))
                            || (matches!(kind, "branch" | "if") && continuation == Some("then")))
                    {
                        return Ok(if continuation == Some(";") {
                            cursor + 1
                        } else {
                            cursor
                        });
                    }
                }
                ";" => return Ok(cursor),
                ")" | "]" | "}" => return Err(ClickError::new("unbalanced source tactic")),
                _ => {}
            }
            cursor += 1;
        }
        Err(ClickError::new(
            "unterminated tactic in selected source proof",
        ))
    }

    fn direct_tactic_token_ranges(
        &self,
        open: usize,
        close: usize,
    ) -> Result<TacticRanges, ClickError> {
        if let Some(ranges) = self.ranges.borrow().get(&open) {
            return Ok(Rc::clone(ranges));
        }
        let mut ranges = Vec::new();
        let mut start = open + 1;
        while start < close {
            let end = self.tactic_end_token(start, close)?;
            ranges.push(start..end + 1);
            start = end + 1;
        }
        let ranges = Rc::new(ranges);
        self.ranges.borrow_mut().insert(open, Rc::clone(&ranges));
        Ok(ranges)
    }

    fn find_if_branch_blocks(
        &self,
        tactic: &Range<usize>,
    ) -> Result<(usize, usize, usize, usize), ClickError> {
        let mut cursor = tactic.start + 1;
        let mut then_block = None;
        while cursor < tactic.end {
            crate::instrumentation::record_deterministic_work(1);
            if self.tokens[cursor].text == "{" {
                let close = self.close_token(cursor)?;
                if self
                    .tokens
                    .get(close + 1)
                    .is_some_and(|token| token.text == "else")
                {
                    then_block = Some((cursor, close));
                }
                cursor = close + 1;
            } else {
                cursor += 1;
            }
        }
        let (open, close) =
            then_block.ok_or_else(|| ClickError::new("could not locate proof `if` then branch"))?;
        let else_open = close + 2;
        if !self
            .tokens
            .get(else_open)
            .is_some_and(|token| token.text == "{")
        {
            return Err(ClickError::new("could not locate proof `if` else branch"));
        }
        Ok((open, close, else_open, self.close_token(else_open)?))
    }

    fn find_branch_blocks(
        &self,
        tactic: &Range<usize>,
    ) -> Result<(usize, usize, usize, usize), ClickError> {
        let mut arms = Vec::new();
        let mut cursor = tactic.start + 1;
        while cursor < tactic.end {
            crate::instrumentation::record_deterministic_work(1);
            if matches!(self.tokens[cursor].text.as_str(), "then" | "else")
                && self
                    .tokens
                    .get(cursor + 1)
                    .is_some_and(|token| token.text == "{")
            {
                let open = cursor + 1;
                arms.push((open, self.close_token(open)?));
            }
            if self.tokens[cursor].text == "{" {
                cursor = self.close_token(cursor)?;
            }
            cursor += 1;
        }
        match arms.as_slice() {
            &[(a, b), (c, d)] => Ok((a, b, c, d)),
            _ => Err(ClickError::new("could not locate branch arms")),
        }
    }

    pub fn tactic_starts_on_line(&self, line: usize) -> Vec<SourcePosition> {
        self.starts
            .get(&line)
            .into_iter()
            .flatten()
            .map(|&start| self.positions[start].clone())
            .collect()
    }

    fn index_starts(&mut self) {
        // The `then` block of a proof `if` and the arm blocks of `cases` follow
        // a condition, not a keyword; they are found from the tactic that owns
        // them, which the scan reaches first.
        let mut arm_blocks = std::collections::BTreeSet::new();
        let mut starts = std::collections::BTreeSet::new();
        let tokens = &self.tokens;
        for (open, token) in tokens.iter().enumerate() {
            crate::instrumentation::record_deterministic_work(1);
            if token.text != "{" {
                continue;
            }
            let preceding = open.checked_sub(1).and_then(|index| tokens.get(index));
            // A match arm's block follows `=>`, which the scanner emits as the
            // two punctuation tokens `=` and `>`.
            let arm_block =
                open >= 2 && tokens[open - 2].text == "=" && tokens[open - 1].text == ">";
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
            let Ok(close) = self.close_token(open) else {
                continue;
            };
            let Ok(ranges) = self.direct_tactic_token_ranges(open, close) else {
                continue;
            };
            for range in ranges.iter() {
                match tokens[range.start].text.as_str() {
                    "if" => {
                        if let Ok((then_open, ..)) = self.find_if_branch_blocks(range) {
                            arm_blocks.insert(then_open);
                        }
                    }
                    "cases" => {
                        if let Ok(arms) = self.find_cases_arm_blocks(range) {
                            arm_blocks.extend(arms.into_iter().map(|(open, _)| open));
                        }
                    }
                    _ => {}
                }
                starts.insert(range.start);
            }
        }
        for start in starts {
            self.starts
                .entry(self.positions[start].line)
                .or_default()
                .push(start);
        }
    }
    pub fn nested_tactic_source_position(
        &self,
        outer: &SourcePosition,
        nested_indices: &[usize],
    ) -> Result<SourcePosition, ClickError> {
        let tokens = &self.tokens;
        let offset = self.offset_at_position(outer.line, outer.column)?;
        let mut current = tokens
            .binary_search_by_key(&offset, |token| token.span.start)
            .ok()
            .ok_or_else(|| ClickError::new("could not locate enclosing source tactic"))?;
        let mut indices = nested_indices.iter().copied();
        while let Some(index) = indices.next() {
            let kind = tokens[current].text.as_str();
            if let Some(arms) = self.structured_tactic_arm_blocks(current)? {
                let (open, close) = *arms.get(index).ok_or_else(|| {
                    ClickError::new(format!("source `{kind}` has no arm {index}"))
                })?;
                let position = indices.next().ok_or_else(|| {
                    ClickError::new(format!(
                        "source path names arm {index} of `{kind}` without a tactic in it"
                    ))
                })?;
                let ranges = self.direct_tactic_token_ranges(open, close)?;
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
                crate::instrumentation::record_deterministic_work(1);
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
            let close = self.close_token(open)?;
            let ranges = self.direct_tactic_token_ranges(open, close)?;
            current = ranges
                .get(index)
                .ok_or_else(|| ClickError::new(format!("nested source tactic {index} is missing")))?
                .start;
        }
        Ok(self.positions[current].clone())
    }

    pub fn tactic_source_at_position(
        &self,
        position: &SourcePosition,
    ) -> Result<String, ClickError> {
        let tokens = &self.tokens;
        let offset = self.offset_at_position(position.line, position.column)?;
        let start = tokens
            .binary_search_by_key(&offset, |token| token.span.start)
            .ok()
            .ok_or_else(|| ClickError::new("could not locate source tactic"))?;
        let end = self.tactic_end_token(start, tokens.len())?;
        Ok(self.source[tokens[start].span.start..tokens[end].span.end].to_string())
    }

    pub fn tactic_arm_containing_position(
        &self,
        tactic_position: &SourcePosition,
        target_position: &SourcePosition,
    ) -> Result<Option<usize>, ClickError> {
        let tokens = &self.tokens;
        let tactic_offset =
            self.offset_at_position(tactic_position.line, tactic_position.column)?;
        let target_offset =
            self.offset_at_position(target_position.line, target_position.column)?;
        let start = tokens
            .binary_search_by_key(&tactic_offset, |token| token.span.start)
            .ok()
            .ok_or_else(|| ClickError::new("could not locate trace branch tactic"))?;
        let end = self.tactic_end_token(start, tokens.len())?;
        let range = start..end + 1;
        let pair = |(first_open, first_close, second_open, second_close)| {
            vec![(first_open, first_close), (second_open, second_close)]
        };
        let blocks = match tokens[start].text.as_str() {
            "branch" => pair(self.find_branch_blocks(&range)?),
            "if" => pair(self.find_if_branch_blocks(&range)?),
            "outcomes" => pair(self.find_outcomes_arm_blocks(&range)?),
            "cases" => self.find_cases_arm_blocks(&range)?,
            "both" => {
                let left_open = start + 1;
                if tokens.get(left_open).map(|token| token.text.as_str()) != Some("{") {
                    return Ok(None);
                }
                let left_close = self.close_token(left_open)?;
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
                    self.close_token(right_open)?,
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

    pub fn tactic_have_body_contains_position(
        &self,
        tactic_position: &SourcePosition,
        target_position: &SourcePosition,
    ) -> Result<bool, ClickError> {
        let tokens = &self.tokens;
        let tactic_offset =
            self.offset_at_position(tactic_position.line, tactic_position.column)?;
        let target_offset =
            self.offset_at_position(target_position.line, target_position.column)?;
        let start = tokens
            .binary_search_by_key(&tactic_offset, |token| token.span.start)
            .ok()
            .ok_or_else(|| ClickError::new("could not locate trace have tactic"))?;
        if tokens[start].text != "have" {
            return Ok(false);
        }
        let end = self.tactic_end_token(start, tokens.len())?;
        let Some(by) = (start..=end).find(|&index| tokens[index].text == "by") else {
            return Ok(false);
        };
        let Some(open) = (by + 1..=end).find(|&index| tokens[index].text == "{") else {
            return Ok(false);
        };
        let close = self.close_token(open)?;
        Ok(tokens[open].span.start < target_offset && target_offset < tokens[close].span.end)
    }

    pub fn tactic_line_has_multiple_starts(
        &self,
        position: &SourcePosition,
    ) -> Result<bool, ClickError> {
        let selected = self.offset_at_position(position.line, position.column)?;
        let Some(starts) = self.starts.get(&position.line) else {
            return Ok(false);
        };
        let present = starts
            .binary_search_by_key(&selected, |&start| self.tokens[start].span.start)
            .is_ok();
        if starts.len() + usize::from(!present) <= 1 {
            return Ok(false);
        }
        if self.tokens[starts[0]].span.start != selected {
            return Ok(true);
        }
        let Ok(start) = self
            .tokens
            .binary_search_by_key(&selected, |token| token.span.start)
        else {
            return Ok(true);
        };
        let end = self.tactic_end_token(start, self.tokens.len())?;
        Ok(starts
            .last()
            .is_some_and(|&start| self.tokens[start].span.start >= self.tokens[end].span.end))
    }

    fn structured_tactic_arm_blocks(
        &self,
        start: usize,
    ) -> Result<Option<Vec<(usize, usize)>>, ClickError> {
        let tokens = &self.tokens;
        let kind = tokens[start].text.as_str();
        if !matches!(kind, "if" | "cases" | "both") {
            return Ok(None);
        }
        let end = self.tactic_end_token(start, tokens.len())?;
        let range = start..end + 1;
        let (first_open, first_close, second_open, second_close) = match kind {
            "if" => self.find_if_branch_blocks(&range)?,
            "cases" => return self.find_cases_arm_blocks(&range).map(Some),
            _ => {
                let left_open = (start + 1..range.end)
                    .find(|&index| tokens[index].text == "{")
                    .ok_or_else(|| ClickError::new("source `both` tactic has no left arm"))?;
                let left_close = self.close_token(left_open)?;
                let right_open = left_close + 2;
                if tokens.get(left_close + 1).map(|token| token.text.as_str()) != Some("and")
                    || tokens.get(right_open).map(|token| token.text.as_str()) != Some("{")
                {
                    return Err(ClickError::new("source `both` tactic has no right arm"));
                }
                let right_close = self.close_token(right_open)?;
                (left_open, left_close, right_open, right_close)
            }
        };
        Ok(Some(vec![
            (first_open, first_close),
            (second_open, second_close),
        ]))
    }

    fn find_cases_arm_blocks(
        &self,
        tactic: &Range<usize>,
    ) -> Result<Vec<(usize, usize)>, ClickError> {
        let tokens = &self.tokens;
        let outer_open = tactic.start + 1;
        if tokens.get(outer_open).map(|token| token.text.as_str()) != Some("{") {
            return Err(ClickError::new("source `cases` tactic has no arms"));
        }
        let outer_close = self.close_token(outer_open)?;
        let mut arms = Vec::new();
        let mut cursor = outer_open + 1;
        while cursor < outer_close {
            crate::instrumentation::record_deterministic_work(1);
            if tokens[cursor].text == "{" {
                let close = self.close_token(cursor)?;
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

    fn find_outcomes_arm_blocks(
        &self,
        tactic: &Range<usize>,
    ) -> Result<(usize, usize, usize, usize), ClickError> {
        let tokens = &self.tokens;
        let outer_open = tactic.start + 1;
        if tokens.get(outer_open).map(|token| token.text.as_str()) != Some("{") {
            return Err(ClickError::new("source `outcomes` tactic has no arms"));
        }
        let outer_close = self.close_token(outer_open)?;
        let mut returned = None;
        let mut threw = None;
        let mut cursor = outer_open + 1;
        while cursor < outer_close {
            crate::instrumentation::record_deterministic_work(1);
            if tokens[cursor].text == "{" {
                let close = self.close_token(cursor)?;
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
}
