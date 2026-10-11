//! Source-file positions shared by Surface Click and program languages.

use std::{fmt, sync::Arc};

/// The compiler source location associated with an imported physical line.
///
/// Preprocessed output does not preserve a meaningful macro-expanded column,
/// so imports retain the original file and line only.
#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub struct SourceOrigin {
    pub filename: Arc<str>,
    pub line: usize,
}

/// The file that holds an extracted source, such as an mdtest holding a
/// fenced ```c block, and the lines of that file before the source's first
/// line. Diagnostics use it to name the line a person edits.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SourceContainer {
    pub filename: Arc<str>,
    pub line_offset: usize,
}

impl SourceContainer {
    pub fn new(filename: impl Into<Arc<str>>, line_offset: usize) -> Self {
        Self {
            filename: filename.into(),
            line_offset,
        }
    }

    /// The container location of one-based `line` of the extracted source.
    pub fn origin(&self, line: usize) -> SourceOrigin {
        SourceOrigin {
            filename: self.filename.clone(),
            line: line + self.line_offset,
        }
    }
}

/// A one-based line and column in a source file.
#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub struct SourcePosition {
    pub line: usize,
    pub column: usize,
    pub origin: Option<Arc<SourceOrigin>>,
}

impl SourcePosition {
    pub fn new(line: usize, column: usize) -> Self {
        Self {
            line,
            column,
            origin: None,
        }
    }

    pub(crate) fn with_origin(
        line: usize,
        column: usize,
        filename: Arc<str>,
        original_line: usize,
    ) -> Self {
        Self {
            line,
            column,
            origin: Some(Arc::new(SourceOrigin {
                filename,
                line: original_line,
            })),
        }
    }
}

impl fmt::Display for SourcePosition {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.origin {
            Some(origin) => write!(f, "{}:{}", origin.filename, origin.line),
            None => write!(f, "line {}, column {}", self.line, self.column),
        }
    }
}

/// The position of one character at a time, front to back, without a table
/// of every character's position: a scanner that asks only at token starts
/// pays for the characters it passes, not for a position object each.
pub(crate) struct SourcePositionCursor<'a> {
    container: Option<&'a SourceContainer>,
    line: usize,
    column: usize,
    origin: Option<Arc<SourceOrigin>>,
}

impl<'a> SourcePositionCursor<'a> {
    pub(crate) fn new(container: Option<&'a SourceContainer>) -> Self {
        Self {
            container,
            line: 1,
            column: 1,
            origin: container.map(|container| Arc::new(container.origin(1))),
        }
    }

    /// The position of the current character.
    pub(crate) fn position(&self) -> SourcePosition {
        SourcePosition {
            line: self.line,
            column: self.column,
            origin: self.origin.clone(),
        }
    }

    /// Moves past the current character, `ch`.
    pub(crate) fn advance(&mut self, ch: char) {
        if ch == '\n' {
            self.line += 1;
            self.column = 1;
            self.origin = self
                .container
                .map(|container| Arc::new(container.origin(self.line)));
        } else {
            self.column += 1;
        }
    }
}
