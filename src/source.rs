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

/// Maps every character index of `source` to its one-based line and column.
pub(crate) fn character_positions(source: &str) -> Vec<SourcePosition> {
    character_positions_in(source, None)
}

/// Maps every character index of `source` to its one-based line and column,
/// with each position's origin in `container` when the source has one.
pub(crate) fn character_positions_in(
    source: &str,
    container: Option<&SourceContainer>,
) -> Vec<SourcePosition> {
    let mut positions = Vec::with_capacity(source.chars().count());
    let mut line = 1;
    let mut column = 1;
    let mut origin = container.map(|container| Arc::new(container.origin(line)));
    for ch in source.chars() {
        positions.push(SourcePosition {
            line,
            column,
            origin: origin.clone(),
        });
        if ch == '\n' {
            line += 1;
            column = 1;
            origin = container.map(|container| Arc::new(container.origin(line)));
        } else {
            column += 1;
        }
    }
    positions
}
