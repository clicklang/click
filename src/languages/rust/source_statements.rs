//! A Rust function's statements as written, for `statement(i)` paths.
//!
//! `statement(i)` is the `i`th statement of the function body's block, its
//! tail expression included. `S.statement(j)` is the `j`th statement `S`
//! contains, counted across every block inside `S` in source order: an
//! `if`'s arms share one count, as in C, and so do a `match`'s arms, an arm
//! whose body is no block counting as one statement. A closure's body and a
//! nested item are not the function's statements.
//!
//! Each statement records the source range it covers, so a MIR statement is
//! the innermost statement whose range holds where it starts.

use syn::spanned::Spanned;
use syn::visit::Visit;

/// A position in a source file: its line from 1 and its column from 0, in
/// characters, as `proc_macro2` counts them.
pub(crate) type Position = (usize, usize);

/// One statement as written: its path, `statement(i).statement(j)...`, and
/// the range of source it covers.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct SourceStatement {
    pub(crate) path: Vec<u32>,
    pub(crate) start: Position,
    pub(crate) end: Position,
}

/// `source` parsed, once for all its functions; `None` when it does not
/// parse.
pub(crate) fn parse(source: &str) -> Option<syn::File> {
    syn::parse_file(source).ok()
}

/// The statements of the function in `file` whose item covers `at`, in
/// preorder: a statement before the statements it contains. `None` when no
/// function body covers `at`.
pub(crate) fn function_statements(file: &syn::File, at: Position) -> Option<Vec<SourceStatement>> {
    let mut finder = BodyFinder { at, body: None };
    finder.visit_file(file);
    let body = finder.body??;
    let mut statements = Vec::new();
    for (index, statement) in body.stmts.iter().enumerate() {
        record(
            Item::Statement(statement),
            vec![index as u32],
            &mut statements,
        );
    }
    Some(statements)
}

/// The innermost statement of `statements` whose range holds `at`.
pub(crate) fn innermost(statements: &[SourceStatement], at: Position) -> Option<usize> {
    statements
        .iter()
        .enumerate()
        .filter(|(_, statement)| statement.start <= at && at < statement.end)
        .max_by_key(|(_, statement)| statement.path.len())
        .map(|(index, _)| index)
}

/// The body of the innermost function item or closure whose range holds
/// `at`: `Some(None)` for a closure whose body is no block, which has no
/// statements of its own.
struct BodyFinder<'ast> {
    at: Position,
    body: Option<Option<&'ast syn::Block>>,
}

impl BodyFinder<'_> {
    fn covers(&self, spanned: &impl Spanned) -> bool {
        let span = spanned.span();
        let (start, end) = (span.start(), span.end());
        (start.line, start.column) <= self.at && self.at < (end.line, end.column)
    }
}

impl<'ast> Visit<'ast> for BodyFinder<'ast> {
    fn visit_item_fn(&mut self, item: &'ast syn::ItemFn) {
        if self.covers(item) {
            self.body = Some(Some(&item.block));
        }
        syn::visit::visit_item_fn(self, item);
    }

    fn visit_impl_item_fn(&mut self, item: &'ast syn::ImplItemFn) {
        if self.covers(item) {
            self.body = Some(Some(&item.block));
        }
        syn::visit::visit_impl_item_fn(self, item);
    }

    fn visit_trait_item_fn(&mut self, item: &'ast syn::TraitItemFn) {
        if let Some(block) = &item.default
            && self.covers(item)
        {
            self.body = Some(Some(block));
        }
        syn::visit::visit_trait_item_fn(self, item);
    }

    /// A closure is a function of its own, inside the one that writes it.
    fn visit_expr_closure(&mut self, closure: &'ast syn::ExprClosure) {
        if self.covers(closure) {
            self.body = Some(match closure.body.as_ref() {
                syn::Expr::Block(block) => Some(&block.block),
                _ => None,
            });
        }
        syn::visit::visit_expr_closure(self, closure);
    }
}

/// A statement as written: a block's statement, or a `match` arm's body that
/// is no block.
#[derive(Clone, Copy)]
enum Item<'ast> {
    Statement(&'ast syn::Stmt),
    ArmBody(&'ast syn::Expr),
}

impl Item<'_> {
    fn range(self) -> (Position, Position) {
        let span = match self {
            Item::Statement(statement) => statement.span(),
            Item::ArmBody(expression) => expression.span(),
        };
        let (start, end) = (span.start(), span.end());
        ((start.line, start.column), (end.line, end.column))
    }
}

/// Records `item` at `path`, then the statements it contains.
fn record(item: Item<'_>, path: Vec<u32>, statements: &mut Vec<SourceStatement>) {
    let (start, end) = item.range();
    statements.push(SourceStatement {
        path: path.clone(),
        start,
        end,
    });
    let mut children = Children::default();
    match item {
        Item::Statement(statement) => children.visit_stmt(statement),
        Item::ArmBody(expression) => children.visit_expr(expression),
    }
    for (index, child) in children.items.into_iter().enumerate() {
        let mut child_path = path.clone();
        child_path.push(index as u32);
        record(child, child_path, statements);
    }
}

/// The statements one statement contains, in source order: those of every
/// block inside it, and each `match` arm body that is no block, without
/// descending into them, into closures or into nested items.
#[derive(Default)]
struct Children<'ast> {
    items: Vec<Item<'ast>>,
}

impl<'ast> Visit<'ast> for Children<'ast> {
    fn visit_block(&mut self, block: &'ast syn::Block) {
        self.items.extend(block.stmts.iter().map(Item::Statement));
    }

    fn visit_arm(&mut self, arm: &'ast syn::Arm) {
        match arm.body.as_ref() {
            syn::Expr::Block(block) => self.visit_block(&block.block),
            body => self.items.push(Item::ArmBody(body)),
        }
    }

    fn visit_expr_closure(&mut self, _: &'ast syn::ExprClosure) {}

    fn visit_item(&mut self, _: &'ast syn::Item) {}
}

#[cfg(test)]
mod tests {
    use super::*;

    fn paths(source: &str, at: Position) -> Vec<Vec<u32>> {
        function_statements(&parse(source).unwrap(), at)
            .unwrap()
            .into_iter()
            .map(|statement| statement.path)
            .collect()
    }

    #[test]
    fn statements_nest_through_blocks_and_share_a_count_across_arms() {
        let source = "pub fn f(x: u32) -> u32 {\n    let y = x + 1;\n    if y > 2 { g(y); h(y) } else { k(y) }\n    match y { 0 => 1, _ => { y } }\n}\n";
        assert_eq!(
            paths(source, (1, 4)),
            vec![
                vec![0],
                vec![1],
                vec![1, 0],
                vec![1, 1],
                vec![1, 2],
                vec![2],
                vec![2, 0],
                vec![2, 1],
            ]
        );
    }

    #[test]
    fn a_position_is_in_its_innermost_statement() {
        let source =
            "pub fn f(x: u32) -> u32 {\n    let y = x + 1;\n    if y > 2 { g(y) } else { 0 }\n}\n";
        let statements = function_statements(&parse(source).unwrap(), (1, 4)).unwrap();
        let at = |line, column| innermost(&statements, (line, column)).map(|i| &statements[i].path);
        assert_eq!(at(2, 12), Some(&vec![0]));
        assert_eq!(at(3, 7), Some(&vec![1]));
        assert_eq!(at(3, 15), Some(&vec![1, 0]));
        assert_eq!(at(1, 0), None);
    }

    #[test]
    fn closures_and_nested_items_are_not_the_function_s_statements() {
        let source = "pub fn f(x: u32) -> u32 {\n    let c = |a: u32| { a + 1 };\n    fn inner() {}\n    c(x)\n}\n";
        assert_eq!(paths(source, (1, 4)), vec![vec![0], vec![1], vec![2]]);
    }

    #[test]
    fn a_closure_is_a_function_of_its_own() {
        let source =
            "pub fn f(x: u32) -> u32 {\n    let c = |a: u32| { let b = a; b + 1 };\n    c(x)\n}\n";
        // A position inside the closure finds the closure's body.
        assert_eq!(paths(source, (2, 23)), vec![vec![0], vec![1]]);
        let bare = "pub fn f(x: u32) -> u32 {\n    let c = |a: u32| a + 1;\n    c(x)\n}\n";
        assert_eq!(function_statements(&parse(bare).unwrap(), (2, 21)), None);
    }

    #[test]
    fn a_method_body_is_found_inside_its_impl() {
        let source = "pub struct S;\nimpl S {\n    pub fn m(&self) -> u32 {\n        let a = 1;\n        a\n    }\n}\n";
        assert_eq!(paths(source, (3, 8)), vec![vec![0], vec![1]]);
    }
}
