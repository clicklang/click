//! The statements of a kernel `Seq`, as a persistent indexed sequence.
//!
//! A source block used to be a right-nested pair tree,
//! `Seq(s1, Seq(s2, ... Seq(s_{n-1}, s_n)))`, so the path from a block's root
//! to its k-th statement was k nodes long and replacing that statement rebuilt
//! all k. [`CStatementSequence`] holds the same statements in an
//! `imbl::Vector`: replacing one is logarithmic in the block's length and
//! shares every other statement, and taking the statements after the first
//! (a frontier advancing through the block) is constant.
//!
//! The sequence stands for exactly the tree it replaced. It holds at least
//! two statements and its last is never a `Seq`: a pair whose second half is
//! a sequence is that sequence with one more statement in front, as the tree
//! nested it. A statement before the last may be a `Seq`: that is a pair whose
//! first half is a pair, `Seq(Seq(a, b), c)`, kept as the tree kept it. So
//! every pair tree has one sequence and every sequence one pair tree, and
//! equality, hashing, ordering and `Debug` here are those of the tree, read
//! along the sequence.

use super::CStatement;
use std::cmp::Ordering;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::sync::Arc;

/// The statements a `CStatement::Seq` runs, in order. See the module
/// documentation for the pair tree it stands for.
#[derive(Clone)]
pub struct CStatementSequence {
    /// The statements from `start` on are this sequence's; those before it
    /// belong to a sequence this one is a suffix of, and are shared with it.
    items: imbl::Vector<Arc<CStatement>>,
    start: usize,
}

impl CStatementSequence {
    /// The sequence of the pair `Seq(first, second)`.
    pub fn pair(first: Arc<CStatement>, second: Arc<CStatement>) -> Self {
        if matches!(&*second, CStatement::Seq(_)) {
            // A sequence no one else holds is extended in place.
            let rest = match Arc::try_unwrap(second) {
                Ok(CStatement::Seq(rest)) => rest,
                Err(shared) => match &*shared {
                    CStatement::Seq(rest) => rest.clone(),
                    _ => unreachable!("checked to be a sequence"),
                },
                Ok(_) => unreachable!("checked to be a sequence"),
            };
            return rest.with_front(first);
        }
        let mut items = imbl::Vector::new();
        items.push_back(first);
        items.push_back(second);
        Self { items, start: 0 }
    }

    /// The sequence of `statements` in order, read as the pair tree a right
    /// fold of [`Self::pair`] over them builds: a `Seq` last is spliced in,
    /// any other `Seq` is kept as one statement. `None` for fewer than two
    /// statements, which no pair tree holds.
    pub fn from_statements(statements: impl IntoIterator<Item = Arc<CStatement>>) -> Option<Self> {
        let mut items: imbl::Vector<Arc<CStatement>> = statements.into_iter().collect();
        if items.len() < 2 {
            return None;
        }
        let last = items.pop_back().expect("two statements");
        match &*last {
            CStatement::Seq(rest) => items.append(rest.logical_items()),
            _ => items.push_back(last),
        }
        Some(Self { items, start: 0 })
    }

    fn with_front(self, first: Arc<CStatement>) -> Self {
        let Self { mut items, start } = self;
        if start > 0 {
            // The slot before a suffix is free in this copy: reuse it rather
            // than shift every statement.
            items.set(start - 1, first);
            return Self {
                items,
                start: start - 1,
            };
        }
        items.push_front(first);
        Self { items, start: 0 }
    }

    fn logical_items(&self) -> imbl::Vector<Arc<CStatement>> {
        if self.start == 0 {
            self.items.clone()
        } else {
            self.items.skip(self.start)
        }
    }

    /// How many statements the sequence runs; at least two.
    pub fn len(&self) -> usize {
        self.items.len() - self.start
    }

    /// Always false: a sequence holds at least two statements.
    pub fn is_empty(&self) -> bool {
        false
    }

    /// The statement at `index`, counting from the first.
    pub fn get(&self, index: usize) -> Option<&Arc<CStatement>> {
        if index >= self.len() {
            return None;
        }
        self.items.get(self.start + index)
    }

    /// The first statement: the pair's first half.
    pub fn first(&self) -> &Arc<CStatement> {
        &self.items[self.start]
    }

    /// The statements after the first, as one statement: the pair's second
    /// half. Constant: it shares this sequence's statements.
    pub fn rest(&self) -> Arc<CStatement> {
        if self.len() == 2 {
            return self.items[self.start + 1].clone();
        }
        Arc::new(CStatement::Seq(Self {
            items: self.items.clone(),
            start: self.start + 1,
        }))
    }

    /// The statements in execution order.
    pub fn iter(&self) -> impl DoubleEndedIterator<Item = &Arc<CStatement>> + ExactSizeIterator {
        self.items.focus().narrow(self.start..).into_iter()
    }

    /// The statements in execution order, to change in place. Each is
    /// copied first if another sequence shares it. A change must not make
    /// the last statement a `Seq`, which [`Self::with_statement`] would
    /// splice in instead.
    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut Arc<CStatement>> {
        self.items.focus_mut().narrow(self.start..).into_iter()
    }

    /// This sequence with the statement at `index` replaced by `statement`,
    /// sharing every other statement. Logarithmic in the length, except
    /// that a `Seq` put last is spliced in, as [`Self::pair`] would.
    pub fn with_statement(&self, index: usize, statement: Arc<CStatement>) -> Self {
        assert!(index < self.len(), "statement index within the sequence");
        if index + 1 == self.len()
            && let CStatement::Seq(rest) = &*statement
        {
            let mut items = self.items.clone();
            items.pop_back();
            items.append(rest.logical_items());
            return Self {
                items,
                start: self.start,
            };
        }
        Self {
            items: self.items.update(self.start + index, statement),
            start: self.start,
        }
    }

    /// Each statement mapped by `map`, in order, read as a right fold of
    /// [`Self::pair`] over the results.
    pub fn map(&self, mut map: impl FnMut(&Arc<CStatement>) -> Arc<CStatement>) -> Self {
        Self::from_statements(self.iter().map(&mut map)).expect("a sequence maps to a sequence")
    }

    /// [`Self::map`] with a fallible map, stopping at its first error.
    pub fn try_map<E>(
        &self,
        mut map: impl FnMut(&Arc<CStatement>) -> Result<Arc<CStatement>, E>,
    ) -> Result<Self, E> {
        let mut mapped = Vec::with_capacity(self.len());
        for statement in self.iter() {
            mapped.push(map(statement)?);
        }
        Ok(Self::from_statements(mapped).expect("a sequence maps to a sequence"))
    }
}

thread_local! {
    /// A `Seq`, to compare a statement's variant with: the pair tree's
    /// second half is a `Seq` exactly when more than one statement remains.
    static SEQ_STATEMENT: CStatement = CStatement::Seq(CStatementSequence::pair(
        Arc::new(CStatement::Skip),
        Arc::new(CStatement::Skip),
    ));
}

impl PartialEq for CStatementSequence {
    fn eq(&self, other: &Self) -> bool {
        if self.start == other.start && self.items.ptr_eq(&other.items) {
            return true;
        }
        self.len() == other.len()
            && self
                .iter()
                .zip(other.iter())
                .all(|(left, right)| left == right)
    }
}

impl Eq for CStatementSequence {}

impl Hash for CStatementSequence {
    /// The pair tree's derived hash: each statement, with the `Seq`
    /// discriminant of the nested pair before every statement but the first
    /// and the last.
    fn hash<H: Hasher>(&self, state: &mut H) {
        let last = self.len() - 1;
        SEQ_STATEMENT.with(|seq| {
            let seq = std::mem::discriminant(seq);
            for (index, statement) in self.iter().enumerate() {
                if index > 0 && index < last {
                    seq.hash(state);
                }
                statement.hash(state);
            }
        });
    }
}

impl Ord for CStatementSequence {
    /// The pair tree's derived order: first halves, then second halves, where
    /// a second half holding one statement is that statement and one holding
    /// more is a `Seq`.
    fn cmp(&self, other: &Self) -> Ordering {
        let (left_last, right_last) = (self.len() - 1, other.len() - 1);
        let mut index = 0;
        loop {
            match self.items[self.start + index].cmp(&other.items[other.start + index]) {
                Ordering::Equal => {}
                order => return order,
            }
            index += 1;
            let left = &self.items[self.start + index];
            let right = &other.items[other.start + index];
            match (index == left_last, index == right_last) {
                (true, true) => return left.cmp(right),
                (true, false) => return SEQ_STATEMENT.with(|seq| (**left).cmp(seq)),
                (false, true) => return SEQ_STATEMENT.with(|seq| seq.cmp(&**right)),
                (false, false) => {}
            }
        }
    }
}

impl PartialOrd for CStatementSequence {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl fmt::Debug for CStatementSequence {
    /// The pair tree's derived `Debug` inside its `Seq(...)`: `first, rest`,
    /// one field per line in the alternate form, as two fields print.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        struct Rest<'a>(&'a CStatementSequence, usize);
        impl fmt::Debug for Rest<'_> {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                let Rest(sequence, index) = *self;
                fmt::Debug::fmt(&**sequence.get(index).expect("statement"), f)?;
                f.write_str(if f.alternate() { ",\n" } else { ", " })?;
                if index + 2 == sequence.len() {
                    fmt::Debug::fmt(&**sequence.get(index + 1).expect("statement"), f)
                } else {
                    f.debug_tuple("Seq")
                        .field(&Rest(sequence, index + 1))
                        .finish()
                }
            }
        }
        fmt::Debug::fmt(&Rest(self, 0), f)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn leaf(index: i32) -> Arc<CStatement> {
        Arc::new(CStatement::Assign {
            name: format!("x{index}"),
            expression: crate::kernel::c_int32_literal(index as u32),
            source: Default::default(),
        })
    }

    fn pair(first: Arc<CStatement>, second: Arc<CStatement>) -> Arc<CStatement> {
        Arc::new(CStatement::seq(first, second))
    }

    /// Sequences of every shape over a few statements: right-nested blocks,
    /// left-nested pairs, and blocks whose middle statement is a block.
    fn shapes() -> Vec<Arc<CStatement>> {
        let (a, b, c, d) = (leaf(1), leaf(2), leaf(3), leaf(4));
        let skip = Arc::new(CStatement::Skip);
        vec![
            pair(a.clone(), b.clone()),
            pair(b.clone(), a.clone()),
            pair(a.clone(), skip.clone()),
            pair(skip.clone(), a.clone()),
            pair(a.clone(), pair(b.clone(), c.clone())),
            pair(pair(a.clone(), b.clone()), c.clone()),
            pair(a.clone(), pair(b.clone(), pair(c.clone(), d.clone()))),
            pair(a.clone(), pair(pair(b.clone(), c.clone()), d.clone())),
            pair(pair(a.clone(), b.clone()), pair(c.clone(), d.clone())),
            pair(a.clone(), pair(b.clone(), skip.clone())),
            pair(a.clone(), pair(skip, b.clone())),
            // A suffix of a longer sequence, sharing its storage.
            match &*pair(d, pair(a, pair(b, c))) {
                CStatement::Seq(statements) => statements.rest(),
                _ => unreachable!(),
            },
        ]
    }

    fn sequence(statement: &CStatement) -> &CStatementSequence {
        match statement {
            CStatement::Seq(statements) => statements,
            _ => panic!("a sequence"),
        }
    }

    /// The bytes a hash writes, to compare two hashes write for write.
    #[derive(Default)]
    struct Recorder(Vec<u8>);

    impl Hasher for Recorder {
        fn finish(&self) -> u64 {
            0
        }
        fn write(&mut self, bytes: &[u8]) {
            self.0.extend_from_slice(bytes);
        }
    }

    fn written(value: &impl Hash) -> Vec<u8> {
        let mut recorder = Recorder::default();
        value.hash(&mut recorder);
        recorder.0
    }

    /// Every trait reads a sequence as the pair `Seq(first, rest)`: the
    /// definitions the derived traits of the pair tree satisfy.
    #[test]
    fn a_sequence_compares_hashes_and_prints_as_its_pair_tree() {
        let shapes = shapes();
        for left in &shapes {
            let pairs = sequence(left);
            let (first, rest) = (pairs.first(), pairs.rest());
            let mut expected = Recorder::default();
            std::mem::discriminant(&**left).hash(&mut expected);
            first.hash(&mut expected);
            rest.hash(&mut expected);
            assert_eq!(written(left), expected.0, "{left:?}");
            assert_eq!(format!("{left:?}"), format!("Seq({first:?}, {rest:?})"));
            struct Tree<'a>(&'a CStatement, &'a CStatement);
            impl fmt::Debug for Tree<'_> {
                fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                    f.debug_tuple("Seq").field(self.0).field(self.1).finish()
                }
            }
            assert_eq!(
                format!("{left:#?}"),
                format!("{:#?}", Tree(first, &rest)),
                "{left:?}"
            );
            for right in &shapes {
                let other = sequence(right);
                let tree = first
                    .cmp(other.first())
                    .then_with(|| rest.cmp(&other.rest()));
                assert_eq!(left.cmp(right), tree, "{left:?} against {right:?}");
                assert_eq!(left == right, tree == Ordering::Equal);
            }
            // Against any other statement, a sequence orders as a `Seq`.
            for statement in [CStatement::Skip, CStatement::Break, (*leaf(9)).clone()] {
                assert_eq!(
                    (**left).cmp(&statement),
                    SEQ_STATEMENT.with(|seq| seq.cmp(&statement))
                );
            }
        }
    }

    #[test]
    fn a_pair_whose_second_half_is_a_sequence_extends_it() {
        let (a, b, c) = (leaf(1), leaf(2), leaf(3));
        let right = pair(a.clone(), pair(b.clone(), c.clone()));
        assert_eq!(sequence(&right).len(), 3);
        let left = pair(pair(a.clone(), b.clone()), c.clone());
        assert_eq!(sequence(&left).len(), 2);
        assert_ne!(right, left);
        let built = CStatementSequence::from_statements([a.clone(), b.clone(), c.clone()]).unwrap();
        assert_eq!(*right, CStatement::Seq(built));
        // A sequence last is spliced in, by a fold, a map and a replacement.
        let spliced =
            CStatementSequence::from_statements([a.clone(), pair(b.clone(), c.clone())]).unwrap();
        assert_eq!(*right, CStatement::Seq(spliced.clone()));
        assert_eq!(
            CStatement::Seq(sequence(&pair(a.clone(), a.clone())).with_statement(1, pair(b, c))),
            *right
        );
        assert_eq!(CStatement::Seq(spliced.map(Arc::clone)), *right);
        assert!(CStatementSequence::from_statements([a]).is_none());
    }

    #[test]
    fn a_suffix_and_a_replacement_share_the_other_statements() {
        let statements = (0..200).map(leaf).collect::<Vec<_>>();
        let whole = CStatementSequence::from_statements(statements.clone()).unwrap();
        let rest = whole.rest();
        let rest = sequence(&rest);
        assert_eq!(rest.len(), 199);
        assert!(
            rest.iter()
                .zip(&statements[1..])
                .all(|(l, r)| Arc::ptr_eq(l, r))
        );
        // Putting a statement back in front reuses the suffix's free slot.
        let again = rest.clone().with_front(statements[0].clone());
        assert_eq!(again, whole);
        assert!(again.items.ptr_eq(&whole.items) || again.start == 0);
        let replaced = whole.with_statement(150, leaf(-1));
        assert_eq!(replaced.get(150), Some(&leaf(-1)));
        assert!(
            replaced
                .iter()
                .zip(&statements)
                .enumerate()
                .all(|(index, (l, r))| index == 150 || Arc::ptr_eq(l, r))
        );
        assert_eq!(whole.get(150), Some(&statements[150]));
    }
}
