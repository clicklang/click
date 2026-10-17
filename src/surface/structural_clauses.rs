//! A function block's structural clauses, indexed so that binding one
//! frontier loop clause, resolving a label and re-checking the bound list
//! cost the clause's own work rather than a walk over every clause the
//! earlier loops bound.

use super::{CodeRegion, StructuralClause};
use crate::persistent::{PersistentMap, PersistentSet};

/// The clauses in binding order. A clause for a loop that already has one
/// takes that clause's place; any other clause goes after the last.
#[derive(Clone, Default)]
pub struct StructuralClauses {
    /// Each clause under the position it took when first bound.
    entries: PersistentMap<u64, StructuralClause>,
    next_position: u64,
    /// The position of each loop's clause.
    loop_positions: PersistentMap<usize, u64>,
    /// Every labelled clause, as its label and position.
    labelled: PersistentMap<(String, u64), ()>,
    /// The labels whose clauses name more than one region.
    rebound_labels: PersistentSet<String>,
    /// How many clauses carry a proof scope, and how many carry a proof
    /// scope or declared resources.
    scoped: usize,
    scoped_or_resourced: usize,
    /// The loop count every clause outside `unvalidated` was validated
    /// against ([`Self::validate`]).
    validated_loop_count: Option<usize>,
    unvalidated: PersistentSet<u64>,
}

impl StructuralClauses {
    /// The list holding no clause, for lowerings that read none.
    pub(in crate::surface) fn empty() -> &'static Self {
        static EMPTY: std::sync::LazyLock<StructuralClauses> =
            std::sync::LazyLock::new(StructuralClauses::default);
        &EMPTY
    }

    pub fn iter(&self) -> StructuralClausesIter<'_> {
        StructuralClausesIter(self.entries.iter())
    }

    pub fn to_vec(&self) -> Vec<StructuralClause> {
        self.iter().cloned().collect()
    }

    pub fn len(&self) -> usize {
        self.entries.len()
    }

    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Whether any clause carries a proof scope.
    pub(in crate::surface) fn any_scoped(&self) -> bool {
        self.scoped != 0
    }

    /// Whether any clause carries a proof scope or declares resources.
    pub(in crate::surface) fn any_scoped_or_resourced(&self) -> bool {
        self.scoped_or_resourced != 0
    }

    /// The clause bound to loop `index`: a loop has at most one.
    pub(in crate::surface) fn for_loop(&self, index: usize) -> Option<&StructuralClause> {
        let position = self.loop_positions.get(&index)?;
        self.entries.get(position)
    }

    /// Whether any clause is bound to a loop.
    pub(in crate::surface) fn any_loop(&self) -> bool {
        !self.loop_positions.is_empty()
    }

    /// The region of the first clause, in binding order, labelled `label`.
    pub(in crate::surface) fn labelled_region(&self, label: &str) -> Option<&CodeRegion> {
        let ((found, position), _) = self.labelled.get_greater_than(&(label.to_string(), 0))?;
        if found != label {
            return None;
        }
        self.entries.get(position).map(StructuralClause::region)
    }

    /// Whether some label names two regions, as
    /// `refuse_rebound_loop_labels` refuses.
    pub(in crate::surface) fn has_rebound_label(&self) -> bool {
        !self.rebound_labels.is_empty()
    }

    /// Bind `clause`: in place of the clause for the same loop, or after
    /// the last clause.
    pub(in crate::surface) fn bind(&mut self, clause: StructuralClause) {
        let existing = match clause.region() {
            CodeRegion::Loop(index) => self.loop_positions.get(index).copied(),
            _ => None,
        };
        let position = match existing {
            Some(position) => {
                let previous = self
                    .entries
                    .get(&position)
                    .cloned()
                    .expect("a loop's position holds its clause");
                self.forget(&previous, position);
                position
            }
            None => {
                self.next_position += 1;
                let position = self.next_position;
                if let CodeRegion::Loop(index) = clause.region() {
                    self.loop_positions.insert(*index, position);
                }
                position
            }
        };
        self.scoped += usize::from(!clause.scope.is_empty());
        self.scoped_or_resourced +=
            usize::from(!clause.scope.is_empty() || !clause.resources().is_empty());
        let label = clause.label().map(str::to_string);
        self.entries.insert(position, clause);
        if let Some(label) = label {
            self.labelled.insert((label.clone(), position), ());
            self.recount_label(&label);
        }
        self.unvalidated = self.unvalidated.with_value(position);
    }

    fn forget(&mut self, clause: &StructuralClause, position: u64) {
        self.scoped -= usize::from(!clause.scope.is_empty());
        self.scoped_or_resourced -=
            usize::from(!clause.scope.is_empty() || !clause.resources().is_empty());
        if let Some(label) = clause.label() {
            self.labelled.remove(&(label.to_string(), position));
            self.recount_label(label);
        }
    }

    /// Whether `label`'s clauses name more than one region, over its own
    /// clauses only.
    fn recount_label(&mut self, label: &str) {
        let mut first_region = None;
        let mut rebound = false;
        let mut cursor = (label.to_string(), 0);
        while let Some(((found, position), _)) = self.labelled.get_greater_than(&cursor) {
            if found != label {
                break;
            }
            #[cfg(test)]
            count_clause_visit();
            let region = self
                .entries
                .get(position)
                .expect("a labelled position holds its clause")
                .region();
            match first_region {
                None => first_region = Some(region),
                Some(first) if first != region => rebound = true,
                Some(_) => {}
            }
            cursor = (found.clone(), *position);
        }
        self.rebound_labels = if rebound {
            self.rebound_labels.with_value(label.to_string())
        } else {
            self.rebound_labels.without_value(&label.to_string())
        };
    }

    /// Check every clause with `check`, in binding order, as a check of the
    /// whole list against `loop_count` would: a clause already checked
    /// against the same loop count, and not rebound since, is not checked
    /// again. `check` must depend on nothing but the clause and the loop
    /// count, so the first failure is the one a whole check finds.
    pub(in crate::surface) fn validate<E>(
        &mut self,
        loop_count: usize,
        mut check: impl FnMut(&StructuralClause) -> Result<(), E>,
    ) -> Result<(), E> {
        if self.validated_loop_count == Some(loop_count) {
            for position in self.unvalidated.iter() {
                #[cfg(test)]
                count_clause_visit();
                if let Some(clause) = self.entries.get(position) {
                    check(clause)?;
                }
            }
        } else {
            for clause in self.iter() {
                check(clause)?;
            }
        }
        self.validated_loop_count = Some(loop_count);
        self.unvalidated = PersistentSet::default();
        Ok(())
    }
}

impl From<Vec<StructuralClause>> for StructuralClauses {
    fn from(clauses: Vec<StructuralClause>) -> Self {
        let mut list = Self::default();
        for clause in clauses {
            list.bind(clause);
        }
        list
    }
}

impl PartialEq for StructuralClauses {
    fn eq(&self, other: &Self) -> bool {
        self.len() == other.len() && self.iter().eq(other.iter())
    }
}

impl Eq for StructuralClauses {}

impl std::fmt::Debug for StructuralClauses {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.debug_list().entries(self.iter()).finish()
    }
}

impl<'a> IntoIterator for &'a StructuralClauses {
    type Item = &'a StructuralClause;
    type IntoIter = StructuralClausesIter<'a>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

/// The clauses of a [`StructuralClauses`], in binding order.
pub struct StructuralClausesIter<'a>(
    crate::persistent::PersistentMapIter<'a, u64, StructuralClause>,
);

#[cfg(test)]
thread_local! {
    static CLAUSE_VISITS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// The clauses clause lists yielded or re-read on this thread so far.
#[cfg(test)]
pub(crate) fn structural_clause_visits() -> usize {
    CLAUSE_VISITS.with(std::cell::Cell::get)
}

#[cfg(test)]
fn count_clause_visit() {
    CLAUSE_VISITS.with(|count| count.set(count.get() + 1));
}

impl<'a> Iterator for StructuralClausesIter<'a> {
    type Item = &'a StructuralClause;

    fn next(&mut self) -> Option<Self::Item> {
        let clause = self.0.next().map(|(_, clause)| clause);
        #[cfg(test)]
        if clause.is_some() {
            count_clause_visit();
        }
        clause
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

impl DoubleEndedIterator for StructuralClausesIter<'_> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.0.next_back().map(|(_, clause)| clause)
    }
}

impl ExactSizeIterator for StructuralClausesIter<'_> {}
