//! Select each returned view's loan once from the call's explicit sources.
use super::*;
use crate::kernel::equality_graph::CanonicalPointer;

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct SelectedBacking {
    pub(super) loan: LoanId,
    pub(super) support: ResourceOccurrenceId,
    pub(super) entering: Option<LoanViewBinding>,
    permission: ResourceFact,
}
#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
enum Key {
    Exact(Resource),
    Memory(CanonicalPointer, u32, MachineTerm, MachineTerm),
    Family(ResourceFamily),
}
#[derive(Default)]
pub(super) struct ReturnLoanBackings {
    pieces: BTreeMap<Key, Option<SelectedBacking>>,
    heads: BTreeMap<Resource, Option<SelectedBacking>>,
    single: Option<SelectedBacking>,
    loans: BTreeSet<LoanId>,
}
impl ReturnLoanBackings {
    fn keys(piece: &ResourceFact, assumptions: &PureFactContext) -> Vec<Key> {
        let mut keys = Vec::new();
        if let Some(range) = piece.memory_range()
            && range.int32_bounds().is_some()
            && let Some(base) = assumptions.equality_graph.canonical_pointer(range.base())
        {
            keys.push(Key::Memory(
                base,
                range.element_width(),
                range.start().clone(),
                range.end().clone(),
            ));
        }
        keys.push(Key::Exact(piece.resource().clone()));
        keys.push(Key::Family(piece.family()));
        keys
    }
    fn insert<K: Ord>(
        map: &mut BTreeMap<K, Option<SelectedBacking>>,
        key: K,
        source: &SelectedBacking,
    ) {
        match map.entry(key) {
            std::collections::btree_map::Entry::Vacant(entry) => {
                entry.insert(Some(source.clone()));
            }
            std::collections::btree_map::Entry::Occupied(mut entry) => {
                if entry
                    .get()
                    .as_ref()
                    .is_some_and(|old| old.loan != source.loan || old.entering != source.entering)
                {
                    entry.insert(None);
                }
            }
        }
    }
    fn add(&mut self, source: SelectedBacking, assumptions: &PureFactContext) {
        crate::instrumentation::record_deterministic_work(1);
        if self.loans.insert(source.loan) {
            self.single = (self.loans.len() == 1).then(|| source.clone());
        }
        for key in Self::keys(&source.permission, assumptions) {
            Self::insert(&mut self.pieces, key, &source);
        }
    }
    pub(super) fn from_plan(plan: &StableViewTransferPlan, assumptions: &PureFactContext) -> Self {
        let mut result = Self::default();
        let mut seen = BTreeSet::new();
        // These are new loans emitted by this call's plan, not inherited loan
        // histories. Multiple requirements can share one emitted frontier.
        for view in plan.stable_views() {
            if !seen.insert(view.loan) {
                continue;
            }
            for permission in plan.ledger.permitted_descriptions(view.loan) {
                result.add(
                    SelectedBacking {
                        loan: view.loan,
                        support: view.support,
                        entering: None,
                        permission,
                    },
                    assumptions,
                );
            }
        }
        for (head, binding) in &plan.transferred_holds {
            let source = SelectedBacking {
                loan: binding.loan,
                support: binding.support,
                entering: Some(binding.clone()),
                permission: binding.viewed.clone(),
            };
            Self::insert(&mut result.heads, head.resource().clone(), &source);
            result.add(source, assumptions);
        }
        result
    }
    pub(super) fn select(
        &self,
        head: &ResourceFact,
        piece: &ResourceFact,
        ledger: &LoanLedger,
        assumptions: &PureFactContext,
    ) -> Result<SelectedBacking, bool> {
        let _checking =
            crate::instrumentation::CheckingWorkScope::new("select returned loan backing", 1);
        #[cfg(test)]
        let _fast =
            crate::kernel::search::FastOperationScope::enter("returned loan backing selection");
        let mut candidate = self.heads.get(head.resource());
        if candidate.is_none() {
            for key in Self::keys(piece, assumptions) {
                if let Some(source) = self.pieces.get(&key) {
                    candidate = Some(source);
                    break;
                }
            }
        }
        let mut selected = match candidate {
            Some(Some(source)) => source.clone(),
            Some(None) => return Err(true),
            None => self.single.clone().ok_or(false)?,
        };
        // The plan's newly emitted permission is already selected. An inherited
        // hold uses its producer-maintained per-loan index instead of scanning
        // the loan's projection history.
        if selected.entering.is_some() {
            selected.permission = ledger
                .selected_return_permission(selected.loan, piece, &selected.permission, assumptions)
                .ok_or(false)?;
        } else if !crate::kernel::loans::returned_permission_covers(
            &selected.permission,
            piece,
            assumptions,
        ) {
            return Err(false);
        }
        Ok(selected)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn source(
        ledger: &LoanLedger,
        owner: super::super::super::loans::LoanParticipantId,
        reader: super::super::super::loans::LoanParticipantId,
        p: Pointer,
    ) -> (LoanLedger, SelectedBacking) {
        let fact = ResourceFact::own_memory(MemoryRange::new(p, 0u32.into(), 1u32.into()));
        let (_, inserted) =
            ResourceContext::new().unchecked_with_facts_and_occurrences([fact.clone()]);
        let support = inserted[0].1;
        let opening = ledger.lend(owner, reader, support, fact.clone()).unwrap();
        (
            ledger.apply(&opening.transition).unwrap(),
            SelectedBacking {
                loan: opening.loan,
                support,
                entering: None,
                permission: ResourceFact::View(fact.resource().clone()),
            },
        )
    }
    #[test]
    fn selection_retains_the_backing_occurrence_and_refuses_aliased_ambiguity() {
        let ledger = LoanLedger::new();
        let owner = ledger.fresh_participant().unwrap();
        let reader = ledger.fresh_participant().unwrap();
        let p = Pointer::symbolic(Variable(8_912_000));
        let q = Pointer::symbolic(Variable(8_912_001));
        let (ledger, a) = source(&ledger, owner, reader, p.clone());
        let (ledger, b) = source(&ledger, owner, reader, q.clone());
        let facts = PureFactContext::new();
        let head = ResourceFact::own_composite("returned".into(), vec![]);
        let mut index = ReturnLoanBackings::default();
        index.add(a.clone(), &facts);
        index.add(b.clone(), &facts);
        assert_eq!(
            index
                .select(&head, &a.permission, &ledger, &facts)
                .unwrap()
                .support,
            a.support
        );
        let aliases = facts.assume_condition(ConditionTerm::pointer_equal(p, q), true);
        let mut index = ReturnLoanBackings::default();
        index.add(a.clone(), &aliases);
        index.add(b, &aliases);
        assert_eq!(
            index.select(&head, &a.permission, &ledger, &aliases),
            Err(true)
        );
    }
    mod scaling_tests {
        include!("../../scaling_tests/kernel/functions/return_loan_backing.rs");
    }
}

#[cfg(test)]
mod coverage_tests {
    use super::*;
    #[test]
    fn a_selected_whole_view_backs_separate_translated_pieces() {
        let p = Pointer::symbolic(Variable(8_915_000));
        let q = Pointer::symbolic(Variable(8_915_001));
        let facts = PureFactContext::new().assume_condition(
            ConditionTerm::pointer_equal(q.clone(), p.offset_by_bytes(4)),
            true,
        );
        let whole =
            ResourceFact::view_memory(MemoryRange::new(p.clone(), 0u32.into(), 2u32.into()));
        let _fast = crate::kernel::search::FastOperationScope::enter(
            "selected loan coverage of separate pieces",
        );
        for base in [p, q] {
            let piece = ResourceFact::view_memory(MemoryRange::new(base, 0u32.into(), 1u32.into()));
            assert!(crate::kernel::loans::returned_permission_covers(
                &whole, &piece, &facts
            ));
        }
    }
}
