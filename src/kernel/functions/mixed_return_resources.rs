//! Retain return-clause roles through guards and deferred evaluation.
use super::*;

pub(super) struct EvaluatedReturnResources {
    pub(super) resources: ResourceContext,
    /// One marker per emitted occurrence retrieved from the checked entry
    /// borrow queue, in insertion order. A declared role alone is insufficient.
    /// A raw-description consumer does not authorize restoration from this.
    pub(super) entry_borrows: Vec<bool>,
}

pub(super) struct PreparedReturnComposition {
    pub(super) frame: ResourceContext,
    pub(super) pending: ResourceContext,
    pub(super) entry_borrow_outputs: ResourceContext,
    restored: Vec<(ResourceFact, ResourceOccurrenceId)>,
    restore_order: Vec<bool>,
}

impl EvaluatedReturnResources {
    pub(super) fn restore_entry_borrows(
        &self,
        frame: ResourceContext,
        composition: ReturnResourceComposition,
        assumptions: &PureFactContext,
    ) -> Result<PreparedReturnComposition, ResourceContextValidityError> {
        let restore_order = self
            .entry_borrows
            .iter()
            .map(|entry| {
                *entry && matches!(composition, ReturnResourceComposition::RestoreEntryBorrows)
            })
            .collect::<Vec<_>>();
        if !restore_order.iter().any(|restore| *restore) {
            return Ok(PreparedReturnComposition {
                frame,
                pending: self.resources.clone(),
                entry_borrow_outputs: ResourceContext::new_with_equalities(assumptions),
                restored: Vec::new(),
                restore_order,
            });
        }
        let mut borrowed = ResourceContext::new_with_equalities(assumptions);
        let mut pending = ResourceContext::new_with_equalities(assumptions);
        for (fact, restore) in self.resources.facts().iter().zip(&restore_order) {
            if *restore {
                borrowed = borrowed.unchecked_with_fact(fact.clone());
            } else {
                pending = pending.unchecked_with_fact(fact.clone());
            }
        }
        let entry_borrow_outputs = borrowed.clone();
        let (frame, restored) = ResourceContext::restore_call_borrows(
            ReturnedCallBorrows {
                frame,
                outputs: borrowed,
            },
            assumptions,
        )?;
        Ok(PreparedReturnComposition {
            frame,
            pending,
            entry_borrow_outputs,
            restored,
            restore_order,
        })
    }
}

impl PreparedReturnComposition {
    pub(super) fn finish(
        self,
        assumptions: &PureFactContext,
    ) -> Result<
        (ResourceContext, Vec<(ResourceFact, ResourceOccurrenceId)>),
        ResourceContextValidityError,
    > {
        let (frame, inserted) = if self.pending.facts().is_empty() {
            (self.frame, Vec::new())
        } else {
            self.frame
                .try_compose_with_legacy_discovery_and_occurrences(
                    self.pending.facts().iter().cloned(),
                    assumptions,
                )?
        };
        if self.restored.is_empty() {
            return Ok((frame, inserted));
        }
        // Both constructors retain one occurrence for each supplied fact.
        // Rejoin their output-sized sequences in the original emitted order,
        // without matching descriptions or replacing occurrence identities.
        let mut restored = self.restored.into_iter();
        let mut inserted = inserted.into_iter();
        let occurrences = self
            .restore_order
            .into_iter()
            .map(|restore| {
                if restore {
                    restored.next().expect("restored entry occurrence")
                } else {
                    inserted.next().expect("admitted output occurrence")
                }
            })
            .collect();
        Ok((frame, occurrences))
    }
}

#[cfg(test)]
mod tests;

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/functions/mixed_return_resources.rs");
}
