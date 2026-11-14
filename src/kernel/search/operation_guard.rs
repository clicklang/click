//! Test-only enforcement of migrated operation/search boundaries.
//! This catches registered discovery, not arbitrary loops or unmetered work.
use std::cell::Cell;

thread_local! {
    static OPERATION: Cell<Option<&'static str>> = const { Cell::new(None) };
}

pub(crate) struct FastOperationScope(Option<&'static str>);

impl FastOperationScope {
    pub(crate) fn enter(name: &'static str) -> Self {
        Self(OPERATION.with(|current| current.replace(Some(name))))
    }
}

impl Drop for FastOperationScope {
    fn drop(&mut self) {
        OPERATION.with(|current| current.set(self.0));
    }
}

pub(crate) fn record_discovery(name: &'static str) {
    OPERATION.with(|current| {
        assert!(
            current.get().is_none(),
            "operation {:?} entered discovery {name}",
            current.get()
        );
    });
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::search::ProofSearch;
    use crate::kernel::{ConditionTerm, Proposition, PureFactContext};

    #[test]
    fn discovery_is_forbidden_even_for_true_and_restored_after_unwind() {
        let context = PureFactContext::new();
        assert!(ProofSearch::proves(
            &context,
            &Proposition::ConditionIs(ConditionTerm::Constant(true), true)
        ));
        let failure = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let _operation = FastOperationScope::enter("explicit theorem application");
            ProofSearch::proves(
                &context,
                &Proposition::ConditionIs(ConditionTerm::Constant(true), true),
            )
        }));
        assert!(failure.is_err());
        assert!(ProofSearch::proves(
            &context,
            &Proposition::ConditionIs(ConditionTerm::Constant(true), true)
        ));
    }

    #[test]
    fn nested_operations_do_not_relax_the_outer_boundary() {
        let _outer = FastOperationScope::enter("outer primitive");
        {
            let _inner = FastOperationScope::enter("inner primitive");
            assert!(std::panic::catch_unwind(|| record_discovery("inner search")).is_err());
        }
        assert!(std::panic::catch_unwind(|| record_discovery("outer search")).is_err());
    }
}

#[cfg(test)]
#[test]
#[should_panic(expected = "entered discovery condition fact transport")]
fn condition_transport_cannot_hide_inside_statement_publication() {
    let _operation = FastOperationScope::enter("statement result publication");
    crate::kernel::memory_provenance::prove_program_condition_fact_direct_transport(
        &crate::kernel::Proposition::ConditionIs(
            crate::kernel::ConditionTerm::Constant(true),
            true,
        ),
        &crate::kernel::Memory::new(),
        &crate::kernel::PureFactContext::new(),
    );
}
