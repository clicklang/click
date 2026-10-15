//! Semantic birth/end operations issued from checked locked-source lowering.
//! Observation labels remain inert; these plans bind the actual IR operands.
use super::*;
use std::sync::Arc;

/// Full labels are retained once for diagnostics and source membership. Hot
/// semantic identity uses the same collision-resistant identity discipline as
/// locked imports, with explicit lengths separating the two source labels.
#[derive(Clone, Debug)]
pub(crate) struct ScalarReferencePlanFamily {
    pub(crate) import_identity: Arc<str>,
    pub(crate) function: Arc<str>,
    digest: [u8; 32],
}
impl ScalarReferencePlanFamily {
    pub(crate) fn new(import_identity: &str, function: &str) -> Arc<Self> {
        use sha2::{Digest, Sha256};
        let mut hash = Sha256::new();
        hash.update(b"click-scalar-reference-source-family-v1");
        for label in [import_identity, function] {
            hash.update((label.len() as u64).to_le_bytes());
            hash.update(label.as_bytes());
        }
        Arc::new(Self {
            import_identity: import_identity.into(),
            function: function.into(),
            digest: hash.finalize().into(),
        })
    }
}
impl PartialEq for ScalarReferencePlanFamily {
    fn eq(&self, other: &Self) -> bool {
        self.digest == other.digest
    }
}
impl Eq for ScalarReferencePlanFamily {}
impl std::hash::Hash for ScalarReferencePlanFamily {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        std::hash::Hash::hash(&self.digest, state);
    }
}
impl Ord for ScalarReferencePlanFamily {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.digest.cmp(&other.digest)
    }
}
impl PartialOrd for ScalarReferencePlanFamily {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub(crate) struct ScalarReferencePlanKey {
    pub(crate) family: Arc<ScalarReferencePlanFamily>,
    pub(crate) block: usize,
    pub(crate) borrow: usize,
    pub(crate) end_block: usize,
    pub(crate) end: usize,
}
impl std::ops::Deref for ScalarReferencePlanKey {
    type Target = ScalarReferencePlanFamily;
    fn deref(&self) -> &Self::Target {
        &self.family
    }
}

/// Private birth operands are captured after checked source analysis and
/// lowering agree on the selected assignment in one immutable body.
#[derive(Debug)]
pub(crate) struct ScalarReferenceSourcePlan {
    key: ScalarReferencePlanKey,
    parent: String,
    child: String,
    value_type: CType,
    assignment: CExpression,
}
impl ScalarReferenceSourcePlan {
    pub(crate) fn new(
        key: ScalarReferencePlanKey,
        parent: String,
        child: String,
        value_type: CType,
        assignment: CExpression,
    ) -> Arc<Self> {
        Arc::new(Self {
            key,
            parent,
            child,
            value_type,
            assignment,
        })
    }
    pub(crate) fn key(&self) -> &ScalarReferencePlanKey {
        &self.key
    }
    pub(super) fn validates_assignment(&self, name: &str, expression: &CExpression) -> bool {
        name == self.child && expression == &self.assignment
    }
    pub(super) fn begin(
        &self,
        before: &CState,
        after: &CState,
        assumptions: &PureFactContext,
    ) -> Result<CState, loans::LoanRefusal> {
        let CValue::Pointer(parent) = before
            .locals
            .get(&self.parent)
            .ok_or(loans::LoanRefusal::InvalidEvidence)?
        else {
            return Err(loans::LoanRefusal::InvalidEvidence);
        };
        let CValue::Pointer(child) = after
            .locals
            .get(&self.child)
            .ok_or(loans::LoanRefusal::InvalidEvidence)?
        else {
            return Err(loans::LoanRefusal::InvalidEvidence);
        };
        if parent.pointer() != child.pointer() || parent.c_type() != child.c_type() {
            return Err(loans::LoanRefusal::InvalidEvidence);
        }
        let mut state = after.clone();
        match (state.loan_ledger(), state.loan_participant()) {
            (None, None) => {
                let ledger = loans::LoanLedger::new();
                let holder = ledger.fresh_participant()?;
                state = state
                    .with_loan_ledger(Some(ledger))
                    .with_loan_participant(Some(holder));
            }
            (Some(_), Some(_)) => {}
            _ => return Err(loans::LoanRefusal::InvalidEvidence),
        }
        let support = if parent.local_reference().is_some() {
            None
        } else {
            Some(
                state
                    .resources()
                    .exact_scalar_owner_occurrence(
                        parent.pointer(),
                        self.value_type.byte_width(),
                        assumptions,
                    )
                    .ok_or(loans::LoanRefusal::MissingBacking)?,
            )
        };
        let (mut state, child) = state.begin_source_scalar_reference(
            parent,
            support,
            self.value_type,
            assumptions,
            self.key.clone(),
        )?;
        let value = CValue::Pointer(child);
        // Assignment already checked this private local's storage; attaching
        // custody changes its permission identity, not the pointer's address.
        eval::sync_stack_local(&mut state, &self.child, &value);
        state.locals.set(self.child.clone(), value);
        Ok(state)
    }
}

pub(super) fn source_loan_error(error: loans::LoanRefusal) -> CRuntimeError {
    CRuntimeError::LoanRefusal(Box::new(error.diagnostic(LoanRefusalOperation::Transition)))
}

#[cfg(test)]
mod tests;

/// An explicit checked source borrow ending. Construction is restricted to
/// lowering after its immutable-source frontier has been checked. The key is
/// semantic identity; execution resolves only this invocation's live handle.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CScalarReferenceEnd(Arc<ScalarReferencePlanKey>);
impl CScalarReferenceEnd {
    pub(crate) fn new(key: ScalarReferencePlanKey) -> Self {
        Self(Arc::new(key))
    }
    pub(super) fn execute(
        &self,
        state: &CState,
        assumptions: &PureFactContext,
    ) -> Result<CState, loans::LoanRefusal> {
        state.end_source_scalar_reference(&self.0, assumptions)
    }
}
