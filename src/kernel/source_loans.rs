//! Semantic birth/end operations issued from checked locked-source lowering.
//! Observation labels remain inert; these plans bind the actual IR operands.
use super::*;
use std::sync::Arc;

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub(crate) struct ScalarReferencePlanKey {
    pub(crate) import_identity: Arc<str>,
    pub(crate) function: Arc<str>,
    pub(crate) block: usize,
    pub(crate) borrow: usize,
    pub(crate) end: usize,
}

/// Private operands are captured only after the source frontier checker and
/// the lowering pass agree on both selected operations in one immutable body.
#[derive(Debug)]
pub(crate) struct ScalarReferenceSourcePlan {
    key: ScalarReferencePlanKey,
    parent: String,
    child: String,
    value_type: CType,
    assignment: CExpression,
    ending: ScalarReferenceEnding,
}
#[derive(Debug)]
enum ScalarReferenceEnding {
    Store((CExpression, CExpression, CType, bool, bool)),
    Read {
        name: String,
        expression: CExpression,
        reference: String,
    },
}
impl ScalarReferenceSourcePlan {
    pub(crate) fn new(
        key: ScalarReferencePlanKey,
        parent: String,
        child: String,
        value_type: CType,
        assignment: CExpression,
        store: (CExpression, CExpression, CType, bool, bool),
    ) -> Arc<Self> {
        Arc::new(Self {
            key,
            parent,
            child,
            value_type,
            assignment,
            ending: ScalarReferenceEnding::Store(store),
        })
    }
    pub(crate) fn new_read(
        key: ScalarReferencePlanKey,
        parent: String,
        child: String,
        value_type: CType,
        assignment: CExpression,
        read: (String, CExpression, String),
    ) -> Arc<Self> {
        Arc::new(Self {
            key,
            parent,
            child,
            value_type,
            assignment,
            ending: ScalarReferenceEnding::Read {
                name: read.0,
                expression: read.1,
                reference: read.2,
            },
        })
    }
    pub(crate) fn key(&self) -> &ScalarReferencePlanKey {
        &self.key
    }
    pub(super) fn validates_assignment(&self, name: &str, expression: &CExpression) -> bool {
        name == self.child && expression == &self.assignment
    }
    pub(super) fn validates_store(
        &self,
        pointer: &CExpression,
        value: &CExpression,
        value_type: CType,
        volatile: bool,
        constant: bool,
    ) -> bool {
        let ScalarReferenceEnding::Store(store) = &self.ending else {
            return false;
        };
        (&store.0, &store.1, store.2, store.3, store.4)
            == (pointer, value, value_type, volatile, constant)
    }
    pub(super) fn validates_read_assignment(&self, name: &str, expression: &CExpression) -> bool {
        let ScalarReferenceEnding::Read {
            name: expected,
            expression: expected_expression,
            reference,
        } = &self.ending
        else {
            return false;
        };
        name == expected
            && expression == expected_expression
            && matches!(expression, CExpression::TypedLoad { pointer, value_type, volatile: false, pointee_constant: false, .. }
                if *value_type == self.value_type && matches!(pointer.as_ref(), CExpression::Variable(local) if local == reference))
    }
    /// Only a successful direct read assignment may call this operation. The
    /// selected reference must be a private local, so its value in `before` is
    /// exactly the operand consumed by the ordinary checked load. No source
    /// observation or earlier read fact supplies permission or ending evidence.
    pub(super) fn end_read(
        &self,
        before: &CState,
        after: &CState,
        assumptions: &PureFactContext,
    ) -> Result<CState, loans::LoanRefusal> {
        let ScalarReferenceEnding::Read {
            name,
            expression,
            reference,
        } = &self.ending
        else {
            return Err(loans::LoanRefusal::InvalidEvidence);
        };
        if !self.validates_read_assignment(name, expression)
            || before
                .locals
                .slot(reference)
                .is_some_and(|slot| !block_is_never_address_taken_local(&slot.block))
        {
            return Err(loans::LoanRefusal::UnsupportedResource);
        }
        let Some(CValue::Pointer(pointer)) = before.locals.get(reference) else {
            return Err(loans::LoanRefusal::InvalidEvidence);
        };
        let reference = pointer
            .local_reference()
            .ok_or(loans::LoanRefusal::MissingLoanBinding)?;
        if pointer.c_type().pointee_type() != Some(self.value_type) {
            return Err(loans::LoanRefusal::InvalidEvidence);
        }
        self.end(
            after,
            *reference,
            pointer.pointer().clone(),
            self.value_type,
            assumptions,
        )
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
        let support = state
            .resources()
            .exact_scalar_owner_occurrence(
                parent.pointer(),
                self.value_type.byte_width(),
                assumptions,
            )
            .ok_or(loans::LoanRefusal::MissingBacking)?;
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
    pub(super) fn end(
        &self,
        state: &CState,
        reference: loans::LocalScalarReference,
        pointer: Pointer,
        value_type: CType,
        assumptions: &PureFactContext,
    ) -> Result<CState, loans::LoanRefusal> {
        state.validate_source_scalar_reference(&reference, &self.key)?;
        let pointer = CPointerValue::new(
            pointer,
            value_type
                .pointer_to()
                .ok_or(loans::LoanRefusal::InvalidEvidence)?,
        )
        .with_local_reference(reference);
        state.end_local_scalar_reference(&pointer, assumptions)
    }
}

pub(super) fn source_loan_error(error: loans::LoanRefusal) -> CRuntimeError {
    CRuntimeError::LoanRefusal(Box::new(error.diagnostic(LoanRefusalOperation::Transition)))
}

#[cfg(test)]
mod tests;
