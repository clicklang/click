//! Sealed source scopes reconcile only completed local-reference work.
use super::*;

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub(crate) struct ScalarReferenceScopeKey {
    family: Arc<ScalarReferencePlanFamily>,
    block: usize,
    join: usize,
    cleanup: [u8; 32],
}
#[derive(Debug)]
pub(crate) struct ScalarReferenceScopePlan {
    key: ScalarReferenceScopeKey,
    locals: Vec<(String, CType)>,
}
impl ScalarReferenceScopePlan {
    pub(crate) fn new(
        family: Arc<ScalarReferencePlanFamily>,
        block: usize,
        join: usize,
        locals: Vec<(String, CType)>,
    ) -> Arc<Self> {
        use sha2::{Digest, Sha256};
        let mut hash = Sha256::new();
        hash.update(b"click-local-reference-scope-cleanup-v1");
        for (name, ty) in &locals {
            hash.update((name.len() as u64).to_le_bytes());
            hash.update(name.as_bytes());
            let ty = format!("{ty:?}");
            hash.update((ty.len() as u64).to_le_bytes());
            hash.update(ty.as_bytes());
        }
        Arc::new(Self {
            key: ScalarReferenceScopeKey {
                family,
                block,
                join,
                cleanup: hash.finalize().into(),
            },
            locals,
        })
    }
    pub(crate) fn operation(self: &Arc<Self>, closing: bool) -> CStatement {
        CStatement::ScalarReferenceScope(CScalarReferenceScope {
            plan: self.clone(),
            closing,
        })
    }
    #[cfg(test)]
    pub(in crate::kernel::source_loans) fn key(&self) -> &ScalarReferenceScopeKey {
        &self.key
    }
}

/// Private operands come from checked locked-source analysis. Only completed
/// local-reference transitions may be discarded, and no allocation counter is
/// rewound. Cleanup prevents a branch join from abstracting a dead reference
/// into a fresh ordinary pointer.
#[derive(Clone, Debug)]
pub struct CScalarReferenceScope {
    plan: Arc<ScalarReferenceScopePlan>,
    closing: bool,
}
impl CScalarReferenceScope {
    pub(crate) fn cleared_locals(&self) -> &[(String, CType)] {
        if self.closing { &self.plan.locals } else { &[] }
    }
    pub(in crate::kernel) fn execute(&self, state: &CState) -> Result<CState, loans::LoanRefusal> {
        let mut state = state.clone();
        if !self.closing {
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
            let ledger = state.loan_ledger().unwrap().begin_local_reference_scope(
                state.loan_participant().unwrap(),
                self.plan.key.clone(),
            )?;
            return Ok(state.with_loan_ledger(Some(ledger)));
        }
        let ledger = state
            .loan_ledger()
            .ok_or(loans::LoanRefusal::MissingLoanBinding)?;
        let holder = state
            .loan_participant()
            .ok_or(loans::LoanRefusal::WrongHolder)?;
        let base = ledger.close_local_reference_scope(holder, &self.plan.key, state.resources())?;
        for (name, expected) in &self.plan.locals {
            crate::instrumentation::record_deterministic_work(1);
            let binding = state
                .locals
                .binding(name)
                .ok_or(loans::LoanRefusal::InvalidEvidence)?;
            let (ty, slot) = match binding {
                CLocalBinding::Object {
                    storage_declared: true,
                    c_type,
                    slot,
                    volatile: false,
                    constant: false,
                    ..
                }
                | CLocalBinding::UninitializedObject {
                    c_type,
                    slot,
                    volatile: false,
                    constant: false,
                    ..
                } => (*c_type, slot.clone()),
                _ => return Err(loans::LoanRefusal::UnsupportedResource),
            };
            if !ty.is_pointer()
                || ty != *expected
                || !block_is_never_address_taken_local(&slot.block)
            {
                return Err(loans::LoanRefusal::UnsupportedResource);
            }
            state.locals.forget_initialization(name);
            let memory = state
                .memory
                .clone()
                .with_uninitialized_object(slot, ty.byte_width());
            state.set_memory(memory);
        }
        Ok(state.with_loan_ledger(Some(base)))
    }
}
impl PartialEq for CScalarReferenceScope {
    fn eq(&self, other: &Self) -> bool {
        self.closing == other.closing && self.plan.key == other.plan.key
    }
}
impl Eq for CScalarReferenceScope {}
impl std::hash::Hash for CScalarReferenceScope {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        std::hash::Hash::hash(&(&self.plan.key, self.closing), state);
    }
}
impl Ord for CScalarReferenceScope {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        (&self.plan.key, self.closing).cmp(&(&other.plan.key, other.closing))
    }
}
impl PartialOrd for CScalarReferenceScope {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
