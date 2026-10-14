//! Producer observations connecting a locked MIR operation to an actual
//! checked memory access. These observations grant no memory permission.
use super::*;
use std::sync::Arc;

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub(crate) enum ReferenceAccessKind {
    Read,
    Write,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub(crate) struct ReferenceAccessSourceId {
    pub(crate) import_identity: Arc<str>,
    pub(crate) function: Arc<str>,
    pub(crate) block: usize,
    pub(crate) statement: usize,
    pub(crate) node: usize,
    pub(crate) reference_local: Arc<str>,
    pub(crate) kind: ReferenceAccessKind,
}

/// Optional producer provenance. It is not part of statement semantics or
/// proof identity, and is not an authorization to perform the store.
#[derive(Clone, Debug, Default)]
pub struct CStatementStoreSource(Option<Arc<ReferenceAccessSourceId>>);
impl CStatementStoreSource {
    pub(crate) fn new(source: ReferenceAccessSourceId) -> Self {
        Self(Some(Arc::new(source)))
    }
    pub(crate) fn as_ref(&self) -> Option<&ReferenceAccessSourceId> {
        self.0.as_deref()
    }
}
impl PartialEq for CStatementStoreSource {
    fn eq(&self, _: &Self) -> bool {
        true
    }
}
impl Eq for CStatementStoreSource {}
impl std::hash::Hash for CStatementStoreSource {
    fn hash<H: std::hash::Hasher>(&self, _: &mut H) {}
}
impl Ord for CStatementStoreSource {
    fn cmp(&self, _: &Self) -> std::cmp::Ordering {
        std::cmp::Ordering::Equal
    }
}
impl PartialOrd for CStatementStoreSource {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

/// Constructed only from a kernel producer's completed read or checked store.
/// Matching source provenance alone never constructs this observation.
#[derive(Debug)]
pub(crate) struct ExecutedReferenceAccess<'a> {
    source: &'a ReferenceAccessSourceId,
    pointer: &'a Pointer,
}

/// Private provenance for any completed source read, including cached values
/// that do not mint a new load variable. Comparison ignores this metadata.
#[derive(Clone, Debug, Default)]
pub(crate) struct ReferenceReadSource(Option<Arc<ReferenceReadObservation>>);
#[derive(Debug)]
struct ReferenceReadObservation {
    source: Arc<ReferenceAccessSourceId>,
    pointer: Pointer,
    snapshot: CMemorySnapshotIdentity,
    value_type: CType,
}
impl ReferenceReadSource {
    pub(super) fn new(
        source: Arc<ReferenceAccessSourceId>,
        pointer: Pointer,
        memory: &CMemory,
        value_type: CType,
    ) -> Self {
        Self(Some(Arc::new(ReferenceReadObservation {
            source,
            pointer,
            snapshot: CMemorySnapshotIdentity::of(memory),
            value_type,
        })))
    }
    pub(super) fn is_some(&self) -> bool {
        self.0.is_some()
    }
    pub(super) fn matches_proposition(&self, proposition: &Proposition) -> bool {
        self.0.as_ref().is_none_or(|read| matches!(proposition,
            Proposition::CMemoryReadDefined { memory, pointer, value_type }
            if read.snapshot == CMemorySnapshotIdentity::of(memory) && read.pointer == *pointer && read.value_type == *value_type))
    }
}
impl PartialEq for ReferenceReadSource {
    fn eq(&self, _: &Self) -> bool {
        true
    }
}
impl Eq for ReferenceReadSource {}
impl std::hash::Hash for ReferenceReadSource {
    fn hash<H: std::hash::Hasher>(&self, _: &mut H) {}
}
impl Ord for ReferenceReadSource {
    fn cmp(&self, _: &Self) -> std::cmp::Ordering {
        std::cmp::Ordering::Equal
    }
}
impl PartialOrd for ReferenceReadSource {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl ExecutedReferenceAccess<'_> {
    pub(crate) fn source(&self) -> &ReferenceAccessSourceId {
        self.source
    }
    pub(crate) fn pointer(&self) -> &Pointer {
        self.pointer
    }
}

impl SymbolicCExecution {
    /// Walk this selected execution's actual effects, without consulting
    /// ambient proof facts or scanning an environment/history.
    pub(crate) fn executed_reference_accesses(
        &self,
    ) -> impl Iterator<Item = ExecutedReferenceAccess<'_>> {
        self.paths
            .iter()
            .flat_map(|path| path.effect_facts.iter().chain(path.facts.iter()))
            .flat_map(|fact| {
                let store = fact.certified_store.as_ref().and_then(|store| {
                    let source = store.source.as_ref()?;
                    (fact.certified && source.kind == ReferenceAccessKind::Write).then_some(
                        ExecutedReferenceAccess {
                            source,
                            pointer: &store.pointer,
                        },
                    )
                });
                let read = fact.reference_read.0.as_deref().and_then(|read| {
                    (fact.certified && read.source.kind == ReferenceAccessKind::Read).then_some(
                        ExecutedReferenceAccess {
                            source: &read.source,
                            pointer: &read.pointer,
                        },
                    )
                });
                store.into_iter().chain(read)
            })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn read_fact() -> ExecutionPureFact {
        let pointer = Pointer {
            block: "source-read".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let memory = CMemory::new()
            .with_block(pointer.block.clone(), 4)
            .store(pointer.clone(), int32(7));
        let source = Arc::new(ReferenceAccessSourceId {
            import_identity: "locked".into(),
            function: "read".into(),
            block: 0,
            statement: 1,
            node: 0,
            reference_local: "child".into(),
            kind: ReferenceAccessKind::Read,
        });
        let mut fact = ExecutionPureFact::certified(Proposition::CMemoryReadDefined {
            memory: memory.clone(),
            pointer: pointer.clone(),
            value_type: CType::Int32,
        });
        fact.public = false;
        fact.logical_read_equation = true;
        fact.reference_read = ReferenceReadSource::new(source, pointer, &memory, CType::Int32);
        fact
    }
    #[test]
    fn source_reference_rewritten_fact_discards_its_read_observation() {
        let fact = read_fact();
        let unchanged = fact.clone().with_proposition(fact.proposition().clone());
        assert!(unchanged.reference_read.is_some());
        let mut changed = fact.proposition().clone();
        let Proposition::CMemoryReadDefined { pointer, .. } = &mut changed else {
            panic!()
        };
        *pointer = pointer.offset_by_bytes(4);
        assert!(!fact.with_proposition(changed).reference_read.is_some());
    }
    #[test]
    fn source_reference_selected_observation_merge_does_not_scan_ambient_facts() {
        for size in [16, 64, 256, 1024] {
            let mut prefix = ExecutionFacts::new();
            for index in 0..size {
                prefix.push(ExecutionPureFact::condition(
                    ConditionTerm::Bitvector32Equal(
                        Box::new(Bitvector32Term::Variable(Variable(index))),
                        Box::new(Bitvector32Term::Constant(7)),
                    ),
                    true,
                ));
            }
            let mut suffix = ExecutionFacts::new();
            suffix.push(read_fact());
            let (merged, work) = crate::instrumentation::measure_deterministic_work(|| {
                crate::kernel::reasoning::path_facts::merge_facts(
                    &prefix,
                    &suffix,
                    &PureFactContext::new(),
                )
                .unwrap()
            });
            assert_eq!(merged.len(), size as usize + 1);
            assert!(merged.iter().last().unwrap().reference_read.is_some());
            assert!(
                work <= 64,
                "selected source delta scanned {size} old facts: {work}"
            );
        }
    }
}
