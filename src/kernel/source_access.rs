//! Producer observations connecting locked MIR operations to completed
//! reference assignments and checked memory accesses. Observation labels grant
//! no permission; optional checked lease plans are separate semantic operations.
use super::*;
use std::sync::Arc;

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ReferenceBorrowSourceId {
    pub(crate) import_identity: Arc<str>,
    pub(crate) function: Arc<str>,
    pub(crate) block: usize,
    pub(crate) statement: usize,
    pub(crate) parent: Arc<str>,
    pub(crate) child: Arc<str>,
}

/// Source observations compare neutrally. A checked lease plan participates in
/// statement identity and executes an actual checked birth or read ending.
#[derive(Clone, Debug, Default)]
pub struct CStatementAssignSource(
    Option<Arc<ReferenceBorrowSourceId>>,
    Option<Arc<ScalarReferenceAssignmentLease>>,
);
#[derive(Debug)]
struct ScalarReferenceAssignmentLease {
    plan: Arc<ScalarReferenceSourcePlan>,
    read_ending: bool,
}
impl CStatementAssignSource {
    pub(crate) fn new(source: ReferenceBorrowSourceId) -> Self {
        Self(Some(Arc::new(source)), None)
    }
    pub(crate) fn as_ref(&self) -> Option<&ReferenceBorrowSourceId> {
        self.0.as_deref()
    }
    pub(crate) fn with_lease_plan(mut self, plan: Arc<ScalarReferenceSourcePlan>) -> Self {
        self.1 = Some(Arc::new(ScalarReferenceAssignmentLease {
            plan,
            read_ending: false,
        }));
        self
    }
    pub(crate) fn with_lease_read_end(mut self, plan: Arc<ScalarReferenceSourcePlan>) -> Self {
        self.1 = Some(Arc::new(ScalarReferenceAssignmentLease {
            plan,
            read_ending: true,
        }));
        self
    }
    pub(super) fn lease_plan(&self) -> Option<&Arc<ScalarReferenceSourcePlan>> {
        self.1.as_ref().map(|operation| &operation.plan)
    }
    pub(super) fn is_lease_read_end(&self) -> bool {
        self.1
            .as_ref()
            .is_some_and(|operation| operation.read_ending)
    }
    fn semantic_key(&self) -> Option<(bool, &ScalarReferencePlanKey)> {
        self.1
            .as_ref()
            .map(|operation| (operation.read_ending, operation.plan.key()))
    }
    pub(super) fn completed(
        &self,
        before: &CState,
        after: &CState,
        assigned: &str,
    ) -> Option<ExecutionPureFact> {
        let source = self.0.as_ref()?;
        if assigned != source.child.as_ref() {
            return None;
        }
        let CValue::Pointer(parent) = before.locals.get(&source.parent)? else {
            return None;
        };
        let CValue::Pointer(child) = after.locals.get(&source.child)? else {
            return None;
        };
        if parent.pointer() != child.pointer() || parent.c_type() != child.c_type() {
            return None;
        }
        let mut fact = ExecutionPureFact::certified(Proposition::ConditionIs(
            ConditionTerm::PointerEqual(
                Box::new(parent.pointer().clone()),
                Box::new(child.pointer().clone()),
            ),
            true,
        ));
        fact.public = false;
        fact.logical_read_equation = true;
        fact.reference_observation = ReferenceObservationSource(Some(Arc::new(
            ReferenceObservation::Borrow(ReferenceBorrowObservation {
                source: source.clone(),
                pointer: child.pointer().clone(),
            }),
        )));
        Some(fact)
    }
}
impl PartialEq for CStatementAssignSource {
    fn eq(&self, other: &Self) -> bool {
        self.semantic_key() == other.semantic_key()
    }
}
impl Eq for CStatementAssignSource {}
impl std::hash::Hash for CStatementAssignSource {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        std::hash::Hash::hash(&self.semantic_key(), state);
    }
}
impl Ord for CStatementAssignSource {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.semantic_key().cmp(&other.semantic_key())
    }
}
impl PartialOrd for CStatementAssignSource {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

#[derive(Debug)]
struct ReferenceBorrowObservation {
    source: Arc<ReferenceBorrowSourceId>,
    pointer: Pointer,
}
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

/// Observations compare neutrally and never authorize a store. A checked
/// ending plan participates in statement identity and consumes actual custody.
#[derive(Clone, Debug, Default)]
pub struct CStatementStoreSource(
    Option<Arc<ReferenceAccessSourceId>>,
    Option<Arc<ScalarReferenceSourcePlan>>,
);
impl CStatementStoreSource {
    pub(crate) fn new(source: ReferenceAccessSourceId) -> Self {
        Self(Some(Arc::new(source)), None)
    }
    pub(crate) fn with_lease_plan(mut self, plan: Arc<ScalarReferenceSourcePlan>) -> Self {
        self.1 = Some(plan);
        self
    }
    pub(super) fn lease_plan(&self) -> Option<&Arc<ScalarReferenceSourcePlan>> {
        self.1.as_ref()
    }
    pub(crate) fn as_ref(&self) -> Option<&ReferenceAccessSourceId> {
        self.0.as_deref()
    }
}
impl PartialEq for CStatementStoreSource {
    fn eq(&self, other: &Self) -> bool {
        self.1.as_ref().map(|plan| plan.key()) == other.1.as_ref().map(|plan| plan.key())
    }
}
impl Eq for CStatementStoreSource {}
impl std::hash::Hash for CStatementStoreSource {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        std::hash::Hash::hash(&self.1.as_ref().map(|plan| plan.key()), state);
    }
}
impl Ord for CStatementStoreSource {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.1
            .as_ref()
            .map(|plan| plan.key())
            .cmp(&other.1.as_ref().map(|plan| plan.key()))
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

#[derive(Debug)]
pub(crate) enum ExecutedReferenceBoundary<'a> {
    Borrow {
        source: &'a ReferenceBorrowSourceId,
        pointer: &'a Pointer,
    },
    Store(ExecutedReferenceAccess<'a>),
}

/// One optional provenance slot for completed reads and reference births.
/// Payloads are shared and allocated only for observed producers; comparison
/// ignores metadata. Pure facts do not pay for an extra slot for each kind.
#[derive(Clone, Debug, Default)]
pub(crate) struct ReferenceObservationSource(Option<Arc<ReferenceObservation>>);
#[derive(Debug)]
enum ReferenceObservation {
    Read {
        source: Arc<ReferenceAccessSourceId>,
        pointer: Pointer,
        snapshot: CMemorySnapshotIdentity,
        value_type: CType,
    },
    Borrow(ReferenceBorrowObservation),
}
impl ReferenceObservationSource {
    pub(super) fn new(
        source: Arc<ReferenceAccessSourceId>,
        pointer: Pointer,
        memory: &CMemory,
        value_type: CType,
    ) -> Self {
        Self(Some(Arc::new(ReferenceObservation::Read {
            source,
            pointer,
            snapshot: CMemorySnapshotIdentity::of(memory),
            value_type,
        })))
    }
    pub(super) fn is_some(&self) -> bool {
        self.0.is_some()
    }
    #[cfg(test)]
    fn is_borrow(&self) -> bool {
        matches!(self.0.as_deref(), Some(ReferenceObservation::Borrow(_)))
    }
    pub(super) fn matches_proposition(&self, proposition: &Proposition) -> bool {
        self.0.as_deref().is_none_or(|observation| match observation {
            ReferenceObservation::Read { source: _, pointer: expected, snapshot, value_type: expected_type } => matches!(proposition,
                Proposition::CMemoryReadDefined { memory, pointer, value_type }
                if *snapshot == CMemorySnapshotIdentity::of(memory) && expected == pointer && expected_type == value_type),
            ReferenceObservation::Borrow(birth) => matches!(proposition,
                Proposition::ConditionIs(ConditionTerm::PointerEqual(left, right), true)
                if left.as_ref() == &birth.pointer && right.as_ref() == &birth.pointer),
        })
    }
}
impl PartialEq for ReferenceObservationSource {
    fn eq(&self, _: &Self) -> bool {
        true
    }
}
impl Eq for ReferenceObservationSource {}
impl std::hash::Hash for ReferenceObservationSource {
    fn hash<H: std::hash::Hasher>(&self, _: &mut H) {}
}
impl Ord for ReferenceObservationSource {
    fn cmp(&self, _: &Self) -> std::cmp::Ordering {
        std::cmp::Ordering::Equal
    }
}
impl PartialOrd for ReferenceObservationSource {
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
    /// Selected producer order, grouped by the execution path that actually
    /// completed each operation. A label alone cannot construct a boundary.
    pub(crate) fn executed_reference_boundaries(
        &self,
    ) -> impl Iterator<Item = (usize, ExecutedReferenceBoundary<'_>)> {
        self.paths
            .iter()
            .enumerate()
            .flat_map(|(path_index, path)| {
                path.effect_facts
                    .iter()
                    .chain(path.facts.iter())
                    .filter_map(move |fact| {
                        if !fact.certified {
                            return None;
                        }
                        if let Some(ReferenceObservation::Borrow(birth)) =
                            fact.reference_observation.0.as_deref()
                        {
                            return Some((
                                path_index,
                                ExecutedReferenceBoundary::Borrow {
                                    source: &birth.source,
                                    pointer: &birth.pointer,
                                },
                            ));
                        }
                        let store = fact.certified_store.as_ref()?;
                        let source = store.source.as_ref()?;
                        (source.kind == ReferenceAccessKind::Write).then_some((
                            path_index,
                            ExecutedReferenceBoundary::Store(ExecutedReferenceAccess {
                                source,
                                pointer: &store.pointer,
                            }),
                        ))
                    })
            })
    }
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
                let read = fact
                    .reference_observation
                    .0
                    .as_deref()
                    .and_then(|observation| {
                        let ReferenceObservation::Read {
                            source, pointer, ..
                        } = observation
                        else {
                            return None;
                        };
                        (fact.certified && source.kind == ReferenceAccessKind::Read)
                            .then_some(ExecutedReferenceAccess { source, pointer })
                    });
                store.into_iter().chain(read)
            })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn borrow_fact() -> ExecutionPureFact {
        let pointer = Pointer {
            block: "birth".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let before = CState::new().with_local(
            "parent",
            CValue::typed_pointer(pointer.clone(), CType::Int32Pointer),
        );
        let after = before
            .clone()
            .with_local("child", CValue::typed_pointer(pointer, CType::Int32Pointer));
        CStatementAssignSource::new(ReferenceBorrowSourceId {
            import_identity: "locked".into(),
            function: "borrow".into(),
            block: 0,
            statement: 0,
            parent: "parent".into(),
            child: "child".into(),
        })
        .completed(&before, &after, "child")
        .unwrap()
    }
    #[test]
    fn source_reference_rewritten_birth_discards_its_observation() {
        let fact = borrow_fact();
        assert!(
            fact.clone()
                .with_proposition(fact.proposition().clone())
                .reference_observation
                .is_borrow()
        );
        assert!(
            !fact
                .with_proposition(Proposition::ConditionIs(
                    ConditionTerm::Bitvector32Equal(
                        Box::new(Bitvector32Term::Constant(0)),
                        Box::new(Bitvector32Term::Constant(0))
                    ),
                    true
                ))
                .reference_observation
                .is_borrow()
        );
    }
    #[test]
    fn source_reference_birth_requires_the_completed_parent_pointer_and_type() {
        let pointer = Pointer {
            block: "birth".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let before = CState::new().with_local(
            "parent",
            CValue::typed_pointer(pointer.clone(), CType::Int32Pointer),
        );
        let source = CStatementAssignSource::new(ReferenceBorrowSourceId {
            import_identity: "locked".into(),
            function: "borrow".into(),
            block: 0,
            statement: 0,
            parent: "parent".into(),
            child: "child".into(),
        });
        let different_pointer = before.clone().with_local(
            "child",
            CValue::typed_pointer(pointer.offset_by_bytes(4), CType::Int32Pointer),
        );
        assert!(
            source
                .completed(&before, &different_pointer, "child")
                .is_none()
        );
        let different_type = before.clone().with_local(
            "child",
            CValue::typed_pointer(pointer.clone(), CType::UInt8Pointer),
        );
        assert!(
            source
                .completed(&before, &different_type, "child")
                .is_none()
        );
        let after = before
            .clone()
            .with_local("child", CValue::typed_pointer(pointer, CType::Int32Pointer));
        assert!(source.completed(&before, &after, "other").is_none());
        assert!(source.completed(&CState::new(), &after, "child").is_none());
    }
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
        fact.reference_observation =
            ReferenceObservationSource::new(source, pointer, &memory, CType::Int32);
        fact
    }
    #[test]
    fn source_reference_rewritten_fact_discards_its_read_observation() {
        let fact = read_fact();
        let unchanged = fact.clone().with_proposition(fact.proposition().clone());
        assert!(unchanged.reference_observation.is_some());
        let mut changed = fact.proposition().clone();
        let Proposition::CMemoryReadDefined { pointer, .. } = &mut changed else {
            panic!()
        };
        *pointer = pointer.offset_by_bytes(4);
        assert!(
            !fact
                .with_proposition(changed)
                .reference_observation
                .is_some()
        );
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
            assert!(
                merged
                    .iter()
                    .last()
                    .unwrap()
                    .reference_observation
                    .is_some()
            );
            assert!(
                work <= 64,
                "selected source delta scanned {size} old facts: {work}"
            );
            let mut births = ExecutionFacts::new();
            births.push(borrow_fact());
            let (merged, work) = crate::instrumentation::measure_deterministic_work(|| {
                crate::kernel::reasoning::path_facts::merge_facts(
                    &prefix,
                    &births,
                    &PureFactContext::new(),
                )
                .unwrap()
            });
            assert_eq!(merged.len(), size as usize + 1);
            assert!(
                merged
                    .iter()
                    .last()
                    .unwrap()
                    .reference_observation
                    .is_borrow()
            );
            assert!(work <= 64, "birth delta scanned {size} old facts: {work}");
        }
    }
}
