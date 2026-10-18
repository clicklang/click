//! Read equations for the pointer aliases a call's reservation already checked.
//! The map exists only while instantiating that call path. It is not a global
//! snapshot equivalence, and diagnostic construction history supplies no evidence.

use super::*;
use std::{cell::RefCell, collections::HashMap, marker::PhantomData, rc::Rc};

type RootKey = (usize, usize, usize, usize, usize);

#[derive(Clone)]
struct ReadSource {
    // Retain both keys' roots: allocator reuse cannot alias a live entry.
    _rewritten: CMemory,
    original: CMemory,
}

thread_local! {
    static SOURCES: RefCell<HashMap<RootKey, ReadSource>> = RefCell::new(HashMap::new());
}

/// Builds the rewritten snapshot and its read source together. Call code
/// cannot accidentally pair an entry snapshot with a changed post-state.
#[derive(Clone)]
pub(super) struct CallReadState {
    state: CState,
    original: CMemory,
}

impl CallReadState {
    pub(super) fn new(state: &CState, aliases: &[(CResourceFact, CResourceFact)]) -> Self {
        Self {
            state: with_canonical_borrowed_pointer_memory(state, aliases),
            original: state.memory().clone(),
        }
    }
}

impl std::ops::Deref for CallReadState {
    type Target = CState;
    fn deref(&self) -> &CState {
        &self.state
    }
}

pub(super) struct CallReadAliasScope {
    previous: Vec<(RootKey, Option<ReadSource>)>,
    _thread: PhantomData<Rc<()>>,
}

impl CallReadAliasScope {
    /// Only the call producer installs pairs, after its reservation selected
    /// checked aliases and `with_canonical_borrowed_pointer_memory` applied them.
    pub(super) fn enter<'a>(states: impl IntoIterator<Item = &'a CallReadState>) -> Self {
        let mut previous = Vec::new();
        SOURCES.with(|sources| {
            let mut sources = sources.borrow_mut();
            for state in states {
                let rewritten = &state.state;
                let original = &state.original;
                crate::instrumentation::record_deterministic_work(1);
                if rewritten.memory().same_storage_roots(original) {
                    continue;
                }
                let key = rewritten.memory().storage_root_identity();
                let old = sources.insert(
                    key,
                    ReadSource {
                        _rewritten: rewritten.memory().clone(),
                        original: original.clone(),
                    },
                );
                previous.push((key, old));
            }
        });
        Self {
            previous,
            _thread: PhantomData,
        }
    }
}

impl Drop for CallReadAliasScope {
    fn drop(&mut self) {
        SOURCES.with(|sources| {
            let mut sources = sources.borrow_mut();
            for (key, previous) in self.previous.drain(..).rev() {
                match previous {
                    Some(previous) => {
                        sources.insert(key, previous);
                    }
                    None => {
                        sources.remove(&key);
                    }
                }
            }
        });
    }
}

pub(in crate::kernel) fn source_for(memory: &CMemory) -> Option<CMemory> {
    crate::instrumentation::record_deterministic_work(1);
    SOURCES.with(|sources| {
        sources
            .borrow()
            .get(&memory.storage_root_identity())
            .map(|source| source.original.clone())
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    struct Fixture {
        before: CState,
        rewritten: CallReadState,
        aliases: Vec<(CResourceFact, CResourceFact)>,
        address: Pointer,
        assumptions: PureFactContext,
    }

    fn fixture() -> Fixture {
        let address = Pointer::symbolic(Variable(985_100));
        let slot = Pointer::symbolic(Variable(985_101));
        let formal = Pointer::symbolic(Variable(985_102));
        let actual = Pointer::loaded_value(
            &intern_c_memory(CMemory::new()),
            &Pointer::symbolic(Variable(985_103)),
        );
        let before =
            CState::new().with_memory(CMemory::new().store(slot, CValue::pointer(formal.clone())));
        let aliases = vec![(
            CResourceFact::own_memory(CMemoryRange::new(formal.clone(), 0u32.into(), 1u32.into())),
            CResourceFact::own_memory(CMemoryRange::new(actual.clone(), 0u32.into(), 1u32.into())),
        )];
        let rewritten = CallReadState::new(&before, &aliases);
        let assumptions = PureFactContext::new()
            .assume_condition(ConditionTerm::pointer_equal(formal, actual), true);
        Fixture {
            before,
            rewritten,
            aliases,
            address,
            assumptions,
        }
    }

    fn observe(
        state: &CState,
        address: &Pointer,
        ty: CType,
        assumptions: &PureFactContext,
    ) -> (CValue, ExecutionFacts) {
        let mut paths = crate::kernel::eval::evaluate_logical_memory_load_paths(
            state.memory(),
            address.clone(),
            ty,
            ExecutionFacts::new(),
            vec![],
            assumptions,
        );
        assert_eq!(paths.len(), 1);
        let path = paths.pop().unwrap();
        let CExpressionOutcome::Value(value) = path.outcome else {
            panic!("logical read");
        };
        (value, path.facts)
    }

    fn equality(left: &CValue, right: &CValue) -> ConditionTerm {
        match (left.numeric_value(), right.numeric_value()) {
            (CValue::UInt64(a), CValue::UInt64(b)) => {
                ConditionTerm::uint64_equal(a.clone(), b.clone())
            }
            (CValue::Int32(a), CValue::Int32(b)) => ConditionTerm::equal(a.clone(), b.clone()),
            _ => panic!("fixture type"),
        }
    }

    #[test]
    fn checked_call_read_alias_reaches_shared_closure_and_stays_scoped() {
        let _session = crate::kernel::VerificationSession::enter();
        for ty in [CType::Int32, CType::UInt64] {
            let _word = crate::kernel::eval::WordRepresentationScope::enter(true);
            let mut f = fixture();
            let (original, original_facts) = observe(&f.before, &f.address, ty, &f.assumptions);
            for fact in original_facts {
                f.assumptions = f.assumptions.assume_proposition(fact.proposition().clone());
            }
            let (rewritten, unbridged) = observe(&f.rewritten, &f.address, ty, &f.assumptions);
            assert_ne!(original, rewritten, "exercise different read terms");
            let goal = equality(&rewritten, &original);
            assert!(
                !f.assumptions
                    .contains_known(&Proposition::ConditionIs(goal.clone(), true))
            );
            let baseline = f.assumptions.clone();
            let facts = {
                let _scope = CallReadAliasScope::enter([&f.rewritten]);
                let (_, facts) = observe(&f.rewritten, &f.address, ty, &f.assumptions);
                facts
            };
            assert!(facts.len() > unbridged.len());
            assert!(
                facts.iter().all(|fact| !matches!(
                    fact.proposition(),
                    Proposition::CMemoryLoadable { .. } | Proposition::CMemoryReadDefined { .. }
                )),
                "read value equality grants no access or definedness"
            );
            let mut admitted = baseline.clone();
            for fact in &facts {
                admitted = admitted.assume_proposition(fact.proposition().clone());
            }
            assert!(
                admitted.contains_known(&Proposition::ConditionIs(goal.clone(), true)),
                "checked read equation"
            );
            assert!(
                !baseline.contains_known(&Proposition::ConditionIs(goal.clone(), true)),
                "no branch leakage"
            );
            let (_, after_scope) = observe(&f.rewritten, &f.address, ty, &baseline);
            assert_eq!(after_scope, unbridged, "no retained global alias evidence");
            assert!(
                !baseline.contains_known(&Proposition::ConditionIs(goal.clone(), true)),
                "scope does not leak through later observations"
            );

            let changed =
                f.rewritten
                    .state
                    .clone()
                    .with_memory(f.rewritten.memory().clone().store(
                        f.address.clone(),
                        match ty {
                            CType::Int32 => CValue::Int32(9u32.into()),
                            _ => CValue::UInt64(Bitvector32Term::UInt64Constant(9)),
                        },
                    ));
            let _scope = CallReadAliasScope::enter([&f.rewritten]);
            assert!(
                source_for(changed.memory()).is_none(),
                "a store is not this alias snapshot"
            );
            let (changed_value, changed_facts) = observe(&changed, &f.address, ty, &admitted);
            for fact in changed_facts {
                admitted = admitted.assume_proposition(fact.proposition().clone());
            }
            assert!(
                !admitted.contains_known(&Proposition::ConditionIs(
                    equality(&changed_value, &original),
                    true
                )),
                "an actual overwrite stays different"
            );
        }
    }

    #[test]
    fn checked_call_read_alias_nested_scope_restores_its_source() {
        let _session = crate::kernel::VerificationSession::enter();
        let f = fixture();
        assert!(source_for(f.rewritten.memory()).is_none());
        {
            let _outer = CallReadAliasScope::enter([&f.rewritten]);
            assert!(
                source_for(f.rewritten.memory())
                    .unwrap()
                    .same_storage_roots(f.before.memory())
            );
            {
                let _inner = CallReadAliasScope::enter([&f.rewritten]);
                assert!(source_for(f.rewritten.memory()).is_some());
            }
            assert!(source_for(f.rewritten.memory()).is_some());
        }
        assert!(source_for(f.rewritten.memory()).is_none());
    }

    #[cfg(test)]
    mod scaling_tests {
        include!("../../scaling_tests/kernel/functions/call_read_aliases/tests.rs");
    }
}
