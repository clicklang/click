//! Syntax correspondence for checked rewritten-load evidence. Cached entries
//! contain only written term pairs; memory authority is checked by the caller.
use super::*;

type Differences = PersistentMap<(u64, u64), (KernelTerm, KernelTerm)>;
thread_local! {
    static DIFFERENCES: std::cell::RefCell<HashMap<(u64, u64), Option<Differences>>> = Default::default();
}

pub(in crate::kernel) fn clear_rewritten_load_syntax_cache() {
    DIFFERENCES.with(|cache| cache.borrow_mut().clear());
}

/// Corresponding unmatched leaves, preserving the native walk's exact
/// operators, cast encodings and literal tags. No equality facts are read.
pub(super) fn differences(left: &KernelTerm, right: &KernelTerm) -> Option<Differences> {
    DIFFERENCES.with(|cache| {
        let mut cache = cache.borrow_mut();
        let mut pending = vec![(left, right, false)];
        while let Some((a, b, finish)) = pending.pop() {
            if crate::instrumentation::deadline_exceeded_with_work(1) {
                return None;
            }
            let key = (a.id(), b.id());
            if cache.contains_key(&key) {
                continue;
            }
            let av = MachineOperandView::Shared(a);
            let bv = MachineOperandView::Shared(b);
            let same_atom = a == b
                || av
                    .variable()
                    .zip(bv.variable())
                    .is_some_and(|(a, b)| a == b)
                || av.literal().zip(bv.literal()).is_some_and(|(a, b)| a == b)
                || a.machine_conversion_leaf()
                    .zip(b.machine_conversion_leaf())
                    .is_some_and(|(a, b)| a == b);
            if same_atom {
                cache.insert(key, Some(Differences::default()));
                continue;
            }
            let children = match (a.node(), b.node()) {
                (
                    KernelTermNode::MachineIf { arguments: aa },
                    KernelTermNode::MachineIf { arguments: ba },
                ) if a.ty() == b.ty() => aa.iter().zip(ba).collect(),
                (
                    KernelTermNode::BoolCompare {
                        format: af,
                        relation: ar,
                        arguments: aa,
                    },
                    KernelTermNode::BoolCompare {
                        format: bf,
                        relation: br,
                        arguments: ba,
                    },
                ) if af == bf && ar == br => aa.iter().zip(ba).collect(),
                (
                    KernelTermNode::BoolEqual { arguments: aa },
                    KernelTermNode::BoolEqual { arguments: ba },
                ) => aa.iter().zip(ba).collect(),
                (
                    KernelTermNode::MachineBinary {
                        format: af,
                        operator: ao,
                        arguments: aa,
                    },
                    KernelTermNode::MachineBinary {
                        format: bf,
                        operator: bo,
                        arguments: ba,
                    },
                ) => {
                    if af != bf || ao != bo {
                        cache.insert(key, None);
                        continue;
                    }
                    vec![(&aa[0], &ba[0]), (&aa[1], &ba[1])]
                }
                (
                    KernelTermNode::MachineUnary {
                        format: af,
                        operator: ao,
                        operand: aa,
                    },
                    KernelTermNode::MachineUnary {
                        format: bf,
                        operator: bo,
                        operand: ba,
                    },
                ) => {
                    if af != bf || ao != bo {
                        cache.insert(key, None);
                        continue;
                    }
                    vec![(aa, ba)]
                }
                (
                    KernelTermNode::MachineCast {
                        encoding: ae,
                        source: af,
                        destination: at,
                        operand: aa,
                    },
                    KernelTermNode::MachineCast {
                        encoding: be,
                        source: bf,
                        destination: bt,
                        operand: ba,
                    },
                ) => {
                    if ae != be || af != bf || at != bt {
                        cache.insert(key, None);
                        continue;
                    }
                    vec![(aa, ba)]
                }
                // Both are unary in the native walk, but name different operators.
                (KernelTermNode::MachineUnary { .. }, KernelTermNode::MachineCast { .. })
                | (KernelTermNode::MachineCast { .. }, KernelTermNode::MachineUnary { .. }) => {
                    cache.insert(key, None);
                    continue;
                }
                _ => {
                    cache.insert(
                        key,
                        Some(Differences::default().with_inserted(key, (a.clone(), b.clone()))),
                    );
                    continue;
                }
            };
            if !finish {
                pending.push((a, b, true));
                for (a, b) in children {
                    pending.push((a, b, false));
                }
                continue;
            }
            let mut result = Some(Differences::default());
            for (a, b) in children {
                let Some(next) = &cache[&(a.id(), b.id())] else {
                    result = None;
                    break;
                };
                let current = result.take().unwrap();
                let (large, small) = if current.len() >= next.len() {
                    (&current, next)
                } else {
                    (next, &current)
                };
                let mut merged = large.clone();
                if !large.shares_root_with(small) {
                    for (key, value) in small.iter() {
                        if crate::instrumentation::deadline_exceeded_with_work(1) {
                            return None;
                        }
                        merged = merged.with_inserted(*key, value.clone());
                    }
                }
                result = Some(merged);
            }
            cache.insert(key, result);
        }
        cache[&(left.id(), right.id())].clone()
    })
}

/// Explicit native evidence still owns native operands. Materialize only its
/// selected leaf, never the arithmetic traversed to find that leaf.
pub(super) fn evidence_operand(term: &KernelTerm) -> Option<MachineTerm> {
    let view = MachineOperandView::Shared(term);
    view.literal()
        .or_else(|| view.read_source().map(|leaf| leaf.into_owned()))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn retained_load_differences_preserve_native_operator_and_binder_rules() {
        let _session = VerificationSession::enter();
        let memory = intern_c_memory(Memory::new());
        let pointer = Pointer {
            block: PointerBlock::Symbolic(Variable(1005600)),
            offset: PointerOffsetTerm::Constant(0),
        };
        let named = MachineTerm::Variable(crate::kernel::eval::load_variable_for_cell(
            &memory,
            &pointer,
            LoadKind::Int32,
        ));
        let structural = MachineTerm::MemoryLoad(memory, Box::new(pointer), LoadKind::Int32);
        for load in [named, structural] {
            let one = MachineTerm::constant(1);
            let facts = ProofFacts::from_ordered(&[Proposition::ConditionIs(
                ConditionTerm::equal(load.clone(), one.clone()),
                true,
            )]);
            let binary = |op, left| MachineTerm::Binary {
                format: MachineIntegerType::Int32,
                op,
                left: Box::new(left),
                right: Box::new(MachineTerm::constant(7)),
            };
            let cast = |value| MachineTerm::Cast {
                spelling: MachineCastSpelling::Generic,
                from: MachineIntegerType::UInt32,
                to: MachineIntegerType::Int32,
                value: Box::new(value),
            };
            let native = |value| {
                Proposition::ConditionIs(
                    ConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::Equal,
                        left: Box::new(value),
                        right: Box::new(MachineTerm::constant(0)),
                    },
                    true,
                )
            };
            let shared = |value| {
                Proposition::ConditionIs(
                    ConditionTerm::IntegerEqual(
                        IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
                            MachineIntegerType::Int32,
                            value,
                        ))
                        .into(),
                        IntegerTerm::constant_i64(0).into(),
                    ),
                    true,
                )
            };
            for (a, b, expected, bound_expected) in [
                (load.clone(), one.clone(), true, true),
                (load.clone(), MachineTerm::constant(2), false, false),
                (
                    binary(MachineBinaryOp::Add, load.clone()),
                    binary(MachineBinaryOp::Add, one.clone()),
                    true,
                    false,
                ),
                (
                    binary(MachineBinaryOp::Add, load.clone()),
                    binary(MachineBinaryOp::Subtract, one.clone()),
                    false,
                    false,
                ),
                (cast(load.clone()), cast(one), true, false),
                (
                    binary(MachineBinaryOp::Add, load.clone()),
                    binary(MachineBinaryOp::Add, load),
                    true,
                    true,
                ),
            ] {
                for bound in [false, true] {
                    let bind = |body| {
                        if bound {
                            Proposition::ForAll {
                                name: Default::default(),
                                var: Variable(1005601),
                                sort: Sort::CInt32,
                                body: Box::new(body),
                            }
                        } else {
                            body
                        }
                    };
                    let expected = if bound { bound_expected } else { expected };
                    assert_eq!(
                        facts
                            .with_checked_rewritten_loads(
                                &bind(native(a.clone())),
                                &bind(native(b.clone()))
                            )
                            .is_some(),
                        expected
                    );
                    assert_eq!(
                        facts
                            .with_checked_rewritten_loads(
                                &bind(shared(a.clone())),
                                &bind(shared(b.clone()))
                            )
                            .is_some(),
                        expected
                    );
                }
            }
        }
    }

    #[test]
    fn retained_load_evidence_cannot_use_an_outer_fact_for_a_bound_address() {
        let _session = VerificationSession::enter();
        let binder = Variable(1005699);
        let read = MachineTerm::MemoryLoad(
            intern_c_memory(Memory::new()),
            Box::new(Pointer::symbolic(binder)),
            LoadKind::Int32,
        );
        let equal = |value| {
            Proposition::ConditionIs(ConditionTerm::equal(value, MachineTerm::constant(1)), true)
        };
        let facts = ProofFacts::from_ordered(&[equal(read.clone())]);
        let bind = |body| Proposition::ForAll {
            name: Default::default(),
            var: binder,
            sort: Sort::CInt32,
            body: Box::new(body),
        };
        assert!(
            facts
                .with_checked_rewritten_loads(
                    &bind(equal(read)),
                    &bind(equal(MachineTerm::constant(1))),
                )
                .is_none()
        );
    }

    fn observed(value: SharedMachineIntegerTerm) -> Proposition {
        Proposition::ConditionIs(
            ConditionTerm::IntegerEqual(
                IntegerTerm::Machine(value).into(),
                IntegerTerm::constant_i64(0).into(),
            ),
            true,
        )
    }

    #[test]
    fn mixed_read_evidence_refuses_opaque_mismatch_without_export() {
        let _session = VerificationSession::enter();
        let ty = MachineIntegerType::Int32;
        let x = KernelTerm::variable(KernelType::C(ty.c_type()), Variable(1007330));
        let sum = KernelTerm::machine_binary_shared(ty, MachineBinaryOp::Add, [x.clone(), x]);
        let opaque = MachineTerm::PureFunctionApplication {
            name: "read_evidence_opaque".into(),
            arguments: vec![MachineTerm::constant(1), MachineTerm::constant(2)],
        };
        let native = SharedMachineIntegerTerm::intern(ty, opaque);
        assert!(native.shared_operand().is_none());
        let a = observed(SharedMachineIntegerTerm::from_shared(ty, sum).unwrap());
        let b = observed(native);
        let before = KernelTermExport::machine_export_count();
        assert!(
            ProofFacts::default()
                .with_checked_rewritten_loads(&a, &b)
                .is_none()
        );
        assert!(
            ProofFacts::default()
                .with_checked_rewritten_loads(&b, &a)
                .is_none()
        );
        assert_eq!(KernelTermExport::machine_export_count(), before);
    }

    #[test]
    fn arithmetic_read_evidence_keeps_its_exact_source_authority() {
        let _session = VerificationSession::enter();
        let ty = MachineIntegerType::Int32;
        let pointer = Pointer::symbolic(Variable(1007340));
        let load = MachineTerm::MemoryLoad(
            intern_c_memory(Memory::new()),
            pointer.into(),
            LoadKind::Int32,
        );
        let sum = MachineTerm::add(
            MachineTerm::Variable(Variable(1007341)),
            MachineTerm::Variable(Variable(1007341)),
        );
        let read = SharedMachineIntegerTerm::intern(ty, load.clone());
        let arithmetic = SharedMachineIntegerTerm::intern(ty, sum.clone());
        let source = Proposition::ConditionIs(ConditionTerm::equal(load, sum), true);
        let facts = ProofFacts::from_ordered(&[source]);
        let (a, b) = (observed(read), observed(arithmetic));
        let before = KernelTermExport::machine_export_count();
        assert!(facts.with_checked_rewritten_loads(&a, &b).is_some());
        assert!(
            ProofFacts::default()
                .with_checked_rewritten_loads(&a, &b)
                .is_none()
        );
        assert_eq!(KernelTermExport::machine_export_count(), before);
    }

    #[test]
    fn shared_read_evidence_preserves_stored_and_origin_chain_sources() {
        let _session = VerificationSession::enter();
        let ty = MachineIntegerType::Int32;
        let pointer = Memory::global_pointer("shared-read-source");
        let sum = MachineTerm::add(
            MachineTerm::Variable(Variable(1007350)),
            MachineTerm::Variable(Variable(1007350)),
        );
        let initial = Memory::new().with_block("shared-read-source", 4);
        let stored = initial
            .clone()
            .store(pointer.clone(), ProgramValue::Int32(sum.clone()));
        let load = |memory| {
            MachineTerm::MemoryLoad(
                intern_c_memory(memory),
                pointer.clone().into(),
                LoadKind::Int32,
            )
        };
        let observe = |value| observed(SharedMachineIntegerTerm::intern(ty, value));
        let arithmetic = observe(sum.clone());
        let stored_read = observe(load(stored));
        let before = KernelTermExport::machine_export_count();
        for (a, b) in [(&stored_read, &arithmetic), (&arithmetic, &stored_read)] {
            assert!(
                ProofFacts::default()
                    .with_checked_rewritten_loads(a, b)
                    .is_some()
            );
        }
        let early = load(initial.clone());
        let later = load(initial.clone().with_block("unrelated", 4));
        let facts = ProofFacts::from_ordered(&[Proposition::ConditionIs(
            ConditionTerm::Compare {
                format: MachineIntegerType::UInt32,
                relation: CompareRelation::Equal,
                left: early.clone().into(),
                right: sum.into(),
            },
            true,
        )]);
        let later = observe(later);
        assert!(
            facts
                .with_checked_rewritten_loads(&later, &arithmetic)
                .is_some()
        );
        assert!(
            ProofFacts::default()
                .with_checked_rewritten_loads(&later, &arithmetic)
                .is_none()
        );
        let overwritten = observe(load(initial.store(
            pointer.clone(),
            ProgramValue::Int32(MachineTerm::constant(7)),
        )));
        assert!(
            facts
                .with_checked_rewritten_loads(&overwritten, &arithmetic)
                .is_none()
        );
        assert_eq!(KernelTermExport::machine_export_count(), before);
    }

    mod scaling_tests {
        use super::*;
        include!("../../../scaling_tests/kernel/proof/facts/rewritten_loads.rs");
    }
}
