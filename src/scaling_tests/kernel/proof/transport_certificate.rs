use super::*;

#[test]
fn transport_certificate_does_not_walk_prior_memory_history() {
    for cached in [false, true] {
        let costs = [4, 16, 64, 256].map(|history| {
            let _session = crate::kernel::VerificationSession::enter();
            let _reads = typed_reads::ReadScope::enter();
            let (certificate, goal) = tests::fixture(history, cached);
            let (result, cost) =
                crate::instrumentation::measure_deterministic_work(|| certificate.apply(|_| true));
            assert_eq!(result.unwrap(), goal);
            assert!(cost > 0);
            cost
        });
        assert!(
            costs.iter().all(|cost| *cost == costs[0]),
            "cached={cached}: {costs:?}"
        );
    }
}

#[test]
fn transport_certificate_work_is_linear_in_explicit_nodes() {
    let costs = [1u64, 4, 16, 64].map(|length| {
        let _session = crate::kernel::VerificationSession::enter();
        let _reads = typed_reads::ReadScope::enter();
        let equality = |left: u64, right: u64| {
            Proposition::ConditionIs(
                ConditionTerm::PointerValueEqual(
                    Box::new(CPointerValue::new(
                        Pointer::symbolic(Variable(8_390_000 + left)),
                        CType::Int32Pointer,
                    )),
                    Box::new(CPointerValue::new(
                        Pointer::symbolic(Variable(8_390_000 + right)),
                        CType::Int32Pointer,
                    )),
                ),
                true,
            )
        };
        let mut certificate = TransportCertificate {
            nodes: vec![TransportNode::Premise {
                proposition: equality(0, 1),
                result: equality(0, 1),
            }],
            conclusion: 0,
        };
        let mut previous = 0;
        for i in 1..length {
            let next = certificate.nodes.len();
            certificate.nodes.push(TransportNode::Premise {
                proposition: equality(i, i + 1),
                result: equality(i, i + 1),
            });
            certificate.nodes.push(TransportNode::Transitive {
                left: previous,
                right: next,
                result: equality(0, i + 1),
            });
            previous = next + 1;
        }
        let goal = equality(0, length);
        certificate.conclusion = previous;
        let (result, cost) =
            crate::instrumentation::measure_deterministic_work(|| certificate.apply(|_| true));
        assert_eq!(result.unwrap(), goal);
        (length, cost)
    });
    assert!(costs.windows(2).all(|p| p[1].1 <= p[0].1 * 8), "{costs:?}");
}

#[test]
fn transport_certificate_scalar_names_do_not_walk_prior_memory_history() {
    let costs = [4, 16, 64, 256].map(|history| {
        let _session = crate::kernel::VerificationSession::enter();
        let _reads = typed_reads::ReadScope::enter();
        let (mut certificate, _) = tests::fixture(history, false);
        let TransportNode::Premise {
            proposition: Proposition::CMemoryMutatesOnly { before, after, .. },
            ..
        } = &certificate.nodes[0]
        else {
            unreachable!()
        };
        let before = intern_c_memory(before.clone());
        let after = intern_c_memory(after.clone());
        let TransportNode::Premise {
            proposition,
            result,
        } = &mut certificate.nodes[1]
        else {
            unreachable!()
        };
        let Proposition::CResourceSeparate { right, .. } = proposition else {
            unreachable!()
        };
        let CResource::Memory(range) = right.as_ref() else {
            unreachable!()
        };
        let (address, _) = range.byte_footprint();
        *right = Box::new(CResource::Memory(CMemoryRange::new_with_element_width(
            address.clone(),
            0u32.into(),
            1u32.into(),
            4,
        )));
        *result = proposition.clone();
        let read = |memory: &SharedCMemory| {
            Box::new(integer_bits(tests::observe(memory.memory(), &address, CType::Int32)).unwrap())
        };
        let goal = Proposition::ConditionIs(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: read(&after),
                right: read(&before),
            },
            true,
        );
        certificate.nodes[2] = TransportNode::Preserve {
            effect: 0,
            separation: 1,
            result: goal.clone(),
        };
        let (result, cost) =
            crate::instrumentation::measure_deterministic_work(|| certificate.apply(|_| true));
        assert_eq!(result.unwrap(), goal);
        cost
    });
    assert!(costs[0] > 0);
    assert!(costs.iter().all(|cost| *cost == costs[0]), "{costs:?}");
}

#[test]
fn transport_certificate_uses_selected_observations_without_scanning_the_registry() {
    let costs = [4, 16, 64, 256].map(|unrelated| {
        let _session = crate::kernel::VerificationSession::enter();
        let _reads = typed_reads::ReadScope::enter();
        let (certificate, goal) = tests::fixture(2, false);
        let memory = CMemory::new();
        for index in 0..unrelated {
            tests::observe(
                &memory,
                &Pointer::symbolic(Variable(8_410_000 + index)),
                CType::Int32Pointer,
            );
        }
        let (result, cost) =
            crate::instrumentation::measure_deterministic_work(|| certificate.apply(|_| true));
        assert_eq!(result.unwrap(), goal);
        cost
    });
    assert!(costs[0] > 0);
    assert!(costs.iter().all(|cost| *cost == costs[0]), "{costs:?}");
}
