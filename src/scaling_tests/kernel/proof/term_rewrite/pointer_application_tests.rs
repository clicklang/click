// Scaling tests of `src/kernel/proof/term_rewrite/pointer_application_tests.rs`: deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn pure_pointer_dag_substitution_and_capture_collection_scale_linearly() {
    let source = Variable(410);
    let replacement = Address::symbolic(Variable(411));
    let mut measurements = Vec::new();
    for depth in [16, 32, 64] {
        let mut input = Address::symbolic(source);
        let mut expected = replacement.clone();
        for _ in 0..depth {
            input = call("pair", vec![argument(input.clone()), argument(input)]);
            expected = call("pair", vec![argument(expected.clone()), argument(expected)]);
        }
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            let mut rewrite = TermRewrite::for_pointer_variable(source, &replacement);
            let result = rewrite.pointer(&input);
            assert_eq!(rewrite.refusal(), None);
            result
        });
        assert!(result == expected);
        let (_, capture_work) = crate::instrumentation::measure_deterministic_work(|| {
            let mut variables = CarrierVariables::for_rewrite(false);
            collect_pointer_carriers(&input, &mut variables);
            assert_eq!(variables.program_values, BTreeSet::from([source]));
            let mut captured = BTreeSet::new();
            crate::kernel::prelude::collect_proposition_capture_variables(
                &Proposition::condition_is(
                    OldConditionTerm::AddressEqual(
                        Box::new(input.clone()),
                        Box::new(input.clone()),
                    ),
                    true,
                ),
                &mut captured,
            );
            assert!(captured.contains(&source));
        });
        measurements.push(work + capture_work);
    }
    for pair in measurements.windows(2) {
        assert!(pair[1] <= 3 * pair[0] + 32, "work: {measurements:?}");
    }
}

#[test]
fn pure_pointer_legacy_scalar_substitution_visits_the_shared_dag_once() {
    let variable = Variable(710);
    let replacement = OldMachineTerm::constant(9);
    let mut measurements = Vec::new();
    for depth in [8, 16, 32] {
        let mut input = call(
            "scalar",
            vec![PureFunctionArgument::Value(ProgramValue::Int32(
                OldMachineTerm::Variable(variable),
            ))],
        );
        let mut expected = call(
            "scalar",
            vec![PureFunctionArgument::Value(ProgramValue::Int32(
                replacement.clone(),
            ))],
        );
        for _ in 0..depth {
            input = call("pair", vec![argument(input.clone()), argument(input)]);
            expected = call("pair", vec![argument(expected.clone()), argument(expected)]);
        }
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::kernel::prelude::substitute_bitvector_variable_in_pointer(
                &input,
                variable,
                &replacement,
            )
        });
        assert!(result == expected);
        measurements.push(work);
    }
    for pair in measurements.windows(2) {
        assert!(pair[1] <= 3 * pair[0] + 32, "work: {measurements:?}");
    }
}

#[test]
fn full_pointer_substitution_visits_shared_read_origins_once() {
    let _session = VerificationSession::enter();
    let memory = intern_memory(SymbolicMemory::new());
    let p = OldPointer::new(Address::symbolic(Variable(810)), ProgramType::Int32Pointer);
    let q = OldPointer::new(Address::symbolic(Variable(811)), ProgramType::Int32Pointer);
    let mut costs = Vec::new();
    for depth in [16, 32, 64] {
        let mut input = p.address().clone();
        let mut expected = q.address().clone();
        for _ in 0..depth {
            input = Address::loaded_value(
                &memory,
                &call("pair", vec![argument(input.clone()), argument(input)]),
            );
            expected = Address::loaded_value(
                &memory,
                &call("pair", vec![argument(expected.clone()), argument(expected)]),
            );
        }
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            let mut rewrite = TermRewrite::for_pointer_value_exact(&p, &q);
            let result = rewrite.pointer(&input);
            assert_eq!(rewrite.refusal(), None);
            result
        });
        assert_eq!(result, expected);
        costs.push(work);
    }
    assert!(costs[0] > 0);
    for pair in costs.windows(2) {
        assert!(pair[1] <= 3 * pair[0] + 32, "{costs:?}");
    }
}

#[test]
fn full_pointer_resource_relationship_rewriting_scales_with_its_arguments() {
    let mut samples = Vec::new();
    for size in [16usize, 64, 256, 1024] {
        let _session = crate::kernel::VerificationSession::enter();
        let memory = intern_memory(SymbolicMemory::new());
        let source = OldPointer::from_read(
            Address::symbolic(Variable(425_100)),
            ProgramType::Int32Pointer,
            &memory,
            &Address::symbolic(Variable(425_101)),
        );
        let target = OldPointer::new(
            Address::symbolic(Variable(425_102)),
            ProgramType::Int32Pointer,
        );
        let relationship = |value: &OldPointer| Proposition::ResourceSeparate {
            left: Box::new(Resource::Memory(MemoryRange::from_pointer_value(
                value,
                0u32.into(),
                1u32.into(),
                4,
            ))),
            right: Box::new(Resource::Composite {
                name: "many".into(),
                arguments: vec![
                    AlgebraicValue::Program(ProgramValue::Pointer(value.clone()));
                    size
                ]
                .into(),
            }),
        };
        let input = relationship(&source);
        let (actual, work) = crate::instrumentation::measure_deterministic_work(|| {
            let mut rewrite = TermRewrite::for_pointer_value_exact(&source, &target);
            let result = rewrite.proposition(&input);
            assert!(rewrite.refusal().is_none());
            result
        });
        assert_eq!(actual, relationship(&target));
        samples.push(work);
    }
    for pair in samples.windows(2) {
        assert!(pair[1] <= pair[0] * 5 + 64, "{samples:?}");
    }
}

#[test]
fn displaced_full_pointer_rewrite_scales_with_the_selected_offset() {
    for symbolic in [false, true] {
        let mut costs = Vec::new();
        for size in [8_u64, 32, 128] {
            let parameter = |id| {
                OldPointer::new(
                    Address {
                        base: AddressBase::ExternalArgument,
                        offset: OldAddressOffset::scale_int32(
                            OldMachineTerm::Variable(Variable(id)),
                            1,
                        ),
                    },
                    ProgramType::UInt8Pointer,
                )
            };
            let base = parameter(916_221);
            let source = if symbolic {
                OldPointer::new(
                    Address::symbolic(Variable(916_222)),
                    ProgramType::UInt8Pointer,
                )
            } else {
                parameter(916_222)
            };
            let target = base.clone().with_address(base.address().offset_by_bytes(2));
            let delta = (0..size).fold(OldAddressOffset::Constant(0), |offset, index| {
                OldAddressOffset::add(
                    offset,
                    OldAddressOffset::scale_int32(
                        OldMachineTerm::Variable(Variable(920_000 + index)),
                        1,
                    ),
                )
            });
            let input = source.clone().with_address(Address {
                base: source.address().base.clone(),
                offset: OldAddressOffset::add(source.address().offset.clone(), delta.clone()),
            });
            let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                let mut rewrite = TermRewrite::for_pointer_value_exact(&source, &target);
                let result = rewrite.value(&ProgramValue::Pointer(input));
                assert_eq!(rewrite.refusal(), None);
                result
            });
            let ProgramValue::Pointer(result) = result else {
                panic!("pointer type")
            };
            assert_eq!(result.address().base, target.address().base);
            assert_eq!(
                crate::kernel::eval::canonical_offset_term(&result.address().offset),
                crate::kernel::eval::canonical_offset_term(&OldAddressOffset::add(
                    target.address().offset.clone(),
                    delta
                ))
            );
            assert_eq!(result.provenance(), target.provenance());
            assert_eq!(result.bounds_owner(), target.bounds_owner());
            assert!(
                work >= usize::try_from(size).unwrap(),
                "{symbolic}: {size}: {work}"
            );
            costs.push(work);
        }
        for pair in costs.windows(2) {
            assert!(pair[1] <= pair[0] * 5 + 64, "{symbolic}: {costs:?}");
        }
    }
}

#[test]
fn integer_address_rewrite_visits_a_shared_pointer_dag_once() {
    let word = OldMachineTerm::Variable(Variable(912));
    let replacement = OldMachineTerm::uint64_constant(1);
    let mut costs = Vec::new();
    for depth in [8, 16, 32] {
        let mut input = Address::from_integer_address(OldMachineTerm::uint64_bitwise_and(
            word.clone(),
            OldMachineTerm::uint64_constant(!3),
        ));
        for _ in 0..depth {
            input = call("pair", vec![argument(input.clone()), argument(input)]);
        }
        let (output, work) = crate::instrumentation::measure_deterministic_work(|| {
            let mut rewrite = TermRewrite::for_bits(&word, &replacement);
            let output = rewrite.pointer(&input);
            assert_eq!(rewrite.refusal(), None);
            output
        });
        // Rewriting retains each C pointer's bounds metadata; constructing
        // a fresh typed null would instead introduce a known null bounds.
        // Check the shared application's shape and selected numeric leaf.
        let mut leaf = &output;
        for _ in 0..depth {
            let AddressBase::PureFunctionApplication(application) = &leaf.base else {
                panic!("lost a shared application")
            };
            assert_eq!(application.name(), "pair");
            let [
                PureFunctionArgument::Value(ProgramValue::Pointer(left)),
                PureFunctionArgument::Value(ProgramValue::Pointer(right)),
            ] = application.arguments()
            else {
                panic!("lost pointer arguments")
            };
            assert!(left == right, "the shared branches must stay identical");
            leaf = left.address();
        }
        assert_eq!(leaf, &Address::null());
        costs.push(work);
    }
    assert!(costs[0] > 0);
    for pair in costs.windows(2) {
        assert!(pair[1] <= 3 * pair[0] + 32, "{costs:?}");
    }
}

#[test]
fn integer_address_rewrite_ignores_unrelated_interned_applications() {
    let word = OldMachineTerm::Variable(Variable(913));
    let replacement = OldMachineTerm::uint64_constant(1);
    let mut costs = Vec::new();
    let mut repeated_costs = Vec::new();
    for size in [0, 64, 256] {
        // Compare cold queries at each size, and repeated queries separately.
        // Typed application keys populate the session's observation cache.
        let _session = crate::kernel::VerificationSession::enter();
        let input = Address::from_integer_address(OldMachineTerm::uint64_bitwise_and(
            word.clone(),
            OldMachineTerm::uint64_constant(!3),
        ));
        let _unrelated = (0..size)
            .map(|i| {
                call(
                    "unrelated",
                    vec![argument(Address::symbolic(Variable(20_000 + i)))],
                )
            })
            .collect::<Vec<_>>();
        let (output, work) = crate::instrumentation::measure_deterministic_work(|| {
            TermRewrite::for_bits(&word, &replacement).pointer(&input)
        });
        assert_eq!(output, Address::null());
        costs.push(work);
        let (output, work) = crate::instrumentation::measure_deterministic_work(|| {
            TermRewrite::for_bits(&word, &replacement).pointer(&input)
        });
        assert_eq!(output, Address::null());
        repeated_costs.push(work);
    }
    assert!(costs[0] > 0);
    assert_eq!(costs, vec![costs[0]; 3]);
    assert_eq!(repeated_costs, vec![repeated_costs[0]; 3]);
}

#[test]
fn exact_displacement_rewrite_visits_shared_subexpressions_once() {
    let _session = VerificationSession::enter();
    for depth in [4, 8, 12, 16] {
        let from = OldAddressOffset::Variable(Variable(1008500 + depth as u64));
        let to = OldAddressOffset::Constant(1);
        let doubling_chain = |leaf: &OldAddressOffset| {
            let mut root = KernelAddressOffset::import(leaf);
            for _ in 0..depth {
                root = KernelAddressOffset::Add([root.clone(), root])
                    .into_shared()
                    .unwrap();
            }
            root
        };
        let source = StoredPointerOffset::from_rewritten_root(doubling_chain(&from));
        let expected = doubling_chain(&to);
        let (output, work) = crate::instrumentation::measure_deterministic_work(|| {
            TermRewrite::for_pointer_offset_exact(&from, &to).contract_offset(&source)
        });
        assert_eq!(output.root(), Some(&expected));
        assert!(!source.has_cached_native_offset());
        assert!(!output.has_cached_native_offset());
        assert!(work <= 20 * depth, "depth={depth}, work={work}");
    }
}
