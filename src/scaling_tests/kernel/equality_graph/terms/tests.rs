// Scaling tests of `src/kernel/equality_graph/terms.rs` (module `tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn addition_congruence_late_merge_work_scales_with_affected_parents() {
    for size in [16u64, 64, 256, 1024] {
        let mut graph = EqualityGraph::default();
        for i in 0..size {
            graph.add_offset_equality(&add(var(0), var(10 + i)), &var(10_000 + i));
            graph.add_offset_equality(&add(var(1), var(10 + i)), &var(20_000 + i));
        }
        let ((_, work), map_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                graph.add_offset_equality(&var(0), &var(1));
                for i in 0..size {
                    assert!(graph.are_offsets_equal(&var(10_000 + i), &var(20_000 + i)));
                }
            })
        });
        let logarithm = size.ilog2() as usize + 1;
        assert!(work < 80 * size as usize, "size={size}, work={work}");
        assert!(
            map_work < 512 * size as usize * logarithm,
            "size={size}, map work={map_work}"
        );
    }
}

#[test]
fn addition_congruence_forks_do_not_reindex_unrelated_parents() {
    for size in [16u64, 64, 256, 1024] {
        let mut graph = EqualityGraph::default();
        for i in 0..size {
            graph.add_offset_equality(&add(var(0), var(10 + i)), &var(10_000 + i));
        }
        let ((_, work), map_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                for i in 0..size {
                    let mut branch = graph.clone();
                    // Argument order must not move the class with many
                    // parents under this newly registered singleton.
                    branch.add_offset_equality(&var(20_000 + i), &var(0));
                    assert!(branch.are_offsets_equal(&add(var(20_000 + i), var(10)), &var(10_000)));
                }
            })
        });
        let logarithm = size.ilog2() as usize + 1;
        assert!(work < 100 * size as usize, "size={size}, work={work}");
        assert!(
            map_work < 512 * size as usize * logarithm,
            "size={size}, map work={map_work}"
        );
        assert!(!graph.are_offsets_equal(&var(20_000), &var(0)));
    }
}

#[test]
fn offset_graph_construction_and_fork_queries_scale_with_indexed_work() {
    let offset = |id| PointerOffsetTerm::scaled_int32_node(MachineTerm::Variable(Variable(id)), 4);
    for size in [16u64, 64, 256, 1024] {
        let ((graph, work), map_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                let mut graph = EqualityGraph::default();
                for i in 0..size {
                    graph.add_offset_equality(&offset(i), &offset(i + 1));
                    assert!(graph.are_offsets_equal(&offset(0), &offset(i + 1)));
                }
                graph
            })
        });
        let logarithm = size.ilog2() as usize + 1;
        assert!(work < 40 * size as usize, "size={size}, work={work}");
        assert!(
            map_work < 160 * size as usize * logarithm,
            "size={size}, map work={map_work}"
        );
        let (_, fork_work) = crate::persistent::measure_persistent_work(|| {
            let mut branch = graph.clone();
            branch.add_offset_equality(&offset(size), &offset(size + 1));
            assert!(branch.are_offsets_equal(&offset(0), &offset(size + 1)));
            assert!(!graph.are_offsets_equal(&offset(0), &offset(size + 1)));
        });
        assert!(
            fork_work < 160 * logarithm,
            "size={size}, fork work={fork_work}"
        );
    }
}

#[test]
fn late_wide_zero_reindexes_only_its_existing_offsets() {
    let mut measured = Vec::new();
    for size in [4u64, 16, 64] {
        let mut graph = EqualityGraph::default();
        let scaled = |base: &Pointer, value| Pointer {
            block: base.block.clone(),
            offset: PointerOffsetTerm::scaled_int64_node(
                MachineTerm::Variable(Variable(value)),
                4,
                true,
            ),
        };
        for i in 0..size {
            let base = Pointer::symbolic(Variable(896_000 + i));
            assert!(!graph.are_equal(&scaled(&base, 897_000 + i), &base));
        }
        let base = Pointer::symbolic(Variable(898_000));
        let pointer = scaled(&base, 898_001);
        assert!(!graph.are_equal(&pointer, &base));
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            graph.add_uint64_equality(
                &MachineTerm::Variable(Variable(898_001)),
                &MachineTerm::uint64_constant(0),
            );
        });
        assert!(graph.are_equal(&pointer, &base));
        measured.push(work);
    }
    assert!(
        measured.iter().all(|work| *work <= measured[0] + 32),
        "unrelated wide offsets increased selected propagation: {measured:?}"
    );
}

#[test]
fn shared_machine_prefix_registration_is_linear_and_branch_local() {
    use crate::kernel::{
        IntegerTerm, KernelTerm, KernelType, ProgramType, SharedMachineIntegerTerm,
    };
    let mut baseline = Vec::new();
    for unrelated in [0, 32, 64] {
        let mut samples = Vec::new();
        for size in [8, 32, 96] {
            let _session = crate::kernel::VerificationSession::enter();
            let mut graph = EqualityGraph::default();
            for i in 0..unrelated {
                graph.add_int32_equality(
                    &MachineTerm::Variable(Variable(960000 + i)),
                    &MachineTerm::Variable(Variable(970000 + i)),
                );
            }
            let format = MachineIntegerType::Int64;
            let mut term =
                KernelTerm::variable(KernelType::C(ProgramType::Int64), Variable(980000));
            let other =
                IntegerTerm::from_machine(format, MachineTerm::Variable(Variable(980001))).unwrap();
            let mut retained = Vec::new();
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                for _ in 0..size {
                    term = KernelTerm::arithmetic_binary(
                        format,
                        MachineBinaryOp::Add,
                        [term.clone(), term.clone()],
                    )
                    .unwrap();
                    let observation =
                        SharedMachineIntegerTerm::from_shared(format, term.clone()).unwrap();
                    let source = IntegerTerm::Machine(observation.clone());
                    assert!(graph.are_integer_equal(&source, &source));
                    assert!(!graph.are_integer_equal(&source, &other));
                    let comparison =
                        ConditionTerm::integer_less_equal(source.clone(), other.clone());
                    let view = crate::kernel::machine_integer::comparison::native_comparison_view(
                        &comparison,
                        true,
                    )
                    .unwrap();
                    let crate::kernel::machine_integer::comparison::ComparisonOperand::Observation(
                        actual,
                    ) = &view.operands[0]
                    else {
                        panic!("shared observation")
                    };
                    assert_eq!(actual.id(), observation.id());
                    assert!(!observation.has_boxed_operand());
                    retained.push(source);
                    for operator in [MachineBinaryOp::Divide, MachineBinaryOp::ShiftRight] {
                        // Build through the structural bridge with only a root
                        // replacement, retaining the large shared children.
                        let node = crate::kernel::KernelTerm::machine_binary_shared(
                            format,
                            operator,
                            [term.clone(), term.clone()],
                        );
                        let observation =
                            SharedMachineIntegerTerm::from_shared(format, node).unwrap();
                        let source = IntegerTerm::Machine(observation.clone());
                        assert!(graph.are_integer_equal(&source, &source));
                        assert!(!observation.has_boxed_operand());
                        retained.push(source);
                    }
                }
            });
            samples.push((size, work));
            let last = retained.last().unwrap();
            let mut branch = graph.clone();
            branch.add_integer_equality(&last.clone().into(), &other.clone().into());
            assert!(branch.are_integer_equal(last, &other));
            assert!(!graph.are_integer_equal(last, &other));
            for source in retained {
                let IntegerTerm::Machine(observation) = source else {
                    unreachable!()
                };
                assert!(!observation.has_boxed_operand());
            }
        }
        eprintln!("shared registration, unrelated={unrelated}: {samples:?}");
        for pair in samples.windows(2) {
            let [(small, sw), (large, lw)] = pair else {
                unreachable!()
            };
            assert!(lw * small * 4 <= sw * large * 5, "{samples:?}");
        }
        if unrelated == 0 {
            baseline = samples;
        } else {
            assert_eq!(samples, baseline);
        }
    }
}
