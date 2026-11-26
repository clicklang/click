// Scaling tests of `src/surface/lowering/source_layout.rs` (module `source_execution_layout_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.9s in the parallel gate"]
fn read_frontiers_have_linear_expression_work_and_indexed_lookups() {
    for count in [8, 128, 1024] {
        let mut source = String::from("int32 f(const int32* p) {int32 x; int32 other;");
        for _ in 0..count {
            source.push_str("other=1;x=*p+other;");
        }
        source.push_str("return x;}");
        let function = syntax::parse_function(&source).unwrap();
        let typed = function
            .clone()
            .with_prelowered_kernel_function(function.to_kernel_function());
        for function in [&function, &typed] {
            let (layout, work) = crate::instrumentation::measure_deterministic_work(|| {
                SourceExecutionLayout::for_function(function).unwrap()
            });
            assert_eq!(layout.data.reads.len(), count);
            assert!(work < 16 * count, "{count} reads: {work}");
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                for n in 0..count {
                    layout.read_entry(n).unwrap();
                }
            });
            assert_eq!(work, count);
        }
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.2s in the parallel gate"]
fn assignment_frontiers_build_and_resolve_without_scanning_unrelated_stores() {
    for count in [8, 128, 1024] {
        let mut source = String::from("int32 f() {int32 marker; int32 unrelated;");
        for i in 0..count {
            source.push_str(&format!("unrelated={i};marker={i};"));
        }
        source.push_str("return marker;}");
        let function = syntax::parse_function(&source).unwrap();
        let kernel = function.to_kernel_function();
        let typed = function.clone().with_prelowered_kernel_function(kernel);
        for function in [&function, &typed] {
            let (layout, work) = crate::instrumentation::measure_deterministic_work(|| {
                SourceExecutionLayout::for_function(function).unwrap()
            });
            assert!(work <= 8 * count, "{count} stores: {work}");
            assert_eq!(layout.data.assignments["marker"].len(), count);
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                for occurrence in 0..count {
                    layout.assignment_entry("marker", occurrence).unwrap();
                }
            });
            assert_eq!(work, count);
        }
    }
}

#[test]
fn construction_result_metadata_shares_fields_across_calls_and_uses_indexed_reads() {
    for size in [4, 16, 64, 256] {
        let function = construction_result_function(size, size, 0);
        let (layout, work) = crate::instrumentation::measure_deterministic_work(|| {
            SourceExecutionLayout::for_function(&function).unwrap()
        });
        assert!(work > 0 && work <= 16 * size + 64, "{size}: {work}");
        assert!(std::sync::Arc::ptr_eq(
            &layout.data.aggregate_results[&1],
            &layout.data.aggregate_results[&size]
        ));
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            assert_eq!(
                layout
                    .aggregate_result_field(size, "nested.field_3")
                    .unwrap()
                    .offset_bytes(),
                24
            );
        });
        assert_eq!(work, 1);
        let function = construction_result_function(4, 1, size);
        let layout = SourceExecutionLayout::for_function(&function).unwrap();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            assert_eq!(
                layout
                    .aggregate_result_field(size + 1, "nested.field_3")
                    .unwrap()
                    .offset_bytes(),
                24
            );
        });
        assert_eq!(work, 1);
    }
}

#[test]
fn construction_return_parameter_cleanup_scales_with_selected_parameters() {
    let costs = [4, 16, 64, 256].map(|count| {
        let function = record_parameter_return_function(count, true);
        let (layout, work) = crate::instrumentation::measure_deterministic_work(|| {
            SourceExecutionLayout::for_function(&function).unwrap()
        });
        assert_eq!(layout.automatic_exits(1, true).len(), count);
        assert!(layout.automatic_exits(0, true).is_empty());
        work
    });
    assert!(
        costs[0] > 0 && costs.windows(2).all(|pair| pair[1] <= 4 * pair[0] + 32),
        "{costs:?}"
    );
}

#[test]
fn call_capture_selectors_use_the_index_at_multiple_sizes() {
    use crate::kernel::{
        BindingName, LocalBindingId, LocalFunctionId, ProgramType, program_assign,
        program_call_value, program_function, program_seq,
    };
    use crate::languages::interface::{ImportedFunction, InterfaceType};
    use crate::surface::{CodeRegionRef, ProgramPointKind, SourcePathStep};

    for count in [8, 128, 1024] {
        let capture = LocalBindingId::temporary(LocalFunctionId::new(None, "f".into()), 0);
        capture.initialize_program_type(ProgramType::Int32);
        let capture = BindingName::from(capture);
        let (call, result) = program_call_value(2 * count, "get", Vec::new());
        let mut body = program_seq(call, program_assign(&capture, result));
        for i in (0..count).rev() {
            let (related, _) = program_call_value(2 * i, "get", Vec::new());
            let (unrelated, _) = program_call_value(2 * i + 1, "other", Vec::new());
            body = program_seq(related, program_seq(unrelated, body));
        }
        let function = ImportedFunction::external(InterfaceType::Int32, "f".into(), Vec::new())
            .with_prelowered_kernel_function(program_function(
                ProgramType::Int32,
                "f",
                Vec::new(),
                body,
            ));
        let layout = SourceExecutionLayout::for_function(&function).unwrap();
        let expected = layout.step_region(2 * count).unwrap();

        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            let (region, CodeRegionRef::Path(steps)) =
                layout.call_capture_source(&capture).unwrap()
            else {
                panic!("the capture must use a source path");
            };
            assert_eq!(region, expected);
            assert_eq!(steps, [SourcePathStep::Call("get".into(), count as usize)]);
            assert_eq!(
                layout.source_path_region(&steps, ProgramPointKind::Exit),
                Ok(expected)
            );
        });
        assert_eq!(work, 3, "{count} calls");
    }
}

#[test]
fn typed_conditional_value_layout_preserves_join_identity_and_scales() {
    use crate::kernel::{
        ProgramStatement, ProgramType, program_expression as e, program_function, program_if,
        program_return, program_seq, program_skip,
    };
    let value = |step| ProgramStatement::StepValue {
        aggregate_layout: None,
        steps: vec![step],
        expression: e::int32_literal(1),
        value_type: Some(ProgramType::Int32),
        pointee_constant: false,
    };
    let arm = || program_seq(program_seq(value(0), program_skip()), program_skip());
    let mut samples = Vec::new();
    for count in [8, 32, 128, 512] {
        let mut body = program_if(e::int32_literal(1), arm(), arm());
        for step in 1..=count {
            body = program_seq(body, value(step));
        }
        body = program_seq(body, program_return(e::int32_literal(0)));
        let function = syntax::parse_function("int32 f() { return 0; }")
            .unwrap()
            .with_prelowered_kernel_function(program_function(
                ProgramType::Int32,
                "f",
                vec![],
                body,
            ));
        let (layout, work) = crate::instrumentation::measure_deterministic_work(|| {
            SourceExecutionLayout::for_function(&function).unwrap()
        });
        assert!(work > 0);
        assert_eq!(
            layout.step_region(0),
            Some(0),
            "the join owns both arms' result"
        );
        assert_eq!(layout.call_number(0), Some(0));
        assert_eq!(
            layout.result_code_region(0),
            Some(crate::surface::CodeRegionRef::Region(0))
        );
        for step in 1..=count {
            let region = layout.step_region(step).unwrap();
            assert_eq!(layout.call_number(region), Some(step));
            assert_eq!(
                layout.result_code_region(region),
                Some(crate::surface::CodeRegionRef::Region(region))
            );
        }
        samples.push(work);
    }
    assert!(
        samples.windows(2).all(|w| w[1] <= w[0] * 5 + 64),
        "{samples:?}"
    );
}

#[test]
fn cpp_reference_binding_lookup_uses_the_call_and_argument_indexes() {
    use crate::kernel::{
        CppBindingContract, CppObjectConversion, ReferenceBindingKind, ReferenceBindingOperation,
        ReferenceBindingSlot, ReferenceBindingSource, program_call,
    };
    use crate::surface::{ProgramPointKind, SourcePathStep};

    let steps = [
        SourcePathStep::Call("target".into(), 0),
        SourcePathStep::Binding {
            slot: ReferenceBindingSlot::Argument(0),
            release: false,
        },
    ];
    let mut counts = Vec::new();
    for count in [8, 32, 128, 512] {
        let contract = crate::kernel::ReferenceBindingContract::Cpp(CppBindingContract {
            conversion: CppObjectConversion::new("Derived", "Base"),
            kind: ReferenceBindingKind::AcquireShared,
        });
        let transition = |contract, source| ProgramStatement::Call {
            function_name: String::new(),
            arguments: vec![],
            callee: None,
            dispatch: crate::kernel::CallDispatch::Direct,
            reference_binding: Some(std::sync::Arc::new(ReferenceBindingOperation {
                contract,
                source,
            })),
        };
        let acquire = transition(
            contract.clone(),
            Some(ReferenceBindingSource {
                slot: ReferenceBindingSlot::Argument(0),
                call_offset: 1,
                release_offset: 2,
            }),
        );
        let release = transition(contract.release(), None);
        let mut body = program_seq(
            acquire,
            program_seq(program_call("target", vec![]), release),
        );
        for _ in 0..count {
            body = program_seq(program_call("other", vec![]), body);
        }
        let function = syntax::parse_function("int32 f() { return 0; }")
            .unwrap()
            .with_prelowered_kernel_function(program_function(
                ProgramType::Int32,
                "f",
                vec![],
                body,
            ));
        let layout = SourceExecutionLayout::for_function(&function).unwrap();
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            (
                layout.source_path_region(&steps, ProgramPointKind::Entry),
                layout.reference_binding_target(&steps),
                layout.reference_binding_target(&[
                    steps[0].clone(),
                    SourcePathStep::Binding {
                        slot: ReferenceBindingSlot::Argument(0),
                        release: true,
                    },
                ]),
            )
        });
        assert_eq!(result.0, Ok(count));
        assert_eq!(result.1, Ok(&contract));
        assert_eq!(result.2, Ok(&contract.release()));
        counts.push(work);
    }
    assert!(
        counts.windows(2).all(|window| window[0] == window[1]),
        "{counts:?}"
    );
}
