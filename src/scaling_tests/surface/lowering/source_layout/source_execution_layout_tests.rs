// Scaling tests of `src/surface/lowering/source_layout.rs` (module `source_execution_layout_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
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
