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
