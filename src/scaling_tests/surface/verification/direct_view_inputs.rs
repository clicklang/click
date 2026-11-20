// Scaling tests for the contract-local direct view source index.

use super::*;

#[test]
fn direct_view_source_index_builds_once_and_queries_without_scanning() {
    let segment = |position| {
        crate::kernel::MemorySegment::new(
            ProgramExpression::Variable("p".into()),
            ProgramExpression::Value(crate::kernel::int32(position)),
            ProgramExpression::Value(crate::kernel::int32(position + 1)),
        )
    };
    for size in [4, 16, 64, 256] {
        let mut requirements = (0..size)
            .map(|position| ResourceSpec::viewed_memory(segment(position)))
            .collect::<Vec<_>>();
        requirements.extend(std::iter::repeat_n(
            ResourceSpec::viewed_memory(segment(size)),
            size as usize,
        ));
        let (index, build_work) = crate::instrumentation::measure_deterministic_work(|| {
            DirectViewInputs::new(&requirements)
        });
        assert_eq!(build_work, requirements.len());
        let (selected, lookup_work) = crate::instrumentation::measure_deterministic_work(|| {
            [
                index.lookup(&segment(size - 1)),
                index.lookup(&segment(size)),
                index.lookup(&segment(size + 1)),
            ]
        });
        assert_eq!(selected, [Some(Some(size as usize - 1)), Some(None), None]);
        assert_eq!(lookup_work, 3);
    }
}
