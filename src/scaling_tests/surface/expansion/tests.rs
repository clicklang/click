// Scaling tests of `src/surface/expansion/tests.rs`: deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn batch_source_positions_walk_a_long_line_once() {
    let mut measurements = Vec::new();
    for size in [16, 64, 256] {
        let source = "α ".repeat(size);
        let (positions, work) = crate::instrumentation::measure_deterministic_work(|| {
            positions_at_offsets(&source, (0..size).map(|index| index * 3))
        });
        assert_eq!(
            positions.last(),
            Some(&SourcePosition::new(1, size * 2 - 1))
        );
        assert!(work <= size * 3);
        measurements.push(work);
    }
    for pair in measurements.windows(2) {
        assert!(pair[1] <= pair[0] * 5, "{measurements:?}");
    }
}

#[test]
fn arithmetic_certificate_mixed_atom_lowering_scales_with_selected_inputs() {
    let mut work = Vec::new();
    for width in [8, 16, 32, 64] {
        let mut parameters = vec!["x: int32".to_string()];
        parameters.extend((0..width).map(|i| format!("unused{i}: int32")));
        let nodes = "trivial => to_integer(x) == to_integer(x);\n".repeat(width);
        let source = format!(
            "theorem selected({}) {{ ensures to_integer(x) == to_integer(x) by {{ arithmetic_certificate {{ {nodes} conclusion 0; }} }} }}",
            parameters.join(", ")
        );
        let (result, measured) =
            crate::instrumentation::measure_deterministic_work(|| verify_c0_sources(&source, &[]));
        result.unwrap();
        work.push(measured);
    }
    for pair in work.windows(2) {
        assert!(
            pair[1] <= 3 * pair[0],
            "mixed certificate lowering grew superlinearly: {work:?}"
        );
    }
}

#[test]
fn trace_source_index_scales_with_sites_and_unrelated_source() {
    let mut total = Vec::new();
    let mut query_work = Vec::new();
    for size in [16, 64, 256] {
        let source = format!(
            "{}\nby {{ {} }}",
            "// αβ unrelated\n".repeat(size * 4),
            "have true by { normalize(); } ".repeat(size)
        );
        let positions: Vec<_> = source
            .match_indices("have")
            .map(|(offset, _)| position_at_offset(&source, offset))
            .collect();
        let ((index, locations), build_work) =
            crate::instrumentation::measure_deterministic_work(|| {
                let index = ProofSourceIndex::new(&source).unwrap();
                let locations: Vec<_> = positions
                    .iter()
                    .map(|p| index.nested_position(p, &[0]).unwrap())
                    .collect();
                (index, locations)
            });
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for (have, nested) in positions.iter().zip(&locations) {
                assert!(index.have_body_contains(have, nested).unwrap());
                assert!(index.line_has_multiple_starts(nested).unwrap());
                assert_eq!(index.nested_position(have, &[0]).unwrap(), *nested);
                assert!(index.nested_position(have, &[usize::MAX]).is_err());
                assert_eq!(index.arm_containing(have, nested).unwrap(), None);
            }
        });
        total.push(build_work + work);
        query_work.push(work);
        assert!(
            work <= size * 8,
            "queries must inspect only their paths: {work}"
        );
    }
    for pair in total.windows(2) {
        assert!(pair[1] <= pair[0] * 5, "{total:?}");
    }
    for pair in query_work.windows(2) {
        assert!(pair[1] <= pair[0] * 4, "{query_work:?}");
    }
    // A larger immutable container must not increase work per selected site.
    let query = |unrelated| {
        let source = format!(
            "{}by {{ have true by {{ normalize(); }} }}",
            "# unrelated αβ\n".repeat(unrelated)
        );
        let index = ProofSourceIndex::new(&source).unwrap();
        let have = position_at_offset(&source, source.find("have").unwrap());
        crate::instrumentation::measure_deterministic_work(|| {
            let nested = index.nested_position(&have, &[0]).unwrap();
            assert!(index.have_body_contains(&have, &nested).unwrap());
            index.line_has_multiple_starts(&nested).unwrap()
        })
        .1
    };
    assert_eq!(query(16), query(4096));
}

#[test]
fn trace_source_index_skips_nested_subtrees_during_construction() {
    let mut work = Vec::new();
    for depth in [16, 64, 256] {
        let source = format!(
            "by {{ {}normalize();{} }}",
            "have true by { ".repeat(depth),
            " }".repeat(depth)
        );
        let (_, measured) = crate::instrumentation::measure_deterministic_work(|| {
            ProofSourceIndex::new(&source).unwrap()
        });
        work.push(measured);
    }
    for pair in work.windows(2) {
        assert!(
            pair[1] <= pair[0] * 5,
            "nested blocks must skip already indexed subtrees: {work:?}"
        );
    }
}

#[test]
fn trace_source_index_indexes_many_case_arms() {
    for size in [16, 64, 256] {
        let source = format!(
            "by {{ cases {{ {} }} }}",
            "true => { normalize(); } ".repeat(size)
        );
        let index = ProofSourceIndex::new(&source).unwrap();
        let cases = position_at_offset(&source, source.find("cases").unwrap());
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for arm in 0..size {
                let child = index.nested_position(&cases, &[arm, 0]).unwrap();
                assert_eq!(index.arm_containing(&cases, &child).unwrap(), Some(arm));
            }
        });
        assert!(
            work <= size * 12,
            "case targets must use indexed arm intervals: {work}"
        );
    }
}
