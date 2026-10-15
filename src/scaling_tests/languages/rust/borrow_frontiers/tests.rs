// Scaling tests of `src/languages/rust/borrow_frontiers.rs` (module `tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn scalar_reference_frontier_selected_alias_chain_scales_linearly() {
    let mut samples = Vec::new();
    for size in [16, 64, 256, 1024] {
        let mut f = function();
        let mir = f.mir.as_mut().unwrap();
        let mut previous = "child".to_string();
        for index in 0..size {
            let name = format!("alias_{index}");
            mir.locals.push(place(&name, reference_type()));
            mir.blocks[0]
                .statements
                .insert(index + 1, assign(local(&name), local(&previous)));
            previous = name;
        }
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            certify_scalar_reference_end(&f, "test-source", point(0), point(size + 2)).unwrap()
        });
        samples.push((size, work));
        assert!(
            work <= size * 9 + 64,
            "alias chain revisited prefixes: {samples:?}"
        );
    }
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1 * 4 + 48,
            "superlinear alias checking: {samples:?}"
        );
    }
}

#[test]
fn scalar_reference_accesses_index_and_lookup_scale_with_selected_operations() {
    let mut samples = Vec::new();
    for size in [16, 64, 256, 1024] {
        let mut f = function();
        block_mut(&mut f).statements = vec![assign(local("child"), borrow_parent())];
        for _ in 0..size {
            block_mut(&mut f)
                .statements
                .push(assign(deref("child"), E::Integer { value: 7 }));
        }
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            let certificate =
                certify_scalar_reference_end(&f, "source", point(0), point(size + 1)).unwrap();
            for index in 1..=size {
                let accesses = certificate.memory_accesses_at(point(index));
                assert_eq!(accesses.len(), 1);
                assert_eq!(accesses[0].point(), point(index));
                assert_eq!(accesses[0].kind(), ScalarReferenceAccessKind::Write);
            }
        });
        samples.push(work);
        assert!(
            work <= size * 14 + 64,
            "access indexing revisited prefixes: {samples:?}"
        );
    }
    for pair in samples.windows(2) {
        assert!(
            pair[1] <= pair[0] * 4 + 48,
            "superlinear access indexing: {samples:?}"
        );
    }
}
