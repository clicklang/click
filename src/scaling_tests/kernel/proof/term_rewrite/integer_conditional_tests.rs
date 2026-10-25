// Scaling tests of `src/kernel/proof/term_rewrite/integer_conditional_tests.rs`:
// deterministic work measured at several input sizes. Included into its
// `scaling_tests` module; see "Scaling tests" in `docs/internals/testing.md`.

use super::*;

/// `t(k+1) = if v(k) == 0 { t(k) + 1 } else { t(k) }`: both arms share
/// `t(k)`, so the tree doubles at each level while the DAG grows by a
/// constant number of nodes.
fn conditional_chain(size: usize) -> IntegerTerm {
    let mut term = integer(1);
    for level in 0..size as u64 {
        term = IntegerTerm::if_then_else(
            is_zero(1000 + level),
            IntegerTerm::add(term.clone(), IntegerTerm::constant_i64(1)),
            term,
        );
    }
    term
}

#[test]
fn integer_conditional_construction_and_rewriting_scale_with_the_dag() {
    // Depth bounds the recursion; the tree below has 2^size nodes, so any
    // work that followed the tree instead of the DAG would explode.
    let mut previous: Option<(usize, usize, usize)> = None;
    for size in [16usize, 32, 64, 128] {
        let (chain, build) =
            crate::instrumentation::measure_deterministic_work(|| conditional_chain(size));
        assert!(build < 16 * size, "size={size}, build work={build}");

        // No condition is known: the rewrite rebuilds the same DAG,
        // visiting each shared node once.
        let unknown = HashMap::new();
        let (output, unchanged) = crate::instrumentation::measure_deterministic_work(|| {
            TermRewrite::for_conditions(&unknown).integer(&chain)
        });
        assert_eq!(output, chain);
        assert!(
            unchanged < 64 * size,
            "size={size}, rewrite work={unchanged}"
        );

        // Every condition is decided: each conditional is its then-arm.
        let known = (0..size as u64)
            .map(|level| (is_zero(1000 + level), true))
            .collect::<HashMap<_, _>>();
        let (output, decided) = crate::instrumentation::measure_deterministic_work(|| {
            TermRewrite::for_conditions(&known).integer(&chain)
        });
        assert!(!matches!(output, IntegerTerm::If { .. }), "size={size}");
        assert!(decided < 64 * size, "size={size}, decided work={decided}");

        // The measurement sees every level.
        assert!(
            build >= size && unchanged >= size && decided >= size,
            "size={size}"
        );
        // Linear between sizes, not just under a loose bound.
        if let Some((previous_build, previous_unchanged, previous_decided)) = previous {
            assert!(
                build <= 3 * previous_build,
                "size={size}: {build} vs {previous_build}"
            );
            assert!(
                unchanged <= 3 * previous_unchanged,
                "size={size}: {unchanged} vs {previous_unchanged}"
            );
            assert!(
                decided <= 3 * previous_decided,
                "size={size}: {decided} vs {previous_decided}"
            );
        }
        previous = Some((build, unchanged, decided));
    }
}
