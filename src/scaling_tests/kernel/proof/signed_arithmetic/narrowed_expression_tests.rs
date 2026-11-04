// Scaling tests of `src/kernel/proof/signed_arithmetic.rs` (module `narrowed_expression_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn narrowed_native_expression_identity_work_scales_with_selected_expression() {
    let mut measured = Vec::new();
    for count in [16, 32, 64, 128] {
        let mut value = MachineTerm::Variable(Variable(100));
        for i in 0..count {
            value = MachineTerm::uint64_subtract(value, MachineTerm::Variable(Variable(1000 + i)));
        }
        let narrow = MachineTerm::uint32_from_64(value);
        let (atom, work) = crate::instrumentation::measure_deterministic_work(|| {
            SignedArithmeticAtom::from_term(&narrow).unwrap()
        });
        assert!(atom.is_opaque_root());
        measured.push(work);
    }
    assert!(
        measured.windows(2).all(|pair| pair[1] <= 3 * pair[0]),
        "{measured:?}"
    );
}
