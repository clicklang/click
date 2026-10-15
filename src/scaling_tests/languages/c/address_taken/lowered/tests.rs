// Scaling tests of `src/languages/c/address_taken/lowered.rs` (module `tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn imported_addressability_work_scales_with_body_size() {
    for count in [16, 64, 256] {
        let mut body = c_skip();
        for index in 0..count {
            body = c_seq(
                body,
                c_declare(format!("capture_{index}"), CType::Int32Pointer),
            );
        }
        let function = imported(body);
        let (summary, work) = crate::instrumentation::measure_deterministic_work(|| {
            summarize_address_taken([&function])
        });
        assert_eq!(summary.never_taken().len(), count);
        assert_eq!(work, 2 * count + 1);
    }
}
