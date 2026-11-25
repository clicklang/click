use super::*;

const SIDECAR: &str = include_str!("../../design/charon-trial/inclusive-ranges/inclusive.click");

/// Inclusive ranges yield their endpoint once, even at the type's maximum.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 6.8s in the parallel gate"]
fn charon_inclusive_range_loops_yield_their_end_once() {
    let p = Project::from_fixture("design/charon-trial/inclusive-ranges");
    fs::write(p.root.join("borrow.click"), SIDECAR).unwrap();
    let prepared = p.prepared().unwrap();
    ProgramVerificationSession::new_program_prepared(SIDECAR, &prepared)
        .unwrap_or_else(|error| panic!("{error:?}"));
    // `0u8..=255` yields every byte once, 255 included: 256 values, not 255.
    let function = SIDECAR
        .split("\nfn ")
        .find(|function| function.starts_with("every_byte"))
        .unwrap();
    let invalid = format!(
        "verifying \"inclusive.rs\";\nfn {}",
        function.replacen("result == 256u32;", "result == 255u32;", 1)
    );
    let error = ProgramVerificationSession::new_program_prepared(&invalid, &prepared)
        .err()
        .expect("`every_byte` claiming 255 iterations must fail");
    let rendered = format!("{error:?} {error}");
    assert!(rendered.contains("every_byte"), "{rendered}");
}

#[test]
fn charon_inclusive_range_exhaustion_uses_typed_signed_bounds() {
    let p = Project::from_fixture("design/charon-trial/inclusive-ranges");
    let function = SIDECAR
        .split("\nfn ")
        .find(|function| function.starts_with("every_byte"))
        .unwrap();
    let sidecar = format!("verifying \"inclusive.rs\";\nfn {function}");
    fs::write(p.root.join("borrow.click"), &sidecar).unwrap();
    let prepared = p.prepared().unwrap();
    let (verified, events) = click::instrumentation::collect(|| {
        ProgramVerificationSession::new_program_prepared(&sidecar, &prepared)
    });
    verified.unwrap_or_else(|error| panic!("{error:?}"));
    let raising_work: usize =
        events
            .iter()
            .filter_map(|event| match event {
                click::instrumentation::VerificationEvent::OperationFinished {
                    name, work, ..
                } if name == "solve closure: premise raising" => Some(*work),
                _ => None,
            })
            .sum();
    assert!(
        raising_work > 0,
        "the regression must measure premise raising"
    );
    assert!(
        raising_work < 1_500_000,
        "the small proof must not repeat the old multi-million-unit recovery search: {raising_work}"
    );
}
