use super::*;

const SIDECAR: &str = include_str!("../../design/charon-trial/inclusive-ranges/inclusive.click");

/// A `for` over `start..=end` holds the range's bounds and whether it has
/// yielded `end`: it yields `end` once and stops, even at the type's maximum,
/// and verifies from ordinary invariants over `iter_start`, `iter_end` and
/// `iter_done`.
#[test]
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
    let sidecar = r#"verifying "inclusive.rs";
fn every_byte() -> u32 {
    ensures result == 256u32;
} by {
    step_until(loop(0));
    loop {
        decreases 256u32 - total;
        invariant iter_end == 255u8;
        invariant total <= 256u32;
        invariant iter_done == 0 implies total == (iter_start as u32);
        invariant iter_done != 0 implies iter_start == 255u8 and total == 256u32;
        preserve by {
            have total == (iter_start as u32);
        }
    }
}
"#;
    fs::write(p.root.join("borrow.click"), sidecar).unwrap();
    let prepared = p.prepared().unwrap();
    let (verified, events) = click::instrumentation::collect(|| {
        ProgramVerificationSession::new_program_prepared(sidecar, &prepared)
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
