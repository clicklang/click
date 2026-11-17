use super::*;

const SIDECAR: &str = include_str!("../../design/charon-trial/inclusive-ranges/inclusive.click");

/// Inclusive ranges yield their endpoint once, even at the type's maximum.
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
        invariant total <= 256u32;
        invariant iter.is_empty() == false implies iter.end() == 255u8;
        invariant iter.is_empty() == false implies total == (iter.start() as u32);
        invariant iter.is_empty() implies total == 256u32;
        preserve by {
            mark iteration;
            have iter.is_empty() == false;
            have total == (iter.start() as u32);
            if at(iteration, iter.start()) < 255u8 {
                step_until(back_edge());
                have iter.is_empty() == false;
                have to_integer(total) == to_integer(at(iteration, total)) + 1;
                have to_integer(iter.start()) == to_integer(at(iteration, iter.start())) + 1;
                have to_integer(total) == to_integer(iter.start());
                have total == (iter.start() as u32);
            } else {
                have iter.start() == 255u8;
                step_until(back_edge());
                have iter.is_empty();
                have to_integer(total) == to_integer(at(iteration, total)) + 1;
                have to_integer(at(iteration, total)) == 255;
                have to_integer(total) == 256;
                have total == 256u32;
            }
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
