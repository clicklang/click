use super::*;

const SIDECAR: &str = include_str!("../../design/charon-trial/user-iterator/countdown.click");

/// A `for` over a crate's own `impl Iterator` calls its `next` each pass,
/// under `next`'s contract, and a proof reads the iterator's fields as
/// `iter.n`. A wrong invariant and a wrong `next` contract are refused.
#[test]
fn charon_user_iterator_loops_verify_from_next_contract() {
    let p = Project::from_fixture("design/charon-trial/user-iterator");
    fs::write(p.root.join("borrow.click"), SIDECAR).unwrap();
    let prepared = p.prepared().unwrap();
    ProgramVerificationSession::new_program_prepared(SIDECAR, &prepared)
        .unwrap_or_else(|error| panic!("{error:?}"));
    for (before, after) in [
        // The count and the remaining count sum to `n`, not the count alone.
        (
            "invariant to_integer(passes) + to_integer(iter.n) == to_integer(n);",
            "invariant to_integer(passes) == to_integer(n);",
        ),
        // `next` yields the decremented count, not the count it found.
        (
            "result == Option<u32>::Some(old(self.n) - 1u32)",
            "result == Option<u32>::Some(old(self.n))",
        ),
        // The last value yielded is 0, so `last` never ends at `n`.
        ("ensures result == 0u32;", "ensures result == n;"),
    ] {
        assert!(SIDECAR.contains(before), "{before}");
        let invalid = SIDECAR.replacen(before, after, 1);
        ProgramVerificationSession::new_program_prepared(&invalid, &prepared)
            .err()
            .unwrap_or_else(|| panic!("`{before}` -> `{after}` must fail"));
    }
}

/// The `Option` that `next` returns is no local: the loop tests the call's
/// result for `Some` without ending it, and the `Some` arm's payload read
/// ends it.
#[test]
fn charon_user_iterator_next_result_is_a_call_result() {
    use click::languages::rust::schema::{Expression, MirStatement, MirTerminator, Type};
    let p = Project::from_fixture("design/charon-trial/user-iterator");
    fs::write(p.root.join("borrow.click"), SIDECAR).unwrap();
    let prepared = p.prepared().unwrap();
    for name in ["count", "last"] {
        let function = prepared
            .export()
            .functions
            .iter()
            .find(|function| function.name == name)
            .unwrap();
        let mir = function.mir.as_ref().unwrap();
        assert!(
            !mir.locals
                .iter()
                .any(|local| matches!(&local.value_type, Type::Enum { .. })),
            "{name}: {:?}",
            mir.locals
        );
        let mut steps = 0;
        let mut tests = 0;
        let mut payloads = 0;
        for block in &mir.blocks {
            match &block.terminator {
                MirTerminator::Call {
                    function, result, ..
                } if function.source_name() == Some("Countdown_next") => {
                    assert!(result.is_some(), "{name}: {:?}", block.terminator);
                    steps += 1;
                }
                MirTerminator::If {
                    condition: Expression::VariantIs { value, variant },
                    ..
                } => {
                    assert_eq!(variant, "Some");
                    assert!(
                        matches!(value.as_ref(), Expression::CallResult { keeps: true, .. }),
                        "{name}: {value:?}"
                    );
                    tests += 1;
                }
                _ => {}
            }
            for statement in &block.statements {
                if let MirStatement::Assign {
                    value: Expression::EnumField { base, .. },
                    ..
                } = statement
                {
                    assert!(
                        matches!(base.as_ref(), Expression::CallResult { keeps: false, .. }),
                        "{name}: {statement:?}"
                    );
                    payloads += 1;
                }
            }
        }
        assert_eq!((steps, tests, payloads), (1, 1, 1), "{name}");
    }
}
