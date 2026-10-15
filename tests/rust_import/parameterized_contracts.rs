use super::*;

const SIDECAR: &str = include_str!("../../design/charon-trial/parameterized-contracts/adds.click");

fn parameterized_contract_project() -> Project {
    let p = Project::from_fixture("design/charon-trial/parameterized-contracts");
    fs::write(p.root.join("borrow.click"), SIDECAR).unwrap();
    p
}

// A Rust sidecar declares a contract's value parameter with a Rust type,
// `let amount: i32;`. `add3` meets `Adds` with `amount` fixed to 3 from its
// own contract; a weaker contract of `add3` does not.
#[test]
#[ignore = "nightly: 0.7s in the parallel gate"]
fn charon_parameterized_contract_fixes_its_value_where_attached() {
    let p = parameterized_contract_project();
    let prepared = p.prepared().unwrap();
    C0VerificationSession::new_program_prepared(SIDECAR, &prepared)
        .unwrap_or_else(|error| panic!("{error:?}"));
    let weak = SIDECAR.replacen("ensures result == x + 3;", "ensures result >= x;", 1);
    assert_ne!(weak, SIDECAR);
    let error = C0VerificationSession::new_program_prepared(&weak, &prepared)
        .err()
        .expect("a weaker `add3` contract does not meet `Adds`");
    let rendered = format!("{error:?}");
    assert!(
        rendered.contains("is missing prerequisite")
            && rendered.contains("Adds(__rust_checked_0, 3)"),
        "{rendered}"
    );
}
