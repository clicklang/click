use super::*;

#[test]
fn ordinary_execution_opening_does_not_rewalk_entry_premises() {
    for unrelated in [0, 64, 256] {
        let (entry, checked) = checked_execution(unrelated, None).unwrap();
        for executions in [1, 4, 16, 64] {
            let owner = WholeContractRoot::open(entry.clone()).unwrap();
            let (opened, work) = crate::instrumentation::measure_deterministic_work(|| {
                (0..executions)
                    .map(|_| open_execution(&owner, checked.clone()).unwrap())
                    .collect::<Vec<_>>()
            });
            assert_eq!(opened.len(), executions);
            assert!(owner.finish().is_err(), "opening is not completion");
            assert!(
                work <= 32 * executions + 8,
                "{executions} executions, {unrelated} unrelated premises: {work}"
            );
        }
    }
}
