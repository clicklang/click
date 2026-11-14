use super::*;

#[test]
fn owned_entry_admission_visits_executions_without_rewalking_entry_premises() {
    for unrelated in [0, 64, 256] {
        let (entry, checked) = checked_execution(unrelated, None).unwrap();
        for executions in [1, 4, 16, 64] {
            let artifacts = vec![checked.clone(); executions];
            let (admitted, work) = crate::instrumentation::measure_deterministic_work(|| {
                execution_from_owned_contract_entry(&entry, &artifacts)
            });
            assert_eq!(admitted.cases[0].len(), executions);
            assert!(
                work <= 8 * executions + 8,
                "{executions} executions, {unrelated} unrelated premises: {work}"
            );
        }
    }
}
