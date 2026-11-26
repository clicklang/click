use super::*;
use crate::kernel::{ProgramStatement, ProgramType, program_function};

#[test]
fn override_contract_lookup_uses_one_method_key() {
    let contract = FunctionContract::new(
        "Derived::method",
        program_function(
            ProgramType::Void,
            "Derived::method",
            vec![],
            ProgramStatement::Skip,
        ),
    )
    .unwrap();
    for size in [8, 32, 128, 512] {
        let mut contracts = BTreeMap::from([(
            OverrideImplementation("Derived::method".into()),
            contract.clone(),
        )]);
        for index in 0..size {
            contracts.insert(
                OverrideImplementation(format!("Derived::other{index}")),
                contract.clone(),
            );
        }
        let ((hit, miss), work) = crate::instrumentation::measure_deterministic_work(|| {
            (
                override_contract_for_method(&contracts, "Derived::method"),
                override_contract_for_method(&contracts, "Base::method"),
            )
        });
        assert!(hit.is_some());
        assert!(miss.is_none());
        assert_eq!(work, 2, "{size}: override contract lookup work");
    }
}
