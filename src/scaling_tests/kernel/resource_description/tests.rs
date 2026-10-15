// Scaling tests of `src/kernel/resource_description.rs` (module `tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn cloning_a_description_shares_storage_independently_of_argument_count() {
    let mut work = Vec::new();
    for size in [16, 64, 256] {
        let instance = ResourceInstance::new(
            Variable(1),
            "state".into(),
            (0..size)
                .map(|index| int32(index).into())
                .collect::<Vec<_>>()
                .into(),
            ResourceFieldSchema::new(vec![("value".into(), ResourceFieldType::C(CType::Int32))])
                .unwrap(),
            vec![int32(1).into()].into(),
        )
        .unwrap();
        let description = ResourceDescription::from_instance(&instance);
        let ((clone, deterministic), persistent) =
            crate::persistent::measure_persistent_work(|| {
                crate::instrumentation::measure_deterministic_work(|| description.clone())
            });
        assert!(Arc::ptr_eq(&description.0, &clone.0));
        assert_eq!(clone.arguments().len(), size as usize);
        work.push((deterministic, persistent));
    }
    assert!(work.windows(2).all(|pair| pair[1] == pair[0]), "{work:?}");
}
