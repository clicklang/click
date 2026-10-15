// Scaling tests of `src/surface/lowering/resource_lowering.rs` (module `input_identity_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn input_pointer_places_are_exact_and_do_not_scan_unrelated_functions() {
    let selected = input_scope("certificate-selected");
    let variable = input_pointer_variable(selected, 1).unwrap();
    let pointer = crate::kernel::CPointerValue::new(
        Pointer {
            block: PointerBlock::ExternalArgument,
            offset: scale_int32_offset(Bitvector32Term::Variable(variable), 4),
        },
        CType::Int32Pointer,
    );
    INPUT_POINTER_PLACES.with(|places| {
        places
            .borrow_mut()
            .insert(variable, (selected, 1, pointer.clone()));
    });
    for size in [16, 64, 256] {
        for index in 0..size {
            let scope = input_scope(&format!("certificate-unrelated-{index}"));
            let other = input_pointer_variable(scope, 0).unwrap();
            let mut value = pointer.clone();
            value.replace_pointer(Pointer {
                block: PointerBlock::ExternalArgument,
                offset: scale_int32_offset(Bitvector32Term::Variable(other), 4),
            });
            INPUT_POINTER_PLACES.with(|places| {
                places.borrow_mut().insert(other, (scope, 0, value));
            });
        }
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..64 {
                assert_eq!(input_pointer_parameter(selected, &pointer), Some(1));
            }
        });
        assert_eq!(work, 64, "unrelated input count: {size}");
    }
    assert_eq!(
        input_pointer_parameter(input_scope("certificate-other"), &pointer),
        None
    );
    assert_eq!(
        input_pointer_parameter(selected, &pointer.clone().with_type(CType::Int8Pointer)),
        None
    );
    let mut wrong_stride = pointer.clone();
    wrong_stride.replace_pointer(Pointer {
        block: PointerBlock::ExternalArgument,
        offset: scale_int32_offset(Bitvector32Term::Variable(variable), 1),
    });
    assert_eq!(input_pointer_parameter(selected, &wrong_stride), None);
    let mut unknown = pointer;
    unknown.replace_pointer(Pointer {
        block: PointerBlock::ExternalArgument,
        offset: scale_int32_offset(Bitvector32Term::Variable(Variable(999_999)), 4),
    });
    assert_eq!(input_pointer_parameter(selected, &unknown), None);
}
