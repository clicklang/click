use super::*;

#[test]
fn callback_qualification_identity_is_exact_at_every_position_and_arity() {
    let mut seen = std::collections::BTreeSet::new();
    for arity in 0..=13 {
        // Enumerate every qualification combination, including the highest
        // supported arity: neither a high bit nor leading zero is lost.
        for mask in 0..(1usize << (arity + 1)) {
            let parameters = (0..arity)
                .map(|index| (ProgramType::Int8Pointer, mask & (1 << (index + 1)) != 0))
                .collect::<Vec<_>>();
            let key = ProgramType::qualified_function_pointer_signature(
                ProgramType::Int8Pointer,
                mask & 1 != 0,
                &parameters,
            );
            assert_ne!(key, CallbackSignature::UNSPECIFIED);
            assert!(seen.insert(key), "collision at arity {arity}, mask {mask}");
        }
    }
    assert_eq!(
        ProgramType::qualified_function_pointer_signature(
            ProgramType::Int8Pointer,
            true,
            &[(ProgramType::Int8Pointer, true); 14]
        ),
        CallbackSignature::UNSPECIFIED
    );
    assert_eq!(
        ProgramType::qualified_function_pointer_signature(ProgramType::Int32, true, &[]),
        CallbackSignature::UNSPECIFIED
    );
    assert_eq!(
        ProgramType::qualified_function_pointer_signature(
            ProgramType::Void,
            false,
            &[(ProgramType::Int32, true)]
        ),
        CallbackSignature::UNSPECIFIED
    );
    assert!(std::mem::size_of::<ProgramType>() <= 16);
    assert!(std::mem::size_of::<crate::languages::c::syntax::C0Type>() <= 16);
}

#[test]
fn callback_signature_codes_cannot_overlap_adjacent_types() {
    assert_ne!(
        ProgramType::function_pointer_signature(ProgramType::UInt64Pointer, &[ProgramType::UInt8]),
        ProgramType::function_pointer_signature(ProgramType::Void, &[ProgramType::UInt32]),
    );
    let types = [
        ProgramType::Void,
        ProgramType::Int32,
        ProgramType::UInt8,
        ProgramType::UInt32,
        ProgramType::Int32Pointer,
        ProgramType::UInt8Pointer,
        ProgramType::Int32PointerPointer,
        ProgramType::UInt8PointerPointer,
        ProgramType::Int8,
        ProgramType::Int16,
        ProgramType::UInt16,
        ProgramType::Int64,
        ProgramType::UInt64,
        ProgramType::Int8Pointer,
        ProgramType::Int16Pointer,
        ProgramType::UInt16Pointer,
        ProgramType::UInt32Pointer,
        ProgramType::Int64Pointer,
        ProgramType::UInt64Pointer,
        ProgramType::Float32,
        ProgramType::Float64,
        ProgramType::VoidPointer,
    ];
    let mut seen = std::collections::BTreeSet::new();
    for result in types {
        assert!(seen.insert(ProgramType::function_pointer_signature(result, &[])));
        for first in types {
            assert!(seen.insert(ProgramType::function_pointer_signature(result, &[first])));
            for second in types {
                assert!(seen.insert(ProgramType::function_pointer_signature(
                    result,
                    &[first, second]
                )));
            }
        }
    }
    for arity in 0..=13 {
        let parameters = vec![ProgramType::VoidPointer; arity];
        let signature =
            ProgramType::function_pointer_signature(ProgramType::VoidPointer, &parameters);
        assert_ne!(signature, CallbackSignature::UNSPECIFIED);
        if arity > 2 {
            assert!(seen.insert(signature));
        }
    }
    assert_eq!(
        ProgramType::function_pointer_signature(ProgramType::Void, &[ProgramType::Int32; 14]),
        CallbackSignature::UNSPECIFIED
    );
}

/// Whether a function may throw is part of its contract, not of its pointer
/// type: a C pointer type cannot say. Refinement reads it: a function that
/// never throws implements a contract that may, and not the reverse.
#[test]
fn exceptional_outcome_is_part_of_the_contract_not_the_pointer_type() {
    let ordinary = program_function(
        ProgramType::Int32,
        "ordinary",
        vec![program_parameter("value", ProgramType::Int32)],
        program_return(crate::kernel::program_expression::variable("value")),
    );
    let exceptional = ordinary.clone().with_int32_exceptional_outcome();

    assert_eq!(
        ordinary.function_pointer_type(),
        exceptional.function_pointer_type()
    );
    assert!(
        !ordinary
            .contract_interface()
            .exactly_matches(exceptional.contract_interface())
    );
    assert!(
        !ordinary
            .contract_interface()
            .has_compatible_signature_and_composite_vocabulary(exceptional.contract_interface())
    );
    assert!(
        exceptional
            .contract_interface()
            .has_compatible_signature_and_composite_vocabulary(ordinary.contract_interface())
    );
}
