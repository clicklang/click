use super::*;

fn slice_type() -> AlgebraicType {
    let arguments = vec![AlgebraicValueType::C(ProgramType::UInt8)];
    let variants: std::sync::Arc<[AlgebraicVariantType]> = vec![AlgebraicVariantType {
        name: "Slice".to_string(),
        fields: vec![
            AlgebraicValueType::C(ProgramType::UInt8Pointer),
            AlgebraicValueType::C(ProgramType::UInt64),
        ],
    }]
    .into();
    let value_type = AlgebraicValueType::Algebraic {
        name: "Slice".to_string(),
        arguments: arguments.clone(),
    };
    AlgebraicType {
        rigid: false,
        name: "Slice".to_string(),
        arguments,
        variants: variants.clone(),
        schemas: std::sync::Arc::new(AlgebraicSchemas::new(std::collections::BTreeMap::from([(
            value_type, variants,
        )]))),
    }
}

fn subslice(length: u64) -> AlgebraicTerm {
    AlgebraicTerm {
        algebraic_type: slice_type(),
        node: AlgebraicTermNode::Constructor {
            variant: "Slice".to_string(),
            fields: vec![
                AlgebraicValue::C(ProgramValue::typed_pointer(
                    Pointer::null(),
                    ProgramType::UInt8Pointer,
                )),
                AlgebraicValue::C(ProgramValue::UInt64(MachineTerm::uint64_constant(length))),
            ],
        },
    }
}

/// Naming a subslice where it is constructed, and spelling it, are one
/// registry operation each, however many unrelated subslices the session
/// has recorded.
#[test]
fn recording_and_spelling_a_subslice_ignore_unrelated_subslices() {
    for unrelated in [0u64, 64, 1024] {
        let _session = crate::kernel::VerificationSession::enter();
        for length in 0..unrelated {
            record_required_construction(&subslice(1_000_000 + length));
        }
        let probe = subslice(7);
        let (found, work) = crate::instrumentation::measure_deterministic_work(|| {
            record_required_construction(&probe);
            is_required_construction(&probe)
        });
        assert!(found);
        assert!(work <= 2, "unrelated={unrelated}, work={work}");
        let (missing, work) = crate::instrumentation::measure_deterministic_work(|| {
            is_required_construction(&subslice(8))
        });
        assert!(!missing);
        assert!(work <= 1, "unrelated={unrelated}, work={work}");
    }
}

/// A fresh session starts with no recorded subslice.
#[test]
fn a_session_entry_clears_recorded_subslices() {
    {
        let _session = crate::kernel::VerificationSession::enter();
        record_required_construction(&subslice(3));
        assert!(is_required_construction(&subslice(3)));
    }
    let _session = crate::kernel::VerificationSession::enter();
    assert!(!is_required_construction(&subslice(3)));
}
