use super::*;

fn subslice(length: u64) -> Pointer {
    let ProgramValue::Pointer(data) =
        ProgramValue::typed_pointer(Address::null(), ProgramType::UInt8Pointer)
    else {
        unreachable!("a typed pointer is a pointer")
    };
    data.with_element_count(OldMachineTerm::uint64_constant(length))
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
        let other = subslice(8);
        let (missing, work) =
            crate::instrumentation::measure_deterministic_work(|| is_required_construction(&other));
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
