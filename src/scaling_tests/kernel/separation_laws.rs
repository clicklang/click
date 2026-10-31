use super::*;

#[test]
fn subrange_law_does_not_enumerate_the_interval() {
    let costs = [4u32, 64, 4096, 1_000_000].map(|length| {
        let _session = crate::kernel::VerificationSession::enter();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::kernel::prove_separation_subrange(
                CPointerValue::new(Pointer::symbolic(Variable(8_390_000)), CType::Int64Pointer),
                8,
                0u32.into(),
                length.into(),
                1u32.into(),
                (length - 1).into(),
            )
        });
        work
    });
    assert!(costs[0] > 0);
    assert!(costs.iter().all(|cost| *cost == costs[0]), "{costs:?}");
}

#[test]
fn elements_law_does_not_walk_the_index_distance() {
    for format in [
        MachineIntegerType::Int32,
        MachineIntegerType::Int64,
        MachineIntegerType::UInt64,
    ] {
        for width in [1, 8, 16] {
            let costs = [4i32, 64, 4096, i32::MAX].map(|distance| {
                let _session = crate::kernel::VerificationSession::enter();
                let term = |n: i32| match format {
                    MachineIntegerType::Int32 => Bitvector32Term::Constant(n as u32),
                    _ => Bitvector32Term::Int64Constant(i64::from(n)),
                };
                let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                    crate::kernel::prove_separation_elements(
                        CPointerValue::new(
                            Pointer::symbolic(Variable(8_390_001)),
                            CType::Int64Pointer,
                        ),
                        width,
                        format,
                        term(0),
                        term(distance),
                    )
                });
                work
            });
            assert!(costs[0] > 0);
            assert!(costs.iter().all(|cost| *cost == costs[0]), "{costs:?}");
        }
    }
}
