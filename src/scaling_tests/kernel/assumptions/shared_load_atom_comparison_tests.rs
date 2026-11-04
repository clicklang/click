use super::*;

#[test]
fn growing_shared_snapshot_comparisons_reuse_syntax_but_recheck_loads() {
    let mut samples = Vec::new();
    for size in [8, 32, 128] {
        let _session = crate::kernel::VerificationSession::enter();
        let ty = MachineIntegerType::Int32;
        let (_, _, a, b) = load_pair(ty);
        let mut left = KernelTerm::variable(KernelType::C(ty.c_type()), a);
        let mut right = KernelTerm::variable(KernelType::C(ty.c_type()), b);
        let zero =
            crate::kernel::KernelTermImport::default().machine(ty, &Bitvector32Term::constant(0));
        let condition = |root| {
            ConditionTerm::integer_less_equal(
                IntegerTerm::Machine(SharedMachineIntegerTerm::from_shared(ty, root).unwrap()),
                IntegerTerm::constant_i64(7),
            )
        };
        let exports = KernelTermExport::machine_export_count();
        let calls = std::cell::Cell::new(0);
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..size {
                left = KernelTerm::machine_binary_shared(
                    ty,
                    MachineBinaryOp::Add,
                    [left, zero.clone()],
                );
                right = KernelTerm::machine_binary_shared(
                    ty,
                    MachineBinaryOp::Add,
                    [right, zero.clone()],
                );
                let (l, r) = (condition(left.clone()), condition(right.clone()));
                assert!(conditions_equal_with_load_atoms(&l, &r, &|_, _| {
                    calls.set(calls.get() + 1);
                    true
                }));
                assert!(!conditions_equal_with_load_atoms(&l, &r, &|_, _| {
                    calls.set(calls.get() + 1);
                    false
                }));
            }
        });
        // Acceptance checks the named pair once. Refusal checks both that
        // pair and its raw origins; neither answer is cached as authority.
        assert_eq!(calls.get(), size * 3);
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        samples.push(work);
    }
    assert!(
        samples.windows(2).all(|p| p[1] <= p[0] * 5 + 100),
        "{samples:?}"
    );
}
