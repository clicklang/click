use super::*;
use crate::kernel::{
    CType, IntegerTerm, KernelTerm, KernelType, MachineBinaryOp, SharedMachineIntegerTerm, Variable,
};

#[test]
fn conversion_root_queries_retain_shared_prefixes() {
    let mut samples = Vec::new();
    for size in [8, 32, 96] {
        let _session = crate::kernel::VerificationSession::enter();
        let ty = MachineIntegerType::Int32;
        let mut term = KernelTerm::variable(KernelType::C(CType::Int32), Variable(982100));
        let narrow = IntegerTerm::from_machine(
            MachineIntegerType::Int8,
            Bitvector32Term::Variable(Variable(982101)),
        )
        .unwrap();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..size {
                term = KernelTerm::arithmetic_binary(
                    ty,
                    MachineBinaryOp::Add,
                    [term.clone(), term.clone()],
                )
                .unwrap();
                let observation = SharedMachineIntegerTerm::from_shared(ty, term.clone()).unwrap();
                let integer = IntegerTerm::Machine(observation.clone());
                assert!(cast_operands(&integer).is_empty());
                assert!(!narrow_widening(&integer, &narrow));
                assert_eq!(
                    widened_narrow_word(&integer).unwrap().retain(ty).id(),
                    observation.id()
                );
                assert!(!observation.has_boxed_operand());
            }
        });
        samples.push((size, work));
    }
    for pair in samples.windows(2) {
        let [(small, sw), (large, lw)] = pair else {
            unreachable!()
        };
        assert!(lw * small * 4 <= sw * large * 5, "{samples:?}");
    }
}
