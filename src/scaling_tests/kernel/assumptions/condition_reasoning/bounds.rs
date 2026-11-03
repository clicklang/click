use super::*;
use crate::kernel::{KernelTerm, KernelType, MachineBinaryOp, Variable};

#[test]
fn shared_bound_consumers_preserve_dag_operands() {
    let mut samples = Vec::new();
    for size in [8, 32, 96] {
        for ambient in [0, 64] {
            let _session = crate::kernel::VerificationSession::enter();
            let ty = MachineIntegerType::Int32;
            let mut facts = PureFactContext::new();
            for i in 0..ambient {
                facts = facts.assume_condition(
                    ConditionTerm::equal(
                        Bitvector32Term::Variable(Variable(995000 + i)),
                        Bitvector32Term::Constant(7),
                    ),
                    true,
                );
            }
            let mut root = KernelTerm::variable(KernelType::C(ty.c_type()), Variable(994201));
            let observe = |term| IntegerTerm::from_machine(ty, term).unwrap();
            let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
                for level in 0..size {
                    let x = Bitvector32Term::Variable(Variable(996000 + level * 2));
                    let y = Bitvector32Term::Variable(Variable(996001 + level * 2));
                    root = KernelTerm::machine_binary_shared(
                        ty,
                        MachineBinaryOp::Add,
                        [root.clone(), root.clone()],
                    );
                    let operand = SharedMachineIntegerTerm::from_shared(ty, root.clone()).unwrap();
                    let first = ConditionTerm::integer_less_equal(
                        observe(x.clone()),
                        IntegerTerm::Machine(operand.clone()),
                    );
                    let second = ConditionTerm::integer_less_equal(
                        IntegerTerm::Machine(operand.clone()),
                        observe(y.clone()),
                    );
                    facts = facts
                        .assume_condition(first, true)
                        .assume_condition(second, true);
                    assert!(facts.has_upper_bound_at_or_below(&x, &y));
                    assert!(shared_signed_const_add(operand.operand_view(), 1).is_none());
                    assert!(!shared_successor_of(operand.operand_view(), &y));
                    assert!(!operand.has_boxed_operand());
                }
            });
            samples.push((size, ambient, work));
        }
    }
    for pair in samples.chunks_exact(2) {
        assert!(pair[1].2 <= pair[0].2 * 2 + 64, "{samples:?}");
    }
    for pair in samples.chunks_exact(2).collect::<Vec<_>>().windows(2) {
        let (small, _, sw) = pair[0][0];
        let (large, _, lw) = pair[1][0];
        assert!(
            lw * small as usize <= sw * large as usize * 2,
            "{samples:?}"
        );
    }
}
