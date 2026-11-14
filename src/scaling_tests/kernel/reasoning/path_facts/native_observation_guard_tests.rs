// Scaling tests of `src/kernel/reasoning/path_facts.rs` (module
// `native_observation_guard_tests`): exact native observation guard queries.
use super::*;

#[test]
fn native_observation_guard_work_is_flat_beside_unrelated_ambient_conditions() {
    for ty in [
        MachineIntegerType::Int32,
        MachineIntegerType::UInt32,
        MachineIntegerType::Int64,
        MachineIntegerType::UInt64,
    ] {
        let mut samples = Vec::new();
        for size in [16, 64, 256, 1024] {
            let _session = crate::kernel::VerificationSession::enter();
            let (native, observed) = equalities(ty);
            let mut context = PureFactContext::new().defer_non_exact_condition_reasoning();
            for index in 0..size {
                context = context
                    .assume_condition(ConditionTerm::Variable(Variable(913_000 + index)), true);
            }
            context = context.assume_condition(native, false);
            let no_path_facts = ExecutionFacts::new();
            let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                decide_with_facts(&context, &no_path_facts, &observed)
            });
            assert_eq!(result, Some(false));
            assert!(work < 512, "{ty:?}, {size}: {work}");
            samples.push(work);
        }
        assert!(
            samples.iter().max().unwrap() - samples.iter().min().unwrap() <= 64,
            "{ty:?}: {samples:?}"
        );
    }
}

fn growing_arithmetic_guards(truth: Option<bool>) {
    use crate::kernel::{
        KernelTerm, KernelTermExport, KernelType, MachineBinaryOp, SharedMachineIntegerTerm,
    };
    let mut samples = Vec::new();
    for size in [8, 32, 128] {
        let _session = crate::kernel::VerificationSession::enter();
        let ty = MachineIntegerType::Int32;
        let variable = |id| KernelTerm::variable(KernelType::Program(ty.c_type()), Variable(id));
        let mut root = variable(985001);
        let other = variable(985002);
        let zero =
            crate::kernel::KernelTermImport::default().machine(ty, &MachineTerm::constant(0));
        let observe =
            |root| IntegerTerm::Machine(SharedMachineIntegerTerm::from_shared(ty, root).unwrap());
        let mut context = PureFactContext::new().defer_non_exact_condition_reasoning();
        let exports = KernelTermExport::machine_export_count();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for n in 0..size {
                root = KernelTerm::machine_binary_shared(
                    ty,
                    MachineBinaryOp::Add,
                    [root, zero.clone()],
                );
                context =
                    context.assume_condition(ConditionTerm::Variable(Variable(985010 + n)), true);
                let goal =
                    ConditionTerm::integer_equal(observe(root.clone()), observe(other.clone()));
                let path = truth.map_or_else(ExecutionFacts::new, |truth| {
                    ExecutionFacts::from(vec![ExecutionPureFact::new(Proposition::ConditionIs(
                        goal.clone(),
                        truth,
                    ))])
                });
                assert_eq!(decide_with_facts(&context, &path, &goal), truth);
            }
        });
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        samples.push(work);
    }
    assert!(
        samples.windows(2).all(|p| p[1] <= p[0] * 5 + 100),
        "{truth:?}: {samples:?}"
    );
}

#[test]
fn growing_proven_execution_guards_reuse_prefixes() {
    growing_arithmetic_guards(Some(true));
}
#[test]
fn growing_refuted_execution_guards_reuse_prefixes() {
    growing_arithmetic_guards(Some(false));
}
#[test]
fn growing_unresolved_execution_guards_reuse_prefixes() {
    growing_arithmetic_guards(None);
}
