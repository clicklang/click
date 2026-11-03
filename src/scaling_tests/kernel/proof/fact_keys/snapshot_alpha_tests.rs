// Scaling tests of `src/kernel/proof/fact_keys.rs` (module `snapshot_alpha_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn snapshot_alpha_work_ignores_unrelated_heap_size() {
    let make_memory = |unrelated_size| {
        crate::kernel::intern_c_memory(
            CMemory::new()
                .with_block("snapshot-alpha", 8)
                .with_block("unrelated-snapshot-alpha", unrelated_size),
        )
    };
    let mut work = Vec::new();
    for unrelated_size in [8, 128, 1024, 8192] {
        let memory = make_memory(unrelated_size);
        let term = fold_body(&memory, Variable(318_001));
        let term = IntegerTerm::range_fold(
            int32_index(),
            IntegerTerm::constant_i64(0),
            Variable(318_000),
            Variable(318_001),
            term,
        );
        let (_, measured) = crate::instrumentation::measure_deterministic_work(|| {
            integer_equality_alpha_key(&equality(term)).expect("snapshot alpha key")
        });
        work.push(measured);
    }
    let first = work[0];
    for measured in work.into_iter().skip(1) {
        assert!(
            measured <= first + 8,
            "unrelated heap work: {measured} vs {first}"
        );
    }
}

#[test]
fn snapshot_alpha_registered_load_dags_scale_linearly() {
    let mut work = Vec::new();
    for depth in [8usize, 16, 32, 64] {
        let (_memory, load) = registered_load_chain(depth);
        let term = IntegerTerm::range_fold(
            int32_index(),
            IntegerTerm::constant_i64(0),
            Variable(321_000),
            Variable(321_001),
            IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
                MachineIntegerType::Int32,
                Bitvector32Term::Variable(load),
            )),
        );
        let (_, measured) = crate::instrumentation::measure_deterministic_work(|| {
            integer_equality_alpha_key(&equality(term)).expect("registered load DAG key")
        });
        work.push(measured);
    }
    for pair in work.windows(2) {
        assert!(
            pair[1] <= pair[0] * 3 + 32,
            "registered load work: {work:?}"
        );
    }
}

#[test]
fn snapshot_alpha_registered_load_branching_dags_stay_linear() {
    let mut work = Vec::new();
    for depth in [8usize, 16, 32, 64] {
        let (_memory, load) = registered_load_branching_chain(depth);
        let term = IntegerTerm::range_fold(
            int32_index(),
            IntegerTerm::constant_i64(0),
            Variable(323_000),
            Variable(323_001),
            IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
                MachineIntegerType::Int32,
                Bitvector32Term::Variable(load),
            )),
        );
        let (_, measured) = crate::instrumentation::measure_deterministic_work(|| {
            integer_equality_alpha_key(&equality(term)).expect("branching load DAG key")
        });
        work.push(measured);
    }
    for pair in work.windows(2) {
        assert!(
            pair[1] <= pair[0] * 3 + 32,
            "branching registered load work: {work:?}"
        );
    }
}

#[test]
fn snapshot_alpha_nested_shared_load_dags_scale_linearly() {
    let memory = crate::kernel::intern_c_memory(CMemory::new().with_block("snapshot-alpha", 8));
    let mut work = Vec::new();
    for depth in [8usize, 16, 32, 64] {
        let item = Variable(315_001);
        let mut body = fold_body(&memory, item);
        for _ in 0..depth {
            let child: SharedIntegerTerm = body.into();
            body = IntegerTerm::Add(child.clone(), child);
        }
        let term = IntegerTerm::range_fold(
            int32_index(),
            IntegerTerm::constant_i64(0),
            Variable(315_000),
            item,
            body,
        );
        let (_, measured) = crate::instrumentation::measure_deterministic_work(|| {
            integer_equality_alpha_key(&equality(term)).expect("shared load DAG key")
        });
        work.push(measured);
    }
    for pair in work.windows(2) {
        assert!(pair[1] <= pair[0] * 3 + 32, "snapshot alpha work: {work:?}");
    }
}

#[test]
fn machine_comparison_alpha_keys_retain_shared_dags() {
    use crate::kernel::{KernelTerm, KernelType, MachineBinaryOp, SharedMachineIntegerTerm};
    let samples = [8usize, 32, 96].map(|size| {
        let _session = crate::kernel::VerificationSession::enter();
        let format = MachineIntegerType::UInt64;
        let mut term = KernelTerm::variable(KernelType::C(format.c_type()), Variable(98123));
        for _ in 0..size {
            term = KernelTerm::machine_binary_shared(
                format,
                MachineBinaryOp::Add,
                [term.clone(), term],
            );
        }
        let operand = SharedMachineIntegerTerm::from_shared(format, term).unwrap();
        let proposition = Proposition::ForAll {
            var: Variable(98123),
            name: crate::kernel::BinderName::written("i"),
            sort: Sort::CMachineInteger(format),
            body: Box::new(Proposition::ConditionIs(
                ConditionTerm::IntegerLessThan(
                    IntegerTerm::Machine(operand.clone()).into(),
                    IntegerTerm::Constant(BigInt::from(100)).into(),
                ),
                true,
            )),
        };
        let (key, work) = crate::instrumentation::measure_deterministic_work(|| {
            proposition_identity_key(&proposition)
        });
        assert!(key.is_some());
        assert!(!operand.has_boxed_operand());
        (size, work)
    });
    for pair in samples.windows(2) {
        let [(small, sw), (large, lw)] = pair else {
            unreachable!()
        };
        assert!(lw * small <= sw * large * 2, "{samples:?}");
    }
}
