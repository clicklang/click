// Scaling tests of `src/kernel/reasoning/substitution.rs` (module `machine_integer_substitution_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn machine_backed_integer_substitution_scales_with_shared_dag() {
    for depth in [8, 16, 32, 64] {
        let source = SharedMachineIntegerTerm::intern(
            MachineIntegerType::Int32,
            Bitvector32Term::Variable(Variable(7)),
        );
        let mut term = IntegerTerm::Machine(source);
        for _ in 0..depth {
            term = IntegerTerm::add(term.clone(), term.clone());
        }
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            substitute_bitvector_variable_in_integer(
                &term,
                Variable(7),
                &Bitvector32Term::Constant(7),
            )
        });
        assert!(
            work <= (depth + 1) * 32,
            "unexpected shared DAG work at depth {depth}: {work}"
        );
    }
}

/// A chain of `size` machine operations at `format`, each a `Binary` node
/// (`design/machine-integers.md`, Stage 3): the operators cycle through
/// `+`, `/`, `%`, `>>` and `^`, read signed or unsigned by the format.
fn machine_operation_chain(format: MachineIntegerType, size: u32) -> Bitvector32Term {
    use crate::kernel::MachineBinaryOp as Op;
    let ops = [
        Op::Add,
        Op::Divide,
        Op::Remainder,
        Op::ShiftRight,
        Op::BitwiseXor,
    ];
    let mut term = Bitvector32Term::Variable(Variable(151_000));
    for index in 0..size {
        let operand = Bitvector32Term::Variable(Variable(151_001 + u64::from(index)));
        term =
            Bitvector32Term::machine_binary(format, ops[index as usize % ops.len()], term, operand);
    }
    term
}

/// The work of assuming and deciding an equality over a chain of machine
/// operations grows by a bounded amount per operation at every size, and by
/// the same amount at `int32` and `uint32`, whose operators are one `Binary`
/// node at a format rather than per-width variants. `int64` is linear too.
#[test]
fn machine_operator_chains_cost_the_same_per_node_at_every_format() {
    let measure = |format: MachineIntegerType, size: u32| {
        let chain = machine_operation_chain(format, size);
        let target = Bitvector32Term::Variable(Variable(152_000));
        let equality = ConditionTerm::machine_compare(
            format,
            crate::kernel::CompareRelation::Equal,
            chain,
            target,
        );
        let substituted = substitute_bitvector_variable_in_condition(
            &equality,
            Variable(151_000),
            &Bitvector32Term::Constant(1),
        );
        assert_ne!(substituted, equality);
        crate::instrumentation::measure_deterministic_work(|| {
            let context =
                crate::kernel::PureFactContext::new().assume_condition(equality.clone(), true);
            assert_eq!(context.decide(&equality), Some(true));
        })
        .1
    };
    let sizes = [4u32, 8, 16, 32, 64, 128, 256];
    let mut work_by_format = Vec::new();
    for format in [
        MachineIntegerType::Int32,
        MachineIntegerType::UInt32,
        MachineIntegerType::Int64,
    ] {
        let work: Vec<usize> = sizes.iter().map(|size| measure(format, *size)).collect();
        for (pair, size) in work.windows(2).zip(sizes.windows(2)) {
            let added = (size[1] - size[0]) as usize;
            assert!(
                pair[1] > pair[0] && pair[1] - pair[0] <= 16 * added,
                "{format:?}: {} -> {} operations cost {} -> {}",
                size[0],
                size[1],
                pair[0],
                pair[1]
            );
        }
        work_by_format.push(work);
    }
    assert_eq!(
        work_by_format[0], work_by_format[1],
        "int32 and uint32 chains cost alike"
    );
}
