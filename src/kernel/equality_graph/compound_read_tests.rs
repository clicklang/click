use super::*;
use crate::kernel::{
    KernelTermImport, MachineBinaryOp as Op, MachineIntegerType as M, MachineOperandView as V,
};

fn sum(format: M, left: OldMachineTerm, right: OldMachineTerm) -> OldMachineTerm {
    OldMachineTerm::machine_binary(format, Op::Add, left, right)
}
fn number(format: M, n: u128) -> OldMachineTerm {
    match format {
        M::Int32 => OldMachineTerm::constant(n as u32),
        M::UInt64 => OldMachineTerm::uint64_constant(n as u64),
        _ => unreachable!(),
    }
}
fn stored(format: M, value: OldMachineTerm) -> ProgramValue {
    match format {
        M::Int32 => ProgramValue::Int32(value),
        M::UInt64 => ProgramValue::UInt64(value),
        _ => unreachable!(),
    }
}
fn equal(graph: &EqualityGraph, format: M, left: &OldMachineTerm, right: &OldMachineTerm) -> bool {
    match format {
        M::Int32 => graph.are_int32_equal(left, right),
        M::UInt64 => graph.are_uint64_equal(left, right),
        _ => unreachable!(),
    }
}

#[test]
fn compound_read_queries_require_explicit_equations() {
    let _session = crate::kernel::VerificationSession::enter();
    for format in [M::Int32, M::UInt64] {
        let slot = Address::new("compound-slot".into(), AddressOffset::constant(0));
        let value = stored(format, number(format, 7));
        let memory = intern_memory(SymbolicMemory::new().store(slot.clone(), value.clone()));
        let kind = LoadKind::of_value(&value).unwrap();
        if kind.is_word32() {
            crate::kernel::eval::record_load_access_width(memory.memory(), &slot, 4);
        }
        let read =
            OldMachineTerm::read_named(ProgramPoint::at(&memory), Box::new(slot.clone()), kind);
        let expression = sum(format, read.clone(), number(format, 3));
        let expected = number(format, 10);
        let empty = PureFactContext::new();
        assert!(
            !equal(&empty.equality_graph, format, &expression, &expected),
            "{format:?}: compound query imported a cached value"
        );
        let equation =
            crate::kernel::memory_history::store_value_equation(memory.memory(), &slot, &value)
                .unwrap();
        let facts = empty.clone().assume_proposition(equation);
        assert!(
            equal(&facts.equality_graph, format, &expression, &expected),
            "{format:?}: explicit equation"
        );
        assert!(!equal(
            &empty.equality_graph,
            format,
            &expression,
            &expected
        ));
        let alias = Address::symbolic(Variable(989101));
        if kind.is_word32() {
            // A typed word-read producer records this width for each address.
            crate::kernel::eval::record_load_access_width(memory.memory(), &alias, 4);
        }
        let through_alias = sum(
            format,
            OldMachineTerm::read_named(ProgramPoint::at(&memory), Box::new(alias.clone()), kind),
            number(format, 3),
        );
        assert!(!equal(
            &facts.equality_graph,
            format,
            &through_alias,
            &expected
        ));
        let facts = facts.assume_condition(OldConditionTerm::address_equal(slot, alias), true);
        assert!(equal(
            &facts.equality_graph,
            format,
            &through_alias,
            &expected
        ));
        if format == M::Int32 {
            let shared = KernelTermImport::default()
                .machine_arithmetic(format, &expression)
                .unwrap();
            assert!(
                !empty
                    .equality_graph
                    .are_int32_equal_views(V::Shared(&shared), V::Old(&expected))
            );
            assert!(
                facts
                    .equality_graph
                    .are_int32_equal_views(V::Shared(&shared), V::Old(&expected))
            );
        }
    }
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/equality_graph/compound_read_tests.rs");
}
