//! Native 8- and 16-bit nodes: their constructors, widths and congruence.
//! Nothing produces them yet; these pin their meaning before producers do.
use super::*;
use crate::kernel::{CarrierWidth as W, MachineBinaryOp as Op, MachineIntegerType as Ty};

fn var(id: u64) -> MachineTerm {
    MachineTerm::Variable(Variable(id))
}

fn constant(format: Ty, bits: u128) -> MachineTerm {
    MachineTerm::narrow_constant(format, bits)
}

#[test]
fn narrow_constants_fold_modulo_their_width() {
    let _session = crate::kernel::VerificationSession::enter();
    let fold = |format, op, a, b| {
        MachineTerm::machine_binary(format, op, constant(format, a), constant(format, b))
    };
    assert_eq!(fold(Ty::UInt8, Op::Add, 200, 100), constant(Ty::UInt8, 44));
    assert_eq!(fold(Ty::Int8, Op::Subtract, 0, 1), constant(Ty::Int8, 0xff));
    assert_eq!(
        fold(Ty::UInt16, Op::Multiply, 300, 300),
        constant(Ty::UInt16, 90_000 % 65_536)
    );
    assert_eq!(
        fold(Ty::Int16, Op::BitwiseXor, 0xf0f0, 0xffff),
        constant(Ty::Int16, 0x0f0f)
    );
    assert_eq!(
        fold(Ty::UInt8, Op::ShiftLeft, 0x81, 1),
        constant(Ty::UInt8, 0x02)
    );
    // A count at or past the width is not folded, as at 32 bits.
    assert!(matches!(
        fold(Ty::UInt8, Op::ShiftLeft, 1, 8),
        MachineTerm::Binary { .. }
    ));
    assert_eq!(
        MachineTerm::machine_unary(
            Ty::UInt16,
            crate::kernel::MachineUnaryOp::BitwiseNot,
            constant(Ty::UInt16, 1)
        ),
        constant(Ty::UInt16, 0xfffe)
    );
    // Two signednesses of one width are distinct constants of the same bits.
    assert_ne!(constant(Ty::Int8, 0xff), constant(Ty::UInt8, 0xff));
}

#[test]
fn a_narrow_operator_has_its_own_width() {
    let _session = crate::kernel::VerificationSession::enter();
    for (format, width) in [
        (Ty::Int8, W::Bits8),
        (Ty::UInt8, W::Bits8),
        (Ty::Int16, W::Bits16),
        (Ty::UInt16, W::Bits16),
    ] {
        let sum = MachineTerm::machine_binary(format, Op::Add, var(1), constant(format, 1));
        assert_eq!(
            crate::kernel::term_width(&sum),
            Ok(Some(width)),
            "{format:?}"
        );
        // A 32-bit word is not a narrow operand.
        let mixed = MachineTerm::Binary {
            format,
            op: Op::Add,
            left: Box::new(MachineTerm::constant(1)),
            right: Box::new(var(1)),
        };
        assert!(crate::kernel::term_width(&mixed).is_err(), "{format:?}");
        // Division reads a sign and stays promoted.
        let quotient = MachineTerm::Binary {
            format,
            op: Op::Divide,
            left: Box::new(var(1)),
            right: Box::new(var(2)),
        };
        assert!(crate::kernel::term_width(&quotient).is_err(), "{format:?}");
    }
}

#[test]
fn narrow_operators_are_congruent_by_their_bits() {
    let _session = crate::kernel::VerificationSession::enter();
    for (signed, unsigned, width) in [
        (Ty::Int8, Ty::UInt8, W::Bits8),
        (Ty::Int16, Ty::UInt16, W::Bits16),
    ] {
        let graph = EqualityGraph::default();
        let mut state = graph.state.lock().expect("equality graph");
        let terms = &mut state.terms;
        let at = |format, a| MachineTerm::machine_binary(format, Op::Add, a, constant(format, 1));
        assert!(!terms.are_typed_equal(width, &at(unsigned, var(1)), &at(unsigned, var(2))));
        terms.add_typed_equality(width, &var(1), &var(2));
        assert!(terms.are_typed_equal(width, &at(unsigned, var(1)), &at(unsigned, var(2))));
        // Congruence reads only the classes the facts joined.
        assert!(!terms.are_typed_equal(width, &at(signed, var(3)), &at(signed, var(4))));
        terms.add_typed_equality(width, &var(3), &var(4));
        assert!(terms.are_typed_equal(width, &at(signed, var(3)), &at(signed, var(4))));
    }
}

/// A chain of `n` native narrow additions is interned with the same work
/// per node at every size, at each narrow width.
#[test]
fn narrow_operator_chains_intern_with_constant_work_per_node() {
    let _session = crate::kernel::VerificationSession::enter();
    for (format, width) in [
        (Ty::Int8, W::Bits8),
        (Ty::UInt8, W::Bits8),
        (Ty::Int16, W::Bits16),
        (Ty::UInt16, W::Bits16),
    ] {
        let sizes = [8_u64, 32, 128, 512];
        let mut samples = Vec::new();
        for size in sizes {
            // Keep term-bridge imports cold at every sample size.
            crate::kernel::clear_machine_observation_memo();
            let mut sum = var(10_000);
            for index in 1..size {
                sum = MachineTerm::machine_binary(format, Op::Add, sum, var(10_000 + index));
            }
            let graph = EqualityGraph::default();
            let mut state = graph.state.lock().expect("equality graph");
            let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
                state
                    .terms
                    .add_typed_equality(width, &sum, &var(90_000 + size));
            });
            samples.push(work);
        }
        let step =
            |i: usize| (samples[i + 1] - samples[i]) as f64 / (sizes[i + 1] - sizes[i]) as f64;
        for i in 1..sizes.len() - 1 {
            assert_eq!(step(i), step(0), "{format:?}: {samples:?}");
        }
        // A bare chain is interned with a small constant per node: no
        // relation that only a widening or a narrowing of the chain needs
        // (rule N) fires on it (about 9.5 units per node, 2026-11-02).
        assert!(step(0) <= 16.0, "{format:?}: {samples:?}");
    }
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/equality_graph/narrow_tests.rs");
}

fn narrow_stored_value(format: Ty, bits: u128) -> ProgramValue {
    let value = constant(format, bits);
    match format {
        Ty::Int8 => ProgramValue::Int8(value),
        Ty::UInt8 => ProgramValue::UInt8(value),
        Ty::Int16 => ProgramValue::Int16(value),
        Ty::UInt16 => ProgramValue::UInt16(value),
        _ => unreachable!(),
    }
}

fn narrow_equal(
    graph: &EqualityGraph,
    format: Ty,
    left: &MachineTerm,
    right: &MachineTerm,
) -> bool {
    graph.knows_condition(
        &ConditionTerm::machine_compare(
            format,
            CompareRelation::Equal,
            left.clone(),
            right.clone(),
        ),
        true,
    )
}

fn narrow_equal_views(
    graph: &EqualityGraph,
    format: Ty,
    left: crate::kernel::MachineOperandView<'_>,
    right: crate::kernel::MachineOperandView<'_>,
) -> bool {
    graph.are_integer_equal(
        &crate::kernel::IntegerTerm::Machine(left.retain(format)),
        &crate::kernel::IntegerTerm::Machine(right.retain(format)),
    )
}

fn check_narrow_store_equation(format: Ty) {
    use crate::kernel::{KernelTermImport, MachineOperandView as V, VerificationSession};
    let _session = VerificationSession::enter();
    for aliased in [false, true] {
        let pointer = Address {
            base: "narrow".into(),
            offset: AddressOffset::Constant(0),
        };
        let query = if aliased {
            Address::symbolic(Variable(993201))
        } else {
            pointer.clone()
        };
        let bits = if format.format().bits() == 8 {
            0xf1
        } else {
            0xff01
        };
        let value = narrow_stored_value(format, bits);
        let stored = constant(format, bits);
        let kind = LoadKind::of_value(&value).unwrap();
        let memory = intern_memory(
            SymbolicMemory::new()
                .with_block("narrow", 8)
                .store(pointer.clone(), value.clone()),
        );
        let read =
            MachineTerm::read_named(ProgramPoint::at(&memory), Box::new(query.clone()), kind);
        let shared = KernelTermImport::default()
            .machine_arithmetic(format, &read)
            .unwrap();
        let empty = PureFactContext::new().assume_condition(
            ConditionTerm::address_equal(pointer.clone(), query.clone()),
            true,
        );
        assert!(
            !narrow_equal_views(
                &empty.equality_graph,
                format,
                V::Shared(&shared),
                V::Legacy(&stored)
            ),
            "shared {format:?}, alias={aliased}: a read must not import its cached value"
        );
        assert!(
            !narrow_equal(&empty.equality_graph, format, &read, &stored),
            "native {format:?}, alias={aliased}: a read must not import its cached value"
        );
        let equation =
            crate::kernel::memory_history::store_value_equation(memory.memory(), &pointer, &value)
                .unwrap();
        let established = empty.clone().assume_proposition(equation.clone());
        assert!(
            narrow_equal(&established.equality_graph, format, &read, &stored),
            "{format:?}, alias={aliased}: explicit equation"
        );
        assert!(narrow_equal_views(
            &established.equality_graph,
            format,
            V::Shared(&shared),
            V::Legacy(&stored)
        ));
        assert!(!narrow_equal(&empty.equality_graph, format, &read, &stored));
        assert_eq!(shared.machine_read_leaf(), Some(&read));
        if aliased {
            let before_alias = PureFactContext::new().assume_proposition(equation);
            assert!(!narrow_equal(
                &before_alias.equality_graph,
                format,
                &read,
                &stored
            ));
            let after_alias = before_alias.assume_condition(
                ConditionTerm::address_equal(pointer.clone(), query.clone()),
                true,
            );
            assert!(narrow_equal(
                &after_alias.equality_graph,
                format,
                &read,
                &stored
            ));
        }
        let new_value = narrow_stored_value(format, 4);
        let after = intern_memory(
            memory
                .memory()
                .clone()
                .store(pointer.clone(), new_value.clone()),
        );
        let new_read = MachineTerm::read_named(ProgramPoint::at(&after), Box::new(query), kind);
        assert!(!narrow_equal(
            &established.equality_graph,
            format,
            &new_read,
            &constant(format, 4)
        ));
        let updated = established.assume_proposition(
            crate::kernel::memory_history::store_value_equation(
                after.memory(),
                &pointer,
                &new_value,
            )
            .unwrap(),
        );
        assert!(narrow_equal(
            &updated.equality_graph,
            format,
            &new_read,
            &constant(format, 4)
        ));
        assert!(!narrow_equal(
            &updated.equality_graph,
            format,
            &new_read,
            &stored
        ));
        assert!(narrow_equal(
            &updated.equality_graph,
            format,
            &read,
            &stored
        ));
    }
}

#[test]
fn int8_read_requires_store_equation() {
    check_narrow_store_equation(Ty::Int8);
}
#[test]
fn uint8_read_requires_store_equation() {
    check_narrow_store_equation(Ty::UInt8);
}
#[test]
fn int16_read_requires_store_equation() {
    check_narrow_store_equation(Ty::Int16);
}
#[test]
fn uint16_read_requires_store_equation() {
    check_narrow_store_equation(Ty::UInt16);
}
