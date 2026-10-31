//! Native 8- and 16-bit nodes: their constructors, widths and congruence.
//! Nothing produces them yet; these pin their meaning before producers do.
use super::*;
use crate::kernel::{CarrierWidth as W, MachineBinaryOp as Op, MachineIntegerType as Ty};

fn var(id: u64) -> Bitvector32Term {
    Bitvector32Term::Variable(Variable(id))
}

fn constant(format: Ty, bits: u128) -> Bitvector32Term {
    Bitvector32Term::narrow_constant(format, bits)
}

#[test]
fn narrow_constants_fold_modulo_their_width() {
    let _session = crate::kernel::VerificationSession::enter();
    let fold = |format, op, a, b| {
        Bitvector32Term::machine_binary(format, op, constant(format, a), constant(format, b))
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
        Bitvector32Term::Binary { .. }
    ));
    assert_eq!(
        Bitvector32Term::machine_unary(
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
        let sum = Bitvector32Term::machine_binary(format, Op::Add, var(1), constant(format, 1));
        assert_eq!(
            crate::kernel::term_width(&sum),
            Ok(Some(width)),
            "{format:?}"
        );
        // A 32-bit word is not a narrow operand.
        let mixed = Bitvector32Term::Binary {
            format,
            op: Op::Add,
            left: Box::new(Bitvector32Term::Constant(1)),
            right: Box::new(var(1)),
        };
        assert!(crate::kernel::term_width(&mixed).is_err(), "{format:?}");
        // Division reads a sign and stays promoted.
        let quotient = Bitvector32Term::Binary {
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
        let at =
            |format, a| Bitvector32Term::machine_binary(format, Op::Add, a, constant(format, 1));
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
            let mut sum = var(10_000);
            for index in 1..size {
                sum = Bitvector32Term::machine_binary(format, Op::Add, sum, var(10_000 + index));
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
    }
}
