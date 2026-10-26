//! Rule K7 in the e-graph: a conversion into an 8- or 16-bit format is in
//! the class of its word, `w & m` or `((w & m) ^ s) - s`
//! (`machine_integer::representation::narrow_cast_word`), with no fact.

use super::*;
use crate::kernel::MachineIntegerType as Ty;
use crate::kernel::VerificationSession;
use crate::kernel::machine_integer::representation::narrow_cast_word;

fn var(id: u64) -> Bitvector32Term {
    Bitvector32Term::Variable(Variable(id))
}

const NARROW: [Ty; 4] = [Ty::Int8, Ty::UInt8, Ty::Int16, Ty::UInt16];
const SOURCES: [Ty; 8] = [
    Ty::Int8,
    Ty::UInt8,
    Ty::Int16,
    Ty::UInt16,
    Ty::Int32,
    Ty::UInt32,
    Ty::Int64,
    Ty::UInt64,
];

#[test]
fn a_narrow_cast_is_its_word_with_no_fact() {
    let _session = VerificationSession::enter();
    for destination in NARROW {
        for source in SOURCES {
            if source == destination {
                continue;
            }
            let x = var(173_001);
            let cast = Bitvector32Term::machine_integer_cast(source, destination, x.clone());
            let word = narrow_cast_word(source, destination, x.clone()).unwrap();
            let graph = EqualityGraph::default();
            assert!(
                graph.are_int32_equal(&cast, &word),
                "{source:?} -> {destination:?}: {cast:?} == {word:?}"
            );
            // Another width's mask is not the cast's word.
            let other = if destination.format().bits() == 8 {
                Ty::UInt16
            } else {
                Ty::UInt8
            };
            let wrong = narrow_cast_word(source, other, x.clone()).unwrap();
            assert!(
                !graph.are_int32_equal(&cast, &wrong),
                "{source:?} -> {destination:?}"
            );
            assert!(
                !graph.are_int32_equal(&cast, &x),
                "{source:?} -> {destination:?}"
            );
        }
    }
}

/// The source's spelling meets the cast through its operand's class: an
/// equality learned of the operand reaches the written mask of the other.
#[test]
fn a_narrow_cast_meets_the_mask_of_an_equal_operand() {
    let _session = VerificationSession::enter();
    let (x, y) = (var(173_011), var(173_012));
    let cast = Bitvector32Term::machine_integer_cast(Ty::UInt32, Ty::UInt8, x.clone());
    let mask = Bitvector32Term::bitwise_and(y.clone(), Bitvector32Term::UInt32Constant(255));
    let mut graph = EqualityGraph::default();
    assert!(!graph.are_int32_equal(&cast, &mask));
    graph.add_int32_equality(&x, &y);
    assert!(graph.are_int32_equal(&cast, &mask));
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/equality_graph/narrow_cast_tests.rs");
}
