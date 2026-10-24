//! The per-format test matrix (`design/machine-integers.md`, "Coverage").
//!
//! Each test builds the same terms, conditions and rule applications at
//! every format in [`FORMATS`] and checks that they decide alike: the rule
//! applies, and on constants it agrees with the exact arithmetic wherever
//! the values fit. A format a rule does not reach must be listed in that
//! rule's gap list below, with the stage that removes the gap, so a rule
//! that silently misses a format, or newly reaches one, fails here.

use super::representation::{self, Division};
use super::*;
use crate::kernel::proof::arithmetic_special::{
    SpecialArithmeticCertificate, SpecialArithmeticNode,
};
use crate::kernel::{
    Bitvector32Term, ConditionTerm, IntegerTerm, MachineIntegerConstant, MachineIntegerType as Ty,
    OverflowOperation, Proposition, SharedMachineIntegerTerm, Variable,
};
use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};

/// Every format has a comparison (`Compare`, Stage 2).
const COMPARISON_GAPS: &[Ty] = &[];
/// Formats whose Integer comparisons keep their Integer spelling: the
/// native node exists and reads back exactly, but the kernel's order
/// reasoning decides 128-bit comparisons as Integers
/// (`representation::spells_comparison_natively`).
const INTEGER_SPELLED_COMPARISONS: &[Ty] = &[Ty::Int128, Ty::UInt128];
/// No 128-bit operator exists (Stage 3 adds `Binary`).
const OPERATION_GAPS: &[Ty] = &[Ty::Int128, Ty::UInt128];
/// Every format has an overflow test (`Overflows`, Stage 2).
const DEFINEDNESS_GAPS: &[Ty] = &[];
/// A narrow quotient is computed on promoted `int` words and so is never a
/// narrow observation; there are no 128-bit operators (Stage 3).
const DIVISION_GAPS: &[Ty] = &[
    Ty::Int8,
    Ty::UInt8,
    Ty::Int16,
    Ty::UInt16,
    Ty::Int128,
    Ty::UInt128,
];

fn in_gaps(gaps: &[Ty], ty: Ty) -> bool {
    gaps.contains(&ty)
}

fn contains(ty: Ty, value: &BigInt) -> bool {
    let (min, max) = range::range(ty);
    &min <= value && value <= &max
}

/// Values of `ty` at and around its endpoints, zero and small numbers.
fn samples(ty: Ty) -> Vec<BigInt> {
    let (min, max) = range::range(ty);
    let mut values = vec![
        min.clone(),
        &min + 1,
        BigInt::from(-7),
        BigInt::from(-1),
        BigInt::zero(),
        BigInt::one(),
        BigInt::from(2),
        BigInt::from(7),
        BigInt::from(100),
        &max - 1,
        max.clone(),
    ];
    values.retain(|value| contains(ty, value));
    values.sort();
    values.dedup();
    values
}

fn constant(ty: Ty, value: &BigInt) -> Bitvector32Term {
    range::constant_word(ty, value).unwrap_or_else(|| panic!("{value} is in {ty:?}"))
}

/// A symbolic value of `ty` whose word is a canonical carrier: a variable
/// at 32 bits and more, and for a narrow format the conversion of an
/// `int32` variable, as a narrow value is never a bare unregistered word.
fn value(ty: Ty, variable: u64) -> Bitvector32Term {
    let word = Bitvector32Term::Variable(Variable(variable));
    if ty.format().bits() < 32 {
        Bitvector32Term::MachineIntegerCast {
            value: Box::new(word),
            source: Ty::Int32,
            destination: ty,
        }
    } else {
        word
    }
}

fn observe(ty: Ty, word: Bitvector32Term) -> IntegerTerm {
    IntegerTerm::from_machine(ty, word).expect("every format observes its values")
}

fn integer_condition(relation: Relation, left: IntegerTerm, right: IntegerTerm) -> ConditionTerm {
    match relation {
        Relation::Less => ConditionTerm::IntegerLessThan(left.into(), right.into()),
        Relation::LessEqual => ConditionTerm::IntegerLessEqual(left.into(), right.into()),
        Relation::Equal => ConditionTerm::IntegerEqual(left.into(), right.into()),
        Relation::NotEqual => ConditionTerm::IntegerNotEqual(left.into(), right.into()),
    }
}

fn holds(relation: Relation, left: &BigInt, right: &BigInt) -> bool {
    match relation {
        Relation::Less => left < right,
        Relation::LessEqual => left <= right,
        Relation::Equal => left == right,
        Relation::NotEqual => left != right,
    }
}

fn exact(operation: Operation, x: &BigInt, y: &BigInt) -> BigInt {
    match operation {
        Operation::Add => x + y,
        Operation::Subtract => x - y,
        Operation::Multiply => x * y,
    }
}

#[test]
fn the_matrix_names_every_format_once() {
    let mut seen = std::collections::HashSet::new();
    for ty in FORMATS {
        assert!(seen.insert(ty.format()), "{ty:?} is listed twice");
    }
    // Every width and signedness the format descriptor admits.
    for width in [8, 16, 32, 64, 128] {
        for signed in [false, true] {
            assert!(
                FORMATS
                    .iter()
                    .any(|ty| ty.format().bits() == width && ty.format().is_signed() == signed),
                "no format of {width} bits, signed {signed}"
            );
        }
    }
}

#[test]
fn every_format_has_its_range_and_spells_its_constants() {
    for ty in FORMATS {
        let (min, max) = range::range(ty);
        let width = ty.format().bits();
        let expected = if ty.format().is_signed() {
            (
                -(BigInt::one() << (width - 1)),
                (BigInt::one() << (width - 1)) - 1,
            )
        } else {
            (BigInt::zero(), (BigInt::one() << width) - 1)
        };
        assert_eq!((min.clone(), max.clone()), expected, "{ty:?}");
        for value in samples(ty) {
            let word = constant(ty, &value);
            assert_eq!(
                IntegerTerm::from_machine(ty, word),
                Some(IntegerTerm::Constant(value.clone())),
                "{ty:?} {value}"
            );
        }
        assert_eq!(range::constant_word(ty, &(&max + 1)), None, "{ty:?}");
        assert_eq!(range::constant_word(ty, &(&min - 1)), None, "{ty:?}");
        // The range fact of a symbolic value names its format's endpoints.
        let IntegerTerm::Machine(machine) = observe(ty, value(ty, 172_001)) else {
            panic!("{ty:?} observes a variable as a machine value");
        };
        for upper in [false, true] {
            let Proposition::ConditionIs(ConditionTerm::IntegerLessEqual(low, high), true) =
                range::range_fact(&machine, upper)
            else {
                panic!("{ty:?} range fact is an order");
            };
            let endpoint = if upper {
                high.as_const()
            } else {
                low.as_const()
            };
            assert_eq!(endpoint, Some(if upper { &max } else { &min }), "{ty:?}");
        }
    }
}

#[test]
fn exact_comparison_decides_alike_at_every_format() {
    for ty in FORMATS {
        let (a, b) = (value(ty, 172_011), value(ty, 172_012));
        for relation in Relation::ALL {
            let condition =
                integer_condition(relation, observe(ty, a.clone()), observe(ty, b.clone()));
            let native = comparison::native_comparison_of_integer_observation(&condition, true);
            if in_gaps(COMPARISON_GAPS, ty) {
                assert_eq!(native, None, "{ty:?} {relation:?} has no native comparison");
                continue;
            }
            let (native, truth) = if in_gaps(INTEGER_SPELLED_COMPARISONS, ty) {
                assert_eq!(
                    native, None,
                    "{ty:?} {relation:?} keeps its Integer spelling"
                );
                representation::comparison(ty, relation, a.clone(), b.clone())
                    .unwrap_or_else(|| panic!("{ty:?} {relation:?} has a native comparison"))
            } else {
                native.unwrap_or_else(|| panic!("{ty:?} {relation:?} reads natively"))
            };
            // The converse reading gives the Integer comparison back, with
            // `!=` as a false equality.
            let readings = comparison::integer_observations_of_native_comparison(
                &Proposition::ConditionIs(native, truth),
            );
            let expected = match relation {
                Relation::NotEqual => Proposition::ConditionIs(
                    integer_condition(
                        Relation::Equal,
                        observe(ty, a.clone()),
                        observe(ty, b.clone()),
                    ),
                    false,
                ),
                _ => Proposition::ConditionIs(condition.clone(), true),
            };
            assert!(
                readings.contains(&expected),
                "{ty:?} {relation:?}: {readings:?}"
            );
            // On constants the native comparison decides as the Integers do.
            for x in samples(ty) {
                for y in samples(ty) {
                    let (folded, truth) = representation::comparison(
                        ty,
                        relation,
                        constant(ty, &x),
                        constant(ty, &y),
                    )
                    .unwrap();
                    assert_eq!(
                        folded,
                        ConditionTerm::Constant(truth == holds(relation, &x, &y)),
                        "{ty:?} {x} {relation:?} {y}"
                    );
                }
            }
        }
    }
}

/// An order is a native comparison at its own format, of the operands' words
/// as they are: `uint32` and `uint64` orders are unsigned comparisons, not a
/// signed comparison of re-encoded words. A narrow order is the `int32` order
/// of its canonical words. Each reads back at its format alone.
#[test]
fn every_order_is_native_at_its_own_format() {
    use crate::kernel::CompareRelation;
    for ty in FORMATS {
        let (a, b) = (value(ty, 172_031), value(ty, 172_032));
        let filed = if ty.format().bits() < 32 {
            Ty::Int32
        } else {
            ty
        };
        for (relation, compare) in [
            (Relation::Less, CompareRelation::LessThan),
            (Relation::LessEqual, CompareRelation::LessEqual),
        ] {
            let (native, truth) = representation::comparison(ty, relation, a.clone(), b.clone())
                .unwrap_or_else(|| panic!("{ty:?} {relation:?} has a native comparison"));
            assert!(truth, "{ty:?} {relation:?}");
            assert_eq!(
                native,
                ConditionTerm::Compare {
                    format: filed,
                    relation: compare,
                    left: Box::new(a.clone()),
                    right: Box::new(b.clone()),
                },
                "{ty:?} {relation:?}"
            );
            let readings = comparison::integer_observations_of_native_comparison(
                &Proposition::ConditionIs(native, true),
            );
            let expected = Proposition::ConditionIs(
                integer_condition(relation, observe(ty, a.clone()), observe(ty, b.clone())),
                true,
            );
            assert_eq!(readings, vec![expected], "{ty:?} {relation:?}");
        }
    }
}

fn identity_certificate(result: Proposition) -> SpecialArithmeticCertificate {
    SpecialArithmeticCertificate {
        nodes: vec![SpecialArithmeticNode::IntegerOperationIdentity {
            bounds: vec![0, 1],
            result,
        }],
        conclusion: 0,
    }
}

#[test]
fn in_range_identity_holds_at_every_format() {
    for ty in FORMATS {
        let (a, b) = (value(ty, 172_021), value(ty, 172_022));
        for operation in Operation::ALL {
            let word = representation::operation_word(
                ty,
                operation,
                Box::new(a.clone()),
                Box::new(b.clone()),
            );
            if in_gaps(OPERATION_GAPS, ty) {
                assert_eq!(word, None, "{ty:?} {operation:?} has no operator");
                continue;
            }
            let word = word.unwrap_or_else(|| panic!("{ty:?} {operation:?} has an operator"));
            assert_eq!(
                representation::word_operation(ty, &word),
                Some((operation, &a, &b)),
                "{ty:?} {operation:?}"
            );
            let observed = observe(ty, word);
            let value = operation.exact(observe(ty, a.clone()), observe(ty, b.clone()));
            assert_eq!(
                identity::mathematical(&observed),
                Some((ty, value.clone())),
                "{ty:?} {operation:?}"
            );
            // The certificate rule accepts the identity under the format's
            // range, and refuses it under a range one wider.
            let (min, max) = range::range(ty);
            let bounds = |low: BigInt, high: BigInt| {
                vec![
                    Proposition::ConditionIs(
                        ConditionTerm::integer_less_equal(
                            IntegerTerm::constant(low),
                            value.clone(),
                        ),
                        true,
                    ),
                    Proposition::ConditionIs(
                        ConditionTerm::integer_less_equal(
                            value.clone(),
                            IntegerTerm::constant(high),
                        ),
                        true,
                    ),
                ]
            };
            let goal = Proposition::ConditionIs(
                ConditionTerm::integer_equal(observed.clone(), value.clone()),
                true,
            );
            let certificate = identity_certificate(goal.clone());
            assert!(
                certificate
                    .check(&goal, &bounds(min.clone(), max.clone()))
                    .is_ok(),
                "{ty:?} {operation:?}"
            );
            assert!(
                certificate
                    .check(&goal, &bounds(min.clone(), &max + 1))
                    .is_err(),
                "{ty:?} {operation:?}"
            );
            // On constants whose exact result fits, the machine result is
            // the exact one.
            for x in samples(ty) {
                for y in samples(ty) {
                    let exact = exact(operation, &x, &y);
                    if !contains(ty, &exact) {
                        continue;
                    }
                    let folded = representation::folded_operation_word(
                        ty,
                        operation,
                        constant(ty, &x),
                        constant(ty, &y),
                    )
                    .unwrap();
                    assert_eq!(
                        IntegerTerm::from_machine(ty, folded),
                        Some(IntegerTerm::Constant(exact.clone())),
                        "{ty:?} {x} {operation:?} {y}"
                    );
                }
            }
        }
    }
}

/// The folding overflow constructor at `ty`, the oracle the definedness
/// table's nodes are checked against.
fn folded_overflow(
    ty: Ty,
    operation: Operation,
    left: Bitvector32Term,
    right: Bitvector32Term,
) -> ConditionTerm {
    let op = match operation {
        Operation::Add => OverflowOperation::Add,
        Operation::Subtract => OverflowOperation::Subtract,
        Operation::Multiply => OverflowOperation::Multiply,
    };
    ConditionTerm::machine_overflows(ty, op, left, right)
}

#[test]
fn definedness_is_the_range_of_the_exact_result_at_every_format() {
    for ty in FORMATS {
        let (a, b) = (value(ty, 172_031), value(ty, 172_032));
        assert_eq!(
            representation::has_overflow_test(ty),
            !in_gaps(DEFINEDNESS_GAPS, ty),
            "{ty:?}"
        );
        // Definedness facts are filed only where C's overflow is undefined
        // behavior; an unsigned overflow is a wrap, and its test is
        // kernel-internal (`design/machine-integers.md`, "Decisions").
        assert_eq!(
            definedness::defined_formats().any(|defined| defined == ty),
            matches!(ty, Ty::Int32 | Ty::Int64),
            "{ty:?}"
        );
        for operation in Operation::ALL {
            let condition = representation::overflow_condition(
                ty,
                operation,
                Box::new(a.clone()),
                Box::new(b.clone()),
            );
            if in_gaps(DEFINEDNESS_GAPS, ty) {
                assert_eq!(condition, None, "{ty:?} {operation:?} has no overflow test");
                continue;
            }
            let condition =
                condition.unwrap_or_else(|| panic!("{ty:?} {operation:?} has an overflow test"));
            assert!(
                representation::overflow_operation(&condition)
                    .is_some_and(|(found, op, _, _)| found == ty && op == operation),
                "{ty:?} {operation:?}"
            );
            let fact = Proposition::ConditionIs(condition, false);
            let value = operation.exact(observe(ty, a.clone()), observe(ty, b.clone()));
            let (min, max) = range::range(ty);
            let bounds = definedness::integer_bounds_of_definedness(&fact);
            assert_eq!(
                bounds,
                vec![
                    Proposition::ConditionIs(
                        ConditionTerm::integer_less_equal(
                            value.clone(),
                            IntegerTerm::constant(max)
                        ),
                        true,
                    ),
                    Proposition::ConditionIs(
                        ConditionTerm::integer_greater_equal(value, IntegerTerm::constant(min)),
                        true,
                    ),
                ],
                "{ty:?} {operation:?}"
            );
            for bound in &bounds {
                assert_eq!(
                    definedness::overflow_fact_of_integer_bound(bound, FORMATS.into_iter()),
                    Some(fact.clone()),
                    "{ty:?} {operation:?}"
                );
                // The kernel files the converse only where definedness is
                // filed.
                assert_eq!(
                    definedness::definedness_of_integer_bound(bound).is_some(),
                    representation::files_definedness(ty),
                    "{ty:?} {operation:?}"
                );
            }
            for x in samples(ty) {
                for y in samples(ty) {
                    assert_eq!(
                        folded_overflow(ty, operation, constant(ty, &x), constant(ty, &y)),
                        ConditionTerm::Constant(!contains(ty, &exact(operation, &x, &y))),
                        "{ty:?} {x} {operation:?} {y}"
                    );
                }
            }
        }
    }
}

/// A division node `word_division` reads at `ty`, with `operand` and
/// `divisor`.
fn division_word(
    ty: Ty,
    division: Division,
    operand: Bitvector32Term,
    divisor: Bitvector32Term,
) -> Option<Bitvector32Term> {
    use Bitvector32Term as T;
    let (operand, divisor) = (Box::new(operand), Box::new(divisor));
    let candidates = match division {
        Division::Quotient => [
            T::Divide(operand.clone(), divisor.clone()),
            T::UnsignedDivide(operand.clone(), divisor.clone()),
            T::Int64Divide(operand.clone(), divisor.clone()),
            T::UInt64Divide(operand, divisor),
        ],
        Division::ShiftRight => [
            T::ArithmeticShiftRight(operand.clone(), divisor.clone()),
            T::LogicalShiftRight(operand.clone(), divisor.clone()),
            T::Int64ArithmeticShiftRight(operand.clone(), divisor.clone()),
            T::UInt64LogicalShiftRight(operand, divisor),
        ],
        Division::Remainder => [
            T::Remainder(operand.clone(), divisor.clone()),
            T::UnsignedRemainder(operand.clone(), divisor.clone()),
            T::Int64Remainder(operand.clone(), divisor.clone()),
            T::UInt64Remainder(operand, divisor),
        ],
    };
    let mut accepted = candidates.into_iter().filter(|word| {
        representation::word_division(ty, word).is_some_and(|(found, _, _)| found == division)
    });
    let word = accepted.next();
    assert!(
        accepted.next().is_none(),
        "{ty:?} reads one node per division"
    );
    word
}

/// Truncating quotient and remainder, and floor shift, of exact Integers.
fn divide(division: Division, x: &BigInt, divisor: &BigInt) -> BigInt {
    match division {
        // BigInt `/` and `%` truncate toward zero, as C does.
        Division::Quotient => x / divisor,
        Division::Remainder => x % divisor,
        Division::ShiftRight => {
            let quotient = x / divisor;
            if x.is_negative() && !(x % divisor).is_zero() {
                quotient - 1
            } else {
                quotient
            }
        }
    }
}

/// The value of a bound's side: constants, the operation's observation
/// (standing for `result`), its operand (standing for `x`), `+` and `*`.
fn evaluate(
    term: &IntegerTerm,
    operation: &SharedMachineIntegerTerm,
    result: &BigInt,
    x: &BigInt,
) -> BigInt {
    match term {
        IntegerTerm::Constant(value) => value.clone(),
        IntegerTerm::Machine(found) if found.id() == operation.id() => result.clone(),
        IntegerTerm::Machine(_) => x.clone(),
        IntegerTerm::Add(left, right) => {
            evaluate(left, operation, result, x) + evaluate(right, operation, result, x)
        }
        IntegerTerm::Multiply(left, right) => {
            evaluate(left, operation, result, x) * evaluate(right, operation, result, x)
        }
        other => panic!("unexpected bound term {other:?}"),
    }
}

#[test]
fn operation_bounds_hold_at_every_format() {
    for ty in FORMATS {
        for division in [
            Division::Quotient,
            Division::ShiftRight,
            Division::Remainder,
        ] {
            // `x / 4`, `x >> 2` and `x % 4`.
            let spelled = match division {
                Division::ShiftRight => BigInt::from(2),
                _ => BigInt::from(4),
            };
            let divisor = BigInt::from(4);
            let operand = value(ty, 172_041);
            let word = division_word(ty, division, operand.clone(), constant(ty, &spelled));
            if in_gaps(DIVISION_GAPS, ty) {
                assert_eq!(word, None, "{ty:?} {division:?} has no node");
                continue;
            }
            let word = word.unwrap_or_else(|| panic!("{ty:?} {division:?} has a node"));
            let IntegerTerm::Machine(machine) = observe(ty, word) else {
                panic!("{ty:?} observes a division as a machine value");
            };
            let signed = ty.format().is_signed();
            for upper in [false, true] {
                let bound = bounds::operation_bound(&machine, upper);
                // An unsigned remainder's lower bound is its range's.
                if division == Division::Remainder && !upper && !signed {
                    assert_eq!(bound, None, "{ty:?}");
                    continue;
                }
                let Some(Proposition::ConditionIs(
                    ConditionTerm::IntegerLessEqual(low, high),
                    true,
                )) = bound
                else {
                    panic!("{ty:?} {division:?} upper {upper} has a bound");
                };
                // The bound holds of every sample operand and its result.
                for x in samples(ty) {
                    let result = divide(division, &x, &divisor);
                    assert!(
                        evaluate(&low, &machine, &result, &x)
                            <= evaluate(&high, &machine, &result, &x),
                        "{ty:?} {division:?} upper {upper}: {x} gives {result}"
                    );
                }
            }
            // A signed divisor is read at its format: `-4` gives no bound.
            if signed && division != Division::ShiftRight {
                let negative = constant(ty, &BigInt::from(-4));
                let word = division_word(ty, division, operand.clone(), negative).unwrap();
                let IntegerTerm::Machine(machine) = observe(ty, word) else {
                    unreachable!()
                };
                assert_eq!(bounds::operation_bound(&machine, true), None, "{ty:?}");
            }
        }
    }
}

#[test]
fn modular_equality_reduces_at_every_width() {
    for ty in FORMATS {
        let (a, b) = (value(ty, 172_051), value(ty, 172_052));
        let difference = IntegerTerm::subtract(observe(ty, a.clone()), observe(ty, b.clone()));
        let condition = ConditionTerm::IntegerEqual(
            difference.into(),
            IntegerTerm::constant(BigInt::zero()).into(),
        );
        // The rule is stated at the modulus of the format's width, over
        // the observations of formats of that width.
        let modulus = FORMATS
            .into_iter()
            .find(|candidate| {
                candidate.format().bits() == ty.format().bits() && !candidate.format().is_signed()
            })
            .unwrap();
        let wrapped = modular::wrapped_equality_at(modulus, &condition, true);
        // 128 bits has no ring operations, and a narrow format's are the
        // 32-bit word's, which do not reduce modulo its own width: a
        // narrow equality is read at the word's modulus, where its
        // observations are not of the modulus's width.
        if in_gaps(OPERATION_GAPS, ty) || ty.format().bits() < 32 {
            assert_eq!(wrapped, None, "{ty:?}");
            continue;
        }
        let expected = representation::comparison(
            modulus,
            Relation::Equal,
            representation::folded_operation_word(modulus, Operation::Subtract, a, b).unwrap(),
            constant(modulus, &BigInt::zero()),
        )
        .unwrap()
        .0;
        assert_eq!(wrapped, Some(expected), "{ty:?}");
        // On constants, reduction modulo 2^w respects each operation.
        let modulo = BigInt::one() << ty.format().bits();
        let reduce = |value: &BigInt| ((value % &modulo) + &modulo) % &modulo;
        for x in samples(ty) {
            for y in samples(ty) {
                for operation in Operation::ALL {
                    let folded = representation::folded_operation_word(
                        modulus,
                        operation,
                        constant(modulus, &reduce(&x)),
                        constant(modulus, &reduce(&y)),
                    )
                    .unwrap();
                    assert_eq!(
                        IntegerTerm::from_machine(modulus, folded),
                        Some(IntegerTerm::Constant(reduce(&exact(operation, &x, &y)))),
                        "{ty:?} {x} {operation:?} {y}"
                    );
                }
            }
        }
    }
    // A narrow sum is a 32-bit word sum: `to_integer(a) + to_integer(b)
    // == 256` over bytes says nothing of the word `a + b` modulo 2^8.
    let byte = |variable| observe(Ty::UInt8, value(Ty::UInt8, variable));
    let wide_sum = ConditionTerm::IntegerEqual(
        IntegerTerm::add(byte(172_054), byte(172_055)).into(),
        IntegerTerm::constant(BigInt::from(256)).into(),
    );
    for modulus in [Ty::UInt8, Ty::Int8, Ty::UInt16, Ty::Int16] {
        assert_eq!(
            modular::wrapped_equality_at(modulus, &wide_sum, true),
            None,
            "{modulus:?}"
        );
    }
    // The fact context files the 32-bit reading.
    let condition = ConditionTerm::IntegerEqual(
        observe(Ty::Int32, value(Ty::Int32, 172_053)).into(),
        IntegerTerm::constant(BigInt::from(-1)).into(),
    );
    assert_eq!(
        modular::wrapped_equality_of_integer_equality(&condition, true),
        modular::wrapped_equality_at(Ty::UInt32, &condition, true)
    );
    assert!(modular::wrapped_equality_of_integer_equality(&condition, true).is_some());
}

#[test]
fn conversion_preserves_every_value_its_destination_holds() {
    for source in FORMATS {
        for destination in FORMATS {
            if source == destination {
                continue;
            }
            // Modular conversion keeps exactly the values the destination
            // holds, so widening keeps every value.
            for x in samples(source) {
                let converted = MachineIntegerConstant::from_integer(source.format(), &x)
                    .unwrap()
                    .convert_modulo(destination.format())
                    .to_integer();
                assert_eq!(
                    converted == x,
                    contains(destination, &x),
                    "{source:?} -> {destination:?}: {x}"
                );
                if destination.format().contains(source.format()) {
                    assert_eq!(converted, x, "{source:?} -> {destination:?} widens");
                }
            }
            // The certificate rule recognizes the conversion node at every
            // pair, and bounds its operand in the destination's range.
            let operand = value(source, 172_061);
            let original = observe(source, operand.clone());
            let converted = Bitvector32Term::machine_integer_cast(source, destination, operand);
            let Some(observed) = IntegerTerm::from_machine(destination, converted) else {
                panic!("{source:?} -> {destination:?} is observable");
            };
            // A widening of a narrow conversion normalizes to the value
            // itself: the identity is syntactic.
            if observed == original {
                assert!(
                    destination.format().contains(source.format()),
                    "{source:?} -> {destination:?}"
                );
                continue;
            }
            assert_eq!(
                conversion::cast(&observed, &original),
                Some(destination.format()),
                "{source:?} -> {destination:?}"
            );
        }
    }
}

#[test]
fn a_division_reads_only_at_its_own_signedness() {
    let (x, four) = (
        Bitvector32Term::Variable(Variable(172_071)),
        Bitvector32Term::Constant(4),
    );
    let signed = Bitvector32Term::Divide(Box::new(x.clone()), Box::new(four.clone()));
    let unsigned = Bitvector32Term::UnsignedDivide(Box::new(x), Box::new(four));
    assert!(representation::word_division(Ty::UInt32, &signed).is_none());
    assert!(representation::word_division(Ty::Int32, &unsigned).is_none());
    let machine = |word: Bitvector32Term, ty: Ty| -> SharedMachineIntegerTerm {
        match IntegerTerm::from_machine(ty, word) {
            Some(IntegerTerm::Machine(machine)) => machine,
            other => panic!("{other:?}"),
        }
    };
    assert!(bounds::operation_bound(&machine(signed.clone(), Ty::Int32), true).is_some());
    assert!(bounds::operation_bound(&machine(signed, Ty::UInt32), true).is_none());
}
