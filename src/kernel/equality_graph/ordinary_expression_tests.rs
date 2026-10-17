use super::*;
use crate::kernel::{
    BitvectorBinaryOp as B, BitvectorUnaryOp as U, CarrierWidth as W, IntegerTerm as I,
    MachineIntegerType as M,
};

fn word(v: u64) -> Bitvector32Term {
    Bitvector32Term::Variable(Variable(v))
}
fn binary_operations() -> Vec<B> {
    vec![
        B::Add,
        B::Subtract,
        B::Multiply,
        B::Divide,
        B::UnsignedDivide,
        B::Remainder,
        B::UnsignedRemainder,
        B::ShiftLeft,
        B::ArithmeticShiftRight,
        B::LogicalShiftRight,
        B::BitwiseAnd,
        B::BitwiseOr,
        B::BitwiseXor,
        B::Int64Add,
        B::Int64Subtract,
        B::Int64Multiply,
        B::Int64Divide,
        B::Int64Remainder,
        B::Int64ShiftLeft,
        B::Int64ArithmeticShiftRight,
        B::Int64BitwiseAnd,
        B::Int64BitwiseOr,
        B::Int64BitwiseXor,
        B::UInt64Add,
        B::UInt64Subtract,
        B::UInt64Multiply,
        B::UInt64Divide,
        B::UInt64Remainder,
        B::UInt64ShiftLeft,
        B::UInt64LogicalShiftRight,
        B::UInt64BitwiseAnd,
        B::UInt64BitwiseOr,
        B::UInt64BitwiseXor,
    ]
}
fn unary_operations() -> Vec<(U, bool, bool)> {
    let mut ops = vec![
        (U::BitwiseNot, false, false),
        (U::Int64BitwiseNot, true, true),
        (U::UInt64BitwiseNot, true, true),
        (U::Int64From32, false, true),
        (U::UInt64From32, false, true),
        (U::UInt32From64, true, false),
        (U::Int64FromUInt32, false, true),
        (U::UInt64FromInt32, false, true),
        (U::UInt64FromInt64, true, true),
    ];
    for source in [M::Int8, M::UInt16, M::Int32, M::UInt32, M::Int64, M::UInt64] {
        for destination in [M::Int8, M::UInt16, M::Int32, M::UInt32, M::Int64, M::UInt64] {
            ops.push((
                U::MachineIntegerCast {
                    source,
                    destination,
                },
                W::of_machine_type(source) == W::Bits64,
                W::of_machine_type(destination) == W::Bits64,
            ));
        }
    }
    ops
}
fn equal(graph: &EqualityGraph, a: &Bitvector32Term, b: &Bitvector32Term, wide: bool) -> bool {
    if wide {
        graph.are_uint64_equal(a, b)
    } else {
        graph.are_int32_equal(a, b)
    }
}
fn merge(graph: &mut EqualityGraph, a: &Bitvector32Term, b: &Bitvector32Term, wide: bool) {
    if wide {
        graph.add_uint64_equality(a, b);
    } else {
        graph.add_int32_equality(a, b);
    }
}
#[test]
fn every_integer_operator_propagates_early_and_late_aliases() {
    let _session = crate::kernel::VerificationSession::enter();
    for early in [false, true] {
        for op in binary_operations() {
            let wide = !op.is_bitvector32();
            let a = op.build_raw(word(940_001), word(940_003));
            let b = op.build_raw(word(940_002), word(940_003));
            let mut graph = EqualityGraph::default();
            if !early {
                assert!(!equal(&graph, &a, &b, wide), "{op:?}");
            }
            let sibling = graph.clone();
            merge(&mut graph, &word(940_001), &word(940_002), wide);
            assert!(equal(&graph, &a, &b, wide), "{op:?} early={early}");
            assert!(!equal(&sibling, &a, &b, wide));
            if op.is_bitvector32() {
                let c = op.build_raw(word(940_002), word(940_004));
                assert!(!equal(&graph, &a, &c, wide));
                merge(&mut graph, &word(940_003), &word(940_004), false);
                assert!(equal(&graph, &a, &c, wide));
            }
        }
        for (op, source_wide, destination_wide) in unary_operations() {
            let a = op.build_raw(word(940_011));
            let b = op.build_raw(word(940_012));
            let mut graph = EqualityGraph::default();
            if !early {
                assert!(!equal(&graph, &a, &b, destination_wide));
            }
            merge(&mut graph, &word(940_011), &word(940_012), source_wide);
            assert!(
                equal(&graph, &a, &b, destination_wide),
                "{op:?} early={early}"
            );
        }
    }
}
#[test]
fn all_integer_argument_types_follow_model_aliases_without_losing_tags() {
    let _session = crate::kernel::VerificationSession::enter();
    let ty =
        super::algebraic_tests::model_type("AllIntegerArgs", AlgebraicValueType::C(CType::Int32));
    let x = super::algebraic_tests::variable(&ty, 940_021);
    let y = super::algebraic_tests::variable(&ty, 940_022);
    let arg = |ty: M, model: &AlgebraicTerm| {
        ty.value_from_term(Bitvector32Term::ClickFunctionApplication {
            name: "inner".into(),
            arguments: vec![PureFunctionArgument::Algebraic(model.clone())],
        })
    };
    let call = |arg| Bitvector32Term::ClickFunctionApplication {
        name: "outer".into(),
        arguments: vec![PureFunctionArgument::Value(arg)],
    };
    let mut graph = EqualityGraph::default();
    let types = [
        M::Int8,
        M::UInt8,
        M::Int16,
        M::UInt16,
        M::Int32,
        M::UInt32,
        M::Int64,
        M::UInt64,
        M::Int128,
        M::UInt128,
    ];
    for t in types {
        assert!(!graph.are_int32_equal(&call(arg(t, &x)), &call(arg(t, &y))));
    }
    graph.add_algebraic_equality(&x, &y);
    for t in types {
        assert!(
            graph.are_int32_equal(&call(arg(t, &x)), &call(arg(t, &y))),
            "{t:?}"
        );
        for other in types {
            if other != t {
                assert!(!graph.are_int32_equal(&call(arg(t, &x)), &call(arg(other, &y))));
            }
        }
    }
}
#[test]
fn casts_from_integer_share_aliases_and_preserve_conversion_identity() {
    let _session = crate::kernel::VerificationSession::enter();
    let x: crate::kernel::SharedIntegerTerm = I::Variable(Variable(940_031)).into();
    let y: crate::kernel::SharedIntegerTerm = I::Variable(Variable(940_032)).into();
    let cast = |value, destination| Bitvector32Term::IntegerToMachine { value, destination };
    let mut graph = EqualityGraph::default();
    assert!(!graph.are_int32_equal(&cast(x.clone(), M::Int32), &cast(y.clone(), M::Int32)));
    graph.add_integer_equality(&x, &y);
    for t in [M::Int8, M::UInt32, M::Int64, M::UInt64] {
        assert!(equal(
            &graph,
            &cast(x.clone(), t),
            &cast(y.clone(), t),
            W::of_machine_type(t) == W::Bits64
        ));
    }
    assert!(!graph.are_int32_equal(&cast(x.clone(), M::Int8), &cast(y.clone(), M::UInt8)));
    assert!(!graph.are_uint64_equal(
        &U::Int64From32.build_raw(word(940_033)),
        &U::UInt64From32.build_raw(word(940_033))
    ));
}
#[test]
fn machine_literal_aliases_reach_canonical_integer_observations() {
    let _session = crate::kernel::VerificationSession::enter();
    for t in [
        M::Int8,
        M::UInt8,
        M::Int16,
        M::UInt16,
        M::Int32,
        M::UInt32,
        M::Int64,
        M::UInt64,
    ] {
        for n in [-1i64, 0, 1, 127, 255, 32768, i64::from(u32::MAX)] {
            let integer = I::constant_i64(n);
            let Some(literal) = crate::kernel::MachineIntegerConstant::from_integer(
                t.format(),
                &num_bigint::BigInt::from(n),
            )
            .and_then(|c| t.constant_term(c)) else {
                continue;
            };
            for early in [false, true] {
                let mut graph = EqualityGraph::default();
                let observed = I::from_machine(t, word(940_041)).unwrap();
                if !early {
                    assert!(!graph.are_integer_equal(&observed, &integer));
                }
                merge(
                    &mut graph,
                    &word(940_041),
                    &literal,
                    W::of_machine_type(t) == W::Bits64,
                );
                assert!(
                    graph.are_integer_equal(&observed, &integer),
                    "{t:?} {n} early={early}"
                );
            }
        }
    }
}

#[test]
fn nested_operators_register_the_pointer_arguments_they_use() {
    let _session = crate::kernel::VerificationSession::enter();
    let p = Pointer::symbolic(Variable(940_051));
    let q = Pointer::symbolic(Variable(940_052));
    let call = |pointer| Bitvector32Term::ClickFunctionApplication {
        name: "pointer_getter".into(),
        arguments: vec![PureFunctionArgument::Value(CValue::Pointer(
            crate::kernel::CPointerValue::new(pointer, CType::Int32Pointer),
        ))],
    };
    let expression = |pointer| {
        U::UInt64From32.build_raw(B::BitwiseAnd.build_raw(
            B::Multiply.build_raw(call(pointer), word(940_053)),
            Bitvector32Term::Constant(7),
        ))
    };
    let mut graph = EqualityGraph::default();
    let a = expression(p.clone());
    let b = expression(q.clone());
    assert!(!graph.are_uint64_equal(&a, &b));
    graph.add_equality(&p, &q);
    // A pure pointer argument includes its designation and bounds. Numeric
    // address equality alone must not identify these function applications.
    assert!(!graph.are_uint64_equal(&a, &b));
    graph.add_pointer_value_equality(
        &crate::kernel::CPointerValue::new(p, CType::Int32Pointer),
        &crate::kernel::CPointerValue::new(q, CType::Int32Pointer),
    );
    assert!(graph.are_uint64_equal(&a, &b));
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/equality_graph/ordinary_expression_tests.rs");
}
