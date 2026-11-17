// Scaling tests of `src/kernel/primitives.rs`: deterministic work measured at
// several input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

/// A `uint8` value `depth` additions deep over one variable.
fn deep_uint8_value(depth: u64) -> MachineTerm {
    let mut value = MachineTerm::Variable(Variable(930_000));
    for _ in 0..depth {
        value = MachineTerm::Binary {
            format: MachineIntegerType::UInt8,
            op: MachineBinaryOp::Add,
            left: Box::new(value),
            right: Box::new(MachineTerm::machine_constant(
                MachineIntegerConstant::from_signed(MachineIntegerType::UInt8.format(), 1)
                    .expect("1 is a uint8 value"),
            )),
        };
    }
    value
}

/// A native narrow comparison and the `int32` comparison of its widenings
/// are one fact (rule K8): equal, hashed alike and keyed alike. Deciding
/// that identity is one root match per side whatever the operands' size,
/// so its count of identity readings is the same at every size.
#[test]
fn narrow_comparison_identity_is_constant_in_operand_size() {
    use std::hash::{Hash, Hasher};
    let hash = |condition: &ConditionTerm| {
        let mut state = std::collections::hash_map::DefaultHasher::new();
        condition.hash(&mut state);
        state.finish()
    };
    let seven = MachineTerm::machine_constant(
        MachineIntegerConstant::from_signed(MachineIntegerType::UInt8.format(), 7)
            .expect("7 is a uint8 value"),
    );
    let mut counts = Vec::new();
    for depth in [16, 64, 256, 1024] {
        let native = ConditionTerm::Compare {
            format: MachineIntegerType::UInt8,
            relation: CompareRelation::LessThan,
            left: Box::new(deep_uint8_value(depth)),
            right: Box::new(seven.clone()),
        };
        let promoted =
            crate::kernel::machine_integer::comparison::narrow_comparison_as_int32(&native)
                .expect("a native narrow comparison has a promoted spelling");
        assert!(
            matches!(
                promoted,
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    ..
                }
            ),
            "depth={depth}: {promoted:?}"
        );
        COMPARISON_IDENTITY_VISITS.with(|visits| visits.set(0));
        assert_eq!(native, promoted, "depth={depth}");
        assert_eq!(
            native.cmp(&promoted),
            std::cmp::Ordering::Equal,
            "depth={depth}"
        );
        let visits = COMPARISON_IDENTITY_VISITS.with(std::cell::Cell::get);
        assert_eq!(hash(&native), hash(&promoted), "depth={depth}");
        let (native_operator, native_left, native_right) =
            native.as_fact_comparison().expect("a comparison");
        let (promoted_operator, promoted_left, promoted_right) =
            promoted.as_fact_comparison().expect("a comparison");
        assert_eq!(native_operator, promoted_operator, "depth={depth}");
        assert_eq!(native_left, promoted_left, "depth={depth}");
        assert_eq!(native_right, promoted_right, "depth={depth}");
        counts.push(visits);
    }
    // Two comparisons, each read once per equality and once per order.
    assert!(
        counts.iter().all(|&count| count == counts[0] && count <= 4),
        "identity readings by depth: {counts:?}"
    );
}

/// Opaque exception values keep their type at every call/throw boundary.
/// Both existing and newly admitted rigid names use the name index.
#[test]
fn rigid_type_lookup_is_indexed_in_registered_types() {
    let target = TypeParameterName::intern("scaling::opaque_exception_target");
    for size in [0, 16, 64, 256] {
        for index in 0..size {
            TypeParameterName::intern(&format!("scaling::opaque_unrelated_{size}_{index}"));
        }
        let fresh = AlgebraicType::parameter(format!("scaling::opaque_fresh_{size}"));
        let ((found, missing), work) = crate::instrumentation::measure_deterministic_work(|| {
            let found = TypeParameterName::of(&target.algebraic_type());
            assert!(TypeParameterName::carries(&target.algebraic_type()));
            let missing = TypeParameterName::carries(&fresh);
            let admitted = TypeParameterName::of(&fresh);
            assert_eq!(TypeParameterName::of(&fresh), admitted);
            (found, missing)
        });
        assert_eq!(found, target);
        assert!(!missing);
        assert_eq!(work, 5, "registered growth={size}");
    }
}
