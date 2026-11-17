use super::*;
use crate::kernel::VerificationSession;

#[test]
fn algebraic_storage_imports_shared_integer_dags_once_and_hands_off_roots() {
    let samples = [4, 16, 64, 256].map(|size| {
        let _session = VerificationSession::enter();
        let ty = KernelMatch::test_scrutinee(vec![AlgebraicValueType::Integer]).algebraic_type;
        let mut child: SharedIntegerTerm = IntegerTerm::var(Variable(1012120)).into();
        for _ in 0..size {
            child = IntegerTerm::Add(child.clone(), child).into();
        }
        let weak = child.downgrade();
        let source = AlgebraicTerm {
            algebraic_type: ty,
            node: AlgebraicTermNode::Constructor {
                variant: "Arm".into(),
                fields: vec![AlgebraicValue::Integer(IntegerTerm::Negate(child))],
            },
        };
        let (value, cold) =
            crate::instrumentation::measure_deterministic_work(|| AlgebraicResult::from(source));
        assert!(weak.upgrade().is_none());
        let root = value.clone().into_kernel();
        let field = AlgebraicFieldResult::from_algebraic(value.clone());
        let (_, warm) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..32 {
                assert_eq!(value.clone().into_kernel(), root);
                assert_eq!(field.clone().into_kernel(), root);
            }
        });
        assert_eq!(warm, 0, "size={size}");
        (size, cold)
    });
    for pair in samples.windows(2) {
        let [(small, sw), (large, lw)] = pair else {
            unreachable!()
        };
        assert!(lw * small <= sw * large * 2, "{samples:?}");
    }
}
