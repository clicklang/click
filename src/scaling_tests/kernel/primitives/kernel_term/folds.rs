use super::*;

#[test]
fn fold_payload_construction_retains_growing_shared_bodies_with_constant_work() {
    for unrelated in [0, 128, 512] {
        let _unrelated = (0..unrelated)
            .map(|n| KernelTerm::variable(KernelType::Integer, Variable(950_000 + n)))
            .collect::<Vec<_>>();
        for size in [16, 64, 256] {
            let mut body = KernelTerm::variable(KernelType::Integer, Variable(960_000));
            for _ in 0..size {
                body = KernelTerm::integer_operation(
                    KernelIntegerOperator::Add,
                    vec![body.clone(), body],
                )
                .unwrap();
            }
            let zero = KernelTerm::integer_literal(0.into());
            let before = KernelTermExport::machine_export_count();
            let ((fold, copy), work) = crate::instrumentation::measure_deterministic_work(|| {
                let fold = KernelFold::new(
                    KernelFoldIndex::Integer,
                    Variable(960_000),
                    Variable(960_001),
                    [zero.clone(), zero.clone(), zero.clone(), body.clone()],
                )
                .unwrap();
                let copy = fold.clone();
                assert_eq!(fold, copy);
                (fold, copy)
            });
            assert_eq!(fold.arguments[3], body);
            assert_eq!(copy.arguments[3], body);
            assert_eq!(work, 1, "size={size}, unrelated={unrelated}");
            assert_eq!(KernelTermExport::machine_export_count(), before);
        }
    }
}

#[test]
fn nested_integer_fold_producers_keep_common_children_in_linear_work() {
    for size in [8, 32, 128] {
        let _session = crate::kernel::VerificationSession::enter();
        let index = IntegerRangeFoldIndex::Integer {
            start: IntegerTerm::constant_i64(0).into(),
            end: IntegerTerm::Variable(Variable(980001)).into(),
        };
        let (value, work) = crate::instrumentation::measure_deterministic_work(|| {
            let mut value = IntegerTerm::Variable(Variable(980002));
            for _ in 0..size {
                value = IntegerTerm::range_fold(
                    index.clone(),
                    IntegerTerm::constant_i64(0),
                    Variable(980003),
                    Variable(980004),
                    value,
                );
            }
            value
        });
        let root = KernelTermImport::default().integer(&value.into());
        let mut node = &root;
        let mut folds = 0;
        while let KernelTermNode::Fold(fold) = node.node() {
            folds += 1;
            node = &fold.arguments[3];
        }
        assert_eq!(folds, size);
        assert!(work < 250 * size, "size={size}, work={work}");
    }
}

#[test]
fn nested_machine_fold_producers_retain_children_without_native_exports() {
    use crate::kernel::ExecutionValue;
    for size in [8, 32, 128] {
        let _session = crate::kernel::VerificationSession::enter();
        let zero = ExecutionValue::Native(CValue::Int32(MachineTerm::constant(0)));
        let end = ExecutionValue::Native(CValue::Int32(MachineTerm::Variable(Variable(981001))));
        let before = KernelTermExport::machine_export_count();
        let (value, work) = crate::instrumentation::measure_deterministic_work(|| {
            let mut value =
                ExecutionValue::Native(CValue::Int32(MachineTerm::Variable(Variable(981002))));
            for _ in 0..size {
                value = crate::kernel::spec::symbolic_spec_range_fold_value(
                    zero.clone(),
                    end.clone(),
                    zero.clone(),
                    "acc",
                    "item",
                    value,
                )
                .unwrap();
            }
            value
        });
        let mut node = value.shared().expect("retained machine producer");
        let mut folds = 0;
        while let KernelTermNode::Fold(fold) = node.node() {
            folds += 1;
            node = &fold.arguments[3];
        }
        assert_eq!(folds, size);
        assert_eq!(KernelTermExport::machine_export_count(), before);
        assert!(work < 250 * size, "size={size}, work={work}");
    }
}
