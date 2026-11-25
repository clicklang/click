use super::*;

#[test]
fn scalar_machine_predicate_dags_reuse_growing_numeric_prefixes_without_exports() {
    let _session = VerificationSession::enter();
    for size in [16_usize, 64, 256] {
        let from = Variable(998300);
        let format = MachineIntegerType::Int32;
        let mut number = KernelTerm::variable(KernelType::Program(ProgramType::Int32), from);
        let zero = KernelTermImport::for_exact_field_inputs()
            .machine(format, &OldMachineTerm::constant(0));
        let mut root = KernelTerm::variable(KernelType::Bool, Variable(998301));
        for _ in 0..size {
            number = KernelTerm::machine_binary_shared(
                format,
                MachineBinaryOp::Add,
                [number.clone(), number],
            );
            let predicate = KernelTerm::boolean_comparison_raw(
                format,
                CompareRelation::LessThan,
                [number.clone(), zero.clone()],
            );
            root = KernelTerm::boolean_equal_raw([root, predicate]);
        }
        for variable in [from, Variable(998302)] {
            let source = OldMachineTerm::Variable(variable);
            let replacement = OldMachineTerm::Variable(Variable(998303));
            let mut rewrite = TermRewrite::for_bits_checked(&source, &replacement);
            let exports = KernelTermExport::machine_export_count();
            let (actual, work) = crate::instrumentation::measure_deterministic_work(|| {
                rewrite.shared_boolean_operand(&root).unwrap()
            });
            assert!(work <= 96 * (size + 1) + 512, "size={size}, work={work}");
            assert_eq!(KernelTermExport::machine_export_count(), exports);
            assert!(!root.has_cached_native_argument());
            assert!(!number.has_cached_native_argument());
            assert!(!actual.has_cached_native_argument());
            assert!(rewrite.refusal().is_none());
            if variable != from {
                assert_eq!(root.id(), actual.id());
            }
        }
    }
}

#[test]
fn scalar_integer_predicate_dags_reuse_growing_integer_prefixes_without_exports() {
    let _session = VerificationSession::enter();
    for size in [16_usize, 64, 256] {
        let from = Variable(998320);
        let mut number = KernelTerm::variable(KernelType::Integer, from);
        let zero = KernelTerm::integer_literal(0.into());
        let mut root = KernelTerm::variable(KernelType::Bool, Variable(998321));
        for _ in 0..size {
            number = KernelTerm::integer_operation(
                KernelIntegerOperator::Add,
                vec![number.clone(), number],
            )
            .unwrap();
            let predicate = KernelTerm::integer_comparison(
                IntegerComparisonOperator::LessThan,
                [number.clone(), zero.clone()],
            )
            .unwrap();
            root = KernelTerm::boolean_equal_raw([root, predicate]);
        }
        for variable in [from, Variable(998322)] {
            let replacement = IntegerTerm::Variable(Variable(998323));
            let renamings = BTreeMap::new();
            let mut rewrite =
                TermRewrite::for_integer_variables(variable, &replacement, false, &renamings);
            let exports = KernelTermExport::machine_export_count();
            let (actual, work) = crate::instrumentation::measure_deterministic_work(|| {
                rewrite.shared_boolean_operand(&root).unwrap()
            });
            assert!(work <= 64 * (size + 1) + 256, "size={size}, work={work}");
            assert_eq!(KernelTermExport::machine_export_count(), exports);
            assert!(!root.has_cached_native_argument());
            assert!(!number.has_cached_native_argument());
            assert!(!actual.has_cached_native_argument());
            assert!(rewrite.refusal().is_none());
            if variable != from {
                assert_eq!(root.id(), actual.id());
            }
        }
    }
}
