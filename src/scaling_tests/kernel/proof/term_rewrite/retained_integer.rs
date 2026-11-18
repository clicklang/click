use super::*;

#[test]
fn retained_integer_arithmetic_substitution_visits_shared_nodes_once_without_exports() {
    let _session = VerificationSession::enter();
    for size in [16, 64, 256] {
        let from = Variable(991950);
        let mut root = KernelTerm::variable(KernelType::Integer, from);
        for _ in 0..size {
            root =
                KernelTerm::integer_operation(KernelIntegerOperator::Add, vec![root.clone(), root])
                    .unwrap();
        }
        for source in [from, Variable(991951)] {
            let replacement = IntegerTerm::Variable(Variable(991952));
            let renamings = BTreeMap::new();
            let mut rewrite =
                TermRewrite::for_integer_variables(source, &replacement, false, &renamings);
            let exports = KernelTermExport::machine_export_count();
            let (actual, work) = crate::instrumentation::measure_deterministic_work(|| {
                rewrite.shared_integer_operand(&root).unwrap()
            });
            assert!(work <= 8 * (size + 1) + 64, "size={size}, work={work}");
            assert_eq!(KernelTermExport::machine_export_count(), exports);
            assert!(!root.has_cached_native_argument());
            assert!(!actual.has_cached_native_argument());
            if source != from {
                assert_eq!(actual.id(), root.id());
            }
        }
    }
}
