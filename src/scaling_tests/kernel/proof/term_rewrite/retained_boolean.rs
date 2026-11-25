use super::*;

#[test]
fn retained_boolean_connective_rewriting_keeps_growing_dags_shared() {
    let _session = VerificationSession::enter();
    let from = Variable(992150);
    for size in [16_usize, 64, 256] {
        let mut root = KernelTerm::variable(KernelType::Bool, from);
        for index in 0..size {
            let side = KernelTerm::boolean_equal_raw([
                root.clone(),
                KernelTerm::variable(KernelType::Bool, Variable(992200 + index as u64)),
            ]);
            root = KernelTerm::boolean_if_raw([
                KernelTerm::variable(KernelType::Bool, Variable(993200 + index as u64)),
                root,
                side,
            ]);
        }
        for source in [from, Variable(994200)] {
            let program = BTreeMap::from([(
                source,
                TypedProgramValueReplacement::Bitvector(OldMachineTerm::bool_cast(
                    MachineIntegerType::UInt8,
                    OldConditionTerm::Variable(Variable(994201)),
                )),
            )]);
            let integer = BTreeMap::new();
            let algebraic = BTreeMap::new();
            let mut rewrite = TermRewrite::for_typed_variables(&program, &integer, &algebraic);
            let exports = KernelTermExport::machine_export_count();
            let (actual, work) = crate::instrumentation::measure_deterministic_work(|| {
                rewrite.shared_boolean_operand(&root).unwrap()
            });
            assert!(work <= 48 * (size + 1) + 128, "size={size}, work={work}");
            assert_eq!(KernelTermExport::machine_export_count(), exports);
            assert!(!root.has_cached_native_argument());
            assert!(!actual.has_cached_native_argument());
            assert!(rewrite.refusal().is_none());
            if source != from {
                assert_eq!(actual.id(), root.id());
            }
        }
    }
}
