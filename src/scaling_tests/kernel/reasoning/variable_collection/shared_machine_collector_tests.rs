#[test]
fn shared_machine_collector_dag_work_is_linear() {
    use crate::kernel::{KernelTerm, KernelType};
    let mut samples = Vec::new();
    for size in [16usize, 64, 256] {
        let _session = VerificationSession::enter();
        let format = MachineIntegerType::Int32;
        let variable = Variable(989981);
        let mut root = KernelTerm::variable(KernelType::C(CType::Int32), variable);
        for _ in 0..size {
            root = KernelTerm::machine_binary_shared(
                format,
                MachineBinaryOp::Add,
                [root.clone(), root],
            );
        }
        let term =
            IntegerTerm::Machine(SharedMachineIntegerTerm::from_shared(format, root).unwrap());
        let exports = KernelTermExport::machine_export_count();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            let mut variables = BTreeSet::new();
            collect_integer_carrier_variables(&term, &mut variables);
            assert!(variables.is_empty());
            collect_integer_free_variables(&term, &mut variables);
            assert!(variables.is_empty());
            collect_integer_bound_identities(&term, &mut variables, &mut SeenTerms::default());
            assert!(variables.is_empty());
            collect_integer_bitvector_capture_variables(
                &term,
                &mut variables,
                &mut SeenTerms::default(),
            );
            assert_eq!(variables, BTreeSet::from([variable]));
            let (mut integers, mut machines) = Default::default();
            collect_integer_binder_variables_seen(
                &term,
                &mut integers,
                &mut machines,
                &mut SeenTerms::default(),
            );
            assert!(integers.is_empty() && machines.is_empty());
            assert_eq!(
                collect_integer_scope_summary(&term, &mut Default::default()).max,
                variable.0
            );
        });
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        samples.push(work);
    }
    for pair in samples.windows(2) {
        assert!(pair[1] <= pair[0] * 5, "{samples:?}");
    }
}

#[test]
fn shared_scope_maximum_queries_do_not_reindex_growing_prefixes() {
    use crate::kernel::{KernelTerm, KernelType};
    let mut samples = Vec::new();
    for count in [16u64, 64, 256] {
        let _session = VerificationSession::enter();
        let format = MachineIntegerType::Int32;
        let mut root = KernelTerm::variable(KernelType::C(CType::Int32), Variable(990000));
        let exports = KernelTermExport::machine_export_count();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for index in 1..=count {
                root = KernelTerm::machine_binary_shared(
                    format,
                    MachineBinaryOp::Add,
                    [
                        root.clone(),
                        KernelTerm::variable(KernelType::C(CType::Int32), Variable(990000 + index)),
                    ],
                );
                let term = IntegerTerm::Machine(
                    SharedMachineIntegerTerm::from_shared(format, root.clone()).unwrap(),
                );
                // No per-query Integer memo survives: only syntax summaries may
                // be reused while proof/rewrite contexts change.
                assert_eq!(
                    collect_integer_scope_summary(&term, &mut Default::default()).max,
                    990000 + index
                );
            }
        });
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        samples.push(work);
    }
    for pair in samples.windows(2) {
        assert!(pair[1] <= pair[0] * 6, "{samples:?}");
    }
}

#[test]
fn shared_conversion_collectors_visit_common_integer_payloads_once() {
    use crate::kernel::KernelTerm;
    let mut samples = Vec::new();
    for size in [16u64, 64, 256] {
        let _session = VerificationSession::enter();
        let format = MachineIntegerType::Int32;
        let variable = Variable(990401);
        let mut common: SharedIntegerTerm = IntegerTerm::var(variable).into();
        for _ in 0..size {
            common = IntegerTerm::Add(common.clone(), common).into();
        }
        let mut importer = KernelTermImport::default();
        let mut root = importer
            .machine_arithmetic(format, &MachineTerm::constant(0))
            .unwrap();
        for index in 0..size {
            let conversion = MachineTerm::IntegerToMachine {
                destination: format,
                value: IntegerTerm::Add(
                    common.clone(),
                    IntegerTerm::constant_i64(index as i64).into(),
                )
                .into(),
            };
            let leaf = importer.machine_arithmetic(format, &conversion).unwrap();
            root = KernelTerm::machine_binary_shared(format, MachineBinaryOp::Add, [root, leaf]);
        }
        let term =
            IntegerTerm::Machine(SharedMachineIntegerTerm::from_shared(format, root).unwrap());
        let exports = KernelTermExport::machine_export_count();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            let mut variables = BTreeSet::new();
            collect_integer_bound_identities(&term, &mut variables, &mut SeenTerms::default());
            assert_eq!(variables, BTreeSet::from([variable]));
        });
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        samples.push(work);
    }
    for pair in samples.windows(2) {
        assert!(pair[1] <= pair[0] * 6, "{samples:?}");
    }
}
