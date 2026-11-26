#[test]
fn certificate_argument_capture_keeps_growing_machine_terms_shared() {
    // Use the existing deep-fixture stack from tests/support/limits.rs;
    // elaboration and its thread-local work counters run on that same thread.
    std::thread::Builder::new()
        .name("retained-certificate-capture".into())
        .stack_size(64 << 20)
        .spawn(|| {
            let mut previous = None;
            for size in [8, 32, 128] {
                let _session = crate::kernel::VerificationSession::enter();
                let atom = SyntaxTerm::ProgramExpression(ProgramExpression::Value(
                    ProgramValue::UInt64(OldMachineTerm::Variable(Variable(997010))),
                ));
                let mut expression = atom.clone();
                for _ in 0..size {
                    expression = SyntaxTerm::Add(Box::new(expression), Box::new(atom.clone()));
                }
                let exports = KernelTermExport::machine_export_count();
                let (captured, work) =
                    crate::instrumentation::measure_deterministic_work(|| capture(&expression));
                let (root, guards) = captured.unwrap();
                eprintln!("certificate capture size={size}: work={work}");
                assert_eq!(
                    ExecutionValue::Shared(root).program_type(),
                    ProgramType::UInt64
                );
                assert!(guards.is_empty());
                assert_eq!(KernelTermExport::machine_export_count(), exports);
                if let Some(previous) = previous {
                    assert!(
                        work <= 6 * previous,
                        "capture must scale with the written argument: {previous} -> {work}"
                    );
                }
                previous = Some(work);
            }
        })
        .unwrap()
        .join()
        .unwrap();
}
