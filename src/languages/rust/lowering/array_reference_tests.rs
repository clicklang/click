use super::*;
use crate::surface::C0VerificationSession;

#[test]
fn charon_array_reference_assignments_preserve_bounded_storage_and_proof_work() {
    fn shape(s: &CStatement) -> (usize, usize) {
        match s {
            CStatement::Seq(a, b) => {
                let a = shape(a);
                let b = shape(b);
                (1 + a.0 + b.0, a.1 + b.1)
            }
            CStatement::DeclareAggregate { layout, .. } => {
                assert!(
                    layout.fields().is_empty(),
                    "array storage must stay compact"
                );
                (1, 0)
            }
            CStatement::InitializeScalarArray { fresh: false, .. } => (1, 1),
            _ => (1, 0),
        }
    }
    let export = super::super::charon::decode(
        include_bytes!("../../../../design/charon-trial/array-values/bounds.ullbc"),
        "bounds.rs",
        include_bytes!("../../../../design/charon-trial/array-values/bounds.rs"),
    )
    .unwrap();
    let (functions, _) = lower(&export).unwrap();
    let prepared = super::super::import::prepared_for_test(export).unwrap();
    for family in ["fill", "copy"] {
        let mut samples = Vec::new();
        for tag in ["small", "medium", "million"] {
            let _session = crate::kernel::VerificationSession::enter();
            let name = format!("{family}_{tag}");
            let function = functions
                .iter()
                .find(|f| f.name() == name)
                .unwrap()
                .to_kernel_function();
            let shape = shape(function.body());
            assert!(
                shape.1 >= 1,
                "must execute a checked reference region write"
            );
            let sidecar = format!(
                "verifying \"bounds.rs\"; uint32 {name}() {{ ensures result == 7u32; }} by {{ execute(); simp(); }}"
            );
            let (verified, work) = crate::instrumentation::measure_deterministic_work(|| {
                C0VerificationSession::new_program_prepared(&sidecar, &prepared)
            });
            verified.unwrap();
            samples.push((shape, work));
        }
        assert!(
            samples
                .iter()
                .all(|(shape, work)| *shape == samples[0].0 && *work <= samples[0].1 + 64),
            "{family}: {samples:?}"
        );
    }
}

#[test]
fn charon_external_array_operations_keep_lowering_and_proof_work_bounded() {
    let export = super::super::charon::decode(
        include_bytes!("../../../../design/charon-trial/array-values/external.ullbc"),
        "external.rs",
        include_bytes!("../../../../design/charon-trial/array-values/external.rs"),
    )
    .unwrap();
    let (functions, _) = lower(&export).unwrap();
    let prepared = super::super::import::prepared_for_test(export).unwrap();
    fn statements(statement: &CStatement) -> usize {
        match statement {
            CStatement::Seq(a, b) => 1 + statements(a) + statements(b),
            _ => 1,
        }
    }
    for family in ["copy", "fill"] {
        let mut samples = Vec::new();
        for (tag, count) in [("small", 8), ("medium", 1024), ("million", 1_000_000)] {
            let _session = crate::kernel::VerificationSession::enter();
            let name = format!("{family}_{tag}");
            let function = functions
                .iter()
                .find(|f| f.name() == name)
                .unwrap()
                .to_kernel_function();
            let (parameters, contract) = if family == "copy" {
                (
                    "uint32* target, const uint32* source".to_owned(),
                    format!(
                        "views source[0..{count}]; ensures target[0] == old(source[0]); ensures target[{}] == old(source[{}]);",
                        count - 1,
                        count - 1
                    ),
                )
            } else {
                (
                    "uint32* target, uint32 value".to_owned(),
                    format!(
                        "ensures target[0] == value; ensures target[{}] == value;",
                        count - 1
                    ),
                )
            };
            let sidecar = format!(
                "verifying \"external.rs\"; void {name}({parameters}) {{ owns target[0..{count}]; {contract} }} by {{ execute(); simp(); }}"
            );
            let (verified, work) = crate::instrumentation::measure_deterministic_work(|| {
                C0VerificationSession::new_program_prepared(&sidecar, &prepared)
            });
            verified.unwrap();
            samples.push((statements(function.body()), work));
        }
        assert!(
            samples
                .iter()
                .all(|(shape, work)| *shape == samples[0].0 && *work <= samples[0].1 + 128),
            "{family}: {samples:?}"
        );
    }
}
