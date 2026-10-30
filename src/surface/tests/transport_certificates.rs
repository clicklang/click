use super::expansion_tests::mdtest_sources;
use super::*;

#[test]
fn transport_certificate_preserves_pointer_read() {
    let (source, sources) = mdtest_sources("mdtests/transport_certificate.md");
    let sources = sources
        .iter()
        .map(|(n, s)| (n.as_str(), s.as_str()))
        .collect::<Vec<_>>();
    with_proof_trace("copy_pos", || {
        if let Err(error) = without_implicit_auto(|| verify_c0_sources(&source, &sources)) {
            panic!(
                "{}\n{}",
                error.report(),
                error.trace_context_report().unwrap_or_default()
            );
        }
    });
    let expanded =
        expand_c0_claim_source(&source, &sources, "copy_pos", CProofClaim::Grouped).unwrap();
    assert!(expanded.contains("transport_certificate"));
    without_implicit_auto(|| verify_c0_sources(&expanded, &sources)).unwrap();
    let scalar_source = source.replace("source->data", "source->len");
    without_implicit_auto(|| verify_c0_sources(&scalar_source, &sources)).unwrap();
    for (from, to) in [
        ("memory(target->pos))", "memory(target->len))"),
        ("preserve 0, 1", "preserve 1, 0"),
        ("conclusion 2", "conclusion 1"),
    ] {
        let invalid = source.replace(from, to);
        assert_ne!(invalid, source);
        assert!(verify_c0_sources(&invalid, &sources).is_err(), "{invalid}");
    }
}

#[test]
fn transport_certificate_transitive_and_bad_indices() {
    let source = r#"
        theorem transitive_values(x: int32*, y: int32*, z: int32*) {
            requires x == y;
            requires y == z;
            ensures x == z by {
                transport_certificate {
                    premise 0: x == y => x == y;
                    premise 1: y == z => y == z;
                    transitive 0, 1 => x == z;
                    conclusion 2;
                }
            }
        }
    "#;
    without_implicit_auto(|| verify_click_theorems(source)).unwrap();
    for (from, to) in [
        ("transitive 0, 1", "transitive 1, 0"),
        ("transitive 0, 1", "transitive 0, 2"),
        ("premise 1:", "premise 4:"),
        ("premise 0: x == y => x == y", "premise 0: x == y => x == z"),
        ("conclusion 2;", "conclusion 2; conclusion 2;"),
    ] {
        assert!(verify_click_theorems(&source.replace(from, to)).is_err());
    }
}
