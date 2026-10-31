use super::expansion_tests::mdtest_sources;
use super::*;

#[test]
fn transport_certificate_preserves_byte_reads_without_search() {
    let (source, sources) = mdtest_sources("mdtests/transport_certificate_byte_read.md");
    let sources = sources
        .iter()
        .map(|(n, s)| (n.as_str(), s.as_str()))
        .collect::<Vec<_>>();
    without_implicit_auto(|| verify_c0_sources(&source, &sources)).unwrap();
    let expanded = expand_c0_claim_source(&source, &sources, "keep", CProofClaim::Grouped).unwrap();
    without_implicit_auto(|| verify_c0_sources(&expanded, &sources)).unwrap();
    // Separation of q cannot carry a read of the cell actually written.
    let overlapping = source.replace(
        "*q == at(statement(0).entry, *q)",
        "*p == at(statement(0).entry, *p)",
    );
    assert!(without_implicit_auto(|| verify_c0_sources(&overlapping, &sources)).is_err());
}

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
        ("preserve 0 =>", "preserve 1 =>"),
        ("conclusion 1", "conclusion 0"),
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

#[test]
fn transport_certificate_preserves_signed_and_unsigned_64_bit_reads() {
    for (c_type, click_type) in [("long", "int64"), ("unsigned long", "uint64")] {
        let c = format!("void write(int *dest, {c_type} *kept) {{ *dest = 1; *dest = 2; }}");
        let source = format!(
            r#"
            verifying "wide.c";
            void write(int32 *dest, {click_type} *kept) {{
                owns dest[0..1];
                views kept[0..1];
                requires separate(memory(dest[0..1]), memory(kept[0..1]));
            }} by {{
                mark before;
                step();
                mark after;
                have *kept == at(before, *kept) by {{
                    transport_certificate {{
                        premise 0: changes_only(before, after, memory(dest[0..1]))
                            => changes_only(before, after, memory(dest[0..1]));
                        premise 1: at(before, separate(memory(dest[0..1]), memory(kept[0..1])))
                            => at(before, separate(memory(dest[0..1]), memory(kept[0..1])));
                        preserve 0, 1 => *kept == at(before, *kept);
                        conclusion 2;
                    }}
                }}
                step();
                mark final;
                have *kept == at(before, *kept) by {{
                    transport_certificate {{
                        premise 0: changes_only(after, final, memory(dest[0..1]))
                            => changes_only(after, final, memory(dest[0..1]));
                        premise 1: at(before, separate(memory(dest[0..1]), memory(kept[0..1])))
                            => at(before, separate(memory(dest[0..1]), memory(kept[0..1])));
                        preserve 0, 1 => *kept == at(after, *kept);
                        premise 3: at(after, *kept) == at(before, *kept)
                            => at(after, *kept) == at(before, *kept);
                        transitive 2, 3 => *kept == at(before, *kept);
                        conclusion 4;
                    }}
                }}
                step();
            }}
        "#
        );
        without_implicit_auto(|| verify_c0_sources(&source, &[("wide.c", &c)])).unwrap();
    }
}

#[test]
fn region_footprint_refuses_unrecorded_memory_changes() {
    let _session = crate::kernel::VerificationSession::enter();
    let before = CState::new();
    let after = before.clone().with_memory(before.memory().clone().store(
        crate::kernel::Pointer::symbolic(Variable(8_390_200)),
        CValue::Int32(7u32.into()),
    ));
    let mut snapshots = RecordedSnapshots::new();
    snapshots.insert(
        ProgramPointRef {
            region: CodeRegionRef::Region(0),
            kind: ProgramPointKind::Entry,
        },
        before,
    );
    snapshots.insert(
        ProgramPointRef {
            region: CodeRegionRef::Region(0),
            kind: ProgramPointKind::Exit,
        },
        after,
    );
    assert!(snapshots.footprint(&CodeRegionRef::Region(0)).is_err());
}

#[test]
fn region_footprint_identity_survives_unrelated_snapshots() {
    let _session = crate::kernel::VerificationSession::enter();
    let state = CState::new();
    let mut snapshots = RecordedSnapshots::new();
    snapshots.insert(
        ProgramPointRef {
            region: CodeRegionRef::Region(0),
            kind: ProgramPointKind::Entry,
        },
        state.clone(),
    );
    snapshots.insert(
        ProgramPointRef {
            region: CodeRegionRef::Region(0),
            kind: ProgramPointKind::Exit,
        },
        state.clone(),
    );
    let first = snapshots.footprint(&CodeRegionRef::Region(0)).unwrap();
    snapshots.insert(
        ProgramPointRef {
            region: CodeRegionRef::Region(1),
            kind: ProgramPointKind::Entry,
        },
        state,
    );
    assert_eq!(
        first,
        snapshots.footprint(&CodeRegionRef::Region(0)).unwrap()
    );
}

#[test]
fn region_footprint_free_and_call_certificates_expand_without_search() {
    for (fixture, claim) in [
        (
            "mdtests/a_cell_beside_a_freed_allocation_is_framed.md",
            "dispose_beside",
        ),
        ("mdtests/region_footprint_call.md", "beside_call"),
    ] {
        let (source, sources) = mdtest_sources(fixture);
        let sources = sources
            .iter()
            .map(|(name, source)| (name.as_str(), source.as_str()))
            .collect::<Vec<_>>();
        without_implicit_auto(|| verify_c0_sources(&source, &sources)).unwrap();
        let expanded =
            expand_c0_claim_source(&source, &sources, claim, CProofClaim::Grouped).unwrap();
        assert!(expanded.contains("transport_certificate"));
        without_implicit_auto(|| verify_c0_sources(&expanded, &sources)).unwrap();
        if claim == "beside_call" {
            // The contract still supplies this separation. A selected proof
            // must not silently find it in the ambient context.
            let missing = source.replace("            separate(memory(*q), memory(*r));\n", "");
            assert_ne!(missing, source);
            assert!(verify_c0_sources(&missing, &sources).is_err());
        }
    }
}

fn check_resource_field_certificate(ty: &str) {
    let (source, sources) = mdtest_sources("mdtests/transport_certificate_resource_field.md");
    let source = source
        .replace(
            "abstract resource model()",
            "spec enum ModelValue { Empty, Value(int32) }\nabstract resource model()",
        )
        .replace("field value: int32;", &format!("field value: {ty};"));
    let sources = sources
        .iter()
        .map(|(n, s)| (n.as_str(), s.as_str()))
        .collect::<Vec<_>>();
    without_implicit_auto(|| verify_c0_sources(&source, &sources))
        .unwrap_or_else(|e| panic!("{ty}: {}", e.report()));
    let expanded = expand_c0_claim_source(&source, &sources, "keep", CProofClaim::Grouped).unwrap();
    without_implicit_auto(|| verify_c0_sources(&expanded, &sources)).unwrap();
}

#[test]
fn transport_certificate_preserves_named_resource_field() {
    check_resource_field_certificate("int32");
}
#[test]
fn transport_certificate_preserves_integer_resource_field() {
    check_resource_field_certificate("Integer");
}
#[test]
fn transport_certificate_preserves_wide_resource_field() {
    check_resource_field_certificate("uint64");
}
#[test]
fn transport_certificate_preserves_pointer_resource_field() {
    check_resource_field_certificate("int32*");
}
#[test]
fn transport_certificate_preserves_algebraic_resource_field() {
    check_resource_field_certificate("ModelValue");
}

#[test]
fn transport_certificate_resource_descriptors_follow_call_bindings() {
    let (source, sources) = mdtest_sources("mdtests/transport_certificate_resource_field.md");
    let caller = format!(
        "{source}\n{}",
        r#"
        void call_keep(int *p) {
            owns *p;
            owns other: model();
            requires separate(memory(*p), other);
        } by { step(); step(); }
    "#
    );
    let c = format!("{}\nvoid call_keep(int *p) {{ keep(p); }}", sources[0].1);
    without_implicit_auto(|| verify_c0_sources(&caller, &[("resource_frame.c", &c)]))
        .unwrap_or_else(|e| panic!("{}", e.report()));
}

#[test]
fn transport_certificate_refuses_other_or_modified_resource() {
    let (source, sources) = mdtest_sources("mdtests/transport_certificate_resource_field.md");
    let sources = sources
        .iter()
        .map(|(n, s)| (n.as_str(), s.as_str()))
        .collect::<Vec<_>>();
    let wrong_instance = source
        .replace("owns m: model();", "owns m: model(); owns n: model();")
        .replace("m.value", "n.value");
    let error = without_implicit_auto(|| verify_c0_sources(&wrong_instance, &sources)).unwrap_err();
    assert!(
        error.report().contains("selected field"),
        "{}",
        error.report()
    );
    let changed_source = source.replace(
        "void keep(int *p) {",
        "extern void update(int *p) { owns m: model(); }\nvoid keep(int *p) {",
    );
    let changed_c = "void update(int *p); void keep(int *p) { update(p); }";
    let error = without_implicit_auto(|| {
        verify_c0_sources(&changed_source, &[("resource_frame.c", changed_c)])
    })
    .unwrap_err();
    assert!(error.report().contains("normalize"), "{}", error.report());
}

#[test]
fn transport_certificate_named_resource_is_a_theorem_argument() {
    let (source, sources) = mdtest_sources("mdtests/transport_certificate_resource_field.md");
    let source = format!(
        "{}\n{source}",
        r#"
        theorem keep_separation(A: Resource, B: Resource) {
            requires separate(A, B);
            ensures separate(A, B) by { assumption(); }
        }
    "#
    )
    .replacen(
        "    step();",
        r#"
        have separate(memory(*p), m) by {
            apply(keep_separation(memory(*p), m)) using { separate(memory(*p), m); };
        }
        step();"#,
        1,
    );
    let sources = sources
        .iter()
        .map(|(n, s)| (n.as_str(), s.as_str()))
        .collect::<Vec<_>>();
    without_implicit_auto(|| verify_c0_sources(&source, &sources))
        .unwrap_or_else(|e| panic!("{}", e.report()));
    let expanded = expand_c0_claim_source(&source, &sources, "keep", CProofClaim::Grouped).unwrap();
    without_implicit_auto(|| verify_c0_sources(&expanded, &sources)).unwrap();
}
