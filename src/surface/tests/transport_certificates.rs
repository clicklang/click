use super::expansion_tests::mdtest_sources;
use super::*;

#[test]
fn transport_certificate_preserves_byte_reads_without_search() {
    let (source, sources) = mdtest_sources("mdtests/transport_certificate_byte_read.md");
    let sources = sources
        .iter()
        .map(|(n, s)| (n.as_str(), s.as_str()))
        .collect::<Vec<_>>();
    without_implicit_solve(|| verify_c0_sources(&source, &sources)).unwrap();
    let expanded = expand_c0_claim_source(&source, &sources, "keep", CProofClaim::Grouped).unwrap();
    without_implicit_solve(|| verify_c0_sources(&expanded, &sources)).unwrap();
    // Separation of q cannot carry a read of the cell actually written.
    let overlapping = source.replace(
        "*q == at(statement(0).entry, *q)",
        "*p == at(statement(0).entry, *p)",
    );
    assert!(without_implicit_solve(|| verify_c0_sources(&overlapping, &sources)).is_err());
}

#[test]
fn transport_certificate_preserves_pointer_read() {
    let (source, sources) = mdtest_sources("mdtests/transport_certificate.md");
    let sources = sources
        .iter()
        .map(|(n, s)| (n.as_str(), s.as_str()))
        .collect::<Vec<_>>();
    with_proof_trace("copy_pos", || {
        if let Err(error) = without_implicit_solve(|| verify_c0_sources(&source, &sources)) {
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
    without_implicit_solve(|| verify_c0_sources(&expanded, &sources)).unwrap();
    let scalar_source = source.replace("source->data", "source->len");
    without_implicit_solve(|| verify_c0_sources(&scalar_source, &sources)).unwrap();
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
    without_implicit_solve(|| verify_click_theorems(source)).unwrap();
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
        without_implicit_solve(|| verify_c0_sources(&source, &[("wide.c", &c)])).unwrap();
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
        without_implicit_solve(|| verify_c0_sources(&source, &sources)).unwrap();
        let expanded =
            expand_c0_claim_source(&source, &sources, claim, CProofClaim::Grouped).unwrap();
        assert!(expanded.contains("transport_certificate"));
        without_implicit_solve(|| verify_c0_sources(&expanded, &sources)).unwrap();
        if claim == "beside_call" {
            // The contract still supplies this separation. A selected proof
            // must not silently find it in the ambient context.
            let missing = source.replace("            separate(memory(*q), memory(*r));\n", "");
            assert_ne!(missing, source);
            assert!(verify_c0_sources(&missing, &sources).is_err());
        }
    }
}

#[test]
#[ignore = "nightly: expands and replays complete memory proofs"]
fn cell_source_removal_repairs_expand_and_replay_without_implicit_search() {
    for (fixture, claim) in [
        (
            "mdtests/execute_in_a_proof_if_arm_splits_alias_cases_inside_a_c_if.md",
            "f",
        ),
        (
            "mdtests/failed_allocation_preserves_existing_loads.md",
            "failed_allocation_preserves_existing_loads",
        ),
        (
            "mdtests/loop_node_link_frames_across_parent_link_store.md",
            "rotate",
        ),
        ("mdtests/bubble_pass3_max_suffix.md", "bubble_pass3"),
    ] {
        let (source, sources) = mdtest_sources(fixture);
        let sources = sources
            .iter()
            .map(|(name, source)| (name.as_str(), source.as_str()))
            .collect::<Vec<_>>();
        let expanded = expand_c0_claim_source(&source, &sources, claim, CProofClaim::Grouped)
            .unwrap_or_else(|error| panic!("{fixture}: {}", error.report()));
        assert!(expanded.contains("transport_certificate"), "{fixture}");
        without_implicit_solve(|| verify_c0_sources(&expanded, &sources)).unwrap_or_else(|error| {
            panic!(
                "{fixture}: {}\nExpanded source:\n{expanded}",
                error.report()
            )
        });
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
    without_implicit_solve(|| verify_c0_sources(&source, &sources))
        .unwrap_or_else(|e| panic!("{ty}: {}", e.report()));
    let expanded = expand_c0_claim_source(&source, &sources, "keep", CProofClaim::Grouped).unwrap();
    without_implicit_solve(|| verify_c0_sources(&expanded, &sources)).unwrap();
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
    without_implicit_solve(|| verify_c0_sources(&caller, &[("resource_frame.c", &c)]))
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
    let error =
        without_implicit_solve(|| verify_c0_sources(&wrong_instance, &sources)).unwrap_err();
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
    let error = without_implicit_solve(|| {
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
    without_implicit_solve(|| verify_c0_sources(&source, &sources))
        .unwrap_or_else(|e| panic!("{}", e.report()));
    let expanded = expand_c0_claim_source(&source, &sources, "keep", CProofClaim::Grouped).unwrap();
    without_implicit_solve(|| verify_c0_sources(&expanded, &sources)).unwrap();
}

#[test]
#[ignore = "nightly: focused full destructor expansion"]
fn destructor_footprint_cleanup_expands_and_replays() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("mdtests/cpp_generic_class_state_in_a_resource.md");
    let fixture = crate::cli::read_mdtest(&path).unwrap();
    let source = fixture.click_source.as_deref().unwrap();
    let inputs = crate::cli::prepare_mdtest_inputs(&fixture).unwrap();
    let expanded = expand_claim_by_label(
        None,
        source,
        &inputs.program_inputs(),
        "__cpp_q_X8_537461636b3c543e_X6_7e537461636b.contract",
        None,
    )
    .unwrap_or_else(|error| panic!("{}", error.report()));
    assert!(expanded.source.contains("transport_certificate"));
    let line = expanded
        .source
        .lines()
        .position(|line| line.contains("template<class T> Stack<T>::~Stack()"))
        .expect("destructor declaration")
        + 5;
    without_implicit_solve(|| {
        verify_sources_at(&expanded.source, &inputs.program_inputs(), line, 1)
    })
    .unwrap_or_else(|error| panic!("{}\n{}", error.report(), expanded.source));
}

#[test]
#[ignore = "nightly: full positive prefixes of pointer rejection fixtures"]
fn pointer_rejection_prefixes_expand_and_replay() {
    for (fixture, claim, from, to) in [
        (
            "joined_pointer_field_read_rejects_different_field",
            "inspect",
            "have model->right == leaf by {\n                                normalize() using { sibling == model; sibling->left == child; child == leaf; };\n                            }",
            "have child == leaf by { assumption(); }",
        ),
        (
            "mutex_protected_pointer_footprint_stale_read_rejected",
            "read_twice",
            "ensures result == 1;",
            "ensures result == 0 or result == 1;",
        ),
    ] {
        let (source, inputs) = mdtest_sources(&format!("mdtests/{fixture}.md"));
        // The ordinary fixtures still reject their original false claims.
        // Replay the otherwise identical proofs with their valid conclusions.
        let repaired = source.replace(from, to);
        assert_ne!(source, repaired);
        let inputs = inputs
            .iter()
            .map(|(n, s)| (n.as_str(), s.as_str()))
            .collect::<Vec<_>>();
        let expanded = expand_c0_claim_source(&repaired, &inputs, claim, CProofClaim::Grouped)
            .unwrap_or_else(|error| panic!("{fixture}: {}", error.report()));
        without_implicit_solve(|| verify_c0_sources(&expanded, &inputs))
            .unwrap_or_else(|error| panic!("{fixture}: {}\n{expanded}", error.report()));
    }
}

#[test]
fn preserve_step_carries_a_fact_with_ordinary_rewriting() {
    let (source, sources) = mdtest_sources("mdtests/preserve_step_carries_a_fact.md");
    let sources = sources
        .iter()
        .map(|(n, s)| (n.as_str(), s.as_str()))
        .collect::<Vec<_>>();
    without_implicit_solve(|| verify_c0_sources(&source, &sources)).unwrap();
    let expanded = expand_c0_claim_source(&source, &sources, "keep", CProofClaim::Grouped).unwrap();
    assert!(expanded.contains("preserve(separate("), "{expanded}");
    assert!(!expanded.contains("transport("), "{expanded}");
    assert!(!expanded.contains("transport_certificate"), "{expanded}");
    without_implicit_solve(|| verify_c0_sources(&expanded, &sources)).unwrap();
    let overlap = source.replace(
        "have *q == at(statement(0).entry, *q)",
        "have *p == at(statement(0).entry, *p)",
    );
    assert!(without_implicit_solve(|| verify_c0_sources(&overlap, &sources)).is_err());
}

#[test]
fn preserve_step_supports_memory_and_resource_observations() {
    for fixture in [
        "transport_certificate_byte_read.md",
        "transport_certificate.md",
        "transport_certificate_resource_field.md",
    ] {
        let (source, sources) = mdtest_sources(&format!("mdtests/{fixture}"));
        // Replace each single preserve certificate while leaving the
        // two-transition composition in the pointer fixture intact.
        let mut rewritten = source.clone();
        while let Some(start) = rewritten.find("transport_certificate {\n            premise 0:") {
            let end = start + rewritten[start..].find("\n        }").unwrap() + "\n        }".len();
            let block = &rewritten[start..end];
            if !block.contains("conclusion 1;") {
                break;
            }
            let premise = block
                .split("premise 0:")
                .nth(1)
                .unwrap()
                .split("=>")
                .next()
                .unwrap()
                .trim();
            let replacement = format!("preserve({premise});");
            rewritten.replace_range(start..end, &replacement);
        }
        assert_ne!(source, rewritten, "{fixture}");
        let sources = sources
            .iter()
            .map(|(n, s)| (n.as_str(), s.as_str()))
            .collect::<Vec<_>>();
        without_implicit_solve(|| verify_c0_sources(&rewritten, &sources)).unwrap();
    }
}

#[test]
fn resource_viewability_restriction_expands_without_transport() {
    for (fixture, claim) in [
        ("viewable_restrict_memory.md", "first"),
        ("viewable_restrict_resources.md", "view_component"),
    ] {
        let (source, sources) = mdtest_sources(&format!("mdtests/{fixture}"));
        let sources = sources
            .iter()
            .map(|(n, s)| (n.as_str(), s.as_str()))
            .collect::<Vec<_>>();
        without_implicit_solve(|| verify_c0_sources(&source, &sources))
            .unwrap_or_else(|e| panic!("{fixture}: {}", e.report()));
        let expanded = expand_c0_claim_source_by_label(
            &source,
            &sources,
            if claim == "first" {
                "first.contract"
            } else {
                "view_component.ensures_0"
            },
        )
        .unwrap();
        assert!(!expanded.contains("transport("), "{expanded}");
        without_implicit_solve(|| verify_c0_sources(&expanded, &sources)).unwrap();
    }
}

#[test]
fn viewability_transport_expands_to_ordinary_restriction() {
    let (source, sources) = mdtest_sources("mdtests/viewable_restrict_transport_expansion.md");
    let sources = sources
        .iter()
        .map(|(n, s)| (n.as_str(), s.as_str()))
        .collect::<Vec<_>>();
    verify_c0_sources(&source, &sources).unwrap();
    let expanded = expand_c0_claim_source_by_label(&source, &sources, "first.contract").unwrap();
    assert!(
        expanded.contains("separation::viewable_restrict"),
        "{expanded}"
    );
    assert!(expanded.contains("separation::subrange"), "{expanded}");
    assert!(!expanded.contains("transport("), "{expanded}");
    assert!(!expanded.contains("transport_certificate"), "{expanded}");
    without_implicit_solve(|| verify_c0_sources(&expanded, &sources)).unwrap();
}

#[test]
fn generic_viewability_transport_expands_to_ordinary_restriction() {
    let (source, _) = mdtest_sources("mdtests/viewable_restrict_resources.md");
    let source = source.replace(
        "apply(separation::viewable_restrict(A, B))",
        "transport(viewable(A), viewable(B))",
    );
    verify_c0_sources(&source, &[]).unwrap();
    let expanded =
        expand_c0_claim_source_by_label(&source, &[], "restrict_view.ensures_0").unwrap();
    assert!(
        expanded.contains("separation::viewable_restrict"),
        "{expanded}"
    );
    assert!(!expanded.contains("transport("), "{expanded}");
    without_implicit_solve(|| verify_c0_sources(&expanded, &[])).unwrap();
}

#[test]
fn single_write_transport_expands_to_preserve_without_search() {
    let (source, sources) = mdtest_sources("mdtests/single_write_transport_expansion.md");
    let sources = sources
        .iter()
        .map(|(n, s)| (n.as_str(), s.as_str()))
        .collect::<Vec<_>>();
    verify_c0_sources(&source, &sources).unwrap();
    let expanded = expand_c0_claim_source_by_label(&source, &sources, "keep.contract").unwrap();
    assert!(expanded.contains("preserve(separate("), "{expanded}");
    assert!(!expanded.contains("transport("), "{expanded}");
    assert!(!expanded.contains("transport_certificate"), "{expanded}");
    without_implicit_solve(|| verify_c0_sources(&expanded, &sources)).unwrap();
    let overlap = source.replace("have *q == at(statement(0).entry, *q)", "have *p == at(statement(0).entry, *p)")
        .replace("transport(at(statement(0).entry, *q) == at(statement(0).entry, *q),\n            *q == at(statement(0).entry, *q))", "transport(at(statement(0).entry, *p) == at(statement(0).entry, *p),\n            *p == at(statement(0).entry, *p))");
    assert!(verify_c0_sources(&overlap, &sources).is_err());
}

#[test]
fn single_write_resource_transport_expands_to_preserve_without_search() {
    let (source, sources) = mdtest_sources("mdtests/single_write_resource_transport_expansion.md");
    let sources = sources
        .iter()
        .map(|(n, s)| (n.as_str(), s.as_str()))
        .collect::<Vec<_>>();
    verify_c0_sources(&source, &sources).unwrap();
    let expanded = expand_c0_claim_source_by_label(&source, &sources, "keep.contract").unwrap();
    assert!(expanded.contains("preserve(separate("), "{expanded}");
    assert!(!expanded.contains("transport("), "{expanded}");
    assert!(!expanded.contains("transport_certificate"), "{expanded}");
    without_implicit_solve(|| verify_c0_sources(&expanded, &sources)).unwrap();
}

#[test]
fn multiple_write_transport_expands_to_ordinary_equalities() {
    let (source, sources) = mdtest_sources("mdtests/multi_write_transport_expansion.md");
    let sources = sources
        .iter()
        .map(|(n, s)| (n.as_str(), s.as_str()))
        .collect::<Vec<_>>();
    for source in [source.clone(), source.replace(
        "separate(statement(0).footprint, memory(*q));\n            separate(statement(1).footprint, memory(*q));",
        "separate(statement(1).footprint, memory(*q));\n            separate(statement(0).footprint, memory(*q));",
    )] {
        verify_c0_sources(&source, &sources).unwrap();
        let expanded = expand_c0_claim_source_by_label(&source, &sources, "keep.contract").unwrap();
        assert_eq!(expanded.matches("preserve(separate(").count(), 2, "{expanded}");
        assert!(!expanded.contains("transport("), "{expanded}");
        assert!(!expanded.contains("transport_certificate"), "{expanded}");
        without_implicit_solve(|| verify_c0_sources(&expanded, &sources)).unwrap();
    }
}

#[test]
fn multiple_write_resource_transport_expands_to_ordinary_equalities() {
    let (source, sources) = mdtest_sources("mdtests/multi_write_resource_transport_expansion.md");
    let sources = sources
        .iter()
        .map(|(n, s)| (n.as_str(), s.as_str()))
        .collect::<Vec<_>>();
    let expanded = expand_c0_claim_source_by_label(&source, &sources, "keep.contract").unwrap();
    assert_eq!(
        expanded.matches("preserve(separate(").count(),
        2,
        "{expanded}"
    );
    assert!(!expanded.contains("transport("), "{expanded}");
    assert!(!expanded.contains("transport_certificate"), "{expanded}");
    without_implicit_solve(|| verify_c0_sources(&expanded, &sources)).unwrap();
}

#[test]
fn multiple_write_transport_rejects_changed_reads_and_invalid_separation() {
    let (source, sources) = mdtest_sources("mdtests/multi_write_transport_expansion.md");
    let c = sources[0].1.replace("*p = 1;", "*p = 1; *q = 2;");
    let missing = source
        .replace("    have *q ==", "    step();\n    have *q ==")
        .replace("views *q;", "owns *q;");
    assert!(verify_c0_sources(&missing, &[(sources[0].0.as_str(), c.as_str())]).is_err());
    let c = sources[0].1.replace("*p = 1;", "*q = 1;");
    let overlapping = source.replace("views *q;", "owns *q;");
    assert!(verify_c0_sources(&overlapping, &[(sources[0].0.as_str(), c.as_str())]).is_err());
    let invalid = source.replace(
        "            separate(statement(1).footprint, memory(*q));",
        "            separate(statement(1).footprint, memory(*p));",
    );
    let sources = sources
        .iter()
        .map(|(n, s)| (n.as_str(), s.as_str()))
        .collect::<Vec<_>>();
    assert!(verify_c0_sources(&invalid, &sources).is_err());
}
