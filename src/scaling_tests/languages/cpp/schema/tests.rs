// Scaling tests of `src/languages/cpp/schema.rs` (module `tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn constant_inventory_checks_long_chains_and_rejects_malformed_dependencies() {
    let sources = BTreeSet::from(["fixture.cpp".into()]);
    for size in [8, 32, 128, 512] {
        let mut constants = vec![coin_constant()];
        for index in 1..size {
            let mut dependent = max_money_constant("100000000");
            dependent.declaration_id = format!("constant_{index}");
            dependent.name = format!("C{index}");
            let CppExpression::Binary { left, right, .. } = &mut dependent.initializer else {
                unreachable!()
            };
            let CppExpression::IntegralCast { value, .. } = left.as_mut() else {
                unreachable!()
            };
            let CppExpression::IntegerLiteral { value, .. } = value.as_mut() else {
                unreachable!()
            };
            *value = "1".into();
            let CppExpression::ConstantReference { constant, .. } = right.as_mut() else {
                unreachable!()
            };
            constant.declaration_id = constants[index - 1].declaration_id.clone();
            constant.name = constants[index - 1].name.clone();
            constants.push(dependent);
        }
        let (checked, work) = crate::instrumentation::measure_deterministic_work(|| {
            validate_constant_inventory(&constants, "fixture.cpp", &sources)
        });
        assert_eq!(checked.unwrap().declarations.len(), size);
        assert!(
            work >= size && work <= 3 * size,
            "{size} constants: {work} work"
        );
        let mut wrong_value = constants.clone();
        wrong_value[size - 1].evaluated_value = "1".into();
        assert!(
            validate_constant_inventory(&wrong_value, "fixture.cpp", &sources)
                .err()
                .unwrap()
                .contains("disagrees")
        );
        let mut duplicate = constants.clone();
        duplicate.push(coin_constant());
        assert!(
            validate_constant_inventory(&duplicate, "fixture.cpp", &sources)
                .err()
                .unwrap()
                .contains("duplicate")
        );
        let mut cyclic = constants.clone();
        let CppExpression::Binary { right, .. } = &mut cyclic[1].initializer else {
            unreachable!()
        };
        let CppExpression::ConstantReference { constant, .. } = right.as_mut() else {
            unreachable!()
        };
        constant.declaration_id = constants[size - 1].declaration_id.clone();
        constant.name = constants[size - 1].name.clone();
        assert!(
            validate_constant_inventory(&cyclic, "fixture.cpp", &sources)
                .err()
                .unwrap()
                .contains("unknown or later")
        );
    }
    let leaves = [coin_constant(), {
        let mut leaf = coin_constant();
        leaf.declaration_id = "other".into();
        leaf.name = "OTHER".into();
        leaf
    }];
    validate_constant_inventory(&leaves, "fixture.cpp", &sources).unwrap();
}

#[test]
fn graph_reference_checks_index_growing_caller_places_once() {
    for size in [4usize, 32, 256, 2048] {
        let reference_type = CppType::LvalueReference {
            pointee: Box::new(signed_integer(32, false)),
        };
        let place = |id: String, value_type| CppPlace {
            name: id.clone(),
            declaration_id: id,
            value_type,
            span: cleanup_span(),
        };
        let mut caller = CppFunction {
            axiom: None,
            declaration_id: "caller".into(),
            name: "caller".into(),
            function_kind: CppFunctionKind::Free,
            return_type: signed_integer(32, false),
            parameters: (0..size)
                .map(|index| place(format!("parameter-{index}"), reference_type.clone()))
                .collect(),
            declared_noexcept: true,
            closure_captures: 0,
            span: cleanup_span(),
            body: Vec::new(),
        };
        for index in 0..size {
            caller.body.push(CppStatement::Declare {
                local: place(format!("local-{index}"), signed_integer(32, false)),
                initializer: CppInitializer::Value {
                    value: CppExpression::IntegerLiteral {
                        value: "0".into(),
                        value_type: signed_integer(32, false),
                        span: cleanup_span(),
                    },
                },
                span: cleanup_span(),
            });
            caller.body.push(CppStatement::Call {
                callee: CppFunctionReference {
                    through_pointer: false,
                    declaration_id: "read".into(),
                    name: "read".into(),
                    span: cleanup_span(),
                },
                arguments: vec![CppCallArgument::Reference {
                    place: CppPlaceReference {
                        projections: Vec::new(),
                        declaration_id: format!("parameter-{}", size - 1),
                        name: format!("parameter-{}", size - 1),
                        span: cleanup_span(),
                    },
                }],
                span: cleanup_span(),
            });
        }
        let callee = CppFunction {
            axiom: None,
            declaration_id: "read".into(),
            name: "read".into(),
            function_kind: CppFunctionKind::Free,
            return_type: signed_integer(32, false),
            parameters: vec![place("parameter-0".into(), reference_type)],
            declared_noexcept: true,
            closure_captures: 0,
            span: cleanup_span(),
            body: vec![],
        };
        let functions = BTreeMap::from([("caller".into(), &caller), ("read".into(), &callee)]);
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            validate_reachable_calls(
                "caller",
                &functions,
                &RecordIndex::default(),
                &mut Vec::new(),
                &mut BTreeMap::new(),
            )
        });
        assert_eq!(result.unwrap(), (2, false));
        assert!(
            work >= size && work <= 10 * size + 16,
            "{size} places and reference edges: {work} work"
        );
        let places = FunctionPlaces::new(&caller).unwrap();
        assert_eq!(places.declarations.len(), 2 * size);
        assert!(std::ptr::eq(
            places.place_type("parameter-0").unwrap(),
            &caller.parameters[0].value_type
        ));
        assert!(places.place_type("unknown").is_none());
    }
}

#[test]
fn call_depth_budget_accounts_for_previously_checked_subgraphs() {
    for size in [8usize, 32, 63, 64] {
        let reference = |index| CppFunctionReference {
            through_pointer: false,
            declaration_id: format!("f{index}"),
            name: format!("f{index}"),
            span: cleanup_span(),
        };
        let mut functions = (0..size)
            .map(|index| CppFunction {
                axiom: None,
                declaration_id: format!("f{index}"),
                name: format!("f{index}"),
                function_kind: CppFunctionKind::Free,
                return_type: signed_integer(32, false),
                parameters: vec![],
                declared_noexcept: true,
                closure_captures: 0,
                span: cleanup_span(),
                body: if index == 0 {
                    vec![]
                } else {
                    vec![CppStatement::ReturnCall {
                        callee: reference(index - 1),
                        arguments: vec![],
                        value_type: signed_integer(32, false),
                        conversions: vec![],
                        cleanups: vec![],
                        span: cleanup_span(),
                    }]
                },
            })
            .collect::<Vec<_>>();
        let mut root = functions[0].clone();
        root.name = "root".into();
        root.declaration_id = "root".into();
        // Check short subgraphs first, so every following link uses a cache hit.
        root.body = (0..size)
            .map(|index| CppStatement::Call {
                callee: reference(index),
                arguments: vec![],
                span: cleanup_span(),
            })
            .collect();
        functions.push(root);
        let index = functions
            .iter()
            .map(|function| (function.declaration_id.clone(), function))
            .collect();
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            validate_reachable_calls(
                "root",
                &index,
                &RecordIndex::default(),
                &mut Vec::new(),
                &mut BTreeMap::new(),
            )
        });
        if size < super::super::super::budget::MAX_CALL_DEPTH {
            assert_eq!(result.unwrap(), (size + 1, false));
        } else {
            assert!(
                result
                    .unwrap_err()
                    .contains("artifact budget exhausted: call graph depth")
            );
        }
        assert!(
            work >= size && work <= 8 * size + 16,
            "{size} graph nodes: {work} work"
        );
    }
}

#[test]
fn record_inventory_reachability_rejects_unused_layouts() {
    let record = CppRecord {
        byte_template_arguments: vec![],
        declaration_id: "record".into(),
        name: "R".into(),
        size_bytes: 4,
        alignment_bytes: 4,
        destructor: None,
        span: cleanup_span(),
        base: None,
        fields: vec![CppField {
            declaration_id: "field".into(),
            name: "value".into(),
            value_type: signed_integer(32, false),
            offset_bytes: 0,
            size_bytes: 4,
            span: cleanup_span(),
        }],
    };
    let sources = BTreeSet::from(["fixture.cpp".into(), "record.h".into()]);
    for source in ["fixture.cpp", "record.h"] {
        for size in [8, 32, 128, 256] {
            let inventory = (0..size)
                .map(|index| {
                    let mut copy = record.clone();
                    copy.span.file = source.into();
                    copy.fields[0].span.file = source.into();
                    copy.declaration_id = format!("record_{index}");
                    copy.name = format!("R{index}");
                    copy.fields[0].declaration_id = format!("field_{index}");
                    copy
                })
                .collect::<Vec<_>>();
            let (indexed, work) = crate::instrumentation::measure_deterministic_work(|| {
                validate_record_inventory(&inventory, "fixture.cpp", &sources)
            });
            assert_eq!(indexed.unwrap().len(), size);
            assert!(
                work >= size && work <= 7 * size,
                "{size} layouts: {work} work"
            );
        }
    }
    let mut duplicate_field = record.clone();
    duplicate_field.declaration_id = "second".into();
    duplicate_field.name = "Second".into();
    assert!(
        validate_record_inventory(
            &[record.clone(), duplicate_field.clone()],
            "fixture.cpp",
            &sources
        )
        .unwrap_err()
        .contains("duplicate C++ field")
    );
    duplicate_field.fields[0].declaration_id = "other_field".into();
    duplicate_field.name = "R".into();
    assert!(
        validate_record_inventory(&[record.clone(), duplicate_field], "fixture.cpp", &sources)
            .unwrap_err()
            .contains("same-named record layouts")
    );
    record
        .validate(
            "fixture.cpp",
            &sources,
            &RecordIndex::new(BTreeMap::from([("record".into(), &record)])),
        )
        .unwrap();
    let records = RecordIndex::new(BTreeMap::from([("record".into(), &record)]));
    assert!(
        validate_reachable_records(&BTreeMap::new(), &records)
            .unwrap_err()
            .contains("outside the selected")
    );
    let function = CppFunction {
        axiom: None,
        declaration_id: "function".into(),
        name: "read".into(),
        function_kind: CppFunctionKind::Free,
        return_type: signed_integer(32, false),
        declared_noexcept: true,
        closure_captures: 0,
        span: cleanup_span(),
        body: vec![],
        parameters: vec![CppPlace {
            declaration_id: "parameter".into(),
            name: "r".into(),
            span: cleanup_span(),
            value_type: CppType::LvalueReference {
                pointee: Box::new(CppType::Record {
                    declaration_id: "record".into(),
                    name: "R".into(),
                    is_const: false,
                }),
            },
        }],
    };
    validate_reachable_records(&BTreeMap::from([("function".into(), &function)]), &records)
        .unwrap();
}

#[test]
fn standard_byte_template_metadata_validation_scales_with_inventory() {
    for size in [4, 16, 64, 256] {
        let inventory: Vec<_> = (0..size)
            .map(|index| CppRecord {
                declaration_id: format!("record_{index}"),
                name: format!("Holder{index}__std_byte"),
                size_bytes: 4,
                alignment_bytes: 4,
                base: None,
                destructor: None,
                span: cleanup_span(),
                fields: vec![CppField {
                    declaration_id: format!("field_{index}"),
                    name: "value".into(),
                    value_type: signed_integer(32, false),
                    offset_bytes: 0,
                    size_bytes: 4,
                    span: cleanup_span(),
                }],
                byte_template_arguments: vec![CppByteTemplateArgument {
                    index: 0,
                    value_type: CppType::Enumeration {
                        declaration_id: "c:@N@std@E@byte".into(),
                        name: "std::byte".into(),
                        underlying_type: Box::new(CppType::Integer {
                            bits: 8,
                            signed: false,
                            is_const: false,
                            source_aliases: vec![],
                        }),
                        is_scoped: true,
                        is_fixed: true,
                        is_const: false,
                        span: cleanup_span(),
                    },
                }],
            })
            .collect();
        let sources = BTreeSet::from(["fixture.cpp".into()]);
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            validate_record_inventory(&inventory, "fixture.cpp", &sources)
        });
        result.unwrap();
        assert!(
            work >= size && work <= 32 * size + 16,
            "{size} records: {work} work"
        );
    }
}

#[test]
fn embedded_record_graph_validation_is_linear_and_rejects_cycles() {
    let sources = BTreeSet::from(["fixture.cpp".into()]);
    for size in [8, 32, 128, 256] {
        let mut inventory = (0..size)
            .map(|index| CppRecord {
                byte_template_arguments: vec![],
                declaration_id: format!("r{index}"),
                name: format!("R{index}"),
                size_bytes: 4,
                alignment_bytes: 4,
                destructor: None,
                span: cleanup_span(),
                base: None,
                fields: vec![CppField {
                    declaration_id: format!("f{index}"),
                    name: "value".into(),
                    value_type: if index + 1 == size {
                        signed_integer(32, false)
                    } else {
                        CppType::Record {
                            declaration_id: format!("r{}", index + 1),
                            name: format!("R{}", index + 1),
                            is_const: false,
                        }
                    },
                    offset_bytes: 0,
                    size_bytes: 4,
                    span: cleanup_span(),
                }],
            })
            .collect::<Vec<_>>();
        let (checked, work) = crate::instrumentation::measure_deterministic_work(|| {
            validate_record_inventory(&inventory, "fixture.cpp", &sources)
        });
        let checked = checked.unwrap();
        assert!(
            work >= size && work <= 8 * size,
            "{size} nested declarations: {work} work"
        );
        assert_eq!(
            record_layout_order(&checked).unwrap().first().unwrap().name,
            format!("R{}", size - 1)
        );
        let root = CppType::Record {
            declaration_id: "r0".into(),
            name: "R0".into(),
            is_const: false,
        };
        let path = (0..size)
            .map(|index| CppFieldReference {
                record_declaration_id: format!("r{index}"),
                declaration_id: format!("f{index}"),
                name: "value".into(),
                span: cleanup_span(),
            })
            .collect::<Vec<_>>();
        let (resolved, work) = crate::instrumentation::measure_deterministic_work(|| {
            checked.resolve_path(&root, &path)
        });
        assert_eq!(resolved.unwrap(), (&signed_integer(32, false), 0));
        assert_eq!(work, size);
        let mut const_root = root.clone();
        let CppType::Record { is_const, .. } = &mut const_root else {
            unreachable!()
        };
        *is_const = true;
        let reference = CppPlaceReference {
            declaration_id: "root".into(),
            name: "root".into(),
            span: cleanup_span(),
            projections: path.into_iter().map(CppProjection::Field).collect(),
        };
        let (resolved, work) = crate::instrumentation::measure_deterministic_work(|| {
            resolve_reference_type(&const_root, &reference, &checked)
        });
        assert_eq!(resolved.unwrap(), (&signed_integer(32, false), true));
        assert_eq!(work, size);
        inventory[size - 1].fields[0].value_type = CppType::Record {
            declaration_id: "r0".into(),
            name: "R0".into(),
            is_const: false,
        };
        assert!(
            validate_record_inventory(&inventory, "fixture.cpp", &sources)
                .unwrap_err()
                .contains("by-value cycle")
        );
    }
}

#[test]
fn field_projection_lookup_does_not_scan_sibling_fields() {
    for size in [8usize, 32, 128, 256] {
        let record = CppRecord {
            byte_template_arguments: vec![],
            declaration_id: "r".into(),
            name: "R".into(),
            size_bytes: size as u32 * 4,
            alignment_bytes: 4,
            destructor: None,
            span: cleanup_span(),
            base: None,
            fields: (0..size)
                .map(|index| CppField {
                    declaration_id: format!("f{index}"),
                    name: format!("value{index}"),
                    value_type: signed_integer(32, false),
                    offset_bytes: index as u32 * 4,
                    size_bytes: 4,
                    span: cleanup_span(),
                })
                .collect(),
        };
        let (records, work) = crate::instrumentation::measure_deterministic_work(|| {
            RecordIndex::new(BTreeMap::from([("r".into(), &record)]))
        });
        assert_eq!(work, size);
        let root = CppType::Record {
            declaration_id: "r".into(),
            name: "R".into(),
            is_const: false,
        };
        let field = CppFieldReference {
            record_declaration_id: "r".into(),
            declaration_id: format!("f{}", size - 1),
            name: format!("value{}", size - 1),
            span: cleanup_span(),
        };
        let (resolved, work) = crate::instrumentation::measure_deterministic_work(|| {
            records.resolve_path(&root, [&field])
        });
        assert_eq!(
            resolved.unwrap(),
            (&signed_integer(32, false), (size - 1) as u32 * 4)
        );
        assert_eq!(work, 1);
        let reference = CppPlaceReference {
            declaration_id: "root".into(),
            name: "root".into(),
            span: cleanup_span(),
            projections: vec![CppProjection::Field(field)],
        };
        let (resolved, work) = crate::instrumentation::measure_deterministic_work(|| {
            resolve_reference_type(&root, &reference, &records)
        });
        assert_eq!(resolved.unwrap(), (&signed_integer(32, false), false));
        assert_eq!(work, 1);
    }
}

#[test]
fn single_base_inventory_walks_have_linear_work_and_reject_cycles() {
    let sources = BTreeSet::from(["fixture.cpp".into()]);
    for size in [8, 32, 128] {
        let mut inventory = (0..size)
            .map(|index| CppRecord {
                byte_template_arguments: vec![],
                declaration_id: format!("r{index}"),
                name: format!("R{index}"),
                size_bytes: 4,
                alignment_bytes: 4,
                destructor: None,
                span: cleanup_span(),
                base: (index + 1 < size).then(|| CppBase {
                    value_type: CppType::Record {
                        declaration_id: format!("r{}", index + 1),
                        name: format!("R{}", index + 1),
                        is_const: false,
                    },
                    offset_bytes: 0,
                    size_bytes: 4,
                    span: cleanup_span(),
                }),
                fields: if index + 1 == size {
                    vec![CppField {
                        declaration_id: "leaf".into(),
                        name: "value".into(),
                        value_type: signed_integer(32, false),
                        offset_bytes: 0,
                        size_bytes: 4,
                        span: cleanup_span(),
                    }]
                } else {
                    Vec::new()
                },
            })
            .collect::<Vec<_>>();
        let (checked, work) = crate::instrumentation::measure_deterministic_work(|| {
            validate_record_inventory(&inventory, "fixture.cpp", &sources)
        });
        let checked = checked.unwrap();
        assert!(
            work >= size && work <= 8 * size,
            "{size} base declarations: {work} work"
        );
        assert_eq!(
            record_layout_order(&checked).unwrap().first().unwrap().name,
            format!("R{}", size - 1)
        );
        let mut path = (0..size - 1)
            .map(|index| CppProjection::Base {
                base: CppBaseReference {
                    record_declaration_id: format!("r{index}"),
                    base_declaration_id: format!("r{}", index + 1),
                    base_name: format!("R{}", index + 1),
                    span: cleanup_span(),
                },
            })
            .collect::<Vec<_>>();
        path.push(CppProjection::Field(CppFieldReference {
            record_declaration_id: format!("r{}", size - 1),
            declaration_id: "leaf".into(),
            name: "value".into(),
            span: cleanup_span(),
        }));
        let place = CppPlaceReference {
            declaration_id: "root".into(),
            name: "root".into(),
            span: cleanup_span(),
            projections: path,
        };
        for is_const in [false, true] {
            let root = CppType::Record {
                declaration_id: "r0".into(),
                name: "R0".into(),
                is_const,
            };
            let (resolved, work) = crate::instrumentation::measure_deterministic_work(|| {
                resolve_reference_type(&root, &place, &checked)
            });
            assert_eq!(resolved.unwrap(), (&signed_integer(32, false), is_const));
            assert_eq!(work, size);
        }
        inventory[size - 1].fields.clear();
        inventory[size - 1].base = Some(CppBase {
            value_type: CppType::Record {
                declaration_id: "r0".into(),
                name: "R0".into(),
                is_const: false,
            },
            offset_bytes: 0,
            size_bytes: 4,
            span: cleanup_span(),
        });
        assert!(
            validate_record_inventory(&inventory, "fixture.cpp", &sources)
                .unwrap_err()
                .contains("by-value cycle")
        );
    }
}

#[test]
fn cross_header_call_origins_have_linear_graph_work() {
    let span_in = |source: String| CppSpan {
        file: source,
        ..cleanup_span()
    };
    let function = |name: String, source: String, body| CppFunction {
        axiom: None,
        declaration_id: name.clone(),
        name,
        function_kind: CppFunctionKind::Free,
        return_type: CppType::Void,
        parameters: vec![],
        declared_noexcept: true,
        closure_captures: 0,
        span: span_in(source),
        body,
    };
    let call = |name: String, source: String| CppStatement::Call {
        callee: CppFunctionReference {
            through_pointer: false,
            declaration_id: name.clone(),
            name,
            span: span_in(source.clone()),
        },
        arguments: vec![],
        span: span_in(source),
    };
    for size in [4, 16, 64, 128] {
        let mut functions = vec![function("leaf".into(), "leaf.h".into(), vec![])];
        for index in 0..size {
            let source = format!("header-{index}.h");
            functions.push(function(
                format!("helper-{index}"),
                source.clone(),
                vec![call("leaf".into(), source)],
            ));
        }
        functions.push(function(
            "root".into(),
            "fixture.cpp".into(),
            (0..size)
                .map(|index| call(format!("helper-{index}"), "fixture.cpp".into()))
                .collect(),
        ));
        let sources = functions
            .iter()
            .map(|function| function.span.file.clone())
            .collect();
        for function in &functions {
            super::super::super::validity::check_function(function, &function.span.file, &sources)
                .unwrap();
        }
        let index = functions
            .iter()
            .map(|function| (function.declaration_id.clone(), function))
            .collect();
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            validate_reachable_calls(
                "root",
                &index,
                &RecordIndex::default(),
                &mut Vec::new(),
                &mut BTreeMap::new(),
            )
        });
        assert_eq!(result.unwrap(), (3, false));
        assert!(work <= 12 * size + 16, "{size}: {work}");
        let mut forged = functions[1].clone();
        let CppStatement::Call { callee, .. } = &mut forged.body[0] else {
            unreachable!()
        };
        callee.span.file = "leaf.h".into();
        let mut index = index.clone();
        index.insert(forged.declaration_id.clone(), &forged);
        assert!(
            validate_reachable_calls(
                "root",
                &index,
                &RecordIndex::default(),
                &mut Vec::new(),
                &mut BTreeMap::new()
            )
            .unwrap_err()
            .contains("source span")
        );
    }
}

#[test]
fn converted_call_chain_validation_has_linear_work() {
    for size in [4, 16, 64, 128] {
        let conversions = (0..size)
            .map(|index| CppScalarConversion {
                cast_kind: CppScalarCastKind::IntegralCast,
                explicit: index % 2 == 0,
                source_type: signed_integer(if index % 2 == 0 { 32 } else { 64 }, false),
                value_type: signed_integer(if index % 2 == 0 { 64 } else { 32 }, false),
                span: cleanup_span(),
            })
            .collect();
        let initializer = CppInitializer::Call {
            callee: CppFunctionReference {
                through_pointer: false,
                declaration_id: "echo".into(),
                name: "echo".into(),
                span: cleanup_span(),
            },
            arguments: vec![],
            conversions,
            span: cleanup_span(),
        };
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            initializer.validate_for_local(
                &signed_integer(32, false),
                &ValidationPlaces::default(),
                &RecordIndex::default(),
                "fixture.cpp",
            )
        });
        result.unwrap();
        assert!(work >= size && work <= 4 * size + 8, "{size}: {work}");
    }
}

#[test]
fn converted_return_chain_validation_has_linear_work_and_bounded_nesting() {
    for size in [4, 16, 64, 128, 256, 257] {
        let conversions = vec![
            CppScalarConversion {
                cast_kind: CppScalarCastKind::NoOp,
                explicit: true,
                source_type: signed_integer(32, false),
                value_type: signed_integer(32, false),
                span: cleanup_span(),
            };
            size
        ];
        let callee = CppFunctionReference {
            through_pointer: false,
            declaration_id: "echo".into(),
            name: "echo".into(),
            span: cleanup_span(),
        };
        let returned = CppStatement::ReturnCall {
            callee: callee.clone(),
            arguments: vec![],
            value_type: signed_integer(32, false),
            conversions: conversions.clone(),
            cleanups: vec![],
            span: cleanup_span(),
        };
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            returned.validate(
                &ValidationPlaces::default(),
                &RecordIndex::default(),
                "fixture.cpp",
            )
        });
        if size <= super::super::super::budget::MAX_SCALAR_CONVERSIONS {
            result.unwrap();
            assert!(work >= size && work <= 4 * size + 8, "{size}: {work}");
        } else {
            assert!(
                result
                    .unwrap_err()
                    .contains("scalar call-result conversions")
            );
            let initializer = CppInitializer::Call {
                callee,
                arguments: vec![],
                conversions,
                span: cleanup_span(),
            };
            assert!(
                initializer
                    .validate_for_local(
                        &signed_integer(32, false),
                        &ValidationPlaces::default(),
                        &RecordIndex::default(),
                        "fixture.cpp",
                    )
                    .unwrap_err()
                    .contains("scalar call-result conversions")
            );
        }
    }
}
