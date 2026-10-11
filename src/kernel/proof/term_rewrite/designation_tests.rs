use super::*;
use std::hash::{Hash, Hasher};

fn object(root: Pointer, member: &str, count: IntegerTerm) -> PointerDesignation {
    PointerDesignation::Object {
        root: root.clone(),
        path: vec![PointerDomainSelection::Member(member.into())].into(),
        base: root,
        element_type: CType::Int32,
        stride: 4,
        count: count.into(),
    }
}

fn value(pointer: Pointer, designation: PointerDesignation) -> CPointerValue {
    CPointerValue::new(pointer, CType::Int32Pointer).with_designation(designation)
}

#[test]
fn designation_is_full_value_identity_and_shared_across_address_and_view_changes() {
    let p = Pointer::symbolic(Variable(410_001));
    let first = value(
        p.clone(),
        object(p.clone(), "first", IntegerTerm::constant_i64(1)),
    );
    let second = value(
        p.clone(),
        object(p.clone(), "second", IntegerTerm::constant_i64(1)),
    );
    assert_eq!(first.pointer(), second.pointer());
    assert_ne!(first, second);
    assert_ne!(first.cmp(&second), std::cmp::Ordering::Equal);
    let hash = |pointer: &CPointerValue| {
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        pointer.hash(&mut hasher);
        hasher.finish()
    };
    assert_ne!(hash(&first), hash(&second));
    let changed = first
        .clone()
        .with_type(CType::UInt8Pointer)
        .with_pointer(Pointer {
            block: p.block,
            offset: PointerOffsetTerm::Constant(4),
        });
    assert!(std::ptr::eq(
        first.designation().unwrap(),
        changed.designation().unwrap()
    ));
    let constant = first.clone().with_pointee_constant(true);
    assert_eq!(first, constant);
    assert_eq!(hash(&first), hash(&constant));
    let legacy = CPointerValue::new(Pointer::null(), CType::Int32Pointer);
    let mut old_hash = std::collections::hash_map::DefaultHasher::new();
    (
        legacy.pointer(),
        &legacy.c_type(),
        legacy.pointee_volatile(),
    )
        .hash(&mut old_hash);
    assert_eq!(hash(&legacy), old_hash.finish());
}

#[test]
fn typed_pointer_substitution_transports_domain_without_rebasing_it() {
    let source = Variable(410_010);
    let target = Pointer::symbolic(Variable(410_011));
    let actual = value(
        target.clone(),
        object(target.clone(), "array", IntegerTerm::constant_i64(16)),
    )
    .with_pointee_volatile(true);
    let occurrence = value(
        Pointer {
            block: PointerBlock::Symbolic(source),
            offset: PointerOffsetTerm::Constant(12),
        },
        PointerDesignation::Unresolved(source),
    );
    let replacements = BTreeMap::from([(source, TypedCReplacement::Pointer(actual.clone()))]);
    let empty_integer = BTreeMap::new();
    let empty_algebraic = BTreeMap::new();
    let mut rewrite =
        TermRewrite::for_typed_variables(&replacements, &empty_integer, &empty_algebraic);
    let CValue::Pointer(result) = rewrite.value(&CValue::Pointer(occurrence.clone())) else {
        panic!()
    };
    assert_eq!(rewrite.refusal(), None);
    assert_eq!(result.offset, PointerOffsetTerm::Constant(12));
    assert_eq!(result.designation(), actual.designation());
    assert!(result.pointee_volatile());
    let unrelated = value(Pointer::null(), PointerDesignation::Unresolved(source));
    let CValue::Pointer(result) = rewrite.value(&CValue::Pointer(unrelated)) else {
        panic!()
    };
    assert_eq!(rewrite.refusal(), None);
    assert_eq!(result.pointer(), &Pointer::null());
    assert_eq!(result.designation(), actual.designation());
    assert!(!result.pointee_volatile());
    let mut address_only = TermRewrite::for_pointer_variable(source, &target);
    let CValue::Pointer(result) = address_only.value(&CValue::Pointer(occurrence)) else {
        panic!()
    };
    assert_eq!(address_only.refusal(), None);
    assert_eq!(
        result.designation(),
        Some(&PointerDesignation::Unresolved(source))
    );
    let explicit = value(
        Pointer::symbolic(source),
        object(
            Pointer::symbolic(source),
            "member",
            IntegerTerm::constant_i64(1),
        ),
    );
    let mut exact = TermRewrite::for_pointer_exact(explicit.pointer(), &target);
    let CValue::Pointer(result) = exact.value(&CValue::Pointer(explicit.clone())) else {
        panic!()
    };
    assert_eq!(exact.refusal(), None);
    assert_eq!(result.pointer(), &target);
    assert!(std::ptr::eq(
        result.designation().unwrap(),
        explicit.designation().unwrap()
    ));
    drop(exact);
    let mut typed =
        TermRewrite::for_typed_variables(&replacements, &empty_integer, &empty_algebraic);
    let CValue::Pointer(result) = typed.value(&CValue::Pointer(explicit)) else {
        panic!()
    };
    assert_eq!(typed.refusal(), None);
    let Some(PointerDesignation::Object { root, base, .. }) = result.designation() else {
        panic!()
    };
    assert_eq!(root, &target);
    assert_eq!(base, &target);
}

#[test]
fn designation_terms_participate_in_math_substitution_and_variable_collection() {
    let c = Variable(410_020);
    let math = Variable(410_021);
    let p = Pointer::symbolic(c);
    let input = value(
        Pointer::null(),
        PointerDesignation::Object {
            root: p.clone(),
            base: p,
            path: vec![PointerDomainSelection::Element(
                IntegerTerm::var(math).into(),
            )]
            .into(),
            element_type: CType::Int32,
            stride: 4,
            count: IntegerTerm::var(math).into(),
        },
    );
    let mut carriers = CarrierVariables::for_rewrite(false);
    collect_c_pointer_carriers(&input, &mut carriers);
    assert_eq!(carriers.c, BTreeSet::from([c]));
    assert_eq!(carriers.integer, BTreeSet::from([math]));
    let mut capture = BTreeSet::new();
    let proposition = Proposition::Equal(
        Term::CValue(CValue::Pointer(input.clone())),
        Term::CValue(CValue::Void),
    );
    crate::kernel::prelude::collect_proposition_capture_variables(&proposition, &mut capture);
    assert!(capture.contains(&c));
    let integer_replacements = BTreeMap::from([(math, IntegerTerm::constant_i64(7))]);
    let empty_c = BTreeMap::new();
    let empty_algebraic = BTreeMap::new();
    let mut rewrite =
        TermRewrite::for_typed_variables(&empty_c, &integer_replacements, &empty_algebraic);
    let CValue::Pointer(result) = rewrite.value(&CValue::Pointer(input)) else {
        panic!()
    };
    assert_eq!(rewrite.refusal(), None);
    let Some(PointerDesignation::Object { path, count, .. }) = result.designation() else {
        panic!()
    };
    assert_eq!(count.as_ref(), &IntegerTerm::constant_i64(7));
    assert_eq!(
        path[0],
        PointerDomainSelection::Element(IntegerTerm::constant_i64(7).into())
    );
}

#[test]
fn unresolved_designation_uses_the_pointer_binder_in_alpha_keys_and_capture_avoidance() {
    let source = Variable(410_030);
    let captured = Variable(410_031);
    let occurrence = value(
        Pointer::symbolic(source),
        PointerDesignation::Unresolved(source),
    );
    let replacement = value(Pointer::null(), PointerDesignation::Unresolved(captured));
    let variants: std::sync::Arc<[AlgebraicVariantType]> = vec![AlgebraicVariantType {
        name: "Node".into(),
        fields: vec![AlgebraicValueType::C(CType::Int32Pointer)],
    }]
    .into();
    let algebraic_type = AlgebraicType {
        rigid: false,
        name: "DesignationScope".into(),
        arguments: vec![],
        variants: variants.clone(),
        schemas: std::sync::Arc::new(AlgebraicSchemas::new(BTreeMap::from([(
            AlgebraicValueType::Algebraic {
                name: "DesignationScope".into(),
                arguments: vec![],
            },
            variants,
        )]))),
    };
    let expression = Bitvector32Term::AlgebraicMatch {
        scrutinee: Box::new(AlgebraicTerm {
            algebraic_type,
            node: AlgebraicTermNode::Variable(Variable(410_032)),
        }),
        arms: vec![AlgebraicBitvectorMatchArm {
            variant: "Node".into(),
            bindings: vec![AlgebraicValue::C(CValue::Pointer(value(
                Pointer::symbolic(captured),
                PointerDesignation::Unresolved(captured),
            )))],
            body: Bitvector32Term::ClickFunctionApplication {
                name: "observe_designation".into(),
                arguments: vec![
                    PureFunctionArgument::Value(CValue::Pointer(occurrence)),
                    PureFunctionArgument::Value(CValue::Pointer(value(
                        Pointer::symbolic(captured),
                        PointerDesignation::Unresolved(captured),
                    ))),
                ],
            },
        }],
    };
    let replacements = BTreeMap::from([(source, TypedCReplacement::Pointer(replacement))]);
    let empty_integer = BTreeMap::new();
    let empty_algebraic = BTreeMap::new();
    let mut rewrite =
        TermRewrite::for_typed_variables(&replacements, &empty_integer, &empty_algebraic);
    let Bitvector32Term::AlgebraicMatch { arms, .. } = rewrite.bits(&expression) else {
        panic!()
    };
    assert_eq!(rewrite.refusal(), None);
    let AlgebraicValue::C(CValue::Pointer(binding)) = &arms[0].bindings[0] else {
        panic!()
    };
    let PointerBlock::Symbolic(renamed) = binding.block else {
        panic!()
    };
    assert_ne!(renamed, captured);
    assert_eq!(
        binding.designation(),
        Some(&PointerDesignation::Unresolved(renamed))
    );
    let Bitvector32Term::ClickFunctionApplication { arguments, .. } = &arms[0].body else {
        panic!()
    };
    let PureFunctionArgument::Value(CValue::Pointer(result)) = &arguments[0] else {
        panic!()
    };
    assert_eq!(
        result.designation(),
        Some(&PointerDesignation::Unresolved(captured))
    );
    let PureFunctionArgument::Value(CValue::Pointer(bound)) = &arguments[1] else {
        panic!()
    };
    assert_eq!(
        bound.designation(),
        Some(&PointerDesignation::Unresolved(renamed))
    );
    let domain_fact = |var| Proposition::Predicate {
        name: "designated_pointer".into(),
        arguments: vec![Term::CValue(CValue::Pointer(value(
            Pointer::null(),
            PointerDesignation::Unresolved(var),
        )))],
    };
    let quantified = |var| Proposition::ForAll {
        var,
        sort: Sort::CPointer(CType::Int32Pointer),
        body: Box::new(domain_fact(var)),
    };
    assert!(
        crate::kernel::proof::fact_keys::propositions_are_alpha_equal(
            &quantified(source),
            &quantified(captured)
        )
    );
    assert!(
        !crate::kernel::proof::fact_keys::propositions_are_alpha_equal(
            &quantified(source),
            &Proposition::ForAll {
                var: captured,
                sort: Sort::CPointer(CType::Int32Pointer),
                body: Box::new(domain_fact(source))
            },
        )
    );
}

#[test]
fn designation_math_dag_traversal_scales_linearly() {
    let mut measurements = Vec::new();
    for depth in [16, 32, 64] {
        let mut count = SharedIntegerTerm::from(IntegerTerm::var(Variable(410_040)));
        for _ in 0..depth {
            count = IntegerTerm::Add(count.clone(), count).into();
        }
        let input = value(
            Pointer::null(),
            object(Pointer::null(), "array", count.as_ref().clone()),
        );
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            let mut carriers = CarrierVariables::for_rewrite(false);
            collect_c_pointer_carriers(&input, &mut carriers);
            assert_eq!(carriers.integer, BTreeSet::from([Variable(410_040)]));
        });
        measurements.push(work);
    }
    for pair in measurements.windows(2) {
        assert!(pair[1] <= 3 * pair[0] + 16, "{measurements:?}");
    }
}

#[test]
fn designation_binders_are_canonical_and_algebraic_scalar_traversal_sees_shared_math() {
    let binder = Variable(410_050);
    assert_eq!(
        c_value_declaration_variable(&CValue::Pointer(value(
            Pointer::symbolic(binder),
            PointerDesignation::Unresolved(binder),
        ))),
        Some(binder)
    );
    assert_eq!(
        c_value_declaration_variable(&CValue::Pointer(value(
            Pointer::symbolic(binder),
            PointerDesignation::Unresolved(Variable(410_051)),
        ))),
        None
    );
    assert_eq!(
        c_value_declaration_variable(&CValue::Pointer(value(
            Pointer::symbolic(binder),
            object(
                Pointer::symbolic(binder),
                "field",
                IntegerTerm::constant_i64(1)
            ),
        ))),
        None
    );
    let scalar = Bitvector32Term::Variable(Variable(410_052));
    let mut measurements = Vec::new();
    for depth in [16, 32, 64] {
        let mut count = SharedIntegerTerm::from(IntegerTerm::Machine(
            SharedMachineIntegerTerm::intern(MachineIntegerType::Int32, scalar.clone()),
        ));
        for _ in 0..depth {
            count = IntegerTerm::Add(count.clone(), count).into();
        }
        let term = AlgebraicTerm {
            algebraic_type: AlgebraicType {
                rigid: false,
                name: "DesignationPayload".into(),
                arguments: vec![],
                variants: vec![].into(),
                schemas: std::sync::Arc::new(AlgebraicSchemas::new(BTreeMap::new())),
            },
            node: AlgebraicTermNode::Constructor {
                variant: "Pointer".into(),
                fields: vec![AlgebraicValue::C(CValue::Pointer(value(
                    Pointer::null(),
                    object(Pointer::null(), "array", count.as_ref().clone()),
                )))],
            },
        };
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            let mut visited = Vec::new();
            term.for_each_bitvector_term(|term| visited.push(term.clone()));
            assert_eq!(visited, vec![scalar.clone()]);
        });
        measurements.push(work);
    }
    for pair in measurements.windows(2) {
        assert!(pair[1] <= 3 * pair[0] + 16, "{measurements:?}");
    }
}

#[test]
fn designation_raw_rewrite_modes_partition_shared_memos_under_caller_managed_binders() {
    let binder = Variable(410_060);
    let source = Pointer {
        block: PointerBlock::Symbolic(Variable(410_061)),
        offset: PointerOffsetTerm::Constant(7),
    };
    let target = Pointer::symbolic(Variable(410_062));
    let offset_target = PointerOffsetTerm::Constant(9);
    let call = |name: &str, arguments| Pointer {
        block: PointerBlock::PureFunctionApplication(SharedPureApplication::intern(
            name.into(),
            arguments,
        )),
        offset: PointerOffsetTerm::Constant(0),
    };
    let inner = call(
        "domain_cache_inner",
        vec![PureFunctionArgument::Value(CValue::typed_pointer(
            source.clone(),
            CType::Int32Pointer,
        ))],
    );
    let memory = crate::kernel::intern_c_memory(CMemory::new());
    let load =
        crate::kernel::eval::load_variable_for_exact_cell(&memory, &source, LoadKind::Bits32, 4);
    let count: SharedIntegerTerm = IntegerTerm::Add(
        IntegerTerm::PureFunctionApplication(SharedPureApplication::intern(
            "domain_cache_extent".into(),
            vec![PureFunctionArgument::Value(CValue::typed_pointer(
                inner.clone(),
                CType::Int32Pointer,
            ))],
        ))
        .into(),
        IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
            MachineIntegerType::Int32,
            Bitvector32Term::Variable(load),
        ))
        .into(),
    )
    .into();
    let address = call(
        "domain_cache_outer",
        vec![
            PureFunctionArgument::Value(CValue::typed_pointer(inner, CType::Int32Pointer)),
            PureFunctionArgument::Integer(count.clone()),
        ],
    );
    let designation = PointerDesignation::Object {
        root: address.clone(),
        base: address.clone(),
        path: vec![PointerDomainSelection::Element(count.clone())].into(),
        element_type: CType::Int32,
        stride: 4,
        count: count.clone(),
    };
    let input = value(address.clone(), designation.clone());
    for mode in 0..3 {
        for domain_first in [false, true] {
            let mut rewrite = match mode {
                0 => TermRewrite::for_pointer_variable(Variable(410_061), &target),
                1 => TermRewrite::for_pointer_exact(&source, &target),
                _ => TermRewrite::for_pointer_offset_exact(&source.offset, &offset_target),
            };
            rewrite.enable_registered_load_resolution();
            // Pure-proposition callers manage ForAll/Exists scopes themselves;
            // TermRewrite::proposition deliberately keeps such scopes opaque.
            let scope = rewrite.push_c_substitution_scope(binder, binder);
            if domain_first {
                assert_eq!(rewrite.designation(&designation), designation);
            }
            let CValue::Pointer(result) = rewrite.value(&CValue::Pointer(input.clone())) else {
                panic!()
            };
            assert_eq!(rewrite.refusal(), None);
            assert_ne!(
                result.pointer(),
                &address,
                "mode={mode} domain_first={domain_first}"
            );
            assert_eq!(
                result.designation(),
                Some(&designation),
                "mode={mode} domain_first={domain_first}"
            );
            assert_eq!(rewrite.designation(&designation), designation);
            assert_eq!(rewrite.refusal(), None);
            rewrite.pop_c_substitution_scope(scope);
        }
    }
    // Integer binders also rename terms in the retained descriptor even when
    // the only active source substitution changes raw pointer addresses.
    let integer = Variable(410_063);
    let renamed = Variable(410_064);
    let domain = PointerDesignation::Object {
        root: source.clone(),
        base: source.clone(),
        path: vec![PointerDomainSelection::Element(
            IntegerTerm::var(integer).into(),
        )]
        .into(),
        element_type: CType::Int32,
        stride: 4,
        count: IntegerTerm::var(integer).into(),
    };
    let mut rewrite = TermRewrite::for_pointer_variable(Variable(410_061), &target);
    let scope = rewrite.push_integer_substitution_scope(integer, renamed, false);
    let CValue::Pointer(result) = rewrite.value(&CValue::Pointer(value(source.clone(), domain)))
    else {
        panic!()
    };
    assert_eq!(rewrite.refusal(), None);
    let Some(PointerDesignation::Object {
        root,
        base,
        path,
        count,
        ..
    }) = result.designation()
    else {
        panic!()
    };
    assert_eq!(root, &source);
    assert_eq!(base, &source);
    assert_eq!(count.as_ref(), &IntegerTerm::var(renamed));
    assert_eq!(
        path[0],
        PointerDomainSelection::Element(IntegerTerm::var(renamed).into())
    );
    rewrite.pop_integer_substitution_scope(scope);
}
