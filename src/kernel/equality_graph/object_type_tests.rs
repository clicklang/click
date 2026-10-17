use super::*;
use crate::kernel::VerificationSession;
use crate::kernel::effective_type::{CAccessClass, CStructClass};

fn class() -> CAccessClass {
    CAccessClass::Struct(CStructClass::opaque("node"))
}
fn pointer(id: u64) -> Pointer {
    Pointer::symbolic(Variable(870_000 + id))
}
fn value(pointer: &Pointer, checked: bool) -> CValue {
    let value = CValue::typed_pointer(pointer.clone(), CType::Int32Pointer);
    if checked {
        value.with_pointer_object_class(Some(class()))
    } else {
        value
    }
}
fn source(name: &str, pointer: &Pointer) -> Proposition {
    Proposition::Predicate {
        name: name.into(),
        arguments: vec![Term::CValue(value(pointer, true))],
    }
}
fn equal(a: &Pointer, b: &Pointer) -> Proposition {
    Proposition::ConditionIs(ConditionTerm::pointer_equal(a.clone(), b.clone()), true)
}
fn can_type(context: &PureFactContext, pointer: &Pointer) -> bool {
    crate::kernel::spec::refine_object_pointer_argument(
        &mut value(pointer, false),
        &class(),
        &CMemory::new(),
        context,
    )
}
fn model_source(pointer: &Pointer, condition: bool) -> Proposition {
    let ty = super::algebraic_tests::model_type(
        "Ref",
        AlgebraicValueType::ObjectPointer(CType::Int32Pointer, class()),
    );
    let variable = super::algebraic_tests::variable(&ty, 880_001);
    let constructor = AlgebraicTerm {
        algebraic_type: ty,
        node: AlgebraicTermNode::Constructor {
            variant: "Node".into(),
            fields: vec![AlgebraicValue::C(value(pointer, true))],
        },
    };
    if condition {
        Proposition::ConditionIs(
            ConditionTerm::AlgebraicEqual(Box::new(variable), Box::new(constructor)),
            true,
        )
    } else {
        Proposition::Equal(Term::Algebraic(variable), Term::Algebraic(constructor))
    }
}

#[test]
fn object_type_evidence_follows_early_and_late_pointer_merges() {
    let _session = VerificationSession::enter();
    let (p, q, r) = (pointer(1), pointer(2), pointer(3));
    for source_first in [false, true] {
        let mut context = PureFactContext::new();
        if source_first {
            context = context.assume_proposition(source("typed", &p));
        }
        assert!(!can_type(&context, &q));
        context = context
            .assume_proposition(equal(&p, &q))
            .assume_proposition(equal(&q, &r));
        if !source_first {
            context = context.assume_proposition(source("typed", &p));
        }
        assert!(can_type(&context, &r));
        assert!(!can_type(
            &context,
            &Pointer {
                block: r.block.clone(),
                offset: PointerOffsetTerm::Constant(4)
            }
        ));
        let other = CAccessClass::Struct(CStructClass::opaque("other"));
        assert!(!crate::kernel::spec::refine_object_pointer_argument(
            &mut value(&r, false),
            &other,
            &CMemory::new(),
            &context
        ));
    }
}

#[test]
fn object_type_support_is_scoped_counted_and_withdrawn_with_its_source() {
    let _session = VerificationSession::enter();
    let (p, q) = (pointer(4), pointer(5));
    let alias = equal(&p, &q);
    let parent = PureFactContext::new().assume_proposition(alias.clone());
    let a = source("a", &p);
    let b = source("b", &p);
    let branch = parent
        .clone()
        .assume_proposition(a.clone())
        .assume_proposition(b.clone());
    assert!(can_type(&branch, &q));
    assert!(!can_type(&parent, &q));
    let one = branch.without_exact_fact(&a);
    assert!(can_type(&one, &q));
    assert!(!can_type(&one.without_exact_fact(&b), &q));
    let split = branch.without_exact_fact(&alias);
    assert!(can_type(&split, &p));
    assert!(!can_type(&split, &q));
    assert!(can_type(&split.assume_proposition(alias), &q));
}

#[test]
fn model_type_support_survives_only_the_kept_fact_partition() {
    let _session = VerificationSession::enter();
    let (p, q) = (pointer(6), pointer(7));
    for condition in [false, true] {
        let model = model_source(&p, condition);
        let mut context = PureFactContext::new()
            .assume_proposition(model.clone())
            .assume_proposition(equal(&p, &q));
        assert!(can_type(&context, &q));
        assert!(!can_type(&context.without_exact_fact(&model), &q));
        context.retain_proposition_facts(|_| false);
        assert_eq!(can_type(&context, &q), condition);
        if let Proposition::ConditionIs(condition, _) = model {
            context = context.assume_proposition(Proposition::ConditionIs(condition, false));
            assert!(!can_type(&context, &q));
        }
    }
}

#[test]
fn goals_alternatives_and_weak_cast_metadata_do_not_admit_type_evidence() {
    let _session = VerificationSession::enter();
    let p = pointer(8);
    let model = model_source(&p, false);
    let Proposition::Equal(Term::Algebraic(a), Term::Algebraic(b)) = &model else {
        unreachable!()
    };
    let context = PureFactContext::new();
    context.equality_graph.are_algebraic_equal(a, b);
    assert!(!can_type(&context, &p));
    let alternatives = context.clone().assume_proposition(Proposition::Or(
        Box::new(model),
        Box::new(source("other", &p)),
    ));
    assert!(!can_type(&alternatives, &p));
    let weak = CValue::typed_pointer(p.clone(), CType::Int32Pointer)
        .with_contract_pointer_object_class(Some(class()), None, 0, 91);
    let weak = context.assume_proposition(Proposition::Predicate {
        name: "weak".into(),
        arguments: vec![Term::CValue(weak)],
    });
    assert!(!can_type(&weak, &p));
}

#[test]
fn object_type_evidence_does_not_bridge_changed_read_snapshots() {
    let _session = VerificationSession::enter();
    let slot = pointer(9);
    let memory = CMemory::new().with_block(slot.block.clone(), 8);
    let changed = memory
        .clone()
        .store(slot.clone(), value(&pointer(10), false));
    let before = Pointer::loaded_value(&memory.into(), &slot);
    let after = Pointer::loaded_value(&changed.into(), &slot);
    let context = PureFactContext::new().assume_proposition(source("old_read", &before));
    assert!(can_type(&context, &before));
    assert!(!can_type(&context, &after));
}

#[test]
fn opaque_call_interning_cannot_supply_another_scopes_type_annotations() {
    let _session = VerificationSession::enter();
    let p = pointer(11);
    let first = SharedPureApplication::intern(
        "opaque".into(),
        vec![PureFunctionArgument::Value(value(&p, true))],
    );
    let reused = SharedPureApplication::intern(
        "opaque".into(),
        vec![PureFunctionArgument::Value(value(&p, false))],
    );
    assert_eq!(first, reused);
    let scalar = IntegerTerm::PureFunctionApplication(reused.clone());
    let source = Proposition::Equal(Term::Integer(scalar.clone()), Term::Integer(scalar));
    let context = PureFactContext::new().assume_proposition(source);
    assert!(!can_type(&context, &p));
    let ty = super::algebraic_tests::model_type(
        "OpaqueRef",
        AlgebraicValueType::ObjectPointer(CType::Int32Pointer, class()),
    );
    let model = AlgebraicTerm {
        algebraic_type: ty,
        node: AlgebraicTermNode::PureFunctionApplication {
            name: "empty_ref".into(),
            arguments: reused.arguments().to_vec(),
        },
    };
    let context = context.assume_proposition(Proposition::Equal(
        Term::Algebraic(model.clone()),
        Term::Algebraic(model),
    ));
    assert!(!can_type(&context, &p));
}

mod scaling_tests {
    include!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/src/scaling_tests/kernel/equality_graph/object_type_tests.rs"
    ));
}
