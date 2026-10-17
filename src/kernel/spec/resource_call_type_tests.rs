use super::*;
use crate::kernel::VerificationSession;
use crate::kernel::effective_type::{CAccessClass, CStructClass};

fn class() -> CAccessClass {
    CAccessClass::Struct(CStructClass::opaque("node"))
}
fn value(index: u64) -> CValue {
    CValue::typed_pointer(Pointer::symbolic(Variable(index)), CType::Int32Pointer)
}
fn clause(value: CValue) -> SpecProposition {
    SpecProposition::Comparison {
        left: SpecExpression::PureFunctionApplication {
            name: "typed".into(),
            result_type: CType::Int32,
            pointer_result: None,
            result_object_class: None,
            arguments: vec![SpecPureFunctionArgument::ObjectPointer {
                argument: Box::new(SpecPureFunctionArgument::Value(SpecExpression::Value(
                    value,
                ))),
                object_class: class(),
            }],
        },
        operator: CComparisonOperator::Equal,
        right: SpecExpression::Value(CValue::Int32(Bitvector32Term::Constant(1))),
    }
}
fn lower(
    source: &SpecProposition,
    context: &PureFactContext,
    held: bool,
) -> Vec<SpecPropositionPath> {
    let mut budget = ExecutionBudget::beside_live_state();
    let state = CState::new();
    if held {
        lower_held_resource_body_clause(&state, source, context, &BTreeMap::new(), &mut budget)
    } else {
        lower_spec_proposition_at_state_with_algebraic_bindings(
            &state,
            source,
            None,
            context,
            &BTreeMap::new(),
            &mut budget,
        )
    }
    .unwrap()
}
#[test]
fn held_call_domains_are_explicit_scoped_and_withdrawable() {
    let _session = VerificationSession::enter();
    let source = clause(value(945_001));
    let parent = PureFactContext::new();
    assert!(lower(&source, &parent, false).is_empty());
    let paths = lower(&source, &parent, true);
    let [path] = paths.as_slice() else {
        panic!("one selected body path expected")
    };
    let receipts: Vec<_> = path
        .facts
        .iter()
        .map(|fact| {
            assert!(fact.is_certified());
            fact.proposition().clone()
        })
        .collect();
    assert_eq!(receipts.len(), 1);
    let opened = parent.clone().assume_proposition(receipts[0].clone());
    assert_eq!(lower(&source, &opened, false).len(), 1);
    assert!(lower(&source, &parent, false).is_empty());
    assert!(lower(&source, &opened.without_exact_fact(&receipts[0]), false).is_empty());
    assert!(lower(&clause(value(945_002)), &opened, false).is_empty());
}
#[test]
fn held_call_domains_do_not_replace_incompatible_positive_evidence() {
    let _session = VerificationSession::enter();
    let source = clause(
        value(945_003)
            .with_pointer_object_class(Some(CAccessClass::Struct(CStructClass::opaque("other")))),
    );
    assert!(lower(&source, &PureFactContext::new(), true).is_empty());
}

#[cfg(test)]
#[path = "../../scaling_tests/kernel/spec/resource_call_type_tests.rs"]
mod scaling_tests;
