//! Source names for the individual values in a rejected child argument.
//! This is presentation, never proof authority.

use super::*;

const MAX_TRACE_FACT_DEPTH: usize = 24;
const MAX_TRACE_STATES: usize = 32;

impl Proof<'_> {
    pub(super) fn trace_pointer_pair(
        &self,
        left: &OldAddress,
        right: &OldAddress,
    ) -> Option<[crate::surface::proof_trace::PointerTraceView; 2]> {
        let view = self.execution_fixed_state_view()?;
        let locals = self.proof_local_values();
        let fact = Proposition::condition_is(
            OldConditionTerm::address_equal(left.clone(), right.clone()),
            true,
        );
        let surface = crate::kernel::search::ProofSearch::available_surface_fact(
            self,
            view.surface_propositions,
            None,
            &fact,
        )
        .or_else(|| {
            let reversed = Proposition::condition_is(
                OldConditionTerm::address_equal(right.clone(), left.clone()),
                true,
            );
            crate::kernel::search::ProofSearch::available_surface_fact(
                self,
                view.surface_propositions,
                None,
                &reversed,
            )
        });
        let surface = surface.or_else(|| {
            let execution = self.branch_execution()?;
            let anchor = ProgramPointRef {
                region: CodeRegionRef::Region(execution.core.frontier.next_statement_index),
                kind: ProgramPointKind::Entry,
            };
            crate::kernel::search::ProofSearch::available_surface_fact(
                self,
                view.surface_propositions,
                Some(&anchor),
                &fact,
            )
        });
        let hints = match &surface {
            Some(SyntaxProposition::Comparison { left, right, .. }) => vec![left, right],
            _ => vec![],
        };
        let recent = view.fixed_state.recorded_states.recent(MAX_TRACE_STATES);
        let function = match self.context.as_ref() {
            ProofContext::Execution(context) => Some(context.parsed_function),
            _ => None,
        };
        let name = |pointer: &OldAddress| {
            use crate::surface::proof_trace::{PointerTraceView, pointer_definition};
            if pointer == &OldAddress::null() {
                return Some(PointerTraceView {
                    text: "0".into(),
                    retained_state: None,
                });
            }
            // Proof-local values are immutable, unlike C locals. A direct
            // name for a value does not move a memory read to the current state.
            let immutable_name = locals
                .iter()
                .find_map(|(name, expression)| match expression {
                    SyntaxTerm::ProgramExpression(ProgramExpression::Value(
                        ProgramValue::Pointer(value),
                    )) if value.address() == pointer => Some(name.clone()),
                    _ => None,
                });
            if let Some(text) = immutable_name {
                return Some(PointerTraceView {
                    text: text.to_string(),
                    retained_state: None,
                });
            }
            let Some(OldMachineTerm::MemoryLoad(memory, address, _)) = pointer_definition(pointer)
            else {
                return None;
            };
            let states = recent
                .iter()
                .filter(|(selector, _)| matches!(selector, ProgramPointSelector::Mark(_)))
                .chain(
                    recent
                        .iter()
                        .filter(|(selector, _)| !matches!(selector, ProgramPointSelector::Mark(_))),
                )
                .filter(|(_, state)| state.memory().same_storage_roots(memory.memory()));
            let matching: Vec<_> = states.collect();
            let point = matching.first().map(|(selector, _)| {
                crate::surface::diagnostics::describe_program_point_selector(selector)
            });
            // A checked field spelling through an immutable proof local is
            // usable even when the defining state has no retained C locals.
            // Check the field's address and pointer type, not merely its text.
            for hint in &hints {
                if let Some(text) = immutable_field_hint(hint, &address, &locals) {
                    return Some(PointerTraceView {
                        text: text.to_string(),
                        retained_state: Some((
                            crate::kernel::ProgramPoint::from(memory).into_shared_memory(),
                            point,
                        )),
                    });
                }
            }
            for (selector, state) in matching {
                let (parameters, arguments) =
                    crate::surface::diagnostics::local_naming_tables_with_source(state, function);
                if let Some(text) = crate::surface::diagnostics::diagnostic_source_pointer_cell(
                    &address,
                    ParameterBinding::new(&parameters, &arguments),
                    None,
                ) {
                    return Some(PointerTraceView {
                        text: text.to_string(),
                        retained_state: Some((
                            crate::kernel::ProgramPoint::from(memory).into_shared_memory(),
                            Some(
                                crate::surface::diagnostics::describe_program_point_selector(
                                    selector,
                                ),
                            ),
                        )),
                    });
                }
            }
            // A local can still name this address in another recorded state.
            // Qualify that base separately; do not pretend that the local's
            // state is the state from which the field value was read.
            for (selector, state) in recent
                .iter()
                .filter(|(selector, _)| matches!(selector, ProgramPointSelector::Mark(_)))
                .chain(
                    recent
                        .iter()
                        .filter(|(selector, _)| !matches!(selector, ProgramPointSelector::Mark(_))),
                )
            {
                let (parameters, arguments) =
                    crate::surface::diagnostics::local_naming_tables_with_source(state, function);
                let base_point =
                    crate::surface::diagnostics::describe_program_point_selector(selector);
                if let Some(text) = crate::surface::diagnostics::diagnostic_source_pointer_cell(
                    &address,
                    ParameterBinding::new(&parameters, &arguments),
                    Some(&base_point),
                ) {
                    return Some(PointerTraceView {
                        text: text.to_string(),
                        retained_state: Some((
                            crate::kernel::ProgramPoint::from(memory).into_shared_memory(),
                            point,
                        )),
                    });
                }
            }
            None
        };
        Some([name(left)?, name(right)?])
    }
}

fn immutable_field_hint(
    expression: &SyntaxTerm,
    address: &OldAddress,
    locals: &BinderMap<SyntaxTerm>,
) -> Option<String> {
    let mut expression = expression;
    for _ in 0..MAX_TRACE_FACT_DEPTH {
        match expression {
            SyntaxTerm::At {
                expression: inner, ..
            }
            | SyntaxTerm::Old(inner) => expression = inner,
            _ => break,
        }
    }
    let SyntaxTerm::Field {
        base,
        field,
        offset_bytes,
        lowered,
        ..
    } = expression
    else {
        return None;
    };
    let ProgramExpression::TypedLoad { value_type, .. } = lowered else {
        return None;
    };
    if !value_type.is_pointer() {
        return None;
    }
    let (name, base) = match base.as_ref() {
        SyntaxTerm::Binding(name)
        | SyntaxTerm::ProgramExpression(ProgramExpression::Variable(
            crate::kernel::BindingName::Named(name),
        )) => {
            let SyntaxTerm::ProgramExpression(ProgramExpression::Value(ProgramValue::Pointer(
                base,
            ))) = locals.get(name)?
            else {
                return None;
            };
            (SurfaceBinder::from(name), base)
        }
        // Checked surface forms substitute model binders with their exact
        // values. Recover the immutable binder before spelling the field.
        SyntaxTerm::ProgramExpression(ProgramExpression::Value(ProgramValue::Pointer(base))) => {
            let (name, _) = locals.iter().find(|(_, value)| matches!(value, SyntaxTerm::ProgramExpression(ProgramExpression::Value(ProgramValue::Pointer(candidate))) if candidate == base))?;
            (name.clone(), base)
        }
        _ => return None,
    };
    let expected = base.address().offset_by_layout(*offset_bytes);
    (expected.base == address.base
        && crate::kernel::offsets_have_same_canonical_form(&expected.offset, &address.offset))
    .then(|| crate::surface::diagnostics::describe_field_place(&name.to_string(), field))
}

#[cfg(test)]
mod pointer_trace_tests {
    use super::*;

    #[test]
    fn field_hint_recovers_substituted_immutable_binders_only_at_their_exact_address() {
        let base = OldAddress::symbolic(Variable(990001));
        let value = ProgramValue::typed_pointer(base.clone(), ProgramType::Int32Pointer);
        let local = SyntaxTerm::ProgramExpression(ProgramExpression::Value(value.clone()));
        let locals: BinderMap<_> = (BTreeMap::from([("zid".to_string(), local.clone())])).into();
        let hint = |base_expression, value_type| SyntaxTerm::Field {
            pointee_struct: None,
            base: Box::new(base_expression),
            field: "left".into(),
            offset_bytes: 8.into(),
            lowered: ProgramExpression::TypedLoad {
                pointer: Box::new(ProgramExpression::Value(value.clone())),
                value_type,
                volatile: false,
                pointee_constant: false,
                access_class: None,
                source: Default::default(),
            },
        };
        let address = base.offset_by_bytes(8);
        let substituted = hint(local.clone(), ProgramType::Int32Pointer);
        assert_eq!(
            immutable_field_hint(&substituted, &address, &locals),
            Some("zid->left".into())
        );
        assert_eq!(
            immutable_field_hint(&substituted, &base.offset_by_bytes(16), &locals),
            None
        );
        assert_eq!(
            immutable_field_hint(&hint(local, ProgramType::UInt64), &address, &locals),
            None
        );
        assert_eq!(
            immutable_field_hint(&substituted, &address, &BinderMap::new()),
            None
        );
        let reassigned: BinderMap<_> = (BTreeMap::from([(
            "zid".to_string(),
            SyntaxTerm::ProgramExpression(ProgramExpression::Value(ProgramValue::typed_pointer(
                OldAddress::symbolic(Variable(990002)),
                ProgramType::Int32Pointer,
            ))),
        )]))
        .into();
        assert_eq!(
            immutable_field_hint(&substituted, &address, &reassigned),
            None
        );
        // A C-local spelling is not enough to make it an immutable binder.
        assert_eq!(
            immutable_field_hint(
                &hint(
                    SyntaxTerm::ProgramBinding("zid".into()),
                    ProgramType::Int32Pointer
                ),
                &address,
                &locals
            ),
            None
        );
    }
}
