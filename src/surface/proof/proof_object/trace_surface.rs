//! Read-only Click rendering for checked trace facts whose kernel shape is
//! more explicit than the current exact-premise citation machinery accepts.
//! This is presentation, never proof authority.

use super::*;
use crate::kernel::{IntegerTerm, PureFunctionArgument, SharedIntegerTerm};

const MAX_TRACE_FACT_DEPTH: usize = 24;
const MAX_TRACE_SNAPSHOTS: usize = 32;

struct TraceSurfaceView<'a> {
    parameters: &'a [syntax::C0Parameter],
    arguments: &'a [CExpression],
    current: &'a CState,
    locals: &'a BTreeMap<String, ContractExpression>,
    recent: Vec<(&'a SnapshotSelector, &'a CState)>,
}

impl Proof<'_> {
    pub(super) fn trace_pointer_pair(
        &self,
        left: &Pointer,
        right: &Pointer,
    ) -> Option<[crate::surface::proof_trace::PointerTraceView; 2]> {
        let view = self.execution_fixed_state_view()?;
        let locals = self.proof_local_values();
        let fact = Proposition::ConditionIs(
            ConditionTerm::pointer_equal(left.clone(), right.clone()),
            true,
        );
        let surface = self
            .available_surface_fact(view.surface_propositions, None, &fact)
            .or_else(|| {
                let reversed = Proposition::ConditionIs(
                    ConditionTerm::pointer_equal(right.clone(), left.clone()),
                    true,
                );
                self.available_surface_fact(view.surface_propositions, None, &reversed)
            });
        let surface = surface.or_else(|| {
            let execution = self.branch_execution()?;
            let anchor = ProgramPointRef {
                region: CodeRegionRef::Statement(execution.core.frontier.next_statement_index),
                kind: ProgramPointKind::Entry,
            };
            self.available_surface_fact(view.surface_propositions, Some(&anchor), &fact)
        });
        let hints = match &surface {
            Some(ClickProposition::Comparison { left, right, .. }) => vec![left, right],
            _ => vec![],
        };
        let recent = view.recorded_snapshots.recent(MAX_TRACE_SNAPSHOTS);
        let function = match self.context.as_ref() {
            ProofContext::Execution(context) => Some(context.parsed_function),
            _ => None,
        };
        let name = |pointer: &Pointer| {
            use crate::surface::proof_trace::{PointerTraceView, pointer_definition};
            if pointer == &Pointer::null() {
                return Some(PointerTraceView {
                    mixed_snapshots: false,
                    text: "0".into(),
                    snapshot: None,
                });
            }
            // Proof-local values are immutable, unlike C locals. A direct
            // name for a value does not move a memory read to the current state.
            let immutable_name =
                locals
                    .iter()
                    .find_map(|(name, expression)| match expression {
                        ContractExpression::CFragment(CExpression::Value(CValue::Pointer(
                            value,
                        ))) if value.pointer() == pointer => Some(name.clone()),
                        _ => None,
                    });
            if let Some(text) = immutable_name {
                return Some(PointerTraceView {
                    mixed_snapshots: false,
                    text,
                    snapshot: None,
                });
            }
            let Some(Bitvector32Term::MemoryLoad(memory, address, _)) = pointer_definition(pointer)
            else {
                return None;
            };
            let states = recent
                .iter()
                .filter(|(selector, _)| matches!(selector, SnapshotSelector::Mark(_)))
                .chain(
                    recent
                        .iter()
                        .filter(|(selector, _)| !matches!(selector, SnapshotSelector::Mark(_))),
                )
                .filter(|(_, state)| state.memory().same_storage_roots(memory.memory()));
            let matching: Vec<_> = states.collect();
            let point = matching.first().map(|(selector, _)| {
                crate::surface::diagnostics::describe_snapshot_selector(selector)
            });
            // A checked field spelling through an immutable proof local is
            // usable even when the defining state has no retained C locals.
            // Check the field's address and pointer type, not merely its text.
            for hint in &hints {
                if let Some(text) = immutable_field_hint(hint, &address, &locals) {
                    return Some(PointerTraceView {
                        mixed_snapshots: false,
                        text,
                        snapshot: Some((memory, point)),
                    });
                }
            }
            for (selector, state) in matching {
                let (parameters, arguments) =
                    crate::surface::diagnostics::local_naming_tables_with_source(state, function);
                if let Some(text) = crate::surface::diagnostics::diagnostic_source_pointer_cell(
                    &address,
                    &parameters,
                    &arguments,
                    None,
                ) {
                    return Some(PointerTraceView {
                        mixed_snapshots: false,
                        text,
                        snapshot: Some((
                            memory,
                            Some(crate::surface::diagnostics::describe_snapshot_selector(
                                selector,
                            )),
                        )),
                    });
                }
            }
            // A local can still name this address in another recorded state.
            // Qualify that base separately; do not pretend that the local's
            // state is the state from which the field value was read.
            for (selector, state) in recent
                .iter()
                .filter(|(selector, _)| matches!(selector, SnapshotSelector::Mark(_)))
                .chain(
                    recent
                        .iter()
                        .filter(|(selector, _)| !matches!(selector, SnapshotSelector::Mark(_))),
                )
            {
                let (parameters, arguments) =
                    crate::surface::diagnostics::local_naming_tables_with_source(state, function);
                let base_point = crate::surface::diagnostics::describe_snapshot_selector(selector);
                if let Some(text) = crate::surface::diagnostics::diagnostic_source_pointer_cell(
                    &address,
                    &parameters,
                    &arguments,
                    Some(&base_point),
                ) {
                    return Some(PointerTraceView {
                        mixed_snapshots: true,
                        text,
                        snapshot: Some((memory, point)),
                    });
                }
            }
            None
        };
        Some([name(left)?, name(right)?])
    }

    pub(super) fn trace_surface_fact(&self, fact: &Proposition) -> Option<(String, bool)> {
        let view = self.execution_fixed_state_view()?;
        let locals = self.proof_local_values();
        let renderer = TraceSurfaceView {
            parameters: view.parameters,
            arguments: view.arguments,
            current: view.state,
            locals: &locals,
            recent: view.recorded_snapshots.recent(MAX_TRACE_SNAPSHOTS),
        };
        let surface = renderer.proposition(fact, &BTreeMap::new(), MAX_TRACE_FACT_DEPTH)?;
        let text = crate::surface::printing::source_click_proposition(&surface);
        if text.contains("__click_") {
            return None;
        }
        // The renderer is diagnostic-only. Promote its output to an exact
        // citation only when the normal lowering path confirms identity.
        let exact = self
            .lower_surface_proposition_direct(&surface, "trace fact")
            .is_ok_and(|lowered| lowered == *fact);
        Some((text, exact))
    }
}

impl TraceSurfaceView<'_> {
    fn proposition(
        &self,
        fact: &Proposition,
        binders: &BTreeMap<crate::kernel::Variable, String>,
        depth: usize,
    ) -> Option<ClickProposition> {
        let depth = depth.checked_sub(1)?;
        match fact {
            Proposition::Implies(left, right) => Some(ClickProposition::Implies(
                Box::new(self.proposition(left, binders, depth)?),
                Box::new(self.proposition(right, binders, depth)?),
            )),
            Proposition::Exists {
                name,
                var,
                sort,
                body,
            } => {
                let Sort::Algebraic(algebraic) = sort else {
                    return None;
                };
                if !algebraic.arguments.is_empty() {
                    return None;
                }
                let mut scoped = binders.clone();
                scoped.insert(*var, name.clone());
                Some(ClickProposition::Exists {
                    click_type: ClickType::Algebraic(AlgebraicTypeApplication::concrete(
                        algebraic.name.clone(),
                    )),
                    name: name.clone(),
                    written_name: Some(name.clone()),
                    body: Box::new(self.proposition(body, &scoped, depth)?),
                })
            }
            Proposition::ConditionIs(condition, polarity) => {
                let (left, operator, right) = match condition {
                    ConditionTerm::IntegerEqual(left, right) => (
                        self.integer(left, binders, depth)?,
                        if *polarity {
                            ComparisonOperator::Equal
                        } else {
                            ComparisonOperator::NotEqual
                        },
                        self.integer(right, binders, depth)?,
                    ),
                    ConditionTerm::IntegerLessEqual(left, right) => (
                        self.integer(left, binders, depth)?,
                        ComparisonOperator::LessEqual,
                        self.integer(right, binders, depth)?,
                    ),
                    ConditionTerm::Bitvector32Equal(left, right) => (
                        self.machine(left, binders, depth)?,
                        if *polarity {
                            ComparisonOperator::Equal
                        } else {
                            ComparisonOperator::NotEqual
                        },
                        self.machine(right, binders, depth)?,
                    ),
                    _ => return None,
                };
                if !*polarity && matches!(condition, ConditionTerm::IntegerLessEqual(..)) {
                    return None;
                }
                Some(ClickProposition::Comparison {
                    left,
                    operator,
                    right,
                })
            }
            _ => None,
        }
    }

    fn integer(
        &self,
        term: &SharedIntegerTerm,
        binders: &BTreeMap<crate::kernel::Variable, String>,
        depth: usize,
    ) -> Option<ContractExpression> {
        let depth = depth.checked_sub(1)?;
        match term.as_ref() {
            IntegerTerm::Constant(value) => {
                Some(ContractExpression::IntegerLiteral(value.to_string()))
            }
            IntegerTerm::Machine(value) => Some(ContractExpression::Call {
                name: "to_integer".into(),
                arguments: vec![self.machine(value.value(), binders, depth)?],
            }),
            IntegerTerm::Subtract(left, right) => Some(ContractExpression::Subtract(
                Box::new(self.integer(left, binders, depth)?),
                Box::new(self.integer(right, binders, depth)?),
            )),
            IntegerTerm::Add(left, right) => Some(ContractExpression::Add(
                Box::new(self.integer(left, binders, depth)?),
                Box::new(self.integer(right, binders, depth)?),
            )),
            IntegerTerm::TruncatingQuotient(left, right)
            | IntegerTerm::TruncatingRemainder(left, right) => Some(ContractExpression::Call {
                name: if matches!(term.as_ref(), IntegerTerm::TruncatingQuotient(_, _)) {
                    "truncating_quotient"
                } else {
                    "truncating_remainder"
                }
                .into(),
                arguments: vec![
                    self.integer(left, binders, depth)?,
                    self.integer(right, binders, depth)?,
                ],
            }),
            IntegerTerm::PureFunctionApplication(application) => {
                self.call(application.name(), application.arguments(), binders, depth)
            }
            _ => None,
        }
    }

    fn machine(
        &self,
        term: &Bitvector32Term,
        binders: &BTreeMap<crate::kernel::Variable, String>,
        depth: usize,
    ) -> Option<ContractExpression> {
        let depth = depth.checked_sub(1)?;
        if let Bitvector32Term::ClickFunctionApplication { name, arguments } = term {
            return self.call(name, arguments, binders, depth);
        }
        if let Bitvector32Term::Variable(variable) = term {
            if let Some(name) = binders.get(variable) {
                return Some(ContractExpression::Binding(name.clone()));
            }
            if let Some((name, _)) = self.locals.iter().find(|(_, value)| {
                matches!(value, ContractExpression::CFragment(CExpression::Value(CValue::Int32(bits))) if bits == term)
            }) {
                return Some(ContractExpression::Binding(name.clone()));
            }
            if let Some((memory, pointer)) = crate::kernel::registered_load_for_variable(variable)
                && let Some(kind) = crate::kernel::registered_load_kind_for_variable(variable)
            {
                for (selector, state) in self.preferred_snapshots() {
                    let snapshot = crate::kernel::intern_c_memory_ref(state.memory());
                    if crate::kernel::canonical_form_of_load(
                        snapshot.clone(),
                        pointer.clone(),
                        kind,
                    ) != *term
                    {
                        continue;
                    }
                    let load =
                        Bitvector32Term::MemoryLoad(snapshot, Box::new(pointer.clone()), kind);
                    if let Some(expression) =
                        super::super::surface_synthesis::synthesize_surface_machine_expression(
                            &load,
                            self.parameters,
                            self.arguments,
                            state,
                        )
                    {
                        return Some(ContractExpression::At {
                            selector: (*selector).clone(),
                            expression: Box::new(expression),
                        });
                    }
                }
                let load = Bitvector32Term::MemoryLoad(memory, Box::new(pointer), kind);
                return super::super::surface_synthesis::synthesize_surface_machine_expression(
                    &load,
                    self.parameters,
                    self.arguments,
                    self.current,
                );
            }
        }
        super::super::surface_synthesis::synthesize_surface_machine_expression(
            term,
            self.parameters,
            self.arguments,
            self.current,
        )
    }

    fn call(
        &self,
        name: &str,
        arguments: &[PureFunctionArgument],
        binders: &BTreeMap<crate::kernel::Variable, String>,
        depth: usize,
    ) -> Option<ContractExpression> {
        let depth = depth.checked_sub(1)?;
        let arguments = arguments
            .iter()
            .map(|argument| match argument {
                PureFunctionArgument::Value(CValue::Int32(value)) => {
                    self.machine(value, binders, depth)
                }
                PureFunctionArgument::ArrayRef {
                    memory,
                    pointer: CValue::Pointer(pointer),
                    ..
                } => self.array(memory, pointer.pointer()),
                PureFunctionArgument::Algebraic(term) => match &term.node {
                    crate::kernel::AlgebraicTermNode::Variable(variable) => binders
                        .get(variable)
                        .cloned()
                        .map(ContractExpression::Binding),
                    _ => None,
                },
                _ => None,
            })
            .collect::<Option<Vec<_>>>()?;
        Some(ContractExpression::Call {
            name: name.into(),
            arguments,
        })
    }

    fn array(&self, memory: &CMemory, pointer: &Pointer) -> Option<ContractExpression> {
        let base =
            self.parameters
                .iter()
                .zip(self.arguments)
                .find_map(|(parameter, argument)| {
                    let CExpression::Value(CValue::Pointer(value)) = argument else {
                        return None;
                    };
                    (value.pointer() == pointer).then(|| {
                        ContractExpression::CFragment(CExpression::Variable(
                            parameter.name().into(),
                        ))
                    })
                })?;
        if self.current.memory() == memory {
            return Some(base);
        }
        for (selector, state) in self.preferred_snapshots() {
            if state.memory() == memory {
                return Some(ContractExpression::At {
                    selector: (*selector).clone(),
                    expression: Box::new(base),
                });
            }
        }
        None
    }

    /// Named marks are the stable, author-chosen spelling when several
    /// recorded program points identify the same memory.
    fn preferred_snapshots(&self) -> impl Iterator<Item = &(&SnapshotSelector, &CState)> {
        self.recent
            .iter()
            .filter(|(selector, _)| matches!(selector, SnapshotSelector::Mark(_)))
            .chain(
                self.recent
                    .iter()
                    .filter(|(selector, _)| !matches!(selector, SnapshotSelector::Mark(_))),
            )
    }
}

/// Only a direct immutable base can be moved under the defining snapshot.
/// In particular, a current C local with the same spelling is insufficient.
fn immutable_field_hint(
    expression: &ContractExpression,
    address: &Pointer,
    locals: &BTreeMap<String, ContractExpression>,
) -> Option<String> {
    let mut expression = expression;
    for _ in 0..MAX_TRACE_FACT_DEPTH {
        match expression {
            ContractExpression::At {
                expression: inner, ..
            }
            | ContractExpression::Old(inner) => expression = inner,
            _ => break,
        }
    }
    let ContractExpression::Field {
        base,
        field,
        offset_bytes,
        lowered,
    } = expression
    else {
        return None;
    };
    let CExpression::TypedLoad { value_type, .. } = lowered else {
        return None;
    };
    if !value_type.is_pointer() {
        return None;
    }
    let (name, base) = match base.as_ref() {
        ContractExpression::Binding(name)
        | ContractExpression::CFragment(CExpression::Variable(name)) => {
            let ContractExpression::CFragment(CExpression::Value(CValue::Pointer(base))) =
                locals.get(name)?
            else {
                return None;
            };
            (name, base)
        }
        // Checked surface forms substitute model binders with their exact
        // values. Recover the immutable binder before spelling the field.
        ContractExpression::CFragment(CExpression::Value(CValue::Pointer(base))) => {
            let (name, _) = locals.iter().find(|(_, value)| matches!(value, ContractExpression::CFragment(CExpression::Value(CValue::Pointer(candidate))) if candidate == base))?;
            (name, base)
        }
        _ => return None,
    };
    let expected = base.pointer().offset_by_bytes(*offset_bytes);
    (expected.block == address.block
        && crate::kernel::offsets_have_same_canonical_form(&expected.offset, &address.offset))
    .then(|| crate::surface::diagnostics::describe_field_place(name, field))
}

#[cfg(test)]
mod pointer_trace_tests {
    use super::*;

    #[test]
    fn field_hint_recovers_substituted_immutable_binders_only_at_their_exact_address() {
        let base = Pointer::symbolic(Variable(990001));
        let value = CValue::typed_pointer(base.clone(), CType::Int32Pointer);
        let local = ContractExpression::CFragment(CExpression::Value(value.clone()));
        let locals = BTreeMap::from([("zid".to_string(), local.clone())]);
        let hint = |base_expression, value_type| ContractExpression::Field {
            base: Box::new(base_expression),
            field: "left".into(),
            offset_bytes: 8,
            lowered: CExpression::TypedLoad {
                pointer: Box::new(CExpression::Value(value.clone())),
                value_type,
                volatile: false,
                pointee_constant: false,
                source: Default::default(),
            },
        };
        let address = base.offset_by_bytes(8);
        let substituted = hint(local.clone(), CType::Int32Pointer);
        assert_eq!(
            immutable_field_hint(&substituted, &address, &locals),
            Some("zid->left".into())
        );
        assert_eq!(
            immutable_field_hint(&substituted, &base.offset_by_bytes(16), &locals),
            None
        );
        assert_eq!(
            immutable_field_hint(&hint(local, CType::UInt64), &address, &locals),
            None
        );
        assert_eq!(
            immutable_field_hint(&substituted, &address, &BTreeMap::new()),
            None
        );
        let reassigned = BTreeMap::from([(
            "zid".to_string(),
            ContractExpression::CFragment(CExpression::Value(CValue::typed_pointer(
                Pointer::symbolic(Variable(990002)),
                CType::Int32Pointer,
            ))),
        )]);
        assert_eq!(
            immutable_field_hint(&substituted, &address, &reassigned),
            None
        );
        // A C-local spelling is not enough to make it an immutable binder.
        assert_eq!(
            immutable_field_hint(
                &hint(
                    ContractExpression::CBinding("zid".into()),
                    CType::Int32Pointer
                ),
                &address,
                &locals
            ),
            None
        );
    }
}
