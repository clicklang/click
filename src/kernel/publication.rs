//! One-shot release/acquire publication through a C11 `atomic_int`.
//!
//! `atomic_init(&flag, 0)` consumes explicit ownership of the flag's storage
//! for good and mints exactly one `publisher(&flag, P)` and one
//! `subscriber(&flag, P)`, for the payload type `P` its call map names. The
//! publisher's single `memory_order_release` store of a nonzero value
//! surrenders one folded `P`; the subscriber's `memory_order_acquire` load
//! either returns zero and keeps the right, or returns nonzero and exchanges
//! the right for that `P`. Nothing else writes the flag, so a nonzero load
//! observes the one release store. Any other order is refused at the call.
//! The trusted runtime statement is `src/languages/c/modeled_pthread_spec.md`.

use super::loans::empty_checked_loan_evidence_sequence;
use super::prelude::*;
use crate::languages::c::thread_runtime::{
    ATOMIC_INIT_NAME, ATOMIC_INIT_PAYLOAD_BINDER_ID, ATOMIC_LOAD_NAME, ATOMIC_STORE_NAME,
};

/// `memory_order_acquire` and `memory_order_release` as `<stdatomic.h>`
/// numbers them.
const MEMORY_ORDER_ACQUIRE: i64 = 2;
const MEMORY_ORDER_RELEASE: i64 = 3;
/// The flag is an `int`.
const FLAG_BYTES: u32 = 4;

fn path(outcome: CStatementOutcome) -> CStatementExecutionPath {
    CStatementExecutionPath {
        loop_invariant_correspondence: Default::default(),
        outcome,
        facts: Vec::new().into(),
        obligations: Vec::new(),
        loan_evidence: empty_checked_loan_evidence_sequence(),
    }
}

fn refusal(message: impl Into<String>) -> CStatementOutcome {
    CStatementOutcome::RuntimeError(CRuntimeError::FunctionContract(message.into()))
}

fn order_name(order: i64) -> &'static str {
    match order {
        0 => "memory_order_relaxed",
        1 => "memory_order_consume",
        2 => "memory_order_acquire",
        3 => "memory_order_release",
        4 => "memory_order_acq_rel",
        5 => "memory_order_seq_cst",
        _ => "an unknown memory order",
    }
}

/// The checked order argument, or the refusal that names it.
fn required_order(
    value: &CValue,
    required: i64,
    operation: &str,
    assumptions: &PureFactContext,
) -> Result<(), CStatementOutcome> {
    let CValue::Int32(term) = value else {
        return Err(refusal(format!(
            "{operation} requires a constant memory order"
        )));
    };
    let Some(order) = super::assumptions::exact_signed_constant(term, assumptions) else {
        return Err(refusal(format!(
            "{operation} requires a constant memory order"
        )));
    };
    if order != required {
        return Err(refusal(format!(
            "{operation} with {} is not supported; one-shot publication uses {}",
            order_name(order),
            order_name(required)
        )));
    }
    Ok(())
}

pub(super) fn is_publication_operation(function_name: &str) -> bool {
    crate::languages::c::thread_runtime::is_publication_operation(function_name)
}

pub(super) fn execute_publication_paths(
    state: &CState,
    target: Option<&str>,
    function_name: &str,
    arguments: &[CExpression],
    assumptions: &PureFactContext,
    environment: &CExecutionEnvironment,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CStatementExecutionPath>> {
    let arity = if function_name == ATOMIC_STORE_NAME {
        3
    } else {
        2
    };
    let transport = environment
        .selected_call_binders
        .as_ref()
        .filter(|transport| transport.names_call_to(function_name));
    let payload = transport.and_then(|transport| {
        transport
            .type_arguments
            .get(&Variable(ATOMIC_INIT_PAYLOAD_BINDER_ID))
    });
    if state.pending_thread_create.is_some()
        || environment.selected_call_contract.is_some()
        || arguments.len() != arity
    {
        return Ok(vec![path(refusal(format!(
            "{function_name} requires a direct {arity}-argument call with no unresolved earlier create"
        )))]);
    }
    if function_name == ATOMIC_INIT_NAME && payload.is_none() {
        return Ok(vec![path(refusal(
            "atomic_init names the resource it publishes: step(atomic_init(&flag, 0), { payload: P(..) })",
        ))]);
    }
    if function_name != ATOMIC_INIT_NAME
        && transport.is_some_and(|transport| !transport.bindings.is_empty())
    {
        return Ok(vec![path(refusal(format!(
            "{function_name} selects its publication right by the flag; it takes no call map"
        )))]);
    }
    let mut paths = Vec::new();
    for argument_path in super::functions::evaluate_c_arguments_paths(
        state,
        arguments,
        assumptions,
        budget,
        Some(environment),
    )? {
        if let Some(outcome) = argument_path.outcome {
            paths.push(CStatementExecutionPath {
                outcome: match outcome {
                    CFunctionOutcome::UndefinedBehavior(error) => {
                        CStatementOutcome::UndefinedBehavior(error)
                    }
                    CFunctionOutcome::RuntimeError(error) => CStatementOutcome::RuntimeError(error),
                    _ => refusal(format!("{function_name} argument did not evaluate")),
                },
                facts: argument_path.facts,
                obligations: argument_path.obligations,
                ..path(refusal(""))
            });
            continue;
        }
        let current = super::reasoning::path_facts::assumptions_with_path_context(
            assumptions,
            &argument_path.facts,
            &argument_path.obligations,
        );
        let CValue::Pointer(flag) = &argument_path.values[0] else {
            paths.push(path(refusal(format!(
                "{function_name} requires an atomic flag pointer"
            ))));
            continue;
        };
        if flag.is_null() {
            paths.push(path(refusal(format!(
                "{function_name} requires a nonnull atomic flag pointer"
            ))));
            continue;
        }
        let flag = flag.pointer().clone();
        let outcome = if function_name == ATOMIC_INIT_NAME {
            initialize(
                state,
                &flag,
                &argument_path.values[1],
                payload.expect("checked payload"),
                &current,
            )
            .map(|state| (state, None))
        } else if function_name == ATOMIC_STORE_NAME {
            release_store(
                state,
                &flag,
                &argument_path.values[1],
                &argument_path.values[2],
                &current,
                environment,
                budget,
            )?
            .map(|state| (state, None))
        } else {
            debug_assert_eq!(function_name, ATOMIC_LOAD_NAME);
            acquire_load(state, &flag, &argument_path.values[1], &current, budget)?
                .map(|(state, value)| (state, Some(value)))
        };
        {
            let facts = argument_path.facts.clone();
            let mut obligations = argument_path.obligations.clone();
            let outcome = match outcome {
                Err(outcome) => outcome,
                Ok((mut next, loaded)) => {
                    let assigned = match (target, loaded) {
                        (Some(target), Some(value)) => super::loops::assign_call_result(
                            &mut next,
                            target,
                            value,
                            &mut obligations,
                            &current,
                        ),
                        (Some(_), None) => Err(CRuntimeError::TypeMismatch),
                        (None, _) => Ok(()),
                    };
                    match assigned {
                        Ok(()) => CStatementOutcome::Normal(Box::new(next)),
                        Err(error) => CStatementOutcome::RuntimeError(error),
                    }
                }
            };
            paths.push(CStatementExecutionPath {
                loop_invariant_correspondence: Default::default(),
                outcome,
                facts,
                obligations,
                loan_evidence: empty_checked_loan_evidence_sequence(),
            });
        }
    }
    budget.check_path_width(paths.len())?;
    Ok(paths)
}

/// Consumes the flag's explicit storage ownership and mints both rights.
fn initialize(
    state: &CState,
    flag: &Pointer,
    value: &CValue,
    payload: &crate::kernel::ResourceDescription,
    assumptions: &PureFactContext,
) -> Result<CState, CStatementOutcome> {
    if !matches!(value, CValue::Int32(term) if super::assumptions::exact_signed_constant(term, assumptions) == Some(0))
    {
        return Err(refusal(
            "atomic_init of a publication flag stores 0: a nonzero flag means published",
        ));
    }
    if !payload.schema().fields().is_empty() {
        return Err(refusal(
            "the published resource must have no fields in the one-shot publication subset",
        ));
    }
    if assumptions.decide(&ConditionTerm::pointer_aligned(
        flag.clone(),
        u64::from(FLAG_BYTES),
    )) != Some(true)
    {
        return Err(CStatementOutcome::RuntimeError(
            CRuntimeError::MissingMutexStorageAlignment {
                mutex: flag.clone(),
                alignment: FLAG_BYTES,
            },
        ));
    }
    let resources = state
        .resources
        .clone()
        .without_owned_storage_access(flag, FLAG_BYTES, assumptions)
        .ok_or_else(|| {
            CStatementOutcome::RuntimeError(CRuntimeError::MissingResource {
                resource: Box::new(CResourceFact::own_memory(
                    CMemoryRange::new_with_element_width(
                        flag.clone(),
                        0u32.into(),
                        FLAG_BYTES.into(),
                        1,
                    ),
                )),
            })
        })?;
    let rights = [PublicationSide::Publisher, PublicationSide::Subscriber].map(|side| {
        CResourceFact::own(CResource::Publication(PublicationRight::new(
            side,
            flag.clone(),
            payload.clone(),
        )))
    });
    let resources = resources
        .try_compose_with_facts_delaying_normalization(rights, assumptions)
        .map_err(|_| refusal("publication rights conflict with current resources"))?;
    let mut next = state.clone();
    next.resources = resources;
    Ok(next)
}

/// The owned folded payload a right publishes.
fn payload_fact(right: &PublicationRight) -> CResourceFact {
    CResourceFact::own(CResource::Composite {
        name: right.payload().family().to_string(),
        arguments: right.payload().arguments().iter().cloned().collect(),
    })
}

/// Surrenders the publisher right and one folded payload, and forgets the
/// payload's memory as an unlock forgets protected memory.
fn release_store(
    state: &CState,
    flag: &Pointer,
    desired: &CValue,
    order: &CValue,
    assumptions: &PureFactContext,
    environment: &CExecutionEnvironment,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Result<CState, CStatementOutcome>> {
    if let Err(outcome) =
        required_order(order, MEMORY_ORDER_RELEASE, ATOMIC_STORE_NAME, assumptions)
    {
        return Ok(Err(outcome));
    }
    let CValue::Int32(desired) = desired else {
        return Ok(Err(refusal("atomic_store_explicit stores an int")));
    };
    if assumptions.decide(&ConditionTerm::Bitvector32Equal(
        Box::new(desired.clone()),
        Box::new(Bitvector32Term::Constant(0)),
    )) != Some(false)
    {
        return Ok(Err(refusal(
            "a publishing store must store a value proven nonzero",
        )));
    }
    let Some(right_fact) = state
        .resources
        .publication_right_at(PublicationSide::Publisher, flag)
        .cloned()
    else {
        return Ok(Err(refusal(
            "a release store to a publication flag requires owns publisher(flag, P)",
        )));
    };
    let CResource::Publication(right) = right_fact.resource() else {
        unreachable!()
    };
    let payload = payload_fact(right);
    let ranges = super::functions::checked_owned_memory_ranges(
        &payload,
        &environment.modeled_mutex_definition_list,
        state,
        assumptions,
    );
    let Some(resources) = state
        .resources
        .clone()
        .without_fact_delaying_normalization(&right_fact, assumptions)
        .and_then(|resources| resources.without_fact_delaying_normalization(&payload, assumptions))
    else {
        return Ok(Err(CStatementOutcome::RuntimeError(
            CRuntimeError::MissingResource {
                resource: Box::new(payload),
            },
        )));
    };
    let Some(ranges) = ranges else {
        return Ok(Err(refusal(
            "the published resource has no checked memory footprint",
        )));
    };
    let mut next = state.clone();
    next.resources = resources;
    if !ranges.is_empty() {
        let kept = ranges
            .iter()
            .any(CMemoryRange::is_unnamed_footprint)
            .then(|| {
                super::functions::call_kept_ownership(
                    &next.resources,
                    &environment.modeled_mutex_definition_list,
                    state,
                    assumptions,
                )
            });
        next.memory = state.memory.clone().with_call_memory_havoc(
            budget.allocate_kernel_variable()?,
            &ranges,
            assumptions,
            kept.as_ref(),
        );
    }
    Ok(Ok(next))
}

/// Returns a fresh value. With the subscriber right, the right is marked as
/// read through that value; the C branch that decides whether it is zero
/// keeps the right or exchanges it for the payload
/// ([`resolve_observed_publications`]). Without the right a load observes
/// some value and receives nothing.
fn acquire_load(
    state: &CState,
    flag: &Pointer,
    order: &CValue,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Result<(CState, CValue), CStatementOutcome>> {
    if let Err(outcome) = required_order(order, MEMORY_ORDER_ACQUIRE, ATOMIC_LOAD_NAME, assumptions)
    {
        return Ok(Err(outcome));
    }
    let value =
        super::functions::symbolic_call_result(CType::Int32, budget.allocate_kernel_variable()?);
    let Some(right_fact) = state
        .resources
        .publication_right_at(PublicationSide::Subscriber, flag)
        .cloned()
    else {
        return Ok(Ok((state.clone(), value)));
    };
    let CResource::Publication(right) = right_fact.resource() else {
        unreachable!()
    };
    if right.observed.is_some() {
        return Ok(Err(refusal(
            "an earlier acquire load's value has not been tested by a C branch, so the subscriber right is not yet kept or exchanged",
        )));
    }
    let Some(resources) = state
        .resources
        .clone()
        .without_fact_delaying_normalization(&right_fact, assumptions)
    else {
        return Ok(Err(refusal("the subscriber right could not be consumed")));
    };
    let mut observed = right.clone();
    observed.observed = Some(value.clone());
    let Ok(resources) = resources.try_compose_with_facts_delaying_normalization(
        [CResourceFact::own(CResource::Publication(observed))],
        assumptions,
    ) else {
        return Ok(Err(refusal(
            "the observed subscriber right conflicts with current resources",
        )));
    };
    let mut next = state.clone();
    next.resources = resources;
    Ok(Ok((next, value)))
}

/// Settles each subscriber right read by an acquire load whose value the
/// branch facts now decide: zero keeps the right, nonzero exchanges it for
/// the published payload. Undecided rights stay observed. Only the flags of
/// observed rights are consulted, through the publication index.
pub(crate) fn resolve_observed_publications(
    state: &CState,
    assumptions: &PureFactContext,
) -> CState {
    let observed = state.resources.observed_publication_rights();
    if observed.is_empty() {
        return state.clone();
    }
    let mut next = state.clone();
    for fact in observed {
        let CResource::Publication(right) = fact.resource() else {
            continue;
        };
        let Some(CValue::Int32(term)) = &right.observed else {
            continue;
        };
        let zero = ConditionTerm::Bitvector32Equal(
            Box::new(term.clone()),
            Box::new(Bitvector32Term::Constant(0)),
        );
        let Some(unpublished) = assumptions.decide(&zero) else {
            continue;
        };
        let replacement = if unpublished {
            let mut kept = right.clone();
            kept.observed = None;
            CResourceFact::own(CResource::Publication(kept))
        } else {
            payload_fact(right)
        };
        let Some(resources) = next
            .resources
            .clone()
            .without_fact_delaying_normalization(&fact, assumptions)
        else {
            continue;
        };
        if let Ok(resources) =
            resources.try_compose_with_facts_delaying_normalization([replacement], assumptions)
        {
            next.resources = resources;
        }
    }
    next
}
