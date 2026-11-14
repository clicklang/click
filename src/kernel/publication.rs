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

use super::prelude::*;
use crate::kernel::{CompareRelation, MachineIntegerType};
use crate::languages::c::thread_runtime::{
    ATOMIC_INIT_NAME, ATOMIC_INIT_PAYLOAD_BINDER_ID, ATOMIC_LOAD_NAME, ATOMIC_STORE_NAME,
};

/// `memory_order_acquire` and `memory_order_release` as `<stdatomic.h>`
/// numbers them.
const MEMORY_ORDER_ACQUIRE: i64 = 2;
const MEMORY_ORDER_RELEASE: i64 = 3;
/// The flag is an `int`.
const FLAG_BYTES: u32 = 4;

fn path(outcome: StatementOutcome) -> StatementExecutionPath {
    StatementExecutionPath::new(outcome, Vec::new().into(), Vec::new())
}

fn refusal(message: impl Into<String>) -> StatementOutcome {
    StatementOutcome::RuntimeError(RuntimeError::FunctionContract(message.into()))
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
    value: &ProgramValue,
    required: i64,
    operation: &str,
    assumptions: &PureFactContext,
) -> Result<(), StatementOutcome> {
    let ProgramValue::Int32(term) = value else {
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
    state: &ExecutionState,
    target: Option<&str>,
    function_name: &str,
    arguments: &[ProgramExpression],
    assumptions: &PureFactContext,
    environment: &ExecutionEnvironment,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<StatementExecutionPath>> {
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
            "atomic_init names the resource it publishes: step(atomic_init, { payload: P(..) })",
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
            paths.push(StatementExecutionPath {
                outcome: match outcome {
                    FunctionOutcome::UndefinedBehavior(error) => {
                        StatementOutcome::UndefinedBehavior(error)
                    }
                    FunctionOutcome::RuntimeError(error) => StatementOutcome::RuntimeError(error),
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
        let ProgramValue::Pointer(flag) = &argument_path.values[0] else {
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
            let mut call_result = None;
            let outcome = match outcome {
                Err(outcome) => outcome,
                Ok((mut next, loaded)) => {
                    call_result = loaded.clone();
                    let assigned = match (target, loaded) {
                        (Some(target), Some(value)) => super::loops::assign_call_result(
                            &mut next,
                            target,
                            value,
                            &mut obligations,
                            &current,
                        ),
                        (Some(_), None) => Err(RuntimeError::TypeMismatch),
                        (None, _) => Ok(()),
                    };
                    match assigned {
                        Ok(()) => StatementOutcome::Normal(Box::new(next)),
                        Err(error) => StatementOutcome::RuntimeError(error),
                    }
                }
            };
            paths.push(
                StatementExecutionPath::new(outcome, facts, obligations)
                    .with_call_result(call_result),
            );
        }
    }
    budget.check_path_width(paths.len())?;
    Ok(paths)
}

/// Consumes the flag's explicit storage ownership and mints both rights.
fn initialize(
    state: &ExecutionState,
    flag: &Pointer,
    value: &ProgramValue,
    payload: &crate::kernel::ResourceDescription,
    assumptions: &PureFactContext,
) -> Result<ExecutionState, StatementOutcome> {
    if !matches!(value, ProgramValue::Int32(term) if super::assumptions::exact_signed_constant(term, assumptions) == Some(0))
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
        return Err(StatementOutcome::RuntimeError(
            RuntimeError::MissingMutexStorageAlignment {
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
            StatementOutcome::RuntimeError(RuntimeError::MissingResource {
                resource: Box::new(ResourceFact::own_memory(
                    MemoryRange::new_with_element_width(
                        flag.clone(),
                        0u32.into(),
                        FLAG_BYTES.into(),
                        1,
                    ),
                )),
            })
        })?;
    let rights = [PublicationSide::Publisher, PublicationSide::Subscriber].map(|side| {
        ResourceFact::own(Resource::Publication(PublicationRight::new(
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
fn payload_fact(right: &PublicationRight) -> ResourceFact {
    ResourceFact::own(Resource::Composite {
        name: right.payload().family().to_string(),
        arguments: right.payload().arguments().iter().cloned().collect(),
    })
}

/// Surrenders the publisher right and one folded payload, and forgets the
/// payload's memory as an unlock forgets protected memory.
fn release_store(
    state: &ExecutionState,
    flag: &Pointer,
    desired: &ProgramValue,
    order: &ProgramValue,
    assumptions: &PureFactContext,
    environment: &ExecutionEnvironment,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Result<ExecutionState, StatementOutcome>> {
    if let Err(outcome) =
        required_order(order, MEMORY_ORDER_RELEASE, ATOMIC_STORE_NAME, assumptions)
    {
        return Ok(Err(outcome));
    }
    let ProgramValue::Int32(desired) = desired else {
        return Ok(Err(refusal("atomic_store_explicit stores an int")));
    };
    if assumptions.decide(&ConditionTerm::Compare {
        format: MachineIntegerType::Int32,
        relation: CompareRelation::Equal,
        left: Box::new(desired.clone()),
        right: Box::new(MachineTerm::constant(0)),
    }) != Some(false)
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
    let Resource::Publication(right) = right_fact.resource() else {
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
        return Ok(Err(StatementOutcome::RuntimeError(
            RuntimeError::MissingResource {
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
            .any(MemoryRange::is_unnamed_footprint)
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
    state: &ExecutionState,
    flag: &Pointer,
    order: &ProgramValue,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Result<(ExecutionState, ProgramValue), StatementOutcome>> {
    if let Err(outcome) = required_order(order, MEMORY_ORDER_ACQUIRE, ATOMIC_LOAD_NAME, assumptions)
    {
        return Ok(Err(outcome));
    }
    let value = super::functions::symbolic_call_result(
        ProgramType::Int32,
        budget.allocate_kernel_variable()?,
    );
    let Some(right_fact) = state
        .resources
        .publication_right_at(PublicationSide::Subscriber, flag)
        .cloned()
    else {
        return Ok(Ok((state.clone(), value)));
    };
    let Resource::Publication(right) = right_fact.resource() else {
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
        [ResourceFact::own(Resource::Publication(observed))],
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
    state: &ExecutionState,
    assumptions: &PureFactContext,
) -> ExecutionState {
    let observed = state.resources.observed_publication_rights();
    if observed.is_empty() {
        return state.clone();
    }
    let mut next = state.clone();
    for fact in observed {
        let Resource::Publication(right) = fact.resource() else {
            continue;
        };
        let Some(ProgramValue::Int32(term)) = &right.observed else {
            continue;
        };
        let zero = ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::Equal,
            left: Box::new(term.clone()),
            right: Box::new(MachineTerm::constant(0)),
        };
        let Some(unpublished) = assumptions.decide(&zero) else {
            continue;
        };
        let replacement = if unpublished {
            let mut kept = right.clone();
            kept.observed = None;
            ResourceFact::own(Resource::Publication(kept))
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::{ResourceDescription, ResourceFieldSchema};

    fn flag(index: usize) -> Pointer {
        Pointer {
            block: format!("publication-flag-{index}").into(),
            offset: PointerOffsetTerm::Constant(0),
        }
    }

    fn payload(index: usize) -> ResourceDescription {
        ResourceDescription::new(
            "ready_payload".to_string(),
            vec![ProgramValue::pointer(flag(index)).into()].into(),
            ResourceFieldSchema::new(vec![]).expect("empty schema"),
        )
    }

    fn right(side: PublicationSide, index: usize) -> ResourceFact {
        ResourceFact::own(Resource::Publication(PublicationRight::new(
            side,
            flag(index),
            payload(index),
        )))
    }

    /// Subscriber rights for flags `0..subscribers`, beside `unrelated`
    /// other flags' publisher rights and as many owned cells.
    fn state(subscribers: usize, unrelated: usize) -> ExecutionState {
        let mut memory = Memory::new();
        let mut resources = ResourceContext::new();
        for index in 0..subscribers {
            resources = resources.unchecked_with_fact(right(PublicationSide::Subscriber, index));
        }
        for index in subscribers..subscribers + unrelated {
            let cell = Pointer {
                block: format!("unrelated-cell-{index}").into(),
                offset: PointerOffsetTerm::Constant(0),
            };
            memory = memory
                .with_block(cell.block.clone(), 4)
                .store(cell.clone(), int32(0));
            resources = resources
                .unchecked_with_fact(right(PublicationSide::Publisher, index))
                .unchecked_with_fact(ResourceFact::own_memory(MemoryRange::new(
                    cell,
                    0.into(),
                    1.into(),
                )));
        }
        ExecutionState::new()
            .with_memory(memory)
            .with_resource_context(resources)
    }

    /// Acquire-loads every subscriber flag, then settles them all as
    /// published, returning the deterministic work of each phase.
    fn acquire_and_settle(subscribers: usize, unrelated: usize) -> (usize, usize) {
        let state = state(subscribers, unrelated);
        let empty = PureFactContext::new();
        let mut budget = ExecutionBudget::new();
        let mut values = Vec::new();
        let (observed, load_work) = crate::instrumentation::measure_deterministic_work(|| {
            let mut current = state.clone();
            for index in 0..subscribers {
                let (next, value) =
                    acquire_load(&current, &flag(index), &int32(2), &empty, &mut budget)
                        .unwrap()
                        .unwrap();
                values.push(value);
                current = next;
            }
            current
        });
        let published = values
            .into_iter()
            .fold(PureFactContext::new(), |facts, value| {
                let ProgramValue::Int32(term) = value else {
                    unreachable!()
                };
                facts.assume_proposition(Proposition::ConditionIs(
                    ConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::Equal,
                        left: Box::new(term),
                        right: Box::new(MachineTerm::constant(0)),
                    },
                    false,
                ))
            });
        assert_eq!(
            observed.resources.observed_publication_rights().len(),
            subscribers
        );
        let (settled, settle_work) = crate::instrumentation::measure_deterministic_work(|| {
            resolve_observed_publications(&observed, &published)
        });
        assert!(!settled.resources.has_observed_publication_rights());
        for index in 0..subscribers {
            assert!(
                settled
                    .resources
                    .publication_right_at(PublicationSide::Subscriber, &flag(index))
                    .is_none()
            );
            assert!(settled.resources.satisfies_fact(
                &payload_fact(&PublicationRight::new(
                    PublicationSide::Subscriber,
                    flag(index),
                    payload(index)
                )),
                &empty,
            ));
        }
        assert!(load_work > 0 && settle_work > 0);
        (load_work, settle_work)
    }

    #[test]
    fn one_acquire_and_settle_ignore_unrelated_flags_and_resources() {
        let samples = [8usize, 16, 32, 64]
            .into_iter()
            .map(|unrelated| (unrelated, acquire_and_settle(1, unrelated)))
            .collect::<Vec<_>>();
        let (_, (first_load, first_settle)) = samples[0];
        let (_, (last_load, last_settle)) = samples[samples.len() - 1];
        // Eight times the unrelated context may cost an indexed lookup's
        // logarithmic factor, never a pass over the context.
        assert!(
            last_load <= first_load * 2 && last_settle <= first_settle * 2,
            "publication work grew with unrelated resources: {samples:?}"
        );
    }

    #[test]
    fn settling_reads_scales_with_the_reads_settled() {
        let samples = [8usize, 16, 32, 64]
            .into_iter()
            .map(|subscribers| (subscribers, acquire_and_settle(subscribers, 8)))
            .collect::<Vec<_>>();
        for pair in samples.windows(2) {
            let ((_, (load, settle)), (_, (next_load, next_settle))) = (pair[0], pair[1]);
            assert!(
                next_load <= load * 3 && next_settle <= settle * 3,
                "publication work grew faster than the reads: {samples:?}"
            );
        }
    }
}
