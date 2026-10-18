use super::*;

#[derive(Default)]
struct MemoryLoadAliasCache {
    resolution_equal: BTreeMap<(u64, Pointer), bool>,
    resolution_distinct: BTreeMap<(u64, Pointer), bool>,
    equal: BTreeMap<(u64, Pointer), bool>,
}

impl MemoryLoadAliasCache {
    fn resolution_equal(
        &mut self,
        pointer: &Pointer,
        stored_pointer: &Pointer,
        assumptions: &PureFactContext,
    ) -> bool {
        *self
            .resolution_equal
            .entry((assumptions.memo_fingerprint(), stored_pointer.clone()))
            .or_insert_with(|| {
                pointers_proven_equal_for_memory_resolution(pointer, stored_pointer, assumptions)
            })
    }

    fn resolution_distinct(
        &mut self,
        pointer: &Pointer,
        stored_pointer: &Pointer,
        assumptions: &PureFactContext,
    ) -> bool {
        *self
            .resolution_distinct
            .entry((assumptions.memo_fingerprint(), stored_pointer.clone()))
            .or_insert_with(|| {
                pointers_proven_distinct_for_memory_resolution(pointer, stored_pointer, assumptions)
            })
    }

    fn equal(
        &mut self,
        pointer: &Pointer,
        stored_pointer: &Pointer,
        assumptions: &PureFactContext,
    ) -> bool {
        *self
            .equal
            .entry((assumptions.memo_fingerprint(), stored_pointer.clone()))
            .or_insert_with(|| {
                pointers_proven_equal_by_reasoning(pointer, stored_pointer, assumptions)
            })
    }
}

#[allow(clippy::too_many_arguments)]
pub(in crate::kernel) fn evaluate_c_memory_load_paths(
    memory: &CMemory,
    pointer: Pointer,
    value_type: CType,
    facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
    has_external_read_resource: bool,
    volatile: bool,
    source: Option<&LoadSourceId>,
    byte_order: Option<ByteOrder>,
) -> Vec<CExpressionPath> {
    let _assumptions_id_scope = assumptions.enter_id_scope();
    if has_pending_reallocation_for_pointer(memory, &pointer) {
        return vec![CExpressionPath {
            outcome: CExpressionOutcome::RuntimeError(CRuntimeError::UnresolvedAllocationOutcome),
            facts,
            obligations,
        }];
    }
    let pointer_for_call_alias = pointer.clone();
    let mut alias_cache = MemoryLoadAliasCache::default();
    // Function reads have an exact load-variable identity, including when
    // reading a borrowed callback table in an ordinary statement proof.
    let observed = (!volatile
        && (assumptions.should_require_owned_expression_loads()
            || matches!(value_type, CType::FunctionPointer(_))))
    .then(|| (crate::kernel::intern_c_memory_ref(memory), pointer.clone()));
    let word_storage =
        (!volatile && matches!(value_type, CType::Int64 | CType::UInt64)).then(|| pointer.clone());
    let mut paths = evaluate_c_memory_load_paths_with_alias_cache(
        memory,
        pointer,
        value_type,
        facts,
        obligations,
        assumptions,
        has_external_read_resource,
        if volatile {
            LoadPurpose::VolatileProgram
        } else {
            LoadPurpose::Program
        },
        &mut alias_cache,
        source,
        byte_order,
    );
    if let Some(address) = word_storage {
        for path in &mut paths {
            if let CExpressionOutcome::Value(value) = &mut path.outcome {
                *value = complete_loaded_word(value.clone(), memory, &address);
            }
        }
    }
    if !volatile {
        for path in &mut paths {
            if let CExpressionOutcome::Value(CValue::Pointer(value)) = &mut path.outcome {
                *value = assumptions.pointer_value_at_entry(value);
                if SpecificationReadScope::is_active() {
                    assumptions
                        .equality_graph
                        .retain_canonical_pointer_read_definition(value.pointer());
                }
            }
        }
    }
    if let Some(observed) = observed {
        for path in &mut paths {
            let CExpressionOutcome::Value(CValue::Pointer(value)) = &path.outcome else {
                continue;
            };
            // A checked, nonvolatile C read supplies its complete current-cell
            // equation. Ordinary observations do not publish this evidence.
            path.facts.push(ExecutionPureFact::logical_read_equation(
                value.clone(),
                Pointer::loaded_value(&observed.0, &observed.1),
            ));
            let mut read_facts = ExecutionFacts::new();
            if let Some(variable) = typed_pointer_read_variable(value.pointer())
                && let Some(load) =
                    crate::kernel::equality_graph::logical_pointer_read_term(value.pointer())
            {
                // Build the selected evidence in a fresh stream, without
                // searching or rewriting unrelated incoming path facts.
                record_load_variable_defining_fact_with_source_and_pointer(
                    variable,
                    load,
                    &mut read_facts,
                    source,
                    Some(value.pointer()),
                );
            }
            for mut fact in read_facts {
                if let Some(GeneratedLoadBinding::Exact {
                    observed_pointer_read,
                    ..
                }) = fact.generated_load_binding.as_deref_mut()
                {
                    *observed_pointer_read = Some(observed.clone());
                }
                path.facts.push(fact);
            }
        }
    }
    if !volatile && SpecificationReadScope::is_active() {
        retain_call_read_aliases(
            memory,
            &pointer_for_call_alias,
            value_type,
            assumptions,
            &mut paths,
        );
    }
    paths
}

/// The paths of one *specification* load: a read written in a contract, an
/// invariant, or a proof step, rather than a read the C program performs.
///
/// A specification load denotes the value one named snapshot holds at one
/// pointer. It is not a step of the program, so it has no branch to take: an
/// alias it cannot resolve leaves the load term unresolved rather than
/// splitting into the cases a C execution would have to choose between. The
/// one-term spec load rule already governs the non-symbolic spec path in
/// `crate::kernel::spec`; this is the same rule on the symbolic one.
pub(in crate::kernel) fn evaluate_spec_memory_load_paths(
    memory: &CMemory,
    pointer: Pointer,
    value_type: CType,
    facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Vec<CExpressionPath> {
    let _assumptions_id_scope = assumptions.enter_id_scope();
    if has_pending_reallocation_for_pointer(memory, &pointer) {
        return vec![CExpressionPath {
            outcome: CExpressionOutcome::RuntimeError(CRuntimeError::UnresolvedAllocationOutcome),
            facts,
            obligations,
        }];
    }
    let mut alias_cache = MemoryLoadAliasCache::default();
    evaluate_c_memory_load_paths_with_alias_cache(
        memory,
        pointer,
        value_type,
        facts,
        obligations,
        assumptions,
        false,
        LoadPurpose::Validity,
        &mut alias_cache,
        None,
        // A specification load denotes a snapshot's cell, not a C access;
        // it has no byte view of a wider cell.
        None,
    )
}

/// Construct the value of a logical read using the shared typed load model.
/// No C access occurs and no validity evidence is introduced.
pub(in crate::kernel) fn evaluate_logical_memory_load_paths(
    memory: &CMemory,
    pointer: Pointer,
    value_type: CType,
    facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Vec<CExpressionPath> {
    let mut paths = evaluate_logical_memory_load_paths_unbridged(
        memory,
        pointer.clone(),
        value_type,
        facts,
        obligations,
        assumptions,
    );
    retain_call_read_aliases(memory, &pointer, value_type, assumptions, &mut paths);
    paths
}

fn evaluate_logical_memory_load_paths_unbridged(
    memory: &CMemory,
    pointer: Pointer,
    value_type: CType,
    facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Vec<CExpressionPath> {
    let pointer = logical_memory_load_address(memory, pointer, value_type, assumptions);
    if assumptions.should_keep_spec_loads_symbolic() {
        let _assumptions_id_scope = assumptions.enter_id_scope();
        let mut paths = evaluate_c_memory_load_paths_with_alias_cache(
            memory,
            pointer.clone(),
            value_type,
            facts,
            obligations,
            assumptions,
            false,
            LoadPurpose::Logical,
            &mut MemoryLoadAliasCache::default(),
            None,
            None,
        );
        for path in &mut paths {
            // An invalid typed read still denotes a logical value. The C
            // evaluator's refusal is retained only by checked evaluation.
            if matches!(path.outcome, CExpressionOutcome::RuntimeError(_))
                && let Some(value) = canonicalized_symbolic_load_value_with_identity(
                    memory,
                    &pointer,
                    value_type,
                    &mut path.facts,
                    assumptions,
                    should_use_symbolic_pointer_identity(memory, &pointer, value_type),
                    None,
                    LoadPurpose::Logical,
                )
            {
                path.outcome = CExpressionOutcome::Value(value);
            }
            if let CExpressionOutcome::Value(value) = &mut path.outcome {
                *value = complete_loaded_word(value.clone(), memory, &pointer);
                if let CValue::Pointer(value) = value {
                    assumptions
                        .equality_graph
                        .retain_canonical_pointer_read_definition(value.pointer());
                }
            }
            path.facts
                .retain(|fact| !is_load_variable_defining_fact(fact.proposition()));
        }
        return paths;
    }
    let mut facts = facts;
    let value = memory
        .known_union_value(&pointer, value_type)
        .filter(|value| value_type.accepts(value))
        .or_else(|| {
            memory.known_value(&pointer).and_then(|stored| {
                let complete_pointer = matches!(&stored, CValue::Pointer(_))
                    || matches!(&stored, CValue::Int32(Bitvector32Term::Variable(variable))
                        if registered_load_kind_for_variable(variable) == Some(LoadKind::Bits32)
                            && registered_load_bytes_for_variable(variable)
                                == Some(crate::kernel::C_POINTER_BYTE_WIDTH));
                canonicalized_pointer_value_from_int_cell(
                    memory,
                    &pointer,
                    &stored,
                    value_type,
                    &mut facts,
                    assumptions,
                    None,
                    LoadPurpose::Logical,
                )
                .or_else(|| value_type.read_cell(&stored))
                .inspect(|value| {
                    if let CValue::Pointer(value) = value {
                        record_pointer_read_observation(value.pointer(), memory, &pointer);
                        let current = Pointer::loaded_value(
                            &crate::kernel::intern_c_memory_ref(memory),
                            &pointer,
                        );
                        if complete_pointer {
                            // The cached value was selected under this path's
                            // premises. Carry its current-cell equation with
                            // the result, rather than treating a global read
                            // observation as evidence in another context.
                            facts.push(ExecutionPureFact::logical_read_equation(
                                value.clone(),
                                current,
                            ));
                        }
                    }
                })
            })
        })
        .or_else(|| {
            // The cell may be stored under another spelling of this address:
            // a C store through `p` after the path proved `p == id`, read
            // here through `id`. The equality holds on this path, so the
            // stored value is this snapshot's value at the address. Only a
            // block the pointer classes put with others is retried.
            assumptions
                .equality_graph
                .pointer_spellings(&pointer)
                .into_iter()
                .find_map(|spelling| {
                    let stored = memory.known_value(&spelling)?;
                    value_type.read_cell(&stored)
                })
        })
        .or_else(|| {
            canonicalized_symbolic_load_value_with_identity(
                memory,
                &pointer,
                value_type,
                &mut facts,
                assumptions,
                should_use_symbolic_pointer_identity(memory, &pointer, value_type),
                None,
                LoadPurpose::Logical,
            )
        });
    facts.retain(|fact| !is_load_variable_defining_fact(fact.proposition()));
    value
        .into_iter()
        .map(|value| {
            if let CValue::Pointer(pointer) = &value {
                assumptions
                    .equality_graph
                    .retain_canonical_pointer_read_definition(pointer.pointer());
            }
            CExpressionPath {
                outcome: CExpressionOutcome::Value(complete_loaded_word(value, memory, &pointer)),
                facts: facts.clone(),
                obligations: obligations.clone(),
            }
        })
        .collect()
}

/// Name the selected caller read with the existing scalar normalizer.
/// No C access, pointer-carrier recovery, or whole-snapshot equality occurs.
fn canonical_integer_read(
    memory: &CMemory,
    pointer: &Pointer,
    ty: CType,
) -> Option<Bitvector32Term> {
    let kind = match ty {
        CType::Bool | CType::Int8 | CType::UInt8 => LoadKind::UInt8,
        CType::Int16 => LoadKind::Int16,
        CType::UInt16 => LoadKind::UInt16,
        CType::Int32 | CType::UInt32 => LoadKind::Bits32,
        CType::Int64 | CType::UInt64 => LoadKind::Bits64,
        _ => return None,
    };
    let value = canonical_form_of_load(
        crate::kernel::intern_c_memory_ref(memory),
        pointer.clone(),
        kind,
    );
    Some(match ty {
        CType::Int8 => Bitvector32Term::signed_byte(value),
        CType::Bool => Bitvector32Term::if_then_else(
            ConditionTerm::equal(value, Bitvector32Term::Constant(0)),
            Bitvector32Term::Constant(0),
            Bitvector32Term::Constant(1),
        ),
        _ => value,
    })
}

fn retain_call_read_aliases(
    memory: &CMemory,
    pointer: &Pointer,
    value_type: CType,
    _assumptions: &PureFactContext,
    paths: &mut [CExpressionPath],
) {
    // A producer with alternative paths cannot install either arm into the
    // shared input context. Likewise, unproved expression-local conditions
    // must remain with their path instead of becoming checked definitions.
    if paths.len() != 1 || paths[0].facts.iter().any(|fact| !fact.is_certified()) {
        return;
    }
    let Some(source_memory) = super::super::functions::call_read_aliases::source_for(memory) else {
        return;
    };
    let Some(source) = source_memory
        .known_value(pointer)
        .and_then(|stored| value_type.read_cell(&stored))
        .and_then(|value| crate::kernel::spec::c_value_bitvector_term(&value))
        .or_else(|| canonical_integer_read(&source_memory, pointer, value_type))
    else {
        return;
    };
    for path in paths {
        let CExpressionOutcome::Value(value) = &path.outcome else {
            continue;
        };
        let Some(value) = crate::kernel::spec::c_value_bitvector_term(value) else {
            continue;
        };
        if source == value {
            continue;
        }
        // Carry only the selected numeric equation. Ordinary fact admission
        // installs it in the shared graph after scratch call contexts expire.
        let equal = match value_type {
            CType::Int64 => ConditionTerm::int64_equal(source.clone(), value),
            CType::UInt64 => ConditionTerm::uint64_equal(source.clone(), value),
            _ => ConditionTerm::equal(source.clone(), value),
        };
        path.facts.push(ExecutionPureFact {
            logical_read_equation: true,
            ..ExecutionPureFact::certified(Proposition::ConditionIs(equal, true))
        });
    }
}

/// Use a published footprint only to select coordinates for this logical
/// address. Equality of the address grants no access or snapshot transport.
fn logical_memory_load_address(
    memory: &CMemory,
    pointer: Pointer,
    value_type: CType,
    assumptions: &PureFactContext,
) -> Pointer {
    // Only opaque model pointers and external pointers with an admitted
    // cross-block alias can need another spelling. Wide scalar loads need
    // the cached coordinate because their equalities do not use int32 load
    // congruence. Keep ordinary and loaded-pointer reads on their fast path.
    let model_pointer = match &pointer.block {
        PointerBlock::Symbolic(variable) if !crate::kernel::is_load_variable(variable) => true,
        PointerBlock::ExternalArgument
            if matches!(value_type, CType::Int64 | CType::UInt64)
                && assumptions
                    .equality_graph
                    .pointer_is_classed(&pointer.block) =>
        {
            false
        }
        _ => return pointer,
    };
    // Preserve an existing exact cell before choosing coordinates through
    // a proved alias. An unfold may have named this cell at a model pointer
    // before its body introduced the equality to the C parameter.
    if memory.known_value(&pointer).is_some() {
        return pointer;
    }
    let coordinate = assumptions
        .composition_object_resources
        .memory_address_spelling(&pointer, assumptions);
    // An uncached footprint only supplies coordinates for a model pointer.
    // External pointers keep their own spelling unless a cell was found.
    if model_pointer {
        coordinate.unwrap_or(pointer)
    } else {
        coordinate
            .filter(|spelling| memory.known_value(spelling).is_some())
            .unwrap_or(pointer)
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum LoadPurpose {
    Program,
    VolatileProgram,
    Logical,
    Validity,
}

fn has_pending_reallocation_for_pointer(memory: &CMemory, pointer: &Pointer) -> bool {
    memory
        .heap
        .pending_reallocations
        .values()
        .any(|pending| pending.old_pointer.block == pointer.block)
}

/// The shared load evaluator behind both entry points above.
///
/// `branches_on_unresolved_aliases` decides what an alias this load cannot
/// decide does: split the load into the two cases a C execution would have to
/// choose between, or leave the load term unresolved.
///
/// A C read is a step of the program. It observes one of those cases, and the
/// execution carries that case's condition with it, so it must branch. A
/// specification read is not a step: it denotes the value the named snapshot
/// holds, and the load term over that snapshot already *is* that value.
/// Leaving the term unresolved is therefore sound wherever splitting was —
/// each case's value equals the load term under that case's condition, so the
/// term is what the cases agree on, and it asserts strictly less than either of
/// them. It is also the only correct answer under a binder: a fold body is
/// evaluated once for every item of its range at once, and "this item aliases
/// the cell the program just wrote" is not a fact about any particular item.
///
/// Each undecided cell splits off its aliasing case and leaves the distinct
/// case, the same load over the memory without that cell, to the next turn
/// of this loop. The cases are the ones a recursion per cell produced, in
/// the same order, on one stack frame.
#[allow(clippy::too_many_arguments)]
fn evaluate_c_memory_load_paths_with_alias_cache(
    memory: &CMemory,
    pointer: Pointer,
    value_type: CType,
    facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
    has_external_read_resource: bool,
    purpose: LoadPurpose,
    alias_cache: &mut MemoryLoadAliasCache,
    source: Option<&LoadSourceId>,
    byte_order: Option<ByteOrder>,
) -> Vec<CExpressionPath> {
    let mut distinct_case = None;
    let mut paths = evaluate_c_memory_load_case(
        memory,
        memory,
        pointer.clone(),
        value_type,
        facts,
        obligations,
        assumptions,
        has_external_read_resource,
        purpose,
        alias_cache,
        source,
        byte_order,
        true,
        &mut distinct_case,
    );
    // The fact set a transported case reads under, kept in place while its
    // id scope is entered: the scope registers its address.
    let mut case_assumptions: Option<PureFactContext> = None;
    // A distinct case's memory is hypothetical: it drops the undecided cell
    // (and its initialization mark) only to name the load's value over the
    // state without it. Whether the bytes the load reads were written is a
    // question about the memory the program holds, which still holds the
    // cell, so every case asks it of the memory the load was read at.
    let original_memory = memory;
    while let Some(case) = distinct_case.take() {
        let DistinctLoadCase {
            memory,
            facts,
            obligations,
            assumptions: transported,
        } = case;
        if transported.is_some() {
            case_assumptions = transported;
        }
        let _case_assumptions_id_scope = case_assumptions
            .as_ref()
            .map(PureFactContext::enter_id_scope);
        // A memory of many undecided cells yields a case per cell, and each
        // carries every earlier case's distinctness facts. Past the budget the
        // remaining case stops splitting: its load term over the memory it
        // reached is the value every further case agrees on, so it stands for
        // them soundly while the pending limit fails the step.
        let splits = !crate::kernel::assumptions::reasoning_interrupted();
        paths.extend(evaluate_c_memory_load_case(
            &memory,
            original_memory,
            pointer.clone(),
            value_type,
            facts,
            obligations,
            case_assumptions.as_ref().unwrap_or(assumptions),
            has_external_read_resource,
            purpose,
            alias_cache,
            source,
            byte_order,
            splits,
            &mut distinct_case,
        ));
    }
    paths
}

/// The case of a load an undecided cell leaves once its aliasing case is
/// split off: the load over `memory`, which no longer holds that cell, under
/// the case's facts, and under `assumptions` when a transport built a fact
/// set of its own for the load (otherwise the one the load was read under).
struct DistinctLoadCase {
    memory: CMemory,
    facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
    assumptions: Option<PureFactContext>,
}

/// One turn of [`evaluate_c_memory_load_paths_with_alias_cache`]: the paths
/// this memory decides, with the distinct case of an undecided cell left in
/// `distinct_case` for the caller. `written` is the memory the load was read
/// at, which every uninitialized-read check asks: `memory` may be a distinct
/// case's, without cells the program wrote.
#[allow(clippy::too_many_arguments)]
fn evaluate_c_memory_load_case(
    memory: &CMemory,
    written: &CMemory,
    pointer: Pointer,
    value_type: CType,
    facts: ExecutionFacts,
    mut obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
    has_external_read_resource: bool,
    purpose: LoadPurpose,
    alias_cache: &mut MemoryLoadAliasCache,
    source: Option<&LoadSourceId>,
    byte_order: Option<ByteOrder>,
    splits: bool,
    distinct_case: &mut Option<DistinctLoadCase>,
) -> Vec<CExpressionPath> {
    let branches_on_unresolved_aliases =
        splits && matches!(purpose, LoadPurpose::Program | LoadPurpose::VolatileProgram);
    let use_symbolic_pointer_identity =
        should_use_symbolic_pointer_identity(memory, &pointer, value_type);
    let mut facts = facts;
    if purpose != LoadPurpose::Logical && memory.is_ended_local_address(&pointer) {
        return vec![CExpressionPath {
            outcome: CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::InvalidMemory),
            facts,
            obligations,
        }];
    }
    // Transport is the exception, not the rule: most loads add no condition
    // fact and must keep reasoning against the *caller's* fact set object.
    // The memo identity of a fact set is the ambient scope its address was
    // registered under (`PureFactContextIdScope`), so cloning it
    // unconditionally handed every query below a fact set no scope names, and
    // the whole load — including the cell scans — then ran memo-cold. Build a
    // new context only when a transport actually lands, and register that one
    // in its own scope.
    let mut load_assumptions: Option<PureFactContext> = None;
    let candidates = if assumptions.should_transport_memory_load_condition_facts() {
        {
            assumptions
                .exact_memory_load_condition_candidates(&pointer)
                .map(|(condition, value)| Proposition::ConditionIs(condition.clone(), value))
                .collect::<Vec<_>>()
        }
    } else {
        Default::default()
    };
    for source in candidates {
        let Some(theorem) = prove_c_condition_fact_transport(&source, memory, assumptions) else {
            continue;
        };
        let Some(target) =
            c_condition_fact_transport_target_in_context(&theorem, &source, assumptions)
        else {
            continue;
        };
        if target == &source {
            continue;
        }
        let target = target.clone();
        let base = load_assumptions
            .take()
            .unwrap_or_else(|| assumptions.clone());
        load_assumptions = Some(base.assume_proposition(target.clone()));
        let transported = ExecutionPureFact::certified_transport(source, target, theorem);
        if !facts.contains(&transported) {
            facts.push(transported);
        }
    }
    let _load_assumptions_id_scope = load_assumptions
        .as_ref()
        .map(PureFactContext::enter_id_scope);
    // Borrowing the transported context here also freezes it, which is what
    // keeps the scope's registered address describing this exact fact set.
    let assumptions = load_assumptions.as_ref().unwrap_or(assumptions);
    // Construction storage remains unwritten under other possible pointer
    // spellings. Authority alone cannot enable the external-memory shortcut;
    // let ordinary alias resolution find actual writes first.
    let allow_symbolic_external_load = has_external_read_resource
        && (!memory.may_read_uninitialized_object(&pointer, value_type.byte_width())
            || purpose == LoadPurpose::Logical
            || written.has_initialized_bytes_under(&pointer, value_type.byte_width(), assumptions)
            || assumptions.has_memory_read_defined_evidence(memory, &pointer, value_type));
    // A typed union overlay is the authoritative view for an exact typed
    // load, including in provenance-sensitive symbolic-load mode. Selecting
    // the raw load first would reinterpret a copied pointer member as an
    // integer and discard its provenance.
    if let Some(value) = memory.known_union_value(&pointer, value_type) {
        if value_type.accepts(&value) {
            return vec![CExpressionPath {
                outcome: CExpressionOutcome::Value(value),
                facts,
                obligations,
            }];
        }
        return vec![CExpressionPath {
            outcome: CExpressionOutcome::RuntimeError(CRuntimeError::LoadTypeMismatch {
                pointer: pointer.clone(),
                value_type,
                stored: None,
            }),
            facts,
            obligations,
        }];
    }

    // Provenance-sensitive lowering asks for the load identity even when this
    // snapshot has already materialized the cell's concrete value. Checking
    // `known_value` first would collapse `at(mark, field == 11)` to `true` and
    // erase the address needed for later frame transport.
    if allow_symbolic_external_load && assumptions.should_force_symbolic_external_loads() {
        let Some(value) = canonicalized_symbolic_load_value_with_identity(
            memory,
            &pointer,
            value_type,
            &mut facts,
            assumptions,
            use_symbolic_pointer_identity,
            source,
            purpose,
        ) else {
            return vec![CExpressionPath {
                outcome: CExpressionOutcome::RuntimeError(CRuntimeError::LoadTypeMismatch {
                    pointer: pointer.clone(),
                    value_type,
                    stored: None,
                }),
                facts,
                obligations,
            }];
        };
        return vec![CExpressionPath {
            outcome: CExpressionOutcome::Value(value),
            facts,
            obligations,
        }];
    }

    // A pointer-typed load of a materialized int32 cell that is not a bare
    // load term (for example a call-havoc variable standing for the framed
    // field) cannot be reinterpreted as a stable pointer form. When the
    // caller permits symbolic external loads, fall through to the symbolic
    // load below — its load-term form relates across snapshots — instead
    // of failing the load.
    let pointer_cell_defers_to_symbolic = |value: &CValue| {
        (matches!(value, CValue::Int32(_))
            || (matches!(value_type, CType::FunctionPointer(_))
                && matches!(
                    value,
                    CValue::Int8(_)
                        | CValue::Int16(_)
                        | CValue::UInt8(_)
                        | CValue::UInt16(_)
                        | CValue::UInt32(_)
                        | CValue::Int64(_)
                        | CValue::UInt64(_)
                )))
            && value_type.is_pointer()
            && has_external_read_resource
            && (assumptions.should_prefer_symbolic_external_loads()
                || matches!(value_type, CType::FunctionPointer(_)))
    };
    // A one-byte C load inside a wider integer cell, including at the cell's
    // own address, reads that cell's little-endian representation. It is
    // decided here, before the exact lookup (whose wider cell would not fit
    // the load) and the whole-memory scan below, by a bounded lookup in the
    // load's own block; a load with no byte view falls through unchanged.
    if value_type.byte_width() == 1
        && let Some(cell) = containing_integer_cell(memory, &pointer, byte_order)
    {
        let outcome = match byte_view_load_value(&cell, value_type) {
            Some(value) => CExpressionOutcome::Value(value),
            None => CExpressionOutcome::RuntimeError(CRuntimeError::LoadTypeMismatch {
                pointer: pointer.clone(),
                value_type,
                stored: None,
            }),
        };
        return vec![CExpressionPath {
            outcome,
            facts,
            obligations,
        }];
    }
    // An exact materialized cell is already the authoritative value for this
    // non-union pointer. Avoid proving every other symbolic cell distinct
    // before the direct map lookup.
    if let Some(value) = memory.known_value(&pointer) {
        if let Some(value) = canonicalized_pointer_value_from_int_cell(
            memory,
            &pointer,
            &value,
            value_type,
            &mut facts,
            assumptions,
            source,
            purpose,
        ) {
            return vec![CExpressionPath {
                outcome: CExpressionOutcome::Value(value),
                facts,
                obligations,
            }];
        }
        if let Some(value) = value_type.read_cell(&value) {
            return vec![CExpressionPath {
                outcome: CExpressionOutcome::Value(value),
                facts,
                obligations,
            }];
        }
        if !pointer_cell_defers_to_symbolic(&value) {
            return vec![CExpressionPath {
                outcome: CExpressionOutcome::RuntimeError(CRuntimeError::LoadTypeMismatch {
                    pointer: pointer.clone(),
                    value_type,
                    stored: None,
                }),
                facts,
                obligations,
            }];
        }
    } else if let Some(value) = crate::instrumentation::measure_operation(
        "kernel",
        "memory load",
        "memory load: equal-cell scan",
        || {
            // A cell in a block proven distinct from the load's is never
            // resolution-equal to it, so only the candidates can match, and
            // they are visited in the whole map's order.
            let candidates = AliasCandidates::of_block(&pointer.block);
            let normalized = std::cell::OnceCell::new();
            let (found, visited) = memory.cells.find_candidate_by(
                &candidates,
                |stored_pointer, _| {
                    let equal = alias_cache.resolution_equal(&pointer, stored_pointer, assumptions);
                    // A bounded equality query can retain an alias guard before its
                    // nested separation search reaches a compact resource composition.
                    // Recheck separation at the top-level query before treating that
                    // materialized cell as authoritative. If both hold, the alias guard
                    // describes an unreachable branch and must not manufacture a typed
                    // load from the disjoint cell.
                    equal && !alias_cache.resolution_distinct(&pointer, stored_pointer, assumptions)
                },
                |run| {
                    crate::kernel::reasoning::memory_resolution::run_slots_equal_to_load(
                        run,
                        &pointer,
                        &normalized,
                        assumptions,
                    )
                },
            );
            crate::instrumentation::record_deterministic_work(visited);
            found
        },
    ) {
        if let Some(value) = canonicalized_pointer_value_from_int_cell(
            memory,
            &pointer,
            &value,
            value_type,
            &mut facts,
            assumptions,
            source,
            purpose,
        ) {
            return vec![CExpressionPath {
                outcome: CExpressionOutcome::Value(value),
                facts,
                obligations,
            }];
        }
        if let Some(value) = value_type.read_cell(&value) {
            return vec![CExpressionPath {
                outcome: CExpressionOutcome::Value(value),
                facts,
                obligations,
            }];
        }
        if !pointer_cell_defers_to_symbolic(&value) {
            return vec![CExpressionPath {
                outcome: CExpressionOutcome::RuntimeError(CRuntimeError::LoadTypeMismatch {
                    pointer: pointer.clone(),
                    value_type,
                    stored: None,
                }),
                facts,
                obligations,
            }];
        }
    }

    // Unlike external argument memory, a fresh heap block has a known
    // initialization history. Permission authorizes a read but cannot turn a
    // never-written heap cell into an unconstrained initialized value.
    if purpose != LoadPurpose::Logical
        && memory.is_uninitialized_heap_address(&pointer, value_type.byte_width(), assumptions)
        && !written.has_initialized_bytes_under(&pointer, value_type.byte_width(), assumptions)
        && !assumptions.has_memory_read_defined_evidence(memory, &pointer, value_type)
    {
        return vec![CExpressionPath {
            outcome: CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::UninitializedRead),
            facts,
            obligations,
        }];
    }

    if purpose != LoadPurpose::Logical && memory.is_deallocated_heap_address(&pointer, assumptions)
    {
        return vec![CExpressionPath {
            outcome: CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::InvalidMemory),
            facts,
            obligations,
        }];
    }

    if allow_symbolic_external_load && assumptions.should_prefer_symbolic_external_loads() {
        let Some(value) = canonicalized_symbolic_load_value_with_identity(
            memory,
            &pointer,
            value_type,
            &mut facts,
            assumptions,
            use_symbolic_pointer_identity,
            source,
            purpose,
        ) else {
            return vec![CExpressionPath {
                outcome: CExpressionOutcome::RuntimeError(CRuntimeError::LoadTypeMismatch {
                    pointer: pointer.clone(),
                    value_type,
                    stored: None,
                }),
                facts,
                obligations,
            }];
        };
        return vec![CExpressionPath {
            outcome: CExpressionOutcome::Value(value),
            facts,
            obligations,
        }];
    }

    let mut memory = memory.clone();
    // The access width belongs to the snapshot the load is read at, not only
    // to the projection of it that the term ends up carrying. Recording it
    // here as well as inside `symbolic_load_value` is what lets a later
    // caller holding the unreduced snapshot ask how many bytes this load
    // reads instead of assuming the widest scalar.
    record_load_access_width(&memory, &pointer, value_type.byte_width());
    let reduction_base = Some(crate::kernel::primitives::intern_derivation_base(
        &mut memory,
    ));
    let cells_before_reduction = memory.cells.len();
    let load_bytes = value_type.byte_width();
    crate::instrumentation::measure_operation(
        "kernel",
        "memory load",
        "memory load: distinct-cell reduction",
        || {
            // Every cell in a block proven distinct from the load's is dropped
            // by this rule (its address is distinct on the first rung and its
            // bytes are `Separate`), so the reduced map is exactly the
            // candidates the rule keeps, built without visiting the rest.
            let candidates = AliasCandidates::of_block(&pointer.block);
            let mut reduced = (*memory.cells).clone();
            let normalized = std::cell::OnceCell::new();
            let visited = reduced.retain_only_candidates_by(
                &candidates,
                |stored_pointer, stored_value| {
                    // Dropping a cell names this load at a snapshot that no longer
                    // records it, so the question is the same byte question
                    // `1a3b2701` put in front of the three snapshot comparisons:
                    // `p + 1` is a different address from `p` under every test the
                    // kernel has while holding the second byte a four-byte read
                    // there returns. The address ladder decides it only where the
                    // bytes it establishes clear both accesses.
                    !(alias_cache.resolution_distinct(&pointer, stored_pointer, assumptions)
                        && access_byte_overlap(
                            stored_pointer,
                            cell_access_byte_width(stored_value),
                            &pointer,
                            load_bytes,
                            assumptions,
                        ) == AccessByteOverlap::Separate)
                },
                |run| {
                    crate::kernel::reasoning::memory_resolution::run_slots_kept_by_load_reduction(
                        run,
                        &pointer,
                        &normalized,
                        load_bytes,
                        assumptions,
                    )
                },
            );
            crate::instrumentation::record_deterministic_work(visited);
            if reduced.len() != cells_before_reduction {
                memory.cells = std::sync::Arc::new(reduced);
            }
        },
    );
    // The returned symbolic load carries the reduced memory snapshot, so
    // other queries must relate it back to its source. Dropping cells
    // provably distinct from the loaded pointer is a no-op for this load,
    // which is exactly the `CellsForgotten` edge; without it the derivation
    // walk dead-ends at this variant.
    //
    // The reduction choice may depend on `assumptions`, and the reduced map
    // may therefore re-intern as a snapshot older than `reduction_base`.
    // That spelling is sound but deliberately gains no fact-free derivation
    // edge: `record_c_memory_derivation` refuses the backwards edge below.
    // The load judgment remains scoped to this exact assumption context.
    // Ordinary execution retains those facts on its path; an exhaustive
    // structural join can retain the value only when both checked arms reach
    // the same state; and an interface join re-lowers every exported fact in
    // both concrete arms and again at the fact-free successor. Thus an older
    // name is not authority to reuse the reduction in a sibling context.
    // `MemoryLoadAliasCache`'s assumption fingerprint is load-bearing for the
    // same reason. The regression below exercises one cache first under a
    // distinct fact (and observes the ancestor name), then under an aliasing
    // fact (and observes the later stored value).
    if let Some(base) = reduction_base
        && memory.cells.len() != cells_before_reduction
    {
        record_c_memory_derivation(&mut memory, CMemoryDerivation::CellsForgotten { base });
    }

    if pointer.has_symbolic_block() && allow_symbolic_external_load {
        let Some(value) = canonicalized_symbolic_load_value_with_identity(
            &memory,
            &pointer,
            value_type,
            &mut facts,
            assumptions,
            use_symbolic_pointer_identity,
            source,
            purpose,
        ) else {
            return vec![CExpressionPath {
                outcome: CExpressionOutcome::RuntimeError(CRuntimeError::LoadTypeMismatch {
                    pointer: pointer.clone(),
                    value_type,
                    stored: None,
                }),
                facts,
                obligations,
            }];
        };
        return vec![CExpressionPath {
            outcome: CExpressionOutcome::Value(value),
            facts,
            obligations,
        }];
    }

    // A symbolic index into a run of seeded cells reads the run's slot at
    // that index, whichever slot it is. When the facts place every value of
    // the index on live slots, the value is the run's own load at the
    // index: each slot holds the load of its address in the run's source,
    // and the pointer is one of those addresses. Asking slot by slot instead
    // split the load once per element, recursively, which overflowed the
    // stack for a file-scope array of a thousand elements.
    if let Some(value) = symbolic_index_run_load(
        &memory,
        &pointer,
        value_type,
        &mut facts,
        assumptions,
        use_symbolic_pointer_identity,
        source,
        purpose,
    ) {
        return vec![CExpressionPath {
            outcome: CExpressionOutcome::Value(value),
            facts,
            obligations,
        }];
    }
    // A run the load indexes symbolically is never split slot by slot. Its
    // slots are one family of cells the facts did not place the index on; a
    // case per slot would only enumerate the array, and the load term over
    // this snapshot is already the value every such case agrees on.
    let symbolically_indexed_runs = memory
        .cells
        .candidate_runs(&AliasCandidates::of_block(&pointer.block))
        .filter(|run| {
            matches!(
                crate::kernel::reasoning::memory_resolution::run_access(run, &pointer),
                crate::kernel::reasoning::memory_resolution::RunAccess::Scaled { .. }
            )
        })
        .cloned()
        .collect::<Vec<_>>();
    let in_symbolically_indexed_run = |stored_pointer: &Pointer| {
        symbolically_indexed_runs
            .iter()
            .any(|run| run.live_slot_index(stored_pointer).is_some())
    };
    // A load that does not split has nothing to learn from an undecided
    // alias, so it does not pay for the scan that looks for one either.
    let unresolved = branches_on_unresolved_aliases
        .then(|| {
            crate::instrumentation::measure_operation(
                "kernel",
                "memory load",
                "memory load: unresolved-cell scan",
                || {
                    // The reduction above left only candidate cells (see
                    // `AliasCandidates`), so this scan is already local.
                    crate::instrumentation::record_deterministic_work(memory.cells.len());
                    memory
                        .cells
                        .iter()
                        .find_map(|(stored_pointer, stored_value)| {
                            (stored_pointer != &pointer
                                && !in_symbolically_indexed_run(stored_pointer)
                                && !alias_cache.resolution_distinct(
                                    &pointer,
                                    stored_pointer,
                                    assumptions,
                                )
                                && !alias_cache.resolution_equal(
                                    &pointer,
                                    stored_pointer,
                                    assumptions,
                                ))
                            .then(|| (stored_pointer.clone(), stored_value.clone()))
                        })
                },
            )
        })
        .flatten();
    if let Some((stored_pointer, stored_value)) = unresolved {
        let mut paths = Vec::new();
        let stored_bytes = cell_access_byte_width(&stored_value);
        // General equality can resolve an indexed address that the narrower
        // memory resolver leaves open. A proven alias supplies this cell's
        // value; merely skipping its alias branch would lose an initialized
        // cell and eventually report an uninitialized read.
        let known_equal = !assumptions.should_defer_non_exact_condition_reasoning()
            && alias_cache.equal(&pointer, &stored_pointer, assumptions);

        let mut equal_facts = facts.clone();
        if known_equal
            || add_pointer_offset_equality_execution_pure_facts(
                &mut equal_facts,
                assumptions,
                pointer.offset.clone(),
                stored_pointer.offset.clone(),
                true,
            )
            .is_some()
        {
            let equal_outcome = if let Some(value) = canonicalized_pointer_value_from_int_cell(
                &memory,
                &pointer,
                &stored_value,
                value_type,
                &mut facts,
                assumptions,
                source,
                purpose,
            ) {
                CExpressionOutcome::Value(value)
            } else if let Some(value) = value_type.read_cell(&stored_value) {
                CExpressionOutcome::Value(value)
            } else {
                CExpressionOutcome::RuntimeError(CRuntimeError::LoadTypeMismatch {
                    pointer: pointer.clone(),
                    value_type,
                    stored: None,
                })
            };
            paths.push(CExpressionPath {
                outcome: equal_outcome,
                facts: equal_facts,
                obligations: obligations.clone(),
            });
        }
        if known_equal {
            return paths;
        }

        let mut distinct_facts = facts;
        if add_pointer_offset_equality_execution_pure_facts(
            &mut distinct_facts,
            assumptions,
            pointer.offset.clone(),
            stored_pointer.offset.clone(),
            false,
        )
        .is_some()
        {
            // Two different addresses clear each other's bytes only when the
            // gap the inequality establishes is wide enough for both
            // accesses: two `int32` slots of one array, not a byte cell at
            // `p + 5` against the `int32` at `p + 4k`, which overlap at
            // `k == 1` although the addresses differ. Dropping the cell
            // would let a zeroed allocation answer that load as zero.
            let bytes_clear = access_byte_overlap(
                &stored_pointer,
                stored_bytes,
                &pointer,
                value_type.byte_width(),
                assumptions,
            ) == AccessByteOverlap::Separate;
            if bytes_clear {
                // The distinct case is this same load over the memory without
                // that cell. The caller's loop evaluates it next, so a memory
                // with many undecided cells costs one frame, not one per cell.
                *distinct_case = Some(DistinctLoadCase {
                    memory: memory.without_cell(&stored_pointer),
                    facts: distinct_facts,
                    obligations,
                    assumptions: load_assumptions.clone(),
                });
            } else {
                // The cell may still hold some of the loaded bytes, so the
                // load's value is its load over this snapshot, which keeps
                // the cell, and no further case is split from it.
                let outcome = match canonicalized_symbolic_load_value_with_identity(
                    &memory,
                    &pointer,
                    value_type,
                    &mut distinct_facts,
                    assumptions,
                    use_symbolic_pointer_identity,
                    source,
                    purpose,
                ) {
                    Some(value) => CExpressionOutcome::Value(value),
                    None => CExpressionOutcome::RuntimeError(CRuntimeError::LoadTypeMismatch {
                        pointer: pointer.clone(),
                        value_type,
                        stored: None,
                    }),
                };
                paths.push(CExpressionPath {
                    outcome,
                    facts: distinct_facts,
                    obligations,
                });
            }
        }

        return paths;
    }

    if memory.is_zeroed_heap_address(&pointer, value_type.byte_width(), assumptions) {
        let value = match value_type {
            CType::Int8 => int8(Bitvector32Term::Constant(0)),
            CType::Int16 => int16(Bitvector32Term::Constant(0)),
            CType::Int32 => int32(Bitvector32Term::Constant(0)),
            CType::UInt8 => uint8(Bitvector32Term::Constant(0)),
            CType::UInt16 => uint16(Bitvector32Term::Constant(0)),
            CType::UInt32 => CValue::UInt32(Bitvector32Term::Constant(0)),
            CType::Int64 => CValue::Int64(Bitvector32Term::Int64Constant(0)),
            CType::UInt64 => CValue::UInt64(Bitvector32Term::UInt64Constant(0)),
            CType::Int128 => match crate::kernel::c_int128_literal(0) {
                CExpression::Value(value) => value,
                _ => unreachable!("wide literal is a value"),
            },
            CType::UInt128 => match crate::kernel::c_uint128_literal(0) {
                CExpression::Value(value) => value,
                _ => unreachable!("wide literal is a value"),
            },
            CType::Float32 => CValue::Float32(Bitvector32Term::Constant(0)),
            CType::Float64 => CValue::Float64(Bitvector32Term::UInt64Constant(0)),
            _ if value_type.is_pointer() => CValue::typed_pointer(Pointer::null(), value_type),
            _ => {
                return vec![CExpressionPath {
                    outcome: CExpressionOutcome::RuntimeError(CRuntimeError::LoadTypeMismatch {
                        pointer: pointer.clone(),
                        value_type,
                        stored: None,
                    }),
                    facts,
                    obligations,
                }];
            }
        };
        return vec![CExpressionPath {
            outcome: CExpressionOutcome::Value(value),
            facts,
            obligations,
        }];
    }

    if memory.is_loadable_concretely(&pointer, value_type.byte_width()) {
        if let Some(value) = cell_value_recorded_on_path(
            &memory,
            &pointer,
            value_type,
            &mut facts,
            assumptions,
            source,
            purpose,
        ) {
            return vec![CExpressionPath {
                outcome: CExpressionOutcome::Value(value),
                facts,
                obligations,
            }];
        }
        let Some(value) = canonicalized_symbolic_load_value_with_identity(
            &memory,
            &pointer,
            value_type,
            &mut facts,
            assumptions,
            use_symbolic_pointer_identity,
            source,
            purpose,
        ) else {
            return vec![CExpressionPath {
                outcome: CExpressionOutcome::RuntimeError(CRuntimeError::LoadTypeMismatch {
                    pointer: pointer.clone(),
                    value_type,
                    stored: None,
                }),
                facts,
                obligations,
            }];
        };
        return vec![CExpressionPath {
            outcome: CExpressionOutcome::Value(value),
            facts,
            obligations,
        }];
    }

    if purpose != LoadPurpose::Logical && !has_external_read_resource {
        let proposition = Proposition::CMemoryLoadable {
            memory: memory.clone(),
            base: pointer.clone(),
            bytes: Bitvector32Term::Constant(value_type.byte_width()),
            wide: false,
        };
        if purpose == LoadPurpose::Validity {
            if add_proof_obligation(&mut obligations, assumptions, proposition).is_none() {
                return Vec::new();
            }
        } else if assumptions.should_defer_non_exact_loadability_obligations() {
            if !assumptions.proves_memory_loadable_for_memory_resolution(
                &memory,
                &pointer,
                &Bitvector32Term::Constant(value_type.byte_width()),
            ) && !assumptions.proves_exact(&proposition)
                && !obligations
                    .iter()
                    .any(|obligation| obligation.proposition() == &proposition)
            {
                obligations.push(ProofObligation::new(proposition));
            }
        } else if add_proof_obligation(&mut obligations, assumptions, proposition).is_none() {
            return Vec::new();
        }
    }

    // Automatic storage is allocated by a declaration, but allocation alone
    // does not initialize it. Once all possibly-aliasing stored cells have
    // been considered above, a local load with no matching cell is an
    // uninitialized read rather than an unconstrained value — unless the
    // bytes it may read were written, by the initialization record or the
    // cells of the memory the load was read at: a store the facts could not
    // place, a havoc or a join forgot the cell's value, never that it was
    // written, and a distinct case dropped a written cell only to name the
    // value; the load then reads an unknown initialized value below. A
    // symbolic offset must not bypass this check: allocation bounds are
    // independent of whether the addressed element has ever been written.
    // The check follows the loadability obligation, which the refused path
    // keeps as a premise: a read that may leave the object is refused for
    // its bound first, and only a read inside it for unwritten bytes.
    if purpose != LoadPurpose::Logical
        && ((pointer.block.is_local_block() && memory.has_block(&pointer.block))
            || memory.may_read_uninitialized_object(&pointer, value_type.byte_width()))
        && !written.has_initialized_bytes_under(&pointer, value_type.byte_width(), assumptions)
        && !assumptions.has_memory_read_defined_evidence(&memory, &pointer, value_type)
    {
        return vec![CExpressionPath {
            outcome: CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::UninitializedRead),
            facts,
            obligations,
        }];
    }

    if let Some(value) = cell_value_recorded_on_path(
        &memory,
        &pointer,
        value_type,
        &mut facts,
        assumptions,
        source,
        purpose,
    ) {
        return vec![CExpressionPath {
            outcome: CExpressionOutcome::Value(value),
            facts,
            obligations,
        }];
    }

    let Some(value) = canonicalized_symbolic_load_value_with_identity(
        &memory,
        &pointer,
        value_type,
        &mut facts,
        assumptions,
        use_symbolic_pointer_identity,
        source,
        purpose,
    ) else {
        return vec![CExpressionPath {
            outcome: CExpressionOutcome::RuntimeError(CRuntimeError::LoadTypeMismatch {
                pointer: pointer.clone(),
                value_type,
                stored: None,
            }),
            facts,
            obligations,
        }];
    };

    vec![CExpressionPath {
        outcome: CExpressionOutcome::Value(value),
        facts,
        obligations,
    }]
}

/// The value a C read finds for its cell in the recorded history on this
/// path, when no cached cell of `memory` answers it.
///
/// This is the cached-cell read above, asked one snapshot further back: a
/// store at an address the facts could not place when it ran drops the cells
/// it may write, and a path that later learns the store missed this cell
/// (`u != 0` for `buf[u] = 7` and a read of `buf[0]`) reads the value the
/// cell held before it. The answer depends on the path's facts exactly as the
/// distinct-cell reduction above does, and like it is spent only on this
/// path's value; nothing is named by it. Only a program read asks: a
/// specification read denotes the named snapshot's value, and a volatile one
/// may observe a write no recorded step made.
fn cell_value_recorded_on_path(
    memory: &CMemory,
    pointer: &Pointer,
    value_type: CType,
    facts: &mut ExecutionFacts,
    assumptions: &PureFactContext,
    source: Option<&LoadSourceId>,
    purpose: LoadPurpose,
) -> Option<CValue> {
    if purpose != LoadPurpose::Program {
        return None;
    }
    let value = crate::kernel::resource_tracker::cell_value_on_path(
        &crate::kernel::intern_c_memory_ref(memory),
        pointer,
        value_type.byte_width(),
        assumptions,
    )?;
    if let Some(value) = canonicalized_pointer_value_from_int_cell(
        memory,
        pointer,
        &value,
        value_type,
        facts,
        assumptions,
        source,
        purpose,
    ) {
        return Some(value);
    }
    value_type.read_cell(&value)
}

/// Reinterprets an int cell's loaded value as a pointer without letting the
/// load enter the offset: a loaded index never enters a pointer offset as a
/// `MemoryLoad` term. The loaded value is bound to a fresh verification
/// variable whose defining equation joins the path's fact stream, so the
/// offset arithmetic downstream works over a small term and the snapshot
/// stays proof-side, consulted only through the defining fact.
fn canonicalized_pointer_value_from_int_cell(
    memory: &CMemory,
    pointer: &Pointer,
    value: &CValue,
    value_type: CType,
    facts: &mut ExecutionFacts,
    assumptions: &PureFactContext,
    source: Option<&LoadSourceId>,
    purpose: LoadPurpose,
) -> Option<CValue> {
    let pointee_byte_width = value_type.pointee_type()?.byte_width();
    let fresh = match value {
        CValue::Int8(bits) => {
            let unsigned @ Bitvector32Term::MemoryLoad(_, _, _) = bits.signed_byte_operand()?
            else {
                return None;
            };
            let fresh = mint_load_variable(unsigned, facts, assumptions, source)?;
            return Some(CValue::Int8(Bitvector32Term::signed_byte(
                Bitvector32Term::Variable(fresh),
            )));
        }
        CValue::Int16(bits @ Bitvector32Term::MemoryLoad(_, _, _)) => {
            let fresh = mint_load_variable(bits, facts, assumptions, source)?;
            return Some(CValue::Int16(Bitvector32Term::Variable(fresh)));
        }
        CValue::Int32(bits @ Bitvector32Term::MemoryLoad(_, _, _)) => {
            load_variable_for_term(bits)?.0
        }
        // A cell materialized with its load variable (canonicalizing at
        // creation) already carries the variable; record its defining fact
        // in this path's stream, as minting would have.
        CValue::Int32(Bitvector32Term::Variable(variable)) if is_load_variable(variable) => {
            *variable
        }
        _ => return None,
    };
    // The selected cached value already names its defining read. An address
    // alias may spell that cell with a different symbolic storage block; it
    // must not rebase the same pointer value onto that caller spelling.
    let defining_load = registered_load_term_for_variable(&fresh);
    let defining_block = match &defining_load {
        Some(Bitvector32Term::MemoryLoad(_, address, _)) => &address.block,
        _ => &pointer.block,
    };
    // A load variable names the pointer value, not an offset in the
    // storage object containing it. Fresh storage provenance must not
    // manufacture disjointness from the actual pointee.
    let loaded = if matches!(
        defining_block,
        PointerBlock::Heap(_) | PointerBlock::Temporary(_)
    ) || defining_block.is_local_block()
    {
        Pointer::symbolic(fresh)
    } else {
        Pointer::loaded(
            defining_block.clone(),
            Bitvector32Term::Variable(fresh),
            i64::from(pointee_byte_width),
        )
    };
    let result = CPointerValue::from_read(
        loaded.clone(),
        value_type,
        &crate::kernel::intern_c_memory_ref(memory),
        pointer,
    );
    // A scalar cache can name the numeric prefix of a pointer whose complete
    // value is still present in the recorded memory. Select that whole value
    // inside the typed read producer; never infer its bounds from the prefix
    // or publish the known pointer as an unconditional name for one cell.
    if let Some(stored) = crate::kernel::memory_provenance::complete_pointer_read_value(
        result.designation(),
        assumptions,
    ) {
        return Some(CValue::Pointer(stored.with_type(value_type)));
    }
    if let Some(load) = defining_load {
        if (matches!(purpose, LoadPurpose::Logical | LoadPurpose::Validity)
            || purpose == LoadPurpose::Program && SpecificationReadScope::is_active())
            && let Bitvector32Term::MemoryLoad(memory, address, _) = &load
        {
            assumptions.register_pointer_read(&loaded, memory, address);
        }
        // The cached scalar spelling still comes from this exact typed read.
        // Preserve the same producer evidence as the symbolic load route,
        // recording each source observation once.
        record_load_variable_defining_fact_with_source_and_pointer(
            fresh,
            load,
            facts,
            source,
            (purpose == LoadPurpose::Program).then_some(&loaded),
        );
    }
    Some(CValue::Pointer(result))
}

fn should_use_symbolic_pointer_identity(
    memory: &CMemory,
    pointer: &Pointer,
    value_type: CType,
) -> bool {
    // A pointer in heap, temporary, or local storage may target any object.
    // Its storage block supplies no provenance for the loaded value, including
    // after loop havoc (which need not be a call-memory havoc).
    // After a call-havoc edge, an unknown pointer-sized cell may contain the
    // address of any live object, including an automatic local. Give that
    // value an opaque identity instead of deriving a fresh offset in the
    // cell's storage block; equality facts can then resolve a dereference to
    // the object it actually aliases.
    let pointer_sized_load = matches!(
        &pointer.offset,
        PointerOffsetTerm::Int32Scaled { byte_width: 8, .. }
            | PointerOffsetTerm::Int64Scaled { byte_width: 8, .. }
    );
    (matches!(
        pointer.block,
        PointerBlock::Heap(_) | PointerBlock::Temporary(_)
    ) || pointer.block.is_local_block()
        || (memory.has_call_memory_havoc() && pointer_sized_load))
        && value_type.is_pointer()
        && memory.known_union_value(pointer, value_type).is_none()
        && memory.known_value(pointer).is_none()
}

/// The value of a load at `pointer` that indexes a run of `memory`
/// symbolically, when the facts place every value of the index on the run's
/// live slots: the load of `pointer` in the run's source, which is what the
/// slot at each such index holds, or a constant run's one value.
///
/// The access must step by the run's element width from a slot boundary and
/// read the run's own element type. Every index the facts' interval admits
/// must be a live slot, so no hole, whose cell may hold a later store or
/// nothing at all, is read through the source. A live slot is the only cell
/// at its address (a store makes a hole of every slot it may meet), which is
/// the same rule that lets the equal-cell scan take an exact slot's value.
/// `None` sends the load on to the ordinary scans.
#[allow(clippy::too_many_arguments)]
fn symbolic_index_run_load(
    memory: &CMemory,
    pointer: &Pointer,
    value_type: CType,
    facts: &mut ExecutionFacts,
    assumptions: &PureFactContext,
    use_symbolic_identity: bool,
    source: Option<&LoadSourceId>,
    purpose: LoadPurpose,
) -> Option<CValue> {
    use crate::kernel::reasoning::memory_resolution::{RunAccess, run_access};
    let run = memory
        .cells
        .candidate_runs(&AliasCandidates::of_block(&pointer.block))
        .find(|run| {
            crate::instrumentation::record_deterministic_work(1);
            let (index, scale, shift, wide) = match run_access(run, pointer) {
                RunAccess::Scaled {
                    index,
                    scale,
                    shift,
                } => (index, scale, shift, false),
                RunAccess::ScaledWide {
                    index,
                    scale,
                    shift,
                } => (index, scale, shift, true),
                _ => return false,
            };
            let width = i64::from(run.element_width());
            if run.element_type() != value_type
                || width == 0
                || scale != width
                || shift.rem_euclid(width) != 0
            {
                return false;
            }
            let first_element = shift.div_euclid(width);
            // An unsigned 64-bit index starts at zero, so its slots begin at
            // `first_element`; they all lie in one live interval when the
            // index is decided below that interval's remaining length.
            if wide {
                let Ok(first) = u32::try_from(first_element) else {
                    return false;
                };
                return run
                    .live_intervals()
                    .intervals()
                    .iter()
                    .any(|(live_low, live_high)| {
                        *live_low <= first
                            && first < *live_high
                            && *live_high <= run.count()
                            && assumptions.decide(&ConditionTerm::uint64_less_than(
                                index.clone(),
                                Bitvector32Term::UInt64Constant(u64::from(*live_high - first)),
                            )) == Some(true)
                    });
            }
            let Some((low, high)) = assumptions.signed_interval_past_exclusions(&index) else {
                return false;
            };
            let (Some(first), Some(last)) = (
                low.checked_add(first_element),
                high.checked_add(first_element),
            ) else {
                return false;
            };
            let (Ok(first), Ok(last)) = (u32::try_from(first), u32::try_from(last)) else {
                return false;
            };
            last < run.count()
                && run
                    .live_intervals()
                    .intervals()
                    .iter()
                    .any(|(live_low, live_high)| *live_low <= first && last < *live_high)
        })?
        .clone();
    // A constant run's slots are not loads of its source, which is empty:
    // every live slot holds the run's one value, so the load reads it.
    if let crate::kernel::primitives::RunValueMode::Constant(value) = run.value_mode() {
        return value_type.read_cell(value);
    }
    canonicalized_symbolic_load_value_with_identity(
        run.source().memory(),
        pointer,
        value_type,
        facts,
        assumptions,
        use_symbolic_identity,
        source,
        purpose,
    )
}

fn complete_loaded_word(value: CValue, memory: &CMemory, address: &Pointer) -> CValue {
    if !WordRepresentationScope::keeps_representation() {
        return match value {
            CValue::PointerInteger(record) => *record.numeric,
            value => value,
        };
    }
    if !matches!(value, CValue::Int64(_) | CValue::UInt64(_)) {
        return value;
    }
    let bits = crate::kernel::spec::c_value_bitvector_term(&value).expect("LP64 word");
    let pointer = CPointerValue::from_read(
        Pointer::integer_address(bits),
        CType::VoidPointer,
        &crate::kernel::intern_c_memory_ref(memory),
        address,
    );
    CValue::PointerInteger(PointerIntegerValue {
        numeric: Box::new(value),
        pointer: Box::new(pointer),
        kind: PointerIntegerKind::Word { changed_bits: 0 },
    })
}

fn canonicalized_symbolic_load_value_with_identity(
    memory: &CMemory,
    pointer: &Pointer,
    value_type: CType,
    facts: &mut ExecutionFacts,
    assumptions: &PureFactContext,
    use_symbolic_identity: bool,
    source: Option<&LoadSourceId>,
    purpose: LoadPurpose,
) -> Option<CValue> {
    // C and logical reads must name the same typed value through a checked
    // opaque address alias. Only the symbolic value's coordinates change:
    // C access validity still checks the original pointer and its provenance.
    let address = logical_memory_load_address(memory, pointer.clone(), value_type, assumptions);
    // Only a complete stored word supplies a representation record. Numeric
    // equalities between loads are not a source of complete C values.
    if let Some(value @ CValue::PointerInteger(_)) = memory.known_value(&address)
        && value_type.accepts(&value)
    {
        return Some(complete_loaded_word(value, memory, &address));
    }
    if WordRepresentationScope::keeps_representation()
        && matches!(value_type, CType::Int64 | CType::UInt64)
        && let Some(value @ CValue::PointerInteger(_)) =
            crate::kernel::memory_provenance::complete_pointer_carrier_read_value(
                &Pointer::loaded_value(&crate::kernel::intern_c_memory_ref(memory), &address),
                assumptions,
            )
        && value_type.accepts(&value)
    {
        return Some(complete_loaded_word(value, memory, &address));
    }
    // Canonical address selection can expose a materialized pointer cell that
    // the original spelling did not name. Reuse its complete stored value;
    // manufacturing another read here would discard the selected designation.
    if let Some(value @ CValue::Pointer(_)) = memory.known_value(&address)
        && value_type.accepts(&value)
    {
        let CValue::Pointer(stored) = &value else {
            unreachable!()
        };
        facts.push(ExecutionPureFact::logical_read_equation(
            stored.clone(),
            Pointer::loaded_value(&crate::kernel::intern_c_memory_ref(memory), &address),
        ));
        return Some(value);
    }
    let value = symbolic_load_value(memory, &address, value_type)?;
    // Terms are canonical at creation: an int or byte load evaluates to its
    // load variable, with the defining fact beside it, so every fact,
    // offset, and range built from the value is canonical.
    match &value {
        // A signed byte read names the byte's unsigned read.
        CValue::Int8(bits) => {
            if let Some(unsigned @ Bitvector32Term::MemoryLoad(_, _, _)) =
                bits.signed_byte_operand()
            {
                let fresh = mint_load_variable(unsigned, facts, assumptions, source)?;
                return Some(CValue::Int8(Bitvector32Term::signed_byte(
                    Bitvector32Term::Variable(fresh),
                )));
            }
        }
        CValue::Int16(bits @ Bitvector32Term::MemoryLoad(_, _, _)) => {
            let fresh = mint_load_variable(bits, facts, assumptions, source)?;
            return Some(CValue::Int16(Bitvector32Term::Variable(fresh)));
        }
        CValue::Int32(bits @ Bitvector32Term::MemoryLoad(_, _, _)) => {
            let fresh = mint_load_variable(bits, facts, assumptions, source)?;
            return Some(CValue::Int32(Bitvector32Term::Variable(fresh)));
        }
        CValue::UInt8(bits @ Bitvector32Term::MemoryLoad(_, _, _)) => {
            let fresh = mint_load_variable(bits, facts, assumptions, source)?;
            return Some(CValue::UInt8(Bitvector32Term::Variable(fresh)));
        }
        CValue::UInt16(bits @ Bitvector32Term::MemoryLoad(_, _, _)) => {
            let fresh = mint_load_variable(bits, facts, assumptions, source)?;
            return Some(CValue::UInt16(Bitvector32Term::Variable(fresh)));
        }
        // The wider integer scalars name their loads for the same reason.
        // Adoption is atomic across producers: contract lowering already
        // materializes a `uint32`, `int64`, or `uint64` cell with
        // `canonical_form_of_load`, so leaving execution's load of the same
        // cell unnamed would split one value into two terms that only
        // the snapshot could reconnect — and a snapshot the execution has
        // since written cannot. A resource body fact about a `uint64` cell
        // (the rbtree's packed parent word) then survives a write to a
        // sibling cell of the same node, which the fold after that write
        // needs.
        CValue::UInt32(bits @ Bitvector32Term::MemoryLoad(_, _, _)) => {
            let fresh = mint_load_variable(bits, facts, assumptions, source)?;
            return Some(CValue::UInt32(Bitvector32Term::Variable(fresh)));
        }
        CValue::Int64(bits @ Bitvector32Term::MemoryLoad(_, _, _)) => {
            let fresh = mint_load_variable(bits, facts, assumptions, source)?;
            return Some(complete_loaded_word(
                CValue::Int64(Bitvector32Term::Variable(fresh)),
                memory,
                &address,
            ));
        }
        CValue::UInt64(bits @ Bitvector32Term::MemoryLoad(_, _, _)) => {
            let fresh = mint_load_variable(bits, facts, assumptions, source)?;
            return Some(complete_loaded_word(
                CValue::UInt64(Bitvector32Term::Variable(fresh)),
                memory,
                &address,
            ));
        }
        CValue::Int128(bits @ Bitvector32Term::MemoryLoad(_, _, _)) => {
            let fresh = mint_load_variable(bits, facts, assumptions, source)?;
            return Some(CValue::Int128(Bitvector32Term::Variable(fresh)));
        }
        CValue::UInt128(bits @ Bitvector32Term::MemoryLoad(_, _, _)) => {
            let fresh = mint_load_variable(bits, facts, assumptions, source)?;
            return Some(CValue::UInt128(Bitvector32Term::Variable(fresh)));
        }
        _ => {}
    }
    let CValue::Pointer(pointer_value) = &value else {
        return Some(complete_loaded_word(value, memory, &address));
    };
    // Losing a scalar cache does not lose a complete pointer stored in the
    // selected memory history. Return that whole value before minting another
    // numeric read coordinate, preserving its bounds and object class.
    let complete_read = CPointerValue::from_read(
        pointer_value.pointer().clone(),
        value_type,
        &crate::kernel::intern_c_memory_ref(memory),
        &address,
    );
    if let Some(stored) = crate::kernel::memory_provenance::complete_pointer_read_value(
        complete_read.designation(),
        assumptions,
    ) {
        let stored = stored.with_type(value_type);
        facts.push(ExecutionPureFact::logical_read_equation(
            stored.clone(),
            Pointer::loaded_value(&crate::kernel::intern_c_memory_ref(memory), &address),
        ));
        return Some(CValue::Pointer(stored));
    }
    let Some((block, bits, byte_width)) = pointer_value.pointer().as_loaded() else {
        return Some(value);
    };
    if !matches!(bits, Bitvector32Term::MemoryLoad(_, _, _)) {
        return Some(value);
    }
    let (fresh, load) = load_variable_for_term(bits)?;
    let pointer = if use_symbolic_identity {
        Pointer::symbolic(fresh)
    } else {
        Pointer::loaded(block.clone(), Bitvector32Term::Variable(fresh), byte_width)
    };
    if matches!(purpose, LoadPurpose::Logical | LoadPurpose::Validity)
        || purpose == LoadPurpose::Program && SpecificationReadScope::is_active()
    {
        record_pointer_read_observation(&pointer, memory, &address);
        // The logical evaluator constructs a term, not a C access. Retain
        // its exact typed definition in the trusted graph's term metadata;
        // logical evaluation still exports no defining proposition premise.
        if let Bitvector32Term::MemoryLoad(memory, address, _) = &load {
            assumptions.register_pointer_read(&pointer, memory, address);
        }
    }
    record_load_variable_defining_fact_with_source_and_pointer(
        fresh,
        load,
        facts,
        source,
        (purpose == LoadPurpose::Program).then_some(&pointer),
    );
    Some(CValue::Pointer(CPointerValue::from_read(
        pointer,
        value_type,
        &crate::kernel::intern_c_memory_ref(memory),
        &address,
    )))
}

const LOAD_VARIABLE_BASE: u64 = 1 << 40;
const LOAD_VARIABLE_RANGE_SIZE: u64 = 1 << 40;
#[allow(
    dead_code,
    reason = "the typed load producer migrates after this identity foundation"
)]
const POINTER_LOAD_ID_RANGE: u64 = 1 << 40;

/// The most load identities one verification session may mint. The registry
/// is the only guard against two distinct loads sharing an id (the defining
/// equations `Var(id) == load(memory, pointer)` circulate as ambient truths),
/// so it must never forget an entry mid-session; exhausting it is a loud
/// verifier failure, never a silent clear.
const LOAD_VARIABLE_REGISTRY_CAPACITY: usize = 1_000_000;

#[cfg(test)]
thread_local! {
    static LOAD_VARIABLE_REGISTRY_CAPACITY_OVERRIDE: std::cell::Cell<Option<usize>> =
        const { std::cell::Cell::new(None) };
}

/// A cheap candidate filter for a pointer that may be an exact typed read.
/// Its shape is not itself evidence: indexed arithmetic can look identical.
pub(crate) fn typed_pointer_read_variable(value: &Pointer) -> Option<Variable> {
    Some(match (&value.block, &value.offset) {
        (
            PointerBlock::Symbolic(variable) | PointerBlock::FunctionSymbolic(variable),
            PointerOffsetTerm::Constant(0),
        ) => *variable,
        (_, PointerOffsetTerm::Int32Scaled { value, .. }) => {
            let Bitvector32Term::Variable(variable) = value.as_ref() else {
                return None;
            };
            *variable
        }
        _ => return None,
    })
}

fn load_variable_registry_capacity() -> usize {
    #[cfg(test)]
    if let Some(capacity) = LOAD_VARIABLE_REGISTRY_CAPACITY_OVERRIDE.with(|cell| cell.get()) {
        return capacity;
    }
    LOAD_VARIABLE_REGISTRY_CAPACITY
}

#[cfg(test)]
thread_local! {
    static LOAD_VARIABLE_RANGE_OVERRIDE: std::cell::Cell<Option<u64>> =
        const { std::cell::Cell::new(None) };
}

/// How many ids the load-variable space offers to the probe in
/// `mint_load_variable_identity`. The real range dwarfs the capacity, so a
/// collision is rare; a test narrows it to make every hash collide.
fn load_variable_range() -> u64 {
    #[cfg(test)]
    if let Some(range) = LOAD_VARIABLE_RANGE_OVERRIDE.with(|cell| cell.get()) {
        return range;
    }
    LOAD_VARIABLE_RANGE_SIZE
}

/// Runs `body` with only the first `range` load-variable ids available, so
/// distinct loads collide at the hash and a test can watch the probe.
#[cfg(test)]
pub(crate) fn with_load_variable_range<T>(range: u64, body: impl FnOnce() -> T) -> T {
    assert!(range > 0 && range <= LOAD_VARIABLE_RANGE_SIZE);
    let previous = LOAD_VARIABLE_RANGE_OVERRIDE.with(|cell| cell.replace(Some(range)));
    let result = body();
    LOAD_VARIABLE_RANGE_OVERRIDE.with(|cell| cell.set(previous));
    result
}

/// Runs `body` with the registry capacity lowered so a test can reach it.
#[cfg(test)]
pub(crate) fn with_load_variable_registry_capacity<T>(
    capacity: usize,
    body: impl FnOnce() -> T,
) -> T {
    let previous =
        LOAD_VARIABLE_REGISTRY_CAPACITY_OVERRIDE.with(|cell| cell.replace(Some(capacity)));
    let result = body();
    LOAD_VARIABLE_REGISTRY_CAPACITY_OVERRIDE.with(|cell| cell.set(previous));
    result
}

#[cfg(test)]
pub(crate) fn load_variable_registry_len() -> usize {
    LOAD_VARIABLE_REGISTRY.with(|registry| registry.borrow().len())
}

/// Whether a kernel variable id lies in the reserved load-variable id space.
/// Structural: no registry consultation, so the answer is deterministic
/// and thread-agnostic.
pub(crate) fn is_load_variable(variable: &Variable) -> bool {
    LOAD_VARIABLE_RANGE.contains(&variable.0)
}

/// Whether a proposition is a load-variable defining equation
/// (`v == load(snapshot, ptr)` for a reserved load variable). Such
/// equations are true by construction, so path wrapping treats them as
/// ambient truths rather than premises.
pub(crate) fn is_load_variable_defining_fact(proposition: &Proposition) -> bool {
    let Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(left, right), true) = proposition
    else {
        return false;
    };
    matches!(
        (left.as_ref(), right.as_ref()),
        (
            Bitvector32Term::Variable(variable),
            Bitvector32Term::MemoryLoad(_, _, _)
        ) if is_load_variable(variable)
    )
}

/// One load variable's registry entry: the load it names, and what the
/// session has learned about it since.
#[derive(Clone)]
struct RegisteredLoad {
    /// The canonical snapshot, address and kind: the load itself.
    memory: SharedCMemory,
    pointer: Pointer,
    kind: LoadKind,
    /// The first-seen live origin, and the origin epoch it was recorded in.
    origin: SharedCMemory,
    epoch: u64,
    /// The widest access width any mint of this name asked for.
    bytes: u32,
}

thread_local! {
    // Latest complete pointer and wide-word reads, indexed by value and
    // function epoch. Observations never change the defining name.
    // Persistent roots keep session capture/restore from copying the table.
    static POINTER_READ_OBSERVATIONS: std::cell::RefCell<
        imbl::HashMap<(u64, Pointer), (SharedCMemory, Pointer)>,
    > = std::cell::RefCell::new(imbl::HashMap::new());
    static WIDE_LOAD_OBSERVATIONS: std::cell::RefCell<
        imbl::HashMap<(u64, Variable), (SharedCMemory, Pointer)>,
    > = std::cell::RefCell::new(imbl::HashMap::new());
    /// Separate pointer-valued load names. The defining key is one canonical
    /// snapshot and address at the fixed eight-byte pointer interpretation;
    /// neither a scalar load variable nor its mutable maximum access width
    /// decides membership in this registry.
    static POINTER_LOAD_REGISTRY: std::cell::RefCell<
        std::collections::HashMap<PointerLoadId, (SharedCMemory, Pointer)>,
    > = std::cell::RefCell::new(std::collections::HashMap::new());
    /// Load variable -> the load it names (canonical memory, pointer, kind),
    /// its first-seen live origin and the origin epoch that origin was
    /// recorded in, and an access width in bytes.
    ///
    /// The kind is part of the name: two reads of one address in one snapshot
    /// that differ in kind are two entries. The width is the framing width a
    /// later caller holding only the name walks with, which covers every
    /// access recorded at the address and so may exceed the kind's own. Mints
    /// that cannot name a width record
    /// [`resource_tracker::widest_scalar_access_bytes`], and a mint that can
    /// widens any narrower width already recorded: one entry stands for every
    /// access that resolved to this name, so it has to cover all of them.
    static LOAD_VARIABLE_REGISTRY: std::cell::RefCell<
        std::collections::HashMap<Variable, RegisteredLoad>,
    > = std::cell::RefCell::new(std::collections::HashMap::new());
    /// The current origin epoch. A load variable's id names one load for the
    /// whole session, but the live snapshot transport resolves through is
    /// first-seen within one verified function: the surface begins a new
    /// epoch per function, and the next mint in a new epoch replaces an
    /// origin recorded under an older one, which belongs to a DAG the
    /// current function's effect snapshots never connect to.
    static LOAD_ORIGIN_EPOCH: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
    static LOAD_VARIABLE_CACHE: std::cell::RefCell<
        std::collections::HashMap<Bitvector32Term, (Variable, Bitvector32Term)>,
    > = std::cell::RefCell::new(std::collections::HashMap::new());
    static TERM_CACHE: std::cell::RefCell<
        std::collections::HashMap<Bitvector32Term, Bitvector32Term>,
    > = std::cell::RefCell::new(std::collections::HashMap::new());
    #[cfg(test)]
    static LOAD_SUBSTITUTION_TERM_VISITS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

#[cfg(test)]
pub(crate) fn reset_load_substitution_term_visits() {
    LOAD_SUBSTITUTION_TERM_VISITS.with(|visits| visits.set(0));
}

#[cfg(test)]
pub(crate) fn load_substitution_term_visits() -> usize {
    LOAD_SUBSTITUTION_TERM_VISITS.with(std::cell::Cell::get)
}

pub(crate) fn clear_load_canonicalization_caches() {
    LOAD_VARIABLE_CACHE.with(|cache| cache.borrow_mut().clear());
    TERM_CACHE.with(|cache| cache.borrow_mut().clear());
}

/// Everything `clear_load_variable_registry` clears, as one value: the load
/// names, their origins, observations and widths, the pointer-load names, and the logical
/// pointer reads. A reusable session captures it once and restores it before
/// each check.
#[derive(Clone)]
pub(crate) struct LoadRegistryState {
    pointer_observations: imbl::HashMap<(u64, Pointer), (SharedCMemory, Pointer)>,
    wide_observations: imbl::HashMap<(u64, Variable), (SharedCMemory, Pointer)>,
    variables: std::collections::HashMap<Variable, RegisteredLoad>,
    pointers: std::collections::HashMap<PointerLoadId, (SharedCMemory, Pointer)>,
    widths: std::collections::HashMap<(SharedCMemory, Pointer), u32>,
    widths_at_address: std::collections::HashMap<Pointer, u32>,
    array_widths: std::collections::BTreeMap<(PointerBlock, i64), SymbolicArrayAccessWidths>,
    origin_epoch: u64,
    logical_pointer_reads: crate::kernel::equality_graph::LogicalPointerReadsState,
}

/// How many load and pointer-load names are registered.
#[cfg(test)]
pub(crate) fn load_registry_entry_count() -> usize {
    LOAD_VARIABLE_REGISTRY.with(|registry| registry.borrow().len())
        + POINTER_LOAD_REGISTRY.with(|registry| registry.borrow().len())
}

pub(crate) fn capture_load_variable_registry() -> LoadRegistryState {
    LoadRegistryState {
        pointer_observations: POINTER_READ_OBSERVATIONS.with(|registry| registry.borrow().clone()),
        wide_observations: WIDE_LOAD_OBSERVATIONS.with(|registry| registry.borrow().clone()),
        variables: LOAD_VARIABLE_REGISTRY.with(|registry| registry.borrow().clone()),
        pointers: POINTER_LOAD_REGISTRY.with(|registry| registry.borrow().clone()),
        widths: LOAD_ACCESS_WIDTH.with(|widths| widths.borrow().clone()),
        widths_at_address: LOAD_ACCESS_WIDTH_AT_ADDRESS.with(|widths| widths.borrow().clone()),
        array_widths: SYMBOLIC_ARRAY_ACCESS_WIDTHS.with(|arrays| arrays.borrow().clone()),
        origin_epoch: LOAD_ORIGIN_EPOCH.with(std::cell::Cell::get),
        logical_pointer_reads: crate::kernel::equality_graph::capture_logical_pointer_reads(),
    }
}

pub(crate) fn restore_load_variable_registry(state: &LoadRegistryState) {
    POINTER_READ_OBSERVATIONS
        .with(|registry| *registry.borrow_mut() = state.pointer_observations.clone());
    WIDE_LOAD_OBSERVATIONS
        .with(|registry| *registry.borrow_mut() = state.wide_observations.clone());
    crate::kernel::equality_graph::restore_logical_pointer_reads(&state.logical_pointer_reads);
    LOAD_VARIABLE_REGISTRY.with(|registry| *registry.borrow_mut() = state.variables.clone());
    POINTER_LOAD_REGISTRY.with(|registry| *registry.borrow_mut() = state.pointers.clone());
    LOAD_ACCESS_WIDTH.with(|widths| *widths.borrow_mut() = state.widths.clone());
    LOAD_ACCESS_WIDTH_AT_ADDRESS
        .with(|widths| *widths.borrow_mut() = state.widths_at_address.clone());
    SYMBOLIC_ARRAY_ACCESS_WIDTHS.with(|arrays| *arrays.borrow_mut() = state.array_widths.clone());
    LOAD_ORIGIN_EPOCH.with(|epoch| epoch.set(state.origin_epoch));
}

pub(crate) fn clear_load_variable_registry() {
    POINTER_READ_OBSERVATIONS.with(|registry| registry.borrow_mut().clear());
    WIDE_LOAD_OBSERVATIONS.with(|registry| registry.borrow_mut().clear());
    crate::kernel::equality_graph::clear_logical_pointer_reads();
    LOAD_VARIABLE_REGISTRY.with(|registry| registry.borrow_mut().clear());
    POINTER_LOAD_REGISTRY.with(|registry| registry.borrow_mut().clear());
    // Access widths are scoped to the verification that observed them. A
    // `local:` address is spelled the same in the next function, so a width
    // left behind would answer for an unrelated cell there.
    LOAD_ACCESS_WIDTH.with(|widths| widths.borrow_mut().clear());
    LOAD_ACCESS_WIDTH_AT_ADDRESS.with(|widths| widths.borrow_mut().clear());
    SYMBOLIC_ARRAY_ACCESS_WIDTHS.with(|arrays| arrays.borrow_mut().clear());
    LOAD_ORIGIN_EPOCH.with(|epoch| epoch.set(0));
}

/// Starts a new load-origin epoch: the next mint of any load variable
/// records its live origin afresh, so origins registered while verifying an
/// earlier function do not answer transport in this one. Ids and their
/// canonical loads are untouched.
///
/// The naming caches are per epoch. A cached name is returned without
/// minting, and minting is what refreshes a variable's origin, so a name
/// cached by an earlier function would keep that function's origin: a later
/// function's transport would then walk the earlier function's DAG history,
/// and its proof cost would depend on what was verified before it.
pub(crate) fn begin_load_origin_epoch() {
    LOAD_ORIGIN_EPOCH.with(|epoch| epoch.set(epoch.get() + 1));
    clear_load_canonicalization_caches();
}

/// The load represented by a load variable minted on this thread.
/// Reasoning uses this to consult the snapshot lazily: a load variable in
/// an equality query is viewed as its load exactly where a load term would
/// have triggered provenance evidence.
pub(crate) fn registered_load_for_variable(
    variable: &Variable,
) -> Option<(SharedCMemory, Pointer)> {
    LOAD_VARIABLE_REGISTRY.with(|registry| {
        registry
            .borrow()
            .get(variable)
            .map(|load| (load.memory.clone(), load.pointer.clone()))
    })
}

/// The load term a load variable names, kind included: the right-hand side
/// of its defining equation.
pub(crate) fn registered_load_term_for_variable(variable: &Variable) -> Option<Bitvector32Term> {
    LOAD_VARIABLE_REGISTRY.with(|registry| {
        registry.borrow().get(variable).map(|load| {
            Bitvector32Term::MemoryLoad(
                load.memory.clone(),
                Box::new(load.pointer.clone()),
                load.kind,
            )
        })
    })
}

/// The kind of read a load variable names.
pub(crate) fn registered_load_kind_for_variable(variable: &Variable) -> Option<LoadKind> {
    LOAD_VARIABLE_REGISTRY.with(|registry| registry.borrow().get(variable).map(|load| load.kind))
}

/// Intern an eight-byte pointer load by its assumption-free defining
/// snapshot and address. Hashing only chooses a candidate slot: a collision
/// probes until the full key matches or an unused slot is found.
#[allow(
    dead_code,
    reason = "the typed load producer migrates after this identity foundation"
)]
pub(crate) fn pointer_load_identity(memory: &SharedCMemory, address: &Pointer) -> PointerLoadId {
    use std::hash::{Hash, Hasher};
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    memory.arena_id().hash(&mut hasher);
    address.hash(&mut hasher);
    let mut slot = hasher.finish() % POINTER_LOAD_ID_RANGE;
    POINTER_LOAD_REGISTRY.with(|registry| {
        let mut registry = registry.borrow_mut();
        loop {
            let identity = PointerLoadId(slot);
            match registry.get(&identity) {
                Some((known_memory, known_address))
                    if known_memory.arena_id() == memory.arena_id() && known_address == address =>
                {
                    return identity;
                }
                Some(_) => {
                    crate::instrumentation::record_deterministic_work(1);
                    slot = (slot + 1) % POINTER_LOAD_ID_RANGE;
                }
                None => {
                    assert!(
                        registry.len() < LOAD_VARIABLE_REGISTRY_CAPACITY,
                        "pointer-load registry capacity exhausted"
                    );
                    registry.insert(identity, (memory.clone(), address.clone()));
                    return identity;
                }
            }
        }
    })
}

/// Decode a pointer-load name without consulting scalar-load metadata.
pub(crate) fn registered_pointer_load(identity: PointerLoadId) -> Option<(SharedCMemory, Pointer)> {
    POINTER_LOAD_REGISTRY.with(|registry| registry.borrow().get(&identity).cloned())
}

thread_local! {
    /// `(snapshot, address)` -> how many bytes the C load there reads.
    ///
    /// A `MemoryLoad` term carries its own read's kind, but one address may
    /// be read at several widths, and a framing walk about the address has to
    /// cover all of them; without this a caller has to assume the widest
    /// scalar, and an `int32` load stops being separable from a store four
    /// bytes away. The entry is written by [`symbolic_load_value`], the one
    /// typed entry point every C load passes through, before any naming can
    /// happen.
    static LOAD_ACCESS_WIDTH: std::cell::RefCell<
        std::collections::HashMap<(SharedCMemory, Pointer), u32>,
    > = std::cell::RefCell::new(std::collections::HashMap::new());

    /// `address` -> the widest C load seen at it, in any snapshot.
    ///
    /// How wide the access at an address is comes from the C type being
    /// loaded, which does not vary with the snapshot. The exact key above is
    /// still preferred, because it answers for one particular load; this one
    /// answers for a walk that reached the address through a snapshot no
    /// typed load was ever performed at, which is every framing walk that
    /// starts at a later snapshot than the load it is carrying.
    ///
    /// Widening on conflict, so a `char` view and a `long` view of one
    /// address answer with the `long`: over-stating a width can only shrink
    /// the separated set.
    static LOAD_ACCESS_WIDTH_AT_ADDRESS: std::cell::RefCell<
        std::collections::HashMap<Pointer, u32>,
    > = std::cell::RefCell::new(std::collections::HashMap::new());
}

/// The element widths a symbolic static array declared for all of its
/// elements at once, in place of one [`record_load_access_width`] per
/// element: see [`declare_symbolic_array_access_widths`].
#[derive(Clone)]
struct SymbolicArrayAccessWidths {
    /// The snapshot every element's load reads.
    source: SharedCMemory,
    /// The byte distance between elements.
    stride: i64,
    count: u32,
    /// The loads of one element: each one's byte offset within the element,
    /// ascending and below `stride`, and its width. A scalar array's element
    /// is one load at offset 0; an array of structs has one per field.
    loads: std::sync::Arc<[(i64, u32)]>,
}

impl SymbolicArrayAccessWidths {
    /// The byte just past the last element's last load's first byte, for an
    /// array based at `base`.
    fn end(&self, base: i64) -> i64 {
        base.saturating_add(
            i64::from(self.count)
                .saturating_sub(1)
                .saturating_mul(self.stride),
        )
        .saturating_add(self.loads.last().map_or(0, |(offset, _)| *offset))
        .saturating_add(1)
    }

    /// The width of the load at `offset` bytes past the array's base, when
    /// one of its elements' loads is there.
    fn width_at(&self, base: i64, offset: i64) -> Option<u32> {
        if offset < base || offset >= self.end(base) {
            return None;
        }
        let within = (offset - base) % self.stride;
        self.loads
            .binary_search_by_key(&within, |(offset, _)| *offset)
            .ok()
            .map(|position| self.loads[position].1)
    }
}

thread_local! {
    /// The symbolic static arrays whose element widths are declared rather
    /// than recorded one element at a time, by block and constant base
    /// offset. No two overlap, so a constant pointer is an element of at most
    /// the one based nearest below it. Every reader of the two width tables
    /// reads a declared element as the entry the per-element record would
    /// have made, so the answers are that record's. Cleared with the tables.
    static SYMBOLIC_ARRAY_ACCESS_WIDTHS: std::cell::RefCell<
        std::collections::BTreeMap<(PointerBlock, i64), SymbolicArrayAccessWidths>,
    > = const { std::cell::RefCell::new(std::collections::BTreeMap::new()) };
}

/// The declared array element spelled exactly `pointer` (a constant offset in
/// the array's block, as the element's own load spells it): the snapshot its
/// load reads, and its width.
fn declared_array_access_width(pointer: &Pointer) -> Option<(SharedCMemory, u32)> {
    let PointerOffsetTerm::Constant(offset) = pointer.offset else {
        return None;
    };
    SYMBOLIC_ARRAY_ACCESS_WIDTHS.with(|arrays| {
        let arrays = arrays.borrow();
        if arrays.is_empty() {
            return None;
        }
        let ((block, base), array) = arrays
            .range(..=(pointer.block.clone(), offset))
            .next_back()?;
        if *block != pointer.block {
            return None;
        }
        array
            .width_at(*base, offset)
            .map(|bytes| (array.source.clone(), bytes))
    })
}

/// The width the snapshot-keyed record at `(memory, pointer)` would hold for
/// a declared array element.
fn declared_exact_access_width(memory: &SharedCMemory, pointer: &Pointer) -> Option<u32> {
    declared_array_access_width(pointer)
        .filter(|(source, _)| source == memory)
        .map(|(_, bytes)| bytes)
}

/// Says that a load of `bytes` bytes happens at every element `base`,
/// `base + stride`, … of a `count`-element array in `source`, exactly as
/// [`symbolic_load_value`] of each element would have recorded it, in work
/// that does not depend on `count`. Only a constant base is declared, and
/// only where no other declared array overlaps the elements; `false`
/// declares nothing, and the caller records the elements one by one.
///
/// Declaring before any element is named keeps every name what it was: the
/// naming reads the width back through [`recorded_load_access_width`], which
/// answers with the declaration.
pub(in crate::kernel) fn declare_symbolic_array_access_widths(
    source: &SharedCMemory,
    base: &Pointer,
    stride: u32,
    count: u32,
    bytes: u32,
) -> bool {
    declare_symbolic_element_access_widths(source, base, stride, count, &[(0, bytes)])
}

/// [`declare_symbolic_array_access_widths`] for an array whose every
/// element is read by several loads, one per `(offset, bytes)` of `loads`
/// (ascending offsets within the element, each below `stride`): an array of
/// structs, whose fields are its elements' loads. `false` declares nothing,
/// as there.
pub(in crate::kernel) fn declare_symbolic_element_access_widths(
    source: &SharedCMemory,
    base: &Pointer,
    stride: u32,
    count: u32,
    loads: &[(u32, u32)],
) -> bool {
    let PointerOffsetTerm::Constant(offset) = base.offset else {
        return false;
    };
    if count == 0
        || stride == 0
        || loads.is_empty()
        || !loads.windows(2).all(|pair| pair[0].0 < pair[1].0)
        || loads.last().is_some_and(|(within, _)| *within >= stride)
    {
        return false;
    }
    let declared = SymbolicArrayAccessWidths {
        source: source.clone(),
        stride: i64::from(stride),
        count,
        loads: loads
            .iter()
            .map(|(within, bytes)| (i64::from(*within), *bytes))
            .collect(),
    };
    let end = declared.end(offset);
    SYMBOLIC_ARRAY_ACCESS_WIDTHS.with(|arrays| {
        let mut arrays = arrays.borrow_mut();
        let key = (base.block.clone(), offset);
        if let Some(held) = arrays.get(&key) {
            // The same array declared again, as every function entry does.
            return held.source == declared.source
                && held.stride == declared.stride
                && held.count == declared.count
                && held.loads == declared.loads;
        }
        let below = arrays
            .range(..&key)
            .next_back()
            .filter(|((block, _), _)| *block == base.block)
            .is_some_and(|((_, held_base), held)| held.end(*held_base) > offset);
        let above = arrays
            .range(&key..)
            .next()
            .filter(|((block, _), _)| *block == base.block)
            .is_some_and(|((_, held_base), _)| *held_base < end);
        if below || above {
            return false;
        }
        arrays.insert(key, declared);
        true
    })
}

/// Remembers that a load of `bytes` bytes happens at this address in this
/// snapshot. Widening on conflict: the entry has to cover every access that
/// resolves through it. A declared array element counts as already recorded
/// at its declared width.
pub(in crate::kernel) fn record_load_access_width(memory: &CMemory, pointer: &Pointer, bytes: u32) {
    let key = (
        crate::kernel::intern_c_memory(memory.clone()),
        pointer.clone(),
    );
    let declared = declared_array_access_width(pointer);
    let declared_exact = declared
        .as_ref()
        .filter(|(source, _)| *source == key.0)
        .map(|(_, bytes)| *bytes);
    let declared_at_address = declared.map(|(_, bytes)| bytes);
    // A recorded width can only ever widen, and a name computed under the
    // narrower one is stale: the epoch walk a narrow access takes crosses
    // stores the wider one stops at, so it names the load at an older
    // snapshot. `LOAD_VARIABLE_CACHE` is keyed by the term alone — a term
    // carries its own kind, not the widest access recorded at its address —
    // so widening has to drop the names that were derived before it.
    // Widening is rare; a name being the answer to a question this
    // table has since changed is not something a later reader can detect.
    let mut widened = false;
    let mut widen = |known: &mut u32| {
        if bytes > *known {
            *known = bytes;
            widened = true;
        }
    };
    LOAD_ACCESS_WIDTH.with(|widths| {
        let mut widths = widths.borrow_mut();
        if widths.len() >= 100_000 {
            widths.clear();
        }
        match widths.get_mut(&key) {
            Some(known) => widen(known),
            None => {
                let mut known = declared_exact.unwrap_or(bytes);
                widen(&mut known);
                widths.insert(key, known);
            }
        }
    });
    LOAD_ACCESS_WIDTH_AT_ADDRESS.with(|widths| {
        let mut widths = widths.borrow_mut();
        if widths.len() >= 100_000 {
            widths.clear();
        }
        match widths.get_mut(pointer) {
            Some(known) => widen(known),
            None => {
                let mut known = declared_at_address.unwrap_or(bytes);
                widen(&mut known);
                widths.insert(pointer.clone(), known);
            }
        }
    });
    if widened {
        LOAD_VARIABLE_CACHE.with(|cache| cache.borrow_mut().clear());
    }
}

/// Says that a load of `bytes` bytes happens at this address, the way
/// [`symbolic_load_value`] says it for a typed C load.
///
/// Kernel tests build `MemoryLoad` terms by hand, without the C load that
/// records its address's width. Without a declaration such an address stands
/// in the widest scalar, which no store four bytes away can be separated
/// from. A test that means "the `int32` at this address" says so here.
#[cfg(test)]
pub(in crate::kernel) fn declare_load_access_width(pointer: &Pointer, bytes: u32) {
    LOAD_ACCESS_WIDTH_AT_ADDRESS.with(|widths| {
        widths
            .borrow_mut()
            .entry(pointer.clone())
            .and_modify(|known| *known = (*known).max(bytes))
            .or_insert_with(|| {
                declared_array_access_width(pointer)
                    .map_or(bytes, |(_, declared)| declared.max(bytes))
            });
    });
}

/// The width of the C load recorded at this address in this snapshot, when
/// one was. `None` means no typed load was seen here, and the caller stands
/// in [`crate::kernel::resource_tracker::widest_scalar_access_bytes`].
pub(crate) fn recorded_load_access_width(memory: &SharedCMemory, pointer: &Pointer) -> Option<u32> {
    LOAD_ACCESS_WIDTH
        .with(|widths| {
            widths
                .borrow()
                .get(&(memory.clone(), pointer.clone()))
                .copied()
        })
        .or_else(|| declared_exact_access_width(memory, pointer))
        .or_else(|| {
            // This snapshot saw no typed load here, but the address still has
            // a width if any snapshot did: the C type at an address does not
            // change with the snapshot a framing walk happens to start from.
            recorded_load_access_width_at_address(pointer)
        })
}

/// The widest C load recorded at this address in any snapshot, a declared
/// array element's included.
fn recorded_load_access_width_at_address(pointer: &Pointer) -> Option<u32> {
    LOAD_ACCESS_WIDTH_AT_ADDRESS
        .with(|widths| widths.borrow().get(pointer).copied())
        .or_else(|| declared_array_access_width(pointer).map(|(_, bytes)| bytes))
}

/// The access width to use for a load named only by a term.
pub(crate) fn load_access_width_or_widest(memory: &SharedCMemory, pointer: &Pointer) -> u32 {
    recorded_load_access_width(memory, pointer)
        .unwrap_or_else(crate::kernel::resource_tracker::widest_scalar_access_bytes)
}

/// The access width a framing walk uses for a `kind` read at this address:
/// the width recorded there, never narrower than the read itself.
pub(crate) fn load_term_access_width(
    memory: &SharedCMemory,
    pointer: &Pointer,
    kind: LoadKind,
) -> u32 {
    recorded_load_access_width(memory, pointer)
        .unwrap_or_else(|| kind.unrecorded_access_byte_width())
        .max(kind.byte_width())
}

/// The widest C load recorded at this address in any snapshot, or the widest
/// scalar when none was seen.
///
/// The snapshot-keyed form above is the precise one and is what a caller
/// holding an interned snapshot asks. This one is for a caller holding a bare
/// `CMemory` it would have to intern only to ask the question, where the C
/// type at the address is the whole answer anyway: every framing comparison
/// runs at a snapshot later than the load it is carrying, so the exact key
/// would miss and fall through to this table regardless.
pub(crate) fn load_access_width_at_address_or_widest(pointer: &Pointer) -> u32 {
    recorded_load_access_width_at_address(pointer)
        .unwrap_or_else(crate::kernel::resource_tracker::widest_scalar_access_bytes)
}

/// How many bytes the access this variable names reads.
///
/// This is the widest access any mint of the name asked for, which can exceed
/// the name's own kind ([`registered_load_kind_for_variable`]) when the
/// address is also read wider. `None` means the variable is not a registered
/// load; a caller that needs a width anyway uses
/// [`crate::kernel::resource_tracker::widest_scalar_access_bytes`].
pub(crate) fn registered_load_bytes_for_variable(variable: &Variable) -> Option<u32> {
    LOAD_VARIABLE_REGISTRY.with(|registry| registry.borrow().get(variable).map(|load| load.bytes))
}

/// The first-seen live snapshot a load variable was minted from in the
/// current origin epoch. The canonical form is a jumped placeholder unsuited
/// to frame checks; transport resolves through this origin, which is
/// DAG-connected and cell-comparable to later effect snapshots of the
/// function that minted it. First-seen is deterministic because mint order
/// is execution order; per-epoch because two functions in one session can
/// mint the same variable from unconnected snapshots.
pub(crate) fn registered_load_origin_for_variable(
    variable: &Variable,
) -> Option<(SharedCMemory, Pointer)> {
    let current_epoch = LOAD_ORIGIN_EPOCH.with(std::cell::Cell::get);
    LOAD_VARIABLE_REGISTRY.with(|registry| {
        registry
            .borrow()
            .get(variable)
            // An origin recorded under an earlier epoch belongs to another
            // function's DAG; it can relate nothing this function executes.
            .filter(|load| load.epoch == current_epoch)
            .map(|load| (load.origin.clone(), load.pointer.clone()))
    })
}

/// [`registered_load_origin_for_variable`] as the load term it names there:
/// the same read, kind included, at the live origin.
pub(crate) fn registered_load_origin_term_for_variable(
    variable: &Variable,
) -> Option<Bitvector32Term> {
    let (origin, pointer) = registered_load_origin_for_variable(variable)?;
    let kind = registered_load_kind_for_variable(variable)?;
    Some(Bitvector32Term::MemoryLoad(origin, Box::new(pointer), kind))
}

/// Whether the pointer a load variable names was obtained before `block`
/// existed, so cannot point into it: a pointer value read at a snapshot
/// cannot hold the address of an object that snapshot does not have.
///
/// The reference is the load's live origin, the state it was first read in,
/// never its canonical memory, which may be a projection that leaves
/// unrelated blocks out. Only local blocks are judged: a local exists from
/// the step that declares it into the snapshot, so a local the origin does
/// not hold, and has not ended, was declared after the read. Heap blocks
/// are not judged, because a heap identity can come from a contract's
/// allocation claim rather than from a snapshot's own blocks.
pub(crate) fn loaded_pointer_predates_block(variable: &Variable, block: &PointerBlock) -> bool {
    if !block.is_local_block() {
        return false;
    }
    let Some((origin, _)) = registered_load_origin_for_variable(variable) else {
        return false;
    };
    !origin.has_block(block) && !origin.forgotten.ended_local_blocks.contains(block)
}

/// Views a term as a memory load for equality reasoning: load terms pass
/// through, and registered load variables resolve to the loads they
/// represent. Other terms are not loads.
pub(crate) fn viewed_as_memory_load(term: &Bitvector32Term) -> Option<Bitvector32Term> {
    match term {
        Bitvector32Term::MemoryLoad(_, _, _) => Some(term.clone()),
        Bitvector32Term::Variable(variable) => registered_load_term_for_variable(variable),
        _ => None,
    }
}

/// Whether a proposition mentions any registered load variable.
/// Cross-effect fact transport uses this to include facts written with load
/// variables in rewriting, exactly as load-term facts are included by
/// mentioning their snapshots.
/// Whether `proposition` names a variable of the load range, registered
/// or not: what [`proposition_mentions_registered_load_variable`] needs
/// before it reads the registry, so a fact this rejects that one rejects at
/// any later time too.
pub(crate) fn proposition_mentions_load_variable(proposition: &Proposition) -> bool {
    let mut variables = std::collections::BTreeSet::new();
    crate::kernel::reasoning::variable_collection::collect_proposition_variables_for_load_presence(
        proposition,
        &mut variables,
    );
    variables.iter().any(is_load_variable)
}

/// The identities load variables are minted from.
pub(crate) const LOAD_VARIABLE_RANGE: std::ops::Range<u64> =
    LOAD_VARIABLE_BASE..LOAD_VARIABLE_BASE + LOAD_VARIABLE_RANGE_SIZE;

pub(crate) fn proposition_mentions_registered_load_variable(proposition: &Proposition) -> bool {
    let mut variables = std::collections::BTreeSet::new();
    crate::kernel::reasoning::variable_collection::collect_proposition_bitvector_variables(
        proposition,
        &mut variables,
    );
    variables.iter().any(|variable| {
        is_load_variable(variable) && registered_load_for_variable(variable).is_some()
    })
}

/// The single canonical form for a term: the deep, assumption-free
/// structural canonicalization ([`canonicalize_atomic_loads`]) followed by
/// load-variable substitution, so every remaining load becomes its load
/// variable. The load variable is the canonical form of its load — a
/// consumer never expands a load variable back into its snapshot-bearing
/// load; the registered defining fact is the only bridge. Equality of
/// canonical forms holds by definition: it needs no proof evidence.
/// Deterministic and idempotent. The traversal is linear and uses explicit
/// worklists. Shallow terms are memoized; deep terms bypass the recursive
/// structural key and take the same complete path directly.
///
/// [`canonicalize_atomic_loads`]: crate::kernel::memory_provenance::canonicalize_atomic_loads
pub(crate) fn canonical_term(term: &Bitvector32Term) -> Bitvector32Term {
    let cacheable = crate::kernel::memory_provenance::term_is_shallow_structural_cache_key(term);
    if cacheable && let Some(hit) = TERM_CACHE.with(|cache| cache.borrow().get(term).cloned()) {
        return hit;
    }
    let structural = crate::kernel::memory_provenance::canonicalize_atomic_loads(term);
    // Register the live observation before its projected form can claim the
    // load's origin. Keep the established projected canonical identity.
    if matches!(term, Bitvector32Term::MemoryLoad(..))
        && matches!(structural, Bitvector32Term::MemoryLoad(..))
    {
        load_variable_for_term(term);
    }
    let result = substitute_load_variables(&structural, &mut None);
    if cacheable {
        TERM_CACHE.with(|cache| {
            let mut cache = cache.borrow_mut();
            if cache.len() >= 100_000 {
                cache.clear();
            }
            cache.insert(term.clone(), result.clone());
        });
    }
    result
}

/// The canonical form for a pointer offset: every scaled index takes its
/// [`canonical_term`] form. The offset analogue of [`canonical_term`].
pub(crate) fn canonical_offset_term(offset: &PointerOffsetTerm) -> PointerOffsetTerm {
    enum Task<'a> {
        Visit(&'a PointerOffsetTerm),
        RebuildAdd,
    }
    let mut tasks = vec![Task::Visit(offset)];
    let mut results = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            Task::Visit(offset) => match offset {
                PointerOffsetTerm::Constant(_) | PointerOffsetTerm::Variable(_) => {
                    results.push(offset.clone())
                }
                PointerOffsetTerm::Add(left, right) => {
                    tasks.push(Task::RebuildAdd);
                    tasks.push(Task::Visit(right));
                    tasks.push(Task::Visit(left));
                }
                PointerOffsetTerm::Int32Scaled { value, byte_width } => {
                    results.push(PointerOffsetTerm::scale_int32(
                        canonical_term(value),
                        *byte_width,
                    ));
                }
                PointerOffsetTerm::Int64Scaled {
                    value,
                    byte_width,
                    unsigned,
                } => results.push(PointerOffsetTerm::scale_int64(
                    canonical_term(value),
                    *byte_width,
                    *unsigned,
                )),
            },
            Task::RebuildAdd => {
                let right = results.pop().expect("visited right offset");
                let left = results.pop().expect("visited left offset");
                results.push(PointerOffsetTerm::add(left, right));
            }
        }
    }
    results.pop().expect("canonicalization produces one offset")
}

/// Gives an index or endpoint term the model's stable representation before
/// it enters pointer-offset or range arithmetic: every load atom is replaced
/// by its load variable and each variable's defining equation joins
/// the fact stream. Every producer that scales an integer term into an
/// offset or evaluates a range endpoint must route the term through this,
/// so a loaded index never enters a `PointerOffsetTerm` or a range bound as
/// a raw `MemoryLoad`. Adoption is atomic across producers: naming one
/// birth site while another emits load terms splits one load identity into
/// two terms that only a proved equality could reconnect.
pub(crate) fn canonicalized_offset_index_term(
    bits: Bitvector32Term,
    facts: &mut ExecutionFacts,
) -> Bitvector32Term {
    if !term_mentions_a_memory_load(&bits) {
        return bits;
    }
    substitute_load_variables(&bits, &mut Some(facts))
}

/// The term for reading `pointer` from `memory` at a creation point with no
/// fact stream (resource materialization, contract evaluation): the load
/// variable. Load variables are content-addressed, so this agrees with
/// every other creation point; the defining fact is available through the
/// registry.
pub(crate) fn canonical_form_of_load(
    memory: SharedCMemory,
    pointer: Pointer,
    kind: LoadKind,
) -> Bitvector32Term {
    // A signed byte read is the conversion of the byte's one unsigned read.
    if kind == LoadKind::Int8 {
        return Bitvector32Term::signed_byte(canonical_form_of_load(
            memory,
            pointer,
            LoadKind::UInt8,
        ));
    }
    let load = Bitvector32Term::MemoryLoad(memory, Box::new(pointer), kind);
    match load_variable_for_term(&load) {
        Some((variable, _)) => Bitvector32Term::Variable(variable),
        None => load,
    }
}

/// The test-only audit of the creation-time invariant (see
/// `docs/internals/canonicalization.md`): while
/// `count_canonical_at_creation_violations` is counting on this thread,
/// every condition fact entering a `PureFactContext` is compared with its
/// canonical form. Each distinct (rewrite kind, creating module) pair is
/// reported once on stderr with an example, where the creating module is
/// the innermost `click::` frame outside the generic context-construction
/// and reasoning layers. Defining facts are exempt: they are the base of
/// the construction. The report is the work list for establishing the
/// invariant at every creation point. Off, this is one thread-local read.
pub(crate) fn check_canonical_at_creation(condition: &ConditionTerm, value: bool) {
    thread_local! {
        static SEEN: std::cell::RefCell<std::collections::BTreeSet<(String, String)>> =
            const { std::cell::RefCell::new(std::collections::BTreeSet::new()) };
    }
    if !CANONICAL_AT_CREATION_VIOLATIONS.with(|count| count.get().is_some()) {
        return;
    }
    let proposition = Proposition::ConditionIs(condition.clone(), value);
    if is_load_variable_defining_fact(&proposition) || is_store_fact(condition, value) {
        return;
    }
    let canonical = canonical_condition(condition);
    if &canonical == condition {
        return;
    }
    CANONICAL_AT_CREATION_VIOLATIONS.with(|count| {
        if let Some(seen) = count.get() {
            count.set(Some(seen + 1));
        }
    });
    let kind = if !condition_mentions_a_memory_load(&canonical) {
        let mut variables = std::collections::BTreeSet::new();
        crate::kernel::reasoning::variable_collection::collect_condition_bitvector_variables(
            &canonical,
            &mut variables,
        );
        if variables.iter().any(is_load_variable) {
            "load -> load variable"
        } else {
            "load -> recorded value"
        }
    } else {
        "load rewritten, still a load"
    };
    const GENERIC: [&str; 12] = [
        "check_canonical_at_creation",
        "assume_condition",
        "assume_proposition",
        "assumptions_from_propositions",
        "assumptions_with_path_context",
        "assumptions_with_propositions",
        "ProofFacts::",
        "atomic_derivation_premises",
        "derive_proposition",
        "::proves",
        "PureFactContext>::",
        "path_facts::",
    ];
    let backtrace = std::backtrace::Backtrace::force_capture().to_string();
    let creator = backtrace
        .lines()
        .filter_map(|line| line.trim().split_once(": ").map(|(_, frame)| frame))
        .find(|frame| {
            frame.starts_with("click::") && !GENERIC.iter().any(|generic| frame.contains(generic))
        })
        .map(|frame| {
            frame
                .split("::{{closure}}")
                .next()
                .unwrap_or(frame)
                .trim_start_matches("click::")
                .to_string()
        })
        .unwrap_or_else(|| "<no click frame>".to_string());
    let first_time = SEEN.with(|seen| {
        seen.borrow_mut()
            .insert((kind.to_string(), creator.clone()))
    });
    if !first_time {
        return;
    }
    let width = 240usize;
    let shown = format!("{condition:?}");
    let shown = &shown[..shown.len().min(width)];
    eprintln!("CANONICAL-AT-CREATION violation [{kind}] created in {creator}\n  example: {shown}");
}

thread_local! {
    /// `Some(n)` while a creation-time invariant audit is counting
    /// violations on this thread; `None` otherwise (the check is off).
    static CANONICAL_AT_CREATION_VIOLATIONS: std::cell::Cell<Option<usize>> =
        const { std::cell::Cell::new(None) };
}

/// Runs `body` with the creation-time invariant check on, returning the
/// body's result and the number of condition facts that entered a
/// `PureFactContext` in a non-canonical form. The standing regression for
/// `docs/internals/canonicalization.md` asserts zero over fixture verification.
#[cfg(test)]
pub(crate) fn count_canonical_at_creation_violations<T>(body: impl FnOnce() -> T) -> (T, usize) {
    let previous = CANONICAL_AT_CREATION_VIOLATIONS.with(|count| count.replace(Some(0)));
    let result = body();
    let violations = CANONICAL_AT_CREATION_VIOLATIONS
        .with(|count| count.replace(previous))
        .unwrap_or(0);
    (result, violations)
}

/// Whether a condition is a store fact `load(after, p) == v` where `after`
/// records `v` at `p`: the memory-content counterpart of a defining fact,
/// exported from a certified store record and cited by certificates through
/// `at(statement(n).exit, ...)`. Like defining facts, store facts are the
/// base the invariant rests on and keep their load term.
pub(crate) fn is_store_fact(condition: &ConditionTerm, value: bool) -> bool {
    if !value {
        return false;
    }
    let ConditionTerm::Bitvector32Equal(left, right) = condition else {
        return false;
    };
    let (load, stored) = match (left.as_ref(), right.as_ref()) {
        (Bitvector32Term::MemoryLoad(memory, pointer, kind), stored)
        | (stored, Bitvector32Term::MemoryLoad(memory, pointer, kind)) => {
            ((memory, pointer, kind), stored)
        }
        _ => return false,
    };
    let Some(value) = load.0.known_value(load.1) else {
        return false;
    };
    load.2.reads_value(&value)
        && matches!(
            value,
            crate::kernel::integer32_c_value!(recorded)
                if &recorded == stored
        )
}

/// The canonical form for a condition: every operand takes its
/// [`canonical_term`] form, so terms that are equal by definition compare
/// identically. The comparison direction of the canonical model for
/// whole facts.
pub(crate) fn canonical_condition(condition: &ConditionTerm) -> ConditionTerm {
    match condition {
        ConditionTerm::Constant(_) | ConditionTerm::Variable(_) => condition.clone(),
        ConditionTerm::AlgebraicEqual(_, _) | ConditionTerm::PointerValueEqual(..) => {
            condition.clone()
        }
        ConditionTerm::Float32(float_condition) => {
            ConditionTerm::Float32(float_condition.map_bitvector_terms(canonical_term))
        }
        ConditionTerm::Float64(float_condition) => {
            ConditionTerm::Float64(float_condition.map_bitvector_terms(canonical_term))
        }
        ConditionTerm::PointerOffsetEqual(left, right) => ConditionTerm::PointerOffsetEqual(
            Box::new(canonical_offset_term(left)),
            Box::new(canonical_offset_term(right)),
        ),
        ConditionTerm::PointerEqual(left, right) => ConditionTerm::PointerEqual(
            Box::new(Pointer {
                block: left.block.clone(),
                offset: canonical_offset_term(&left.offset),
            }),
            Box::new(Pointer {
                block: right.block.clone(),
                offset: canonical_offset_term(&right.offset),
            }),
        ),
        crate::kernel::integer_comparison_condition!(_, _) => condition.clone(),
        condition => {
            let (op, left, right) = condition
                .as_bitvector_comparison()
                .expect("every other condition has its own arm");
            op.build_raw(canonical_term(left), canonical_term(right))
        }
    }
}

/// The canonical form for a condition fact; non-condition propositions pass
/// through unchanged.
pub(crate) fn canonical_condition_fact(fact: &Proposition) -> Proposition {
    let Proposition::ConditionIs(condition, value) = fact else {
        return fact.clone();
    };
    Proposition::ConditionIs(canonical_condition(condition), *value)
}

/// Replaces every load atom in a term with its load variable.
/// When `facts` carries a stream, this is the production mode: each
/// substituted load variable's defining fact joins the stream,
/// deduplicated, so the variable always travels with its defining fact. Binder scopes
/// (`RangeFold` bodies) are left untouched: a load under a fold can mention
/// bound variables, which name no load identity.
fn substitute_load_variables(
    term: &Bitvector32Term,
    facts: &mut Option<&mut ExecutionFacts>,
) -> Bitvector32Term {
    enum Task<'a> {
        VisitTerm(&'a Bitvector32Term),
        VisitCondition(&'a ConditionTerm),
        VisitOffset(&'a PointerOffsetTerm),
        RebuildBinary(BitvectorBinaryOp),
        RebuildUnary(BitvectorUnaryOp),
        RebuildIf,
        RebuildPureFunction {
            name: String,
            argument_count: usize,
        },
        RebuildConditionBinary(BitvectorComparisonOp),
        RebuildFloatCondition {
            is_float64: bool,
            condition: CFloatCondition,
            term_count: usize,
        },
        RebuildPointerOffsetEqual,
        RebuildPointerEqual {
            left_block: PointerBlock,
            right_block: PointerBlock,
        },
        RebuildOffsetAdd,
        RebuildInt32Scaled(i64),
        RebuildInt64Scaled {
            byte_width: i64,
            unsigned: bool,
        },
    }

    let mut tasks = vec![Task::VisitTerm(term)];
    let mut term_results = Vec::new();
    let mut condition_results = Vec::new();
    let mut offset_results = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            Task::VisitTerm(term) => {
                #[cfg(test)]
                LOAD_SUBSTITUTION_TERM_VISITS.with(|visits| visits.set(visits.get() + 1));
                match term {
                    Bitvector32Term::Constant(_)
                    | Bitvector32Term::Variable(_)
                    | Bitvector32Term::Int64Constant(_)
                    | Bitvector32Term::UInt64Constant(_)
                    | Bitvector32Term::MachineIntegerConstant(_) => term_results.push(term.clone()),
                    Bitvector32Term::MemoryLoad(_, _, _) => match load_variable_for_term(term) {
                        Some((variable, load)) => {
                            if let Some(facts) = facts.as_deref_mut() {
                                record_load_variable_defining_fact(variable, load, facts);
                            }
                            term_results.push(Bitvector32Term::Variable(variable));
                        }
                        None => term_results.push(term.clone()),
                    },
                    Bitvector32Term::PointerAddress(_, _)
                    | Bitvector32Term::IntegerToMachine { .. } => term_results.push(term.clone()),
                    Bitvector32Term::ClickFunctionApplication { .. }
                    | Bitvector32Term::AlgebraicMatch { .. } => term_results.push(term.clone()),
                    Bitvector32Term::If {
                        condition,
                        then_term,
                        else_term,
                    } => {
                        tasks.push(Task::RebuildIf);
                        tasks.push(Task::VisitTerm(else_term));
                        tasks.push(Task::VisitTerm(then_term));
                        tasks.push(Task::VisitCondition(condition));
                    }
                    // A fold is a binder boundary: loads in its body can mention
                    // bound variables and therefore do not have a global load
                    // identity. Preserve the whole scoped term verbatim.
                    Bitvector32Term::RangeFold { .. } => term_results.push(term.clone()),
                    Bitvector32Term::PureFunctionApplication { name, arguments } => {
                        tasks.push(Task::RebuildPureFunction {
                            name: name.clone(),
                            argument_count: arguments.len(),
                        });
                        for argument in arguments.iter().rev() {
                            tasks.push(Task::VisitTerm(argument));
                        }
                    }
                    term => match (term.as_binary(), term.as_unary()) {
                        (Some((op, left, right)), _) => {
                            tasks.push(Task::RebuildBinary(op));
                            tasks.push(Task::VisitTerm(right));
                            tasks.push(Task::VisitTerm(left));
                        }
                        (_, Some((op, value))) => {
                            tasks.push(Task::RebuildUnary(op));
                            tasks.push(Task::VisitTerm(value));
                        }
                        _ => unreachable!("every other variant has its own arm"),
                    },
                }
            }
            Task::VisitCondition(condition) => match condition {
                ConditionTerm::AlgebraicEqual(_, _) | ConditionTerm::PointerValueEqual(..) => {
                    condition_results.push(condition.clone())
                }
                crate::kernel::integer_comparison_condition!(_, _) => {
                    condition_results.push(condition.clone())
                }
                ConditionTerm::Constant(_) | ConditionTerm::Variable(_) => {
                    condition_results.push(condition.clone())
                }
                ConditionTerm::Float32(float_condition) => {
                    let term_count = match float_condition {
                        CFloatCondition::Comparison { .. } => 2,
                        CFloatCondition::Classification { .. } => 1,
                    };
                    tasks.push(Task::RebuildFloatCondition {
                        is_float64: false,
                        condition: float_condition.clone(),
                        term_count,
                    });
                    match float_condition {
                        CFloatCondition::Comparison { left, right, .. } => {
                            tasks.push(Task::VisitTerm(right));
                            tasks.push(Task::VisitTerm(left));
                        }
                        CFloatCondition::Classification { value, .. } => {
                            tasks.push(Task::VisitTerm(value));
                        }
                    }
                }
                ConditionTerm::Float64(float_condition) => {
                    let term_count = match float_condition {
                        CFloatCondition::Comparison { .. } => 2,
                        CFloatCondition::Classification { .. } => 1,
                    };
                    tasks.push(Task::RebuildFloatCondition {
                        is_float64: true,
                        condition: float_condition.clone(),
                        term_count,
                    });
                    match float_condition {
                        CFloatCondition::Comparison { left, right, .. } => {
                            tasks.push(Task::VisitTerm(right));
                            tasks.push(Task::VisitTerm(left));
                        }
                        CFloatCondition::Classification { value, .. } => {
                            tasks.push(Task::VisitTerm(value));
                        }
                    }
                }
                ConditionTerm::PointerOffsetEqual(left, right) => {
                    tasks.push(Task::RebuildPointerOffsetEqual);
                    tasks.push(Task::VisitOffset(right));
                    tasks.push(Task::VisitOffset(left));
                }
                ConditionTerm::PointerEqual(left, right) => {
                    tasks.push(Task::RebuildPointerEqual {
                        left_block: left.block.clone(),
                        right_block: right.block.clone(),
                    });
                    tasks.push(Task::VisitOffset(&right.offset));
                    tasks.push(Task::VisitOffset(&left.offset));
                }
                condition => {
                    let (op, left, right) = condition
                        .as_bitvector_comparison()
                        .expect("every other condition has its own arm");
                    tasks.push(Task::RebuildConditionBinary(op));
                    tasks.push(Task::VisitTerm(right));
                    tasks.push(Task::VisitTerm(left));
                }
            },
            Task::VisitOffset(offset) => match offset {
                PointerOffsetTerm::Constant(_) | PointerOffsetTerm::Variable(_) => {
                    offset_results.push(offset.clone())
                }
                PointerOffsetTerm::Add(left, right) => {
                    tasks.push(Task::RebuildOffsetAdd);
                    tasks.push(Task::VisitOffset(right));
                    tasks.push(Task::VisitOffset(left));
                }
                PointerOffsetTerm::Int32Scaled { value, byte_width } => {
                    tasks.push(Task::RebuildInt32Scaled(*byte_width));
                    tasks.push(Task::VisitTerm(value));
                }
                PointerOffsetTerm::Int64Scaled {
                    value,
                    byte_width,
                    unsigned,
                } => {
                    tasks.push(Task::RebuildInt64Scaled {
                        byte_width: *byte_width,
                        unsigned: *unsigned,
                    });
                    tasks.push(Task::VisitTerm(value));
                }
            },
            // Integer operators and conversions are rebuilt as bare nodes;
            // float operators and the machine cast through their smart
            // constructors.
            Task::RebuildBinary(op) => {
                let right = term_results.pop().expect("visited right term");
                let left = term_results.pop().expect("visited left term");
                term_results.push(if op.is_float() {
                    op.build(left, right)
                } else {
                    op.build_raw(left, right)
                });
            }
            Task::RebuildUnary(op) => {
                let value = term_results.pop().expect("visited unary term");
                let smart =
                    op.is_float() || matches!(op, BitvectorUnaryOp::MachineIntegerCast { .. });
                term_results.push(if smart {
                    op.build(value)
                } else {
                    op.build_raw(value)
                });
            }
            Task::RebuildIf => {
                let else_term = term_results.pop().expect("visited else term");
                let then_term = term_results.pop().expect("visited then term");
                let condition = condition_results.pop().expect("visited condition");
                term_results.push(Bitvector32Term::If {
                    condition: Box::new(condition),
                    then_term: Box::new(then_term),
                    else_term: Box::new(else_term),
                });
            }
            Task::RebuildPureFunction {
                name,
                argument_count,
            } => {
                let first = term_results.len() - argument_count;
                let arguments = term_results.split_off(first);
                term_results.push(Bitvector32Term::PureFunctionApplication { name, arguments });
            }
            Task::RebuildConditionBinary(op) => {
                let right = term_results.pop().expect("visited right condition operand");
                let left = term_results.pop().expect("visited left condition operand");
                condition_results.push(op.build_raw(left, right));
            }
            Task::RebuildFloatCondition {
                is_float64,
                condition,
                term_count,
            } => {
                let first = term_results.len() - term_count;
                let mut index = first;
                let rebuilt = condition.map_bitvector_terms(|_| {
                    let term = term_results[index].clone();
                    index += 1;
                    term
                });
                term_results.truncate(first);
                condition_results.push(if is_float64 {
                    ConditionTerm::Float64(rebuilt)
                } else {
                    ConditionTerm::Float32(rebuilt)
                });
            }
            Task::RebuildPointerOffsetEqual => {
                let right = offset_results.pop().expect("visited right pointer offset");
                let left = offset_results.pop().expect("visited left pointer offset");
                condition_results.push(ConditionTerm::PointerOffsetEqual(
                    Box::new(left),
                    Box::new(right),
                ));
            }
            Task::RebuildPointerEqual {
                left_block,
                right_block,
            } => {
                let right = offset_results.pop().expect("visited right pointer offset");
                let left = offset_results.pop().expect("visited left pointer offset");
                condition_results.push(ConditionTerm::PointerEqual(
                    Box::new(Pointer {
                        block: left_block,
                        offset: left,
                    }),
                    Box::new(Pointer {
                        block: right_block,
                        offset: right,
                    }),
                ));
            }
            Task::RebuildOffsetAdd => {
                let right = offset_results.pop().expect("visited right pointer offset");
                let left = offset_results.pop().expect("visited left pointer offset");
                offset_results.push(PointerOffsetTerm::add(left, right));
            }
            Task::RebuildInt32Scaled(byte_width) => {
                let value = term_results.pop().expect("visited scaled term");
                offset_results.push(PointerOffsetTerm::scale_int32(value, byte_width));
            }
            Task::RebuildInt64Scaled {
                byte_width,
                unsigned,
            } => {
                let value = term_results.pop().expect("visited scaled term");
                offset_results.push(PointerOffsetTerm::scale_int64(value, byte_width, unsigned));
            }
        }
    }
    assert_eq!(term_results.len(), 1, "substitution produces one term");
    assert!(condition_results.is_empty());
    assert!(offset_results.is_empty());
    term_results.pop().unwrap()
}

/// Whether two terms have the same canonical form. Two forms of one value
/// compare equal exactly when their [`canonical_term`] forms are
/// identical. Load-free terms are fixed points of the canonical form, so
/// they compare by identity without a canonicalization walk. Both
/// canonicalization stages are bounded by explicit term size.
pub(crate) fn terms_have_same_canonical_form(
    left: &Bitvector32Term,
    right: &Bitvector32Term,
) -> bool {
    if left == right {
        return true;
    }
    if !term_mentions_a_memory_load(left) && !term_mentions_a_memory_load(right) {
        return false;
    }
    canonical_term(left) == canonical_term(right)
}

/// Whether two pointer offsets have the same canonical form; the offset
/// analogue of [`terms_have_same_canonical_form`].
pub(crate) fn offsets_have_same_canonical_form(
    left: &PointerOffsetTerm,
    right: &PointerOffsetTerm,
) -> bool {
    if left == right {
        return true;
    }
    if !offset_mentions_a_memory_load(left) && !offset_mentions_a_memory_load(right) {
        return false;
    }
    canonical_offset_term(left) == canonical_offset_term(right)
}

/// Whether a term contains any load atom the canonical form could rewrite.
/// Load-free terms are fixed points of [`canonical_term`], which the
/// comparators use to answer load-free mismatches without a walk.
fn term_mentions_a_memory_load(term: &Bitvector32Term) -> bool {
    match term {
        Bitvector32Term::Constant(_)
        | Bitvector32Term::Variable(_)
        | Bitvector32Term::Int64Constant(_)
        | Bitvector32Term::UInt64Constant(_)
        | Bitvector32Term::MachineIntegerConstant(_) => false,
        Bitvector32Term::MemoryLoad(_, _, _) => true,
        Bitvector32Term::PointerAddress(pointer, _) => {
            pointer.offset.any_scaled_value(term_mentions_a_memory_load)
        }
        Bitvector32Term::If {
            condition,
            then_term,
            else_term,
        } => {
            condition_mentions_a_memory_load(condition)
                || term_mentions_a_memory_load(then_term)
                || term_mentions_a_memory_load(else_term)
        }
        // The structural stage canonicalizes inside fold bodies even though
        // name substitution stops at the binder, so a fold may still change
        // under the canonical form.
        Bitvector32Term::RangeFold { .. } => true,
        Bitvector32Term::PureFunctionApplication { name: _, arguments } => {
            arguments.iter().any(term_mentions_a_memory_load)
        }
        Bitvector32Term::ClickFunctionApplication { .. } => true,
        Bitvector32Term::AlgebraicMatch { arms, .. } => arms
            .iter()
            .any(|arm| term_mentions_a_memory_load(&arm.body)),
        Bitvector32Term::IntegerToMachine { .. } => true,
        term => {
            if let Some((_, left, right)) = term.as_binary() {
                term_mentions_a_memory_load(left) || term_mentions_a_memory_load(right)
            } else {
                let (_, value) = term
                    .as_unary()
                    .expect("every other term is binary or unary");
                term_mentions_a_memory_load(value)
            }
        }
    }
}

fn condition_mentions_a_memory_load(condition: &ConditionTerm) -> bool {
    match condition {
        ConditionTerm::PointerValueEqual(left, right) => left
            .pointers()
            .chain(right.pointers())
            .any(|p| p.offset.any_scaled_value(term_mentions_a_memory_load)),

        // Until memory canonicalization traverses ADTs, conservatively disable
        // the memory-free fast path for this logical condition.
        ConditionTerm::AlgebraicEqual(_, _) => true,
        ConditionTerm::Constant(_) | ConditionTerm::Variable(_) => false,
        crate::kernel::binary_bitvector_condition!(left, right) => {
            term_mentions_a_memory_load(left) || term_mentions_a_memory_load(right)
        }
        ConditionTerm::Float32(float_condition) | ConditionTerm::Float64(float_condition) => {
            let mut mentions = false;
            float_condition.for_each_bitvector_term(|term| {
                mentions |= term_mentions_a_memory_load(term);
            });
            mentions
        }
        ConditionTerm::PointerOffsetEqual(left, right) => {
            offset_mentions_a_memory_load(left) || offset_mentions_a_memory_load(right)
        }
        ConditionTerm::PointerEqual(left, right) => {
            offset_mentions_a_memory_load(&left.offset)
                || offset_mentions_a_memory_load(&right.offset)
        }
        crate::kernel::integer_comparison_condition!(_, _) => false,
    }
}

fn offset_mentions_a_memory_load(offset: &PointerOffsetTerm) -> bool {
    offset.any_scaled_value(term_mentions_a_memory_load)
}

/// The load variable representing one load identity: the pair of a memory
/// snapshot (by content) and a loaded pointer. Hashing that identity into a
/// reserved id space picks where the search for its id starts, and the
/// thread-local registry assigns the first slot that holds this identity or
/// nothing, so distinct identities get distinct ids by construction. Every
/// pass — contract-grant lowering, requirement evaluation, and body
/// execution — therefore writes the same load with the same variable, and
/// the id is the hash itself unless another load already took that slot in
/// this session. The registry is never cleared within a session, and
/// exhausting its capacity is a loud failure rather than a silent reset.
/// The variable naming a `kind` load of `pointer` in `memory`. The epoch
/// walk that picks the snapshot it is named at is as wide as the widest
/// access recorded at the address, and never narrower than the read.
pub(crate) fn load_variable_for_cell(
    memory: &SharedCMemory,
    pointer: &Pointer,
    kind: LoadKind,
) -> Variable {
    load_variable_for_cell_with_origin(
        memory,
        pointer,
        kind,
        recorded_load_access_width(memory, pointer)
            .unwrap_or_else(|| kind.unrecorded_access_byte_width())
            .max(kind.byte_width()),
        memory,
    )
}

/// Mint the load identity for exactly this snapshot and pointer.
///
/// Fold substitution uses this after rewriting a registered load's address.
/// The ordinary cell helper first projects a snapshot through memory
/// provenance, which is correct for a newly observed load but would change
/// the snapshot identity carried by an existing defining fact.  Keeping this
/// narrow helper separate makes the selected snapshot explicit and avoids
/// traversing or rewriting any of its contents.
pub(crate) fn load_variable_for_exact_cell(
    memory: &SharedCMemory,
    pointer: &Pointer,
    kind: LoadKind,
    bytes: u32,
) -> Variable {
    mint_load_variable_identity(memory, pointer, kind, memory, bytes)
}

/// The variable naming a `kind` load of `pointer` in `memory`.
///
/// `bytes` is the access width the epoch walk uses, and it decides how far
/// back the walk may go: a store lands on this load exactly when it writes
/// one of these bytes. It is never narrower than the read itself.
pub(crate) fn load_variable_for_cell_with_origin(
    memory: &SharedCMemory,
    pointer: &Pointer,
    kind: LoadKind,
    bytes: u32,
    origin: &SharedCMemory,
) -> Variable {
    let bytes = bytes.max(kind.byte_width());
    // Derive the variable from the cell's DAG epoch when one is recorded:
    // snapshots that differ only by effects provably disjoint from this
    // cell then share the variable, so bookkeeping drift and unrelated
    // stores do not mint new identities for one load.
    let epoch = crate::kernel::resource_tracker::last_same_point(
        crate::kernel::resource_tracker::Resource::Cell { pointer, bytes },
        &crate::kernel::resource_tracker::ProgramPoint::at(memory),
    )
    .map(|point| point.snapshot().clone());
    let memory = epoch.as_ref().unwrap_or(memory);
    mint_load_variable_identity(memory, pointer, kind, origin, bytes)
}

/// The kind is part of the identity: two reads of one address in one
/// snapshot that differ in kind are two values. The hash leaves it out, so a
/// load keeps the slot it had when every load of its address agreed on one
/// kind, and a second kind probes past it like any other collision.
fn mint_load_variable_identity(
    memory: &SharedCMemory,
    pointer: &Pointer,
    kind: LoadKind,
    origin: &SharedCMemory,
    bytes: u32,
) -> Variable {
    use std::hash::{Hash, Hasher};
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    memory.hash(&mut hasher);
    pointer.hash(&mut hasher);
    let hash = hasher.finish();
    let range = load_variable_range();
    let current_epoch = LOAD_ORIGIN_EPOCH.with(std::cell::Cell::get);
    LOAD_VARIABLE_REGISTRY.with(|registry| {
        let mut registry = registry.borrow_mut();
        // The hash picks where the search for this load's id starts, not the
        // id itself. A slot is this load's exactly when the registry holds
        // this load there; a slot holding another load is skipped, so two
        // distinct loads can never share an id however their hashes compare.
        // Nothing is removed within a session, so a lookup that reaches an
        // empty slot has passed every slot this load could already hold.
        //
        // Termination: the capacity check below keeps the registry strictly
        // smaller than the id range, so an empty slot always exists; the
        // expected probe length at the real capacity and range is one.
        let mut slot = hash % range;
        loop {
            let variable = Variable(LOAD_VARIABLE_BASE + slot);
            match registry.get_mut(&variable) {
                Some(RegisteredLoad {
                    memory: known_memory,
                    pointer: known_pointer,
                    kind: known_kind,
                    origin: known_origin,
                    epoch: known_epoch,
                    bytes: known_bytes,
                }) if known_memory == memory && known_pointer == pointer && *known_kind == kind => {
                    // One entry stands for every access that resolved to this
                    // name, so its width has to cover all of them: a caller
                    // that reads the width back is asking how many bytes this
                    // name could depend on.
                    *known_bytes = (*known_bytes).max(bytes);
                    // An origin from an earlier epoch was minted by another
                    // function; this function's first mint is its origin.
                    if *known_epoch != current_epoch {
                        *known_origin = origin.clone();
                        *known_epoch = current_epoch;
                    }
                    return variable;
                }
                Some(_) => {
                    crate::instrumentation::record_deterministic_work(1);
                    slot = (slot + 1) % range;
                }
                None => {
                    assert!(
                        (registry.len() as u64) < range.saturating_sub(1)
                            && registry.len() < load_variable_registry_capacity(),
                        "load-variable registry capacity exhausted: this verification session \
                         minted {} distinct load identities; the registry never forgets an \
                         entry because it is what keeps two loads from sharing an id",
                        registry.len()
                    );
                    registry.insert(
                        variable,
                        RegisteredLoad {
                            memory: memory.clone(),
                            pointer: pointer.clone(),
                            kind,
                            origin: origin.clone(),
                            epoch: current_epoch,
                            bytes,
                        },
                    );
                    return variable;
                }
            }
        }
    })
}

/// Reuse an exact read name or a materialized pointer cell's retained name.
/// This lookup never canonicalizes a new read or walks its memory history.
/// A scalar read of fewer bytes cannot supply a whole pointer's identity.
pub(in crate::kernel) fn known_pointer_read_variable_for_term(
    bits: &Bitvector32Term,
) -> Option<Variable> {
    crate::instrumentation::record_deterministic_work(1);
    let Bitvector32Term::MemoryLoad(memory, address, LoadKind::Bits32) = bits else {
        return None;
    };
    let variable = LOAD_VARIABLE_CACHE
        .with(|cache| cache.borrow().get(bits).map(|(variable, _)| *variable))
        .or_else(|| match memory.known_value(address) {
            Some(CValue::Int32(Bitvector32Term::Variable(variable))) => Some(variable),
            _ => materialized_pointer_cell_load_variable(memory, address),
        })?;
    (registered_load_kind_for_variable(&variable) == Some(LoadKind::Bits32)
        && registered_load_bytes_for_variable(&variable)
            == Some(crate::kernel::C_POINTER_BYTE_WIDTH))
    .then_some(variable)
}

// Keep the actual producer expression, including its live snapshot and
// pointer. Load identities can recur in disconnected model arms; their first
// registered origin is not necessarily in the current arm's memory history.
fn record_wide_load_observation(term: &Bitvector32Term, variable: Variable) {
    let Bitvector32Term::MemoryLoad(memory, pointer, LoadKind::Bits64) = term else {
        return;
    };
    if registered_load_kind_for_variable(&variable) != Some(LoadKind::Bits64) {
        return;
    }
    let epoch = LOAD_ORIGIN_EPOCH.with(std::cell::Cell::get);
    crate::instrumentation::record_deterministic_work(1);
    WIDE_LOAD_OBSERVATIONS.with(|registry| {
        let mut registry = registry.borrow_mut();
        let key = (epoch, variable);
        if registry
            .get(&key)
            .is_some_and(|(known_memory, known_pointer)| {
                known_memory == memory && known_pointer == pointer.as_ref()
            })
        {
            return;
        }
        crate::instrumentation::record_deterministic_work(1);
        registry.insert(key, (memory.clone(), pointer.as_ref().clone()));
    });
}

// Only a typed producer records an unconditional pointer-read expression.
fn record_pointer_read_observation(value: &Pointer, memory: &CMemory, address: &Pointer) {
    let epoch = LOAD_ORIGIN_EPOCH.with(std::cell::Cell::get);
    crate::instrumentation::record_deterministic_work(1);
    let memory = crate::kernel::intern_c_memory_ref(memory);
    POINTER_READ_OBSERVATIONS.with(|registry| {
        let mut registry = registry.borrow_mut();
        let key = (epoch, value.clone());
        if registry
            .get(&key)
            .is_some_and(|(known_memory, known_address)| {
                known_memory == &memory && known_address == address
            })
        {
            return;
        }
        crate::instrumentation::record_deterministic_work(1);
        registry.insert(key, (memory, address.clone()));
    });
}

pub(crate) fn latest_pointer_read_observation(value: &Pointer) -> Option<(SharedCMemory, Pointer)> {
    let epoch = LOAD_ORIGIN_EPOCH.with(std::cell::Cell::get);
    crate::instrumentation::record_deterministic_work(1);
    POINTER_READ_OBSERVATIONS
        .with(|registry| registry.borrow().get(&(epoch, value.clone())).cloned())
}

pub(crate) fn latest_wide_load_observation(variable: &Variable) -> Option<Bitvector32Term> {
    let epoch = LOAD_ORIGIN_EPOCH.with(std::cell::Cell::get);
    crate::instrumentation::record_deterministic_work(1);
    WIDE_LOAD_OBSERVATIONS.with(|registry| {
        registry
            .borrow()
            .get(&(epoch, *variable))
            .map(|(memory, pointer)| {
                Bitvector32Term::MemoryLoad(
                    memory.clone(),
                    Box::new(pointer.clone()),
                    LoadKind::Bits64,
                )
            })
    })
}

/// Returns the load variable for a load term's provenance-stable form.
/// The term is first canonicalized without assumptions, resolving cached
/// cells and snapshot representation differences. The same cell loaded at
/// different symbolic states therefore shares one load variable whenever
/// the difference is representational. The second return value is the form
/// used by the variable's defining equation.
pub(crate) fn load_variable_for_term(
    bits: &Bitvector32Term,
) -> Option<(Variable, Bitvector32Term)> {
    let Bitvector32Term::MemoryLoad(_, _, kind) = bits else {
        return None;
    };
    // One byte, one name: a signed byte read is formed only as the
    // conversion of the unsigned read (`Bitvector32Term::memory_read`). A
    // raw signed-byte load term came from a producer that bypassed it; it is
    // refused a name, so it can never stand as a second, unrelated value of
    // the byte.
    if *kind == LoadKind::Int8 {
        return None;
    }
    // Naming is deterministic per term, and callers ask per fact atom per
    // comparison; the epoch walk and canonicalization behind a cold call
    // are not free, so cache by term. Term hashing is cheap: embedded
    // snapshots hash by interned identity.
    if let Some(hit) = LOAD_VARIABLE_CACHE.with(|cache| cache.borrow().get(bits).cloned()) {
        record_wide_load_observation(bits, hit.0);
        return Some(hit);
    }
    crate::instrumentation::record_deterministic_work(1);
    let computed = load_variable_for_term_uncached(bits)?;
    record_wide_load_observation(bits, computed.0);
    LOAD_VARIABLE_CACHE.with(|cache| {
        let mut cache = cache.borrow_mut();
        if cache.len() >= 100_000 {
            cache.clear();
        }
        cache.insert(bits.clone(), computed.clone());
    });
    Some(computed)
}

fn load_variable_for_term_uncached(bits: &Bitvector32Term) -> Option<(Variable, Bitvector32Term)> {
    // A pointer cell this snapshot holds materialized, whose value is the
    // pointer an earlier load of this same cell produced, already names this
    // load: the materialized value is `cell.block + v * width` and `v` is
    // registered as the load of this cell. The integer counterpart below
    // resolves through the canonical form; a pointer cell's value is not an
    // integer, so it is resolved here instead of falling through to the epoch
    // walk. That walk is assumption-free, so it stops at a loop head's havoc
    // even where the head copied the cell back as provably unwritten, and a
    // field such as `arena->occupied` read again inside the loop would get a
    // second name for the value its pointer already carries.
    if let Bitvector32Term::MemoryLoad(memory, pointer, LoadKind::Bits32) = bits
        && let Some(variable) = materialized_pointer_cell_load_variable(memory, pointer)
    {
        return Some((variable, bits.clone()));
    }
    let canonical = crate::kernel::memory_provenance::canonicalize_atomic_loads(bits);
    if let Bitvector32Term::MemoryLoad(memory, pointer, kind) = &canonical {
        let Bitvector32Term::MemoryLoad(origin, _, _) = bits else {
            unreachable!("the pattern above matched a memory load");
        };
        return Some((
            load_variable_for_cell_with_origin(
                memory,
                pointer,
                *kind,
                // Either snapshot's recorded entry is this same load's own
                // width, so the first one found is the answer. Taking the
                // larger would let a miss on one side widen a width the
                // other side knows exactly.
                recorded_load_access_width(origin, pointer)
                    .or_else(|| recorded_load_access_width(memory, pointer))
                    .unwrap_or_else(|| kind.unrecorded_access_byte_width()),
                origin,
            ),
            canonical.clone(),
        ));
    }
    // The canonical form resolved this load through the snapshot's own
    // materialized cell, and the cell holds a load variable: that variable
    // already names this value, so it is this load's name too. Falling
    // through would mint a second identity for one value whenever the cell's
    // snapshot cannot be reached by the assumption-free epoch walk — a cell
    // retained across a call havoc by a `separate` premise, for instance,
    // whose reload would otherwise lose every fact stated about it. The
    // resolution is structural and assumption-free, and the havoc's retention
    // decision is re-checked during certification, so this adds no alias
    // approximation of its own.
    if let Bitvector32Term::Variable(variable) = &canonical
        && let Bitvector32Term::MemoryLoad(_, _, kind) = bits
        && registered_load_kind_for_variable(variable) == Some(*kind)
    {
        return Some((*variable, bits.clone()));
    }
    let Bitvector32Term::MemoryLoad(memory, pointer, kind) = bits else {
        unreachable!("the pattern above matched a memory load");
    };
    Some((load_variable_for_cell(memory, pointer, *kind), bits.clone()))
}

/// The registered load variable a materialized pointer cell's value carries,
/// when that value is exactly the pointer a typed load of this cell produces
/// (`symbolic_pointer_load`): the cell's own block, offset `v * width` at the
/// value's pointee width, with `v` registered as a load of this same address.
/// One map lookup and one registry lookup.
fn materialized_pointer_cell_load_variable(
    memory: &SharedCMemory,
    pointer: &Pointer,
) -> Option<Variable> {
    let CValue::Pointer(value) = memory.cells.get(pointer)? else {
        return None;
    };
    let (storage, index, byte_width) = value.pointer().as_loaded()?;
    if *storage != pointer.block {
        return None;
    }
    // The scale must be the one a typed load of this cell applies, or the
    // stored index would not be the loaded one.
    if value.c_type().pointee_type()?.byte_width() != u32::try_from(byte_width).ok()? {
        return None;
    }
    let Bitvector32Term::Variable(variable) = index else {
        return None;
    };
    let (_, registered) = registered_load_for_variable(variable)?;
    (registered == *pointer
        && registered_load_kind_for_variable(variable) == Some(LoadKind::Bits32))
    .then_some(*variable)
}

/// Binds a load term to its load variable and records the defining
/// equation in the path's fact stream. The defining equation is
/// kernel-certified by construction: the load variable represents this
/// load. It must not demand a checkable assumption derivation
/// downstream.
fn mint_load_variable(
    bits: &Bitvector32Term,
    facts: &mut ExecutionFacts,
    _assumptions: &PureFactContext,
    source: Option<&LoadSourceId>,
) -> Option<Variable> {
    let (fresh, load) = load_variable_for_term(bits)?;
    record_load_variable_defining_fact_with_source(fresh, load, facts, source);
    Some(fresh)
}

/// Records a load variable's exact defining fact in a fact
/// stream, deduplicated by proposition. The equation is kernel-certified by
/// construction: the load variable represents this load. It must not demand
/// a checkable assumption derivation downstream.
pub(crate) fn record_load_variable_defining_fact(
    variable: Variable,
    load: Bitvector32Term,
    facts: &mut ExecutionFacts,
) {
    record_load_variable_defining_fact_with_source(variable, load, facts, None);
}

pub(crate) fn record_load_variable_defining_fact_with_source(
    variable: Variable,
    load: Bitvector32Term,
    facts: &mut ExecutionFacts,
    source: Option<&LoadSourceId>,
) {
    record_load_variable_defining_fact_with_source_and_pointer(variable, load, facts, source, None);
}

fn record_load_variable_defining_fact_with_source_and_pointer(
    variable: Variable,
    load: Bitvector32Term,
    facts: &mut ExecutionFacts,
    source: Option<&LoadSourceId>,
    typed_pointer_value: Option<&Pointer>,
) {
    let Bitvector32Term::MemoryLoad(memory, pointer, _) = &load else {
        // `load_variable_for_term` currently returns a memory load's
        // canonical operand.  Keep this guard explicit so future changes
        // cannot attach producer metadata to an unrelated term.
        return;
    };
    let defining_load = load.clone();
    let defining_proposition = Proposition::ConditionIs(
        ConditionTerm::Bitvector32Equal(
            Box::new(Bitvector32Term::Variable(variable)),
            Box::new(load.clone()),
        ),
        true,
    );
    let binding = GeneratedLoadBinding::Exact {
        variable,
        snapshot: CMemorySnapshotIdentity::of(memory.memory()),
        pointer: pointer.as_ref().clone(),
        load: defining_load,
        typed_pointer_value: typed_pointer_value.cloned(),
        observed_pointer_read: None,
    };
    let event =
        source.and_then(|source| GeneratedLoadSourceEvent::new(source.clone(), binding.clone()));
    let existing_index = facts
        .iter()
        .position(|fact| fact.proposition == defining_proposition);
    if let Some(index) = existing_index {
        let existing = facts.get_mut(index);
        if existing.generated_load_binding.is_none() || typed_pointer_value.is_some() {
            existing.generated_load_binding = Some(Box::new(binding));
        }
        if let Some(event) = event {
            existing.generated_load_source_events.push(event);
        }
        return;
    }
    let mut defining =
        ExecutionPureFact::certified(defining_proposition).with_generated_load_binding(binding);
    if let Some(event) = event {
        defining = defining.with_generated_load_source_event(event);
    }
    facts.push(defining);
}

pub(in crate::kernel) fn symbolic_load_value(
    memory: &CMemory,
    pointer: &Pointer,
    value_type: CType,
) -> Option<CValue> {
    // Every C load reaches the kernel through here with its type. The
    // `MemoryLoad` term built below carries the read's kind; the address's
    // recorded width, which every read there shares, is kept beside it.
    // Recording it here is what lets an `int32` load keep being separated
    // from a store one element away.
    record_load_access_width(memory, pointer, value_type.byte_width());
    symbolic_load_value_unrecorded(memory, pointer, value_type)
}

/// [`symbolic_load_value`] without recording the access width, for a caller
/// that has already said how wide the access is, as a symbolic static array
/// says it for every element at once
/// ([`declare_symbolic_array_access_widths`]).
pub(in crate::kernel) fn symbolic_load_value_unrecorded(
    memory: &CMemory,
    pointer: &Pointer,
    value_type: CType,
) -> Option<CValue> {
    match value_type {
        CType::Int128 | CType::UInt128 => {
            memory.symbolic_wide_integer_load(pointer, MachineIntegerType::from_c_type(value_type)?)
        }
        // An abstract value has no cells of its own (yet).
        CType::Parameter(_) => None,
        CType::Void | CType::VoidPointer => None,
        CType::Bool => {
            let load = Bitvector32Term::MemoryLoad(
                crate::kernel::intern_c_memory(memory.clone()),
                Box::new(pointer.clone()),
                LoadKind::UInt8,
            );
            Some(CValue::Bool(Bitvector32Term::if_then_else(
                ConditionTerm::equal(load, Bitvector32Term::Constant(0)),
                Bitvector32Term::Constant(0),
                Bitvector32Term::Constant(1),
            )))
        }
        CType::Int8 => Some(memory.symbolic_int8_load(pointer)),
        CType::Int16 => Some(memory.symbolic_int16_load(pointer)),
        CType::Int32 => Some(memory.symbolic_int32_load(pointer)),
        CType::UInt8 => Some(memory.symbolic_uint8_load(pointer)),
        CType::UInt16 => Some(memory.symbolic_uint16_load(pointer)),
        CType::UInt32 => Some(memory.symbolic_uint32_load(pointer)),
        CType::Int64 => Some(memory.symbolic_int64_load(pointer)),
        CType::UInt64 => Some(memory.symbolic_uint64_load(pointer)),
        CType::Float32 => Some(memory.symbolic_float32_load(pointer)),
        CType::Float64 => Some(memory.symbolic_float64_load(pointer)),
        CType::Int8Pointer | CType::Int8PointerPointer => Some(memory.symbolic_pointer_load(
            pointer,
            value_type.pointee_type()?.byte_width(),
            value_type,
        )),
        CType::VoidPointerPointer
        | CType::Int16Pointer
        | CType::UInt16Pointer
        | CType::Int32Pointer
        | CType::UInt8Pointer
        | CType::UInt32Pointer
        | CType::Int128Pointer
        | CType::Int64Pointer
        | CType::UInt128Pointer
        | CType::UInt64Pointer
        | CType::Int16PointerPointer
        | CType::UInt16PointerPointer
        | CType::Int32PointerPointer
        | CType::UInt8PointerPointer
        | CType::UInt32PointerPointer
        | CType::Int128PointerPointer
        | CType::Int64PointerPointer
        | CType::UInt128PointerPointer
        | CType::UInt64PointerPointer => Some(memory.symbolic_pointer_load(
            pointer,
            value_type.pointee_type()?.byte_width(),
            value_type,
        )),
        CType::Float32Pointer
        | CType::Float64Pointer
        | CType::Float32PointerPointer
        | CType::Float64PointerPointer => Some(memory.symbolic_pointer_load(
            pointer,
            value_type.pointee_type()?.byte_width(),
            value_type,
        )),
        CType::FunctionPointer(_) => {
            let load = Bitvector32Term::MemoryLoad(
                crate::kernel::intern_c_memory(memory.clone()),
                Box::new(pointer.clone()),
                LoadKind::Bits32,
            );
            let (variable, _) = load_variable_for_term(&load)?;
            Some(CValue::typed_pointer(
                Pointer::symbolic_function(variable),
                value_type,
            ))
        }
        CType::Int8Array(_) => None,
        CType::Int32Array(_)
        | CType::UInt8Array(_)
        | CType::Int16Array(_)
        | CType::UInt16Array(_)
        | CType::UInt32Array(_)
        | CType::Int128Array(_)
        | CType::Int64Array(_)
        | CType::UInt128Array(_)
        | CType::UInt64Array(_)
        | CType::Float32Array(_)
        | CType::Float64Array(_) => None,
        CType::PointerArray(_, _) => None,
    }
}

/// The value a symbolic static-storage cell of type `c_type` at `pointer`
/// holds at function entry, where `memory` holds only the storage's block: a
/// fresh symbolic pointer named by the cell's load for an object pointer (a
/// stored pointer may point into any block), and otherwise the cell's typed
/// load, its integer loads named as their load variables.
///
/// `record_width` says the access width here, as [`symbolic_load_value`]
/// does; a caller that declared it for a whole array
/// ([`declare_symbolic_array_access_widths`]) passes `false`. An object
/// pointer's load retains the same typed definition as a logical read.
/// Reuse only a load already named at this exact snapshot and address.
/// An optional cell-cache reconciliation must not canonicalize a cold load
/// by walking its unrelated memory history. Missing names give no evidence.
pub(in crate::kernel) fn cached_symbolic_storage_cell_value(
    memory: &CMemory,
    pointer: &Pointer,
    c_type: CType,
) -> Option<CValue> {
    let (kind, wrap): (LoadKind, fn(Bitvector32Term) -> CValue) = match c_type {
        // The cache names the byte's unsigned read; a signed read converts it.
        CType::Int8 => (LoadKind::UInt8, |unsigned| {
            CValue::Int8(Bitvector32Term::signed_byte(unsigned))
        }),
        CType::Int16 => (LoadKind::Int16, CValue::Int16),
        CType::Int32 => (LoadKind::Bits32, CValue::Int32),
        CType::UInt8 => (LoadKind::UInt8, CValue::UInt8),
        CType::UInt16 => (LoadKind::UInt16, CValue::UInt16),
        CType::UInt32 => (LoadKind::Bits32, CValue::UInt32),
        CType::Int64 => (LoadKind::Bits64, CValue::Int64),
        CType::UInt64 => (LoadKind::Bits64, CValue::UInt64),
        _ if c_type.is_object_pointer() => {
            let load = Bitvector32Term::MemoryLoad(
                crate::kernel::intern_c_memory(memory.clone()),
                Box::new(pointer.clone()),
                LoadKind::Bits32,
            );
            return LOAD_VARIABLE_CACHE.with(|cache| {
                let variable = cache.borrow().get(&load)?.0;
                Some(CValue::Pointer(CPointerValue::from_read(
                    Pointer::symbolic(variable),
                    c_type,
                    &crate::kernel::intern_c_memory(memory.clone()),
                    pointer,
                )))
            });
        }
        _ => return None,
    };
    let load = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory(memory.clone()),
        Box::new(pointer.clone()),
        kind,
    );
    crate::instrumentation::record_deterministic_work(1);
    TERM_CACHE
        .with(|cache| cache.borrow().get(&load).cloned())
        .or_else(|| {
            LOAD_VARIABLE_CACHE.with(|cache| {
                cache
                    .borrow()
                    .get(&load)
                    .map(|(variable, _)| Bitvector32Term::Variable(*variable))
            })
        })
        .map(wrap)
}

pub(in crate::kernel) fn symbolic_storage_cell_value(
    memory: &CMemory,
    pointer: &Pointer,
    c_type: CType,
    record_width: bool,
) -> Option<CValue> {
    if c_type.is_object_pointer() {
        if record_width && pointer.block.is_local_block() {
            record_load_access_width(memory, pointer, c_type.byte_width());
        }
        let load = Bitvector32Term::MemoryLoad(
            crate::kernel::intern_c_memory(memory.clone()),
            Box::new(pointer.clone()),
            LoadKind::Bits32,
        );
        let (variable, definition) = load_variable_for_term(&load)
            .expect("symbolic pointer cells must be backed by memory loads");
        let value = Pointer::symbolic(variable);
        if let Bitvector32Term::MemoryLoad(snapshot, address, _) = definition {
            crate::kernel::equality_graph::EqualityGraph::default()
                .register_pointer_read_definition(&value, &snapshot, &address);
        }
        return Some(CValue::Pointer(CPointerValue::from_read(
            value,
            c_type,
            &crate::kernel::intern_c_memory(memory.clone()),
            pointer,
        )));
    }
    // The cell holds the load of this storage at its symbolic base, and a
    // term is canonical at creation: name the load as its load variable,
    // exactly as a contract clause over the same storage names it. A raw
    // load here reached the facts a callee's `old(...)` produced, where
    // nothing equates it with the caller's name for the same cell.
    let value = if record_width {
        symbolic_load_value(memory, pointer, c_type)
    } else {
        symbolic_load_value_unrecorded(memory, pointer, c_type)
    };
    value.map(|value| match value {
        CValue::Int8(bits) => CValue::Int8(canonical_term(&bits)),
        CValue::Int16(bits) => CValue::Int16(canonical_term(&bits)),
        CValue::Int32(bits) => CValue::Int32(canonical_term(&bits)),
        CValue::UInt8(bits) => CValue::UInt8(canonical_term(&bits)),
        CValue::UInt16(bits) => CValue::UInt16(canonical_term(&bits)),
        CValue::UInt32(bits) => CValue::UInt32(canonical_term(&bits)),
        CValue::Int64(bits) => CValue::Int64(canonical_term(&bits)),
        CValue::UInt64(bits) => CValue::UInt64(canonical_term(&bits)),
        CValue::Int128(bits) => CValue::Int128(canonical_term(&bits)),
        CValue::UInt128(bits) => CValue::UInt128(canonical_term(&bits)),
        other => other,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn program_pointer_facts_retain_their_scoped_read_producer() {
        let _session = crate::kernel::VerificationSession::enter();
        let empty = PureFactContext::new();
        let registry_before = capture_load_variable_registry();
        let memory = CMemory::new();
        let address = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Constant(8),
        };
        let paths = evaluate_c_memory_load_paths(
            &memory,
            address,
            CType::Int32Pointer,
            ExecutionFacts::new(),
            Vec::new(),
            &empty,
            true,
            false,
            None,
            None,
        );
        let [path] = paths.as_slice() else {
            panic!("one program read")
        };
        let CExpressionOutcome::Value(CValue::Pointer(pointer)) = &path.outcome else {
            panic!("pointer value")
        };
        assert!(
            crate::kernel::equality_graph::logical_pointer_read_for_offset(&pointer.offset)
                .is_none()
        );
        let ordinary: ExecutionFacts = path
            .facts
            .iter()
            .map(|fact| ExecutionPureFact::new(fact.proposition().clone()))
            .collect::<Vec<_>>()
            .into();
        let _ordinary_context = assumptions_with_path_context(&empty, &ordinary, &path.obligations);
        assert!(
            crate::kernel::equality_graph::logical_pointer_read_for_offset(&pointer.offset)
                .is_none()
        );
        let context = assumptions_with_path_context(&empty, &path.facts, &path.obligations);
        assert!(
            empty
                .retained_pointer_read_application(pointer.pointer())
                .is_none()
        );
        assert!(
            _ordinary_context
                .retained_pointer_read_application(pointer.pointer())
                .is_none()
        );
        assert!(
            context
                .retained_pointer_read_application(pointer.pointer())
                .is_some()
        );
        assert!(
            crate::kernel::memory_provenance::checked_pointer_read_endpoint(
                pointer.pointer(),
                &context
            )
            .is_some()
        );
        assert!(
            crate::kernel::equality_graph::logical_pointer_read_for_offset(&pointer.offset)
                .is_none()
        );
        assert!(
            ResourceContext::new()
                .memory_write_range(pointer.pointer(), 4, &context)
                .is_none()
        );
        restore_load_variable_registry(&registry_before);
        assert!(
            context
                .retained_pointer_read_application(pointer.pointer())
                .is_some()
        );
        assert!(
            crate::kernel::memory_provenance::checked_pointer_read_endpoint(
                pointer.pointer(),
                &context
            )
            .is_some()
        );
    }

    #[test]
    fn logical_read_equations_are_not_conditions_or_quantifier_guards() {
        let value = Pointer::symbolic(Variable(959_001));
        let read = Pointer::loaded_value(&intern_c_memory(CMemory::new()), &value);
        let fact = ExecutionPureFact::logical_read_equation(
            CPointerValue::new(value, CType::Int32Pointer),
            read,
        );
        let facts: ExecutionFacts = vec![fact.clone()].into();
        assert!(!facts.has_path_conditions());
        let goal = Proposition::ConditionIs(ConditionTerm::Constant(true), true);
        assert_eq!(wrap_path_context(goal.clone(), &facts, &[]), goal);
        assert_eq!(guard_quantified_witness(goal.clone(), &facts), goal);
        let ordinary: ExecutionFacts =
            vec![ExecutionPureFact::new(fact.proposition().clone())].into();
        assert!(ordinary.has_path_conditions());
        assert_ne!(wrap_path_context(goal.clone(), &ordinary, &[]), goal);
        let changed: ExecutionFacts = vec![fact.with_proposition(goal)].into();
        assert!(
            changed.has_path_conditions(),
            "rewriting drops exact read-producer metadata"
        );
    }

    #[test]
    fn logical_pointer_read_does_not_export_a_narrow_scalar_as_a_full_cell() {
        let _session = crate::kernel::VerificationSession::enter();
        let context = PureFactContext::new();
        let address = Pointer::symbolic(Variable(959_101));
        let base = CMemory::new();
        let mut facts = ExecutionFacts::new();
        let value = canonicalized_symbolic_load_value_with_identity(
            &base,
            &address,
            CType::Int32,
            &mut facts,
            &context,
            false,
            None,
            LoadPurpose::Logical,
        )
        .unwrap();
        let memory = base.materialize_named_cell(address.clone(), value);
        let paths = evaluate_logical_memory_load_paths(
            &memory,
            address,
            CType::Int64Pointer,
            ExecutionFacts::new(),
            Vec::new(),
            &context,
        );
        assert!(paths.iter().all(|path| path.facts.is_empty()));
    }

    // Typed observations must preserve the complete pointer, selected alias
    // premises, snapshot changes, and session boundaries without corpus scans.
    // A cached pointer can still denote an older defining load after a frame
    // materializes its named scalar cell. A checked index must retain where
    // that value was read now, without publishing evidence to another context.
    #[test]
    fn checked_resource_index_retains_its_current_pointer_cell() {
        let _session = crate::kernel::VerificationSession::enter();
        let empty = PureFactContext::new();
        let base = CMemory::new();
        let source = Pointer::symbolic(Variable(955_001));
        let cached = logical_pointer_read(&base, &source, &empty);
        let variable = typed_pointer_read_variable(&cached).expect("typed cached load");
        let address = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(955_002)), 4),
        };
        let alias = Pointer::symbolic(Variable(955_003));
        let current = base.materialize_named_cell(
            address.clone(),
            CValue::Int32(Bitvector32Term::Variable(variable)),
        );
        let logical = logical_pointer_read(&current, &alias, &empty);
        let model = Pointer::symbolic(Variable(955_004));
        let base_context = empty
            .clone()
            .assume_condition(
                ConditionTerm::pointer_equal(alias.clone(), address.clone()),
                true,
            )
            .assume_condition(
                ConditionTerm::PointerValueEqual(
                    Box::new(CPointerValue::new(model.clone(), CType::Int64Pointer)),
                    Box::new(CPointerValue::from_read(
                        logical.clone(),
                        CType::Int64Pointer,
                        &intern_c_memory(current.clone()),
                        &alias,
                    )),
                ),
                true,
            );
        let context = base_context.clone().require_owned_expression_loads();
        let isolated = context.clone();
        let paths = evaluate_c_memory_load_paths(
            &current,
            address.clone(),
            CType::Int64Pointer,
            ExecutionFacts::new(),
            Vec::new(),
            &context,
            true,
            false,
            None,
            None,
        );
        let [path] = paths.as_slice() else {
            panic!("one checked read");
        };
        let CExpressionOutcome::Value(CValue::Pointer(value)) = &path.outcome else {
            panic!("a pointer-valued read");
        };
        let arguments_equal = |facts: &PureFactContext| {
            crate::kernel::resource_arguments_proven_equal(
                &AlgebraicValue::C(CValue::typed_pointer(model.clone(), CType::Int64Pointer)),
                &AlgebraicValue::C(CValue::Pointer(value.clone())),
                facts,
            )
        };
        assert!(
            !arguments_equal(&context),
            "the older definition is not the current observation"
        );
        for fact in &path.facts {
            fact.retain_pointer_read_definition(&context);
        }
        assert!(arguments_equal(&context));
        assert!(
            !arguments_equal(&isolated),
            "checked evidence must stay in its context"
        );
        assert!(context.pointers_known_equal(&model, value.pointer()));
        let mut checkpoint = context.equality_graph.input_root();
        assert!(checkpoint.append_inputs_from(&context.equality_graph));
        assert!(checkpoint.are_equal(&model, value.pointer()));
        let restricted = context.restricted_to_facts(&[], &[]);
        assert!(!restricted.pointers_known_equal(&model, value.pointer()));
        let missing_alias = empty.clone().assume_condition(
            ConditionTerm::PointerValueEqual(
                Box::new(CPointerValue::new(model.clone(), CType::Int64Pointer)),
                Box::new(CPointerValue::from_read(
                    logical.clone(),
                    CType::Int64Pointer,
                    &intern_c_memory(current.clone()),
                    &alias,
                )),
            ),
            true,
        );
        for fact in &path.facts {
            fact.retain_pointer_read_definition(&missing_alias);
        }
        assert!(!arguments_equal(&missing_alias));
        for (ordinary, volatile) in [(true, false), (false, true)] {
            let control = if ordinary {
                base_context.clone()
            } else {
                isolated.clone()
            };
            let paths = evaluate_c_memory_load_paths(
                &current,
                address.clone(),
                CType::Int64Pointer,
                ExecutionFacts::new(),
                Vec::new(),
                &control,
                true,
                volatile,
                None,
                None,
            );
            for path in paths {
                for fact in &path.facts {
                    fact.retain_pointer_read_definition(&control);
                }
            }
            assert!(!arguments_equal(&control));
        }
        let forged_context = isolated.clone();
        for fact in &path.facts {
            let mut forged = fact.clone();
            forged.certified = false;
            forged.retain_pointer_read_definition(&forged_context);
        }
        assert!(!arguments_equal(&forged_context));

        // A contract argument outlives its temporary expression fact stream.
        // It must keep the same certified read evidence as a recursive child.
        let argument_context = base_context.clone().require_owned_expression_loads();
        let state = CState::new()
            .with_memory(current.clone())
            .with_resource_context(ResourceContext::new().unchecked_with_fact(
                CResourceFact::view_memory(CMemoryRange::new_with_element_width(
                    address.clone(),
                    0u32.into(),
                    1u32.into(),
                    8,
                )),
            ));
        let expression = crate::kernel::c_typed_load(
            CExpression::Value(CValue::typed_pointer(
                address.clone(),
                CType::Int64PointerPointer,
            )),
            CType::Int64Pointer,
        );
        let value = crate::kernel::loops::evaluate_loop_effect_segment_value(
            &state,
            &expression,
            &argument_context,
            "checked resource argument",
            &mut ExecutionBudget::beside_live_state(),
        )
        .unwrap()
        .unwrap();
        assert!(crate::kernel::resource_arguments_proven_equal(
            &AlgebraicValue::C(CValue::typed_pointer(model, CType::Int64Pointer)),
            &AlgebraicValue::C(value),
            &argument_context,
        ));
    }

    #[test]
    fn a_loaded_pointer_cannot_reach_a_local_declared_after_the_read() {
        let storage = PointerBlock::Heap(8710);
        let early: PointerBlock = "local:early_object".into();
        let later: PointerBlock = "local:later_object".into();
        let cell = Pointer {
            block: storage.clone(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let memory = CMemory::new()
            .with_block(storage.clone(), 16)
            .with_block(early.clone(), 4);
        let value_type = CType::Int32Pointer;
        let assumptions = PureFactContext::new()
            .assume_proposition(Proposition::CMemoryReadDefined {
                memory: memory.clone(),
                pointer: cell.clone(),
                value_type,
            })
            .assume_proposition(Proposition::CMemoryLoadable {
                memory: memory.clone(),
                base: cell.clone(),
                bytes: Bitvector32Term::Constant(8),
                wide: false,
            });
        let paths = evaluate_spec_memory_load_paths(
            &memory,
            cell,
            value_type,
            Vec::new().into(),
            Vec::new(),
            &assumptions,
        );
        let [path] = paths.as_slice() else {
            panic!("one typed read expected");
        };
        let CExpressionOutcome::Value(CValue::Pointer(value)) = &path.outcome else {
            panic!("pointer value expected");
        };
        let loaded = &value.pointer().block;
        assert!(loaded.proven_distinct(&later));
        assert!(later.proven_distinct(loaded));
        assert!(!loaded.proven_distinct(&early));
        assert!(!loaded.proven_distinct(&PointerBlock::Heap(8711)));
    }

    #[test]
    fn unknown_pointer_in_fresh_storage_does_not_inherit_storage_provenance() {
        for block in [PointerBlock::Heap(8700), PointerBlock::Temporary(8701)] {
            for offset in [0, 8] {
                let cell = Pointer {
                    block: block.clone(),
                    offset: PointerOffsetTerm::Constant(offset),
                };
                let memory = CMemory::new().with_block(block.clone(), 16);
                let value_type = CType::Int32Pointer;
                let assumptions = PureFactContext::new()
                    .assume_proposition(Proposition::CMemoryReadDefined {
                        memory: memory.clone(),
                        pointer: cell.clone(),
                        value_type,
                    })
                    .assume_proposition(Proposition::CMemoryLoadable {
                        memory: memory.clone(),
                        base: cell.clone(),
                        bytes: Bitvector32Term::Constant(8),
                        wide: false,
                    });
                for logical in [false, true] {
                    let paths = if logical {
                        evaluate_logical_memory_load_paths(
                            &memory,
                            cell.clone(),
                            value_type,
                            Vec::new().into(),
                            Vec::new(),
                            &assumptions,
                        )
                    } else {
                        evaluate_spec_memory_load_paths(
                            &memory,
                            cell.clone(),
                            value_type,
                            Vec::new().into(),
                            Vec::new(),
                            &assumptions,
                        )
                    };
                    let [path] = paths.as_slice() else {
                        panic!("one typed read expected");
                    };
                    let CExpressionOutcome::Value(CValue::Pointer(value)) = &path.outcome else {
                        panic!("pointer value expected");
                    };
                    assert!(matches!(value.pointer().block, PointerBlock::Symbolic(_)));
                    assert!(
                        !value
                            .pointer()
                            .block
                            .proven_distinct(&PointerBlock::Heap(8702))
                    );
                    assert_eq!(value.c_type(), value_type);
                }
                let bits = Bitvector32Term::MemoryLoad(
                    crate::kernel::intern_c_memory_ref(&memory),
                    Box::new(cell.clone()),
                    crate::kernel::LoadKind::Bits32,
                );
                let mut facts = crate::kernel::ExecutionFacts::new();
                let cached = canonicalized_pointer_value_from_int_cell(
                    &memory,
                    &cell,
                    &CValue::Int32(bits),
                    value_type,
                    &mut facts,
                    &assumptions,
                    None,
                    LoadPurpose::Validity,
                )
                .unwrap();
                let CValue::Pointer(cached) = cached else {
                    panic!("cached pointer expected");
                };
                assert!(matches!(cached.pointer().block, PointerBlock::Symbolic(_)));
                let target = Pointer {
                    block: PointerBlock::Heap(8702),
                    offset: PointerOffsetTerm::Constant(0),
                };
                let stored = memory.store(
                    cell.clone(),
                    CValue::typed_pointer(target.clone(), value_type),
                );
                let paths = evaluate_logical_memory_load_paths(
                    &stored,
                    cell,
                    value_type,
                    Vec::new().into(),
                    Vec::new(),
                    &assumptions,
                );
                assert!(
                    matches!(&paths[0].outcome, CExpressionOutcome::Value(CValue::Pointer(value)) if value.pointer() == &target)
                );
            }
        }
    }

    #[test]
    fn logical_scalar_read_preserves_cached_offset_spelling() {
        let pointer = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Add(
                Box::new(PointerOffsetTerm::Int32Scaled {
                    value: Box::new(Bitvector32Term::Variable(Variable(944_021))),
                    byte_width: 4,
                }),
                Box::new(PointerOffsetTerm::Constant(16)),
            ),
        };
        let expected = CValue::Int32(Bitvector32Term::Constant(7));
        let memory = CMemory::new().store(pointer.clone(), expected.clone());
        let paths = evaluate_logical_memory_load_paths(
            &memory,
            pointer,
            CType::Int32,
            Vec::new().into(),
            Vec::new(),
            &PureFactContext::new(),
        );
        assert_eq!(paths.len(), 1);
        assert_eq!(paths[0].outcome, CExpressionOutcome::Value(expected));
    }

    #[test]
    fn unknown_pointer_in_local_storage_has_opaque_provenance_with_and_without_call_havoc() {
        for (offset, call_havoc) in [(0, false), (8, false), (0, true), (8, true)] {
            let cell = Pointer {
                block: "local:pointer-holder".into(),
                offset: PointerOffsetTerm::Constant(offset),
            };
            let target = Pointer {
                block: "local:other-object".into(),
                offset: PointerOffsetTerm::Constant(0),
            };
            let value_type = CType::Int32Pointer;
            let before = CMemory::new()
                .with_block(target.block.clone(), 4)
                .with_block(cell.block.clone(), 16)
                .store(
                    cell.clone(),
                    CValue::typed_pointer(target.clone(), value_type),
                );
            let range =
                CMemoryRange::new_with_element_width(cell.clone(), 0u32.into(), 8u32.into(), 1);
            let assumptions = PureFactContext::new();
            let memory = if call_havoc {
                before.with_call_memory_havoc(Variable(944_014), &[range], &assumptions, None)
            } else {
                // A loop head can forget the field's value without adding a
                // call-havoc node. The storage address still says nothing
                // about the pointee's allocation identity.
                before.with_loop_memory_havoc_preserving_loans(
                    Variable(944_014),
                    &BTreeSet::new(),
                    Some(&[range]),
                    None,
                )
            };
            assert!(memory.known_value(&cell).is_none());
            for logical in [false, true] {
                let paths = if logical {
                    evaluate_logical_memory_load_paths(
                        &memory,
                        cell.clone(),
                        value_type,
                        Vec::new().into(),
                        Vec::new(),
                        &assumptions,
                    )
                } else {
                    evaluate_spec_memory_load_paths(
                        &memory,
                        cell.clone(),
                        value_type,
                        Vec::new().into(),
                        Vec::new(),
                        &assumptions,
                    )
                };
                let [path] = paths.as_slice() else {
                    panic!("one typed read expected");
                };
                let CExpressionOutcome::Value(CValue::Pointer(value)) = &path.outcome else {
                    panic!("pointer value expected");
                };
                assert!(matches!(value.pointer().block, PointerBlock::Symbolic(_)));
                assert!(!value.pointer().block.proven_distinct(&target.block));
            }
            let bits = Bitvector32Term::MemoryLoad(
                crate::kernel::intern_c_memory_ref(&memory),
                Box::new(cell.clone()),
                crate::kernel::LoadKind::Bits32,
            );
            let cached = canonicalized_pointer_value_from_int_cell(
                &memory,
                &cell,
                &CValue::Int32(bits),
                value_type,
                &mut ExecutionFacts::new(),
                &assumptions,
                None,
                LoadPurpose::Validity,
            )
            .unwrap();
            let CValue::Pointer(cached) = cached else {
                panic!("cached pointer expected");
            };
            assert!(matches!(cached.pointer().block, PointerBlock::Symbolic(_)));
            assert!(!cached.pointer().block.proven_distinct(&target.block));
        }
    }

    #[test]
    fn indexed_local_load_uses_proven_alias_without_inventing_initialization() {
        let index = Bitvector32Term::Variable(Variable(839));
        let base = Pointer {
            block: "local:indexed".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let pointer = Pointer {
            block: base.block.clone(),
            offset: PointerOffsetTerm::add(
                PointerOffsetTerm::Constant(4),
                PointerOffsetTerm::scale_int32(index.clone(), 4),
            ),
        };
        let assumptions = PureFactContext::new().assume_condition(
            ConditionTerm::equal(index, Bitvector32Term::Constant(1)),
            true,
        );
        let memory = CMemory::new()
            .with_block(base.block.clone(), 12)
            .store(base.offset_by_bytes(4), int32(3));
        for initialized in [false, true] {
            let memory = if initialized {
                memory.clone().store(base.offset_by_bytes(8), int32(7))
            } else {
                memory.clone()
            };
            let paths = evaluate_c_memory_load_paths(
                &memory,
                pointer.clone(),
                CType::Int32,
                Vec::new().into(),
                Vec::new(),
                &assumptions,
                false,
                false,
                None,
                None,
            );
            assert_eq!(paths.len(), 1);
            assert_eq!(
                paths[0].outcome,
                if initialized {
                    CExpressionOutcome::Value(int32(7))
                } else {
                    CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::UninitializedRead)
                }
            );
            assert!(paths[0].facts.is_empty());
        }
    }

    fn test_load_source(occurrence: u32) -> LoadSourceId {
        LoadSourceId {
            owner: LoadSourceOwnerId {
                source_unit: std::sync::Arc::from("load-source.c"),
                function: std::sync::Arc::from("read"),
            },
            occurrence,
            reference_access: None,
        }
    }

    #[test]
    fn alias_cache_keys_answers_by_assumption_context() {
        let left = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Variable(Variable(810)),
        };
        let right = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Variable(Variable(811)),
        };
        let mut cache = MemoryLoadAliasCache::default();
        let empty = PureFactContext::new();
        assert!(!cache.resolution_equal(&left, &right, &empty));

        let equal = empty.assume_condition(
            ConditionTerm::pointer_offset_equal(left.offset.clone(), right.offset.clone()),
            true,
        );
        assert!(cache.resolution_equal(&left, &right, &equal));
    }

    #[test]
    fn ancestor_named_load_does_not_cross_into_an_aliasing_fact_context() {
        let retained_index = Bitvector32Term::Variable(Variable(812));
        let written_index = Bitvector32Term::Variable(Variable(813));
        let read_index = Bitvector32Term::Variable(Variable(814));
        let at = |index| Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::scale_int32(index, 4),
        };
        let retained = at(retained_index);
        let written = at(written_index.clone());
        let read = at(read_index.clone());

        // Keep one unresolved cell so the reduced load is still symbolic.
        // Dropping only the later, proven-distinct write then makes the
        // reduced memory structurally equal to this already-interned ancestor.
        let ancestor_memory = CMemory::new().store(retained, int32(1));
        let ancestor = intern_c_memory_ref(&ancestor_memory);
        let current = ancestor_memory.store(written.clone(), int32(2));
        let distinct = PureFactContext::new().assume_condition(
            ConditionTerm::equal(read_index.clone(), written_index.clone()),
            false,
        );
        let aliasing = PureFactContext::new()
            .assume_condition(ConditionTerm::equal(read_index, written_index), true);
        let mut cache = MemoryLoadAliasCache::default();

        let distinct_paths = evaluate_c_memory_load_paths_with_alias_cache(
            &current,
            read.clone(),
            CType::Int32,
            Vec::new().into(),
            Vec::new(),
            &distinct,
            true,
            LoadPurpose::Validity,
            &mut cache,
            None,
            None,
        );
        let [distinct_path] = distinct_paths.as_slice() else {
            panic!("the decided distinct load should have one path");
        };
        let CExpressionOutcome::Value(CValue::Int32(Bitvector32Term::Variable(variable))) =
            &distinct_path.outcome
        else {
            panic!("the unresolved distinct load should have a symbolic identity");
        };
        let (named_memory, named_pointer) = registered_load_for_variable(variable)
            .expect("the symbolic identity should retain its exact load");
        assert_eq!(named_memory, ancestor);
        assert_eq!(named_pointer, read);

        // Reuse the same per-load cache deliberately. Its assumption-context
        // key must prevent the distinct answer, and therefore the ancestor
        // name, from leaking into the sibling context where the write aliases.
        let aliasing_paths = evaluate_c_memory_load_paths_with_alias_cache(
            &current,
            read,
            CType::Int32,
            Vec::new().into(),
            Vec::new(),
            &aliasing,
            true,
            LoadPurpose::Validity,
            &mut cache,
            None,
            None,
        );
        let [aliasing_path] = aliasing_paths.as_slice() else {
            panic!("the decided aliasing load should have one path");
        };
        assert_eq!(aliasing_path.outcome, CExpressionOutcome::Value(int32(2)));
    }

    #[test]
    fn minted_load_fact_carries_exact_producer_binding() {
        let memory = crate::kernel::intern_c_memory(CMemory::new());
        let pointer = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Constant(12),
        };
        let load = Bitvector32Term::MemoryLoad(
            memory.clone(),
            Box::new(pointer.clone()),
            crate::kernel::LoadKind::Bits32,
        );
        let (variable, canonical) = load_variable_for_term(&load).expect("load identity");
        let mut facts = crate::kernel::ExecutionFacts::new();
        record_load_variable_defining_fact(variable, canonical.clone(), &mut facts);
        assert_eq!(facts.len(), 1);
        let fact = &facts[0];
        assert!(matches!(
            fact.generated_load_binding(),
            Some(GeneratedLoadBinding::Exact {
                variable: recorded,
                snapshot,
                pointer: recorded_pointer,
                load: recorded_load,
                ..
            }) if *recorded == variable
                && *snapshot == CMemorySnapshotIdentity::of(memory.memory())
                && recorded_pointer == &pointer
                && recorded_load == &canonical
        ));
    }

    #[test]
    fn repeated_mint_keeps_each_exact_source_observation_on_one_fact() {
        let memory = crate::kernel::intern_c_memory(CMemory::new());
        let pointer = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Constant(12),
        };
        let load =
            Bitvector32Term::MemoryLoad(memory, Box::new(pointer), crate::kernel::LoadKind::Bits32);
        let (variable, canonical) = load_variable_for_term(&load).expect("load identity");
        let mut facts = crate::kernel::ExecutionFacts::new();
        let first = test_load_source(0);
        let second = test_load_source(1);
        record_load_variable_defining_fact_with_source(
            variable,
            canonical.clone(),
            &mut facts,
            Some(&first),
        );
        record_load_variable_defining_fact_with_source(
            variable,
            canonical,
            &mut facts,
            Some(&second),
        );
        assert_eq!(facts.len(), 1);
        let fact = &facts[0];
        assert_eq!(fact.generated_load_source_events().len(), 2);
        assert_eq!(fact.generated_load_source_events()[0].source(), &first);
        assert_eq!(fact.generated_load_source_events()[1].source(), &second);
    }

    #[test]
    fn transported_equal_equation_from_a_new_epoch_drops_producer_provenance() {
        let pointer = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Constant(20),
        };
        let first_memory = crate::kernel::intern_c_memory(CMemory::new());
        let first_load = Bitvector32Term::MemoryLoad(
            first_memory.clone(),
            Box::new(pointer.clone()),
            crate::kernel::LoadKind::Bits32,
        );
        let mut facts = crate::kernel::ExecutionFacts::new();
        let source = test_load_source(0);
        let variable = mint_load_variable(
            &first_load,
            &mut facts,
            &PureFactContext::new(),
            Some(&source),
        )
        .expect("load identity");
        assert_eq!(facts.len(), 1);
        let fact = &facts[0];
        assert!(fact.generated_load_binding().is_some());
        assert_eq!(fact.generated_load_source_events().len(), 1);

        // A fresh arena represents a new epoch. Its empty CMemory is
        // structurally equal to the first one, but its embedded snapshot
        // identity is intentionally different.
        crate::kernel::primitives::start_fresh_c_memory_arena();
        let second_memory = crate::kernel::intern_c_memory(CMemory::new());
        let second_load = Bitvector32Term::MemoryLoad(
            second_memory.clone(),
            Box::new(pointer),
            crate::kernel::LoadKind::Bits32,
        );
        let replacement = Proposition::ConditionIs(
            ConditionTerm::Bitvector32Equal(
                Box::new(Bitvector32Term::Variable(variable)),
                Box::new(second_load),
            ),
            true,
        );
        assert_eq!(fact.proposition(), &replacement);
        assert_ne!(
            CMemorySnapshotIdentity::of(first_memory.memory()),
            CMemorySnapshotIdentity::of(second_memory.memory())
        );
        let transported = fact.clone().with_proposition(replacement);
        assert!(transported.generated_load_binding().is_none());
        assert!(transported.generated_load_source_events().is_empty());
    }

    /// A symbolic index over many concrete cells splits into a case per cell
    /// on one stack frame. The split used to recurse once per cell, and a
    /// file-scope array of a thousand elements overflowed the main thread's
    /// stack; a few hundred cells do the same on this small one.
    #[test]
    #[ignore = "nightly: 0.6s in the parallel gate"]
    fn a_symbolic_load_over_many_undecided_cells_splits_without_recursing() {
        const CELLS: u32 = 400;
        let paths = std::thread::Builder::new()
            .stack_size(1 << 20)
            .spawn(|| {
                let block = PointerBlock::from("global:split_table");
                let mut memory = CMemory::new().with_block(block.clone(), CELLS * 4);
                for index in 0..CELLS {
                    memory = memory.store(
                        Pointer {
                            block: block.clone(),
                            offset: PointerOffsetTerm::Constant(i64::from(index) * 4),
                        },
                        int32(index),
                    );
                }
                let pointer = Pointer {
                    block,
                    offset: PointerOffsetTerm::scale_int32(
                        Bitvector32Term::Variable(Variable(841)),
                        4,
                    ),
                };
                evaluate_c_memory_load_paths(
                    &memory,
                    pointer,
                    CType::Int32,
                    Vec::new().into(),
                    Vec::new(),
                    &PureFactContext::new(),
                    false,
                    false,
                    None,
                    None,
                )
                .into_iter()
                .map(|path| path.outcome)
                .collect::<Vec<_>>()
            })
            .expect("spawn the small-stack load")
            .join()
            .expect("the split must not overflow a small stack");
        // One aliasing case per cell, in cell order, then the case distinct
        // from every cell.
        assert_eq!(paths.len(), CELLS as usize + 1, "{:?}", paths.last());
        for (index, outcome) in paths.iter().take(CELLS as usize).enumerate() {
            assert_eq!(
                outcome,
                &CExpressionOutcome::Value(int32(u32::try_from(index).unwrap()))
            );
        }
    }

    fn logical_pointer_read(
        memory: &CMemory,
        address: &Pointer,
        context: &PureFactContext,
    ) -> Pointer {
        let paths = evaluate_logical_memory_load_paths(
            memory,
            address.clone(),
            CType::Int64Pointer,
            Vec::new().into(),
            Vec::new(),
            context,
        );
        let [path] = paths.as_slice() else {
            panic!("one logical read expected");
        };
        assert!(
            !path.facts.has_path_conditions(),
            "logical read must not add path conditions"
        );
        assert!(
            path.obligations.is_empty(),
            "logical terms grant no read authority"
        );
        let CExpressionOutcome::Value(CValue::Pointer(value)) = &path.outcome else {
            panic!("pointer value expected");
        };
        value.pointer().clone()
    }

    #[test]
    fn logical_pointer_field_alias_keeps_loaded_supplier_base_after_call() {
        let _session = crate::kernel::VerificationSession::enter();
        let owner = Pointer::symbolic(Variable(955_920))
            .offset_by_elements(Bitvector32Term::Variable(Variable(955_921)), 4);
        let alias = Pointer::symbolic(Variable(955_922));
        let target = Pointer::symbolic(Variable(955_923));
        let right = owner.offset_by_bytes(8);
        let before = CMemory::new().store(
            right.clone(),
            CValue::typed_pointer(target.clone(), CType::Int64Pointer),
        );
        let bare = PureFactContext::new();
        let write =
            CMemoryRange::new_with_element_width(owner.clone(), 0u32.into(), 2u32.into(), 4);
        let memory = before.with_call_memory_havoc(Variable(955_924), &[write], &bare, None);
        let resources = ResourceContext::new().unchecked_with_fact(CResourceFact::view_memory(
            CMemoryRange::new_with_element_width(owner.clone(), 2u32.into(), 4u32.into(), 4),
        ));
        resources.synchronize_memory_equalities(&bare);
        let without_alias = bare
            .clone()
            .assume_proposition(Proposition::CResourceComposition(resources));
        let context = without_alias.clone().assume_condition(
            ConditionTerm::pointer_equal(owner.clone(), alias.clone()),
            true,
        );
        let read = |memory: &CMemory, address: Pointer, context: &PureFactContext| {
            let paths = evaluate_logical_memory_load_paths(
                memory,
                address,
                CType::Int64Pointer,
                ExecutionFacts::new(),
                Vec::new(),
                context,
            );
            let [path] = paths.as_slice() else {
                panic!("one logical read");
            };
            path.outcome.clone()
        };
        let direct = read(&memory, right.clone(), &context);
        assert_eq!(
            direct,
            CExpressionOutcome::Value(CValue::typed_pointer(target, CType::Int64Pointer))
        );
        assert_eq!(read(&memory, alias.offset_by_bytes(8), &context), direct);
        assert_ne!(
            read(&memory, alias.offset_by_bytes(8), &without_alias),
            direct
        );
        assert_ne!(read(&memory, alias.offset_by_bytes(16), &context), direct);
        let changed = memory.store(
            right,
            CValue::typed_pointer(Pointer::symbolic(Variable(955_925)), CType::Int64Pointer),
        );
        let updated = read(&changed, alias.offset_by_bytes(8), &context);
        assert_eq!(updated, read(&changed, owner.offset_by_bytes(8), &context));
        assert_ne!(updated, direct);
        assert!(!ResourceContext::new().permits_memory_read(
            &alias.offset_by_bytes(8),
            8,
            &context
        ));
    }

    #[test]
    fn program_and_logical_reads_share_an_opaque_alias_load_identity() {
        let _session = crate::kernel::VerificationSession::enter();
        let owner = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(95_000)), 4),
        };
        let alias = Pointer::symbolic(Variable(95_001));
        let memory = CMemory::new();
        let empty = PureFactContext::new();
        let resources = ResourceContext::new_with_equalities(&empty).unchecked_with_fact(
            CResourceFact::own_memory(CMemoryRange::new_with_element_width(
                owner.clone(),
                0u32.into(),
                1u32.into(),
                8,
            )),
        );
        let without_alias = empty
            .assume_proposition(Proposition::CResourceComposition(resources))
            .assume_proposition(Proposition::CMemoryReadDefined {
                memory: memory.clone(),
                pointer: alias.clone(),
                value_type: CType::UInt64,
            })
            .assume_proposition(Proposition::CMemoryLoadable {
                memory: memory.clone(),
                base: alias.clone(),
                bytes: 8u32.into(),
                wide: false,
            });
        let context = without_alias.clone().assume_condition(
            ConditionTerm::pointer_equal(owner.clone(), alias.clone()),
            true,
        );
        let logical = evaluate_logical_memory_load_paths(
            &memory,
            alias.clone(),
            CType::UInt64,
            Vec::new().into(),
            Vec::new(),
            &context,
        );
        let program = evaluate_c_memory_load_paths(
            &memory,
            alias.clone(),
            CType::UInt64,
            Vec::new().into(),
            Vec::new(),
            &context,
            true,
            false,
            None,
            None,
        );
        assert_eq!(logical.len(), 1);
        assert_eq!(program.len(), 1);
        assert!(matches!(logical[0].outcome, CExpressionOutcome::Value(_)));
        assert_eq!(program[0].outcome, logical[0].outcome);
        let unrelated = evaluate_logical_memory_load_paths(
            &memory,
            alias.clone(),
            CType::UInt64,
            Vec::new().into(),
            Vec::new(),
            &without_alias,
        );
        assert_ne!(
            unrelated[0].outcome, logical[0].outcome,
            "an unpublished address equality must not merge different reads"
        );
        // The C read may have been named before this model alias existed.
        // Reusing the materialized cell must preserve that earlier value.
        let CExpressionOutcome::Value(earlier_value) = &unrelated[0].outcome else {
            panic!("the earlier read should denote a scalar value");
        };
        let CExpressionOutcome::Value(alias_value) = &logical[0].outcome else {
            panic!("the newly exposed alias should denote a scalar value");
        };
        let cached_memory = memory
            .clone()
            .materialize_named_cell(alias.clone(), earlier_value.clone())
            .materialize_named_cell(owner.clone(), alias_value.clone());
        let reloaded = evaluate_logical_memory_load_paths(
            &cached_memory,
            alias.clone(),
            CType::UInt64,
            Vec::new().into(),
            Vec::new(),
            &context,
        );
        let program_reload = evaluate_c_memory_load_paths(
            &cached_memory,
            alias,
            CType::UInt64,
            Vec::new().into(),
            Vec::new(),
            &context,
            true,
            false,
            None,
            None,
        );
        assert_eq!(reloaded.len(), 1);
        assert_eq!(program_reload.len(), 1);
        assert_eq!(reloaded[0].outcome, unrelated[0].outcome);
        assert_eq!(program_reload[0].outcome, reloaded[0].outcome);
        let displaced = evaluate_logical_memory_load_paths(
            &memory,
            owner.offset_by_bytes(8),
            CType::UInt64,
            Vec::new().into(),
            Vec::new(),
            &context,
        );
        assert_ne!(
            displaced[0].outcome, logical[0].outcome,
            "different field offsets must retain different load identities"
        );
    }

    #[test]
    fn logical_pointer_read_definitions_are_not_hypotheses_or_read_authority() {
        let memory = CMemory::new();
        let a = Pointer::symbolic(Variable(92_200));
        let b = Pointer::symbolic(Variable(92_201));
        let before = PureFactContext::new();
        let sibling = before.clone();
        let x = logical_pointer_read(&memory, &a, &before);
        let y = logical_pointer_read(&memory, &b, &before);
        assert!(before.pure_facts().is_empty());
        assert!(!before.pointers_known_equal(&x, &y));
        let branch = before
            .clone()
            .assume_condition(ConditionTerm::pointer_equal(a.clone(), b.clone()), true);
        assert!(branch.pointers_known_equal(&x, &y));
        assert!(!sibling.pointers_known_equal(&x, &y));
        assert!(!before.pointers_known_equal(&x, &y));
        assert!(!ResourceContext::new().permits_memory_read(&b, 8, &branch));
        let changed = memory.store(
            a.clone(),
            CValue::typed_pointer(Pointer::symbolic(Variable(92_202)), CType::Int64Pointer),
        );
        let z = logical_pointer_read(&changed, &a, &branch);
        assert!(!branch.pointers_known_equal(&x, &z));
        assert!(!branch.pointers_known_equal(&x, &x.offset_by_bytes(8)));
        // Definitions survive reconstruction, but the required address fact
        // must still be supplied by the new context itself.
        let reconstructed = PureFactContext::new()
            .assume_condition(ConditionTerm::pointer_equal(a.clone(), b.clone()), true);
        assert!(reconstructed.pointers_known_equal(&x, &y));
        assert_eq!(reconstructed.pure_facts().len(), 1);
    }

    #[test]
    fn typed_read_validity_accepts_its_certified_pointer_equation() {
        let _session = crate::kernel::VerificationSession::enter();
        let field = Pointer {
            block: "global:defined-complete-pointer".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let stored =
            CValue::typed_pointer(Pointer::symbolic(Variable(210_290)), CType::Int32Pointer);
        // Forget the materialized cell without changing its stored value.
        // The typed read must recover the complete pointer from its history.
        let memory = CMemory::new()
            .store(field.clone(), stored.clone())
            .without_possible_aliasing_cells(
                &Pointer::symbolic(Variable(210_291)),
                8,
                &PureFactContext::new(),
            );
        assert!(memory.known_value(&field).is_none());
        let view = |bytes| {
            PureFactContext::new().assume_proposition(Proposition::CMemoryLoadable {
                memory: memory.clone(),
                base: field.clone(),
                bytes: Bitvector32Term::Constant(bytes),
                wide: false,
            })
        };
        let context = view(8);
        let paths = evaluate_spec_memory_load_paths(
            &memory,
            field.clone(),
            CType::Int32Pointer,
            ExecutionFacts::new(),
            Vec::new(),
            &context,
        );
        let [path] = paths.as_slice() else {
            panic!("one typed read expected");
        };
        assert_eq!(path.outcome, CExpressionOutcome::Value(stored));
        assert!(path.obligations.is_empty());
        assert_eq!(path.facts.len(), 1);
        assert!(path.facts[0].is_logical_read_equation());
        assert!(!context.proves_exact(path.facts[0].proposition()));
        assert!(!is_load_variable_defining_fact(path.facts[0].proposition()));
        let before = context.fact_counts();
        assert!(context.proves_memory_read_defined(&memory, &field, CType::Int32Pointer));
        assert_eq!(context.fact_counts(), before);
        // Recovering a value and its equation grants no missing read extent.
        assert!(!PureFactContext::new().proves_memory_read_defined(
            &memory,
            &field,
            CType::Int32Pointer,
        ));
        assert!(!view(4).proves_memory_read_defined(&memory, &field, CType::Int32Pointer));
    }

    #[test]
    fn a_symbolic_pointer_read_recovers_the_complete_stored_value() {
        let _session = crate::kernel::VerificationSession::enter();
        let field = Pointer {
            block: "global:symbolic-complete-pointer".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let target = Pointer::symbolic(Variable(210_190));
        let class = crate::kernel::effective_type::CAccessClass::Scalar(
            crate::kernel::effective_type::CScalarClass::Int,
        );
        let stored = CPointerValue::new(target.clone(), CType::Int32Pointer)
            .with_extent(Some(SubobjectExtent {
                start: target,
                width: 4u32.into(),
            }))
            .with_object_class(Some(class.clone()));
        let context = PureFactContext::new();
        let memory = CMemory::new()
            .store(field.clone(), CValue::Pointer(stored.clone()))
            .without_possible_aliasing_cells(&Pointer::symbolic(Variable(210_191)), 8, &context);
        assert!(memory.known_value(&field).is_none());
        let read = |memory: &CMemory| {
            let mut facts = ExecutionFacts::new();
            let CValue::Pointer(value) = canonicalized_symbolic_load_value_with_identity(
                memory,
                &field,
                CType::Int32Pointer,
                &mut facts,
                &context,
                false,
                None,
                LoadPurpose::Logical,
            )
            .unwrap() else {
                panic!("pointer read")
            };
            (value, facts)
        };
        let (value, facts) = read(&memory);
        assert_eq!(value, stored);
        assert_eq!(value.object_class(), Some(class));
        assert_eq!(facts.len(), 1);
        assert!(facts[0].is_logical_read_equation());
        facts[0].retain_pointer_read_definition(&context);
        let current = CPointerValue::new(
            Pointer::loaded_value(&crate::kernel::intern_c_memory_ref(&memory), &field),
            CType::Int32Pointer,
        );
        assert!(context.pointer_designations_match(&current, &stored));
        assert!(context.pointers_known_equal(current.pointer(), stored.pointer()));
        assert!(context.pure_facts().is_empty());
        assert!(
            crate::kernel::equality_graph::logical_pointer_read_term(stored.pointer()).is_none()
        );
        let partial = memory.store(field.offset_by_bytes(4), CValue::UInt32(0u32.into()));
        assert!(!context.pointer_designations_match(&read(&partial).0, &stored));
    }

    #[test]
    fn a_pointer_cast_restores_complete_word_reads_inside_a_numeric_observation() {
        let _session = crate::kernel::VerificationSession::enter();
        let field = Pointer {
            block: "global:scoped-word".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let target = Pointer::symbolic(Variable(210_199));
        let pointer = CPointerValue::new(target.clone(), CType::Int32Pointer)
            .with_extent(Some(SubobjectExtent::constant(target.clone(), 4)));
        let stored = CValue::PointerInteger(PointerIntegerValue {
            numeric: Box::new(CValue::UInt64(Bitvector32Term::pointer_address(target))),
            pointer: Box::new(pointer.clone()),
            kind: PointerIntegerKind::Exact,
        });
        let resources = ResourceContext::new().unchecked_with_fact(CResourceFact::own_memory(
            CMemoryRange::new_with_element_width(field.clone(), 0u32.into(), 1u32.into(), 8),
        ));
        let state = CState::new()
            .with_memory(CMemory::new().store(field.clone(), stored))
            .with_resource_context(resources)
            .with_local("word", CValue::typed_pointer(field, CType::UInt64Pointer));
        let context = PureFactContext::new();
        {
            let _numeric = WordRepresentationScope::enter(false);
            let paths = evaluate_c_expression_paths(
                &state,
                &crate::kernel::api::c_cast(
                    CExpression::Load(Box::new(crate::kernel::api::c_variable("word"))),
                    CType::Int32Pointer,
                ),
                &context,
                &mut ExecutionBudget::default(),
            )
            .unwrap();
            assert_eq!(paths.len(), 1);
            assert_eq!(
                paths[0].outcome,
                CExpressionOutcome::Value(CValue::Pointer(pointer))
            );
            assert!(!WordRepresentationScope::keeps_representation());
        }
        assert!(WordRepresentationScope::keeps_representation());
    }

    #[test]
    fn a_symbolic_word_read_recovers_only_a_complete_stored_pointer_record() {
        let _session = crate::kernel::VerificationSession::enter();
        let field = Pointer {
            block: "global:symbolic-word".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let target = Pointer::symbolic(Variable(210_192));
        let pointer = CPointerValue::new(target.clone(), CType::Int32Pointer).with_extent(Some(
            SubobjectExtent {
                start: target.clone(),
                width: 4u32.into(),
            },
        ));
        let context = PureFactContext::new();
        let read = |memory: &CMemory| {
            canonicalized_symbolic_load_value_with_identity(
                memory,
                &field,
                CType::UInt64,
                &mut ExecutionFacts::new(),
                &context,
                false,
                None,
                LoadPurpose::Logical,
            )
            .unwrap()
        };
        for kind in [PointerIntegerKind::Exact, PointerIntegerKind::Tagged] {
            let bits = Bitvector32Term::pointer_address(target.clone());
            let bits = if kind == PointerIntegerKind::Tagged {
                Bitvector32Term::UInt64BitwiseOr(
                    Box::new(bits),
                    Box::new(Bitvector32Term::UInt64Constant(1)),
                )
            } else {
                bits
            };
            let stored = CValue::PointerInteger(PointerIntegerValue {
                numeric: Box::new(CValue::UInt64(bits)),
                pointer: Box::new(pointer.clone()),
                kind,
            });
            let memory = CMemory::new()
                .store(field.clone(), stored.clone())
                .without_possible_aliasing_cells(
                    &Pointer::symbolic(Variable(210_193)),
                    8,
                    &context,
                );
            assert!(memory.known_value(&field).is_none());
            assert_eq!(read(&memory), stored);
            let partial = memory.store(
                field.clone().offset_by_bytes(4),
                CValue::UInt32(0u32.into()),
            );
            assert_ne!(read(&partial), stored);
            let numeric = CMemory::new().store(field.clone(), stored.numeric_value().clone());
            let CValue::PointerInteger(fresh) = read(&numeric) else {
                panic!("word read")
            };
            assert!(matches!(
                fresh.kind,
                PointerIntegerKind::Word { changed_bits: 0 }
            ));
            assert!(fresh.pointer.extent().is_none());
        }
        assert!(context.pure_facts().is_empty());
    }

    #[test]
    fn a_cached_scalar_prefix_recovers_only_the_complete_stored_pointer() {
        let _session = crate::kernel::VerificationSession::enter();
        let field = Pointer {
            block: "global:cached-pointer-a".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let other = Pointer {
            block: "global:cached-pointer-b".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let address = Pointer::symbolic(Variable(210_172));
        let stored = CPointerValue::new(address.clone(), CType::Int32Pointer).with_extent(Some(
            SubobjectExtent {
                start: address,
                width: 4u32.into(),
            },
        ));
        let memory = CMemory::new()
            .store(field.clone(), CValue::Pointer(stored.clone()))
            .store(other.clone(), CValue::Pointer(stored.clone()));
        let memory = memory
            .without_possible_aliasing_cells(
                &Pointer::symbolic(Variable(210_173)),
                8,
                &PureFactContext::new(),
            )
            .materialize_symbolic_cell(field.clone(), CType::Int32)
            .materialize_symbolic_cell(other.clone(), CType::Int32);
        let context = PureFactContext::new();
        let read = |memory: &CMemory, field: &Pointer| {
            let prefix = memory.known_value(field).expect("cached prefix");
            assert!(matches!(prefix, CValue::Int32(_)));
            let CValue::Pointer(value) = canonicalized_pointer_value_from_int_cell(
                memory,
                field,
                &prefix,
                CType::Int32Pointer,
                &mut ExecutionFacts::new(),
                &context,
                None,
                LoadPurpose::Logical,
            )
            .unwrap() else {
                panic!("pointer read")
            };
            value
        };
        assert_eq!(read(&memory, &field), stored);
        assert_eq!(read(&memory, &other), stored);
        assert!(
            crate::kernel::equality_graph::logical_pointer_read_term(stored.pointer()).is_none()
        );
        let overwritten = memory.store(
            field.clone().offset_by_bytes(4),
            CValue::UInt32(0u32.into()),
        );
        let changed = read(&overwritten, &field);
        assert!(changed.extent().is_none());
        assert!(!context.pointer_designations_match(&changed, &stored));
    }

    #[test]
    fn known_pointer_read_names_require_a_complete_pointer_cell() {
        let _session = crate::kernel::VerificationSession::enter();
        let memory = CMemory::new();
        let source = intern_c_memory_ref(&memory);
        let wide = Pointer::symbolic(Variable(210_100));
        let narrow = Pointer::symbolic(Variable(210_101));
        record_load_access_width(&memory, &wide, crate::kernel::C_POINTER_BYTE_WIDTH);
        record_load_access_width(&memory, &narrow, 4);
        let term = |address: &Pointer| {
            Bitvector32Term::MemoryLoad(source.clone(), Box::new(address.clone()), LoadKind::Bits32)
        };
        assert!(known_pointer_read_variable_for_term(&term(&wide)).is_none());
        let (wide_name, _) = load_variable_for_term(&term(&wide)).unwrap();
        let (narrow_name, _) = load_variable_for_term(&term(&narrow)).unwrap();
        assert_eq!(
            known_pointer_read_variable_for_term(&term(&wide)),
            Some(wide_name)
        );
        assert!(known_pointer_read_variable_for_term(&term(&narrow)).is_none());
        let selected = Pointer::symbolic(Variable(210_102));
        for (value, expected) in [
            (
                CValue::Int32(Bitvector32Term::Variable(wide_name)),
                Some(wide_name),
            ),
            (CValue::Int32(Bitvector32Term::Variable(narrow_name)), None),
            (
                CValue::Int32(Bitvector32Term::Variable(Variable(210_103))),
                None,
            ),
            (CValue::UInt64(Bitvector32Term::UInt64Constant(0)), None),
        ] {
            let cached = memory
                .clone()
                .materialize_named_cell(selected.clone(), value);
            let read = Bitvector32Term::MemoryLoad(
                intern_c_memory_ref(&cached),
                Box::new(selected.clone()),
                LoadKind::Bits32,
            );
            assert_eq!(known_pointer_read_variable_for_term(&read), expected);
        }
        let wrong_kind = Bitvector32Term::MemoryLoad(source, Box::new(wide), LoadKind::Bits64);
        assert!(known_pointer_read_variable_for_term(&wrong_kind).is_none());
    }

    #[test]
    fn checked_function_pointer_reads_reconcile_cached_aliases_without_leaking_evidence() {
        let _session = crate::kernel::VerificationSession::enter();
        let table = Pointer {
            block: "global:callback-table".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let argument = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Int32Scaled {
                value: Box::new(Bitvector32Term::Variable(Variable(210_510))),
                byte_width: 4,
            },
        };
        let target = Pointer::function("callback");
        let replacement = Pointer::function("replacement");
        let c_type = CType::FunctionPointer(CallbackSignature::UNSPECIFIED);
        let memory = CMemory::new().store(
            table.offset_by_bytes(8),
            CValue::typed_pointer(target.clone(), c_type),
        );
        let source = intern_c_memory_ref(&memory);
        let seeded =
            memory
                .clone()
                .with_seeded_cells(argument.offset_by_bytes(8), 4, c_type, 0, 2, source);
        let bare = PureFactContext::new();
        let alias = Proposition::ConditionIs(
            ConditionTerm::pointer_equal(argument.clone(), table.clone()),
            true,
        );
        let context = bare.clone().assume_proposition(alias.clone());
        let paths = evaluate_c_memory_load_paths(
            &seeded,
            argument.offset_by_bytes(8),
            c_type,
            ExecutionFacts::new(),
            Vec::new(),
            &context,
            true,
            false,
            None,
            None,
        );
        let [path] = paths.as_slice() else {
            panic!("one checked read expected");
        };
        let CExpressionOutcome::Value(CValue::Pointer(read)) = &path.outcome else {
            panic!("function pointer expected");
        };
        assert!(path.facts.iter().any(|fact| matches!(
            fact.generated_load_binding(),
            Some(GeneratedLoadBinding::Exact {
                typed_pointer_value: Some(_),
                ..
            })
        )));
        let known = path.facts.iter().fold(context.clone(), |context, fact| {
            context.assume_proposition(fact.proposition().clone())
        });
        let merged =
            crate::kernel::reasoning::merge_facts(&ExecutionFacts::new(), &path.facts, &known)
                .unwrap();
        assert!(merged.iter().any(|fact| matches!(
            fact.generated_load_binding(),
            Some(GeneratedLoadBinding::Exact {
                typed_pointer_value: Some(_),
                ..
            })
        )));
        let plain: ExecutionFacts = path
            .facts
            .iter()
            .map(|fact| ExecutionPureFact::new(fact.proposition().clone()))
            .collect();
        assert!(
            crate::kernel::reasoning::merge_facts(&ExecutionFacts::new(), &plain, &known)
                .unwrap()
                .is_empty()
        );
        let mut published =
            crate::kernel::proof::ProofFacts::from_ordered(std::slice::from_ref(&alias));
        for fact in &path.facts {
            published = published.with_kernel_checked_fact(fact.proposition().clone());
        }
        let undecorated = published.clone();
        for fact in &path.facts {
            published.retain_checked_read_fact(fact);
        }
        assert!(
            published
                .assumptions()
                .pointers_known_equal(read.pointer(), &target)
        );
        assert!(
            !undecorated
                .assumptions()
                .pointers_known_equal(read.pointer(), &target)
        );
        assert!(!context.pointers_known_equal(read.pointer(), &target));
        for fact in &path.facts {
            fact.retain_pointer_read_definition(&context);
        }
        assert!(context.pointers_known_equal(read.pointer(), &target));
        assert!(!bare.pointers_known_equal(read.pointer(), &target));
        assert!(
            !context
                .without_exact_fact(&alias)
                .pointers_known_equal(read.pointer(), &target)
        );
        assert!(!ResourceContext::new().permits_memory_read(
            &argument.offset_by_bytes(8),
            8,
            &context
        ));
        let changed = memory.store(
            table.offset_by_bytes(8),
            CValue::typed_pointer(replacement.clone(), c_type),
        );
        let changed_source = intern_c_memory_ref(&changed);
        let changed_seeded =
            changed.with_seeded_cells(argument.offset_by_bytes(8), 4, c_type, 0, 2, changed_source);
        let changed_paths = evaluate_c_memory_load_paths(
            &changed_seeded,
            argument.offset_by_bytes(8),
            c_type,
            ExecutionFacts::new(),
            Vec::new(),
            &context,
            true,
            false,
            None,
            None,
        );
        let [changed_path] = changed_paths.as_slice() else {
            panic!("one changed read expected");
        };
        let CExpressionOutcome::Value(CValue::Pointer(changed_read)) = &changed_path.outcome else {
            panic!("function pointer expected");
        };
        for fact in &changed_path.facts {
            fact.retain_pointer_read_definition(&context);
        }
        assert!(context.pointers_known_equal(changed_read.pointer(), &replacement));
        assert!(!context.pointers_known_equal(read.pointer(), changed_read.pointer()));
    }

    #[test]
    fn canonical_pointer_names_do_not_redefine_a_scalar_prefix_source() {
        let _session = crate::kernel::VerificationSession::enter();
        let base = CMemory::new();
        let source = Pointer::symbolic(Variable(940_095));
        let destination = Pointer::symbolic(Variable(940_096));
        let CValue::Pointer(original) = base.symbolic_pointer_load(&source, 4, CType::Int32Pointer)
        else {
            unreachable!()
        };
        let (block, bits, width) = original.pointer().as_loaded().unwrap();
        let (variable, _) = load_variable_for_term(bits).unwrap();
        let canonical = Pointer::loaded(block.clone(), Bitvector32Term::Variable(variable), width);
        let cached = base.store(
            destination.clone(),
            CValue::Int32(Bitvector32Term::Variable(variable)),
        );
        let CValue::Pointer(prefix) =
            cached.symbolic_pointer_load(&destination, 4, CType::Int32Pointer)
        else {
            unreachable!()
        };
        let (_, prefix_bits, _) = prefix.pointer().as_loaded().unwrap();
        assert_eq!(
            canonical_term(prefix_bits),
            Bitvector32Term::Variable(variable)
        );
        let graph = crate::kernel::equality_graph::EqualityGraph::default();
        graph.retain_canonical_pointer_read_definition(prefix.pointer());
        assert!(
            crate::kernel::equality_graph::logical_pointer_read_for_offset(&canonical.offset)
                .is_none()
        );
        graph.retain_canonical_pointer_read_definition(original.pointer());
        assert!(
            crate::kernel::equality_graph::logical_pointer_read_for_offset(&canonical.offset)
                .is_some()
        );
    }

    #[test]
    fn specification_c_pointer_reads_retain_their_logical_names() {
        let _session = crate::kernel::VerificationSession::enter();
        let memory = CMemory::new();
        let a = Pointer::symbolic(Variable(940_097));
        let b = Pointer::symbolic(Variable(940_098));
        let context = PureFactContext::new()
            .assume_condition(ConditionTerm::pointer_equal(a.clone(), b.clone()), true);
        let read = |address: &Pointer| {
            let paths = evaluate_c_memory_load_paths(
                &memory,
                address.clone(),
                CType::Int64Pointer,
                ExecutionFacts::new(),
                Vec::new(),
                &context,
                true,
                false,
                None,
                None,
            );
            let CExpressionOutcome::Value(CValue::Pointer(pointer)) = &paths[0].outcome else {
                panic!("typed read");
            };
            pointer.pointer().clone()
        };
        let x = read(&a);
        let y = read(&b);
        assert!(!context.pointers_known_equal(&x, &y));
        {
            let _specification = SpecificationReadScope::enter();
            assert_eq!(read(&a), x);
            assert_eq!(read(&b), y);
        }
        assert!(context.pointers_known_equal(&x, &y));
    }

    #[test]
    fn logical_cached_raw_pointer_reads_retain_their_load_variables() {
        let _session = crate::kernel::VerificationSession::enter();
        let base = CMemory::new();
        let origin = intern_c_memory_ref(&base);
        let a = Pointer::loaded(
            PointerBlock::ExternalArgument,
            Bitvector32Term::Variable(Variable(940_091)),
            4,
        );
        let b = Pointer::loaded(
            PointerBlock::ExternalArgument,
            Bitvector32Term::Variable(Variable(940_092)),
            4,
        );
        let field_a = a.clone().offset_by_bytes(8);
        let field_b = b.clone().offset_by_bytes(8);
        let first = base.symbolic_pointer_load(&field_a, 4, CType::Int32Pointer);
        let second = base.symbolic_pointer_load(&field_b, 4, CType::Int32Pointer);
        let slot_a = Pointer {
            block: "local:raw-a".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let slot_b = Pointer {
            block: "local:raw-b".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let memory = base
            .store(slot_a.clone(), first)
            .store(slot_b.clone(), second);
        let context = PureFactContext::new().assume_condition(
            ConditionTerm::pointer_value_equal(
                CPointerValue::new(a, CType::Int32Pointer),
                CPointerValue::new(b, CType::Int32Pointer),
            ),
            true,
        );
        let canonical = |field: &Pointer| {
            Pointer::loaded(
                PointerBlock::ExternalArgument,
                canonical_term(&Bitvector32Term::MemoryLoad(
                    origin.clone(),
                    Box::new(field.clone()),
                    LoadKind::Bits32,
                )),
                4,
            )
        };
        let direct = canonical(&field_a);
        let indirect = canonical(&field_b);
        assert!(!context.equality_graph.are_equal(&direct, &indirect));
        for slot in [&slot_a, &slot_b] {
            let paths = evaluate_logical_memory_load_paths(
                &memory,
                slot.clone(),
                CType::Int32Pointer,
                ExecutionFacts::new(),
                Vec::new(),
                &context,
            );
            assert!(matches!(
                &paths[0].outcome,
                CExpressionOutcome::Value(CValue::Pointer(_))
            ));
        }
        assert!(context.equality_graph.are_equal(&direct, &indirect));
    }

    #[test]
    fn logical_pointer_read_registration_invalidates_an_earlier_memoized_miss() {
        let memory = CMemory::new();
        let a = Pointer::symbolic(Variable(92_210));
        let b = Pointer::symbolic(Variable(92_211));
        let context = PureFactContext::new()
            .assume_condition(ConditionTerm::pointer_equal(a.clone(), b.clone()), true);
        let program_read = |address: &Pointer| {
            let paths = evaluate_c_memory_load_paths(
                &memory,
                address.clone(),
                CType::Int64Pointer,
                Vec::new().into(),
                Vec::new(),
                &context,
                true,
                false,
                None,
                None,
            );
            let CExpressionOutcome::Value(CValue::Pointer(value)) = &paths[0].outcome else {
                panic!("pointer read");
            };
            value.pointer().clone()
        };
        let x = program_read(&a);
        let y = program_read(&b);
        let _scope = context.enter_id_scope();
        assert!(!pointers_proven_equal_for_memory_resolution(
            &x, &y, &context
        ));
        // Warm compound-query dependency misses before producer metadata
        // appears. New definitions must invalidate those misses as well.
        for _ in 0..2 {
            assert!(!context.pointers_known_equal(&x.offset_by_bytes(8), &y.offset_by_bytes(8)));
        }
        assert_eq!(logical_pointer_read(&memory, &a, &context), x);
        assert_eq!(logical_pointer_read(&memory, &b, &context), y);
        assert!(pointers_proven_equal_for_memory_resolution(
            &x, &y, &context
        ));
        assert!(context.pointers_known_equal(&x.offset_by_bytes(8), &y.offset_by_bytes(8)));
    }

    #[test]
    fn cached_typed_read_retains_exact_definition_without_admitting_facts() {
        let context = PureFactContext::new();
        let address = Pointer::symbolic(Variable(92_310));
        let snapshot = intern_c_memory(CMemory::new());
        let load = Bitvector32Term::MemoryLoad(
            snapshot.clone(),
            Box::new(address.clone()),
            crate::kernel::LoadKind::Bits32,
        );
        let (variable, _) = load_variable_for_term(&load).expect("load identity");
        let mut facts = crate::kernel::ExecutionFacts::new();
        let source = test_load_source(0);
        let CValue::Pointer(value) = canonicalized_pointer_value_from_int_cell(
            &snapshot,
            &address,
            &CValue::Int32(Bitvector32Term::Variable(variable)),
            CType::Int64Pointer,
            &mut facts,
            &context,
            Some(&source),
            LoadPurpose::Program,
        )
        .expect("cached typed pointer") else {
            panic!("expected pointer");
        };
        let application = Pointer::loaded_value(&snapshot, &address);
        assert!(!context.pointers_known_equal(value.pointer(), &application));
        assert_eq!(facts.len(), 1);
        let fact = &facts[0];
        assert!(
            matches!(fact.generated_load_binding(), Some(GeneratedLoadBinding::Exact {
            typed_pointer_value: Some(recorded), ..
        }) if recorded == value.pointer())
        );
        assert_eq!(fact.generated_load_source_events().len(), 1);
        assert_eq!(fact.generated_load_source_events()[0].source(), &source);
        assert!(matches!(fact.generated_load_source_events()[0].binding(),
            GeneratedLoadBinding::Exact { typed_pointer_value: Some(recorded), .. }
                if recorded == value.pointer()));
        // An ordinary proposition, even with copied metadata, is not a producer.
        let forged = ExecutionPureFact::new(fact.proposition().clone())
            .with_generated_load_binding(fact.generated_load_binding().unwrap().clone());
        forged.retain_pointer_read_definition(&context);
        assert!(!context.pointers_known_equal(value.pointer(), &application));
        fact.retain_pointer_read_definition(&context);
        assert!(context.pointers_known_equal(value.pointer(), &application));
        assert!(context.pure_facts().is_empty());
        assert!(
            ResourceContext::new()
                .memory_write_range(value.pointer(), 8, &context)
                .is_none()
        );
        let sibling = PureFactContext::new();
        assert!(sibling.pointers_known_equal(value.pointer(), &application));
        assert!(sibling.pure_facts().is_empty());
        let later =
            intern_c_memory(CMemory::new().with_block(PointerBlock::from("global:other"), 8));
        assert!(
            !context
                .pointers_known_equal(value.pointer(), &Pointer::loaded_value(&later, &address))
        );
    }

    #[test]
    fn cached_pointer_prefix_cannot_recover_bounds_after_an_upper_half_write() {
        let _session = crate::kernel::VerificationSession::enter();
        let address = Pointer::symbolic(Variable(92_312));
        let before = CMemory::new();
        let (variable, _) = load_variable_for_term(&Bitvector32Term::MemoryLoad(
            intern_c_memory_ref(&before),
            Box::new(address.clone()),
            LoadKind::Bits32,
        ))
        .unwrap();
        let cached = CValue::Int32(Bitvector32Term::Variable(variable));
        let read = |memory: &CMemory, context: &PureFactContext| {
            let CValue::Pointer(value) = canonicalized_pointer_value_from_int_cell(
                memory,
                &address,
                &cached,
                CType::Int32Pointer,
                &mut ExecutionFacts::new(),
                context,
                None,
                LoadPurpose::Logical,
            )
            .unwrap() else {
                panic!("pointer read")
            };
            value
        };
        let original = read(&before, &PureFactContext::new());
        let base = Pointer {
            block: PointerBlock::Heap(92_312),
            offset: PointerOffsetTerm::Constant(0),
        };
        let bounded = CPointerValue::new(base.clone(), CType::Int32Pointer).with_extent(Some(
            SubobjectExtent {
                start: base,
                width: 4u32.into(),
            },
        ));
        let context = PureFactContext::new().assume_condition(
            ConditionTerm::pointer_value_equal(original.clone(), bounded.clone()),
            true,
        );
        assert_eq!(
            context
                .pointer_value_at_entry(&original)
                .extent()
                .unwrap()
                .width,
            Bitvector32Term::Constant(4)
        );
        let unchanged = before.clone().with_block("unrelated-pointer-cache", 4);
        assert_eq!(
            context
                .pointer_value_at_entry(&read(&unchanged, &context))
                .extent()
                .unwrap()
                .width,
            Bitvector32Term::Constant(4)
        );
        let observed = before
            .clone()
            .materialize_symbolic_cell(address.clone(), CType::Int32)
            .materialize_symbolic_cell(address.clone().offset_by_bytes(4), CType::Int32);
        let observed_read = read(&observed, &context);
        assert_eq!(observed_read.pointer(), original.pointer());
        assert!(context.pointer_designations_match(&observed_read, &bounded));
        assert_eq!(
            context
                .pointer_value_at_entry(&observed_read)
                .extent()
                .unwrap()
                .width,
            Bitvector32Term::Constant(4)
        );
        let overwritten = observed.store(
            address.clone().offset_by_bytes(4),
            CValue::UInt32(0u32.into()),
        );
        let changed = read(&overwritten, &context);
        assert_eq!(
            changed.pointer(),
            original.pointer(),
            "the cached numeric prefix is unchanged; it cannot supply bounds"
        );
        assert!(!context.pointer_designations_match(&changed, &bounded));
        assert!(context.pointer_value_at_entry(&changed).extent().is_none());
    }

    #[test]
    fn cached_volatile_pointer_read_has_no_retainable_definition() {
        let context = PureFactContext::new();
        let address = Pointer::symbolic(Variable(92_311));
        let snapshot = intern_c_memory(CMemory::new());
        let load = Bitvector32Term::MemoryLoad(
            snapshot.clone(),
            Box::new(address.clone()),
            crate::kernel::LoadKind::Bits32,
        );
        let (variable, _) = load_variable_for_term(&load).expect("load identity");
        let mut facts = crate::kernel::ExecutionFacts::new();
        let CValue::Pointer(value) = canonicalized_pointer_value_from_int_cell(
            &snapshot,
            &address,
            &CValue::Int32(Bitvector32Term::Variable(variable)),
            CType::Int64Pointer,
            &mut facts,
            &context,
            None,
            LoadPurpose::VolatileProgram,
        )
        .expect("cached volatile pointer") else {
            panic!("expected pointer");
        };
        for fact in &facts {
            fact.retain_pointer_read_definition(&context);
        }
        assert!(
            !context
                .pointers_known_equal(value.pointer(), &Pointer::loaded_value(&snapshot, &address))
        );
    }

    #[test]
    fn completed_pointer_reads_join_through_later_graph_address_equality() {
        let memory = CMemory::new();
        let snapshot = intern_c_memory(memory.clone());
        let a = Pointer::symbolic(Variable(92_100));
        let b = Pointer::symbolic(Variable(92_101));
        let read = |address: &Pointer, volatile| {
            let paths = evaluate_c_memory_load_paths(
                &memory,
                address.clone(),
                CType::Int64Pointer,
                Vec::new().into(),
                Vec::new(),
                &PureFactContext::new(),
                true,
                volatile,
                None,
                None,
            );
            assert_eq!(paths.len(), 1);
            let CExpressionOutcome::Value(CValue::Pointer(value)) = &paths[0].outcome else {
                panic!("expected a pointer read: {:?}", paths[0].outcome);
            };
            (value.pointer().clone(), paths[0].facts.clone())
        };
        let (x, x_facts) = read(&a, false);
        let (y, y_facts) = read(&b, false);
        let empty = PureFactContext::new();
        assert!(!empty.pointers_known_equal(&x, &Pointer::loaded_value(&snapshot, &a)));
        let available = x_facts
            .iter()
            .chain(&y_facts)
            .fold(empty.clone(), |context, fact| {
                context.assume_execution_pure_fact(fact)
            });
        assert!(available.pointers_known_equal(&x, &Pointer::loaded_value(&snapshot, &a)));
        assert!(!empty.pointers_known_equal(&x, &y));
        let branch = available
            .clone()
            .assume_condition(ConditionTerm::pointer_equal(a.clone(), b.clone()), true);
        assert!(branch.equality_graph.are_equal(&a, &b));
        assert!(
            branch
                .equality_graph
                .are_pointer_loads_equal(&snapshot, &a, &b)
        );
        assert!(branch.pointers_known_equal(&x, &y));
        let owner = ResourceContext::new_with_equalities(&available).unchecked_with_fact(
            CResourceFact::own_memory(CMemoryRange::new_with_element_width(
                x.clone(),
                0u32.into(),
                1u32.into(),
                4,
            )),
        );
        assert!(!owner.permits_memory_read(&y, 4, &available));
        assert!(owner.memory_write_range(&y, 4, &available).is_none());
        assert!(owner.permits_memory_read(&y, 4, &branch));
        assert!(owner.memory_write_range(&y, 4, &branch).is_some());
        let address_first = empty
            .clone()
            .assume_condition(ConditionTerm::pointer_equal(a.clone(), b.clone()), true);
        let address_first = x_facts
            .iter()
            .chain(&y_facts)
            .fold(address_first, |context, fact| {
                context.assume_execution_pure_fact(fact)
            });
        assert!(address_first.pointers_known_equal(&x, &y));
        assert!(!empty.pointers_known_equal(&x, &y));
        // Fork before filing the x read's defining fact. This sibling has
        // the y read and the late address equality, but never received the
        // bridge that would identify x with the loaded pointer.
        let without_x = x_facts
            .iter()
            .skip(1)
            .chain(&y_facts)
            .fold(empty.clone(), |context, fact| {
                context.assume_execution_pure_fact(fact)
            })
            .assume_condition(ConditionTerm::pointer_equal(a.clone(), b.clone()), true);
        assert!(!without_x.pointers_known_equal(&x, &Pointer::loaded_value(&snapshot, &a)));
        assert!(!owner.permits_memory_read(&y, 4, &without_x));
        let address_only = empty
            .clone()
            .assume_condition(ConditionTerm::pointer_equal(a.clone(), b), true);
        assert!(!address_only.pointers_known_equal(&x, &Pointer::loaded_value(&snapshot, &a)));
        let later = intern_c_memory(
            memory
                .clone()
                .with_block(PointerBlock::from("global:later"), 8),
        );
        assert!(!available.pointers_known_equal(&x, &Pointer::loaded_value(&later, &a)));
        let volatile_address = Pointer::symbolic(Variable(92_102));
        let (volatile_value, volatile_facts) = read(&volatile_address, true);
        let volatile_context = volatile_facts.iter().fold(empty, |context, fact| {
            context.assume_execution_pure_fact(fact)
        });
        assert!(!volatile_context.pointers_known_equal(
            &volatile_value,
            &Pointer::loaded_value(&snapshot, &volatile_address),
        ));
        let (volatile_same, volatile_same_facts) = read(&a, true);
        let volatile_only = volatile_same_facts
            .iter()
            .fold(PureFactContext::new(), |context, fact| {
                context.assume_execution_pure_fact(fact)
            });
        let normal_only = x_facts
            .iter()
            .fold(PureFactContext::new(), |context, fact| {
                context.assume_execution_pure_fact(fact)
            });
        assert_eq!(normal_only.condition_facts, volatile_only.condition_facts);
        assert_ne!(
            normal_only.memo_fingerprint(),
            volatile_only.memo_fingerprint()
        );
        assert_ne!(normal_only, volatile_only);
        assert!(
            !volatile_only
                .pointers_known_equal(&volatile_same, &Pointer::loaded_value(&snapshot, &a),)
        );
        let scalar_paths = evaluate_c_memory_load_paths(
            &memory,
            a.clone(),
            CType::Int64,
            Vec::new().into(),
            Vec::new(),
            &PureFactContext::new(),
            true,
            false,
            None,
            None,
        );
        assert_eq!(scalar_paths.len(), 1);
        let scalar_only = scalar_paths[0]
            .facts
            .iter()
            .fold(PureFactContext::new(), |context, fact| {
                context.assume_execution_pure_fact(fact)
            });
        assert!(!scalar_only.pointers_known_equal(&x, &Pointer::loaded_value(&snapshot, &a)));
    }

    /// Explicit normalization checks a typed full-width pointer read and its
    /// cited value relation; offsets alone and stale/partial stores do not suffice.
    #[test]
    fn normalize_recorded_pointer_values_checks_selected_facts_and_width() {
        use crate::kernel::proof::ProofFacts;
        use crate::kernel::proof::fact_reasoning::normalize_using_conditions;
        let _session = crate::kernel::VerificationSession::enter();
        let address = Pointer::symbolic(Variable(99_100));
        let stored = Pointer::symbolic(Variable(99_101));
        let wrong = Pointer::symbolic(Variable(99_102));
        let empty = PureFactContext::new();
        let equality = |left: &Pointer, right: &Pointer| {
            Proposition::ConditionIs(
                ConditionTerm::pointer_equal(left.clone(), right.clone()),
                true,
            )
        };
        let memory = CMemory::new().store(
            address.clone(),
            CValue::typed_pointer(stored.clone(), CType::Int32Pointer),
        );
        let read = |memory: CMemory, address: &Pointer, variable, width| {
            record_load_access_width(&memory, address, width);
            let value = Pointer::symbolic(Variable(variable));
            empty.register_pointer_read(&value, &intern_c_memory(memory), address);
            value
        };
        let value = read(memory.clone(), &address, 99_103, 8);
        let premise = equality(&stored, &Pointer::null());
        let facts = ProofFacts::from_ordered(std::slice::from_ref(&premise));
        for goal in [
            equality(&value, &Pointer::null()),
            equality(&Pointer::null(), &value),
        ] {
            assert!(
                normalize_using_conditions(&goal, std::slice::from_ref(&premise), &facts).is_ok()
            );
            assert!(
                normalize_using_conditions(&goal, &[], &ProofFacts::from_ordered(&[])).is_err()
            );
        }
        assert!(
            normalize_using_conditions(
                &equality(&value, &wrong),
                std::slice::from_ref(&premise),
                &facts
            )
            .is_err()
        );
        assert!(
            normalize_using_conditions(
                &equality(&value.offset_by_bytes(4), &Pointer::null()),
                std::slice::from_ref(&premise),
                &facts
            )
            .is_err()
        );
        let changed = memory
            .without_possible_aliasing_cells(&address.offset_by_bytes(4), 4, &empty)
            .store(
                address.offset_by_bytes(4),
                CValue::Int32(Bitvector32Term::Constant(0)),
            );
        let changed = read(changed, &address, 99_104, 8);
        assert!(
            normalize_using_conditions(
                &equality(&changed, &Pointer::null()),
                std::slice::from_ref(&premise),
                &facts
            )
            .is_err()
        );
        let narrow_address = Pointer::symbolic(Variable(99_105));
        let narrow = read(
            CMemory::new().store(
                narrow_address.clone(),
                CValue::typed_pointer(stored, CType::Int32Pointer),
            ),
            &narrow_address,
            99_106,
            4,
        );
        assert!(
            normalize_using_conditions(
                &equality(&narrow, &Pointer::null()),
                std::slice::from_ref(&premise),
                &facts
            )
            .is_err()
        );
        let scalar_address = Pointer::symbolic(Variable(99_107));
        let scalar = read(
            CMemory::new().store(
                scalar_address.clone(),
                CValue::UInt64(Bitvector32Term::UInt64Constant(0)),
            ),
            &scalar_address,
            99_108,
            8,
        );
        assert!(
            normalize_using_conditions(
                &equality(&scalar, &Pointer::null()),
                &[],
                &ProofFacts::from_ordered(&[])
            )
            .is_err()
        );
    }

    /// Same-block pointer equality is lowered to offset equality. It still
    /// needs an exact typed read, including its stride and unambiguous origin.
    #[test]
    fn normalize_recorded_pointer_offsets_checks_definition_and_stride() {
        use crate::kernel::proof::ProofFacts;
        use crate::kernel::proof::fact_reasoning::normalize_using_conditions;
        let _session = crate::kernel::VerificationSession::enter();
        let context = PureFactContext::new();
        let facts = ProofFacts::from_ordered(&[]);
        let address = Pointer::symbolic(Variable(103_001));
        let stored = Pointer::loaded(
            PointerBlock::ExternalArgument,
            Bitvector32Term::Variable(Variable(103_002)),
            4,
        );
        let read = Pointer::loaded(
            PointerBlock::ExternalArgument,
            Bitvector32Term::Variable(Variable(103_003)),
            4,
        );
        let memory = CMemory::new().store(
            address.clone(),
            CValue::typed_pointer(stored.clone(), CType::Int32Pointer),
        );
        record_load_access_width(&memory, &address, 8);
        context.register_pointer_read(&read, &intern_c_memory(memory.clone()), &address);
        let equality = |left: &PointerOffsetTerm, right: &PointerOffsetTerm| {
            Proposition::ConditionIs(
                ConditionTerm::pointer_offset_equal(left.clone(), right.clone()),
                true,
            )
        };
        for goal in [
            equality(&read.offset, &stored.offset),
            equality(&stored.offset, &read.offset),
        ] {
            assert!(normalize_using_conditions(&goal, &[], &facts).is_ok());
        }
        let wrong_stride = Pointer::loaded(
            PointerBlock::ExternalArgument,
            Bitvector32Term::Variable(Variable(103_003)),
            8,
        );
        assert!(
            normalize_using_conditions(
                &equality(&wrong_stride.offset, &stored.offset),
                &[],
                &facts
            )
            .is_err()
        );
        assert!(
            normalize_using_conditions(
                &equality(&read.offset_by_bytes(4).offset, &stored.offset),
                &[],
                &facts
            )
            .is_err()
        );
        let wrong_value = Pointer::loaded(
            PointerBlock::ExternalArgument,
            Bitvector32Term::Variable(Variable(103_004)),
            4,
        );
        assert!(
            normalize_using_conditions(&equality(&read.offset, &wrong_value.offset), &[], &facts)
                .is_err()
        );
        let partial = memory
            .without_possible_aliasing_cells(&address.offset_by_bytes(4), 4, &context)
            .store(
                address.offset_by_bytes(4),
                CValue::Int32(Bitvector32Term::Constant(0)),
            );
        let changed = Pointer::loaded(
            PointerBlock::ExternalArgument,
            Bitvector32Term::Variable(Variable(103_005)),
            4,
        );
        record_load_access_width(&partial, &address, 8);
        context.register_pointer_read(&changed, &intern_c_memory(partial), &address);
        assert!(
            normalize_using_conditions(&equality(&changed.offset, &stored.offset), &[], &facts)
                .is_err()
        );
        // The same offset shape registered in a different block must not let
        // the last registration choose between two incompatible definitions.
        let conflict = Pointer {
            block: "conflicting-offset-origin".into(),
            offset: read.offset.clone(),
        };
        let conflicting_memory = CMemory::new().store(
            address.clone(),
            CValue::typed_pointer(wrong_value, CType::Int32Pointer),
        );
        record_load_access_width(&conflicting_memory, &address, 8);
        context.register_pointer_read(&conflict, &intern_c_memory(conflicting_memory), &address);
        assert!(
            crate::kernel::equality_graph::logical_pointer_read_for_offset(&read.offset).is_none()
        );
        assert!(
            normalize_using_conditions(&equality(&read.offset, &stored.offset), &[], &facts)
                .is_err()
        );
    }
    /// Canonical read snapshots retain an exact projection edge back to the
    /// execution source. The selected alias is still required to find its store.
    #[test]
    fn normalize_recorded_pointer_value_follows_exact_projection_source() {
        use crate::kernel::proof::ProofFacts;
        use crate::kernel::proof::fact_reasoning::normalize_using_conditions;
        let _session = crate::kernel::VerificationSession::enter();
        let context = PureFactContext::new();
        let address = Pointer::loaded(
            PointerBlock::ExternalArgument,
            Bitvector32Term::Variable(Variable(104_001)),
            4,
        );
        let written = Pointer::loaded(
            PointerBlock::ExternalArgument,
            Bitvector32Term::Variable(Variable(104_002)),
            4,
        );
        let stored = Pointer::symbolic(Variable(104_003));
        let source = CMemory::new()
            .with_block_without_derivation("local:projection", 4)
            .store(
                written.clone(),
                CValue::typed_pointer(stored.clone(), CType::Int32Pointer),
            );
        record_load_access_width(&source, &address, 8);
        let source = intern_c_memory(source);
        let original = Bitvector32Term::MemoryLoad(
            source.clone(),
            Box::new(address.clone()),
            LoadKind::Bits32,
        );
        let projected = crate::kernel::memory_provenance::canonicalize_atomic_loads_deep(&original);
        let Bitvector32Term::MemoryLoad(projected, _, _) = projected else {
            panic!("an unresolved aliased read must remain a load");
        };
        assert_ne!(source, projected);
        record_load_access_width(&projected, &address, 8);
        let read = Pointer::symbolic(Variable(104_004));
        context.register_pointer_read(&read, &projected, &address);
        let alias = Proposition::ConditionIs(ConditionTerm::pointer_equal(address, written), true);
        let goal = Proposition::ConditionIs(ConditionTerm::pointer_equal(read, stored), true);
        let facts = ProofFacts::from_ordered(std::slice::from_ref(&alias));
        assert!(normalize_using_conditions(&goal, std::slice::from_ref(&alias), &facts).is_ok());
        assert!(normalize_using_conditions(&goal, &[], &ProofFacts::from_ordered(&[])).is_err());
    }
    #[test]
    fn symbolic_pointer_load_factory_retains_exact_read_definition() {
        let _session = crate::kernel::VerificationSession::enter();
        let address = Pointer::symbolic(Variable(190_001));
        let memory = CMemory::new();
        let CValue::Pointer(value) = memory.symbolic_pointer_load(&address, 4, CType::Int32Pointer)
        else {
            panic!("typed pointer read")
        };
        assert_eq!(
            crate::kernel::equality_graph::logical_pointer_read_term(value.pointer()),
            Some(Bitvector32Term::MemoryLoad(
                intern_c_memory(memory.clone()),
                Box::new(address.clone()),
                LoadKind::Bits32,
            )),
        );
        // Recording a definition does not settle a value or grant a cell.
        let assumptions = PureFactContext::new();
        assert_eq!(
            assumptions.decide(&ConditionTerm::pointer_equal(
                value.pointer().clone(),
                Pointer::symbolic(Variable(190_002)),
            )),
            None
        );
        assert!(!memory.is_loadable_concretely(&address, 8));
        let forged = Pointer::loaded(
            address.block.clone(),
            Bitvector32Term::MemoryLoad(
                intern_c_memory(memory),
                Box::new(address),
                LoadKind::Bits32,
            ),
            8,
        );
        assert!(crate::kernel::equality_graph::logical_pointer_read_term(&forged).is_none());
    }

    #[cfg(test)]
    mod scaling_tests {
        include!("../../scaling_tests/kernel/eval/memory_loads/tests.rs");
    }
}
