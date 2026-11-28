//! Lexically scoped constructor cases for execution frontiers and pure goals.
//!
//! The frontier may be a function entry, a point after checked C steps, or a
//! loop body. Where the arms end is the caller's business: a function proof
//! joins them at function exit, while a preservation region runs each to the
//! loop's own boundary and never joins them.

use super::*;
use crate::kernel::proof::CheckedProofCasePartition;
use crate::kernel::{AlgebraicTermNode, AlgebraicValue, Term};

pub(in crate::surface::proof) struct ExecutionMatchPlan {
    partition: Arc<CheckedProofCasePartition>,
    source: Arc<ProofMatch>,
    /// One shared copy of the written `match`, so every arm of this plan
    /// records the same path-aligned case identity.
    arm_case_source: Arc<ProofMatch>,
    case_indices: Vec<usize>,
    matched_instance: Option<crate::kernel::ResourceInstance>,
    bindings: Vec<PersistentBinderMap<SyntaxTerm>>,
    integer_bindings: Vec<PersistentBinderMap<crate::kernel::SpecIntegerExpression>>,
    parent_locals: ProofLocals,
    deferred_base: PersistentSequence<DeferredPostExecutionTactic>,
    excluded: Vec<Option<ProofCertificate>>,
    entry_cases: PersistentSequence<CaseAssumption>,
    trace: Option<std::cell::RefCell<crate::surface::proof_trace::TraceMatch>>,
}

impl ExecutionMatchPlan {
    pub(in crate::surface::proof) fn take_trace(
        &self,
    ) -> Option<crate::surface::proof_trace::TraceMatch> {
        self.trace.as_ref().map(|trace| {
            let mut trace = trace.borrow_mut();
            crate::surface::proof_trace::TraceMatch {
                header: trace.header.clone(),
                source_tactic_path: trace.source_tactic_path.clone(),
                arms: std::mem::take(&mut trace.arms),
            }
        })
    }

    pub(in crate::surface::proof) fn excluded_certificate(
        &self,
        index: usize,
    ) -> Option<&ProofCertificate> {
        self.excluded[index].as_ref()
    }
    pub(in crate::surface::proof) fn arm_holds_false(&self, index: usize) -> bool {
        self.partition
            .facts_for_case(self.case_indices[index])
            .is_some_and(|facts| facts.holds_false())
    }

    /// The arms this match still has to execute: every constructor whose arm
    /// still has an open execution path.
    pub(in crate::surface::proof) fn live_cases(&self) -> Vec<usize> {
        (0..self.excluded.len())
            .filter(|&index| self.excluded[index].is_none())
            .collect()
    }

    /// True when exactly one constructor survives, so its arm runs directly on
    /// the parent frontier and never passes through a terminal join.
    pub(in crate::surface::proof) fn has_sole_live_case(&self) -> bool {
        self.excluded.iter().filter(|case| case.is_none()).count() == 1
    }

    /// The surface condition that names one side of a live-arm split: a match
    /// over the same scrutinee that yields `1` exactly on `left`. Excluded
    /// constructors are already impossible, so they take the `0` side.
    pub(in crate::surface::proof) fn condition(&self, left: &[usize]) -> SyntaxProposition {
        SyntaxProposition::Comparison {
            left: SyntaxTerm::AlgebraicMatch {
                scrutinee: Box::new(self.source.scrutinee.clone()),
                arms: self
                    .source
                    .arms
                    .iter()
                    .enumerate()
                    .map(|(index, arm)| AlgebraicMatchArm {
                        type_name: arm.type_name.clone(),
                        variant: arm.variant.clone(),
                        bindings: arm
                            .bindings
                            .iter()
                            .cloned()
                            .map(SurfaceBinder::from)
                            .collect(),
                        body: SyntaxTerm::ProgramExpression(ProgramExpression::Value(
                            ProgramValue::Int32(OldMachineTerm::constant(u32::from(
                                left.contains(&index),
                            ))),
                        )),
                    })
                    .collect(),
            },
            operator: ComparisonOperator::Equal,
            right: SyntaxTerm::ProgramExpression(ProgramExpression::Value(ProgramValue::Int32(
                OldMachineTerm::constant(1),
            ))),
        }
    }
}

/// Tags one deferred post-execution tactic, and everything a surface `if` or
/// `branch` nests inside it, with the match arm's binding scope.
///
/// Ordered finalization flattens those arms and applies each selected tactic
/// to the outcome proof, so a tactic written inside a nested arm reaches that
/// proof on its own. Tagging only the outermost entry left every nested
/// tactic without the arm's field bindings.
fn attach_arm_lexical_scope(
    tactic: &mut DeferredPostExecutionTactic,
    scope: &PersistentBinderMap<SyntaxTerm>,
) {
    if tactic.lexical_bindings.is_none() {
        tactic.lexical_bindings = Some(scope.clone());
    }
    if let PostExecutionTactic::If {
        then_tactics,
        else_tactics,
        ..
    } = &mut tactic.tactic
    {
        for nested in Arc::make_mut(then_tactics)
            .iter_mut()
            .chain(Arc::make_mut(else_tactics).iter_mut())
        {
            attach_arm_lexical_scope(nested, scope);
        }
    }
}

/// One outcome path's constructor cases for a `match` deferred after
/// execution: the checked partition of the scrutinee's value on that path,
/// and each written arm's case and field bindings.
pub(in crate::surface::proof) struct OutcomeMatchCases {
    pub(in crate::surface::proof) partition: Arc<CheckedProofCasePartition>,
    pub(in crate::surface::proof) arms: Vec<(usize, PersistentBinderMap<SyntaxTerm>)>,
    /// The first choice variable after this partition's witnesses.
    pub(in crate::surface::proof) next_variable: u64,
}

impl<'a> Proof<'a> {
    /// Establishes the one marker shared by ordinary and scoped match checking.
    pub(in crate::surface::proof) fn prepare_execution_match(
        &self,
        ensuring: bool,
        source_index: usize,
    ) -> Result<Self, ClickError> {
        let proof = if ensuring {
            self.prepare_entry_interface()?
        } else {
            self.clone()
        };
        let proof = if crate::surface::proof_trace::enabled_for(proof.claim_label()) {
            proof.at_source_tactic(source_index)
        } else {
            proof
        };
        Ok(proof.begin_execution_match())
    }

    pub(in crate::surface::proof) fn begin_execution_match(&self) -> Self {
        Self {
            site: self.site.clone(),
            context: self.context.clone(),
            state: self.state.clone(),
            node: Arc::new(ProofNode {
                path_memo: Default::default(),
                parent: Some(self.node.clone()),
                step: None,
                focused_branch: self.focused_branch_id(),
                depth: self.node.depth,
                // This marker belongs only to the current lineage. A later
                // sibling must not follow it into this arm's nested matches.
                split_branches: vec![self.focused_branch_id()],
            }),
        }
    }

    pub(in crate::surface::proof) fn execution_match_arm_certificate(
        &self,
        marker: &ProofCheckpoint<'a>,
    ) -> Result<ProofCertificate, ClickError> {
        self.certificate_after_node(Some(&marker.node))
    }
    /// This proof with the loop's pass count in scope: `iterations` names
    /// `count`, the head's count for a pass's proof.
    pub(in crate::surface::proof) fn with_loop_iterations(
        &self,
        count: &crate::kernel::IntegerTerm,
    ) -> Self {
        let mut locals = self.state.locals().clone();
        locals.set_integer_values(locals.integer_values.with_inserted(
            crate::surface::LOOP_ITERATIONS_NAME.to_string(),
            crate::kernel::SpecIntegerExpression::Term(count.clone()),
        ));
        self.with_kernel_state(self.state.with_locals(locals))
    }

    pub(in crate::surface::proof) fn with_surface_local_scope(
        &self,
        bindings: &PersistentBinderMap<SyntaxTerm>,
    ) -> Self {
        let mut locals = self.state.locals().clone();
        locals.set_values(bindings.clone());
        self.with_kernel_state(self.state.with_locals(locals))
    }

    pub(in crate::surface::proof) fn surface_local_scope(&self) -> PersistentBinderMap<SyntaxTerm> {
        self.state.locals().values.clone()
    }

    /// Apply only the changed source bindings to an outcome with checked
    /// locals. Remove expired obtains from every typed binding map.
    pub(in crate::surface::proof) fn update_deferred_outcome_locals(
        &self,
        previous: Option<&PersistentBinderMap<SyntaxTerm>>,
        scope: Option<&PersistentBinderMap<SyntaxTerm>>,
        obtained: &PersistentBinderMap<SyntaxTerm>,
        expired: &[String],
    ) -> Self {
        let mut locals = self.state.locals().clone();
        let mut values = locals.values.clone();
        if let (Some(previous), Some(scope)) = (previous, scope) {
            for (name, _, replacement) in previous.diff(scope) {
                match replacement.or_else(|| obtained.get(name)) {
                    Some(value) => values.insert(name.clone(), value.clone()),
                    None => values.remove(name),
                }
            }
        }
        let source = scope.or(previous);
        let mut integers = locals.integer_values.clone();
        let mut algebraics = locals.algebraic_values.clone();
        for name in expired {
            if let Some(value) = source.and_then(|source| source.get(name)) {
                values.insert(name.clone(), value.clone());
            } else {
                values.remove(name);
            }
            integers.remove(name);
            algebraics.remove(name);
        }
        locals.set_values(values);
        locals.set_integer_values(integers);
        locals.set_algebraic_values(algebraics);
        self.with_kernel_state(self.state.with_locals(locals))
    }

    pub(in crate::surface::proof) fn scope_call_payload(
        &self,
        scope: Option<&PersistentBinderMap<SyntaxTerm>>,
        name: &str,
        value: StoredExecutionValue,
    ) -> PersistentBinderMap<SyntaxTerm> {
        scope.unwrap_or(&self.state.locals().values).with_inserted(
            name.to_owned(),
            SyntaxTerm::ProgramExpression(ProgramExpression::Value(value.into_native())),
        )
    }

    /// The constructor each written arm of `source` stands for, by index in
    /// the scrutinee's datatype. Every constructor has exactly one arm, with
    /// one fresh binder per field.
    fn match_case_indices(
        &self,
        source: &ProofMatch,
        value: &crate::kernel::AlgebraicTerm,
        frontier_locals: &crate::kernel::LocalEnvironment,
    ) -> Result<Vec<usize>, ClickError> {
        let variants = &value.algebraic_type.variants;
        if source.arms.len() != variants.len() {
            return Err(self
                .step_error("proof `match` must cover every constructor exactly once")
                .with_failed_tactic("match")
                .with_proof_refusal(crate::surface::ProofRefusal::Tactic));
        }
        let indices: BTreeMap<_, _> = variants
            .iter()
            .enumerate()
            .map(|(index, variant)| (variant.name.as_str(), index))
            .collect();
        let mut seen = BTreeSet::new();
        let mut case_indices = Vec::with_capacity(source.arms.len());
        for arm in &source.arms {
            let Some(&index) = indices.get(arm.variant.as_str()) else {
                return Err(self.step_error(format!(
                    "unknown match constructor `{}::{}`",
                    arm.type_name, arm.variant
                )));
            };
            if arm.type_name != value.algebraic_type.name || !seen.insert(index) {
                return Err(
                    self.step_error("proof `match` has a duplicate constructor or wrong datatype")
                );
            }
            if arm.bindings.len() != variants[index].fields.len() {
                return Err(self.step_error(format!(
                    "match constructor `{}` has the wrong number of field bindings",
                    arm.variant
                )));
            }
            let mut names = BTreeSet::new();
            for name in &arm.bindings {
                if name == "result"
                    || !names.insert(name)
                    || self.state.locals().values.contains_key(name)
                    || frontier_locals.contains_name(name)
                {
                    return Err(
                        self.step_error(format!("match binding `{name}` is already in scope"))
                    );
                }
            }
            case_indices.push(index);
        }
        Ok(case_indices)
    }

    /// Each written arm's field bindings in its case of `partition`, over
    /// this proof's local scope.
    #[allow(clippy::type_complexity)]
    fn match_arm_bindings(
        &self,
        source: &ProofMatch,
        partition: &CheckedProofCasePartition,
        case_indices: &[usize],
        value: &crate::kernel::AlgebraicTerm,
    ) -> Result<
        (
            Vec<PersistentBinderMap<SyntaxTerm>>,
            Vec<PersistentBinderMap<crate::kernel::SpecIntegerExpression>>,
        ),
        ClickError,
    > {
        let mut bindings = Vec::with_capacity(source.arms.len());
        let mut integer_bindings = Vec::with_capacity(source.arms.len());
        for (arm, &index) in source.arms.iter().zip(case_indices) {
            let Some(Proposition::Equal(_, Term::Algebraic(constructor))) =
                partition.case_fact(index)
            else {
                unreachable!()
            };
            let AlgebraicTermNode::Constructor { fields, .. } = &constructor.old_form().node else {
                unreachable!()
            };
            let mut scope = self.state.locals().values.clone();
            let mut integer_scope = self.state.locals().integer_values.clone();
            for (field_index, (name, field)) in arm.bindings.iter().zip(fields).enumerate() {
                let expression = match field {
                    AlgebraicValue::Program(value) => {
                        SyntaxTerm::ProgramExpression(ProgramExpression::Value(value.clone()))
                    }
                    AlgebraicValue::Algebraic(binding) => {
                        // A concrete scrutinee already carries immutable payload
                        // identities. Constructor injectivity in the checked arm
                        // relates the fresh pattern variable to that payload.
                        // Keep an existing surface variable's spelling, just as
                        // C payloads above keep their checked program spelling.
                        let value = crate::kernel::arm_algebraic_payload_spelling(
                            value,
                            &arm.variant,
                            field_index,
                        )
                        .unwrap_or(binding);
                        let AlgebraicTermNode::Variable(variable) = value.node else {
                            unreachable!()
                        };
                        SyntaxTerm::AlgebraicVariable {
                            name: name.clone().into(), binder_index: variable.algebraic_binder_index().expect("a case binder is an algebraic binder") as usize,
                            algebraic_type: AlgebraicTypeApplication {
                                rigid: value.algebraic_type.rigid, name: value.algebraic_type.name.clone(),
                                arguments: value.algebraic_type.arguments.iter().map(super::super::pure_theorems::click_type_from_algebraic_value_type).collect::<Result<_,_>>()?,
                            },
                        }
                    }
                    AlgebraicValue::Integer(value) => {
                        integer_scope = integer_scope.with_inserted(
                            name.clone(),
                            crate::kernel::SpecIntegerExpression::Term(value.clone()),
                        );
                        SyntaxTerm::Binding(name.clone())
                    }
                };
                scope = scope.with_inserted(name.clone(), expression);
            }
            bindings.push(scope);
            integer_bindings.push(integer_scope);
        }
        Ok((bindings, integer_bindings))
    }

    /// The value of a deferred `match`'s scrutinee on one outcome path:
    /// its datatype term over that path's return `state`, under `query`.
    pub(in crate::surface::proof) fn outcome_match_scrutinee(
        &self,
        source: &ProofMatch,
        state: &ExecutionState,
        query: &PureFactStore,
        retained_states: &RecordedStates,
    ) -> Result<crate::kernel::AlgebraicTerm, ClickError> {
        let execution = self
            .execution()
            .ok_or_else(|| self.step_error("a `match` after execution lost its execution"))?;
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Err(self.step_error("a `match` after execution requires a C execution proof"));
        };
        let equation = SyntaxProposition::Comparison {
            left: source.scrutinee.clone(),
            operator: ComparisonOperator::Equal,
            right: source.scrutinee.clone(),
        };
        let SyntaxProposition::Comparison {
            left: expression, ..
        } = self.substitute_fixed_state_locals_in_proposition(&equation)?
        else {
            unreachable!()
        };
        let values = parameter_values(context.parameter_binding())
            .map_err(|error| self.step_error(error.message))?;
        let array_refs = array_refs_for_parameters(
            context.parsed_function.parameters(),
            &values,
            &state.program_point(),
        );
        capture_fixed_state_algebraic_value(
            &expression,
            query.assumptions(),
            ContractEnvironment::new(&values, &array_refs)
                .with_parameters(context.parameter_binding()),
            BTreeMap::new(),
            context.old_reference_state(&execution.core.frontier, state),
            state,
            retained_states,
            context.spec_definitions,
        )
        .map_err(|message| {
            self.step_error(format!(
                "could not lower the scrutinee of a `match` after execution: {message}"
            ))
        })
    }

    /// Partitions one outcome path by the constructors of `value`, the
    /// scrutinee of a `match` deferred after execution as that path lowers
    /// it, under `authority`. Witnesses start at `next_variable`, so the
    /// paths of one split never share them.
    pub(in crate::surface::proof) fn outcome_match_cases(
        &self,
        source: &ProofMatch,
        value: &crate::kernel::AlgebraicTerm,
        authority: &PureFactStore,
        next_variable: u64,
    ) -> Result<OutcomeMatchCases, ClickError> {
        let execution = self
            .execution()
            .ok_or_else(|| self.step_error("a `match` after execution lost its execution"))?;
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Err(self.step_error("a `match` after execution requires a C execution proof"));
        };
        let case_indices = self.match_case_indices(source, value, execution.core.state.locals())?;
        let first = next_variable.max(self.state.locals().next_choice_variable);
        let (partition, _, next) = execution
            .core
            .algebraic_case_partition(
                authority,
                value,
                context.function_environment,
                context.function.composite_resource_definitions(),
                None,
                first,
            )
            .ok_or_else(|| {
                self.step_error("a `match` after execution requires a supported ADT scrutinee")
            })?;
        let (bindings, integer_bindings) =
            self.match_arm_bindings(source, &partition, &case_indices, value)?;
        let base = self.state.locals().integer_values.len();
        if integer_bindings.iter().any(|scope| scope.len() != base) {
            return Err(self.step_error(
                "a `match` after execution cannot yet bind an integer constructor field",
            ));
        }
        Ok(OutcomeMatchCases {
            partition,
            arms: case_indices.into_iter().zip(bindings).collect(),
            next_variable: next,
        })
    }

    pub(in crate::surface::proof) fn plan_execution_match(
        &self,
        source: &Arc<ProofMatch>,
    ) -> Result<ExecutionMatchPlan, ClickError> {
        let equation = SyntaxProposition::Comparison {
            left: source.scrutinee.clone(),
            operator: ComparisonOperator::Equal,
            right: source.scrutinee.clone(),
        };
        let execution = self
            .execution()
            .ok_or_else(|| self.step_error("proof `match` requires an execution frontier"))?;
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Err(self.step_error("proof `match` currently requires a C execution proof"));
        };
        let SyntaxProposition::Comparison {
            left: expression, ..
        } = self.substitute_fixed_state_locals_in_proposition(&equation)?
        else {
            unreachable!()
        };
        // A direct resource-field match has one indexed semantic owner. Pass
        // that exact projection into the kernel partition so constructor-arm
        // facts are checked for this instance without searching unrelated
        // resources. Other algebraic expressions remain ordinary matches.
        let matched_resource_field = match &expression {
            SyntaxTerm::ResourceField(access) => {
                let state = &execution.core.state;
                let name = access.projected_name();
                if let Some((instance, field_index)) = state.projected_resource_field(
                    access.identity,
                    &access.children,
                    access.field_index,
                    name.as_deref(),
                ) {
                    Some(crate::kernel::ResourceFieldProjection {
                        identity: instance.identity().into(),
                        children: Vec::new(),
                        field_name: None,
                        field_index,
                        at_entry: false,
                    })
                } else {
                    Some(crate::kernel::ResourceFieldProjection {
                        identity: access.identity,
                        children: access.children.clone(),
                        field_name: name,
                        field_index: access.field_index,
                        at_entry: false,
                    })
                }
            }
            _ => None,
        };
        let matched_instance = matched_resource_field.as_ref().and_then(|projection| {
            execution
                .core
                .state
                .resource_instance_at_path(projection.identity, &projection.children)
                .cloned()
        });
        let values = parameter_values(context.parameter_binding())
            .map_err(|error| self.step_error(error.message))?;
        let array_refs = array_refs_for_parameters(
            context.parsed_function.parameters(),
            &values,
            &execution.core.state.program_point(),
        );
        // A Rust `match` of a local that is no parameter, such as a call's
        // result, splits the algebraic value the local holds here, the one
        // its variant tests read.
        let local = match &expression {
            SyntaxTerm::Binding(name)
            | SyntaxTerm::ProgramExpression(ProgramExpression::Variable(
                crate::kernel::BindingName::Named(name),
            )) if !values.contains_key(name) && !self.state.locals().values.contains_key(name) => {
                match execution.core.state.locals().get_native(name).as_deref() {
                    Some(ProgramValue::Parameter(term)) => Some((**term).clone()),
                    _ => None,
                }
            }
            _ => None,
        };
        let value = match local {
            Some(term) => term,
            None => capture_fixed_state_algebraic_value(
                &expression,
                self.facts().assumptions(),
                ContractEnvironment::new(&values, &array_refs)
                    .with_parameters(context.parameter_binding()),
                BTreeMap::new(),
                context.old_reference_state(&execution.core.frontier, &execution.core.state),
                &execution.core.state,
                &execution.presentation.recorded_states,
                context.spec_definitions,
            )
            .map_err(|message| {
                self.step_error(format!("could not lower match scrutinee: {message}"))
            })?,
        };
        let case_indices =
            self.match_case_indices(source, &value, execution.core.state.locals())?;
        // Each case binder is an algebraic binder index. The kernel, not this
        // spelling, checks freshness.
        let first = self.state.locals().next_choice_variable;
        let (partition, _, next) = execution
            .core
            .algebraic_case_partition(
                self.facts(),
                &value,
                context.function_environment,
                context.function.composite_resource_definitions(),
                matched_resource_field.as_ref(),
                first,
            )
            .ok_or_else(|| {
                self.step_error(
                    "proof `match` requires a supported ADT scrutinee at this execution frontier",
                )
            })?;
        let (bindings, integer_bindings) =
            self.match_arm_bindings(source, &partition, &case_indices, &value)?;
        let mut parent_locals = self.state.locals().clone();
        parent_locals.next_choice_variable = next;
        let plan = ExecutionMatchPlan {
            partition,
            source: Arc::clone(source),
            arm_case_source: Arc::clone(source),
            case_indices,
            matched_instance,
            bindings,
            integer_bindings,
            parent_locals,
            deferred_base: execution.presentation.post_execution_tactics.clone(),
            excluded: vec![None; source.arms.len()],
            entry_cases: execution.presentation.case_assumptions.clone(),
            trace: crate::surface::proof_trace::enabled_for(self.claim_label()).then(|| {
                std::cell::RefCell::new(crate::surface::proof_trace::TraceMatch {
                    header: format!(
                        "{}: match",
                        self.site().path().unwrap_or_else(|| "checked match".into())
                    ),
                    source_tactic_path: self.site().source_tactic_path(),
                    arms: (0..source.arms.len()).map(|_| None).collect(),
                })
            }),
        };
        Ok(plan)
    }

    /// Uses the arm's indexed falsehood to exclude this constructor.
    pub(in crate::surface::proof) fn execution_match_arm_unreachable(
        &self,
        plan: &ExecutionMatchPlan,
        index: usize,
    ) -> Option<Arc<CheckedProofCasePartition>> {
        plan.partition
            .excluding_constructor_case_in(plan.case_indices[index], self.facts())
    }

    /// Publishes the retained partition and the closed arm's certificate.
    /// `self` is the successor of the bridge and its terminal closure.
    /// `entered` is the checkpoint taken on entry to that arm.
    pub(in crate::surface::proof) fn finish_execution_match_arm_exclusion(
        &self,
        plan: &mut ExecutionMatchPlan,
        index: usize,
        entered: &ProofCheckpoint<'a>,
        partition: Arc<CheckedProofCasePartition>,
    ) -> Result<(), ClickError> {
        plan.excluded[index] = Some(self.execution_match_arm_certificate(entered)?);
        self.record_execution_match_arm_trace(plan, index, entered);
        plan.partition = partition;
        Ok(())
    }

    pub(in crate::surface::proof) fn enter_execution_match_arm(
        &self,
        plan: &ExecutionMatchPlan,
        index: usize,
    ) -> Result<Self, ClickError> {
        let state = self
            .state
            .introduce_frontier_match_case(plan.partition.clone(), plan.case_indices[index])
            .map_err(|message| self.step_error(message))?;
        let mut locals = plan.parent_locals.clone();
        locals.set_values(plan.bindings[index].clone());
        locals.set_integer_values(plan.integer_bindings[index].clone());
        let arm = &plan.source.arms[index];
        let Some(Proposition::Equal(_, Term::Algebraic(constructor))) =
            plan.partition.case_fact(plan.case_indices[index])
        else {
            unreachable!()
        };
        let surface = SyntaxProposition::Comparison {
            left: plan.source.scrutinee.clone(),
            operator: ComparisonOperator::Equal,
            right: SyntaxTerm::AlgebraicConstructor {
                algebraic_type: AlgebraicTypeApplication {
                    rigid: false,
                    name: constructor.old_form().algebraic_type.name.clone(),
                    arguments: constructor
                        .old_form()
                        .algebraic_type
                        .arguments
                        .iter()
                        .map(super::super::pure_theorems::click_type_from_algebraic_value_type)
                        .collect::<Result<_, _>>()?,
                },
                variant: arm.variant.clone(),
                arguments: arm
                    .bindings
                    .iter()
                    .map(|name| match plan.bindings[index].get(name).unwrap() {
                        // A C-typed field's binding holds the kernel value the
                        // case fact assigns it, and that value has no source
                        // spelling. The arm's own binder names it, so a
                        // certificate generated inside the arm prints the
                        // binder the source wrote instead of a kernel variable
                        // id that no later lowering can resolve.
                        SyntaxTerm::ProgramExpression(ProgramExpression::Value(_)) => {
                            SyntaxTerm::ProgramExpression(ProgramExpression::Variable(
                                (name.clone()).into(),
                            ))
                        }
                        expression => expression.clone(),
                    })
                    .collect(),
            },
        };
        let case = plan
            .partition
            .case_fact(plan.case_indices[index])
            .unwrap()
            .clone();
        let ProofContext::Execution(context) = self.context.as_ref() else {
            unreachable!();
        };
        let tactic_index = context.tactic_index;
        // The split's constructor equation remains a fact of its arm.
        // Expansion can spell a whole-function match directly only at entry.
        let at_function_entry = self
            .execution()
            .is_some_and(|execution| execution.core.frontier.is_at_function_entry());
        // Where the arms complete the function proof, the `match` step is
        // assembled from the arm certificates by `finish_execution_match`.
        // Where they do not — a loop body, whose arms each close the
        // invariants on their own path — each arm is a separate certified
        // path, so record the arm as a path-aligned case and note where in
        // this path's tactics it was taken. Path merging rebuilds the `match`
        // from those.
        let arm_case = ProofMatchArmCase {
            source: plan.arm_case_source.clone(),
            arm: index,
        };
        // This path's own steps: the proof also retains the steps of the
        // arms checked before this one, which are not on this arm's path.
        let tactic_offset = self.path_step_count()?;
        let proof = self.with_kernel_state(state.with_locals(locals));
        let function_values = parameter_values(context.parameter_binding())?;
        let clause_presentations = if let Some(instance) = plan.matched_instance.as_ref() {
            crate::surface::proof::resources::pair_instance_body_clause_presentations(
                context.resource_environment,
                context.spec_definitions.functions,
                instance,
                plan.partition
                    .body_clauses_for_case(plan.case_indices[index])
                    .unwrap_or_default(),
                &function_values,
                Some(&arm.bindings),
            )?
        } else {
            Vec::new()
        };
        // The kernel producer pairs these checked clauses with the facts it
        // introduced. Consume that result directly; comparing the freshly
        // produced facts again would reject equivalent retained carriers.
        // Spell what the arm adds besides its case, a premise's instance
        // `s_circle_0 < 4294967295u32` above all, with the arm's binders, so
        // a certificate in the arm or after it can cite it.
        let binder_names = arm
            .bindings
            .iter()
            .filter_map(|name| match plan.bindings[index].get(name)? {
                SyntaxTerm::ProgramExpression(ProgramExpression::Value(value)) => {
                    crate::kernel::single_variable_of_program_value(value)
                        .map(|variable| (variable, SurfaceBinder::from(name)))
                }
                _ => None,
            })
            .collect::<BTreeMap<_, _>>();
        let execution = proof
            .execution()
            .ok_or_else(|| self.step_error("match arm lost its execution frontier"))?;
        // The case itself is spelled again when its value is a parameter's
        // that the scrutinee, a local, copies: `o == Option::Some(..)`
        // beside `local == Option::Some(..)`, so goals about `o` reduce.
        let instance_spellings = plan
            .partition
            .additions_for_case(plan.case_indices[index])
            .iter()
            .filter_map(|fact| {
                crate::surface::proof::surface_synthesis::synthesize_surface_proposition_with_names(
                    fact,
                    context.parameter_binding(),
                    &execution.core.state,
                    &binder_names,
                )
                .filter(|spelled| *fact != case || *spelled != surface)
                .map(|spelled| (spelled, fact.clone()))
            })
            .collect::<Vec<_>>();
        let (proof, result) = proof.edit_execution_presentation(|presentation| {
            presentation
                .surface_propositions
                .record_lowering(&surface, &case)?;
            for (spelled, fact) in &instance_spellings {
                presentation
                    .surface_propositions
                    .record_lowering(spelled, fact)?;
            }
            for clause in &clause_presentations {
                presentation.resource_body_clauses.push(clause.clone());
            }
            presentation.case_assumptions.push(CaseAssumption {
                tactic_index,
                condition: surface.clone(),
                value: true,
                fact: Some(case),
                match_arm: Some(arm_case),
            });
            if !at_function_entry && presentation.surface_record.blocker.is_none() {
                presentation
                    .surface_record
                    .path_choices
                    .push(SurfacePathChoice {
                        occurrence: tactic_index,
                        selector: SurfacePathSelector::Proposition(surface),
                        value: true,
                        tactic_offset,
                        scope_end: None,
                    });
            }
            Ok::<_, ClickError>(())
        })?;
        result?;
        let proof = if plan.trace.is_some() {
            // Keep a distinct diagnostic node for the checked constructor case.
            // It carries no proof step and adds no premise or certificate rule.
            let proof = Self {
                node: Arc::new(ProofNode {
                    path_memo: Default::default(),
                    parent: Some(proof.node.clone()),
                    focused_branch: proof.focused_branch_id(),
                    depth: proof.node.depth,
                    split_branches: Vec::new(),
                    step: None,
                }),
                ..proof
            };
            crate::surface::proof_trace::record(
                crate::surface::proof_trace::trace_node_key(&proof.node),
                crate::surface::proof_trace::TraceStep {
                    header: format!(
                        "{}: match ({}::{} arm)",
                        self.site().path().unwrap_or_else(|| "checked match".into()),
                        arm.type_name,
                        arm.variant
                    ),
                    source_tactic_path: self.site().source_tactic_path(),
                    call_source: None,
                    facts: vec![
                        proof.checked_trace_fact(
                            plan.partition
                                .case_fact(plan.case_indices[index])
                                .expect("checked constructor case")
                                .clone(),
                        ),
                    ],
                    more_facts: 0,
                    frontier: None,
                    load: None,
                    read_equalities: Vec::new(),
                    read_context_changed: false,
                    transport: None,
                    resources: Vec::new(),
                    more_resources: 0,
                    origin: crate::surface::proof_trace::smart_origin(),
                    chosen: None,
                    forgotten_cells: Vec::new(),
                    history_stops: Vec::new(),
                },
            );
            proof
        } else {
            proof
        };
        Ok(proof)
    }

    pub(in crate::surface::proof) fn leave_execution_match_arm(
        &self,
        plan: &ExecutionMatchPlan,
    ) -> Result<Self, ClickError> {
        self.leave_execution_match_arm_keeping(plan, false)
    }

    /// Leaves an arm that the implicit tail opened at a Rust `match` and ran
    /// to function exit. The arm's binders stay in scope on its finished path,
    /// as its case fact does, so the closer at function exit can cite that
    /// fact.
    pub(in crate::surface::proof) fn leave_terminal_execution_match_arm(
        &self,
        plan: &ExecutionMatchPlan,
    ) -> Result<Self, ClickError> {
        self.leave_execution_match_arm_keeping(plan, true)
    }

    fn leave_execution_match_arm_keeping(
        &self,
        plan: &ExecutionMatchPlan,
        keep_binders: bool,
    ) -> Result<Self, ClickError> {
        let scope = self.state.locals().values.clone();
        let (proof, result) = self.clone().edit_execution_presentation(|presentation| {
            let suffix = presentation
                .post_execution_tactics
                .suffix_since(&plan.deferred_base)
                .ok_or("match arm lost its deferred-tactic prefix")?;
            let mut deferred = plan.deferred_base.clone();
            for mut tactic in suffix {
                attach_arm_lexical_scope(&mut tactic, &scope);
                deferred.push(tactic);
            }
            presentation.post_execution_tactics = deferred;
            Ok::<_, &'static str>(())
        })?;
        result.map_err(|message| self.step_error(message))?;
        let mut locals = plan.parent_locals.clone();
        if keep_binders {
            // A binder no other arm also names stays bound on the finished
            // paths: each such name has one value, its own arm's.
            let mut arms_naming = BTreeMap::<&str, usize>::new();
            for arm in &plan.source.arms {
                for name in &arm.bindings {
                    *arms_naming.entry(name.as_str()).or_default() += 1;
                }
            }
            for (arm, bindings) in plan.source.arms.iter().zip(&plan.bindings) {
                for name in &arm.bindings {
                    if arms_naming[name.as_str()] == 1
                        && let Some(value) = bindings.get(name)
                    {
                        locals.set_values(locals.values.with_inserted(name.clone(), value.clone()));
                    }
                }
            }
        }
        locals.next_choice_variable = locals
            .next_choice_variable
            .max(self.state.locals().next_choice_variable);
        let proof = if plan.has_sole_live_case() {
            // A sole live arm runs on the parent frontier, so unlike any
            // joined arm it never passed through merge_terminal_execution_join.
            // Restore the same outer routing scope here: case evidence is
            // retained in the trace, not added to the whole function's
            // contract requirements.
            proof
                .edit_execution_presentation(|presentation| {
                    presentation.case_assumptions = plan.entry_cases.clone();
                })?
                .0
        } else {
            proof
        };
        Ok(proof.with_kernel_state(proof.state.with_locals(locals)))
    }

    pub(in crate::surface::proof) fn record_execution_match_arm_trace(
        &self,
        plan: &ExecutionMatchPlan,
        index: usize,
        marker: &ProofCheckpoint<'a>,
    ) {
        if let Some(trace) = &plan.trace {
            let arm = &plan.source.arms[index];
            trace.borrow_mut().arms[index] = Some(crate::surface::proof_trace::TraceMatchArm {
                names: Box::new(self.diagnostic_state()),
                name: format!("{}::{}", arm.type_name, arm.variant),
                fact: self.checked_trace_fact(
                    plan.partition
                        .case_fact(plan.case_indices[index])
                        .expect("checked constructor case")
                        .clone(),
                ),
                lineage: trace_arm_lineage(&self.node, &marker.node, self.focused_branch_id()),
                _retained: Box::new(self.node.clone()),
            });
        }
    }

    pub(in crate::surface::proof) fn finish_execution_match(
        &self,
        marker: &ProofCheckpoint<'a>,
        source: &ProofMatch,
        proofs: Vec<ProofCertificate>,
        trace: Option<crate::surface::proof_trace::TraceMatch>,
    ) -> Result<Self, ClickError> {
        if self.focused_branch_id() != marker.node.focused_branch
            || proofs.len() != source.arms.len()
        {
            return Err(
                self.step_error("match did not rejoin its exact parent and constructor family")
            );
        }
        let step = source.certificate_step(source.ensuring.clone(), proofs);
        let successor = Self {
            site: self.site.clone(),
            context: marker.context.clone(),
            state: self.state.clone(),
            node: ProofNode::step_child(&marker.node, self.focused_branch_id(), Arc::new(step)),
        };
        if let Some(trace) = trace {
            crate::surface::proof_trace::record_match(
                crate::surface::proof_trace::trace_node_key(&successor.node),
                trace,
            );
        }
        Ok(successor)
    }

    pub(in crate::surface::proof) fn split_execution_match_group(
        &self,
        condition: SyntaxProposition,
    ) -> Result<(Self, ExecutionProofCaseSplit<'a>), ClickError> {
        let branch = self
            .focused_branch()
            .ok_or_else(|| self.step_error("match requires an open frontier"))?;
        let execution = branch
            .state
            .execution
            .clone()
            .ok_or_else(|| self.step_error("match requires execution state"))?;
        let (state, split, ids, path_facts) = self
            .state
            .split_frontier_match_group()
            .map_err(|_| self.step_error("match requires an execution frontier"))?
            .into_parts_with_facts();
        let successor = Self {
            site: self.site.clone(),
            context: self.context.clone(),
            state,
            node: ProofNode::marker(&self.node, self.focused_branch_id(), ids.to_vec()),
        };
        let record = Box::new(ExecutionProofCaseSplitData {
            marker: successor.checkpoint(),
            split,
            arm_branches: ids,
            case_condition: ProofCaseCondition::If(condition),
            base_facts: [branch.state.facts.clone(), branch.state.facts.clone()],
            base_executions: [execution.clone(), execution.clone()],
            path_facts,
            common_facts: branch.state.facts.clone(),
            parent_locals: self.state.locals().clone(),
            execution_start_state: execution
                .core
                .frontier
                .execution_start_state(&execution.core.state)
                .clone(),
            parent_execution: execution,
        });
        Ok((successor, record))
    }
}

/// Pure matches reduce to constructor implications, not execution partitions.
pub(in crate::surface::proof) struct PureMatchPlan {
    source: Arc<ProofMatch>,
    presentation: PropositionPresentation,
    locals: ProofLocals,
    site: ProofStepSite,
    induction_case: bool,
}

impl<'a> Proof<'a> {
    pub(in crate::surface::proof) fn prepare_pure_match(
        &self,
        source: &Arc<ProofMatch>,
    ) -> Result<(Self, PureMatchPlan), ClickError> {
        if source.ensuring.is_some() {
            return Err(self.step_error(
                "pure proof `match` proves the current goal and does not take `ensuring`",
            ));
        }
        let ProofContext::Pure(context) = self.context.as_ref() else {
            return Err(self.step_error("this match requires a pure proposition proof"));
        };
        let value = self.capture_pure_algebraic_witness(&source.scrutinee)?;
        let variants = &value.algebraic_type.variants;
        let indices: BTreeMap<_, _> = variants
            .iter()
            .enumerate()
            .map(|(index, variant)| (variant.name.as_str(), index))
            .collect();
        let mut seen = BTreeSet::new();
        let mut order = Vec::new();
        for arm in &source.arms {
            if arm.type_name != value.algebraic_type.name {
                return Err(self.step_error("proof `match` pattern has the wrong datatype"));
            }
            let Some(&index) = indices.get(arm.variant.as_str()) else {
                return Err(self.step_error("proof `match` names an unknown constructor"));
            };
            if !seen.insert(index) {
                return Err(self.step_error("proof `match` repeats a constructor"));
            }
            if arm.bindings.len() != variants[index].fields.len() {
                return Err(self.step_error("proof `match` pattern has the wrong number of fields"));
            }
            let mut bindings = BTreeSet::new();
            for name in &arm.bindings {
                if !bindings.insert(name)
                    || (self.state().locals().induction_active
                        && context
                            .induction_setup
                            .as_ref()
                            .is_some_and(|setup| setup.hypothesis == *name))
                    || self.state.locals().values.contains_key(name)
                    || context.theorem_context.values.contains_key(name)
                    || context.theorem_context.integer_values.contains_key(name)
                    || context
                        .theorem_context
                        .declaration_bindings
                        .contains_key(name)
                    || self
                        .structural_induction_setup()
                        .is_some_and(|setup| setup.algebraic_values.contains_key(name))
                {
                    return Err(
                        self.step_error(format!("match binding `{name}` is already in scope"))
                    );
                }
            }
            order.push(index);
        }
        let presentation = self
            .focused_branch()
            .and_then(|branch| match &branch.obligation {
                Obligation::Proposition(goal) => Some(goal.presentation.clone()),
                _ => None,
            })
            .ok_or_else(|| self.step_error("pure match requires a proposition goal"))?;
        let state = self
            .state
            .refine_proposition_algebraic_match(&value, &order)
            .map_err(|message| self.step_error(message))?;
        // The match opens the same marker as an execution match, recording
        // the branch it runs on: a checkpoint of the incoming node would name
        // the branch of its last step, which after an `if` arm is a sibling.
        Ok((
            self.begin_execution_match().with_kernel_state(state),
            PureMatchPlan {
                source: source.clone(),
                presentation,
                locals: self.state.locals().clone(),
                site: self.site.clone(),
                induction_case: self.state().locals().induction_active
                    && context
                        .induction_setup
                        .as_ref()
                        .is_some_and(|setup| setup.structural_root.as_ref() == Some(&value)),
            },
        ))
    }

    pub(in crate::surface::proof) fn split_pure_match_group(
        &self,
    ) -> Result<(Self, SplitId, [BranchId; 2]), ClickError> {
        let (state, split, ids) = self
            .state
            .split_proposition_both(|parent, _| parent.clone())
            .map_err(|message| self.step_error(message))?
            .into_parts();
        Ok((
            Self {
                node: ProofNode::marker(&self.node, self.focused_branch_id(), ids.to_vec()),
                ..self.with_kernel_state(state)
            },
            split,
            ids,
        ))
    }

    pub(in crate::surface::proof) fn enter_pure_match_case(
        &self,
        plan: &PureMatchPlan,
        index: usize,
    ) -> Result<(Self, Option<Proposition>), ClickError> {
        let mut proof = self
            .with_kernel_state(self.state.with_locals(plan.locals.clone()))
            .at_site(&plan.site);
        for name in &plan.source.arms[index].bindings {
            let sort = match proof.proposition_goal("match field requires a universal goal")? {
                Proposition::ForAll { sort, .. } => sort.clone(),
                _ => return Err(proof.step_error("match field requires a universal goal")),
            };
            let mut witness = None;
            let state = proof
                .state
                .apply_intro(|presentation, introduction, _| {
                    if let PropositionIntroduction::Universal { variable, .. } = introduction {
                        witness = Some(variable);
                    }
                    presentation.clone()
                })
                .map_err(|_| proof.step_error("could not introduce a fresh match field"))?;
            let variable = witness.expect("kernel introduced the checked universal");
            let mut locals = state.locals().clone();
            let expression = match sort {
                Sort::Algebraic(algebraic_type) => {
                    locals.set_algebraic_values(locals.algebraic_values.with_inserted(
                        name.clone(),
                        crate::kernel::SpecAlgebraicExpression {
                            algebraic_type,
                            node: crate::kernel::SpecAlgebraicExpressionNode::Variable(variable),
                        },
                    ));
                    SyntaxTerm::Binding(name.clone())
                }
                Sort::Integer => {
                    locals.set_integer_values(locals.integer_values.with_inserted(
                        name.clone(),
                        crate::kernel::SpecIntegerExpression::Term(
                            crate::kernel::IntegerTerm::var(variable),
                        ),
                    ));
                    SyntaxTerm::Binding(name.clone())
                }
                Sort::ProgramObjectPointer(interface_type, class) => {
                    SyntaxTerm::ProgramExpression(ProgramExpression::Value(
                        crate::kernel::symbolic_call_result(interface_type, variable)
                            .with_pointer_object_class(Some(class)),
                    ))
                }
                Sort::ProgramPointer(interface_type) => {
                    SyntaxTerm::ProgramExpression(ProgramExpression::Value(
                        crate::kernel::symbolic_call_result(interface_type, variable),
                    ))
                }
                Sort::ProgramInt32 => SyntaxTerm::ProgramExpression(ProgramExpression::Value(
                    crate::kernel::symbolic_call_result(ProgramType::Int32, variable),
                )),
                Sort::ProgramInt64 => SyntaxTerm::ProgramExpression(ProgramExpression::Value(
                    crate::kernel::symbolic_call_result(ProgramType::Int64, variable),
                )),
                _ => return Err(proof.step_error("unsupported match field sort")),
            };
            locals.set_values(locals.values.with_inserted(name.clone(), expression));
            proof = proof.with_kernel_state(state.with_locals(locals));
        }
        let mut arm_trace = None;
        let state = proof
            .state
            .apply_intro(|_, introduction, introduced| {
                assert!(matches!(introduction, PropositionIntroduction::Implication));
                // Induction setup and goal refinement publish their own fact deltas.
                // Save the equation from the introduction that actually added it.
                arm_trace = proof.new_pure_match_trace(&plan.source).map(|trace| {
                    let equation = introduced.expect("implication introduces its antecedent");
                    (trace, equation.clone())
                });
                plan.presentation.clone()
            })
            .map_err(|_| {
                proof.step_error("could not introduce the checked constructor equation")
            })?;
        let mut entered = proof.with_kernel_state(state);
        if plan.induction_case {
            entered = entered.enter_structural_induction_case(
                &plan.source.scrutinee,
                &plan.source.arms[index],
            )?;
            entered = entered.refine_structural_case_goal(
                &plan.source.scrutinee,
                &plan.source.arms[index],
                false,
            )?;
        }
        entered.node = ProofNode::marker(
            &proof.node,
            proof.focused_branch_id(),
            vec![proof.focused_branch_id()],
        );
        // Retain the constructor equation before running the arm, so even a
        // rejected first tactic has the checked case in its failure trace.
        let constructor_equation = arm_trace.map(|(mut trace, equation)| {
            let marker = entered.checkpoint();
            trace.arms[index] = Some(entered.pure_match_arm_trace(
                &entered,
                &marker,
                &plan.source,
                index,
                &equation,
            ));
            crate::surface::proof_trace::record_match(
                crate::surface::proof_trace::trace_node_key(&entered.node),
                trace,
            );
            equation
        });
        Ok((entered, constructor_equation))
    }

    pub(in crate::surface::proof) fn leave_pure_match_case(
        &self,
        plan: &PureMatchPlan,
        index: usize,
    ) -> Result<Self, ClickError> {
        if !self.uses_structural_induction() {
            return Ok(self.with_kernel_state(self.state.with_locals(plan.locals.clone())));
        }
        let proof = if plan.induction_case {
            self.refine_structural_case_goal(
                &plan.source.scrutinee,
                &plan.source.arms[index],
                true,
            )?
        } else {
            self.clone()
        };
        let mut locals = plan.locals.clone();
        let mut values = PersistentBinderMap::default();
        let mut algebraic = PersistentBinderMap::default();
        let mut integers = PersistentBinderMap::default();
        for name in &plan.source.arms[index].bindings {
            if let Some(value) = proof.state().locals().values.get(name) {
                values.insert(name.clone(), value.clone());
            }
            if let Some(value) = proof.local_algebraic_values().get(name) {
                algebraic.insert(name.clone(), value.clone());
                locals
                    .retained_match_algebraic
                    .insert(name.clone(), value.clone());
            }
            if let Some(value) = proof.local_integer_values().get(name) {
                integers.insert(name.clone(), value.clone());
                locals
                    .retained_match_integers
                    .insert(name.clone(), value.clone());
            }
        }
        locals
            .value_names
            .update_values(&PersistentBinderMap::default(), &values);
        locals
            .value_names
            .update_algebraics(&PersistentBinderMap::default(), &algebraic);
        locals
            .value_names
            .update_integers(&PersistentBinderMap::default(), &integers);
        Ok(proof.with_kernel_state(proof.state.with_locals(locals)))
    }
}

impl<'a> Proof<'a> {
    pub(in crate::surface::proof) fn new_pure_match_trace(
        &self,
        source: &ProofMatch,
    ) -> Option<crate::surface::proof_trace::TraceMatch> {
        crate::surface::proof_trace::enabled_for(self.claim_label()).then(|| {
            crate::surface::proof_trace::TraceMatch {
                header: format!(
                    "{}: match",
                    self.site().path().unwrap_or_else(|| "checked match".into())
                ),
                source_tactic_path: self.site().source_tactic_path(),
                arms: (0..source.arms.len()).map(|_| None).collect(),
            }
        })
    }

    pub(in crate::surface::proof) fn pure_match_arm_trace(
        &self,
        entered: &Self,
        marker: &ProofCheckpoint<'a>,
        source: &ProofMatch,
        index: usize,
        constructor_equation: &Proposition,
    ) -> crate::surface::proof_trace::TraceMatchArm {
        crate::surface::proof_trace::TraceMatchArm {
            names: Box::new(entered.diagnostic_state()),
            name: format!(
                "{}::{}",
                source.arms[index].type_name, source.arms[index].variant
            ),
            fact: entered.checked_trace_fact(constructor_equation.clone()),
            lineage: trace_arm_lineage(&self.node, &marker.node, self.focused_branch_id()),
            _retained: Box::new(self.node.clone()),
        }
    }
}
