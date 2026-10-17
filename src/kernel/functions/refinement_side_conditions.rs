//! Side conditions of contract refinement and of applying a verified contract: assuming and proving contract propositions, which specifications are state-independent, and which parameters an ensures clause reads after the call.

use super::*;

pub(super) fn assume_contract_propositions(
    state: &CState,
    entry_state: &CState,
    propositions: &[SpecProposition],
    assumptions: &mut PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<bool> {
    for proposition in propositions {
        let paths = lower_spec_proposition_at_state_with_loop_entry(
            state,
            proposition,
            Some(entry_state),
            assumptions,
            budget,
        )?;
        let [path] = paths.as_slice() else {
            return Ok(false);
        };
        for fact in &path.facts {
            *assumptions = assumptions
                .clone()
                .assume_proposition(fact.proposition().clone());
        }
        for obligation in &path.obligations {
            *assumptions = assumptions
                .clone()
                .assume_proposition(obligation.proposition().clone());
        }
        assume_contract_proposition(assumptions, path.proposition.clone());
    }
    Ok(true)
}

/// Adds a contract proposition and the deterministic logical consequences
/// exposed by facts already present in this local refinement context.
pub(super) fn assume_contract_proposition(
    assumptions: &mut PureFactContext,
    proposition: Proposition,
) {
    *assumptions = assumptions.clone().assume_proposition(proposition.clone());
    match proposition {
        Proposition::Equal(Term::Sequence(left), Term::Sequence(right)) => {
            // Linear decomposition of this explicitly selected premise.
            for (left, right) in super::super::spec::sequence_elements(&left)
                .zip(super::super::spec::sequence_elements(&right))
            {
                if let Some(equality) =
                    super::super::spec::integer_sequence_element_equality(left, right)
                {
                    *assumptions = assumptions.clone().assume_proposition(equality);
                }
            }
        }
        Proposition::And(left, right) => {
            assume_contract_proposition(assumptions, *left);
            assume_contract_proposition(assumptions, *right);
        }
        // Modus ponens on an explicitly assumed contract premise, with the
        // antecedent established by the exact routes only. An antecedent
        // those do not decide leaves the implication assumed as written;
        // the consequent then needs an explicit proof step.
        Proposition::Implies(left, right)
            if required_obligation_is_exactly_discharged(assumptions, &left) =>
        {
            assume_contract_proposition(assumptions, *right);
        }
        _ => {}
    }
}

/// The obligation check below is route-restricted with the rest of package
/// 10(b) but has no reaching fixture: a refined requirement's lowered path
/// carries an obligation only when the surrounding refinement context cannot
/// already see the access, and in that case no route — exact or otherwise —
/// discharges it. Attempts through an owned field and through an explicit
/// `requires loadable(...)` both produced obligation-free paths.
pub(super) fn prove_contract_propositions(
    state: &CState,
    entry_state: &CState,
    propositions: &[SpecProposition],
    assumptions: &mut PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<bool> {
    for proposition in propositions {
        let paths = lower_spec_proposition_at_state_with_loop_entry(
            state,
            proposition,
            Some(entry_state),
            assumptions,
            budget,
        )?;
        let [path] = paths.as_slice() else {
            return Ok(false);
        };
        for fact in &path.facts {
            *assumptions = assumptions
                .clone()
                .assume_proposition(fact.proposition().clone());
        }
        if path.obligations.iter().any(|obligation| {
            !required_obligation_is_exactly_discharged(assumptions, obligation.proposition())
        }) || !contract_refinement_proves(assumptions, &path.proposition)
        {
            return Ok(false);
        }
        for obligation in &path.obligations {
            *assumptions = assumptions
                .clone()
                .assume_proposition(obligation.proposition().clone());
        }
        *assumptions = assumptions
            .clone()
            .assume_proposition(path.proposition.clone());
    }
    Ok(true)
}

/// The exact routes a refinement check may use on one leaf proposition:
/// builtin propositions, indexed exact membership in the assumed facts, and
/// the frozen condition decision procedure on a bare condition. It performs
/// no logical search — it never assumes an antecedent, enumerates ambient
/// candidates, or recursively constructs a derivation. `Not` of a bare
/// condition is the same bare condition with the opposite value, which is how
/// `contains_assumed_exact` and `evaluate_guarded_contract_condition` already
/// read it.
pub(super) fn refinement_route_proves(
    assumptions: &PureFactContext,
    proposition: &Proposition,
) -> bool {
    if assumptions.proves_exact(proposition) {
        return true;
    }
    match proposition {
        Proposition::ConditionIs(condition, value) => assumptions.decide(condition) == Some(*value),
        Proposition::Not(body) => match body.as_ref() {
            Proposition::ConditionIs(condition, value) => {
                assumptions.decide(condition) == Some(!*value)
            }
            _ => false,
        },
        _ => false,
    }
}

/// Checks one lowered contract clause against the refinement assumptions.
///
/// This is the exact leaf route and nothing else. The logical descent this
/// used to perform — sequence-element alignment, `and` split, `or` arm
/// choice, `implies` with a refuted antecedent, and a search over recorded
/// equality-class rewrites of a comparison's operands — was kernel proof
/// planning: it chose an index alignment, an arm, and a rewrite
/// representative, and issued refinement authority from that choice with no
/// record of it. Those choices now belong to the refinement theorem's proof,
/// where `both`, `left`/`right`, `intro`, `extract`, and `rewrite` spell them
/// and `click expand` prints them. See `prepare_contract_refinement_obligations`,
/// which emits the refinement implication, and
/// `api.rs::prove_c_function_contract_refinement`, which issues authority only
/// from a closed proof of exactly that implication.
pub(super) fn contract_refinement_proves(
    assumptions: &PureFactContext,
    proposition: &Proposition,
) -> bool {
    refinement_route_proves(assumptions, proposition)
}

pub(super) fn spec_proposition_is_state_independent(proposition: &SpecProposition) -> bool {
    spec_tree_all(SpecNode::Proposition(proposition), state_independent_node)
}

pub(in crate::kernel) fn spec_algebraic_expression_is_state_independent(
    expression: &SpecAlgebraicExpression,
) -> bool {
    spec_tree_all(SpecNode::Algebraic(expression), state_independent_node)
}

/// Whether one spec node reads no program state of its own. Anything not
/// listed reads state, or is not supported here, and refuses.
pub(super) fn state_independent_node(node: SpecNode<'_>) -> Visit<()> {
    match node {
        SpecNode::Proposition(proposition) => match proposition {
            SpecProposition::Comparison { .. }
            | SpecProposition::FloatClassification { .. }
            | SpecProposition::Defined(_)
            | SpecProposition::And(..)
            | SpecProposition::Or(..)
            | SpecProposition::Implies(..)
            | SpecProposition::Not(_)
            | SpecProposition::ForAllMachineInteger { .. }
            | SpecProposition::ForAllInt32 { .. }
            | SpecProposition::ForAllInteger { .. }
            | SpecProposition::ForAllAlgebraic { .. }
            | SpecProposition::ForAllPointer { .. }
            | SpecProposition::ExistsMachineInteger { .. }
            | SpecProposition::ExistsInt32 { .. }
            | SpecProposition::ExistsInteger { .. }
            | SpecProposition::ExistsAlgebraic { .. }
            | SpecProposition::ExistsPointer { .. } => Visit::Descend,
            _ => Visit::Stop(()),
        },
        SpecNode::Expression(expression) => match expression {
            SpecExpression::Value(_) => Visit::Skip,
            SpecExpression::CExpression(expression)
                if c_expression_is_state_independent(expression) =>
            {
                Visit::Skip
            }
            crate::kernel::binary_spec_expression!(_, _)
            | SpecExpression::BitwiseNot(_)
            | SpecExpression::LoopEntrySnapshot(_)
            | SpecExpression::Cast(..)
            | SpecExpression::PointerCoercion(..)
            | SpecExpression::If { .. }
            | SpecExpression::Let { .. }
            | SpecExpression::PureFunctionApplication { .. }
            | SpecExpression::Subobject { .. }
            | SpecExpression::PointerOffset { .. } => Visit::Descend,
            _ => Visit::Stop(()),
        },
        // An Integer value reads the state exactly when a machine value inside
        // it does: `to_integer(*p)` reads `*p`. A `Term` is closed, whether an
        // Integer binder, a constant, or a value already resolved at lowering.
        SpecNode::Integer(integer) => match integer {
            SpecIntegerExpression::Term(_) => Visit::Skip,
            SpecIntegerExpression::FromMachine(_)
            | SpecIntegerExpression::Negate(_)
            | crate::kernel::binary_spec_integer_expression!(_, _)
            | SpecIntegerExpression::PureFunctionApplication { .. } => Visit::Descend,
            SpecIntegerExpression::ResourceField(_)
            | SpecIntegerExpression::AlgebraicMatch { .. }
            | SpecIntegerExpression::RangeFold { .. } => Visit::Stop(()),
        },
        SpecNode::Algebraic(algebraic) => match &algebraic.node {
            SpecAlgebraicExpressionNode::ResourceField(_) => Visit::Stop(()),
            SpecAlgebraicExpressionNode::Variable(_) | SpecAlgebraicExpressionNode::Binding(_) => {
                Visit::Skip
            }
            SpecAlgebraicExpressionNode::Constructor { .. }
            | SpecAlgebraicExpressionNode::Match { .. }
            | SpecAlgebraicExpressionNode::PureFunctionApplication { .. } => Visit::Descend,
        },
        SpecNode::AlgebraicValue(_) => Visit::Descend,
        SpecNode::Argument(SpecPureFunctionArgument::ArrayRef { .. }) => Visit::Stop(()),
        SpecNode::Argument(_) => Visit::Descend,
        SpecNode::PredicateArgument(_) | SpecNode::Sequence(_) | SpecNode::Resource(_) => {
            Visit::Stop(())
        }
    }
}

/// The stateful refinement rule admits ordinary scalar propositions whose only
/// stateful operation is a C memory access (possibly below `old`), including
/// finite sequence comparisons and membership, plus resource-field reads and
/// the algebraic values those fields carry. Explicit memory snapshots,
/// `at(...)`, counted-resource populations, and range folds stay outside it:
/// their stateful refinement laws are not written down, so they need an
/// explicit refinement theorem. Mathematical `Integer` comparisons stay
/// outside it for the same reason. The caller separately checks resource and
/// footprint refinement.
pub(super) fn spec_proposition_supports_stateful_memory_refinement(
    proposition: &SpecProposition,
) -> bool {
    spec_tree_all(
        SpecNode::Proposition(proposition),
        stateful_memory_refinement_node,
    )
}

/// One node of [`spec_proposition_supports_stateful_memory_refinement`].
///
/// Every variant is listed. A new specification form is excluded until its
/// refinement behaviour has been considered, which a wildcard would silently
/// reverse.
pub(super) fn stateful_memory_refinement_node(node: SpecNode<'_>) -> Visit<()> {
    match node {
        SpecNode::Proposition(proposition) => match proposition {
            SpecProposition::SequenceComparison { .. }
            | SpecProposition::SequenceMembership { .. }
            | SpecProposition::Comparison { .. }
            | SpecProposition::AlgebraicComparison { .. }
            | SpecProposition::FloatClassification { .. }
            | SpecProposition::Defined(_)
            | SpecProposition::And(..)
            | SpecProposition::Or(..)
            | SpecProposition::Implies(..)
            | SpecProposition::Not(_)
            | SpecProposition::ForAllMachineInteger { .. }
            | SpecProposition::ForAllInt32 { .. }
            | SpecProposition::ForAllInteger { .. }
            | SpecProposition::ForAllAlgebraic { .. }
            | SpecProposition::ForAllPointer { .. }
            | SpecProposition::ExistsMachineInteger { .. }
            | SpecProposition::ExistsInt32 { .. }
            | SpecProposition::ExistsInteger { .. }
            | SpecProposition::ExistsAlgebraic { .. }
            | SpecProposition::ExistsPointer { .. } => Visit::Descend,
            SpecProposition::IntegerComparison { .. }
            | SpecProposition::Predicate { .. }
            | SpecProposition::ResourceSeparate { .. }
            | SpecProposition::ResourceContains { .. }
            | SpecProposition::MemoryLoadable { .. } => Visit::Stop(()),
        },
        SpecNode::Sequence(_) => Visit::Descend,
        SpecNode::Expression(expression) => match expression {
            // A field read names an instance the two interfaces share. Both the
            // current and the entry projection lower through
            // `resource_instance_at_path` against the state the caller supplies;
            // a projection the state cannot answer refuses the refinement there.
            SpecExpression::ResourceField { .. } | SpecExpression::Value(_) => Visit::Skip,
            SpecExpression::IntegerToMachine { .. } => Visit::Stop(()),
            SpecExpression::CExpression(expression) => {
                if c_expression_supports_stateful_memory_refinement(expression) {
                    Visit::Skip
                } else {
                    Visit::Stop(())
                }
            }
            crate::kernel::binary_spec_expression!(_, _)
            | SpecExpression::BitwiseNot(_)
            | SpecExpression::Cast(..)
            | SpecExpression::PointerCoercion(..)
            | SpecExpression::If { .. }
            | SpecExpression::Let { .. }
            | SpecExpression::PureFunctionApplication { .. }
            | SpecExpression::Subobject { .. }
            | SpecExpression::PointerOffset { .. }
            | SpecExpression::MemoryLoad {
                memory: SpecMemory::Current | SpecMemory::FunctionEntry,
                ..
            }
            | SpecExpression::AlgebraicMatch { .. } => Visit::Descend,
            SpecExpression::CountedResourceCount { .. }
            | SpecExpression::RangeFold { .. }
            | SpecExpression::LoopEntrySnapshot(_)
            | SpecExpression::MemoryLoad { .. }
            | SpecExpression::AggregateFieldValue { .. } => Visit::Stop(()),
        },
        // Algebraic values are ordinary terms over instance fields,
        // constructors, match arms, and opaque pure functions. None of them
        // reads memory except through the `SpecExpression` nodes, which are
        // filtered by the same rule, so an algebraic clause is admitted exactly
        // when its scalar leaves are.
        SpecNode::Algebraic(algebraic) => match &algebraic.node {
            SpecAlgebraicExpressionNode::Variable(_)
            | SpecAlgebraicExpressionNode::Binding(_)
            | SpecAlgebraicExpressionNode::ResourceField(_) => Visit::Skip,
            SpecAlgebraicExpressionNode::Constructor { .. }
            | SpecAlgebraicExpressionNode::Match { .. }
            | SpecAlgebraicExpressionNode::PureFunctionApplication { .. } => Visit::Descend,
        },
        SpecNode::AlgebraicValue(value) => match value {
            SpecAlgebraicValue::C(_) | SpecAlgebraicValue::Algebraic(_) => Visit::Descend,
            // Mathematical `Integer` values keep the exclusion that
            // `SpecPureFunctionArgument::Integer` states.
            SpecAlgebraicValue::Integer(_) => Visit::Stop(()),
        },
        SpecNode::Argument(argument) => match argument {
            SpecPureFunctionArgument::Value(_) | SpecPureFunctionArgument::Algebraic(_) => {
                Visit::Descend
            }
            SpecPureFunctionArgument::Integer(_) => Visit::Stop(()),
            // An array snapshot is an explicit memory image; its stateful
            // refinement law is not written down.
            SpecPureFunctionArgument::ArrayRef { .. } => Visit::Stop(()),
        },
        // Every route to these is refused above, before they are reached.
        SpecNode::Integer(_) | SpecNode::PredicateArgument(_) | SpecNode::Resource(_) => {
            Visit::Stop(())
        }
    }
}

/// The datatype reflexivity shortcut may skip evaluation only for expressions
/// that cannot emit a guard or obligation. State independence alone does not
/// imply totality: a mathematical conversion may have a required domain.
pub(in crate::kernel) fn spec_algebraic_expression_is_obligation_free(
    expression: &SpecAlgebraicExpression,
) -> bool {
    spec_tree_all(SpecNode::Algebraic(expression), obligation_free_node)
}

pub(super) fn obligation_free_node(node: SpecNode<'_>) -> Visit<()> {
    match node {
        SpecNode::Algebraic(algebraic) => match &algebraic.node {
            SpecAlgebraicExpressionNode::Variable(_) | SpecAlgebraicExpressionNode::Binding(_) => {
                Visit::Skip
            }
            SpecAlgebraicExpressionNode::PureFunctionApplication { name, .. }
                if name == "to_nat" =>
            {
                Visit::Stop(())
            }
            SpecAlgebraicExpressionNode::Constructor { .. }
            | SpecAlgebraicExpressionNode::PureFunctionApplication { .. } => Visit::Descend,
            SpecAlgebraicExpressionNode::Match { scrutinee, arms } => {
                if algebraic_match_covers_each_variant_once(scrutinee, arms) {
                    Visit::Descend
                } else {
                    Visit::Stop(())
                }
            }
            SpecAlgebraicExpressionNode::ResourceField(_) => Visit::Stop(()),
        },
        SpecNode::AlgebraicValue(_) => Visit::Descend,
        SpecNode::Argument(SpecPureFunctionArgument::ArrayRef { .. }) => Visit::Stop(()),
        SpecNode::Argument(_) => Visit::Descend,
        // A C value is admitted only as a literal, a variable, or a function
        // address; it is not walked.
        SpecNode::Expression(
            SpecExpression::Value(_)
            | SpecExpression::CExpression(
                CExpression::Value(_) | CExpression::Variable(_) | CExpression::FunctionAddress(_),
            ),
        ) => Visit::Skip,
        SpecNode::Expression(_) => Visit::Stop(()),
        SpecNode::Integer(integer) => match integer {
            SpecIntegerExpression::Term(_) => Visit::Skip,
            SpecIntegerExpression::Negate(_)
            | SpecIntegerExpression::Add(..)
            | SpecIntegerExpression::Subtract(..)
            | SpecIntegerExpression::Multiply(..)
            | SpecIntegerExpression::PureFunctionApplication { .. } => Visit::Descend,
            SpecIntegerExpression::TruncatingQuotient(..)
            | SpecIntegerExpression::TruncatingRemainder(..)
            | SpecIntegerExpression::AlgebraicMatch { .. }
            | SpecIntegerExpression::FromMachine(_)
            | SpecIntegerExpression::ResourceField(_)
            | SpecIntegerExpression::RangeFold { .. } => Visit::Stop(()),
        },
        SpecNode::Proposition(_)
        | SpecNode::PredicateArgument(_)
        | SpecNode::Sequence(_)
        | SpecNode::Resource(_) => Visit::Stop(()),
    }
}

/// Whether a match names each variant of its scrutinee's type exactly once,
/// binding as many names as that variant has fields.
pub(super) fn algebraic_match_covers_each_variant_once(
    scrutinee: &SpecAlgebraicExpression,
    arms: &[SpecAlgebraicResultMatchArm],
) -> bool {
    if arms.len() != scrutinee.algebraic_type.variants.len() {
        return false;
    }
    let variants = scrutinee
        .algebraic_type
        .variants
        .iter()
        .map(|variant| (variant.name.as_str(), variant.fields.len()))
        .collect::<BTreeMap<_, _>>();
    let mut seen = BTreeSet::new();
    arms.iter().all(|arm| {
        seen.insert(arm.variant.as_str())
            && variants.get(arm.variant.as_str()) == Some(&arm.bindings.len())
    })
}

pub(super) fn c_expression_supports_stateful_memory_refinement(expression: &CExpression) -> bool {
    match expression {
        CExpression::Value(_) | CExpression::Variable(_) | CExpression::FunctionAddress(_) => true,
        CExpression::Cast { expression, .. }
        | CExpression::FloatNegate(expression)
        | CExpression::FloatClassification { expression, .. }
        | CExpression::AddressOf(expression)
        | CExpression::CheckedObjectAddress(expression)
        | CExpression::PointerOffsetBytes {
            pointer: expression,
            ..
        }
        | CExpression::Subobject {
            pointer: expression,
            ..
        }
        | CExpression::Not(expression)
        | CExpression::BitwiseNot(expression)
        | CExpression::Load(expression) => {
            c_expression_supports_stateful_memory_refinement(expression)
        }
        CExpression::TypedLoad { pointer, .. } => {
            c_expression_supports_stateful_memory_refinement(pointer)
        }
        CExpression::Conditional {
            condition,
            then_branch,
            else_branch,
        } => {
            c_expression_supports_stateful_memory_refinement(condition)
                && c_expression_supports_stateful_memory_refinement(then_branch)
                && c_expression_supports_stateful_memory_refinement(else_branch)
        }
        crate::kernel::binary_c_expression!(left, right) => {
            c_expression_supports_stateful_memory_refinement(left)
                && c_expression_supports_stateful_memory_refinement(right)
        }
    }
}

pub(in crate::kernel) fn c_expression_is_state_independent(expression: &CExpression) -> bool {
    match expression {
        CExpression::Value(_) | CExpression::Variable(_) | CExpression::FunctionAddress(_) => true,
        CExpression::Cast { expression, .. }
        | CExpression::FloatNegate(expression)
        | CExpression::FloatClassification { expression, .. }
        | CExpression::PointerOffsetBytes {
            pointer: expression,
            ..
        }
        | CExpression::Subobject {
            pointer: expression,
            ..
        }
        | CExpression::Not(expression)
        | CExpression::BitwiseNot(expression) => c_expression_is_state_independent(expression),
        CExpression::Conditional {
            condition,
            then_branch,
            else_branch,
        } => {
            c_expression_is_state_independent(condition)
                && c_expression_is_state_independent(then_branch)
                && c_expression_is_state_independent(else_branch)
        }
        crate::kernel::binary_c_operation!(left, right) => {
            c_expression_is_state_independent(left) && c_expression_is_state_independent(right)
        }
        CExpression::AddressOf(_)
        | CExpression::CheckedObjectAddress(_)
        | CExpression::Load(_)
        | CExpression::TypedLoad { .. }
        | CExpression::Index(_, _) => false,
    }
}

/// Whether a specification subtree reads a by-value aggregate parameter
/// from the current callee state. Entry-state reads (`old(...)`) use
/// `SpecMemory::FunctionEntry` and are intentionally ignored: they describe
/// the caller's argument image, which is stable across the call.
pub(super) fn spec_reads_current_parameter(node: SpecNode<'_>, parameter_name: &str) -> bool {
    !spec_tree_all(node, |node| match node {
        SpecNode::Expression(SpecExpression::CExpression(expression))
            if c_expression_mentions_variable(expression, parameter_name) =>
        {
            Visit::Stop(())
        }
        SpecNode::Expression(SpecExpression::MemoryLoad { memory, .. })
        | SpecNode::Proposition(SpecProposition::MemoryLoadable { memory, .. })
        | SpecNode::PredicateArgument(SpecPredicateArgument::ArrayRef { memory, .. })
        | SpecNode::Argument(SpecPureFunctionArgument::ArrayRef { memory, .. })
            if matches!(memory, SpecMemory::FunctionEntry | SpecMemory::Fixed(_)) =>
        {
            Visit::Skip
        }
        _ => Visit::Descend,
    })
}

pub(super) fn c_expression_mentions_variable(expression: &CExpression, name: &str) -> bool {
    match expression {
        CExpression::Variable(variable) => variable == name,
        CExpression::Value(_) | CExpression::FunctionAddress(_) => false,
        CExpression::Cast { expression, .. }
        | CExpression::FloatNegate(expression)
        | CExpression::FloatClassification { expression, .. }
        | CExpression::AddressOf(expression)
        | CExpression::CheckedObjectAddress(expression)
        | CExpression::PointerOffsetBytes {
            pointer: expression,
            ..
        }
        | CExpression::Subobject {
            pointer: expression,
            ..
        }
        | CExpression::Not(expression)
        | CExpression::Load(expression)
        | CExpression::TypedLoad {
            pointer: expression,
            ..
        }
        | CExpression::BitwiseNot(expression) => c_expression_mentions_variable(expression, name),
        CExpression::Conditional {
            condition,
            then_branch,
            else_branch,
        } => {
            c_expression_mentions_variable(condition, name)
                || c_expression_mentions_variable(then_branch, name)
                || c_expression_mentions_variable(else_branch, name)
        }
        crate::kernel::binary_c_expression!(left, right) => {
            c_expression_mentions_variable(left, name)
                || c_expression_mentions_variable(right, name)
        }
    }
}

pub(super) fn c_expression_takes_address_of_variable(expression: &CExpression, name: &str) -> bool {
    match expression {
        CExpression::AddressOf(expression) | CExpression::CheckedObjectAddress(expression) => {
            c_expression_mentions_variable(expression, name)
        }
        CExpression::Value(_) | CExpression::Variable(_) | CExpression::FunctionAddress(_) => false,
        CExpression::Cast { expression, .. }
        | CExpression::FloatNegate(expression)
        | CExpression::FloatClassification { expression, .. }
        | CExpression::PointerOffsetBytes {
            pointer: expression,
            ..
        }
        | CExpression::Subobject {
            pointer: expression,
            ..
        }
        | CExpression::Not(expression)
        | CExpression::Load(expression)
        | CExpression::TypedLoad {
            pointer: expression,
            ..
        }
        | CExpression::BitwiseNot(expression) => {
            c_expression_takes_address_of_variable(expression, name)
        }
        CExpression::Conditional {
            condition,
            then_branch,
            else_branch,
        } => {
            c_expression_takes_address_of_variable(condition, name)
                || c_expression_takes_address_of_variable(then_branch, name)
                || c_expression_takes_address_of_variable(else_branch, name)
        }
        crate::kernel::binary_c_expression!(left, right) => {
            c_expression_takes_address_of_variable(left, name)
                || c_expression_takes_address_of_variable(right, name)
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct ParameterAccessRange {
    start: u32,
    end: u32,
}

pub(super) fn parameter_access_range(start: u32, width: u32) -> Option<ParameterAccessRange> {
    (width > 0).then_some(())?;
    Some(ParameterAccessRange {
        start,
        end: start.checked_add(width)?,
    })
}

impl ParameterAccessRange {
    pub(super) fn overlaps(self, other: Self) -> bool {
        self.start < other.end && other.start < self.end
    }
}

pub(super) fn c_expression_parameter_offset(
    expression: &CExpression,
    parameter_name: &str,
) -> Option<u32> {
    match expression {
        CExpression::Variable(variable) if variable == parameter_name => Some(0),
        CExpression::PointerOffsetBytes { pointer, bytes } => {
            c_expression_parameter_offset(pointer, parameter_name)?.checked_add(*bytes)
        }
        CExpression::Subobject { pointer, .. } => {
            c_expression_parameter_offset(pointer, parameter_name)
        }
        CExpression::Cast { expression, .. } => {
            c_expression_parameter_offset(expression, parameter_name)
        }
        _ => None,
    }
}

pub(super) fn spec_expression_constant(expression: &SpecExpression) -> Option<u32> {
    let SpecExpression::Value(value) = expression else {
        return None;
    };
    match value.numeric_value() {
        CValue::PointerInteger(_) => unreachable!("numeric projection"),
        CValue::Int8(term) => term.as_const(),
        CValue::Int16(term)
        | CValue::Int32(term)
        | CValue::UInt8(term)
        | CValue::UInt16(term)
        | CValue::UInt32(term)
        | CValue::Int64(term)
        | CValue::UInt64(term) => term.as_const(),
        CValue::Int128(_)
        | CValue::UInt128(_)
        | CValue::Void
        | CValue::Float32(_)
        | CValue::Float64(_)
        | CValue::Pointer(_) => None,
        CValue::Bool(term) => term.as_const(),
    }
}

pub(super) fn spec_expression_parameter_offset(
    expression: &SpecExpression,
    parameter_name: &str,
) -> Option<u32> {
    match expression {
        SpecExpression::CExpression(expression) => {
            c_expression_parameter_offset(expression, parameter_name)
        }
        SpecExpression::Cast(expression, _)
        | SpecExpression::PointerCoercion(expression, _)
        | SpecExpression::LoopEntrySnapshot(expression)
        | SpecExpression::Subobject {
            pointer: expression,
            ..
        } => spec_expression_parameter_offset(expression, parameter_name),
        SpecExpression::PointerOffset {
            pointer,
            elements,
            byte_width,
        } => spec_expression_parameter_offset(pointer, parameter_name)?
            .checked_add(spec_expression_constant(elements)?.checked_mul(*byte_width)?),
        _ => None,
    }
}

/// Track storage provenance rather than reads used to compute a store's
/// address. The exit-state check still detects writes through local aliases.
pub(super) fn c_expression_uses_object_address(expression: &CExpression, name: &str) -> bool {
    match expression {
        CExpression::Variable(variable) => variable == name,
        CExpression::Value(_) | CExpression::FunctionAddress(_) => false,
        // A scalar or pointer load produces a value, not the address of the
        // containing object. Inline arrays still denote embedded storage.
        CExpression::TypedLoad {
            pointer,
            value_type: CType::Int32Array(_) | CType::UInt8Array(_),
            ..
        } => c_expression_uses_object_address(pointer, name),
        CExpression::Load(_) | CExpression::TypedLoad { .. } => false,
        CExpression::AddressOf(expression) | CExpression::CheckedObjectAddress(expression) => {
            match expression.as_ref() {
                CExpression::Load(pointer) | CExpression::TypedLoad { pointer, .. } => {
                    c_expression_uses_object_address(pointer, name)
                }
                expression => c_expression_uses_object_address(expression, name),
            }
        }

        CExpression::Cast { expression, .. }
        | CExpression::FloatNegate(expression)
        | CExpression::FloatClassification { expression, .. }
        | CExpression::PointerOffsetBytes {
            pointer: expression,
            ..
        }
        | CExpression::Subobject {
            pointer: expression,
            ..
        }
        | CExpression::Not(expression)
        | CExpression::BitwiseNot(expression) => c_expression_uses_object_address(expression, name),
        CExpression::Conditional {
            condition,
            then_branch,
            else_branch,
        } => {
            c_expression_uses_object_address(condition, name)
                || c_expression_uses_object_address(then_branch, name)
                || c_expression_uses_object_address(else_branch, name)
        }
        crate::kernel::binary_c_expression!(left, right) => {
            c_expression_uses_object_address(left, name)
                || c_expression_uses_object_address(right, name)
        }
    }
}

pub(super) fn statement_writes_aggregate_parameter(
    statement: &CStatement,
    parameter_name: &str,
    writes: &mut Vec<ParameterAccessRange>,
    unknown_write: &mut bool,
) {
    match statement {
        CStatement::Store { pointer, .. } => {
            if c_expression_parameter_offset(pointer, parameter_name).is_some()
                || c_expression_uses_object_address(pointer, parameter_name)
            {
                *unknown_write = true;
            }
        }
        CStatement::TypedStore {
            pointer,
            value_type,
            ..
        } => {
            if let Some(offset) = c_expression_parameter_offset(pointer, parameter_name) {
                if let Some(range) = parameter_access_range(offset, value_type.byte_width()) {
                    writes.push(range);
                }
            } else if c_expression_uses_object_address(pointer, parameter_name) {
                *unknown_write = true;
            }
        }
        CStatement::InitializeScalarArray {
            target,
            element_type,
            count,
            ..
        } => {
            if let Some(offset) = c_expression_parameter_offset(target, parameter_name) {
                if let Some(bytes) = element_type.byte_width().checked_mul(*count)
                    && let Some(range) = parameter_access_range(offset, bytes)
                {
                    writes.push(range);
                } else {
                    *unknown_write = true;
                }
            } else if c_expression_uses_object_address(target, parameter_name) {
                *unknown_write = true;
            }
        }
        CStatement::CopyAggregate { target, layout, .. } => {
            if let Some(offset) = c_expression_parameter_offset(target, parameter_name) {
                if let Some(range) = parameter_access_range(offset, layout.size_bytes()) {
                    writes.push(range);
                }
            } else if c_expression_uses_object_address(target, parameter_name) {
                *unknown_write = true;
            }
        }
        CStatement::Update { target, .. } => {
            let pointer = match target {
                CExpression::Load(pointer)
                | CExpression::TypedLoad { pointer, .. }
                | CExpression::Index(pointer, _) => pointer.as_ref(),
                target => target,
            };
            if c_expression_uses_object_address(pointer, parameter_name) {
                *unknown_write = true;
            }
        }
        CStatement::Call { arguments, .. } | CStatement::CallAssign { arguments, .. } => {
            if arguments
                .iter()
                .any(|argument| c_expression_takes_address_of_variable(argument, parameter_name))
            {
                *unknown_write = true;
            }
        }
        CStatement::Seq(first, second) => {
            statement_writes_aggregate_parameter(first, parameter_name, writes, unknown_write);
            statement_writes_aggregate_parameter(second, parameter_name, writes, unknown_write);
        }
        CStatement::If {
            then_branch,
            else_branch,
            ..
        } => {
            statement_writes_aggregate_parameter(
                then_branch,
                parameter_name,
                writes,
                unknown_write,
            );
            statement_writes_aggregate_parameter(
                else_branch,
                parameter_name,
                writes,
                unknown_write,
            );
        }
        CStatement::TryCatchInt32 {
            try_body, handler, ..
        } => {
            statement_writes_aggregate_parameter(try_body, parameter_name, writes, unknown_write);
            statement_writes_aggregate_parameter(handler, parameter_name, writes, unknown_write);
        }
        CStatement::ForStep { step, .. } => {
            statement_writes_aggregate_parameter(step, parameter_name, writes, unknown_write);
        }
        CStatement::While { body, .. } => {
            statement_writes_aggregate_parameter(body, parameter_name, writes, unknown_write);
        }
        CStatement::Switch { cases, .. } => {
            for case in cases {
                statement_writes_aggregate_parameter(
                    &case.body,
                    parameter_name,
                    writes,
                    unknown_write,
                );
            }
        }
        CStatement::Skip
        | CStatement::EndScalarReference(_)
        | CStatement::ScalarReferenceScope(_)
        | CStatement::EndAutomaticLifetimes { .. }
        | CStatement::Break
        | CStatement::Continue
        | CStatement::Goto { .. }
        | CStatement::Declare { .. }
        | CStatement::DeclareAggregate { .. }
        | CStatement::Assign { .. }
        | CStatement::HeapAllocate { .. }
        | CStatement::HeapFree { .. }
        | CStatement::Assert { .. }
        | CStatement::Throw(_)
        | CStatement::Return(_) => {}
    }
}

/// Collects the byte ranges of `parameter_name` that `proposition` reads from
/// the current callee state, in source order. A read whose range is not a
/// constant offset from the parameter sets `unknown_read` instead.
pub(super) fn spec_proposition_current_parameter_accesses(
    proposition: &SpecProposition,
    parameter_name: &str,
    reads: &mut Vec<ParameterAccessRange>,
    unknown_read: &mut bool,
) {
    spec_tree_all(SpecNode::Proposition(proposition), |node| {
        match node {
            SpecNode::Expression(SpecExpression::IntegerToMachine { .. }) => *unknown_read = true,
            SpecNode::Expression(
                SpecExpression::AggregateFieldValue {
                    pointer,
                    value_type,
                    ..
                }
                | SpecExpression::MemoryLoad {
                    memory: SpecMemory::Current,
                    pointer,
                    value_type,
                },
            ) => match spec_expression_parameter_offset(pointer, parameter_name) {
                Some(offset) => {
                    reads.extend(parameter_access_range(offset, value_type.byte_width()))
                }
                None => {
                    *unknown_read |=
                        spec_reads_current_parameter(SpecNode::Expression(pointer), parameter_name)
                }
            },
            // These reads have no precise byte range here, so any read of the
            // parameter is an unknown read. An Integer read is one of them.
            SpecNode::Integer(_)
            | SpecNode::Expression(
                SpecExpression::CExpression(_) | SpecExpression::MemoryLoad { .. },
            )
            | SpecNode::Proposition(SpecProposition::MemoryLoadable { .. })
            | SpecNode::PredicateArgument(SpecPredicateArgument::ArrayRef { .. })
            | SpecNode::Argument(SpecPureFunctionArgument::ArrayRef { .. })
            | SpecNode::Resource(SpecResource::Memory { .. }) => {
                *unknown_read |= spec_reads_current_parameter(node, parameter_name)
            }
            _ => return Visit::Descend,
        }
        Visit::Skip
    });
}

/// Rejects a postcondition that would expose a modified by-value aggregate
/// parameter through the caller-side contract view. This source-level check
/// runs while the function contract is assembled, before any proof tactic can
/// publish the private copy as a caller fact.
pub(crate) fn modified_by_value_aggregate_parameter_with_current_ensure_in_source(
    function: &CFunction,
) -> Option<String> {
    function
        .parameters()
        .iter()
        .filter(|parameter| parameter.aggregate_layout().is_some())
        .find(|parameter| {
            let mut writes = Vec::new();
            let mut unknown_write = false;
            statement_writes_aggregate_parameter(
                function.source_body(),
                parameter.name(),
                &mut writes,
                &mut unknown_write,
            );
            if writes.is_empty() && !unknown_write {
                return false;
            }
            let mut reads = Vec::new();
            let mut unknown_read = false;
            for ensure in function.contract_ensures() {
                spec_proposition_current_parameter_accesses(
                    ensure,
                    parameter.name(),
                    &mut reads,
                    &mut unknown_read,
                );
            }
            (unknown_write && (unknown_read || !reads.is_empty()))
                || (unknown_read && !writes.is_empty())
                || writes
                    .iter()
                    .any(|write| reads.iter().any(|read| write.overlaps(*read)))
        })
        .map(|parameter| parameter.name().to_string())
}

pub(super) fn statement_outcome_state(outcome: &CStatementOutcome) -> Option<&CState> {
    match outcome {
        CStatementOutcome::Normal(state)
        | CStatementOutcome::Break(state)
        | CStatementOutcome::Continue(state)
        | CStatementOutcome::Jump { state, .. } => Some(state),
        CStatementOutcome::Return { state, .. } | CStatementOutcome::Throw { state, .. } => {
            Some(state)
        }
        CStatementOutcome::VerificationDiverges
        | CStatementOutcome::UndefinedBehavior(_)
        | CStatementOutcome::RuntimeError(_) => None,
    }
}

pub(super) fn aggregate_parameter_copy_changed(
    entry_state: &CState,
    outcome: &CStatementOutcome,
    parameter: &CParameter,
) -> bool {
    let Some(exit_state) = statement_outcome_state(outcome) else {
        return false;
    };
    let Some(CLocalBinding::AggregateObject { slot, layout, .. }) =
        entry_state.locals.binding(parameter.name())
    else {
        return false;
    };
    let end = i64::from(layout.size_bytes());
    entry_state
        .memory
        .differing_cell_pointers(&exit_state.memory)
        .into_iter()
        .any(|pointer| {
            pointer.block == slot.block
                && pointer
                    .offset
                    .as_const()
                    .is_some_and(|offset| offset >= 0 && offset < end)
        })
}

pub(super) fn modified_by_value_aggregate_parameter_with_current_ensure(
    entry_state: &CState,
    outcome: &CStatementOutcome,
    function: &CFunction,
) -> Option<String> {
    let ensures = match outcome {
        CStatementOutcome::Return { .. } => function.contract_ensures(),
        CStatementOutcome::Throw { .. } => function.exceptional_ensures(),
        _ => &[],
    };
    function
        .parameters()
        .iter()
        .filter(|parameter| parameter.aggregate_layout().is_some())
        .find(|parameter| {
            aggregate_parameter_copy_changed(entry_state, outcome, parameter)
                && ensures.iter().any(|ensure| {
                    spec_reads_current_parameter(SpecNode::Proposition(ensure), parameter.name())
                })
        })
        .map(|parameter| parameter.name().to_string())
}
