//! Sort-preserving congruence and explicitly directed conditional reduction.
//! SymbolicMemory states are opaque: this walks the selected logical expression,
//! never a heap or an ambient proof state.
use crate::kernel::CompareRelation;
#[cfg(test)]
use crate::kernel::binary_node;
use crate::kernel::execution_value::storage_keys::OffsetKey;
use crate::kernel::int32_constant;
use crate::kernel::*;
use crate::kernel::{
    AlgebraicBitvectorMatchArm, AlgebraicResultMatchArm, AlgebraicTerm, AlgebraicTermNode,
    AlgebraicValue, PureFunctionArgument,
};
use crate::kernel::{MachineCastSpelling, OldMachineTerm, cast_term};
use crate::kernel::{OffsetTree, OffsetView};
#[cfg(test)]
use num_traits::ToPrimitive;
use std::collections::HashMap;
use std::collections::{BTreeMap, BTreeSet};

#[cfg(test)]
mod algebraic_match_tests;
mod common_boolean;
#[cfg(test)]
mod graph_condition_tests;
#[cfg(test)]
mod integer_conditional_tests;
#[cfg(test)]
mod pointer_application_tests;
mod retained_boolean;
#[allow(dead_code)]
mod retained_folds;
mod retained_integer;
#[allow(dead_code)]
mod retained_matches;
mod retained_scalar_boolean;
mod shared_comparison;
pub(in crate::kernel) use common_boolean::{
    substitute_application_address_bits, substitute_application_address_pointer,
    substitute_pointer_boolean_value,
};
#[cfg(test)]
mod shared_source_tests;
mod shared_wide_syntax;
mod spec_rewrite;

thread_local! {
    // Completed arithmetic comparisons depend only on immutable terms and
    // their registered read identities. Reset with the load-origin session.
    static ARITHMETIC_COMPARISONS: std::cell::RefCell<HashMap<Proposition, Option<Proposition>>> =
        std::cell::RefCell::new(HashMap::new());
}

pub(crate) fn clear_arithmetic_comparison_cache() {
    ARITHMETIC_COMPARISONS.with(|cache| cache.borrow_mut().clear());
    shared_comparison::clear();
    shared_wide_syntax::clear();
}

fn collect_machine_carriers(machine: &SharedMachineIntegerTerm, variables: &mut CarrierVariables) {
    collect_machine_operand_carriers(machine.operand_view(), variables);
}

fn collect_machine_operand_carriers(
    operand: MachineOperandView<'_>,
    variables: &mut CarrierVariables,
) {
    let root = match operand {
        MachineOperandView::Shared(root) => root,
        MachineOperandView::Old(term) => {
            collect_bitvector_carriers(term, variables);
            return;
        }
    };
    if !variables.shared_machine_operands.insert(root.id()) {
        return;
    }
    if let Some(leaves) = shared_machine_conversion_leaves(root, || variables.visit()) {
        for (_, leaf) in leaves.iter() {
            if let KernelTermNode::Match(matched) = leaf.node() {
                retained_matches::collect_match_carriers(matched, variables);
                continue;
            }
            if let KernelTermNode::Fold(fold) = leaf.node() {
                variables.program_values.insert(fold.accumulator);
                variables.program_values.insert(fold.item);
                for child in &fold.arguments {
                    collect_machine_operand_carriers(MachineOperandView::Shared(child), variables);
                }
                continue;
            }
            if matches!(leaf.node(), KernelTermNode::FloatConvert { .. }) {
                collect_bitvector_carriers(
                    &KernelTermExport::machine(leaf).expect("float conversion"),
                    variables,
                );
                continue;
            }
            collect_bitvector_carriers(
                leaf.machine_conversion_leaf().expect("conversion leaf"),
                variables,
            );
        }
    }
    if let Some(reads) = shared_machine_read_leaves(root, || variables.visit()) {
        for (_, read) in reads.iter() {
            let (memory, pointer, kind) =
                MachineOperandView::Shared(read).read().expect("read leaf");
            if let Some(terms) = &mut variables.read_terms {
                terms
                    .entry((memory.arena_id(), pointer.clone(), kind))
                    .or_insert_with(|| read.machine_read_leaf().expect("read leaf").clone());
            }
            collect_pointer_carriers(pointer, variables);
        }
    }
    let written = shared_machine_syntax_variables(root, || variables.visit());
    let Some(written) = written else {
        return;
    };
    for variable in written.iter() {
        if !variables.visit() {
            return;
        }
        variables.program_values.insert(*variable);
        collect_registered_load_carriers(*variable, variables);
    }
}

#[derive(Clone, Default)]
struct RewriteScope {
    program_values: BTreeMap<Variable, Variable>,
    integer: BTreeMap<Variable, Variable>,
    algebraic: BTreeMap<Variable, Variable>,
}

#[derive(Clone, Copy)]
pub(crate) enum BindingCarrier {
    Program,
    Integer,
    Algebraic,
}

/// A constructor field may carry either a scalar program term or a pointer.  Keep
/// that distinction while rewriting so a same-ID binding in another carrier
/// cannot be substituted accidentally.
#[derive(Clone)]
pub(crate) enum TypedProgramValueReplacement {
    Bitvector(OldMachineTerm),
    /// The whole value: a use of the bound variable's address adopts its
    /// subobject bounds.
    Pointer(OldPointer),
}

type MatchFieldReplacements = (
    BTreeMap<Variable, TypedProgramValueReplacement>,
    BTreeMap<Variable, IntegerTerm>,
    BTreeMap<Variable, AlgebraicTerm>,
);

fn match_field_replacements(
    bindings: &[AlgebraicValue],
    fields: &[AlgebraicValue],
    types: &[AlgebraicValueType],
) -> Option<MatchFieldReplacements> {
    let mut program_replacements = BTreeMap::new();
    let mut integer_replacements = BTreeMap::new();
    let mut algebraic_replacements = BTreeMap::new();
    for ((binding, field), expected) in bindings.iter().zip(fields).zip(types) {
        if !field.has_type(expected) {
            return None;
        }
        let (carrier, variable) = typed_binding_variable(expected, binding)?;
        let duplicate = match (carrier, field) {
            (BindingCarrier::Program, AlgebraicValue::Program(value)) => {
                let replacement = typed_field_replacement(binding, value)?;
                program_replacements.insert(variable, replacement).is_some()
            }
            (BindingCarrier::Integer, AlgebraicValue::Integer(value)) => integer_replacements
                .insert(variable, value.clone())
                .is_some(),
            (BindingCarrier::Algebraic, AlgebraicValue::Algebraic(value)) => algebraic_replacements
                .insert(variable, value.clone())
                .is_some(),
            // A value of a Rust type parameter is a term of its type.
            (
                BindingCarrier::Algebraic,
                AlgebraicValue::Program(ProgramValue::Parameter(value)),
            ) => algebraic_replacements
                .insert(variable, (**value).clone())
                .is_some(),
            _ => return None,
        };
        if duplicate {
            return None;
        }
    }
    Some((
        program_replacements,
        integer_replacements,
        algebraic_replacements,
    ))
}

struct TypedVariableReplacements<'a> {
    program_values: &'a BTreeMap<Variable, TypedProgramValueReplacement>,
    integer: &'a BTreeMap<Variable, IntegerTerm>,
    algebraic: &'a BTreeMap<Variable, AlgebraicTerm>,
}

enum ScopeChange {
    Program(Variable, Option<Variable>),
    Integer(Variable, Option<Variable>),
    Algebraic(Variable, Option<Variable>),
}

// Fold scopes use the same carrier maps as match scopes.  This separate log
// records only the temporary fold changes, so restoring a fold cannot disturb
// an enclosing algebraic match's scope changes.
enum FoldScopeChange {
    Program(Variable, Option<Variable>),
    Integer(Variable, Option<Variable>),
}

#[derive(Clone, Default)]
struct CarrierVariables {
    program_values: BTreeSet<Variable>,
    integer: BTreeSet<Variable>,
    algebraic: BTreeSet<Variable>,
    nodes: usize,
    charge_work: bool,
    budgeted: bool,
    work_exhausted: bool,
    registered_loads: BTreeSet<Variable>,
    pointer_loads: BTreeSet<crate::kernel::Load>,
    pointer_applications: BTreeSet<u64>,
    shared_machine_operands: BTreeSet<u64>,
    mathematical_integers: BTreeSet<u64>,
    pointer_terms: Option<Vec<Address>>,
    read_terms: Option<BTreeMap<((u32, u32), Address, LoadKind), OldMachineTerm>>,
}

impl CarrierVariables {
    fn for_rewrite(budgeted: bool) -> Self {
        Self {
            charge_work: true,
            budgeted,
            ..Self::default()
        }
    }

    fn contains(&self, carrier: BindingCarrier, variable: Variable) -> bool {
        match carrier {
            BindingCarrier::Program => self.program_values.contains(&variable),
            BindingCarrier::Integer => self.integer.contains(&variable),
            BindingCarrier::Algebraic => self.algebraic.contains(&variable),
        }
    }

    fn visit(&mut self) -> bool {
        if self.work_exhausted {
            return false;
        }
        self.nodes = self.nodes.saturating_add(1);
        if !self.charge_work {
            return true;
        }
        self.work_exhausted = if self.budgeted {
            crate::instrumentation::deadline_exceeded_with_work(1)
        } else {
            crate::instrumentation::record_deterministic_work(1);
            false
        };
        !self.work_exhausted
    }

    fn exhausted(&self) -> bool {
        self.work_exhausted
    }
}

pub(super) fn is_simple_int32_match(value: &OldMachineTerm) -> bool {
    let OldMachineTerm::AlgebraicMatch { arms, .. } = value else {
        return false;
    };
    arms.iter().all(|arm| {
        arm.body.as_const().is_some()
            || matches!(&arm.body, OldMachineTerm::Variable(variable) if arm.bindings.iter().any(|binding|
                matches!(binding, AlgebraicValue::Program(ProgramValue::Int32(OldMachineTerm::Variable(bound))) if bound == variable)))
    })
}

fn program_value_variable(value: &ProgramValue) -> Option<Variable> {
    match value {
        ProgramValue::PointerInteger(record) => program_value_variable(&record.numeric),
        ProgramValue::Int8(OldMachineTerm::Variable(variable)) => Some(*variable),
        // A `Bool` binder (Stage 5), carried as its cast.
        ProgramValue::Bool(OldMachineTerm::BoolCast { value, .. })
            if matches!(value.as_ref(), crate::kernel::OldConditionTerm::Variable(_)) =>
        {
            match value.as_ref() {
                crate::kernel::OldConditionTerm::Variable(variable) => Some(*variable),
                _ => None,
            }
        }
        ProgramValue::Bool(OldMachineTerm::Variable(variable))
        | ProgramValue::Int16(OldMachineTerm::Variable(variable))
        | ProgramValue::UInt8(OldMachineTerm::Variable(variable))
        | ProgramValue::UInt16(OldMachineTerm::Variable(variable))
        | ProgramValue::Int32(OldMachineTerm::Variable(variable))
        | ProgramValue::UInt32(OldMachineTerm::Variable(variable))
        | ProgramValue::Int64(OldMachineTerm::Variable(variable))
        | ProgramValue::UInt64(OldMachineTerm::Variable(variable))
        | ProgramValue::Float32(OldMachineTerm::Variable(variable))
        | ProgramValue::Float64(OldMachineTerm::Variable(variable)) => Some(*variable),
        ProgramValue::Pointer(pointer) => match &pointer.base {
            AddressBase::Symbolic(variable) | AddressBase::FunctionSymbolic(variable) => {
                Some(*variable)
            }
            _ => None,
        },
        _ => None,
    }
}

fn typed_program_replacement(value: &ProgramValue) -> Option<TypedProgramValueReplacement> {
    match value {
        ProgramValue::PointerInteger(record) => typed_program_replacement(&record.numeric),
        ProgramValue::Int8(term) => Some(TypedProgramValueReplacement::Bitvector(term.clone())),
        ProgramValue::Bool(term)
        | ProgramValue::Int16(term)
        | ProgramValue::UInt8(term)
        | ProgramValue::UInt16(term)
        | ProgramValue::Int32(term)
        | ProgramValue::UInt32(term)
        | ProgramValue::Int64(term)
        | ProgramValue::UInt64(term)
        | ProgramValue::Int128(term)
        | ProgramValue::UInt128(term)
        | ProgramValue::Float32(term)
        | ProgramValue::Float64(term) => {
            Some(TypedProgramValueReplacement::Bitvector(term.clone()))
        }
        ProgramValue::Pointer(pointer) => {
            Some(TypedProgramValueReplacement::Pointer(pointer.clone()))
        }
        ProgramValue::Parameter(_) => None,
        ProgramValue::Void => None,
    }
}

pub(super) fn binding_variable(value: &AlgebraicValue) -> Option<(BindingCarrier, Variable)> {
    match value {
        AlgebraicValue::Program(value) => {
            program_value_variable(value).map(|variable| (BindingCarrier::Program, variable))
        }
        AlgebraicValue::Integer(IntegerTerm::Variable(variable)) => {
            Some((BindingCarrier::Integer, *variable))
        }
        AlgebraicValue::Algebraic(AlgebraicTerm {
            node: AlgebraicTermNode::Variable(variable),
            ..
        }) => Some((BindingCarrier::Algebraic, *variable)),
        _ => None,
    }
}

/// Read an already typed declaration without a constructor field to replace.
pub(crate) fn typed_declaration_variable(
    binding: &AlgebraicValue,
) -> Option<(BindingCarrier, Variable)> {
    typed_binding_variable(&binding.value_type(), binding)
}

fn typed_binding_variable(
    expected: &AlgebraicValueType,
    binding: &AlgebraicValue,
) -> Option<(BindingCarrier, Variable)> {
    match (expected, binding) {
        (AlgebraicValueType::Integer, AlgebraicValue::Integer(IntegerTerm::Variable(variable))) => {
            Some((BindingCarrier::Integer, *variable))
        }
        // A value of a Rust type parameter is a term of its type.
        (expected, AlgebraicValue::Program(value @ ProgramValue::Parameter(term)))
            if expected.accepts_program_value(value) =>
        {
            match &term.node {
                AlgebraicTermNode::Variable(variable) => {
                    Some((BindingCarrier::Algebraic, *variable))
                }
                _ => None,
            }
        }
        (expected, AlgebraicValue::Program(value)) if expected.accepts_program_value(value) => {
            program_declaration_variable(value).map(|variable| (BindingCarrier::Program, variable))
        }
        (
            AlgebraicValueType::Algebraic { .. } | AlgebraicValueType::Parameter(_),
            AlgebraicValue::Algebraic(value),
        ) if value.algebraic_type.value_type() == *expected
            && matches!(&value.node, AlgebraicTermNode::Variable(_)) =>
        {
            let AlgebraicTermNode::Variable(variable) = &value.node else {
                unreachable!()
            };
            Some((BindingCarrier::Algebraic, *variable))
        }
        _ => None,
    }
}

/// The integer a `bool` value converts, `w` in C's conversion `w != 0`
/// (Stage 5: the cast of the `Bool` `not (w == 0)`), or `None`.
fn bool_operand(term: &OldMachineTerm) -> Option<&OldMachineTerm> {
    let condition = term.bool_cast_operand()?.bool_negation_operand()?;
    let OldConditionTerm::Compare {
        format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
        relation: CompareRelation::Equal,
        left: operand,
        right: zero,
    } = condition
    else {
        return None;
    };
    matches!(zero.as_ref(), int32_constant!(0)).then_some(operand.as_ref())
}

/// The variable of a `bool` match binder: a `Bool` binder carried as its
/// cast (Stage 5), or C's conversion of a fresh variable to `bool`.
fn bool_binder_variable(value: &ProgramValue) -> Option<Variable> {
    let ProgramValue::Bool(term) = value else {
        return None;
    };
    if let Some(OldConditionTerm::Variable(variable)) = term.bool_cast_operand() {
        return Some(*variable);
    }
    match bool_operand(term)? {
        OldMachineTerm::Variable(variable) => Some(*variable),
        _ => None,
    }
}

/// What the variable of match binder `binding` is replaced by for constructor
/// field `field`. A `Bool` binder takes the field's `Bool`, whose word it is
/// replaced by. A binder that converts its variable to `bool` takes the
/// operand of a field that is itself a conversion, or a `0` or `1` field, so
/// the arm reads exactly the field; any other `bool` field is refused.
fn typed_field_replacement(
    binding: &AlgebraicValue,
    field: &ProgramValue,
) -> Option<TypedProgramValueReplacement> {
    if let AlgebraicValue::Program(binding) = binding
        && bool_binder_variable(binding).is_some()
    {
        let ProgramValue::Bool(term) = field else {
            return None;
        };
        if let ProgramValue::Bool(binder) = binding
            && matches!(
                binder.bool_cast_operand(),
                Some(OldConditionTerm::Variable(_))
            )
        {
            return Some(TypedProgramValueReplacement::Bitvector(term.clone()));
        }
        let operand = match term {
            int32_constant!(0 | 1) => term,
            _ => bool_operand(term)?,
        };
        return Some(TypedProgramValueReplacement::Bitvector(operand.clone()));
    }
    typed_program_replacement(field)
}

/// Read a stored program declaration without cloning its descriptor.
pub(crate) fn program_declaration_variable(value: &ProgramValue) -> Option<Variable> {
    program_value_declaration_variable(value).or_else(|| bool_binder_variable(value))
}

fn program_value_declaration_variable(value: &ProgramValue) -> Option<Variable> {
    match value {
        ProgramValue::PointerInteger(record) => program_value_declaration_variable(&record.numeric),
        ProgramValue::Int8(OldMachineTerm::Variable(variable)) => Some(*variable),
        // A `Bool` binder (Stage 5), carried as its cast.
        ProgramValue::Bool(OldMachineTerm::BoolCast { value, .. })
            if matches!(value.as_ref(), crate::kernel::OldConditionTerm::Variable(_)) =>
        {
            match value.as_ref() {
                crate::kernel::OldConditionTerm::Variable(variable) => Some(*variable),
                _ => None,
            }
        }
        ProgramValue::Bool(OldMachineTerm::Variable(variable))
        | ProgramValue::Int16(OldMachineTerm::Variable(variable))
        | ProgramValue::UInt8(OldMachineTerm::Variable(variable))
        | ProgramValue::UInt16(OldMachineTerm::Variable(variable))
        | ProgramValue::Int32(OldMachineTerm::Variable(variable))
        | ProgramValue::UInt32(OldMachineTerm::Variable(variable))
        | ProgramValue::Int64(OldMachineTerm::Variable(variable))
        | ProgramValue::UInt64(OldMachineTerm::Variable(variable))
        | ProgramValue::Float32(OldMachineTerm::Variable(variable))
        | ProgramValue::Float64(OldMachineTerm::Variable(variable)) => Some(*variable),
        ProgramValue::Pointer(pointer)
            if matches!(
                &pointer.address().base,
                AddressBase::Symbolic(_) | AddressBase::FunctionSymbolic(_)
            ) && matches!(pointer.address().offset.view(), OffsetView::Constant(0)) =>
        {
            match pointer.address().base {
                AddressBase::Symbolic(variable) | AddressBase::FunctionSymbolic(variable) => {
                    Some(variable)
                }
                _ => unreachable!(),
            }
        }
        _ => None,
    }
}

fn replace_binding_variable(
    value: &mut AlgebraicValue,
    carrier: BindingCarrier,
    variable: Variable,
) {
    match (carrier, value) {
        (BindingCarrier::Program, AlgebraicValue::Program(value)) => match value {
            ProgramValue::Int8(term) if matches!(term, OldMachineTerm::Variable(_)) => {
                *term = OldMachineTerm::Variable(variable);
            }
            ProgramValue::Bool(term)
            | ProgramValue::Int16(term)
            | ProgramValue::UInt8(term)
            | ProgramValue::UInt16(term)
            | ProgramValue::Int32(term)
            | ProgramValue::UInt32(term)
            | ProgramValue::Int64(term)
            | ProgramValue::UInt64(term)
            | ProgramValue::Int128(term)
            | ProgramValue::UInt128(term)
            | ProgramValue::Float32(term)
            | ProgramValue::Float64(term)
                if matches!(term, OldMachineTerm::Variable(_)) =>
            {
                *term = OldMachineTerm::Variable(variable);
            }
            ProgramValue::Pointer(pointer)
                if matches!(
                    &pointer.base,
                    AddressBase::Symbolic(_) | AddressBase::FunctionSymbolic(_)
                ) =>
            {
                // Rename the binder's block wherever the value names it: in
                // its address and in its bounds' start.
                let old = pointer.base.clone();
                let new = match old {
                    AddressBase::FunctionSymbolic(_) => AddressBase::FunctionSymbolic(variable),
                    _ => AddressBase::Symbolic(variable),
                };
                *pointer = pointer.map_pointers(|address| {
                    let mut renamed = address.clone();
                    if renamed.base == old {
                        renamed.set_base(new.clone());
                    }
                    renamed
                });
            }
            _ => {}
        },
        (BindingCarrier::Integer, AlgebraicValue::Integer(term)) => {
            *term = IntegerTerm::Variable(variable);
        }
        (BindingCarrier::Algebraic, AlgebraicValue::Algebraic(term)) => {
            if matches!(&term.node, AlgebraicTermNode::Variable(_)) {
                term.node = AlgebraicTermNode::Variable(variable);
            }
        }
        _ => {}
    }
}

fn restore_mapping(
    mappings: &mut BTreeMap<Variable, Variable>,
    variable: Variable,
    previous: Option<Variable>,
) {
    if let Some(previous) = previous {
        mappings.insert(variable, previous);
    } else {
        mappings.remove(&variable);
    }
}

pub(crate) fn mathematical_comparison(
    condition: &StoredConditionTerm,
) -> Option<(IntegerComparisonOperator, &[KernelTerm; 2])> {
    let KernelTermNode::IntegerCompare {
        operator,
        arguments,
    } = condition.root()?.node()
    else {
        return None;
    };
    arguments
        .iter()
        .all(KernelTerm::is_mathematical_integer)
        .then_some((*operator, arguments))
}

fn collect_stored_condition_carriers(
    condition: &StoredConditionTerm,
    variables: &mut CarrierVariables,
) {
    if let Some((_, arguments)) = mathematical_comparison(condition) {
        if variables.visit() {
            for argument in arguments {
                collect_mathematical_integer_carriers(argument, variables);
            }
        }
    } else {
        collect_condition_carriers(condition.old_form(), variables);
    }
}

fn collect_mathematical_integer_carriers(root: &KernelTerm, variables: &mut CarrierVariables) {
    let mut pending = vec![root];
    while let Some(term) = pending.pop() {
        if !variables.mathematical_integers.insert(term.id()) {
            continue;
        }
        if !variables.visit() {
            return;
        }
        match term.node() {
            KernelTermNode::IntegerLiteral(_) => {}
            KernelTermNode::Variable(variable) => {
                variables.integer.insert(*variable);
            }
            KernelTermNode::IntegerOperation { arguments, .. } => {
                pending.extend(arguments.iter().rev());
            }
            KernelTermNode::Fold(fold) => {
                variables.integer.extend([fold.accumulator, fold.item]);
                pending.extend(fold.arguments.iter().rev());
            }
            _ => unreachable!("mathematical Integer operand"),
        }
    }
}

fn collect_integer_shared_carriers(
    term: &SharedIntegerTerm,
    variables: &mut CarrierVariables,
    seen: &mut BTreeSet<u64>,
) {
    if seen.insert(term.id()) {
        collect_integer_carriers(term, variables, seen);
    }
}

fn collect_integer_carriers(
    term: &IntegerTerm,
    variables: &mut CarrierVariables,
    seen: &mut BTreeSet<u64>,
) {
    if !variables.visit() {
        return;
    }
    match term {
        IntegerTerm::Constant(_) => {}
        IntegerTerm::Variable(variable) => {
            variables.integer.insert(*variable);
        }
        IntegerTerm::Machine(value) => collect_machine_carriers(value, variables),
        IntegerTerm::Negate(value) => collect_integer_shared_carriers(value, variables, seen),
        crate::kernel::binary_integer_term!(left, right) => {
            collect_integer_shared_carriers(left, variables, seen);
            if variables.exhausted() {
                return;
            }
            collect_integer_shared_carriers(right, variables, seen);
        }
        IntegerTerm::If {
            condition,
            then_term,
            else_term,
        } => {
            collect_condition_carriers(condition, variables);
            if variables.exhausted() {
                return;
            }
            collect_integer_shared_carriers(then_term, variables, seen);
            if variables.exhausted() {
                return;
            }
            collect_integer_shared_carriers(else_term, variables, seen);
        }
        IntegerTerm::RangeFold {
            index,
            initial,
            accumulator,
            item,
            body,
        } => {
            match index {
                IntegerRangeFoldIndex::Int32 { start, end }
                | IntegerRangeFoldIndex::UInt64 { start, end } => {
                    collect_machine_carriers(start.machine_operand(), variables);
                    if variables.exhausted() {
                        return;
                    }
                    collect_machine_carriers(end.machine_operand(), variables);
                }
                IntegerRangeFoldIndex::Integer { start, end } => {
                    collect_integer_shared_carriers(start, variables, seen);
                    if variables.exhausted() {
                        return;
                    }
                    collect_integer_shared_carriers(end, variables, seen);
                }
            }
            if variables.exhausted() {
                return;
            }
            collect_integer_shared_carriers(initial, variables, seen);
            if variables.exhausted() {
                return;
            }
            collect_integer_shared_carriers(body, variables, seen);
            if variables.exhausted() {
                return;
            }
            variables.integer.insert(*accumulator);
            match index {
                IntegerRangeFoldIndex::Integer { .. } => {
                    variables.integer.insert(*item);
                }
                IntegerRangeFoldIndex::Int32 { .. } | IntegerRangeFoldIndex::UInt64 { .. } => {
                    variables.program_values.insert(*item);
                }
            }
        }
        IntegerTerm::PureFunctionApplication(application) => {
            for argument in application.arguments() {
                collect_argument_carriers(argument, variables, seen);
                if variables.exhausted() {
                    return;
                }
            }
        }
        IntegerTerm::AlgebraicMatch { scrutinee, arms } => {
            collect_algebraic_carriers_seen(scrutinee, variables, seen);
            if variables.exhausted() {
                return;
            }
            for arm in arms {
                for binding in &arm.bindings {
                    collect_algebraic_value_carriers(binding, variables, seen);
                    if variables.exhausted() {
                        return;
                    }
                }
                collect_integer_shared_carriers(&arm.body, variables, seen);
                if variables.exhausted() {
                    return;
                }
            }
        }
    }
}

fn collect_argument_carriers(
    argument: &PureFunctionArgument,
    variables: &mut CarrierVariables,
    seen: &mut BTreeSet<u64>,
) {
    if !variables.visit() {
        return;
    }
    match argument {
        PureFunctionArgument::Value(value) => collect_program_value_carriers(value, variables),
        PureFunctionArgument::SharedMachine(value) => collect_machine_carriers(value, variables),
        PureFunctionArgument::Integer(value) => {
            collect_integer_shared_carriers(value, variables, seen)
        }
        PureFunctionArgument::Algebraic(value) => {
            collect_algebraic_carriers_seen(value, variables, seen)
        }
        PureFunctionArgument::ArrayRef { pointer, .. } => {
            collect_program_value_carriers(pointer, variables);
        }
    }
}

fn collect_algebraic_value_carriers<'a>(
    value: impl Into<ResourceFieldValue<'a>>,
    variables: &mut CarrierVariables,
    seen: &mut BTreeSet<u64>,
) {
    if !variables.visit() {
        return;
    }
    match value.into() {
        ResourceFieldValue::Program(value) => collect_program_value_carriers(value, variables),
        ResourceFieldValue::Integer(value) => collect_integer_carriers(value, variables, seen),
        ResourceFieldValue::Algebraic(value) => {
            collect_algebraic_carriers_seen(value, variables, seen)
        }
    }
}

fn collect_program_value_carriers(value: &ProgramValue, variables: &mut CarrierVariables) {
    if !variables.visit() {
        return;
    }
    match value {
        ProgramValue::PointerInteger(record) => {
            collect_program_value_carriers(&record.numeric, variables);
            collect_program_value_carriers(
                &ProgramValue::Pointer(*record.pointer.clone()),
                variables,
            );
        }
        ProgramValue::Parameter(term) => collect_algebraic_carriers(term, variables),
        ProgramValue::Void => {}
        ProgramValue::Int8(term) => collect_bitvector_carriers(term, variables),
        ProgramValue::Bool(term)
        | ProgramValue::Int16(term)
        | ProgramValue::UInt8(term)
        | ProgramValue::UInt16(term)
        | ProgramValue::Int32(term)
        | ProgramValue::UInt32(term)
        | ProgramValue::Int64(term)
        | ProgramValue::UInt64(term)
        | ProgramValue::Int128(term)
        | ProgramValue::UInt128(term)
        | ProgramValue::Float32(term)
        | ProgramValue::Float64(term) => collect_bitvector_carriers(term, variables),
        ProgramValue::Pointer(pointer) => {
            for component in pointer.pointers() {
                collect_pointer_carriers(component, variables);
            }
        }
    }
}

fn collect_algebraic_carriers(term: &AlgebraicTerm, variables: &mut CarrierVariables) {
    collect_algebraic_carriers_seen(term, variables, &mut BTreeSet::new());
}

fn collect_algebraic_carriers_seen(
    term: &AlgebraicTerm,
    variables: &mut CarrierVariables,
    seen: &mut BTreeSet<u64>,
) {
    if !variables.visit() {
        return;
    }
    match &term.node {
        AlgebraicTermNode::Variable(variable) => {
            variables.algebraic.insert(*variable);
        }
        AlgebraicTermNode::MemoryLoad {
            point: memory,
            pointer,
        } => {
            collect_algebraic_value_carriers(
                &AlgebraicTermNode::memory_load_carrier_value(
                    memory,
                    pointer,
                    &term.algebraic_type,
                ),
                variables,
                seen,
            );
        }
        AlgebraicTermNode::Constructor { fields, .. } => {
            for field in fields {
                collect_algebraic_value_carriers(field, variables, seen);
                if variables.exhausted() {
                    return;
                }
            }
        }
        AlgebraicTermNode::Match { scrutinee, arms } => {
            collect_algebraic_carriers_seen(scrutinee, variables, seen);
            if variables.exhausted() {
                return;
            }
            for arm in arms {
                for binding in &arm.bindings {
                    collect_algebraic_value_carriers(binding, variables, seen);
                    if variables.exhausted() {
                        return;
                    }
                }
                collect_algebraic_carriers_seen(&arm.body, variables, seen);
                if variables.exhausted() {
                    return;
                }
            }
        }
        AlgebraicTermNode::PureFunctionApplication { arguments, .. } => {
            for argument in arguments {
                collect_argument_carriers(argument, variables, seen);
                if variables.exhausted() {
                    return;
                }
            }
        }
        AlgebraicTermNode::If {
            condition,
            then_term,
            else_term,
        } => {
            collect_condition_carriers(condition, variables);
            if variables.exhausted() {
                return;
            }
            collect_algebraic_carriers_seen(then_term, variables, seen);
            if variables.exhausted() {
                return;
            }
            collect_algebraic_carriers_seen(else_term, variables, seen);
        }
    }
}

fn collect_pointer_carriers(pointer: &Address, variables: &mut CarrierVariables) {
    if !variables.visit() {
        return;
    }
    if let Some(pointers) = &mut variables.pointer_terms
        && *pointer != Address::null()
    {
        pointers.push(pointer.clone());
    }
    collect_address_base_carriers(&pointer.base, variables);
    if variables.exhausted() {
        return;
    }
    collect_pointer_offset_carriers(&pointer.offset, variables);
}

fn collect_address_base_carriers(block: &AddressBase, variables: &mut CarrierVariables) {
    match block {
        AddressBase::Symbolic(variable) | AddressBase::FunctionSymbolic(variable) => {
            variables.program_values.insert(*variable);
        }
        AddressBase::PureFunctionApplication(application)
            if variables.pointer_applications.insert(application.id()) =>
        {
            let mut seen = BTreeSet::new();
            for argument in application.arguments() {
                collect_argument_carriers(argument, variables, &mut seen);
                if variables.exhausted() {
                    return;
                }
            }
        }
        // A loaded pointer carries whatever its defining read's address
        // carries, as a registered load variable's offset does.
        AddressBase::Load(load) if variables.pointer_loads.insert(load.clone()) => {
            collect_pointer_carriers(load.cell(), variables);
        }
        _ => {}
    }
}

fn collect_condition_carriers(condition: &OldConditionTerm, variables: &mut CarrierVariables) {
    if !variables.visit() {
        return;
    }
    match condition {
        OldConditionTerm::PointerEqual(left, right) => {
            collect_program_value_carriers(&ProgramValue::Pointer((**left).clone()), variables);
            collect_program_value_carriers(&ProgramValue::Pointer((**right).clone()), variables);
        }

        OldConditionTerm::AlgebraicEqual(left, right) => {
            let mut seen = BTreeSet::new();
            collect_algebraic_carriers_seen(left, variables, &mut seen);
            if variables.exhausted() {
                return;
            }
            collect_algebraic_carriers_seen(right, variables, &mut seen);
        }
        crate::kernel::integer_comparison_condition!(left, right) => {
            let mut seen = BTreeSet::new();
            collect_integer_shared_carriers(left, variables, &mut seen);
            if variables.exhausted() {
                return;
            }
            collect_integer_shared_carriers(right, variables, &mut seen);
        }
        OldConditionTerm::Constant(_) | OldConditionTerm::Variable(_) => {}
        crate::kernel::binary_bitvector_condition!(left, right) => {
            collect_bitvector_carriers(left, variables);
            if variables.exhausted() {
                return;
            }
            collect_bitvector_carriers(right, variables);
        }
        OldConditionTerm::Float32(float_condition) | OldConditionTerm::Float64(float_condition) => {
            float_condition.for_each_bitvector_term(|term| {
                if !variables.exhausted() {
                    collect_bitvector_carriers(term, variables);
                }
            });
        }
        OldConditionTerm::AddressOffsetEqual(left, right) => {
            collect_pointer_offset_carriers(left, variables);
            if variables.exhausted() {
                return;
            }
            collect_pointer_offset_carriers(right, variables);
        }
        OldConditionTerm::AddressEqual(left, right) => {
            collect_pointer_carriers(left, variables);
            if variables.exhausted() {
                return;
            }
            collect_pointer_carriers(right, variables);
        }
        OldConditionTerm::BoolApplication(application) => {
            let mut seen = BTreeSet::new();
            for argument in application.arguments() {
                collect_argument_carriers(argument, variables, &mut seen);
                if variables.exhausted() {
                    return;
                }
            }
        }
        OldConditionTerm::BoolIf {
            condition,
            then_condition,
            else_condition,
        } => {
            for condition in [condition, then_condition, else_condition] {
                collect_condition_carriers(condition, variables);
                if variables.exhausted() {
                    return;
                }
            }
        }
        OldConditionTerm::BoolEqual(left, right) => {
            collect_condition_carriers(left, variables);
            if variables.exhausted() {
                return;
            }
            collect_condition_carriers(right, variables);
        }
    }
}

fn collect_bitvector_carriers(term: &OldMachineTerm, variables: &mut CarrierVariables) {
    if !variables.visit() {
        return;
    }
    match term {
        OldMachineTerm::ThreadHandle(_) => {}
        OldMachineTerm::Constant { .. } => {}
        OldMachineTerm::Variable(variable) => {
            variables.program_values.insert(*variable);
            collect_registered_load_carriers(*variable, variables);
        }
        crate::kernel::binary_machine_term!(left, right) => {
            collect_bitvector_carriers(left, variables);
            if variables.exhausted() {
                return;
            }
            collect_bitvector_carriers(right, variables);
        }
        crate::kernel::unary_machine_term!(value) => collect_bitvector_carriers(value, variables),
        OldMachineTerm::BoolCast { value, .. } => collect_condition_carriers(value, variables),
        OldMachineTerm::If {
            condition,
            then_term,
            else_term,
        } => {
            collect_condition_carriers(condition, variables);
            if variables.exhausted() {
                return;
            }
            collect_bitvector_carriers(then_term, variables);
            if variables.exhausted() {
                return;
            }
            collect_bitvector_carriers(else_term, variables);
        }
        OldMachineTerm::RangeFold {
            start,
            end,
            initial,
            accumulator,
            item,
            body,
        } => {
            collect_bitvector_carriers(start, variables);
            if variables.exhausted() {
                return;
            }
            collect_bitvector_carriers(end, variables);
            if variables.exhausted() {
                return;
            }
            collect_bitvector_carriers(initial, variables);
            if variables.exhausted() {
                return;
            }
            collect_bitvector_carriers(body, variables);
            if variables.exhausted() {
                return;
            }
            variables.program_values.insert(*accumulator);
            variables.program_values.insert(*item);
        }
        OldMachineTerm::PureFunctionApplication { arguments, .. } => {
            for argument in arguments {
                collect_bitvector_carriers(argument, variables);
                if variables.exhausted() {
                    return;
                }
            }
        }
        OldMachineTerm::ClickFunctionApplication { arguments, .. } => {
            let mut seen = BTreeSet::new();
            for argument in arguments {
                collect_argument_carriers(argument, variables, &mut seen);
                if variables.exhausted() {
                    return;
                }
            }
        }
        OldMachineTerm::AlgebraicMatch { scrutinee, arms } => {
            let mut seen = BTreeSet::new();
            collect_algebraic_carriers_seen(scrutinee, variables, &mut seen);
            if variables.exhausted() {
                return;
            }
            for arm in arms {
                for binding in &arm.bindings {
                    collect_algebraic_value_carriers(binding, variables, &mut seen);
                    if variables.exhausted() {
                        return;
                    }
                }
                collect_bitvector_carriers(&arm.body, variables);
                if variables.exhausted() {
                    return;
                }
            }
        }
        // SymbolicMemory states are opaque proof-state values.  Only the selected
        // pointer expression participates in freshness collection.
        OldMachineTerm::MemoryLoad(memory, pointer, kind) => {
            if let Some(terms) = &mut variables.read_terms {
                terms
                    .entry((
                        memory.shared_memory().arena_id(),
                        pointer.as_ref().clone(),
                        *kind,
                    ))
                    .or_insert_with(|| term.clone());
            }
            collect_pointer_carriers(pointer, variables);
        }
        OldMachineTerm::IntegerAddress(pointer, _) => {
            collect_pointer_carriers(pointer, variables);
        }
        OldMachineTerm::IntegerToMachine { value, .. } => {
            collect_integer_shared_carriers(value, variables, &mut BTreeSet::new());
        }
        OldMachineTerm::Float32Binary { left, right, .. }
        | OldMachineTerm::Float64Binary { left, right, .. } => {
            collect_bitvector_carriers(left, variables);
            if variables.exhausted() {
                return;
            }
            collect_bitvector_carriers(right, variables);
        }
    }
}

/// Decide rebuilt scalar guards through their existing context-free rules.
/// Machine comparisons use their smart constructors; concrete nullary enum
/// constructors use the algebraic equality decision. Other guards stay intact.
pub(in crate::kernel::proof) fn folded_machine_condition(
    condition: OldConditionTerm,
) -> OldConditionTerm {
    match condition {
        OldConditionTerm::AlgebraicEqual(ref left, ref right)
            if matches!(&left.node, AlgebraicTermNode::Constructor { fields, .. } if fields.is_empty())
                && matches!(&right.node, AlgebraicTermNode::Constructor { fields, .. } if fields.is_empty()) =>
        {
            // A rewritten enum discriminant is a concrete guard, just like
            // an integer literal comparison. Decide it before visiting an
            // unreachable arm (which may contain an unrelated binder).
            // Restrict this constant-folding path to nullary constructors;
            // unknown fields still require their own checked evidence.
            let equality = Proposition::Equal(
                Term::Algebraic(left.as_ref().clone().into()),
                Term::Algebraic(right.as_ref().clone().into()),
            );
            crate::kernel::spec::constant_spec_condition_value(&equality)
                .map(OldConditionTerm::Constant)
                .unwrap_or(condition)
        }
        OldConditionTerm::Compare {
            format: format @ (MachineIntegerType::Int32 | MachineIntegerType::UInt32),
            relation: CompareRelation::Equal,
            left,
            right,
        } => OldConditionTerm::machine_compare(format, CompareRelation::Equal, *left, *right),
        OldConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::LessThan,
            left,
            right,
        } => OldConditionTerm::signed_less_than(*left, *right),
        OldConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::LessEqual,
            left,
            right,
        } => OldConditionTerm::signed_less_equal(*left, *right),
        OldConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::GreaterThan,
            left,
            right,
        } => OldConditionTerm::signed_greater_than(*left, *right),
        OldConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::GreaterEqual,
            left,
            right,
        } => OldConditionTerm::signed_greater_equal(*left, *right),
        condition => condition,
    }
}

/// The content a registered load variable's own state already holds at its
/// own cell, when that state holds one exactly.
///
/// A registered load variable is *defined* as `load(memory, pointer)` for the
/// pair the registry holds for it -- that is what makes its defining equation
/// a kernel-certified truth rather than a premise a proof must discharge. A
/// state's cell map is the authoritative content of that state at an
/// exact pointer: every load evaluation consults it before anything else and
/// returns it unconditionally when it hits. So when the map holds an entry for
/// exactly this pointer, that entry *is* `load(memory, pointer)`, and
/// returning it here unfolds the variable's own definition rather than
/// asserting anything new about memory. No alias is decided, no pointer is
/// compared, and no fact set is consulted.
///
/// Three conditions bound it, and each closes a way the cell could be
/// something other than this load's value.
///
/// *Width.* The variable's load must be a four-byte integer read
/// (`LoadKind::Int32`, which its registered term carries), and the cell must
/// be a `ProgramValue::Int32`, which is a four-byte value: a cell answers only a read
/// of its own kind. Every scaled term in the pointer's own offset must also
/// scale by four, which makes the address an element address of a four-byte
/// array rather than a narrower field inside a wider element. A one-byte array
/// indexes by `*1` and a narrow struct field adds a constant to a stride that
/// is the struct's size, so neither reaches here.
///
/// *Union overlays.* A typed union overlay outranks the raw cell for an exact
/// typed load, so a raw cell read while an overlay is present would be the
/// wrong value rather than a missing one. `SymbolicMemory::store_with_context` drops
/// every overlay at the pointer it writes and `SymbolicMemory::store_union` drops the
/// raw cell at the pointer it overlays, so the two never coexist at one
/// pointer — an invariant this helper depends on and does not enforce
/// elsewhere. It is asserted in debug builds and refused in release ones, and
/// `store_and_union_cells_never_coexist_at_one_pointer` pins the invariant
/// itself.
///
/// *Exactness.* Only the exact pointer is looked up. No alias is decided, no
/// pointer is compared, and no fact set is consulted.
fn materialized_registered_load_value(variable: Variable) -> Option<OldMachineTerm> {
    let (memory, pointer) = crate::kernel::eval::registered_load_for_variable(&variable)?;
    let kind = crate::kernel::eval::registered_load_kind_for_variable(&variable)?;
    if !kind.is_word32() || !pointer_addresses_four_byte_elements(&pointer) {
        return None;
    }
    let memory = memory.memory();
    debug_assert!(
        !(memory.has_union_overlay_at(&pointer) && memory.known_value(&pointer).is_some()),
        "a raw cell and a union overlay coexist at one pointer"
    );
    if memory.has_union_overlay_at(&pointer) {
        return None;
    }
    // The cell's value as this read returns it: σ of a word stored at the
    // other 32-bit signedness (rule K5).
    match kind.read_cell(&memory.known_value(&pointer)?)? {
        ProgramValue::Int32(bits) | ProgramValue::UInt32(bits) => Some(bits),
        _ => None,
    }
}

/// Whether every scaled term in a pointer's offset steps by four bytes.
///
/// This is the pointer's own record of its element width. A pointer built by
/// indexing a four-byte array scales by four at every step, including the
/// argument's own base offset; a narrower array scales by its own width, and a
/// field inside a wider element adds a constant to a stride that is the
/// element's size rather than the field's. A pointer shape this does not
/// recognize answers `false`, so an unfamiliar address is refused rather than
/// assumed.
fn pointer_addresses_four_byte_elements(pointer: &Address) -> bool {
    fn offset_scales_by_four(offset: &AddressOffset) -> bool {
        match offset.view() {
            OffsetView::Int32Scaled { byte_width, .. } => byte_width == 4,
            OffsetView::Int64Scaled { byte_width, .. } => byte_width == 4,
            OffsetView::Add(left, right) => {
                offset_scales_by_four(left) && offset_scales_by_four(right)
            }
            // A bare constant or variable offset carries no element width of
            // its own, so it cannot witness one.
            OffsetView::Constant(_) | OffsetView::Variable(_) => false,
        }
    }
    offset_scales_by_four(&pointer.offset)
}

/// Extend the carrier summary through one registered load's selected
/// pointer.  A per-walker load set prevents shared or cyclic registry edges
/// from reopening the same pointer DAG; states remain completely opaque.
fn collect_registered_load_carriers(load: Variable, variables: &mut CarrierVariables) {
    if !crate::kernel::is_load_variable(&load) || !variables.registered_loads.insert(load) {
        return;
    }
    let Some((_, pointer)) = crate::kernel::eval::registered_load_for_variable(&load) else {
        return;
    };
    collect_pointer_carriers(&pointer, variables);
}

fn collect_pointer_offset_carriers(offset: &AddressOffset, variables: &mut CarrierVariables) {
    if !variables.visit() {
        return;
    }
    match offset.view() {
        OffsetView::Constant(_) => {}
        OffsetView::Variable(variable) => {
            variables.program_values.insert(variable);
            collect_registered_load_carriers(variable, variables);
        }
        OffsetView::Add(left, right) => {
            collect_pointer_offset_carriers(left, variables);
            if variables.exhausted() {
                return;
            }
            collect_pointer_offset_carriers(right, variables);
        }
        OffsetView::Int32Scaled { index: value, .. }
        | OffsetView::Int64Scaled { index: value, .. } => {
            collect_machine_carriers(&value, variables)
        }
    }
}

fn collect_retained_offset_carriers(
    offset: &SharedAddressOffset,
    variables: &mut CarrierVariables,
) {
    offset.visit_root_while(|node| {
        collect_offset_node_carriers(node, variables, |index, variables| {
            collect_machine_carriers(&SharedAddressOffset::exact_index(index), variables);
        })
    });
}

fn collect_offset_node_carriers(
    node: &KernelAddressOffset,
    variables: &mut CarrierVariables,
    collect_index: impl FnOnce(&KernelTerm, &mut CarrierVariables),
) -> bool {
    if !variables.visit() {
        return false;
    }
    match node {
        KernelAddressOffset::Variable(variable) => {
            variables.program_values.insert(*variable);
            collect_registered_load_carriers(*variable, variables);
        }
        node => {
            if let Some(index) = node.index() {
                collect_index(index, variables);
            }
        }
    }
    !variables.exhausted()
}

fn collect_sequence_carriers(term: &SequenceTerm, variables: &mut CarrierVariables) {
    if !variables.visit() {
        return;
    }
    match term.node.as_ref() {
        SequenceTermNode::Literal(values) => {
            for value in values.iter() {
                collect_program_value_carriers(value, variables);
                if variables.exhausted() {
                    return;
                }
            }
        }
        SequenceTermNode::Concat(left, right) => {
            collect_sequence_carriers(left, variables);
            if variables.exhausted() {
                return;
            }
            collect_sequence_carriers(right, variables);
        }
    }
}

/// Collect variables needed for capture avoidance in the checked Integer
/// substitution fragment.  Pure function ArrayRef states are proof-state
/// values, so their memory field is deliberately not traversed here; only the
/// explicit pointer expression participates in lexical freshness.
pub(crate) struct IntegerSubstitutionVariableCollector {
    carriers: CarrierVariables,
}

impl IntegerSubstitutionVariableCollector {
    /// Construct the checked collector used by pure Integer substitution.
    /// Registered-load identities remain memoized for the entire proposition,
    /// so repeated loadability obligations do not reopen one pointer DAG.
    pub(crate) fn checked() -> Self {
        Self {
            carriers: CarrierVariables::for_rewrite(true),
        }
    }

    /// A collector that records no deterministic work: for a lookup whose
    /// visit is bounded by the queried proposition itself (memory states
    /// stay opaque), run beside a check that already charges for it.
    pub(crate) fn uncharged() -> Self {
        Self {
            carriers: CarrierVariables::default(),
        }
    }

    /// Select structural reads alongside lexical variables, without opening states.
    pub(crate) fn collect_read_terms(&mut self) {
        self.carriers.read_terms = Some(BTreeMap::new());
    }

    pub(crate) fn take_read_terms(&mut self) -> impl Iterator<Item = OldMachineTerm> {
        self.carriers
            .read_terms
            .take()
            .unwrap_or_default()
            .into_values()
    }

    pub(crate) fn collect(&mut self, proposition: &Proposition) {
        if !self.carriers.exhausted() {
            collect_integer_substitution_variables_with_carriers(proposition, &mut self.carriers);
        }
    }

    pub(crate) fn exhausted(&self) -> bool {
        self.carriers.exhausted()
    }

    pub(crate) fn extend_into(&self, variables: &mut BTreeSet<Variable>) {
        variables.extend(self.carriers.program_values.iter().copied());
        variables.extend(self.carriers.integer.iter().copied());
        variables.extend(self.carriers.algebraic.iter().copied());
    }
}

/// Collect only pointer expressions reachable from this explicit goal. SymbolicMemory
/// states remain opaque, just as in capture-avoiding term rewriting.
pub(crate) fn proposition_pointer_terms(proposition: &Proposition) -> Vec<Address> {
    let mut carriers = CarrierVariables::for_rewrite(false);
    carriers.pointer_terms = Some(Vec::new());
    collect_integer_substitution_variables_with_carriers(proposition, &mut carriers);
    carriers.pointer_terms.unwrap_or_default()
}

fn collect_integer_substitution_variables_with_carriers(
    proposition: &Proposition,
    carriers: &mut CarrierVariables,
) {
    // Charge every logical container and avoid recursion through quantifier
    // chains, including when setup is the first operation to exhaust a budget.
    let mut pending = vec![proposition];
    while let Some(proposition) = pending.pop() {
        if !carriers.visit() {
            return;
        }
        match proposition {
            Proposition::VolatileAccess(event) => {
                collect_pointer_carriers(&event.pointer, carriers);
                collect_program_value_carriers(event.value.old_form(), carriers);
            }
            Proposition::Predicate { arguments, .. } => {
                for argument in arguments {
                    collect_integer_substitution_term_variables(argument, carriers);
                    if carriers.exhausted() {
                        return;
                    }
                }
            }
            Proposition::Equal(left, right) => {
                collect_integer_substitution_term_variables(left, carriers);
                if carriers.exhausted() {
                    return;
                }
                collect_integer_substitution_term_variables(right, carriers);
            }
            Proposition::SequenceMembership { element, sequence } => {
                collect_program_value_carriers(element.old_form(), carriers);
                collect_sequence_carriers(sequence, carriers);
            }
            Proposition::ConditionIs(condition, _) => {
                collect_stored_condition_carriers(condition, carriers);
            }
            // Loadability obligations produced while lowering a symbolic array
            // read carry the selected pointer and byte-count terms directly.  The
            // memory state is intentionally opaque: only these expressions
            // participate in capture reservation.
            Proposition::MemoryReadDefined { pointer, .. } => {
                collect_pointer_carriers(pointer, carriers);
            }
            Proposition::MemoryLoadable { base, bytes, .. } => {
                collect_pointer_carriers(base, carriers);
                if carriers.exhausted() {
                    return;
                }
                collect_bitvector_carriers(bytes.old_form(), carriers);
            }
            Proposition::ResourceViewable { resource, .. } => {
                collect_resource_carriers(resource, carriers)
            }
            Proposition::ResourceContains { parent, child } => {
                collect_resource_carriers(parent, carriers);
                collect_resource_carriers(child, carriers);
            }
            Proposition::ResourceSeparate { left, right } => {
                collect_resource_carriers(left, carriers);
                collect_resource_carriers(right, carriers);
            }
            Proposition::ResourceComposition(resources) => {
                for fact in resources.facts() {
                    collect_resource_carriers(fact.resource(), carriers);
                    if carriers.exhausted() {
                        return;
                    }
                }
            }
            Proposition::And(left, right)
            | Proposition::Or(left, right)
            | Proposition::Implies(left, right) => {
                pending.push(right);
                pending.push(left);
            }
            Proposition::Not(body) => {
                pending.push(body);
            }
            Proposition::ForAll { body, .. } | Proposition::Exists { body, .. } => {
                pending.push(body);
            }
            _ => {}
        }
    }
}

// Visit only the explicitly named footprint and arguments. Stored cells,
// sealed resource identities and binder-bearing bodies remain opaque.
fn collect_resource_carriers(resource: &Resource, carriers: &mut CarrierVariables) {
    let mut pending = vec![resource];
    while let Some(resource) = pending.pop() {
        if !carriers.visit() {
            return;
        }
        match resource {
            Resource::Star(pair) => {
                pending.extend([&pair.0, &pair.1]);
            }
            Resource::Memory(range) => {
                collect_program_value_carriers(
                    &ProgramValue::Pointer(range.pointer_carrier()),
                    carriers,
                );
                collect_bitvector_carriers(range.bound_terms().0, carriers);
                collect_bitvector_carriers(range.bound_terms().1, carriers);
            }
            Resource::Composite { arguments, .. } | Resource::Token { arguments, .. } => {
                for argument in arguments.iter() {
                    match argument {
                        crate::kernel::ResourceFieldValue::Program(value) => {
                            collect_program_value_carriers(value, carriers)
                        }
                        crate::kernel::ResourceFieldValue::Integer(value) => {
                            collect_integer_carriers(value, carriers, &mut BTreeSet::new());
                        }
                        crate::kernel::ResourceFieldValue::Algebraic(value) => {
                            collect_algebraic_carriers(value, carriers)
                        }
                    }
                    if carriers.exhausted() {
                        return;
                    }
                }
            }
            _ => {}
        }
    }
}

fn collect_integer_substitution_term_variables(term: &Term, variables: &mut CarrierVariables) {
    match term {
        Term::Integer(value) => {
            if let Some(root) = value.root().filter(|root| root.is_mathematical_integer()) {
                collect_mathematical_integer_carriers(root, variables);
            } else {
                collect_integer_carriers(value.old_form(), variables, &mut BTreeSet::new());
            }
        }
        Term::Bitvector32(value) => collect_bitvector_carriers(value.old_form(), variables),
        Term::ProgramValue(value) => collect_program_value_carriers(value.old_form(), variables),
        Term::Condition(value) => collect_stored_condition_carriers(value, variables),
        Term::PointerOffset(value) => {
            collect_retained_offset_carriers(value.root(), variables);
        }
        Term::Algebraic(value) => collect_algebraic_carriers(value.old_form(), variables),
        Term::Sequence(value)
            if value
                .element_type
                .is_none_or(crate::kernel::spec::retained_sequence_element_type) =>
        {
            collect_sequence_carriers(value, variables)
        }
        _ => {}
    }
}

// Once a checked rewrite runs out of work, its caller discards the result and
// reports the bounded failure.  Keep the transient value used to unwind the
// walker shallow; cloning an unvisited C/ADT subtree here would defeat the
// bound that caused the failure.
fn exhausted_algebraic(term: &AlgebraicTerm) -> AlgebraicTerm {
    AlgebraicTerm {
        algebraic_type: term.algebraic_type.clone(),
        node: AlgebraicTermNode::Variable(Variable(u64::MAX)),
    }
}

fn exhausted_integer(term: &IntegerTerm) -> IntegerTerm {
    match term {
        IntegerTerm::AlgebraicMatch { scrutinee, .. } => IntegerTerm::AlgebraicMatch {
            scrutinee: Box::new(exhausted_algebraic(scrutinee)),
            arms: Vec::new(),
        },
        IntegerTerm::Variable(variable) => IntegerTerm::Variable(*variable),
        _ => IntegerTerm::constant_i64(0),
    }
}

fn exhausted_pointer() -> Address {
    Address::new(
        AddressBase::Concrete(String::new()),
        AddressOffset::constant(0),
    )
}

fn exhausted_offset() -> AddressOffset {
    AddressOffset::constant(0)
}

fn exhausted_program_value(value: &ProgramValue) -> ProgramValue {
    match value.numeric_value() {
        ProgramValue::PointerInteger(_) => unreachable!("numeric projection"),
        ProgramValue::Parameter(term) => {
            ProgramValue::Parameter(Box::new(exhausted_algebraic(term)))
        }
        ProgramValue::Void => ProgramValue::Void,
        ProgramValue::Bool(_) => ProgramValue::bool_constant(false),
        ProgramValue::Int8(_) => crate::kernel::int8(0),
        ProgramValue::Int16(_) => crate::kernel::int16(0),
        ProgramValue::UInt8(_) => crate::kernel::uint8(0),
        ProgramValue::UInt16(_) => crate::kernel::uint16(0),
        ProgramValue::Int32(_) => ProgramValue::Int32(OldMachineTerm::constant(0)),
        ProgramValue::UInt32(_) => ProgramValue::UInt32(OldMachineTerm::uint32_constant(0)),
        ProgramValue::Int64(_) => ProgramValue::Int64(OldMachineTerm::int64_constant(0)),
        ProgramValue::UInt64(_) => ProgramValue::UInt64(OldMachineTerm::uint64_constant(0)),
        ProgramValue::Int128(_) => MachineIntegerType::Int128
            .constant_value(
                crate::kernel::MachineIntegerConstant::from_signed(
                    MachineIntegerType::Int128.format(),
                    0,
                )
                .unwrap(),
            )
            .unwrap(),
        ProgramValue::UInt128(_) => MachineIntegerType::UInt128
            .constant_value(
                crate::kernel::MachineIntegerConstant::from_unsigned(
                    MachineIntegerType::UInt128.format(),
                    0,
                )
                .unwrap(),
            )
            .unwrap(),
        ProgramValue::Float32(_) => ProgramValue::Float32(OldMachineTerm::constant(0)),
        ProgramValue::Float64(_) => ProgramValue::Float64(OldMachineTerm::uint64_constant(0)),
        ProgramValue::Pointer(pointer) => {
            ProgramValue::Pointer(OldPointer::new(exhausted_pointer(), pointer.program_type()))
        }
    }
}

fn exhausted_sequence(term: &SequenceTerm) -> SequenceTerm {
    SequenceTerm {
        element_type: term.element_type,
        node: std::sync::Arc::new(SequenceTermNode::Literal(Vec::<ProgramValue>::new().into())),
    }
}

fn exhausted_argument(argument: &PureFunctionArgument) -> PureFunctionArgument {
    match argument {
        PureFunctionArgument::Value(value) => {
            PureFunctionArgument::Value(exhausted_program_value(value))
        }
        PureFunctionArgument::SharedMachine(value) => {
            PureFunctionArgument::SharedMachine(SharedMachineIntegerTerm::index(
                value.ty(),
                crate::kernel::machine_integer::range::constant_word(value.ty(), &0.into())
                    .unwrap(),
            ))
        }
        PureFunctionArgument::Integer(value) => {
            PureFunctionArgument::Integer(exhausted_integer(value.as_ref()).into())
        }
        PureFunctionArgument::Algebraic(value) => {
            PureFunctionArgument::Algebraic(exhausted_algebraic(value))
        }
        PureFunctionArgument::ArrayRef {
            point,
            pointer,
            element_type,
        } => PureFunctionArgument::ArrayRef {
            point: point.clone(),
            pointer: exhausted_program_value(pointer),
            element_type: *element_type,
        },
    }
}

fn exhausted_term(term: &Term) -> Term {
    match term {
        Term::Condition(_) => Term::Condition(OldConditionTerm::Constant(false).into()),
        Term::Bitvector32(_) => Term::Bitvector32(OldMachineTerm::constant(0).into()),
        Term::Integer(value) if value.root().is_some() => term.clone(),
        Term::Integer(value) => Term::Integer(exhausted_integer(value.old_form()).into()),
        Term::PointerOffset(_) => Term::PointerOffset(exhausted_offset().into()),
        Term::ProgramValue(value) => match value.value() {
            ExecutionValue::Shared(_) => term.clone(),
            ExecutionValue::Native(value) => {
                Term::ProgramValue(exhausted_program_value(value).into())
            }
        },
        Term::Sequence(value) => Term::Sequence(exhausted_sequence(value)),
        Term::Algebraic(value) if value.root().is_some() => term.clone(),
        Term::Algebraic(value) => Term::Algebraic(exhausted_algebraic(value.old_form()).into()),
        _ => term.clone(),
    }
}

fn exhausted_proposition() -> Proposition {
    Proposition::condition_is(OldConditionTerm::Constant(false), true)
}

struct IntegerVariableRewrite<'a> {
    from: Variable,
    to: &'a IntegerTerm,
    renamings: &'a BTreeMap<Variable, Variable>,
}

/// Saved lexical state for the checked pure-Integer substitution walker.
///
/// Pure proposition substitution traverses the proposition itself because the
/// general proposition walker deliberately does not rewrite binder-bearing
/// propositions.  Keeping the scope token here lets that traversal install
/// the same carrier-aware mapping in one `TermRewrite` instance and restore it
/// on every return path without cloning a suffix environment.
pub(crate) struct IntegerSubstitutionScope {
    variable: Variable,
    previous: Option<Variable>,
    scope_id: u64,
    integer_shadowed: bool,
}

/// Saved lexical state for a C-carrier quantifier visited by the checked
/// Integer proposition substitution walker.  C and Integer binders share the
/// numeric variable namespace in the term representation, but their lexical
/// mappings must remain separate.
pub(crate) struct ProgramValueSubstitutionScope {
    variable: Variable,
    previous: Option<Variable>,
    scope_id: u64,
}

/// Algebraic binders have their own lexical map, independent of Integer
/// and program-value binders with the same numeric variable ID.
pub(crate) struct AlgebraicSubstitutionScope {
    variable: Variable,
    previous: Option<Variable>,
    scope_id: u64,
}

#[derive(PartialEq, Eq, Hash)]
enum BoundedIndexKey {
    Variable(Variable),
    Term(SharedMachineIntegerTerm),
}

impl BoundedIndexKey {
    fn of(value: &SharedMachineIntegerTerm) -> Self {
        match value.operand_view().variable() {
            Some(variable) => Self::Variable(*variable),
            None => Self::Term(value.clone()),
        }
    }
}

// Build once, on the first unsigned wide-offset query, from explicitly cited
// conditions. Later offset queries check their full-width index by key. Scalar
// normalization never prepares this pointer-only index.
fn bounded_uint64_indices(
    conditions: &HashMap<OldConditionTerm, bool>,
) -> std::collections::HashSet<BoundedIndexKey> {
    conditions
        .iter()
        .filter_map(|(condition, value)| {
            crate::instrumentation::record_deterministic_work(1);
            let (lower, upper, strict) = match (condition, *value) {
                (
                    OldConditionTerm::Compare {
                        format: MachineIntegerType::UInt64,
                        relation: CompareRelation::LessEqual,
                        left: a,
                        right: b,
                    },
                    true,
                )
                | (
                    OldConditionTerm::Compare {
                        format: MachineIntegerType::UInt64,
                        relation: CompareRelation::GreaterThan,
                        left: a,
                        right: b,
                    },
                    false,
                ) => (a, b, false),
                (
                    OldConditionTerm::Compare {
                        format: MachineIntegerType::UInt64,
                        relation: CompareRelation::LessThan,
                        left: a,
                        right: b,
                    },
                    true,
                )
                | (
                    OldConditionTerm::Compare {
                        format: MachineIntegerType::UInt64,
                        relation: CompareRelation::GreaterEqual,
                        left: a,
                        right: b,
                    },
                    false,
                ) => (a, b, true),
                (
                    OldConditionTerm::Compare {
                        format: MachineIntegerType::UInt64,
                        relation: CompareRelation::GreaterEqual,
                        left: a,
                        right: b,
                    },
                    true,
                )
                | (
                    OldConditionTerm::Compare {
                        format: MachineIntegerType::UInt64,
                        relation: CompareRelation::LessThan,
                        left: a,
                        right: b,
                    },
                    false,
                ) => (b, a, false),
                (
                    OldConditionTerm::Compare {
                        format: MachineIntegerType::UInt64,
                        relation: CompareRelation::GreaterThan,
                        left: a,
                        right: b,
                    },
                    true,
                )
                | (
                    OldConditionTerm::Compare {
                        format: MachineIntegerType::UInt64,
                        relation: CompareRelation::LessEqual,
                        left: a,
                        right: b,
                    },
                    false,
                ) => (b, a, true),
                _ => return None,
            };
            let limit = upper.uint64_as_const()?;
            let limit = if strict { limit.checked_sub(1)? } else { limit };
            (limit <= i32::MAX as u64).then(|| {
                if let OldMachineTerm::Variable(variable) = lower.as_ref() {
                    BoundedIndexKey::Variable(*variable)
                } else {
                    BoundedIndexKey::Term(SharedMachineIntegerTerm::index(
                        MachineIntegerType::Int64,
                        lower.as_ref().clone(),
                    ))
                }
            })
        })
        .collect()
}

/// Lexical dependencies of a selected read address. Variable IDs are local
/// to their carrier: an Integer binder cannot shadow a C address variable.
struct ReadAddressDependencies {
    program_values: BTreeSet<Variable>,
    integer: BTreeSet<Variable>,
    algebraic: BTreeSet<Variable>,
}

impl ReadAddressDependencies {
    fn is_bound_in(&self, scope: &RewriteScope) -> bool {
        self.program_values
            .iter()
            .any(|variable| scope.program_values.contains_key(variable))
            || self
                .integer
                .iter()
                .any(|variable| scope.integer.contains_key(variable))
            || self
                .algebraic
                .iter()
                .any(|variable| scope.algebraic.contains_key(variable))
    }
}

struct OffsetReplacement<'a> {
    from: &'a AddressOffset,
    to: &'a AddressOffset,
    retained: std::cell::OnceCell<Option<(OffsetKey, SharedAddressOffset)>>,
}

impl<'a> OffsetReplacement<'a> {
    fn new(from: &'a AddressOffset, to: &'a AddressOffset) -> Self {
        Self {
            from,
            to,
            retained: Default::default(),
        }
    }

    fn retained(&self) -> Option<&(OffsetKey, SharedAddressOffset)> {
        self.retained
            .get_or_init(|| {
                let to = self.to.shared().clone();
                Some((OffsetKey::native(self.from), to))
            })
            .as_ref()
    }
}

pub(crate) struct TermRewrite<'a> {
    // Comparison only: rebuild arithmetic through its assumption-free
    // identities. Ordinary equality rewrites retain the written nodes.
    comparison_arithmetic: bool,
    algebraic: Option<(&'a AlgebraicTerm, &'a AlgebraicTerm)>,
    bitvector: Option<(MachineOperandView<'a>, MachineOperandView<'a>)>,
    integer_exact: Option<(&'a SharedIntegerTerm, &'a SharedIntegerTerm)>,
    pointer_variable: Option<(Variable, &'a Address)>,
    pointer_addresses_only: bool,
    pointer_exact: Option<(&'a Address, &'a Address)>,
    pointer_value_exact: Option<(&'a OldPointer, &'a OldPointer)>,
    pointer_offset_exact: Option<OffsetReplacement<'a>>,
    /// A `Bool` equality's rewrite (Stage 5, rule L-Eq): every occurrence of
    /// the first condition is replaced by the second.
    condition_exact: Option<(&'a OldConditionTerm, &'a OldConditionTerm)>,
    conditions: Option<&'a HashMap<OldConditionTerm, bool>>,
    cited_conditions: Option<&'a crate::kernel::equality_graph::EqualityGraph>,
    cited_comparison_context: Option<&'a PureFactContext>,
    bounded_uint64_indices: Option<std::collections::HashSet<BoundedIndexKey>>,
    pointer_association_conditions:
        Option<HashMap<(u64, u64), Vec<(OldMachineTerm, OldMachineTerm, bool)>>>,
    equality_graph: Option<&'a crate::kernel::equality_graph::EqualityGraph>,
    pointer_context: Option<&'a PureFactContext>,
    collected_conditions: Option<Vec<OldConditionTerm>>,
    integer_cache: HashMap<(u64, u64, bool, bool), IntegerTerm>,
    fold_integer_bridge: KernelTermExport,
    pointer_application_cache: HashMap<(u64, u64, bool, bool), AddressBase>,
    pointer_origin_cache: HashMap<(crate::kernel::Load, u64, bool, bool), AddressBase>,
    scope_renaming_max: u64,
    integer_body_summaries: crate::kernel::prelude::RetainedIntegerScopeSummaries,
    integer_variables: Option<IntegerVariableRewrite<'a>>,
    integer_replacement_variables: Option<BTreeSet<Variable>>,
    bitvector_replacement_variables: Option<BTreeSet<Variable>>,
    integer_replacement_variable_max: Option<u64>,
    bitvector_replacement_variable_max: Option<u64>,
    integer_renaming_max: Option<u64>,
    enforce_integer_work_limit: bool,
    typed_variables: Option<TypedVariableReplacements<'a>>,
    comparison_reads: Option<
        &'a HashMap<((u32, u32), Address, LoadKind), (OldMachineTerm, ReadAddressDependencies)>,
    >,
    /// Reads of a library or enum value at a fixed address, each with the
    /// value its state stores there: the read-over-write authority for
    /// values a scalar cell cannot hold.
    comparison_algebraic_reads:
        Option<&'a HashMap<(crate::kernel::ProgramPoint, Address), AlgebraicTerm>>,
    // Recursive read-address walks must share this memo: each address can
    // reference the same earlier read more than once. Include lexical scope
    // and temporary rewrite modes so entries never cross interpretations.
    shared_machine_cache: Option<
        std::rc::Rc<std::cell::RefCell<HashMap<(u64, u64, bool, bool, bool, bool), KernelTerm>>>,
    >,
    integer_shadowed: bool,
    scope: RewriteScope,
    scope_id: u64,
    next_scope_id: u64,
    source_disabled: bool,
    source_variables_reserved: bool,
    reserved_variables: BTreeSet<Variable>,
    fresh_next: u64,
    replacement_carriers: Option<CarrierVariables>,
    /// Materialize registered load origins for an Integer fold body or a
    /// selected complete-pointer value rewrite. Other rewrites keep load
    /// variables opaque, avoiding unrelated registry DAG expansion.
    resolve_registered_loads: bool,
    /// Rewritten registered loads are memoized by load identity and lexical
    /// scope.  A changed address is re-minted as a load variable for the
    /// exact original state, so a branching registry DAG stays shared
    /// instead of expanding into owned `MemoryLoad` trees at every parent.
    registered_load_cache: HashMap<(Variable, u64), Variable>,
    /// A malformed registry cycle is rejected before recursive pointer
    /// expansion can consume unbounded work.
    registered_load_pointer_active: BTreeSet<Variable>,
    /// Set when the walker met a scope it will not substitute through. The
    /// value it then hands back is a placeholder, not a rewritten term, so
    /// both refusal flags are private: callers read them through
    /// [`TermRewrite::refusal`], and a debug build panics when a walker that
    /// refused a scope is dropped without that question having been asked.
    unsupported_integer_scope: bool,
    integer_work_exhausted: bool,
    refusal_observed: std::cell::Cell<bool>,
    pub(crate) changed: bool,
    #[cfg(test)]
    pub(crate) visits: usize,
    #[cfg(test)]
    pub(crate) collector_visits: usize,
}
/// Why a [`TermRewrite`] result must not be used.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum RewriteRefusal {
    /// The walker ran out of checked work; the enclosing tactic's budget
    /// report is the diagnostic.
    WorkExhausted,
    /// The walker met a binder or load it will not substitute through.
    UnsupportedScope,
}

impl Drop for TermRewrite<'_> {
    fn drop(&mut self) {
        // A refused scope leaves a placeholder constant in the result. A
        // caller that never asks cannot have told it from a rewritten term,
        // which is how `rewrite` once turned an unfolded `match` into `0`.
        // Work exhaustion is not asserted here: it is sticky in the run's
        // budget state, which fails the run whatever the caller does.
        #[cfg(debug_assertions)]
        if self.unsupported_integer_scope
            && !self.refusal_observed.get()
            && !std::thread::panicking()
        {
            panic!("a TermRewrite refused a scope and its caller never read `refusal()`");
        }
    }
}

impl<'a> TermRewrite<'a> {
    /// Whether the value this walker returned is a placeholder. Every caller
    /// that can reach a refusing scope must ask before using the result.
    /// Whether the rewrite replaced anything it was given to replace.
    pub(crate) fn replaced_anything(&self) -> bool {
        self.changed
    }

    pub(crate) fn refusal(&self) -> Option<RewriteRefusal> {
        self.refusal_observed.set(true);
        self.refusal_status()
    }

    // Internal traversal must not acknowledge a refusal on the caller's behalf.
    fn refusal_status(&self) -> Option<RewriteRefusal> {
        if self.integer_work_exhausted {
            Some(RewriteRefusal::WorkExhausted)
        } else if self.unsupported_integer_scope {
            Some(RewriteRefusal::UnsupportedScope)
        } else {
            None
        }
    }

    /// Whether checked work ran out, for a caller that stops early between
    /// walker calls. It does not stand in for [`TermRewrite::refusal`].
    pub(crate) fn work_exhausted(&self) -> bool {
        self.integer_work_exhausted
    }

    fn for_arithmetic_comparison() -> Self {
        let mut rewrite = Self::empty();
        rewrite.comparison_arithmetic = true;
        rewrite.enforce_integer_work_limit = true;
        // Comparison introduces no substitution or fresh binder.
        rewrite.source_variables_reserved = true;
        // Normalize the selected scalar read's address too. The read's
        // state and loaded-pointer identities stay opaque; the existing
        // per-scope registry memo shares repeated address terms.
        rewrite.resolve_registered_loads = true;
        rewrite
    }

    pub(super) fn retained_arithmetic_comparison(
        [left, right]: &[KernelTerm; 2],
    ) -> Option<[KernelTerm; 2]> {
        let mut rewrite = Self::for_arithmetic_comparison();
        let result = (|| {
            Some([
                rewrite.rewrite_stored_integer_root(left)?,
                rewrite.rewrite_stored_integer_root(right)?,
            ])
        })();
        if rewrite.refusal().is_some() || crate::instrumentation::deadline_exceeded_with_work(0) {
            return None;
        }
        result
    }

    pub(crate) fn arithmetic_comparison(proposition: &Proposition) -> Option<Proposition> {
        if crate::instrumentation::deadline_exceeded_with_work(0) {
            return None;
        }
        if let Some(result) =
            ARITHMETIC_COMPARISONS.with(|cache| cache.borrow().get(proposition).cloned())
        {
            return result;
        }
        let mut rewrite = Self::for_arithmetic_comparison();
        let result = rewrite.proposition(proposition);
        if rewrite.refusal().is_some() || crate::instrumentation::deadline_exceeded_with_work(0) {
            return None;
        }
        let result = (result != *proposition).then_some(result);
        ARITHMETIC_COMPARISONS.with(|cache| {
            let mut cache = cache.borrow_mut();
            if cache.len() >= 4096 {
                cache.clear();
            }
            cache.insert(proposition.clone(), result.clone());
        });
        result
    }

    pub(crate) fn normalize_algebraic(term: &AlgebraicTerm) -> Option<AlgebraicTerm> {
        if !term.is_well_formed() {
            return None;
        }
        let mut rewrite = Self::empty();
        let result = rewrite.algebraic(term);
        (rewrite.refusal().is_none() && rewrite.changed).then_some(result)
    }

    pub(crate) fn new(from: &'a AlgebraicTerm, to: &'a AlgebraicTerm) -> Self {
        let mut rewrite = Self::empty();
        rewrite.algebraic = Some((from, to));
        rewrite
    }

    fn preserves_algebraic_matches(&self) -> bool {
        self.algebraic.is_some()
            || self.integer_exact.is_some()
            || self.integer_variables.is_some()
            || MATCH_REDUCTION_SUSPENDED.with(std::cell::Cell::get)
    }

    fn preserves_closed_value_conditional(&self, guard: &OldConditionTerm) -> bool {
        (self.integer_variables.is_some() || MATCH_REDUCTION_SUSPENDED.with(std::cell::Cell::get))
            && crate::kernel::proof::fact_reasoning::literal_value_if_guard(guard).is_some()
    }

    fn preserves_machine_conditional(&self, guard: &OldConditionTerm) -> bool {
        self.integer_exact.is_some()
            || (self.integer_variables.is_some()
                && matches!(
                    guard,
                    OldConditionTerm::Compare {
                        format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
                        relation: CompareRelation::Equal,
                        left,
                        right,
                    } if left.as_const().is_some() && right.as_const().is_some()
                ))
    }

    /// Exact Integer congruence over the selected logical DAG. Internal
    /// binder scopes are refused; logical quantifiers are handled by the
    /// equality-rewrite rule before this atomic walker is entered.
    pub(crate) fn for_integer_exact(
        from: &'a SharedIntegerTerm,
        to: &'a SharedIntegerTerm,
    ) -> Self {
        let mut rewrite = Self::empty();
        rewrite.integer_exact = Some((from, to));
        rewrite.enforce_integer_work_limit = true;
        rewrite
    }

    /// Simultaneous one-step read comparison. Only selected syntax is visited;
    /// inserted values and the contents of states remain opaque.
    #[cfg(test)]
    pub(crate) fn comparison_read_batch(
        proposition: &Proposition,
        replacements: impl IntoIterator<Item = (OldMachineTerm, OldMachineTerm)>,
    ) -> Option<Proposition> {
        Self::comparison_read_batch_with_algebraic(proposition, replacements, &HashMap::new())
    }

    /// [`Self::comparison_read_batch`], also replacing each read of a
    /// library or enum value in `algebraic_reads` by the value stored there.
    pub(crate) fn comparison_read_batch_with_algebraic(
        proposition: &Proposition,
        replacements: impl IntoIterator<Item = (OldMachineTerm, OldMachineTerm)>,
        algebraic_reads: &HashMap<(crate::kernel::ProgramPoint, Address), AlgebraicTerm>,
    ) -> Option<Proposition> {
        let mut named = BTreeMap::new();
        let mut reads = HashMap::new();
        for (source, value) in replacements {
            if crate::instrumentation::deadline_exceeded_with_work(1) {
                return None;
            }
            if let Some(read) = crate::kernel::eval::viewed_as_memory_load(&source) {
                let mut carriers = CarrierVariables::for_rewrite(true);
                // Collect the explicit address, never its state contents.
                if let OldMachineTerm::MemoryLoad(_, pointer, _) = &read {
                    collect_pointer_carriers(pointer, &mut carriers);
                }
                if carriers.exhausted() {
                    return None;
                }
                let dependencies = ReadAddressDependencies {
                    program_values: carriers.program_values,
                    integer: carriers.integer,
                    algebraic: carriers.algebraic,
                };
                let OldMachineTerm::MemoryLoad(memory, pointer, kind) = read else {
                    unreachable!()
                };
                reads.insert(
                    (
                        memory.shared_memory().arena_id(),
                        Address::from(pointer),
                        kind,
                    ),
                    (value, dependencies),
                );
            } else if let OldMachineTerm::Variable(variable) = source {
                // Registered names use the exact read table, including its
                // lexical address dependencies, just like structural reads.
                named.insert(variable, TypedProgramValueReplacement::Bitvector(value));
            }
        }
        if named.is_empty() && reads.is_empty() && algebraic_reads.is_empty() {
            return Some(proposition.clone());
        }
        let integers = BTreeMap::new();
        let algebraic = BTreeMap::new();
        let mut rewrite = TermRewrite::for_typed_variables(&named, &integers, &algebraic);
        rewrite.comparison_reads = Some(&reads);
        rewrite.comparison_algebraic_reads = Some(algebraic_reads);
        let result = rewrite.substitute_proposition(proposition);
        if rewrite.refusal().is_some() {
            None
        } else {
            Some(result)
        }
    }

    fn empty() -> Self {
        Self {
            comparison_arithmetic: false,
            comparison_reads: None,
            comparison_algebraic_reads: None,
            shared_machine_cache: None,
            conditions: None,
            cited_conditions: None,
            cited_comparison_context: None,
            bounded_uint64_indices: None,
            pointer_association_conditions: None,
            equality_graph: None,
            pointer_context: None,
            pointer_addresses_only: false,
            collected_conditions: None,
            algebraic: None,
            bitvector: None,
            integer_exact: None,
            changed: false,
            integer_cache: HashMap::new(),
            fold_integer_bridge: KernelTermExport::default(),
            pointer_application_cache: HashMap::new(),
            pointer_origin_cache: HashMap::new(),
            scope_renaming_max: 0,
            integer_body_summaries: Default::default(),
            integer_replacement_variables: None,
            bitvector_replacement_variables: None,
            integer_replacement_variable_max: None,
            bitvector_replacement_variable_max: None,
            integer_renaming_max: None,
            enforce_integer_work_limit: false,
            integer_variables: None,
            typed_variables: None,
            integer_shadowed: false,
            scope: RewriteScope::default(),
            scope_id: 0,
            next_scope_id: 1,
            source_disabled: false,
            source_variables_reserved: false,
            reserved_variables: BTreeSet::new(),
            fresh_next: 0,
            replacement_carriers: None,
            resolve_registered_loads: false,
            registered_load_cache: HashMap::new(),
            registered_load_pointer_active: BTreeSet::new(),
            unsupported_integer_scope: false,
            refusal_observed: std::cell::Cell::new(false),
            integer_work_exhausted: false,
            pointer_variable: None,
            pointer_exact: None,
            pointer_value_exact: None,
            pointer_offset_exact: None,
            condition_exact: None,
            #[cfg(test)]
            visits: 0,
            #[cfg(test)]
            collector_visits: 0,
        }
    }

    /// The rewrite by a true `Bool` equality `from == to` (rule L-Eq): the
    /// two have the same truth, so either may stand for the other wherever
    /// a `Bool` is read.
    pub(crate) fn for_condition_exact(
        from: &'a OldConditionTerm,
        to: &'a OldConditionTerm,
    ) -> Self {
        let mut rewrite = Self::empty();
        rewrite.condition_exact = Some((from, to));
        rewrite
    }

    pub(crate) fn for_bits(from: &'a OldMachineTerm, to: &'a OldMachineTerm) -> Self {
        let _collection_scope = crate::instrumentation::CheckedCollectionScope::new();
        Self::for_bits_with_budget(
            MachineOperandView::Old(from),
            MachineOperandView::Old(to),
            false,
        )
    }

    fn for_bits_with_budget(
        from: MachineOperandView<'a>,
        to: MachineOperandView<'a>,
        budgeted: bool,
    ) -> Self {
        let mut replacement_carriers = CarrierVariables::for_rewrite(budgeted);
        // Shared replacements may be growing DAG prefixes. Capture information
        // is needed only when entering a binder, not for an ordinary rewrite.
        let defer_capture = matches!(to, MachineOperandView::Shared(_));
        if !defer_capture {
            collect_machine_operand_carriers(to, &mut replacement_carriers);
        }
        let CarrierVariables {
            integer: integer_replacement_variables,
            program_values: bitvector_replacement_variables,
            work_exhausted: replacement_work_exhausted,
            ..
        } = replacement_carriers;
        let integer_replacement_variable_max = integer_replacement_variables
            .iter()
            .map(|variable| variable.0)
            .max();
        let bitvector_replacement_variable_max = bitvector_replacement_variables
            .iter()
            .map(|variable| variable.0)
            .max();
        let mut rewrite = Self {
            comparison_arithmetic: false,
            comparison_reads: None,
            comparison_algebraic_reads: None,
            shared_machine_cache: None,
            conditions: None,
            cited_conditions: None,
            cited_comparison_context: None,
            bounded_uint64_indices: None,
            pointer_association_conditions: None,
            equality_graph: None,
            pointer_context: None,
            pointer_addresses_only: false,
            collected_conditions: None,
            algebraic: None,
            bitvector: Some((from, to)),
            integer_exact: None,
            changed: false,
            integer_cache: HashMap::new(),
            fold_integer_bridge: KernelTermExport::default(),
            pointer_application_cache: HashMap::new(),
            pointer_origin_cache: HashMap::new(),
            scope_renaming_max: 0,
            integer_body_summaries: Default::default(),
            integer_replacement_variables: (!defer_capture)
                .then_some(integer_replacement_variables),
            bitvector_replacement_variables: (!defer_capture)
                .then_some(bitvector_replacement_variables),
            integer_replacement_variable_max,
            bitvector_replacement_variable_max,
            integer_renaming_max: None,
            enforce_integer_work_limit: false,
            integer_variables: None,
            typed_variables: None,
            integer_shadowed: false,
            scope: RewriteScope::default(),
            scope_id: 0,
            next_scope_id: 1,
            source_disabled: false,
            source_variables_reserved: false,
            reserved_variables: BTreeSet::new(),
            fresh_next: 0,
            replacement_carriers: None,
            resolve_registered_loads: false,
            registered_load_cache: HashMap::new(),
            registered_load_pointer_active: BTreeSet::new(),
            unsupported_integer_scope: false,
            refusal_observed: std::cell::Cell::new(false),
            integer_work_exhausted: replacement_work_exhausted,
            pointer_variable: None,
            pointer_exact: None,
            pointer_value_exact: None,
            pointer_offset_exact: None,
            condition_exact: None,
            #[cfg(test)]
            visits: 0,
            #[cfg(test)]
            collector_visits: 0,
        };
        rewrite.seed_fresh_allocator();
        rewrite
    }

    /// The ordinary substitution profile with a retained replacement.
    pub(crate) fn for_machine_operand(
        from: &'a OldMachineTerm,
        to: MachineOperandView<'a>,
    ) -> Self {
        let _collection_scope = crate::instrumentation::CheckedCollectionScope::new();
        Self::for_bits_with_budget(MachineOperandView::Old(from), to, false)
    }

    /// Construct the checked machine rewrite used by range-fold laws. Setup
    /// collection and the subsequent traversal share the tactic's bounded
    /// work state, so a partial term is never accepted as a checked result.
    pub(crate) fn for_bits_checked(from: &'a OldMachineTerm, to: &'a OldMachineTerm) -> Self {
        Self::for_machine_operand_checked(from, MachineOperandView::Old(to))
    }

    pub(crate) fn for_machine_operand_checked(
        from: &'a OldMachineTerm,
        to: MachineOperandView<'a>,
    ) -> Self {
        Self::for_machine_operands_checked(MachineOperandView::Old(from), to)
    }

    pub(crate) fn for_machine_operands_checked(
        from: MachineOperandView<'a>,
        to: MachineOperandView<'a>,
    ) -> Self {
        let _collection_scope = crate::instrumentation::CheckedCollectionScope::new();
        let mut rewrite = Self::for_bits_with_budget(from, to, true);
        rewrite.enforce_integer_work_limit = true;
        rewrite.integer_work_exhausted |= crate::instrumentation::checked_collection_exhausted();
        rewrite
    }

    /// Expose registered read addresses for checked fold substitution or
    /// pointer congruence. Ordinary machine rewrites keep these reads opaque.
    pub(crate) fn enable_registered_load_resolution(&mut self) {
        self.resolve_registered_loads = true;
    }

    fn rewrite_registered_load(&mut self, variable: Variable) -> Option<Variable> {
        // Registered addresses can themselves name reads. Charge each lookup,
        // including cache hits, so this relevant-address traversal shares the
        // enclosing tactic's work and deadline bounds.
        if crate::instrumentation::deadline_exceeded_with_work(1) {
            self.integer_work_exhausted = true;
            return None;
        }
        if !self.registered_load_pointer_active.insert(variable) {
            // A reserved load variable with a cyclic registry origin cannot
            // be rewritten soundly.  Let checked callers reject the result
            // instead of retaining an under-substituted pointer.
            self.unsupported_integer_scope = true;
            return None;
        }
        let cache_key = (variable, self.scope_id);
        if let Some(rewritten) = self.registered_load_cache.get(&cache_key) {
            let rewritten = *rewritten;
            self.registered_load_pointer_active.remove(&variable);
            self.changed |= rewritten != variable;
            return Some(rewritten);
        }
        // Substitution can expose another cell even when it changes only
        // a fold's bound index. Its producer state, rather than the old
        // address's projected value state, owns that new read.
        let origin = crate::kernel::registered_load_origin_for_variable(&variable);
        let Some((memory, pointer)) =
            origin.or_else(|| crate::kernel::eval::registered_load_for_variable(&variable))
        else {
            self.registered_load_pointer_active.remove(&variable);
            self.unsupported_integer_scope = true;
            return None;
        };
        let rewritten = self.pointer(&pointer);
        self.registered_load_pointer_active.remove(&variable);
        if self.checked_work_exhausted() || self.unsupported_integer_scope {
            return None;
        }
        let rewritten = if rewritten == pointer {
            variable
        } else {
            let Some(kind) = crate::kernel::registered_load_kind_for_variable(&variable) else {
                self.unsupported_integer_scope = true;
                return None;
            };
            // A cell holding a stored read of the same kind reads as it.
            let stored = match memory.memory().known_value(&rewritten) {
                Some(
                    ProgramValue::Int32(OldMachineTerm::Variable(stored))
                    | ProgramValue::UInt32(OldMachineTerm::Variable(stored)),
                ) if crate::kernel::is_load_variable(&stored)
                    && crate::kernel::registered_load_kind_for_variable(&stored) == Some(kind) =>
                {
                    Some(stored)
                }
                _ => None,
            };
            if let Some(stored) = stored {
                stored
            } else {
                crate::kernel::eval::load_variable_for_exact_cell(
                    &memory,
                    &rewritten,
                    kind,
                    crate::kernel::registered_load_bytes_for_variable(&variable).unwrap_or_else(
                        crate::kernel::resource_tracker::widest_scalar_access_bytes,
                    ),
                )
            }
        };
        self.changed |= rewritten != variable;
        self.registered_load_cache.insert(cache_key, rewritten);
        Some(rewritten)
    }

    pub(crate) fn for_conditions(conditions: &'a HashMap<OldConditionTerm, bool>) -> Self {
        Self {
            comparison_arithmetic: false,
            comparison_reads: None,
            comparison_algebraic_reads: None,
            shared_machine_cache: None,
            algebraic: None,
            bitvector: None,
            integer_exact: None,
            conditions: Some(conditions),
            cited_conditions: None,
            cited_comparison_context: None,
            bounded_uint64_indices: None,
            pointer_association_conditions: None,
            equality_graph: None,
            pointer_context: None,
            pointer_addresses_only: false,
            collected_conditions: None,
            changed: false,
            integer_cache: HashMap::new(),
            fold_integer_bridge: KernelTermExport::default(),
            pointer_application_cache: HashMap::new(),
            pointer_origin_cache: HashMap::new(),
            scope_renaming_max: 0,
            integer_body_summaries: Default::default(),
            integer_replacement_variables: None,
            bitvector_replacement_variables: None,
            integer_replacement_variable_max: None,
            bitvector_replacement_variable_max: None,
            integer_renaming_max: None,
            enforce_integer_work_limit: false,
            integer_variables: None,
            typed_variables: None,
            integer_shadowed: false,
            scope: RewriteScope::default(),
            scope_id: 0,
            next_scope_id: 1,
            source_disabled: false,
            source_variables_reserved: false,
            reserved_variables: BTreeSet::new(),
            fresh_next: 0,
            replacement_carriers: None,
            resolve_registered_loads: false,
            registered_load_cache: HashMap::new(),
            registered_load_pointer_active: BTreeSet::new(),
            unsupported_integer_scope: false,
            refusal_observed: std::cell::Cell::new(false),
            integer_work_exhausted: false,
            pointer_variable: None,
            pointer_exact: None,
            pointer_value_exact: None,
            pointer_offset_exact: None,
            condition_exact: None,
            #[cfg(test)]
            visits: 0,
            #[cfg(test)]
            collector_visits: 0,
        }
    }
    /// Conditional reduction in the checked proof context. The graph can
    /// establish positive equality only; an unsuccessful query stays unknown.
    /// Like cited conditions, this context never enters binder bodies.
    pub(in crate::kernel) fn for_conditions_with_graph(
        conditions: &'a HashMap<OldConditionTerm, bool>,
        graph: &'a crate::kernel::equality_graph::EqualityGraph,
    ) -> Self {
        let mut rewrite = Self::for_conditions(conditions);
        rewrite.equality_graph = Some(graph);
        rewrite
    }

    pub(in crate::kernel) fn for_cited_conditions_with_context(
        conditions: &'a HashMap<OldConditionTerm, bool>,
        selected: &'a PureFactContext,
        ambient: &'a PureFactContext,
    ) -> Self {
        let mut rewrite = Self::for_cited_conditions_with_graph(
            conditions,
            &selected.equality_graph,
            &ambient.equality_graph,
        );
        rewrite.cited_comparison_context = Some(selected);
        rewrite.pointer_context = Some(ambient);
        rewrite
    }

    /// The explicitly selected premises may decide either polarity. Their
    /// graph is built once by the selecting operation, never by a lookup.
    pub(in crate::kernel) fn for_cited_conditions_with_graph(
        conditions: &'a HashMap<OldConditionTerm, bool>,
        selected: &'a crate::kernel::equality_graph::EqualityGraph,
        ambient: &'a crate::kernel::equality_graph::EqualityGraph,
    ) -> Self {
        let mut rewrite = Self::for_conditions_with_graph(conditions, ambient);
        rewrite.cited_conditions = Some(selected);
        rewrite
    }

    pub(crate) fn for_pointer_offset_exact(from: &'a AddressOffset, to: &'a AddressOffset) -> Self {
        let mut rewrite = Self::empty();
        rewrite.pointer_offset_exact = Some(OffsetReplacement::new(from, to));
        rewrite.enforce_integer_work_limit = true;
        rewrite
    }

    pub(crate) fn for_pointer_exact(from: &'a Address, to: &'a Address) -> Self {
        let mut rewrite = Self::empty();
        rewrite.pointer_exact = Some((from, to));
        rewrite.enforce_integer_work_limit = true;
        rewrite
    }

    pub(crate) fn for_pointer_value_exact(from: &'a OldPointer, to: &'a OldPointer) -> Self {
        let mut rewrite = Self::empty();
        rewrite.pointer_value_exact = Some((from, to));
        // Reads named by load variables can sit at addresses formed from
        // the substituted value, such as a bound `p->len` beside `p->data`.
        rewrite.resolve_registered_loads = true;
        // A full value equality also rewrites raw addresses in loadability,
        // memory endpoints and other address-only propositions.
        rewrite.pointer_exact = Some((from.address(), to.address()));
        // Native C arguments share a numeric block. Their base pointer is
        // an offset subterm of a displaced copy, rather than its own block.
        // A full equality also establishes this same-block offset equality.
        if from.address().base == AddressBase::ExternalArgument
            && to.address().base == AddressBase::ExternalArgument
        {
            rewrite.pointer_offset_exact = Some(OffsetReplacement::new(
                &from.address().offset,
                &to.address().offset,
            ));
        }
        rewrite.enforce_integer_work_limit = true;
        rewrite
    }

    /// Numeric address equality cannot substitute an allocation or bounds identity.
    pub(crate) fn for_pointer_address_variable(from: Variable, to: &'a Address) -> Self {
        let mut rewrite = Self::for_pointer_variable(from, to);
        rewrite.pointer_addresses_only = true;
        rewrite
    }

    pub(crate) fn for_pointer_variable(from: Variable, to: &'a Address) -> Self {
        Self {
            comparison_arithmetic: false,
            comparison_reads: None,
            comparison_algebraic_reads: None,
            shared_machine_cache: None,
            algebraic: None,
            bitvector: None,
            integer_exact: None,
            pointer_variable: Some((from, to)),
            pointer_exact: None,
            pointer_value_exact: None,
            pointer_offset_exact: None,
            condition_exact: None,
            conditions: None,
            cited_conditions: None,
            cited_comparison_context: None,
            bounded_uint64_indices: None,
            pointer_association_conditions: None,
            equality_graph: None,
            pointer_context: None,
            pointer_addresses_only: false,
            collected_conditions: None,
            integer_cache: HashMap::new(),
            fold_integer_bridge: KernelTermExport::default(),
            pointer_application_cache: HashMap::new(),
            pointer_origin_cache: HashMap::new(),
            scope_renaming_max: 0,
            integer_body_summaries: Default::default(),
            integer_replacement_variables: None,
            bitvector_replacement_variables: None,
            integer_replacement_variable_max: None,
            bitvector_replacement_variable_max: None,
            integer_renaming_max: None,
            enforce_integer_work_limit: false,
            integer_variables: None,
            typed_variables: None,
            integer_shadowed: false,
            scope: RewriteScope::default(),
            scope_id: 0,
            next_scope_id: 1,
            source_disabled: false,
            source_variables_reserved: false,
            reserved_variables: BTreeSet::new(),
            fresh_next: 0,
            replacement_carriers: None,
            resolve_registered_loads: false,
            registered_load_cache: HashMap::new(),
            registered_load_pointer_active: BTreeSet::new(),
            unsupported_integer_scope: false,
            refusal_observed: std::cell::Cell::new(false),
            integer_work_exhausted: false,
            changed: false,
            #[cfg(test)]
            visits: 0,
            #[cfg(test)]
            collector_visits: 0,
        }
    }

    /// Maps Integer variables in one binder-free atomic proposition. The
    /// caller handles logical binders and reserves the replacement's variables.
    /// Unsupported internal scopes are reported, never silently copied.
    pub(crate) fn for_integer_variables(
        from: Variable,
        to: &'a IntegerTerm,
        shadowed: bool,
        renamings: &'a BTreeMap<Variable, Variable>,
    ) -> Self {
        let _collection_scope = crate::instrumentation::CheckedCollectionScope::new();
        let mut replacement_integer_binders = BTreeSet::new();
        let mut replacement_bitvector_binders = BTreeSet::new();
        crate::kernel::prelude::collect_integer_binder_variables(
            to,
            &mut replacement_integer_binders,
            &mut replacement_bitvector_binders,
        );
        let mut integer_replacement_variables = BTreeSet::new();
        crate::kernel::prelude::collect_integer_free_variables(
            to,
            &mut integer_replacement_variables,
        );
        let mut bitvector_replacement_variables = BTreeSet::new();
        crate::kernel::prelude::collect_integer_capture_bitvector_variables(
            to,
            &mut bitvector_replacement_variables,
        );
        let integer_replacement_variable_max = integer_replacement_variables
            .iter()
            .chain(replacement_integer_binders.iter())
            .map(|variable| variable.0)
            .max();
        let bitvector_replacement_variable_max = bitvector_replacement_variables
            .iter()
            .chain(replacement_bitvector_binders.iter())
            .map(|variable| variable.0)
            .max();
        let integer_renaming_max = renamings.values().map(|variable| variable.0).max();
        let mut walker = Self {
            comparison_arithmetic: false,
            comparison_reads: None,
            comparison_algebraic_reads: None,
            shared_machine_cache: None,
            algebraic: None,
            bitvector: None,
            integer_exact: None,
            pointer_variable: None,
            pointer_exact: None,
            pointer_value_exact: None,
            pointer_offset_exact: None,
            condition_exact: None,
            conditions: None,
            cited_conditions: None,
            cited_comparison_context: None,
            bounded_uint64_indices: None,
            pointer_association_conditions: None,
            equality_graph: None,
            pointer_context: None,
            pointer_addresses_only: false,
            collected_conditions: None,
            integer_cache: HashMap::new(),
            fold_integer_bridge: KernelTermExport::default(),
            pointer_application_cache: HashMap::new(),
            pointer_origin_cache: HashMap::new(),
            scope_renaming_max: 0,
            integer_body_summaries: Default::default(),
            integer_replacement_variables: Some(integer_replacement_variables),
            bitvector_replacement_variables: Some(bitvector_replacement_variables),
            integer_replacement_variable_max,
            bitvector_replacement_variable_max,
            integer_renaming_max,
            enforce_integer_work_limit: true,
            integer_variables: None,
            typed_variables: None,
            integer_shadowed: shadowed,
            scope: RewriteScope {
                integer: renamings.clone(),
                ..RewriteScope::default()
            },
            scope_id: 0,
            next_scope_id: 1,
            source_disabled: false,
            source_variables_reserved: false,
            reserved_variables: BTreeSet::new(),
            fresh_next: 0,
            replacement_carriers: None,
            resolve_registered_loads: false,
            registered_load_cache: HashMap::new(),
            registered_load_pointer_active: BTreeSet::new(),
            unsupported_integer_scope: false,
            refusal_observed: std::cell::Cell::new(false),
            integer_work_exhausted: false,
            changed: false,
            #[cfg(test)]
            visits: 0,
            #[cfg(test)]
            collector_visits: 0,
        };
        walker.integer_variables = Some(IntegerVariableRewrite {
            from,
            to,
            renamings,
        });
        walker.seed_fresh_allocator();
        walker.integer_work_exhausted |= crate::instrumentation::checked_collection_exhausted();
        walker
    }

    /// Reserve all IDs collected by the outer pure-proposition validation in
    /// one pass.  The ordinary term entry points collect their source terms
    /// lazily; checked pure substitution has already validated the complete
    /// proposition and must therefore avoid repeating that collection for
    /// every atomic leaf.
    pub(crate) fn reserve_integer_substitution_variables(
        &mut self,
        variables: &BTreeSet<Variable>,
    ) {
        if self.source_variables_reserved {
            return;
        }
        self.source_variables_reserved = true;
        self.charge_rewrite_work(1);
        if self.integer_work_exhausted {
            return;
        }
        // All collected IDs are reserved by starting the shared allocator
        // strictly above the maximum.  Keeping the complete source set in
        // `reserved_variables` would add an uncharged linear copy here and
        // would not change any allocation decision.
        // The greatest ordinary variable: the allocator mints ordinary
        // variables, and other origins sort after them.
        if let Some(last) = variables.range(..Variable::FIRST_NON_ORDINARY).next_back() {
            let Some(next) = last.0.checked_add(1) else {
                self.integer_work_exhausted = true;
                return;
            };
            self.fresh_next = self.fresh_next.max(next);
        }
    }

    /// Install an Integer binder mapping for a pure-proposition scope.  The
    /// map is carrier-specific, so a program-value binder with the same numeric ID cannot
    /// affect this scope.  Scope IDs invalidate the DAG cache whenever the
    /// visible mapping changes.
    pub(crate) fn push_integer_substitution_scope(
        &mut self,
        variable: Variable,
        mapped: Variable,
        integer_shadowed: bool,
    ) -> IntegerSubstitutionScope {
        let previous = self.scope.integer.insert(variable, mapped);
        let scope_id = self.scope_id;
        let previous_shadowed = self.integer_shadowed;
        if previous != Some(mapped) || previous_shadowed != integer_shadowed {
            self.bump_scope_id();
        }
        self.integer_shadowed = integer_shadowed;
        IntegerSubstitutionScope {
            variable,
            previous,
            scope_id,
            integer_shadowed: previous_shadowed,
        }
    }

    /// Restore a scope installed by `push_integer_substitution_scope`.
    pub(crate) fn pop_integer_substitution_scope(&mut self, scope: IntegerSubstitutionScope) {
        restore_mapping(&mut self.scope.integer, scope.variable, scope.previous);
        self.scope_id = scope.scope_id;
        self.integer_shadowed = scope.integer_shadowed;
    }

    /// Return whether the checked replacement contains a variable in the
    /// requested carrier.  The carrier summary follows registered load
    /// origins through their selected pointer expressions while keeping memory
    /// states opaque.  It is computed once and shared by all nested
    /// proposition binders.
    pub(crate) fn replacement_contains_integer_variable(&mut self, variable: Variable) -> bool {
        self.ensure_replacement_carriers();
        self.replacement_carriers
            .as_ref()
            .is_some_and(|replacement| replacement.integer.contains(&variable))
    }

    pub(crate) fn replacement_contains_program_variable(&mut self, variable: Variable) -> bool {
        self.ensure_replacement_carriers();
        self.replacement_carriers
            .as_ref()
            .is_some_and(|replacement| replacement.program_values.contains(&variable))
    }

    pub(crate) fn replacement_contains_algebraic_variable(&mut self, variable: Variable) -> bool {
        self.ensure_replacement_carriers();
        self.replacement_carriers
            .as_ref()
            .is_some_and(|replacement| replacement.algebraic.contains(&variable))
    }

    /// Install a C-carrier binder mapping without changing the Integer
    /// shadowing state.  The scope token restores only the previous C mapping
    /// and the cache scope ID.
    pub(crate) fn push_program_substitution_scope(
        &mut self,
        variable: Variable,
        mapped: Variable,
    ) -> ProgramValueSubstitutionScope {
        let previous = self.scope.program_values.insert(variable, mapped);
        let scope_id = self.scope_id;
        if previous != Some(mapped) {
            self.bump_scope_id();
        }
        ProgramValueSubstitutionScope {
            variable,
            previous,
            scope_id,
        }
    }

    pub(crate) fn pop_program_substitution_scope(&mut self, scope: ProgramValueSubstitutionScope) {
        restore_mapping(
            &mut self.scope.program_values,
            scope.variable,
            scope.previous,
        );
        self.scope_id = scope.scope_id;
    }

    pub(crate) fn push_algebraic_substitution_scope(
        &mut self,
        variable: Variable,
        mapped: Variable,
    ) -> AlgebraicSubstitutionScope {
        let previous = self.scope.algebraic.insert(variable, mapped);
        let scope_id = self.scope_id;
        if previous != Some(mapped) {
            self.bump_scope_id();
        }
        AlgebraicSubstitutionScope {
            variable,
            previous,
            scope_id,
        }
    }

    pub(crate) fn pop_algebraic_substitution_scope(&mut self, scope: AlgebraicSubstitutionScope) {
        restore_mapping(&mut self.scope.algebraic, scope.variable, scope.previous);
        self.scope_id = scope.scope_id;
    }

    /// Rewrites a constructor body with all field substitutions installed at
    /// once.  The replacement terms are inserted unchanged, so a field that
    /// mentions another binder is not rewritten by the later field mapping.
    pub(crate) fn for_typed_variables(
        program_values: &'a BTreeMap<Variable, TypedProgramValueReplacement>,
        integer: &'a BTreeMap<Variable, IntegerTerm>,
        algebraic: &'a BTreeMap<Variable, AlgebraicTerm>,
    ) -> Self {
        Self {
            comparison_arithmetic: false,
            comparison_reads: None,
            comparison_algebraic_reads: None,
            shared_machine_cache: None,
            algebraic: None,
            bitvector: None,
            integer_exact: None,
            pointer_variable: None,
            pointer_exact: None,
            pointer_value_exact: None,
            pointer_offset_exact: None,
            condition_exact: None,
            conditions: None,
            cited_conditions: None,
            cited_comparison_context: None,
            bounded_uint64_indices: None,
            pointer_association_conditions: None,
            equality_graph: None,
            pointer_context: None,
            pointer_addresses_only: false,
            collected_conditions: None,
            integer_cache: HashMap::new(),
            fold_integer_bridge: KernelTermExport::default(),
            pointer_application_cache: HashMap::new(),
            pointer_origin_cache: HashMap::new(),
            scope_renaming_max: 0,
            integer_body_summaries: Default::default(),
            integer_replacement_variables: None,
            bitvector_replacement_variables: None,
            integer_replacement_variable_max: None,
            bitvector_replacement_variable_max: None,
            integer_renaming_max: None,
            enforce_integer_work_limit: false,
            integer_variables: None,
            typed_variables: Some(TypedVariableReplacements {
                program_values,
                integer,
                algebraic,
            }),
            integer_shadowed: false,
            scope: RewriteScope::default(),
            scope_id: 0,
            next_scope_id: 1,
            source_disabled: false,
            source_variables_reserved: false,
            reserved_variables: BTreeSet::new(),
            fresh_next: 0,
            replacement_carriers: None,
            resolve_registered_loads: false,
            registered_load_cache: HashMap::new(),
            registered_load_pointer_active: BTreeSet::new(),
            unsupported_integer_scope: false,
            refusal_observed: std::cell::Cell::new(false),
            integer_work_exhausted: false,
            changed: false,
            #[cfg(test)]
            visits: 0,
            #[cfg(test)]
            collector_visits: 0,
        }
    }

    /// A narrowing conversion whose operand the cited conditions place in
    /// the destination range is that operand's carrier
    /// (`narrowed_cast_identity`), just as a conditional whose guard they
    /// decide is its arm. Each bound must be a cited condition, about the
    /// operand as written or as rewritten, or fold to true by itself; no
    /// other fact is consulted. `conditional_guards` reports the bounds so
    /// a search can cite them.
    /// The 32-bit word of `widen(conv(v))`, the widening into `int32` or
    /// `uint32` of a narrowing `conv` whose operand the conditions place
    /// inside its range: the operand's word (`narrowed_cast_identity`). A
    /// narrowing is a value of its own width; only its widening has a word.
    fn widened_narrowed_cast_carrier(
        &mut self,
        original: &OldMachineTerm,
        rewritten: &OldMachineTerm,
        source: crate::kernel::MachineIntegerType,
        destination: crate::kernel::MachineIntegerType,
    ) -> Option<OldMachineTerm> {
        if !crate::kernel::is_narrow_widening32(source, destination) {
            return None;
        }
        let (
            OldMachineTerm::Cast {
                spelling: MachineCastSpelling::Generic,
                value: original,
                from: original_source,
                to: original_destination,
            },
            OldMachineTerm::Cast {
                spelling: MachineCastSpelling::Generic,
                value: rewritten,
                from: rewritten_source,
                to: rewritten_destination,
            },
        ) = (original, rewritten)
        else {
            return None;
        };
        if original_source != rewritten_source
            || *original_destination != source
            || *rewritten_destination != source
        {
            return None;
        }
        self.narrowed_cast_carrier(original, rewritten, *rewritten_source, source)
    }

    fn narrowed_cast_carrier(
        &mut self,
        original: &OldMachineTerm,
        rewritten: &OldMachineTerm,
        source: crate::kernel::MachineIntegerType,
        destination: crate::kernel::MachineIntegerType,
    ) -> Option<OldMachineTerm> {
        let (bounds, carrier) =
            crate::kernel::assumptions::narrowed_cast_identity(rewritten, source, destination)?;
        if let Some(collected) = &mut self.collected_conditions {
            let (original_bounds, _) =
                crate::kernel::assumptions::narrowed_cast_identity(original, source, destination)?;
            collected.extend(
                original_bounds
                    .into_iter()
                    .flat_map(|bound| bound.conditions),
            );
            collected.extend(
                bounds
                    .iter()
                    .flat_map(|bound| bound.conditions.iter().cloned()),
            );
            return None;
        }
        let conditions = self.conditions?;
        let (original_bounds, _) =
            crate::kernel::assumptions::narrowed_cast_identity(original, source, destination)?;
        let holds = |condition: &OldConditionTerm| {
            crate::instrumentation::record_deterministic_work(1);
            conditions.get(condition) == Some(&true)
                || folded_machine_condition(condition.clone()) == OldConditionTerm::Constant(true)
        };
        bounds
            .iter()
            .zip(&original_bounds)
            .all(|(bound, original)| {
                bound
                    .conditions
                    .iter()
                    .chain(&original.conditions)
                    .any(holds)
            })
            .then_some(carrier)
    }

    pub(crate) fn conditional_guards(proposition: &Proposition) -> Vec<OldConditionTerm> {
        let empty = HashMap::new();
        let mut walker = TermRewrite::for_conditions(&empty);
        walker.collected_conditions = Some(Vec::new());
        walker.proposition(proposition);
        walker.collected_conditions.take().unwrap()
    }

    fn new_carrier_variables(&self) -> CarrierVariables {
        CarrierVariables::for_rewrite(
            self.integer_variables.is_some()
                || self.typed_variables.is_some()
                || self.enforce_integer_work_limit,
        )
    }

    fn checked_work_exhausted(&self) -> bool {
        self.integer_work_exhausted
    }

    fn seed_fresh_allocator(&mut self) {
        for variable in self
            .integer_replacement_variables
            .iter()
            .flat_map(|variables| variables.iter())
            .chain(
                self.bitvector_replacement_variables
                    .iter()
                    .flat_map(|variables| variables.iter()),
            )
        {
            self.reserved_variables.insert(*variable);
        }
        let upper = self
            .integer_replacement_variable_max
            .into_iter()
            .chain(self.bitvector_replacement_variable_max)
            .chain(self.integer_renaming_max)
            .max();
        if let Some(upper) = upper {
            self.fresh_next = self.fresh_next.max(upper.saturating_add(1));
        }
    }

    fn body_variable_max(&mut self, body: &KernelTerm) -> Option<u64> {
        let _collection_scope = crate::instrumentation::CheckedCollectionScope::new();
        let maximum = self.integer_body_summaries.maximum(body);
        if crate::instrumentation::checked_collection_exhausted() {
            self.integer_work_exhausted = true;
        }
        maximum
    }

    fn remove_fold_scope_mapping(
        &mut self,
        integer: bool,
        variable: Variable,
        changes: &mut Vec<FoldScopeChange>,
    ) {
        let previous = if integer {
            self.scope.integer.remove(&variable)
        } else {
            self.scope.program_values.remove(&variable)
        };
        changes.push(if integer {
            FoldScopeChange::Integer(variable, previous)
        } else {
            FoldScopeChange::Program(variable, previous)
        });
    }

    fn push_fold_scope_mapping(
        &mut self,
        integer: bool,
        from: Variable,
        to: Variable,
        changes: &mut Vec<FoldScopeChange>,
    ) {
        let previous = if integer {
            self.scope.integer.insert(from, to)
        } else {
            self.scope.program_values.insert(from, to)
        };
        changes.push(if integer {
            FoldScopeChange::Integer(from, previous)
        } else {
            FoldScopeChange::Program(from, previous)
        });
        self.scope_renaming_max = self.scope_renaming_max.max(to.0);
    }

    fn restore_fold_scope_mappings(&mut self, changes: &[FoldScopeChange]) {
        for change in changes.iter().rev() {
            match change {
                FoldScopeChange::Integer(variable, previous) => {
                    restore_mapping(&mut self.scope.integer, *variable, *previous);
                }
                FoldScopeChange::Program(variable, previous) => {
                    restore_mapping(&mut self.scope.program_values, *variable, *previous);
                }
            }
        }
    }

    fn reserve_source_variables(&mut self, variables: CarrierVariables) {
        if self.source_variables_reserved {
            return;
        }
        #[cfg(test)]
        {
            self.collector_visits = self.collector_visits.saturating_add(variables.nodes);
        }
        self.source_variables_reserved = true;
        self.integer_work_exhausted |= variables.work_exhausted;
        if self.integer_work_exhausted {
            return;
        }
        self.charge_rewrite_work(1);
        if self.integer_work_exhausted {
            return;
        }
        self.extend_reserved_variables(&variables);
    }

    fn extend_reserved_variables(&mut self, variables: &CarrierVariables) {
        for variable in variables
            .program_values
            .iter()
            .chain(variables.integer.iter())
            .chain(variables.algebraic.iter())
            .copied()
        {
            self.reserved_variables.insert(variable);
            if let Some(next) = variable.0.checked_add(1) {
                self.fresh_next = self.fresh_next.max(next);
            }
        }
    }

    fn reserve_terms_variables_once(&mut self, terms: &[&Term]) {
        if self.source_variables_reserved {
            return;
        }
        let mut variables = self.new_carrier_variables();
        let mut seen = BTreeSet::new();
        for term in terms {
            match term {
                Term::Condition(condition)
                    if matches!(
                        condition.root().map(KernelTerm::node),
                        Some(KernelTermNode::IntegerCompare { arguments, .. })
                            if arguments.iter().all(|root| self.can_rewrite_exact_observation(root))
                    ) => {}
                Term::Condition(condition) => {
                    collect_stored_condition_carriers(condition, &mut variables)
                }
                Term::Bitvector32(value) => {
                    collect_bitvector_carriers(value.old_form(), &mut variables)
                }
                // This exact rewrite does not enter binders or freshen names.
                Term::Integer(value)
                    if value
                        .root()
                        .is_some_and(|root| self.can_rewrite_exact_observation(root)) => {}
                Term::Integer(value) => {
                    if let Some(root) = value.root().filter(|root| root.is_mathematical_integer()) {
                        collect_mathematical_integer_carriers(root, &mut variables);
                    } else {
                        collect_integer_shared_carriers(
                            &SharedIntegerTerm::from(value.old_form().clone()),
                            &mut variables,
                            &mut seen,
                        );
                    }
                }
                Term::PointerOffset(offset) => {
                    let root = offset.root();
                    collect_retained_offset_carriers(root, &mut variables);
                }
                Term::ProgramValue(value) => {
                    collect_program_value_carriers(value.old_form(), &mut variables);
                }
                Term::Sequence(value) => collect_sequence_carriers(value, &mut variables),
                Term::Algebraic(value) => {
                    collect_algebraic_carriers_seen(value.old_form(), &mut variables, &mut seen)
                }
                Term::ArrayReadPoint(_) | Term::ExecutionState(_) => {}
            }
            if variables.exhausted() {
                break;
            }
        }
        self.reserve_source_variables(variables);
    }

    fn reserve_term_variables_once(&mut self, term: &Term) {
        self.reserve_terms_variables_once(std::slice::from_ref(&term));
    }

    fn reserve_integer_variables_once(&mut self, term: &IntegerTerm) {
        if self.source_variables_reserved {
            return;
        }
        let mut variables = self.new_carrier_variables();
        collect_integer_carriers(term, &mut variables, &mut BTreeSet::new());
        self.reserve_source_variables(variables);
    }

    fn reserve_bitvector_variables_once(&mut self, term: &OldMachineTerm) {
        if self.source_variables_reserved {
            return;
        }
        let mut variables = self.new_carrier_variables();
        collect_bitvector_carriers(term, &mut variables);
        self.reserve_source_variables(variables);
    }

    fn reserve_condition_variables_once(&mut self, condition: &OldConditionTerm) {
        if self.source_variables_reserved {
            return;
        }
        let mut variables = self.new_carrier_variables();
        collect_condition_carriers(condition, &mut variables);
        self.reserve_source_variables(variables);
    }

    fn reserve_resource_variables_once(&mut self, resources: &[&Resource]) {
        if self.source_variables_reserved {
            return;
        }
        let mut variables = self.new_carrier_variables();
        let mut seen = BTreeSet::new();
        for resource in resources {
            match resource {
                Resource::Memory(range) => {
                    collect_program_value_carriers(
                        &ProgramValue::Pointer(range.pointer_carrier()),
                        &mut variables,
                    );
                    collect_bitvector_carriers(range.bound_terms().0, &mut variables);
                    collect_bitvector_carriers(range.bound_terms().1, &mut variables);
                }
                Resource::Composite { arguments, .. } | Resource::Token { arguments, .. } => {
                    for argument in arguments.iter() {
                        collect_algebraic_value_carriers(argument, &mut variables, &mut seen);
                    }
                }
                _ => {}
            }
        }
        self.reserve_source_variables(variables);
    }

    fn resource(&mut self, resource: &Resource) -> Resource {
        self.visit();
        if self.checked_work_exhausted() {
            return resource.clone();
        }
        match resource {
            Resource::Star(pair) => Resource::star(self.resource(&pair.0), self.resource(&pair.1)),

            Resource::Memory(range) => {
                let carrier = range.pointer_carrier();
                let ProgramValue::Pointer(mut mapped) = self.value(&ProgramValue::Pointer(carrier))
                else {
                    unreachable!()
                };
                if let Some((from, to)) = self.pointer_value_exact
                    && !self.source_disabled
                    && range.provenance.as_ref() == from.provenance()
                    && range.carrier_owner().map(|owner| &**owner) == from.bounds_owner()
                    && range.carrier_known() == from.bounds_are_known()
                {
                    // The footprint already fixed its admitted byte bounds.
                    // A complete equality transports its retained carrier,
                    // including transitions between known and opaque bounds.
                    mapped = to.clone().with_address(mapped.address().clone());
                }
                let mut result = range
                    .with_bounds(
                        mapped.address().clone(),
                        self.bits(range.bound_terms().0),
                        self.bits(range.bound_terms().1),
                    )
                    .with_pointer_carrier(&mapped);
                result.typed_carrier = range.typed_carrier;
                Resource::Memory(result)
            }
            Resource::Composite { name, arguments } | Resource::Token { name, arguments } => {
                self.charge_rewrite_work(arguments.len());
                let arguments = arguments
                    .iter()
                    .map(|argument| self.field(argument))
                    .collect();
                if matches!(resource, Resource::Composite { .. }) {
                    Resource::Composite {
                        name: name.clone(),
                        arguments,
                    }
                } else {
                    Resource::Token {
                        name: name.clone(),
                        arguments,
                    }
                }
            }
            _ => {
                // Sealed identities and binder-bearing resource bodies need
                // their own operations; this atomic substitution does not enter them.
                if self.comparison_reads.is_none()
                    && (self.typed_variables.is_some() || self.integer_variables.is_some())
                {
                    self.integer_work_exhausted = true;
                }
                resource.clone()
            }
        }
    }

    /// Capture-avoiding substitution through an explicitly supplied proposition.
    /// One source reservation and replacement summary are shared by all leaves.
    pub(crate) fn substitute_proposition(&mut self, proposition: &Proposition) -> Proposition {
        self.ensure_replacement_carriers();
        let mut carriers = self.new_carrier_variables();
        collect_integer_substitution_variables_with_carriers(proposition, &mut carriers);
        self.reserve_source_variables(carriers);
        if self.refusal().is_some() {
            return exhausted_proposition();
        }
        // Reserve logical binders too, including unused binders: a fresh name
        // introduced for an outer capture must not collide with an inner one.
        let mut pending = vec![proposition];
        while let Some(proposition) = pending.pop() {
            self.visit();
            if self.refusal().is_some() {
                return exhausted_proposition();
            }
            match proposition {
                Proposition::ForAll { var, body, .. } | Proposition::Exists { var, body, .. } => {
                    self.reserved_variables.insert(**var);
                    pending.push(body);
                }
                Proposition::And(left, right)
                | Proposition::Or(left, right)
                | Proposition::Implies(left, right) => {
                    pending.extend([left.as_ref(), right.as_ref()])
                }
                Proposition::Not(body) => pending.push(body),
                _ => {}
            }
        }
        self.scoped_proposition(proposition)
    }

    // Atomic rewriting stays separate: only callers selecting the complete
    // proposition use this traversal through logical containers and binders.
    fn scoped_proposition(&mut self, proposition: &Proposition) -> Proposition {
        self.visit();
        match proposition {
            Proposition::And(left, right) => Proposition::And(
                Box::new(self.scoped_proposition(left)),
                Box::new(self.scoped_proposition(right)),
            ),
            Proposition::Or(left, right) => Proposition::Or(
                Box::new(self.scoped_proposition(left)),
                Box::new(self.scoped_proposition(right)),
            ),
            Proposition::Implies(left, right) => Proposition::Implies(
                Box::new(self.scoped_proposition(left)),
                Box::new(self.scoped_proposition(right)),
            ),
            Proposition::Not(body) => Proposition::Not(Box::new(self.scoped_proposition(body))),
            Proposition::Predicate { name, arguments } => Proposition::Predicate {
                name: name.clone(),
                arguments: arguments
                    .iter()
                    .map(|argument| self.term(argument))
                    .collect(),
            },
            Proposition::ForAll {
                name,
                var,
                sort,
                body,
            } => {
                let (var, body) = self.scoped_quantifier(*var, sort, body);
                Proposition::ForAll {
                    name: name.clone(),
                    var,
                    sort: sort.clone(),
                    body: Box::new(body),
                }
            }
            Proposition::Exists {
                name,
                var,
                sort,
                body,
            } => {
                let (var, body) = self.scoped_quantifier(*var, sort, body);
                Proposition::Exists {
                    name: name.clone(),
                    var,
                    sort: sort.clone(),
                    body: Box::new(body),
                }
            }
            _ => self.proposition(proposition),
        }
    }

    fn scoped_quantifier(
        &mut self,
        binder: QuantifierBinder,
        sort: &Sort,
        body: &Proposition,
    ) -> (QuantifierBinder, Proposition) {
        let variable = *binder;
        let carrier = match sort {
            Sort::Integer => Some(BindingCarrier::Integer),
            Sort::Algebraic(_) => Some(BindingCarrier::Algebraic),
            Sort::Bitvector32
            | Sort::ProgramInt32
            | Sort::ProgramInt64
            | Sort::ProgramInteger(_)
            | Sort::ProgramPointer(_)
            | Sort::ProgramObjectPointer(_, _)
            | Sort::Condition => Some(BindingCarrier::Program),
        };
        let Some(carrier) = carrier else {
            return (binder, self.scoped_proposition(body));
        };
        // A replacement mentions only taller quantifiers' variables, so it
        // never captures this binder, which is kept.
        debug_assert!(
            !self
                .replacement_carriers
                .as_ref()
                .is_some_and(|replacement| replacement.contains(carrier, variable)),
            "a replacement mentions the quantifier it is substituted under"
        );
        let scope_id = self.scope_id;
        let shadowed = self.integer_shadowed;
        let mut changes = Vec::new();
        self.push_binding_mapping(carrier, variable, variable, &mut changes);
        let body = self.scoped_proposition(body);
        self.restore_scope(&changes, scope_id, shadowed);
        (binder, body)
    }

    pub(crate) fn proposition(&mut self, proposition: &Proposition) -> Proposition {
        if self.checked_work_exhausted() {
            return exhausted_proposition();
        }
        if self.integer_variables.is_some()
            || self.typed_variables.is_some()
            || self.enforce_integer_work_limit
        {
            self.visit();
            if self.checked_work_exhausted() {
                return exhausted_proposition();
            }
        }
        match proposition {
            Proposition::VolatileAccess(event) => {
                if !self.source_variables_reserved {
                    let mut variables = self.new_carrier_variables();
                    collect_pointer_carriers(&event.pointer, &mut variables);
                    collect_program_value_carriers(event.value.old_form(), &mut variables);
                    self.reserve_source_variables(variables);
                }
                Proposition::VolatileAccess(std::sync::Arc::new(VolatileAccess {
                    pointer: self.pointer(&event.pointer),
                    value: self.value(event.value.old_form()).into(),
                    id: event.id,
                    kind: event.kind,
                    value_type: event.value_type,
                }))
            }
            Proposition::Equal(a, b) => {
                self.reserve_terms_variables_once(&[a, b]);
                if self.checked_work_exhausted() {
                    return exhausted_proposition();
                }
                let left = self.term(a);
                if self.checked_work_exhausted() {
                    return exhausted_proposition();
                }
                let right = self.term(b);
                if self.checked_work_exhausted() {
                    return exhausted_proposition();
                }
                Proposition::Equal(left, right)
            }
            Proposition::SequenceMembership { element, sequence } => {
                self.reserve_terms_variables_once(&[
                    &Term::ProgramValue(element.clone()),
                    &Term::Sequence(sequence.clone()),
                ]);
                if self.checked_work_exhausted() {
                    return exhausted_proposition();
                }
                Proposition::SequenceMembership {
                    element: self.rewrite_sequence_value(element.value()).into(),
                    sequence: sequence
                        .map_program_values(&mut |value| self.rewrite_sequence_value(value)),
                }
            }
            Proposition::ConditionIs(condition, value) => {
                if let Some(condition) = self.rewrite_stored_integer_comparison(condition) {
                    return Proposition::condition_is(condition, *value);
                }
                // A closed float predicate has no occurrence of the Integer
                // binder. Keep its arithmetic under structural substitution.
                if self.integer_variables.is_some()
                    && condition
                        .operand_view()
                        .closed_float_predicate_value()
                        .is_some()
                {
                    return proposition.clone();
                }
                self.reserve_condition_variables_once(condition.old_form());
                if self.checked_work_exhausted() {
                    return exhausted_proposition();
                }
                let condition = self.condition(condition.old_form());
                if self.checked_work_exhausted() {
                    return exhausted_proposition();
                }
                // Keep the truth polarity form used by ordinary lowering.
                // A rewrite can introduce an outer Bool negation.
                condition.truth_claim(*value)
            }
            Proposition::MemoryLoadable {
                memory,
                base,
                bytes,
                wide,
            } => {
                if !self.source_variables_reserved {
                    let mut variables = self.new_carrier_variables();
                    collect_pointer_carriers(base, &mut variables);
                    collect_bitvector_carriers(bytes.old_form(), &mut variables);
                    self.reserve_source_variables(variables);
                }
                let base = self.pointer(base);
                let bytes = self.bits(bytes.old_form());
                if self.checked_work_exhausted() {
                    return exhausted_proposition();
                }
                Proposition::MemoryLoadable {
                    memory: memory.clone(),
                    base,
                    bytes: crate::kernel::StoredMachineTerm::new(
                        if *wide {
                            crate::kernel::MachineIntegerType::UInt64
                        } else {
                            crate::kernel::MachineIntegerType::Int32
                        },
                        bytes,
                    ),
                    wide: *wide,
                }
            }
            Proposition::MemoryCanStore {
                memory,
                pointer,
                byte_width,
            } => {
                if !self.source_variables_reserved {
                    let mut variables = self.new_carrier_variables();
                    collect_pointer_carriers(pointer, &mut variables);
                    self.reserve_source_variables(variables);
                }
                let pointer = self.pointer(pointer);
                if self.checked_work_exhausted() {
                    return exhausted_proposition();
                }
                Proposition::MemoryCanStore {
                    memory: memory.clone(),
                    pointer,
                    byte_width: *byte_width,
                }
            }
            Proposition::MemoryReadDefined {
                at,
                memory,
                pointer,
                value_type,
            } => {
                if !self.source_variables_reserved {
                    let mut variables = self.new_carrier_variables();
                    collect_pointer_carriers(pointer, &mut variables);
                    self.reserve_source_variables(variables);
                }
                let pointer = self.pointer(pointer);
                if self.checked_work_exhausted() {
                    return exhausted_proposition();
                }
                Proposition::MemoryReadDefined {
                    at: *at,
                    memory: memory.clone(),
                    pointer,
                    value_type: *value_type,
                }
            }
            Proposition::ResourceSeparate { left, right } => {
                self.reserve_resource_variables_once(&[left, right]);
                Proposition::ResourceSeparate {
                    left: Box::new(self.resource(left)),
                    right: Box::new(self.resource(right)),
                }
            }
            Proposition::ResourceViewable { memory, resource } => {
                self.reserve_resource_variables_once(&[resource]);
                crate::kernel::resource_viewable(memory, self.resource(resource))
            }
            Proposition::ResourceContains { parent, child } => {
                self.reserve_resource_variables_once(&[parent, child]);
                Proposition::ResourceContains {
                    parent: Box::new(self.resource(parent)),
                    child: Box::new(self.resource(child)),
                }
            }
            Proposition::Not(p) => {
                let body = self.proposition(p);
                if self.checked_work_exhausted() {
                    exhausted_proposition()
                } else {
                    Proposition::Not(Box::new(body))
                }
            }
            // Comparison introduces no substitution or fresh variable, so it
            // preserves binder scopes while visiting each connective once.
            Proposition::And(left, right) if self.comparison_arithmetic => Proposition::And(
                Box::new(self.proposition(left)),
                Box::new(self.proposition(right)),
            ),
            Proposition::Or(left, right) if self.comparison_arithmetic => Proposition::Or(
                Box::new(self.proposition(left)),
                Box::new(self.proposition(right)),
            ),
            Proposition::Implies(left, right) if self.comparison_arithmetic => {
                Proposition::Implies(
                    Box::new(self.proposition(left)),
                    Box::new(self.proposition(right)),
                )
            }
            Proposition::ForAll {
                name,
                var,
                sort,
                body,
            } if self.comparison_arithmetic => Proposition::ForAll {
                name: name.clone(),
                var: *var,
                sort: sort.clone(),
                body: Box::new(self.proposition(body)),
            },
            Proposition::Exists {
                name,
                var,
                sort,
                body,
            } if self.comparison_arithmetic => Proposition::Exists {
                name: name.clone(),
                var: *var,
                sort: sort.clone(),
                body: Box::new(self.proposition(body)),
            },
            // Binder-bearing and compound propositions require their own explicit proof steps.
            _ => {
                if self.comparison_reads.is_none()
                    && (self.integer_variables.is_some()
                        || self.typed_variables.is_some()
                        || self.enforce_integer_work_limit)
                {
                    self.integer_work_exhausted = true;
                    exhausted_proposition()
                } else {
                    proposition.clone()
                }
            }
        }
    }
    fn visit(&mut self) {
        if self.integer_variables.is_some()
            || self.typed_variables.is_some()
            || self.enforce_integer_work_limit
        {
            self.integer_work_exhausted |= crate::instrumentation::deadline_exceeded_with_work(1);
        } else {
            crate::instrumentation::record_deterministic_work(1);
        }
        #[cfg(test)]
        {
            self.visits += 1;
        }
    }
    pub(crate) fn term(&mut self, term: &Term) -> Term {
        self.reserve_term_variables_once(term);
        if self.checked_work_exhausted() {
            return exhausted_term(term);
        }
        self.visit();
        if self.checked_work_exhausted() {
            return exhausted_term(term);
        }
        let result = match term {
            Term::Algebraic(v) => Term::Algebraic(self.algebraic(v.old_form()).into()),
            Term::Bitvector32(v) => Term::Bitvector32(v.map_native(|word| self.bits(word))),
            Term::Integer(v) => Term::Integer(self.stored_integer(v)),
            Term::ProgramValue(v) => Term::ProgramValue(self.value(v.old_form()).into()),
            Term::Condition(v) => Term::Condition(
                self.rewrite_stored_integer_comparison(v)
                    .unwrap_or_else(|| self.condition(v.old_form()).into()),
            ),
            Term::PointerOffset(v) => Term::PointerOffset(self.contract_offset(v)),
            Term::Sequence(v)
                if v.element_type
                    .is_none_or(crate::kernel::spec::retained_sequence_element_type) =>
            {
                Term::Sequence(
                    v.map_program_values(&mut |value| self.rewrite_sequence_value(value)),
                )
            }
            _ => term.clone(),
        };
        if self.checked_work_exhausted() {
            exhausted_term(term)
        } else {
            result
        }
    }
    fn rewrite_stored_integer_comparison(
        &mut self,
        condition: &StoredConditionTerm,
    ) -> Option<StoredConditionTerm> {
        let KernelTermNode::IntegerCompare {
            operator,
            arguments,
        } = condition.root()?.node()
        else {
            return None;
        };
        let mathematical = self.retained_mathematical_rewrite()
            && arguments.iter().all(KernelTerm::is_mathematical_integer);
        if !mathematical
            && !arguments
                .iter()
                .all(|root| self.can_rewrite_exact_observation(root))
        {
            return None;
        }
        if mathematical && !self.source_variables_reserved {
            let mut variables = self.new_carrier_variables();
            collect_stored_condition_carriers(condition, &mut variables);
            self.reserve_source_variables(variables);
        }
        self.visit();
        let rewritten = (|| {
            let left = self.rewrite_stored_integer_root(&arguments[0])?;
            let right = self.rewrite_stored_integer_root(&arguments[1])?;
            KernelTerm::integer_comparison(*operator, [left, right]).ok()
        })();
        match rewritten {
            Some(root) => StoredConditionTerm::from_root(root),
            None if self.refusal_status().is_some() => Some(condition.clone()),
            None => None,
        }
    }

    fn retained_mathematical_rewrite(&self) -> bool {
        self.integer_variables
            .as_ref()
            .is_some_and(|mapping| mapping.to.is_mathematical())
            || self.integer_exact.is_some_and(|(source, replacement)| {
                source.read_through_ref().mathematical_root().is_some()
                    && replacement.mathematical_root().is_some()
            })
    }

    fn stored_integer(&mut self, value: &StoredIntegerTerm) -> StoredIntegerTerm {
        if let Some(root) = value.root() {
            let mathematical =
                root.is_mathematical_integer() && self.retained_mathematical_rewrite();
            if mathematical && !self.source_variables_reserved {
                let mut variables = self.new_carrier_variables();
                collect_mathematical_integer_carriers(root, &mut variables);
                self.reserve_source_variables(variables);
            }
            if mathematical || self.can_rewrite_exact_observation(root) {
                if let Some(result) = self.rewrite_stored_integer_root(root) {
                    return StoredIntegerTerm::from_root(result).expect("Integer rewrite result");
                }
                if self.refusal_status().is_some() {
                    return IntegerTerm::constant_i64(0).into();
                }
            }
        }
        self.integer(value.old_form()).into()
    }

    fn rewrite_stored_integer_root(&mut self, root: &KernelTerm) -> Option<KernelTerm> {
        self.visit();
        self.shared_fold_integer_child(root)
    }

    fn rewrite_sequence_value(&mut self, value: &ExecutionValue) -> ExecutionValue {
        match value {
            ExecutionValue::Shared(root) => self
                .shared_machine_operand(root)
                .map(ExecutionValue::Shared)
                .unwrap_or_else(|| value.clone()),
            ExecutionValue::Native(value) => ExecutionValue::Native(self.value(value)),
        }
    }
    fn algebraic(&mut self, term: &AlgebraicTerm) -> AlgebraicTerm {
        if self.checked_work_exhausted() {
            return exhausted_algebraic(term);
        }
        self.visit();
        if self.checked_work_exhausted() {
            return exhausted_algebraic(term);
        }
        if let AlgebraicTermNode::Variable(variable) = &term.node
            && let Some(mapped) = self.scope.algebraic.get(variable)
        {
            let mut result = term.clone();
            result.node = AlgebraicTermNode::Variable(*mapped);
            return result;
        }
        if let AlgebraicTermNode::Variable(variable) = &term.node
            && let Some(replacements) = &self.typed_variables
            && let Some(replacement) = replacements.algebraic.get(variable)
        {
            self.changed = true;
            return replacement.clone();
        }
        if let Some((from, to)) = self.algebraic
            && !self.source_disabled
            && term == from
        {
            self.changed = true;
            return self.rewrite_algebraic_replacement(to);
        }
        if let AlgebraicTermNode::MemoryLoad {
            point: memory,
            pointer,
        } = &term.node
            && let Some(reads) = self.comparison_algebraic_reads
            && let Some(replacement) = reads.get(&(memory.clone(), pointer.as_ref().clone()))
        {
            self.changed = true;
            return replacement.clone();
        }
        let node = match &term.node {
            AlgebraicTermNode::Variable(v) => AlgebraicTermNode::Variable(*v),
            AlgebraicTermNode::MemoryLoad { point, pointer } if point.is_entry_read() => {
                let pointer = self.pointer(pointer);
                if pointer.base == AddressBase::ExternalArgument {
                    AlgebraicTermNode::MemoryLoad {
                        point: point.clone(),
                        pointer: Box::new(pointer),
                    }
                } else {
                    AlgebraicTermNode::MemoryLoad {
                        point: crate::kernel::ProgramPoint::walked(
                            &crate::kernel::memory_history::canonical_value_load_memory(
                                point.shared_memory(),
                                &pointer,
                                crate::kernel::AccessExtent::of_algebraic(&term.algebraic_type),
                            ),
                            point,
                        ),
                        pointer: Box::new(pointer),
                    }
                }
            }
            AlgebraicTermNode::MemoryLoad {
                point: memory,
                pointer,
            } => {
                let carrier = AlgebraicTermNode::memory_load_carrier_value(
                    memory,
                    pointer,
                    &term.algebraic_type,
                );
                match self.field(&carrier) {
                    AlgebraicValue::Program(value) => {
                        let rewritten = AlgebraicTermNode::memory_load_from_carrier(&value)
                            .unwrap_or_else(|| term.node.clone());
                        match rewritten {
                            AlgebraicTermNode::MemoryLoad {
                                point: moved_memory,
                                pointer: moved_pointer,
                            } if moved_memory == *memory && moved_pointer != *pointer => {
                                // A projection names the original selected cell.
                                // Moving the read names the substituted cell at
                                // its recorded observation, as lowering does.
                                let extent =
                                    crate::kernel::AccessExtent::of_algebraic(&term.algebraic_type);
                                let origin = crate::kernel::prelude::value_load_origin(
                                    memory.shared_memory(),
                                    pointer,
                                    extent,
                                )
                                .unwrap_or_else(|| memory.shared_memory().clone());
                                AlgebraicTermNode::MemoryLoad {
                                    point: crate::kernel::ProgramPoint::walked(
                                        &crate::kernel::memory_history::canonical_value_load_memory(
                                            &origin,
                                            &moved_pointer,
                                            extent,
                                        ),
                                        memory,
                                    ),
                                    pointer: moved_pointer,
                                }
                            }
                            other => other,
                        }
                    }
                    _ => term.node.clone(),
                }
            }
            AlgebraicTermNode::Constructor { variant, fields } => {
                let mut rewritten = Vec::with_capacity(fields.len());
                for field in fields {
                    rewritten.push(self.field(field));
                    if self.checked_work_exhausted() {
                        return exhausted_algebraic(term);
                    }
                }
                AlgebraicTermNode::Constructor {
                    variant: variant.clone(),
                    fields: rewritten,
                }
            }
            AlgebraicTermNode::PureFunctionApplication { name, arguments } => {
                let mut rewritten = Vec::with_capacity(arguments.len());
                for argument in arguments {
                    rewritten.push(self.argument(argument));
                    if self.checked_work_exhausted() {
                        return exhausted_algebraic(term);
                    }
                }
                AlgebraicTermNode::PureFunctionApplication {
                    name: name.clone(),
                    arguments: rewritten,
                }
            }
            AlgebraicTermNode::Match { scrutinee, arms } => {
                self.reserve_algebraic_match_variables(term, scrutinee, arms);
                if self.checked_work_exhausted() {
                    return exhausted_algebraic(term);
                }
                let scrutinee = self.algebraic(scrutinee);
                if self.checked_work_exhausted() {
                    return exhausted_algebraic(term);
                }
                let mut rewritten_arms = Vec::with_capacity(arms.len());
                for arm in arms {
                    let saved_scope_id = self.scope_id;
                    let saved_shadowed = self.integer_shadowed;
                    let mut changes = Vec::new();
                    let mut bindings = arm.bindings.clone();
                    if !self.rewrite_match_bindings(&mut bindings, &mut changes) {
                        self.restore_scope(&changes, saved_scope_id, saved_shadowed);
                        self.integer_work_exhausted = true;
                        return exhausted_algebraic(term);
                    }
                    let body = if self.conditions.is_some() {
                        arm.body.clone()
                    } else {
                        self.algebraic(&arm.body)
                    };
                    self.restore_scope(&changes, saved_scope_id, saved_shadowed);
                    if self.checked_work_exhausted() {
                        return exhausted_algebraic(term);
                    }
                    rewritten_arms.push(AlgebraicResultMatchArm {
                        binding_names: arm.binding_names.clone(),
                        variant: arm.variant.clone(),
                        bindings,
                        body,
                    });
                }
                // A checked constructor determines the arm without proof search.
                // Validate the whole match before discarding its other arms.
                if (!self.preserves_algebraic_matches() || term.algebraic_type.rigid)
                    && matches!(scrutinee.node, AlgebraicTermNode::Constructor { .. })
                    && term.is_well_formed()
                    && let Some(value) =
                        self.rewrite_algebraic_match_iota(&scrutinee, &rewritten_arms)
                {
                    return value;
                }
                AlgebraicTermNode::Match {
                    scrutinee: Box::new(scrutinee),
                    arms: rewritten_arms,
                }
            }
            AlgebraicTermNode::If {
                condition,
                then_term,
                else_term,
            } => {
                // As a scalar conditional: a rewrite that decides the
                // condition leaves the arm it selects.
                if let Some(conditions) = &mut self.collected_conditions {
                    conditions.push(condition.as_ref().clone());
                }
                let preserve = self.integer_exact.is_some()
                    || self.preserves_closed_value_conditional(condition);
                let condition = self.condition(condition);
                let condition = if preserve {
                    condition
                } else {
                    folded_machine_condition(condition)
                };
                if self.checked_work_exhausted() {
                    return exhausted_algebraic(term);
                }
                if !preserve && let OldConditionTerm::Constant(value) = condition {
                    return self.algebraic(if value { then_term } else { else_term });
                }
                let then_term = self.algebraic(then_term);
                let else_term = self.algebraic(else_term);
                if self.checked_work_exhausted() {
                    return exhausted_algebraic(term);
                }
                AlgebraicTermNode::If {
                    condition: Box::new(condition),
                    then_term: Box::new(then_term),
                    else_term: Box::new(else_term),
                }
            }
        };
        AlgebraicTerm {
            algebraic_type: term.algebraic_type.clone(),
            node,
        }
    }

    /// A replacement is an expression from the enclosing lexical scope.  It
    /// is inserted as-is: applying the current arm's renamings to it would
    /// capture a free variable in the replacement.
    fn rewrite_algebraic_replacement(&mut self, replacement: &AlgebraicTerm) -> AlgebraicTerm {
        replacement.clone()
    }
    fn field<'field>(&mut self, v: impl Into<ResourceFieldValue<'field>>) -> AlgebraicValue {
        let v = v.into();
        if self.checked_work_exhausted() {
            return match v {
                ResourceFieldValue::Program(value) => {
                    AlgebraicValue::Program(exhausted_program_value(value))
                }
                ResourceFieldValue::Integer(value) => {
                    AlgebraicValue::Integer(exhausted_integer(value))
                }
                ResourceFieldValue::Algebraic(value) => {
                    AlgebraicValue::Algebraic(exhausted_algebraic(value))
                }
            };
        }
        match v {
            ResourceFieldValue::Program(v) => AlgebraicValue::Program(self.value(v)),
            ResourceFieldValue::Integer(v) => AlgebraicValue::Integer(self.integer(v)),
            ResourceFieldValue::Algebraic(v) => AlgebraicValue::Algebraic(self.algebraic(v)),
        }
    }
    fn argument(&mut self, a: &PureFunctionArgument) -> PureFunctionArgument {
        if self.checked_work_exhausted() {
            return exhausted_argument(a);
        }
        let result = match a {
            PureFunctionArgument::Value(v) => PureFunctionArgument::Value(self.value(v)),
            PureFunctionArgument::SharedMachine(v) => {
                PureFunctionArgument::SharedMachine(self.index_bits(v))
            }
            PureFunctionArgument::Integer(v) => {
                PureFunctionArgument::Integer(self.integer_shared(v).into())
            }
            PureFunctionArgument::Algebraic(v) => {
                PureFunctionArgument::Algebraic(self.algebraic(v))
            }
            PureFunctionArgument::ArrayRef {
                point,
                pointer,
                element_type,
            } => PureFunctionArgument::ArrayRef {
                // A captured memory state is an opaque proof-state value.
                // Rewrite only the explicit pointer argument; scanning or
                // rebuilding the state would make substitution depend on
                // unrelated heap size.
                point: point.clone(),
                pointer: self.value(pointer),
                element_type: *element_type,
            },
        };
        if self.checked_work_exhausted() {
            exhausted_argument(a)
        } else {
            result
        }
    }
    fn value(&mut self, v: &ProgramValue) -> ProgramValue {
        if self.checked_work_exhausted() {
            return exhausted_program_value(v);
        }
        let result = match v {
            ProgramValue::PointerInteger(record) => {
                let ProgramValue::Pointer(pointer) =
                    self.value(&ProgramValue::Pointer(*record.pointer.clone()))
                else {
                    unreachable!()
                };
                ProgramValue::PointerInteger(PointerIntegerValue {
                    kind: record.kind.clone(),
                    numeric: Box::new(self.value(&record.numeric)),
                    pointer: Box::new(pointer),
                })
            }
            ProgramValue::Parameter(term) => {
                ProgramValue::Parameter(Box::new(self.algebraic(term)))
            }
            ProgramValue::Void => ProgramValue::Void,
            ProgramValue::Bool(v) => ProgramValue::Bool(self.bits(v)),
            ProgramValue::Int8(v) => ProgramValue::Int8(self.bits(v)),
            ProgramValue::Int16(v) => ProgramValue::Int16(self.bits(v)),
            ProgramValue::UInt16(v) => ProgramValue::UInt16(self.bits(v)),
            ProgramValue::UInt8(v) => ProgramValue::UInt8(self.bits(v)),
            ProgramValue::Int32(v) => ProgramValue::Int32(self.bits(v)),
            ProgramValue::UInt32(v) => ProgramValue::UInt32(self.bits(v)),
            ProgramValue::Int64(v) => ProgramValue::Int64(self.bits(v)),
            ProgramValue::UInt64(v) => ProgramValue::UInt64(self.bits(v)),
            ProgramValue::Int128(v) => ProgramValue::Int128(self.bits(v)),
            ProgramValue::UInt128(v) => ProgramValue::UInt128(self.bits(v)),
            ProgramValue::Float32(v) => ProgramValue::Float32(self.bits(v)),
            ProgramValue::Float64(v) => ProgramValue::Float64(self.bits(v)),
            ProgramValue::Pointer(v) => {
                if let Some((from, to)) = self.pointer_value_exact
                    && v == from
                    && !self.source_disabled
                {
                    self.changed = true;
                    // Pointer equality ignores the type, which belongs to the
                    // term: the replacement keeps this occurrence's type, and
                    // the designated object's checked type. The cited
                    // equality's spelling need not carry the evidence retained
                    // by this occurrence (for example, a typed constructor
                    // field).
                    return ProgramValue::Pointer(
                        to.clone()
                            .with_type(v.program_type())
                            .with_object_type_evidence(v.object_type_evidence().cloned()),
                    );
                }
                let shifted_source = self.pointer_value_exact.filter(|(from, to)| {
                    !self.source_disabled
                        && v.address() != from.address()
                        && v.address().base == from.address().base
                        && ((matches!(from.address().base, AddressBase::Symbolic(_))
                            && matches!(from.address().offset.view(), OffsetView::Constant(0)))
                            || (from.address().base == AddressBase::ExternalArgument
                                && to.address().base == AddressBase::ExternalArgument))
                });
                let shifted_replacement = shifted_source.and_then(|(from, to)| {
                    (v.provenance() == from.provenance()
                        && v.bounds() == from.bounds()
                        && v.bounds_are_known() == from.bounds_are_known()
                        && v.bounds_owner() == from.bounds_owner())
                    .then(|| to.clone())
                });
                let retain_view = shifted_source.is_some() && shifted_replacement.is_none();
                let replacement = shifted_replacement.or_else(|| match &v.address().base {
                    AddressBase::Symbolic(variable) | AddressBase::FunctionSymbolic(variable) => {
                        (!self.scope.program_values.contains_key(variable))
                            .then_some(())
                            .and(self.typed_variables.as_ref())
                            .and_then(|values| values.program_values.get(variable))
                            .and_then(|value| match value {
                                TypedProgramValueReplacement::Pointer(pointer) => Some(pointer.clone()),
                                _ => None,
                            })
                    }
                    _ => None,
                }.or_else(|| {
                    let (from, to) = self.pointer_variable?;
                    if self.pointer_addresses_only || self.scope.program_values.contains_key(&from)
                        || !matches!(v.address().base, AddressBase::Symbolic(variable) | AddressBase::FunctionSymbolic(variable) if variable == from)
                        || v.provenance() != &v.address().object_identity()
                    {
                        return None;
                    }
                    // Lexical substitution replaces a complete formal value.
                    // Address-equality rewrites use a separate constructor.
                    Some(OldPointer::new(to.clone(), v.program_type()))
                }));
                let adopted = if !v.bounds_are_known() {
                    replacement.as_ref().and_then(|p| p.bounds().cloned())
                } else {
                    None
                };
                let addresses_only = self.pointer_addresses_only
                    || (self.pointer_exact.is_some() && self.pointer_value_exact.is_none());
                let provenance = if addresses_only {
                    v.provenance().clone()
                } else if let Some(replacement) = &replacement {
                    replacement.provenance().clone()
                } else if let Some((from, to)) = self.pointer_variable
                    && !self.scope.program_values.contains_key(&from)
                    && matches!(v.provenance().base, AddressBase::Symbolic(variable) | AddressBase::FunctionSymbolic(variable) if variable == from)
                {
                    to.object_identity()
                } else if let Some((from, to)) = self.pointer_value_exact
                    && !self.source_disabled
                    && v.provenance() == from.provenance()
                {
                    to.provenance().clone()
                } else if self.pointer_exact.is_some() && self.pointer_value_exact.is_none() {
                    v.provenance().clone()
                } else {
                    self.pointer(v.provenance())
                };
                let bounds_owner = match v.bounds_owner() {
                    None => None,
                    Some(origin) => {
                        if addresses_only {
                            Some(std::sync::Arc::new(origin.clone()))
                        } else if replacement.is_some() && origin == &v.address().object_identity()
                        {
                            replacement
                                .as_ref()
                                .and_then(|p| p.bounds_owner().cloned())
                                .map(std::sync::Arc::new)
                        } else if let Some((from, to)) = self.pointer_variable
                            && !self.scope.program_values.contains_key(&from)
                            && matches!(origin.base, AddressBase::Symbolic(variable) | AddressBase::FunctionSymbolic(variable) if variable == from)
                        {
                            Some(std::sync::Arc::new(to.object_identity()))
                        } else if let Some((from, to)) = self.pointer_value_exact
                            && !self.source_disabled
                            && !from.bounds_are_known()
                            && from.bounds_owner() == Some(origin)
                        {
                            to.bounds_owner().cloned().map(std::sync::Arc::new)
                        } else if self.pointer_exact.is_some() && self.pointer_value_exact.is_none()
                        {
                            Some(std::sync::Arc::new(origin.clone()))
                        } else {
                            Some(std::sync::Arc::new(self.pointer(origin)))
                        }
                    }
                };
                let previous_load_resolution = self.resolve_registered_loads;
                if self.pointer_value_exact.is_some() {
                    self.resolve_registered_loads = true;
                }
                let mut mapped = v
                    .map_pointers(|address| self.pointer(address))
                    .with_provenance(std::sync::Arc::new(provenance))
                    .with_bounds_owner(bounds_owner);
                if retain_view && let Some((from, _)) = shifted_source {
                    // The numeric consequence cannot identify the base's own
                    // domain with a different view's domain. Nested reads still
                    // substitute their arguments through the equality.
                    if v.provenance() != from.provenance()
                        && v.provenance().base == from.address().base
                    {
                        mapped =
                            mapped.with_provenance(std::sync::Arc::new(v.provenance().clone()));
                    }
                    if (from.bounds_are_known() || v.bounds_owner() != from.bounds_owner())
                        && v.bounds_owner()
                            .is_some_and(|origin| origin.base == from.address().base)
                    {
                        mapped = mapped
                            .with_bounds_owner(v.bounds_owner().cloned().map(std::sync::Arc::new));
                    }
                }
                self.resolve_registered_loads = previous_load_resolution;
                ProgramValue::Pointer(match adopted {
                    Some(bounds) => mapped.with_bounds(Some(bounds)),
                    None if !v.bounds_are_known()
                        && replacement.as_ref().is_some_and(|p| p.bounds_are_known()) =>
                    {
                        mapped.with_root_bounds()
                    }
                    None => mapped,
                })
            }
        };
        if self.checked_work_exhausted() {
            exhausted_program_value(v)
        } else {
            result
        }
    }
    pub(crate) fn integer(&mut self, v: &IntegerTerm) -> IntegerTerm {
        self.integer_with_match_retention(v, false)
    }

    fn integer_with_match_retention(&mut self, v: &IntegerTerm, retain_match: bool) -> IntegerTerm {
        self.reserve_integer_variables_once(v);
        if self.checked_work_exhausted() {
            return exhausted_integer(v);
        }
        self.visit();
        if self.checked_work_exhausted() {
            return exhausted_integer(v);
        }
        self.integer_shared_with_match_retention(
            &SharedIntegerTerm::from(v.clone()),
            Some(v),
            retain_match,
        )
    }

    fn integer_shared(&mut self, shared: &SharedIntegerTerm) -> IntegerTerm {
        self.integer_shared_with_match_retention(
            shared,
            None,
            MATCH_REDUCTION_SUSPENDED.with(std::cell::Cell::get),
        )
    }

    fn integer_shared_with_match_retention(
        &mut self,
        shared: &SharedIntegerTerm,
        native_input: Option<&IntegerTerm>,
        retain_match: bool,
    ) -> IntegerTerm {
        let input = || native_input.unwrap_or_else(|| shared.as_ref());
        if self.checked_work_exhausted() {
            return exhausted_integer(input());
        }
        let retain_match = retain_match && matches!(shared.root().node(), KernelTermNode::Match(_));
        let cache_key = (
            shared.id(),
            self.scope_key(),
            self.resolve_registered_loads,
            retain_match,
        );
        if let Some(result) = self.integer_cache.get(&cache_key) {
            return result.clone();
        }
        self.visit();
        if self.checked_work_exhausted() {
            return exhausted_integer(input());
        }
        // An occurrence is matched up to its observations' value relations
        // (rule W): `to_integer(count as uint32 as int32)` occurs in a goal
        // that reads the same word through σ. Both readings are cached.
        if let Some((from, to)) = self.integer_exact
            && (shared == from || shared.read_through_ref() == from.read_through_ref())
        {
            let work = match to.as_ref() {
                IntegerTerm::Constant(value) => value.bits() as usize + 1,
                _ => 1,
            };
            self.charge_rewrite_work(work);
            if self.checked_work_exhausted() {
                return exhausted_integer(input());
            }
            self.changed = true;
            // Do not recursively rewrite the replacement. Matching uses
            // interned DAG identities; literal retention was charged above.
            let result = to.as_ref().clone();
            self.integer_cache.insert(cache_key, result.clone());
            return result;
        }
        let result = match input() {
            IntegerTerm::Constant(value) => {
                if self.integer_variables.is_some()
                    || self.typed_variables.is_some()
                    || self.enforce_integer_work_limit
                {
                    self.integer_work_exhausted |=
                        crate::instrumentation::deadline_exceeded_with_work(
                            value.bits() as usize + 1,
                        );
                    if self.integer_work_exhausted {
                        return exhausted_integer(input());
                    }
                }
                input().clone()
            }
            IntegerTerm::Variable(variable) => self.rewrite_integer_variable(*variable),
            IntegerTerm::PureFunctionApplication(application) => {
                let mut arguments = Vec::with_capacity(application.arguments().len());
                for argument in application.arguments() {
                    arguments.push(self.argument(argument));
                    if self.checked_work_exhausted() {
                        return exhausted_integer(input());
                    }
                }
                IntegerTerm::PureFunctionApplication(SharedPureApplication::intern(
                    application.name().to_string(),
                    arguments,
                ))
            }
            IntegerTerm::Machine(value) => {
                // Every rewrite mode retains the shared arithmetic traversal;
                // conditional reductions consult only their selected guards.
                if let Some(root) = value.shared_operand()
                    && let Some(result) = self.shared_machine_operand(root)
                {
                    let changed = result != *root;
                    let operand = MachineOperandView::Shared(&result);
                    // A substituted carrier need not admit the observation's
                    // numeric reading (for example a full-width unsigned
                    // literal in a signed conversion). Preserve that typed
                    // machine observation, as the native path below does.
                    let result = if self.integer_exact.is_some() {
                        IntegerTerm::Machine(operand.retain(value.ty()))
                    } else {
                        operand
                            .observe(value.ty())
                            .unwrap_or_else(|| IntegerTerm::Machine(operand.retain(value.ty())))
                    };
                    // A changed observation must use the same numeric opaque
                    // keys as freshly lowered syntax. A no-op keeps its exact
                    // retained handle, including producer metadata.
                    let result = match result {
                        IntegerTerm::Machine(machine) if changed => {
                            if let Some(root) = machine.shared_operand() {
                                IntegerTerm::Machine(
                                    SharedMachineIntegerTerm::observe_shared(
                                        machine.ty(),
                                        root.clone(),
                                    )
                                    .expect("rewritten machine observation"),
                                )
                            } else {
                                IntegerTerm::Machine(machine)
                            }
                        }
                        result => result,
                    };
                    self.integer_cache.insert(cache_key, result.clone());
                    return result;
                }
                if self.refusal().is_some() {
                    return exhausted_integer(input());
                }
                let bits = self.bits(value.value());
                if self.checked_work_exhausted() {
                    return exhausted_integer(input());
                }
                // The mathematical observation of a machine *constant* is that
                // constant: `from_machine` folds it and keeps the carrier
                // whenever the bits are still symbolic. Without this, a rewrite
                // that resolves the observed machine term to a literal leaves
                // `to_integer(1)` beside the `1` a reader wrote, and the two
                // are the same Integer. This folds one already-decided
                // observation, never a symbolic expression.
                if self.integer_exact.is_some() {
                    // Preserve the observation's carrier and cast syntax even
                    // when an explicit Integer payload was substituted.
                    IntegerTerm::Machine(crate::kernel::SharedMachineIntegerTerm::intern(
                        value.ty(),
                        bits,
                    ))
                } else {
                    IntegerTerm::from_machine(value.ty(), bits.clone()).unwrap_or_else(|| {
                        IntegerTerm::Machine(crate::kernel::SharedMachineIntegerTerm::intern(
                            value.ty(),
                            bits,
                        ))
                    })
                }
            }
            // Rewriting preserves the symbolic DAG. In particular, it must
            // not fold a repeated symbolic expression into a giant literal.
            IntegerTerm::Negate(value) => IntegerTerm::Negate(self.integer_shared(value).into()),
            IntegerTerm::Add(left, right) => IntegerTerm::Add(
                self.integer_shared(left).into(),
                self.integer_shared(right).into(),
            ),
            IntegerTerm::Subtract(left, right) => IntegerTerm::Subtract(
                self.integer_shared(left).into(),
                self.integer_shared(right).into(),
            ),
            IntegerTerm::Multiply(left, right) => IntegerTerm::Multiply(
                self.integer_shared(left).into(),
                self.integer_shared(right).into(),
            ),
            IntegerTerm::TruncatingQuotient(left, right) => IntegerTerm::TruncatingQuotient(
                self.integer_shared(left).into(),
                self.integer_shared(right).into(),
            ),
            IntegerTerm::TruncatingRemainder(left, right) => IntegerTerm::TruncatingRemainder(
                self.integer_shared(left).into(),
                self.integer_shared(right).into(),
            ),
            IntegerTerm::RangeFold { .. } => {
                let root = KernelTermImport::default().integer(shared);
                let KernelTermNode::Fold(fold) = root.node() else {
                    unreachable!("migrated Integer fold");
                };
                match self.retained_fold_in(fold) {
                    Ok(fold) => fold
                        .integer_compatibility(&mut self.fold_integer_bridge)
                        .expect("rewritten Integer fold"),
                    Err(_) => IntegerTerm::constant_i64(0),
                }
            }
            IntegerTerm::AlgebraicMatch { .. } => {
                let root = KernelTermImport::default().integer(shared);
                let KernelTermNode::Match(matched) = root.node() else {
                    unreachable!("Integer match")
                };
                match self.rewrite_retained_match_value_in(matched, retain_match) {
                    Some(root) => self
                        .fold_integer_bridge
                        .integer(&root)
                        .expect("Integer match reading")
                        .as_ref()
                        .clone(),
                    None => IntegerTerm::constant_i64(0),
                }
            }
            IntegerTerm::If {
                condition,
                then_term,
                else_term,
            } => {
                // As a machine conditional: a rewrite that decides the
                // condition leaves the arm it selects, and arms the rewrite
                // made equal decide nothing either.
                if let Some(conditions) = &mut self.collected_conditions {
                    conditions.push(condition.as_ref().clone());
                }
                let keep_closed = self.preserves_closed_value_conditional(condition);
                let preserve = self.integer_exact.is_some() || keep_closed;
                let condition = self.condition(condition);
                let condition = if preserve {
                    condition
                } else {
                    folded_machine_condition(condition)
                };
                if self.checked_work_exhausted() {
                    return exhausted_integer(input());
                }
                if !preserve && let OldConditionTerm::Constant(value) = condition {
                    let result = self.integer_shared(if value { then_term } else { else_term });
                    if self.checked_work_exhausted() {
                        return exhausted_integer(input());
                    }
                    self.integer_cache.insert(cache_key, result.clone());
                    return result;
                }
                let then_term = self.integer_shared(then_term);
                let else_term = self.integer_shared(else_term);
                // Arms the rewrite made equal are one term in either mode:
                // like dropping a rewritten `+ 0` above, it only deletes a
                // node, and keeping it would leave `if c { y } else { y }`
                // beside the `y` every producer builds.
                if !keep_closed && (!preserve || then_term == else_term) {
                    IntegerTerm::if_then_else(condition, then_term, else_term)
                } else {
                    IntegerTerm::If {
                        condition: Box::new(condition),
                        then_term: then_term.into(),
                        else_term: else_term.into(),
                    }
                }
            }
        };
        if self.checked_work_exhausted() {
            return exhausted_integer(input());
        }
        self.integer_cache.insert(cache_key, result.clone());
        result
    }

    fn retained_integer_fold(&mut self, fold: &KernelFold) -> Option<KernelFold> {
        let original_accumulator = fold.accumulator;
        let original_item = fold.item;
        if self.integer_exact.is_some()
            || self.pointer_exact.is_some()
            || self.pointer_offset_exact.is_some()
        {
            self.unsupported_integer_scope = true;
            return None;
        }
        let item_is_integer = fold.index == KernelFoldIndex::Integer;
        if !item_is_integer && self.has_composite_bitvector_source() {
            // A composite source can contain variables whose binding status
            // changes under this C-item binder.  Refuse that scope until a
            // carrier-aware source summary is available; plain variable
            // sources remain fully supported.
            self.unsupported_integer_scope = true;
            return None;
        }
        let integer_source = self.integer_variables.as_ref().map(|mapping| mapping.from);
        let c_source = self
            .bitvector
            .and_then(|(from, _)| from.variable().copied());

        if self.bitvector.is_some() && self.bitvector_replacement_variables.is_none() {
            self.ensure_replacement_carriers();
            if let Some(variables) = &self.replacement_carriers {
                self.integer_replacement_variable_max = variables
                    .integer
                    .range(..Variable::FIRST_NON_ORDINARY)
                    .next_back()
                    .map(|v| v.0);
                self.bitvector_replacement_variable_max = variables
                    .program_values
                    .range(..Variable::FIRST_NON_ORDINARY)
                    .next_back()
                    .map(|v| v.0);
                self.integer_replacement_variables = Some(variables.integer.clone());
                self.bitvector_replacement_variables = Some(variables.program_values.clone());
            }
        }

        // Typed substitutions use the same carrier-aware replacement summary
        // as algebraic matches.  In particular, a C variable with the same
        // numeric ID as an Integer variable must not affect this decision.
        if self.typed_variables.is_some() {
            self.ensure_replacement_carriers();
        }
        if self.checked_work_exhausted() {
            return None;
        }
        let integer_replacement_contains = self
            .integer_replacement_variables
            .as_ref()
            .is_some_and(|variables| variables.contains(&original_accumulator));
        let c_replacement_contains = self
            .bitvector_replacement_variables
            .as_ref()
            .is_some_and(|variables| variables.contains(&original_item));
        let typed_integer_replacement_contains = self
            .replacement_carriers
            .as_ref()
            .is_some_and(|variables| variables.integer.contains(&original_accumulator));
        let typed_integer_item_replacement_contains = self
            .replacement_carriers
            .as_ref()
            .is_some_and(|variables| variables.integer.contains(&original_item));
        let typed_c_replacement_contains = self
            .replacement_carriers
            .as_ref()
            .is_some_and(|variables| variables.program_values.contains(&original_item));

        let integer_source_key = self
            .typed_variables
            .as_ref()
            .is_some_and(|replacements| replacements.integer.contains_key(&original_accumulator));
        let integer_item_source_key = self
            .typed_variables
            .as_ref()
            .is_some_and(|replacements| replacements.integer.contains_key(&original_item));
        let c_item_source_key = self
            .typed_variables
            .as_ref()
            .is_some_and(|replacements| replacements.program_values.contains_key(&original_item));
        let accumulator_blocks_source = self.integer_shadowed
            || integer_source == Some(original_accumulator)
            || integer_source_key;
        let item_blocks_source = if item_is_integer {
            self.integer_shadowed
                || integer_source == Some(original_item)
                || integer_item_source_key
        } else {
            c_source == Some(original_item) || c_item_source_key
        };
        let typed_mode = self.typed_variables.is_some();
        let accumulator_capture = if typed_mode {
            typed_integer_replacement_contains
        } else {
            integer_replacement_contains && !accumulator_blocks_source
        };
        let item_capture = if item_is_integer {
            if typed_mode {
                typed_integer_item_replacement_contains
            } else {
                self.integer_replacement_variables
                    .as_ref()
                    .is_some_and(|variables| variables.contains(&original_item))
                    && !item_blocks_source
            }
        } else if typed_mode {
            typed_c_replacement_contains
        } else {
            c_replacement_contains && !item_blocks_source
        };

        // Fold endpoints and the initial value live outside the body scope.
        let [start, end, initial, body] = &fold.arguments;
        let (start, end) = if item_is_integer {
            (
                self.shared_fold_integer_child(start)?,
                self.shared_fold_integer_child(end)?,
            )
        } else {
            let format = if fold.index == KernelFoldIndex::Int32 {
                MachineIntegerType::Int32
            } else {
                MachineIntegerType::UInt64
            };
            let start = self.retained_fold_endpoint(start, format)?;
            let end = self.retained_fold_endpoint(end, format)?;
            (start, end)
        };
        let initial = self.shared_fold_integer_child(initial)?;
        if self.checked_work_exhausted() {
            return None;
        }

        let body_variable_max = if accumulator_capture || item_capture {
            self.body_variable_max(body)?
        } else {
            0
        };
        if self.checked_work_exhausted() {
            return None;
        }
        let mut fresh_upper = body_variable_max
            .max(self.integer_replacement_variable_max.unwrap_or(0))
            .max(self.bitvector_replacement_variable_max.unwrap_or(0))
            .max(self.integer_renaming_max.unwrap_or(0))
            .max(self.scope_renaming_max)
            .max(original_accumulator.0)
            .max(original_item.0);
        if let Some(source) = integer_source {
            fresh_upper = fresh_upper.max(source.0);
        }
        if let Some(source) = c_source {
            fresh_upper = fresh_upper.max(source.0);
        }
        let mut accumulator = original_accumulator;
        let mut item = original_item;
        if (accumulator_capture || item_capture)
            && let Some(next) = fresh_upper.checked_add(1)
        {
            self.fresh_next = self.fresh_next.max(next);
        } else if accumulator_capture || item_capture {
            self.integer_work_exhausted = true;
            return None;
        }
        if accumulator_capture {
            accumulator = self.fresh_variable()?;
            self.scope_renaming_max = self.scope_renaming_max.max(accumulator.0);
        }
        if item_capture {
            item = self.fresh_variable()?;
            self.scope_renaming_max = self.scope_renaming_max.max(item.0);
        }

        let accumulator_scope_shadowed = self.scope.integer.contains_key(&original_accumulator);
        let item_scope_shadowed = if item_is_integer {
            self.scope.integer.contains_key(&original_item)
        } else {
            self.scope.program_values.contains_key(&original_item)
        };
        let changed_scope = self.comparison_reads.is_some()
            || accumulator_capture
            || item_capture
            || accumulator_blocks_source
            || item_blocks_source
            || accumulator_scope_shadowed
            || item_scope_shadowed;
        let mapping_shadows_integer_source =
            self.integer_variables.as_ref().is_some_and(|mapping| {
                mapping.from == original_accumulator
                    || (item_is_integer && mapping.from == original_item)
            });

        let body = if !changed_scope {
            self.integer_fold_body(body)
        } else {
            let parent_scope = self.scope_id;
            let parent_shadowed = self.integer_shadowed;
            self.bump_scope_id();
            if self.checked_work_exhausted() {
                return None;
            }
            let mut changes = Vec::new();
            self.remove_fold_scope_mapping(true, original_accumulator, &mut changes);
            if item_is_integer {
                self.remove_fold_scope_mapping(true, original_item, &mut changes);
            } else {
                self.remove_fold_scope_mapping(false, original_item, &mut changes);
            }
            if accumulator_capture {
                self.push_fold_scope_mapping(true, original_accumulator, accumulator, &mut changes);
            } else {
                // Every fold binder hides an outer substitution at the same
                // carrier and ID, even when no freshening was needed.
                self.push_fold_scope_mapping(
                    true,
                    original_accumulator,
                    original_accumulator,
                    &mut changes,
                );
            }
            if item_capture {
                self.push_fold_scope_mapping(item_is_integer, original_item, item, &mut changes);
            } else {
                self.push_fold_scope_mapping(
                    item_is_integer,
                    original_item,
                    original_item,
                    &mut changes,
                );
            }
            if mapping_shadows_integer_source {
                self.integer_shadowed = true;
            }
            let body = self.integer_fold_body(body);
            self.restore_fold_scope_mappings(&changes);
            self.integer_shadowed = parent_shadowed;
            self.scope_id = parent_scope;
            body
        };

        Some(KernelFold {
            index: fold.index,
            accumulator,
            item,
            arguments: [start, end, initial, body?],
        })
    }

    fn retained_fold_endpoint(
        &mut self,
        root: &KernelTerm,
        format: MachineIntegerType,
    ) -> Option<KernelTerm> {
        let endpoint = SharedIntegerRangeEndpoint::from_shared(root.clone())?;
        let rewritten = self.range_endpoint(&endpoint);
        if self.checked_work_exhausted() {
            return None;
        }
        Some(KernelFold::import_endpoint(format, &rewritten))
    }

    fn integer_fold_body(&mut self, body: &KernelTerm) -> Option<KernelTerm> {
        if self.conditions.is_some() {
            return Some(body.clone());
        }
        let previous = self.resolve_registered_loads;
        self.resolve_registered_loads = true;
        let body = self.shared_fold_integer_child(body);
        self.resolve_registered_loads = previous;
        body
    }

    fn scope_key(&self) -> u64 {
        self.scope_id
    }

    fn rewrite_integer_variable(&mut self, variable: Variable) -> IntegerTerm {
        if let Some(mapped) = self.scope.integer.get(&variable) {
            return IntegerTerm::Variable(*mapped);
        }
        if !self.source_disabled
            && !self.integer_shadowed
            && let Some(replacements) = &self.typed_variables
            && let Some(replacement) = replacements.integer.get(&variable)
        {
            self.charge_rewrite_work(1);
            if self.integer_work_exhausted {
                return IntegerTerm::Variable(variable);
            }
            self.changed = true;
            // Replacement terms are from the enclosing scope.  Never walk
            // them under a nested match's lexical mappings.
            return replacement.clone();
        }
        let Some(mapping) = &self.integer_variables else {
            return IntegerTerm::Variable(variable);
        };
        if let Some(mapped) = mapping.renamings.get(&variable) {
            return IntegerTerm::Variable(*mapped);
        }
        if self.source_disabled || self.integer_shadowed || variable != mapping.from {
            return IntegerTerm::Variable(variable);
        }
        let replacement = mapping.to.clone();
        let work = match &replacement {
            IntegerTerm::Constant(value) => value.bits() as usize + 1,
            _ => 1,
        };
        self.integer_work_exhausted |= crate::instrumentation::deadline_exceeded_with_work(work);
        if self.integer_work_exhausted {
            return IntegerTerm::Variable(variable);
        }
        // Do not walk the replacement under the current lexical scope.  The
        // replacement's variables are free in this occurrence and must not
        // be remapped by an arm binder (or recursively substitute `from`).
        replacement
    }

    pub(super) fn reduce_known_int32_match(value: &OldMachineTerm) -> Option<OldMachineTerm> {
        let OldMachineTerm::AlgebraicMatch { scrutinee, arms } = value else {
            return None;
        };
        if !matches!(scrutinee.node, AlgebraicTermNode::Constructor { .. })
            || !is_simple_int32_match(value)
        {
            return None;
        }
        let mut rewrite = Self::empty();
        let reduced = rewrite.rewrite_bitvector_match_iota(scrutinee, arms);
        rewrite.refusal().is_none().then_some(reduced).flatten()
    }

    fn rewrite_bitvector_match_iota(
        &mut self,
        scrutinee: &AlgebraicTerm,
        arms: &[AlgebraicBitvectorMatchArm],
    ) -> Option<OldMachineTerm> {
        let fields = scrutinee.checked_constructor_fields()?;
        let AlgebraicTermNode::Constructor { variant, .. } = &scrutinee.node else {
            return None;
        };
        let arm = arms.iter().find(|arm| arm.variant == *variant)?;
        let schema = scrutinee
            .algebraic_type
            .variants
            .iter()
            .find(|schema| schema.name == *variant)?;
        if arm.bindings.len() != fields.len() {
            return None;
        }
        let (program_replacements, integer_replacements, algebraic_replacements) =
            match_field_replacements(&arm.bindings, fields, &schema.fields)?;
        let mut field_rewrite = TermRewrite::for_typed_variables(
            &program_replacements,
            &integer_replacements,
            &algebraic_replacements,
        );
        let value = field_rewrite.bits(&arm.body);
        self.changed |= field_rewrite.changed;
        field_rewrite.refusal_observed.set(true);
        self.unsupported_integer_scope |= field_rewrite.unsupported_integer_scope;
        self.integer_work_exhausted |= field_rewrite.integer_work_exhausted;
        #[cfg(test)]
        {
            self.visits += field_rewrite.visits;
        }
        if self.unsupported_integer_scope || self.integer_work_exhausted {
            return None;
        }
        self.changed = true;
        Some(value)
    }

    fn rewrite_algebraic_match_iota(
        &mut self,
        scrutinee: &AlgebraicTerm,
        arms: &[AlgebraicResultMatchArm],
    ) -> Option<AlgebraicTerm> {
        let fields = scrutinee.checked_constructor_fields()?;
        let AlgebraicTermNode::Constructor { variant, .. } = &scrutinee.node else {
            return None;
        };
        let arm = arms.iter().find(|arm| arm.variant == *variant)?;
        let schema = scrutinee
            .algebraic_type
            .variants
            .iter()
            .find(|schema| schema.name == *variant)?;
        if arm.bindings.len() != fields.len() {
            return None;
        }
        let (program_replacements, integer_replacements, algebraic_replacements) =
            match_field_replacements(&arm.bindings, fields, &schema.fields)?;
        let mut field_rewrite = TermRewrite::for_typed_variables(
            &program_replacements,
            &integer_replacements,
            &algebraic_replacements,
        );
        let value = field_rewrite.algebraic(&arm.body);
        self.changed |= field_rewrite.changed;
        field_rewrite.refusal_observed.set(true);
        self.unsupported_integer_scope |= field_rewrite.unsupported_integer_scope;
        self.integer_work_exhausted |= field_rewrite.integer_work_exhausted;
        #[cfg(test)]
        {
            self.visits += field_rewrite.visits;
        }
        if self.unsupported_integer_scope || self.integer_work_exhausted {
            return None;
        }
        self.changed = true;
        Some(value)
    }

    fn rewrite_match_bindings(
        &mut self,
        bindings: &mut [AlgebraicValue],
        changes: &mut Vec<ScopeChange>,
    ) -> bool {
        if (self.integer_exact.is_some()
            || self.pointer_exact.is_some()
            || self.pointer_offset_exact.is_some())
            && !bindings.is_empty()
        {
            self.unsupported_integer_scope = true;
            return false;
        }
        self.ensure_replacement_carriers();
        for binding in bindings {
            let Some((carrier, variable)) = binding_variable(binding) else {
                continue;
            };
            if matches!(carrier, BindingCarrier::Program) && self.has_composite_bitvector_source() {
                self.unsupported_integer_scope = true;
                return false;
            }
            let replacement_capture = self
                .replacement_carriers
                .as_ref()
                .is_some_and(|replacement| replacement.contains(carrier, variable));
            if replacement_capture {
                let Some(fresh) = self.fresh_variable() else {
                    return false;
                };
                self.push_binding_mapping(carrier, variable, fresh, changes);
                replace_binding_variable(binding, carrier, fresh);
            } else if self.comparison_reads.is_some()
                || self.binding_shadows_source(carrier, variable)
            {
                self.push_binding_mapping(carrier, variable, variable, changes);
                if matches!(carrier, BindingCarrier::Integer) && !self.integer_shadowed {
                    self.integer_shadowed = true;
                    self.bump_scope_id();
                }
            }
            if self.integer_work_exhausted {
                return false;
            }
        }
        true
    }

    fn rewrite_program_binder(
        &mut self,
        variable: Variable,
        changes: &mut Vec<ScopeChange>,
    ) -> Option<Variable> {
        if self.integer_exact.is_some()
            || self.pointer_exact.is_some()
            || self.pointer_offset_exact.is_some()
            || self.has_composite_bitvector_source()
        {
            self.unsupported_integer_scope = true;
            return None;
        }
        self.ensure_replacement_carriers();
        if self
            .replacement_carriers
            .as_ref()
            .is_some_and(|replacement| replacement.contains(BindingCarrier::Program, variable))
        {
            let fresh = self.fresh_variable()?;
            self.push_binding_mapping(BindingCarrier::Program, variable, fresh, changes);
            return Some(fresh);
        }
        if self.comparison_reads.is_some()
            || self.binding_shadows_source(BindingCarrier::Program, variable)
        {
            self.push_binding_mapping(BindingCarrier::Program, variable, variable, changes);
            return Some(variable);
        }
        Some(variable)
    }

    fn has_composite_bitvector_source(&self) -> bool {
        self.bitvector
            .is_some_and(|(source, _)| source.variable().is_none())
    }

    fn reserve_algebraic_match_variables(
        &mut self,
        _term: &AlgebraicTerm,
        scrutinee: &AlgebraicTerm,
        arms: &[AlgebraicResultMatchArm],
    ) {
        self.ensure_replacement_carriers();
        if self.source_variables_reserved {
            return;
        }
        let mut variables = self.new_carrier_variables();
        let mut seen = BTreeSet::new();
        collect_algebraic_carriers_seen(scrutinee, &mut variables, &mut seen);
        if variables.exhausted() {
            self.reserve_source_variables(variables);
            return;
        }
        for arm in arms {
            for binding in &arm.bindings {
                collect_algebraic_value_carriers(binding, &mut variables, &mut seen);
                if variables.exhausted() {
                    self.reserve_source_variables(variables);
                    return;
                }
            }
            collect_algebraic_carriers_seen(&arm.body, &mut variables, &mut seen);
            if variables.exhausted() {
                self.reserve_source_variables(variables);
                return;
            }
        }
        self.reserve_source_variables(variables);
    }

    fn reserve_bitvector_scope_variables(&mut self, term: &OldMachineTerm) {
        self.ensure_replacement_carriers();
        if self.source_variables_reserved {
            return;
        }
        let mut variables = self.new_carrier_variables();
        collect_bitvector_carriers(term, &mut variables);
        self.reserve_source_variables(variables);
    }

    fn binding_shadows_source(&self, carrier: BindingCarrier, variable: Variable) -> bool {
        match carrier {
            BindingCarrier::Program => {
                self.bitvector
                    .is_some_and(|(source, _)| source.variable() == Some(&variable))
                    || self
                        .pointer_variable
                        .is_some_and(|(source, _)| source == variable)
                    || self.typed_variables.as_ref().is_some_and(|replacements| {
                        replacements.program_values.contains_key(&variable)
                    })
            }
            BindingCarrier::Integer => {
                self.integer_variables
                    .as_ref()
                    .is_some_and(|mapping| mapping.from == variable)
                    || self
                        .typed_variables
                        .as_ref()
                        .is_some_and(|replacements| replacements.integer.contains_key(&variable))
            }
            BindingCarrier::Algebraic => {
                matches!(
                    self.algebraic,
                    Some((AlgebraicTerm { node: AlgebraicTermNode::Variable(source), .. }, _))
                        if *source == variable
                ) || self
                    .typed_variables
                    .as_ref()
                    .is_some_and(|replacements| replacements.algebraic.contains_key(&variable))
            }
        }
    }

    fn push_binding_mapping(
        &mut self,
        carrier: BindingCarrier,
        from: Variable,
        to: Variable,
        changes: &mut Vec<ScopeChange>,
    ) {
        let previous = match carrier {
            BindingCarrier::Program => self.scope.program_values.insert(from, to),
            BindingCarrier::Integer => self.scope.integer.insert(from, to),
            BindingCarrier::Algebraic => self.scope.algebraic.insert(from, to),
        };
        match carrier {
            BindingCarrier::Program => changes.push(ScopeChange::Program(from, previous)),
            BindingCarrier::Integer => changes.push(ScopeChange::Integer(from, previous)),
            BindingCarrier::Algebraic => changes.push(ScopeChange::Algebraic(from, previous)),
        }
        if previous != Some(to) {
            self.bump_scope_id();
        }
    }

    fn restore_scope(&mut self, changes: &[ScopeChange], scope_id: u64, integer_shadowed: bool) {
        self.charge_rewrite_work(changes.len());
        for change in changes.iter().rev() {
            match change {
                ScopeChange::Program(variable, previous) => {
                    restore_mapping(&mut self.scope.program_values, *variable, *previous)
                }
                ScopeChange::Integer(variable, previous) => {
                    restore_mapping(&mut self.scope.integer, *variable, *previous)
                }
                ScopeChange::Algebraic(variable, previous) => {
                    restore_mapping(&mut self.scope.algebraic, *variable, *previous)
                }
            }
        }
        self.scope_id = scope_id;
        self.integer_shadowed = integer_shadowed;
    }

    fn ensure_replacement_carriers(&mut self) {
        if self.replacement_carriers.is_some() {
            return;
        }
        let mut variables = self.new_carrier_variables();
        let mut seen = BTreeSet::new();
        if let Some(mapping) = &self.integer_variables {
            collect_integer_carriers(mapping.to, &mut variables, &mut seen);
        }
        if !variables.exhausted()
            && let Some((_, to)) = self.bitvector
        {
            collect_machine_operand_carriers(to, &mut variables);
        }
        if !variables.exhausted()
            && let Some((_, to)) = self.algebraic
        {
            collect_algebraic_carriers_seen(to, &mut variables, &mut seen);
        }
        if !variables.exhausted()
            && let Some((_, to)) = self.pointer_variable
        {
            collect_pointer_carriers(to, &mut variables);
        }
        if let Some(reads) = self.comparison_reads {
            for (value, _) in reads.values() {
                collect_bitvector_carriers(value, &mut variables);
                if variables.exhausted() {
                    break;
                }
            }
        }
        if !variables.exhausted()
            && let Some(replacements) = &self.typed_variables
        {
            for replacement in replacements.program_values.values() {
                match replacement {
                    TypedProgramValueReplacement::Bitvector(value) => {
                        collect_bitvector_carriers(value, &mut variables)
                    }
                    TypedProgramValueReplacement::Pointer(pointer) => {
                        for address in pointer.pointers() {
                            collect_pointer_carriers(address, &mut variables);
                        }
                    }
                }
                if variables.exhausted() {
                    break;
                }
            }
            for replacement in replacements.integer.values() {
                if variables.exhausted() {
                    break;
                }
                collect_integer_carriers(replacement, &mut variables, &mut seen);
            }
            for replacement in replacements.algebraic.values() {
                if variables.exhausted() {
                    break;
                }
                collect_algebraic_carriers_seen(replacement, &mut variables, &mut seen);
            }
        }
        #[cfg(test)]
        {
            self.collector_visits = self.collector_visits.saturating_add(variables.nodes);
        }
        self.integer_work_exhausted |= variables.work_exhausted;
        if self.integer_work_exhausted {
            self.replacement_carriers = Some(variables);
            return;
        }
        self.charge_rewrite_work(1);
        if self.integer_work_exhausted {
            self.replacement_carriers = Some(variables);
            return;
        }
        self.extend_reserved_variables(&variables);
        self.replacement_carriers = Some(variables);
    }

    fn bump_scope_id(&mut self) {
        self.charge_rewrite_work(1);
        if let Some(next) = self.next_scope_id.checked_add(1) {
            self.scope_id = self.next_scope_id;
            self.next_scope_id = next;
        } else {
            self.integer_work_exhausted = true;
        }
    }

    fn fresh_variable(&mut self) -> Option<Variable> {
        if self.bitvector.is_some() && self.bitvector_replacement_variables.is_none() {
            self.ensure_replacement_carriers();
        }
        if self.integer_work_exhausted {
            return None;
        }
        loop {
            let variable = Variable(self.fresh_next);
            let Some(next) = self.fresh_next.checked_add(1) else {
                self.integer_work_exhausted = true;
                return None;
            };
            self.fresh_next = next;
            self.charge_rewrite_work(1);
            if self.reserved_variables.insert(variable) {
                return Some(variable);
            }
        }
    }

    fn charge_rewrite_work(&mut self, work: usize) {
        if self.integer_variables.is_some()
            || self.typed_variables.is_some()
            || self.enforce_integer_work_limit
        {
            self.integer_work_exhausted |=
                crate::instrumentation::deadline_exceeded_with_work(work);
        } else {
            crate::instrumentation::record_deterministic_work(work);
        }
    }

    fn pointer(&mut self, p: &Address) -> Address {
        if self.checked_work_exhausted() {
            return exhausted_pointer();
        }
        if let Some((from, to)) = self.pointer_exact
            && p == from
            && !self.source_disabled
        {
            self.changed = true;
            return to.clone();
        }
        // A full value equality `p == q` also substitutes `p + d` by `q + d`
        // when `p` is the base of its block: the displaced pointer is formed
        // from that same value. Address equality alone never moves a pointer
        // to another origin, so this rule needs the full value equality.
        if let Some((from, to)) = self.pointer_exact
            && self.pointer_value_exact.is_some()
            && !self.source_disabled
            && p.base == from.base
            && matches!(from.offset.view(), OffsetView::Constant(0))
            && matches!(from.base, AddressBase::Load(_))
        {
            self.changed = true;
            let displacement = self.offset(&p.offset);
            return to.with_offset(AddressOffset::add(to.offset.clone(), displacement));
        }
        // A read depends on its selected address. Substitute full pointers
        // or numeric indices through that address, retaining the read's
        // defining state and memoizing shared read definitions.
        if (self.pointer_value_exact.is_some() || self.bitvector.is_some())
            && !self.source_disabled
            && let Some(read) = p.as_loaded_value()
        {
            self.charge_rewrite_work(1);
            let key = (
                read.identity,
                self.scope_id,
                self.source_disabled,
                self.resolve_registered_loads,
            );
            let offset = self.offset(&read.displacement);
            if let Some(block) = self.pointer_origin_cache.get(&key) {
                self.changed |= block != &p.base;
                return Address::new(block.clone(), offset);
            }
            let address = self.pointer(&read.defining_address);
            let block = if address != read.defining_address {
                self.changed = true;
                // Rewriting changes the selected address, not the read into
                // its stored value. Keep the immutable defining state.
                Address::version_read_at(&read.defining_memory, Some(&read.point), &address)
                    .base
                    .clone()
            } else {
                p.base.clone()
            };
            self.pointer_origin_cache.insert(key, block.clone());
            return Address::new(block, offset);
        }
        // Opaque object and bounds identities participate in lexical
        // binding, never in numeric pointer rewrites.
        if let AddressBase::ExternalObject(variable) = &p.base {
            if let Some(mapped) = self.scope.program_values.get(variable) {
                return Address::new(AddressBase::ExternalObject(*mapped), self.offset(&p.offset));
            }
            if let Some(TypedProgramValueReplacement::Pointer(replacement)) = self
                .typed_variables
                .as_ref()
                .and_then(|values| values.program_values.get(variable))
            {
                let root = replacement.provenance().clone();
                self.changed = true;
                return root.with_offset(AddressOffset::add(
                    root.offset.clone(),
                    self.offset(&p.offset),
                ));
            }
            if let Some((from, to)) = self.pointer_variable
                && *variable == from
            {
                let root = to.object_identity();
                self.changed = true;
                return root.with_offset(AddressOffset::add(
                    root.offset.clone(),
                    self.offset(&p.offset),
                ));
            }
        }
        if let AddressBase::Symbolic(variable) | AddressBase::FunctionSymbolic(variable) = &p.base
            && let Some(mapped) = self.scope.program_values.get(variable)
        {
            let mapped = *mapped;
            let offset = self.offset(&p.offset);
            if self.checked_work_exhausted() {
                return exhausted_pointer();
            }
            return Address::new(
                match &p.base {
                    AddressBase::FunctionSymbolic(_) => AddressBase::FunctionSymbolic(mapped),
                    _ => AddressBase::Symbolic(mapped),
                },
                offset,
            );
        }
        if let AddressBase::Symbolic(variable) | AddressBase::FunctionSymbolic(variable) = &p.base
            && let Some(replacements) = &self.typed_variables
            && let Some(TypedProgramValueReplacement::Pointer(replacement)) =
                replacements.program_values.get(variable)
        {
            self.changed = true;
            let offset = self.offset(&p.offset);
            if self.checked_work_exhausted() {
                return exhausted_pointer();
            }
            return replacement.with_offset(AddressOffset::add(replacement.offset.clone(), offset));
        }
        // A loop state's pointer value is a symbolic base plus its
        // displacement. Rewriting the complete base value also respells
        // displaced addresses; the value path retains their selected bounds.
        if let Some((from, to)) = self.pointer_value_exact
            && !self.source_disabled
            && matches!(from.address().base, AddressBase::Symbolic(_))
            && matches!(from.address().offset.view(), OffsetView::Constant(0))
            && p.base == from.address().base
        {
            self.changed = true;
            let offset = self.offset(&p.offset);
            if self.checked_work_exhausted() {
                return exhausted_pointer();
            }
            return to
                .address()
                .with_offset(AddressOffset::add(to.address().offset.clone(), offset));
        }
        if let Some((from, to)) = self.pointer_variable
            && matches!(&p.base, AddressBase::Symbolic(variable) | AddressBase::FunctionSymbolic(variable) if *variable == from)
        {
            self.changed = true;
            let offset = self.offset(&p.offset);
            if self.checked_work_exhausted() {
                return exhausted_pointer();
            }
            return to.with_offset(AddressOffset::add(to.offset.clone(), offset));
        }
        let offset = self.offset(&p.offset);
        if self.checked_work_exhausted() {
            return exhausted_pointer();
        }
        Address::new(
            match &p.base {
                AddressBase::Symbolic(variable)
                    if self.resolve_registered_loads
                        && (self.pointer_variable.is_some()
                            || self.pointer_exact.is_some()
                            || self.pointer_offset_exact.is_some())
                        && crate::kernel::is_load_variable(variable) =>
                {
                    AddressBase::Symbolic(
                        self.rewrite_registered_load(*variable).unwrap_or(*variable),
                    )
                }
                AddressBase::PureFunctionApplication(application) => {
                    self.charge_rewrite_work(1);
                    let key = (
                        application.id(),
                        self.scope_id,
                        self.source_disabled,
                        self.resolve_registered_loads,
                    );
                    if let Some(result) = self.pointer_application_cache.get(&key) {
                        result.clone()
                    } else {
                        let mut arguments = Vec::with_capacity(application.arguments().len());
                        for argument in application.arguments() {
                            arguments.push(self.argument(argument));
                            if self.checked_work_exhausted() {
                                return exhausted_pointer();
                            }
                        }
                        let rewritten = SharedPureApplication::intern(
                            application.name().to_string(),
                            arguments,
                        );
                        // A checked substitution can clear every address bit.
                        // Use the same null representation as the original
                        // cast, keeping the displacement outside this block.
                        let result = if let Some(bits) = rewritten.integer_address_bits() {
                            Address::from_integer_address(bits.clone()).base.clone()
                        } else {
                            AddressBase::PureFunctionApplication(rewritten)
                        };
                        self.pointer_application_cache.insert(key, result.clone());
                        result
                    }
                }
                other => other.clone(),
            },
            offset,
        )
    }
    fn index_bits(&mut self, value: &SharedMachineIntegerTerm) -> SharedMachineIntegerTerm {
        let operand = value.operand_view();
        // Root atoms retain the cheap native rewrite path without exporting.
        if let Some(atom) = operand
            .literal()
            .or_else(|| operand.variable().map(|v| OldMachineTerm::Variable(*v)))
        {
            return SharedMachineIntegerTerm::index(value.ty(), self.bits(&atom));
        }
        if let Some(root) = value.shared_operand() {
            return match self.shared_machine_operand(root) {
                Some(rewritten) => SharedMachineIntegerTerm::from_shared(value.ty(), rewritten)
                    .expect("rewritten index retains its machine carrier"),
                None => {
                    self.unsupported_integer_scope = true;
                    value.clone()
                }
            };
        }
        SharedMachineIntegerTerm::index(value.ty(), self.bits(value.value()))
    }

    fn rebuilt_index(
        &self,
        value: SharedMachineIntegerTerm,
        byte_width: i64,
        wide: Option<bool>,
    ) -> AddressOffset {
        let view = value.operand_view();
        // Native input and fixed-size leaves use the existing constant policy.
        let native = view
            .literal()
            .map(std::borrow::Cow::Owned)
            .or_else(|| view.read_source());
        if let Some(native) = native {
            let native = if self.resolve_registered_loads {
                canonicalize_integer_to_machine_constant(native.into_owned())
            } else {
                native.into_owned()
            };
            return match (wide, self.resolve_registered_loads) {
                (None, true) => AddressOffset::scale_int32(native, byte_width),
                (None, false) => AddressOffset::scaled_int32_node(native, byte_width),
                (Some(unsigned), true) => AddressOffset::scale_int64(native, byte_width, unsigned),
                (Some(unsigned), false) => {
                    AddressOffset::scaled_int64_node(native, byte_width, unsigned)
                }
            };
        }
        if wide == Some(false) && self.resolve_registered_loads {
            let widened = |v: MachineOperandView<'_>| match v.cast() {
                Some((MachineCastSpelling::Int64From32, _, _, child)) => {
                    Some(child.retain(MachineIntegerType::Int32))
                }
                _ => None,
            };
            if u32::try_from(byte_width).is_ok()
                && let Some(child) = widened(view)
            {
                return self.rebuilt_index(child, byte_width, None);
            }
            if let Some((MachineIntegerType::Int64, MachineBinaryOp::Multiply, [left, right])) =
                view.binary()
            {
                for (index, stride) in [(left, right), (right, left)] {
                    if let (Some(index), Some(stride)) = (widened(index), stride.int64_constant())
                        && let Ok(stride) = u32::try_from(stride)
                        && let Some(width) = i64::from(stride).checked_mul(byte_width)
                        && u32::try_from(width).is_ok()
                    {
                        return self.rebuilt_index(index, width, None);
                    }
                }
            }
        }
        match wide {
            None => AddressOffset::int32_scaled(value, byte_width),
            Some(unsigned) => AddressOffset::int64_scaled(value, byte_width, unsigned),
        }
    }

    fn rewrite_offset_index(
        &mut self,
        value: &SharedMachineIntegerTerm,
        byte_width: i64,
        wide: Option<bool>,
    ) -> AddressOffset {
        let value = self.index_bits(value);
        let bounded = wide == Some(true)
            && self.conditions.is_some_and(|conditions| {
                self.bounded_uint64_indices
                    .get_or_insert_with(|| bounded_uint64_indices(conditions))
                    .contains(&BoundedIndexKey::of(&value))
            });
        if bounded {
            self.changed = true;
            let narrowed = if let Some(root) = value.shared_operand() {
                SharedMachineIntegerTerm::from_shared(
                    MachineIntegerType::Int32,
                    root.checking_low_word(),
                )
                .expect("low-word index")
            } else {
                SharedMachineIntegerTerm::index(
                    MachineIntegerType::Int32,
                    OldMachineTerm::uint32_from_64(value.value().clone()),
                )
            };
            // The checked narrowing keeps a written scaled node.
            AddressOffset::int32_scaled(narrowed, byte_width)
        } else {
            self.rebuilt_index(value, byte_width, wide)
        }
    }

    fn contract_offset(&mut self, offset: &StoredPointerOffset) -> StoredPointerOffset {
        let source = offset.root();
        let replacement = match &self.pointer_offset_exact {
            Some(exact) if self.pointer_value_exact.is_none() || !self.source_disabled => {
                let Some(retained) = exact.retained() else {
                    return self.offset(offset.old_form()).into();
                };
                Some(retained.clone())
            }
            _ => None,
        };
        match self.rewrite_retained_offset_replacing(source, replacement.as_ref()) {
            Ok(root) if root == *source => offset.clone(),
            Ok(root) => StoredPointerOffset::from_rewritten_root(root),
            Err(()) => exhausted_offset().into(),
        }
    }

    fn rewrite_retained_offset(
        &mut self,
        source: &SharedAddressOffset,
    ) -> Result<SharedAddressOffset, ()> {
        self.rewrite_retained_offset_replacing(source, None)
    }

    fn rewrite_retained_offset_replacing(
        &mut self,
        source: &SharedAddressOffset,
        replacement: Option<&(OffsetKey, SharedAddressOffset)>,
    ) -> Result<SharedAddressOffset, ()> {
        let replaced = std::cell::Cell::new(false);
        let replace = |candidate: &SharedAddressOffset| {
            let (from, to) = replacement?;
            from.matches_root(candidate).then(|| {
                replaced.set(true);
                to.clone()
            })
        };
        let root = source.try_map_root_replacing(replace, |original, node| {
            if self.checked_work_exhausted() {
                return Err(());
            }
            Ok(match node {
                KernelAddressOffset::Add([a, b]) if self.resolve_registered_loads => {
                    SharedAddressOffset::add(a, b)
                }
                KernelAddressOffset::Add(children) => KernelAddressOffset::Add(children)
                    .into_shared()
                    .expect("offset sum"),
                KernelAddressOffset::Variable(variable)
                    if self.resolve_registered_loads
                        && crate::kernel::is_load_variable(&variable) =>
                {
                    self.rewrite_registered_load(variable).map_or_else(
                        || original.clone(),
                        |variable| {
                            KernelAddressOffset::Variable(variable)
                                .into_shared()
                                .expect("offset variable")
                        },
                    )
                }
                KernelAddressOffset::Int32Scaled { value, byte_width } => {
                    let index = SharedAddressOffset::exact_index(&value);
                    self.rewrite_offset_index(&index, byte_width, None)
                        .into_shared()
                }
                KernelAddressOffset::Int64Scaled {
                    value,
                    byte_width,
                    unsigned,
                } => {
                    let index = SharedAddressOffset::exact_index(&value);
                    self.rewrite_offset_index(&index, byte_width, Some(unsigned))
                        .into_shared()
                }
                _ => original.clone(),
            })
        })?;
        self.changed |= replaced.get();
        (!self.checked_work_exhausted()).then_some(root).ok_or(())
    }

    fn offset(&mut self, v: &AddressOffset) -> AddressOffset {
        if let Some(exact) = &self.pointer_offset_exact
            && v == exact.from
            && (self.pointer_value_exact.is_none() || !self.source_disabled)
        {
            self.changed = true;
            return exact.to.clone();
        }
        if self.checked_work_exhausted() {
            return exhausted_offset();
        }
        let result = match v.view() {
            OffsetView::Constant(_) => v.clone(),
            OffsetView::Variable(variable)
                if self.resolve_registered_loads && crate::kernel::is_load_variable(&variable) =>
            {
                self.rewrite_registered_load(variable)
                    .map_or_else(|| v.clone(), AddressOffset::variable)
            }
            OffsetView::Variable(_) => v.clone(),
            OffsetView::Add(a, b) => {
                let left = self.offset(a);
                let right = self.offset(b);
                if self.resolve_registered_loads {
                    AddressOffset::add(left, right)
                } else {
                    AddressOffset::raw_add(left, right)
                }
            }
            OffsetView::Int32Scaled { index, byte_width } => {
                self.rewrite_offset_index(&index, byte_width, None)
            }
            OffsetView::Int64Scaled {
                index,
                byte_width,
                unsigned,
            } => self.rewrite_offset_index(&index, byte_width, Some(unsigned)),
        };
        if self.checked_work_exhausted() {
            exhausted_offset()
        } else {
            result
        }
    }
    fn cited_condition_value(&self, condition: &OldConditionTerm) -> Option<bool> {
        self.conditions
            .and_then(|conditions| {
                conditions
                    .get(condition)
                    .or_else(|| conditions.get(&condition.flipped()))
                    .copied()
            })
            .or_else(|| {
                self.cited_conditions.and_then(|graph| {
                    [true, false]
                        .into_iter()
                        .find(|value| graph.knows_condition(condition, *value))
                        .or_else(|| {
                            use crate::kernel::machine_integer::{
                                Relation, comparison::comparison_view,
                            };
                            let view = comparison_view(condition, true)?;
                            if !matches!(
                                view.format,
                                MachineIntegerType::Int64 | MachineIntegerType::UInt64
                            ) {
                                return None;
                            }
                            let equal = match view.relation {
                                Relation::Equal => true,
                                Relation::NotEqual => false,
                                _ => return None,
                            };
                            // A cited wide equality can fix both words to
                            // different constants. This indexed class lookup
                            // decides an If guard without any ambient facts.
                            let [left, right] = view
                                .operands
                                .each_ref()
                                .map(|operand| operand.operand_view());
                            Some(
                                (graph.uint64_constant_view(left)?
                                    == graph.uint64_constant_view(right)?)
                                    == equal,
                            )
                        })
                })
            })
    }

    pub(crate) fn condition(&mut self, v: &OldConditionTerm) -> OldConditionTerm {
        self.reserve_condition_variables_once(v);
        if self.checked_work_exhausted() {
            return OldConditionTerm::Constant(false);
        }
        self.visit();
        if self.checked_work_exhausted() {
            return OldConditionTerm::Constant(false);
        }
        // Only the explicitly cited facts can refute a condition here. The
        // shared graph makes address-origin annotations numerically transparent.
        if let Some(value) = self.cited_condition_value(v) {
            return OldConditionTerm::Constant(value);
        }
        if let Some((from, to)) = self.condition_exact
            && v == from
        {
            self.changed = true;
            return to.clone();
        }
        // A `Bool` atom guards the value it is read in, as the condition of
        // a conditional does: a fact about it decides that value. So does a
        // `Bool` conditional's condition.
        if let Some(conditions) = &mut self.collected_conditions {
            match v {
                OldConditionTerm::Variable(_) | OldConditionTerm::BoolApplication(_) => {
                    conditions.push(v.clone())
                }
                // Each part of a `Bool` conditional or equality guards it.
                v if v.is_bool_value_form() => conditions.extend(
                    v.bool_children()
                        .filter(|child| {
                            !matches!(child, OldConditionTerm::Constant(_))
                                && !child.is_bool_value_form()
                        })
                        .cloned(),
                ),
                _ => {}
            }
        }
        // A `Bool` binder (Stage 5) is renamed with its scope and replaced
        // by the truth of the `Bool` word it is instantiated with.
        if let OldConditionTerm::Variable(variable) = v {
            if let Some(mapped) = self.scope.program_values.get(variable) {
                return OldConditionTerm::Variable(*mapped);
            }
            if let Some(replacements) = &self.typed_variables
                && let Some(TypedProgramValueReplacement::Bitvector(replacement)) =
                    replacements.program_values.get(variable)
            {
                self.changed = true;
                return OldConditionTerm::truth_of_bool_word(replacement);
            }
        }
        let result = match v {
            OldConditionTerm::Constant(_) | OldConditionTerm::Variable(_) => v.clone(),
            OldConditionTerm::AlgebraicEqual(a, b) => OldConditionTerm::AlgebraicEqual(
                Box::new(self.algebraic(a)),
                Box::new(self.algebraic(b)),
            ),
            OldConditionTerm::Float32(condition) => {
                OldConditionTerm::Float32(condition.map_bitvector_terms(|b| self.bits(b)))
            }
            OldConditionTerm::Float64(condition) => {
                OldConditionTerm::Float64(condition.map_bitvector_terms(|b| self.bits(b)))
            }
            OldConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation,
                left,
                right,
            } if self.preserves_algebraic_matches()
                && (is_simple_int32_match(left) || is_simple_int32_match(right)) =>
            {
                OldConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: *relation,
                    left: Box::new(
                        self.bits_with_match_reduction(left, !is_simple_int32_match(left)),
                    ),
                    right: Box::new(
                        self.bits_with_match_reduction(right, !is_simple_int32_match(right)),
                    ),
                }
            }
            OldConditionTerm::Compare {
                format: MachineIntegerType::Int64,
                relation: CompareRelation::Equal,
                left: a,
                right: b,
            } => {
                let left = self.bits(a);
                let right = self.bits(b);
                if matches!(
                    (&left, &right),
                    (OldMachineTerm::IntegerAddress(_, _), zero)
                        | (zero, OldMachineTerm::IntegerAddress(_, _))
                        if zero.uint64_as_const() == Some(0)
                ) {
                    // Rewriting can expose a null address after the original
                    // comparison was constructed. Use the same relation as a
                    // directly written zero-address comparison, then consume
                    // only the selected conditions for that relation.
                    self.changed = true;
                    let canonical = OldConditionTerm::int64_equal(left, right);
                    self.cited_condition_value(&canonical)
                        .map_or(canonical, OldConditionTerm::Constant)
                } else {
                    OldConditionTerm::Compare {
                        format: MachineIntegerType::Int64,
                        relation: CompareRelation::Equal,
                        left: Box::new(left),
                        right: Box::new(right),
                    }
                }
            }
            OldConditionTerm::PointerEqual(a, b) => {
                let ProgramValue::Pointer(a) = self.value(&ProgramValue::Pointer((**a).clone()))
                else {
                    unreachable!()
                };
                let ProgramValue::Pointer(b) = self.value(&ProgramValue::Pointer((**b).clone()))
                else {
                    unreachable!()
                };
                let canonical = |value: OldPointer| {
                    value.map_addresses(|p| {
                        p.with_offset(crate::kernel::eval::canonical_offset_term(&p.offset))
                    })
                };
                OldConditionTerm::pointer_equal(canonical(a), canonical(b))
            }
            OldConditionTerm::AddressEqual(a, b) => {
                OldConditionTerm::AddressEqual(Box::new(self.pointer(a)), Box::new(self.pointer(b)))
            }
            OldConditionTerm::AddressOffsetEqual(a, b) => OldConditionTerm::AddressOffsetEqual(
                Box::new(self.offset(a)),
                Box::new(self.offset(b)),
            ),
            crate::kernel::integer_comparison_condition!(a, b) => {
                let retain_match = self.preserves_algebraic_matches();
                let left = self.integer_with_match_retention(a, retain_match).into();
                let right = self.integer_with_match_retention(b, retain_match).into();
                match v {
                    OldConditionTerm::IntegerLessThan(..) => {
                        OldConditionTerm::IntegerLessThan(left, right)
                    }
                    OldConditionTerm::IntegerLessEqual(..) => {
                        OldConditionTerm::IntegerLessEqual(left, right)
                    }
                    OldConditionTerm::IntegerGreaterThan(..) => {
                        OldConditionTerm::IntegerGreaterThan(left, right)
                    }
                    OldConditionTerm::IntegerGreaterEqual(..) => {
                        OldConditionTerm::IntegerGreaterEqual(left, right)
                    }
                    OldConditionTerm::IntegerEqual(..) => {
                        OldConditionTerm::IntegerEqual(left, right)
                    }
                    OldConditionTerm::IntegerNotEqual(..) => {
                        OldConditionTerm::IntegerNotEqual(left, right)
                    }
                    _ => unreachable!("Integer comparison"),
                }
            }
            // A `Bool` value rewrites its children, an application's
            // arguments and a read's pointer, as a word-valued application
            // and a load do; a read keeps its state.
            v if v.is_bool_value_form() => {
                let mut children = Vec::with_capacity(3);
                for child in v.bool_children() {
                    children.push(self.condition(child));
                }
                let mut children = children.into_iter();
                let rewritten = match v {
                    OldConditionTerm::BoolApplication(application) => {
                        let mut arguments = Vec::with_capacity(application.arguments().len());
                        for argument in application.arguments() {
                            arguments.push(self.argument(argument));
                        }
                        OldConditionTerm::BoolApplication(
                            crate::kernel::SharedPureApplication::intern(
                                application.name().to_owned(),
                                arguments,
                            ),
                        )
                    }
                    // A rewrite that decided a conditional's condition, or
                    // made an equality's operands one, leaves what the
                    // folding constructors would have built, as the word
                    // conditional above does.
                    OldConditionTerm::BoolIf { .. } if self.integer_exact.is_none() => {
                        let condition = children.next().expect("a condition");
                        let then_condition = children.next().expect("a then branch");
                        let else_condition = children.next().expect("an else branch");
                        OldConditionTerm::bool_if(
                            folded_machine_condition(condition),
                            then_condition,
                            else_condition,
                        )
                    }
                    OldConditionTerm::BoolEqual(..) if self.integer_exact.is_none() => {
                        let left = children.next().expect("a left operand");
                        let right = children.next().expect("a right operand");
                        OldConditionTerm::bool_equal(left, right)
                    }
                    v => v
                        .map_bool_value_form(
                            |_| children.next().expect("one rewrite per child"),
                            |argument| argument.clone(),
                        )
                        .expect("a `Bool` value form maps"),
                };
                if self.checked_work_exhausted() {
                    return OldConditionTerm::Constant(false);
                }
                // A cited `Bool` value the rewrite of its parts produced,
                // `f(if f(x) { x } else { y })` read under `f(x)`, is
                // decided by its citation as the written value is.
                if rewritten != *v
                    && let Some(value) = self.cited_condition_value(&rewritten)
                {
                    return OldConditionTerm::Constant(value);
                }
                rewritten
            }
            v => {
                let (op, left, right) = v
                    .as_bitvector_comparison()
                    .expect("every other condition has its own arm");
                super::equality_rewrite::rebuild_machine_comparison(
                    op,
                    self.bits(left),
                    self.bits(right),
                )
            }
        };
        // Comparison forms are lookup aids, not stored syntax. Replacing a
        // read can expose a literal machine comparison; preserve the old
        // substitution path's constant result without simplifying symbolic
        // operands or revisiting an arithmetic prefix.
        if self.comparison_reads.is_some()
            && let OldConditionTerm::Compare {
                format,
                relation,
                left,
                right,
            } = &result
            && matches!(left.as_ref(), OldMachineTerm::Constant { .. })
            && matches!(right.as_ref(), OldMachineTerm::Constant { .. })
        {
            return OldConditionTerm::machine_compare(
                *format,
                *relation,
                left.as_ref().clone(),
                right.as_ref().clone(),
            );
        }
        if let Some([left, right]) = result.pointer_offset_association_guard() {
            if let Some(conditions) = &mut self.collected_conditions {
                // Planner output: the public guard carrier still owns native
                // operands. Checking below never constructs this output.
                conditions.push(OldConditionTerm::signed_add_overflows(
                    left.structural_value().clone(),
                    right.structural_value().clone(),
                ));
            }
            let leaf = |value: &SharedMachineIntegerTerm| {
                value.operand_view().literal().or_else(|| {
                    value
                        .operand_view()
                        .read_source()
                        .map(|leaf| leaf.into_owned())
                })
            };
            let known_false = if let (Some(a), Some(b)) = (leaf(&left), leaf(&right)) {
                let guard = OldConditionTerm::signed_add_overflows(a, b);
                guard == OldConditionTerm::Constant(false)
                    || self
                        .conditions
                        .is_some_and(|conditions| conditions.get(&guard) == Some(&false))
            } else if let Some(conditions) = self.conditions {
                let fingerprint = crate::kernel::assumptions::machine_syntax_fingerprint;
                let index = self.pointer_association_conditions.get_or_insert_with(|| {
                    let mut index = HashMap::<_, Vec<_>>::new();
                    for (condition, value) in conditions {
                        crate::instrumentation::record_deterministic_work(1);
                        if let OldConditionTerm::Overflows {
                            format: MachineIntegerType::Int32,
                            op: crate::kernel::OverflowOperation::Add,
                            left,
                            right,
                        } = condition
                        {
                            let key = (
                                fingerprint(MachineOperandView::Old(left)),
                                fingerprint(MachineOperandView::Old(right)),
                            );
                            index.entry(key).or_default().push((
                                left.as_ref().clone(),
                                right.as_ref().clone(),
                                *value,
                            ));
                        }
                    }
                    index
                });
                let key = (
                    fingerprint(left.operand_view()),
                    fingerprint(right.operand_view()),
                );
                index.get(&key).is_some_and(|bucket| {
                    bucket.iter().any(|(a, b, value)| {
                        !value
                            && crate::kernel::machine_operand_syntax_cmp(
                                left.operand_view(),
                                MachineOperandView::Old(a),
                            )
                            .is_eq()
                            && crate::kernel::machine_operand_syntax_cmp(
                                right.operand_view(),
                                MachineOperandView::Old(b),
                            )
                            .is_eq()
                    })
                })
            } else {
                false
            };
            if known_false {
                return OldConditionTerm::Constant(true);
            }
        }
        if let Some(guard) = result.pointer_offset_uint64_association_guard() {
            if let Some(conditions) = &mut self.collected_conditions {
                conditions.push(guard.clone());
            }
            // One exact lookup, keyed by the guard the regrouped sum spells.
            if guard == OldConditionTerm::Constant(true)
                || self
                    .conditions
                    .is_some_and(|conditions| conditions.get(&guard) == Some(&true))
            {
                return OldConditionTerm::Constant(true);
            }
        }
        if let OldConditionTerm::Compare {
            format: MachineIntegerType::Int64,
            relation: CompareRelation::Equal,
            left: a,
            right: b,
        } = &result
        {
            let le = OldConditionTerm::uint64_less_equal(a.as_ref().clone(), b.as_ref().clone());
            let lt = OldConditionTerm::uint64_less_than(a.as_ref().clone(), b.as_ref().clone());
            if let Some(conditions) = &mut self.collected_conditions {
                conditions.extend([le.clone(), lt.clone()]);
            }
            if self.conditions.is_some_and(|conditions| {
                conditions.get(&le) == Some(&true) && conditions.get(&lt) == Some(&false)
            }) {
                return OldConditionTerm::Constant(true);
            }
        }
        if let Some(guards) = result.uint64_index_order_guards() {
            if let Some(conditions) = &mut self.collected_conditions {
                conditions.extend(guards.iter().cloned());
            }
            if self.conditions.is_some_and(|conditions| {
                guards.iter().all(|guard| {
                    *guard == OldConditionTerm::Constant(true)
                        || conditions.get(guard) == Some(&true)
                })
            }) {
                return OldConditionTerm::Constant(true);
            }
        }
        if let Some(guard) = result
            .uint64_successor_guard()
            .or_else(|| result.uint64_subtraction_guard())
            .or_else(|| result.uint64_remainder_bound_guard())
        {
            if let Some(conditions) = &mut self.collected_conditions {
                conditions.push(guard.clone());
            }
            if self
                .conditions
                .is_some_and(|conditions| conditions.get(&guard) == Some(&true))
            {
                return OldConditionTerm::Constant(true);
            }
        }
        if let Some(guards) = result
            .uint64_subtraction_upper_bound_guards()
            .or_else(|| result.uint64_partial_restoration_upper_bound_guards())
        {
            if let Some(conditions) = &mut self.collected_conditions {
                conditions.extend(guards.iter().cloned());
            }
            if self.conditions.is_some_and(|conditions| {
                guards.iter().all(|guard| {
                    *guard == OldConditionTerm::Constant(true)
                        || conditions.get(guard) == Some(&true)
                })
            }) {
                return OldConditionTerm::Constant(true);
            }
        }
        if let Some(guards) = result.nonnegative_division_bound_guards() {
            if let Some(conditions) = &mut self.collected_conditions {
                conditions.extend(guards.iter().cloned());
            }
            if self.conditions.is_some_and(|conditions| {
                guards.iter().all(|guard| {
                    *guard == OldConditionTerm::Constant(true)
                        || conditions.get(guard) == Some(&true)
                })
            }) {
                return OldConditionTerm::Constant(true);
            }
        }
        if self.checked_work_exhausted() {
            OldConditionTerm::Constant(false)
        } else if self.equality_graph.is_some_and(|graph| match &result {
            OldConditionTerm::PointerEqual(left, right) => {
                let matches = self.pointer_context.map_or_else(
                    || left.same_provenance_as(right),
                    |context| context.pointer_provenance_match(left, right),
                );
                matches && graph.are_equal(left.address(), right.address())
            }
            OldConditionTerm::AddressEqual(left, right) => graph.are_equal(left, right),
            OldConditionTerm::AddressOffsetEqual(left, right) => {
                graph.are_offsets_equal(left, right)
            }
            OldConditionTerm::Compare {
                format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
                relation: CompareRelation::Equal,
                left,
                right,
            } => graph.are_int32_equal(left, right),
            OldConditionTerm::Compare {
                format: MachineIntegerType::Int64,
                relation: CompareRelation::Equal,
                left,
                right,
            } => graph.are_uint64_equal(left, right),
            _ => false,
        }) {
            OldConditionTerm::Constant(true)
        } else {
            result
        }
    }
    fn range_endpoint(
        &mut self,
        endpoint: &SharedIntegerRangeEndpoint,
    ) -> SharedIntegerRangeEndpoint {
        if let Some(root) = endpoint.machine_operand().shared_operand()
            && let Some(rewritten) = self.shared_machine_operand(root)
        {
            return endpoint
                .with_shared_operand(rewritten)
                .expect("range endpoint carrier");
        }
        if self.checked_work_exhausted() {
            return endpoint.clone();
        }
        SharedIntegerRangeEndpoint::intern(self.bits(endpoint.value()))
    }

    /// Match a retained source against an explicit native output carrier.
    /// Visit only the selected syntax; no source is exported for inspection.
    fn matches_machine_source(
        &mut self,
        native: &OldMachineTerm,
        source: MachineOperandView<'_>,
    ) -> bool {
        fn same_payload(
            rewrite: &mut TermRewrite<'_>,
            left: &OldMachineTerm,
            right: &OldMachineTerm,
        ) -> bool {
            fn native(view: MachineOperandView<'_>) -> &OldMachineTerm {
                let MachineOperandView::Old(term) = view else {
                    unreachable!("native syntax child")
                };
                term
            }
            let mut pending = vec![(left, right)];
            while let Some((left, right)) = pending.pop() {
                // This is matching work inside one existing rewrite visit,
                // not another visit of the rewritten source expression.
                rewrite.charge_rewrite_work(1);
                if rewrite.checked_work_exhausted() {
                    return false;
                }
                if std::ptr::eq(left, right) {
                    continue;
                }
                // The only new equality here is a call's typed argument
                // carrier choice. Keep every surrounding native syntax tag,
                // operation format, cast spelling and binder identity exact.
                if std::mem::discriminant(left) != std::mem::discriminant(right) {
                    return false;
                }
                let a = MachineOperandView::Old(left);
                let b = MachineOperandView::Old(right);
                if let (Some((af, ao, av)), Some((bf, bo, bv))) = (a.binary(), b.binary()) {
                    if (af, ao) != (bf, bo) {
                        return false;
                    }
                    pending.extend(av.into_iter().zip(bv).map(|(a, b)| (native(a), native(b))));
                    continue;
                }
                if let (Some((af, ao, av)), Some((bf, bo, bv))) = (a.unary(), b.unary()) {
                    if (af, ao) != (bf, bo) {
                        return false;
                    }
                    pending.push((native(av), native(bv)));
                    continue;
                }
                if let (Some((ae, af, at, av)), Some((be, bf, bt, bv))) = (a.cast(), b.cast()) {
                    if (ae, af, at) != (be, bf, bt) {
                        return false;
                    }
                    pending.push((native(av), native(bv)));
                    continue;
                }
                match (left, right) {
                    (
                        OldMachineTerm::ClickFunctionApplication {
                            name: a,
                            arguments: av,
                        },
                        OldMachineTerm::ClickFunctionApplication {
                            name: b,
                            arguments: bv,
                        },
                    ) if a == b => {
                        if SharedPureApplication::intern(a.clone(), av.clone())
                            != SharedPureApplication::intern(b.clone(), bv.clone())
                        {
                            return false;
                        }
                    }
                    (
                        OldMachineTerm::If {
                            condition: a,
                            then_term: at,
                            else_term: af,
                        },
                        OldMachineTerm::If {
                            condition: b,
                            then_term: bt,
                            else_term: bf,
                        },
                    ) if a == b => {
                        pending.push((at, bt));
                        pending.push((af, bf));
                    }
                    _ if left == right => {}
                    _ => return false,
                }
            }
            true
        }
        let MachineOperandView::Shared(root) = source else {
            let MachineOperandView::Old(source) = source else {
                unreachable!()
            };
            if same_payload(self, native, source) {
                return true;
            }
            // Shared observations can retain a native read name for output.
            // When a replacement crosses the native-only value boundary,
            // match that name to the exact structural read selected by the
            // caller, without choosing another state or resolving a value.
            let (variable, read) = match (native, source) {
                (OldMachineTerm::Variable(variable), read @ OldMachineTerm::MemoryLoad(..))
                | (read @ OldMachineTerm::MemoryLoad(..), OldMachineTerm::Variable(variable)) => {
                    (variable, read)
                }
                _ => return false,
            };
            return crate::kernel::eval::viewed_as_memory_load(&OldMachineTerm::Variable(
                *variable,
            ))
            .as_ref()
                == Some(read);
        };
        let mut pending = vec![(native, root)];
        while let Some((native, shared)) = pending.pop() {
            self.visit();
            if self.checked_work_exhausted() {
                return false;
            }
            let view = MachineOperandView::Old(native);
            match shared.node() {
                KernelTermNode::ThreadHandle(id) => {
                    if *native != OldMachineTerm::ThreadHandle(*id) {
                        return false;
                    }
                }
                KernelTermNode::Match(matched) => {
                    let OldMachineTerm::AlgebraicMatch { scrutinee, arms } = native else {
                        return false;
                    };
                    let mut export = KernelTermExport::default();
                    if export.argument(&matched.arguments[0]).ok()
                        != Some(PureFunctionArgument::Algebraic((**scrutinee).clone()))
                        || arms.len() != matched.arms.len()
                    {
                        return false;
                    }
                    for ((native, arm), body) in
                        arms.iter().zip(&matched.arms).zip(&matched.arguments[1..])
                    {
                        if native.variant != arm.variant
                            || arm.export_bindings(&mut export).ok().as_ref()
                                != Some(&native.bindings)
                        {
                            return false;
                        }
                        pending.push((&native.body, body));
                    }
                }
                KernelTermNode::Variable(variable) => {
                    if view.variable() != Some(variable) {
                        return false;
                    }
                }
                KernelTermNode::MemoryLoad { .. } => {
                    let OldMachineTerm::MemoryLoad(memory, address, kind) =
                        shared.machine_read_leaf().expect("read descriptor")
                    else {
                        unreachable!("read descriptor")
                    };
                    if view.read().is_some_and(|(m, p, k)| {
                        m == memory.shared_memory() && p == address.as_ref() && k == *kind
                    }) {
                        continue;
                    }
                    let variable = view.variable().copied();
                    let KernelType::Program(ty) = shared.ty() else {
                        return false;
                    };
                    let Some(format) = MachineIntegerType::from_program_type(*ty) else {
                        return false;
                    };
                    if variable
                        .and_then(|name| {
                            crate::kernel::eval::registered_scalar_read_term(&name, format)
                        })
                        .as_ref()
                        != Some(shared)
                    {
                        return false;
                    }
                }
                KernelTermNode::MachineLiteral(literal) => {
                    if *native != literal.old_term() {
                        return false;
                    }
                }
                KernelTermNode::MachineIf { arguments } => {
                    let OldMachineTerm::If {
                        condition,
                        then_term,
                        else_term,
                    } = native
                    else {
                        return false;
                    };
                    if KernelTermExport::condition(&arguments[0]).ok().as_ref()
                        != Some(condition.as_ref())
                    {
                        return false;
                    }
                    pending.push((else_term, &arguments[2]));
                    pending.push((then_term, &arguments[1]));
                }
                KernelTermNode::MachineBinary {
                    format,
                    operator,
                    arguments,
                } => {
                    let Some((
                        actual_format,
                        actual_operator,
                        [MachineOperandView::Old(a), MachineOperandView::Old(b)],
                    )) = view.binary()
                    else {
                        return false;
                    };
                    if *format != actual_format || *operator != actual_operator {
                        return false;
                    }
                    pending.push((b, &arguments[1]));
                    pending.push((a, &arguments[0]));
                }
                KernelTermNode::MachineUnary {
                    format,
                    operator,
                    operand,
                } => {
                    let Some((actual_format, actual_operator, MachineOperandView::Old(value))) =
                        view.unary()
                    else {
                        return false;
                    };
                    if *format != actual_format || *operator != actual_operator {
                        return false;
                    }
                    pending.push((value, operand));
                }
                KernelTermNode::MachineCast {
                    encoding,
                    source,
                    destination,
                    operand,
                } => {
                    let Some((
                        actual_encoding,
                        actual_source,
                        actual_destination,
                        MachineOperandView::Old(value),
                    )) = view.cast()
                    else {
                        return false;
                    };
                    if *encoding != actual_encoding
                        || *source != actual_source
                        || *destination != actual_destination
                    {
                        return false;
                    }
                    pending.push((value, operand));
                }
                KernelTermNode::IntegerToMachine { .. }
                | KernelTermNode::BoolCast { .. }
                | KernelTermNode::MachineObservationInput { .. }
                | KernelTermNode::WrittenMachine(_)
                | KernelTermNode::Call { .. }
                | KernelTermNode::IntegerAddress { .. } => {
                    if !shared
                        .machine_conversion_leaf()
                        .is_some_and(|leaf| same_payload(self, leaf, native))
                    {
                        return false;
                    }
                }
                _ => return false,
            }
        }
        true
    }

    pub(crate) fn bits(&mut self, v: &OldMachineTerm) -> OldMachineTerm {
        self.bits_with_match_reduction(v, !MATCH_REDUCTION_SUSPENDED.with(std::cell::Cell::get))
    }

    fn bits_with_match_reduction(
        &mut self,
        v: &OldMachineTerm,
        reduce_match: bool,
    ) -> OldMachineTerm {
        self.reserve_bitvector_variables_once(v);
        if self.checked_work_exhausted() {
            return OldMachineTerm::constant(0);
        }
        self.visit();
        if self.checked_work_exhausted() {
            return OldMachineTerm::constant(0);
        }
        if let OldMachineTerm::Variable(variable) = v
            && let Some(mapped) = self.scope.program_values.get(variable)
        {
            return OldMachineTerm::Variable(*mapped);
        }
        if let OldMachineTerm::Variable(variable) = v
            && let Some(replacements) = &self.typed_variables
            && let Some(TypedProgramValueReplacement::Bitvector(replacement)) =
                replacements.program_values.get(variable)
        {
            self.changed = true;
            return replacement.clone();
        }
        if let Some(reads) = self.comparison_reads
            && let Some(OldMachineTerm::MemoryLoad(memory, pointer, kind)) =
                crate::kernel::eval::viewed_as_memory_load(v)
            && let Some((replacement, variables)) = reads.get(&(
                memory.shared_memory().arena_id(),
                Address::from(pointer),
                kind,
            ))
            && !variables.is_bound_in(&self.scope)
        {
            self.changed = true;
            return replacement.clone();
        }
        if let Some((from, to)) = self.bitvector
            && !self.source_disabled
            && self.matches_machine_source(v, from)
        {
            self.changed = true;
            // Native output carriers still require a written machine term.
            // Shared observation rewrites replace the retained node directly
            // before entering this legacy-output construction.
            return match to {
                MachineOperandView::Old(term) => term.clone(),
                MachineOperandView::Shared(root) => {
                    KernelTermExport::machine(root).expect("shared machine replacement")
                }
            };
        }
        if self.resolve_registered_loads
            && let OldMachineTerm::Variable(variable) = v
            && crate::kernel::is_load_variable(variable)
        {
            // Keep the load's state exact and rewrite only its selected
            // address.  Re-materializing the registered variable would hide
            // a binder-dependent pointer from the fold substitution, while
            // scanning or rewriting the memory state would change an
            // unrelated proof-state value.
            if let Some(rewritten) = self.rewrite_registered_load(*variable) {
                // Substituting the binder can turn a binder-dependent address
                // into one this very state already materializes. The load
                // is then that cell's content, and leaving a fresh load
                // identity in its place would hide from the proof the value
                // the store it names just wrote.
                if rewritten != *variable
                    && let Some(value) = materialized_registered_load_value(rewritten)
                {
                    self.changed = true;
                    return value;
                }
                return if self.comparison_arithmetic {
                    crate::kernel::registered_load_term_for_variable(&rewritten)
                        .unwrap_or(OldMachineTerm::Variable(rewritten))
                } else {
                    OldMachineTerm::Variable(rewritten)
                };
            }
            if self.checked_work_exhausted() {
                return OldMachineTerm::constant(0);
            }
            if self.unsupported_integer_scope {
                return OldMachineTerm::Variable(*variable);
            }
        }
        let result = match v {
            OldMachineTerm::Cast {
                spelling: MachineCastSpelling::Generic,
                value,
                from: source,
                to: destination,
            } => {
                let original = value;
                let value = self.bits(value);
                if self.integer_exact.is_some() {
                    // Exact Integer congruence preserves native syntax. Folding
                    // an unrelated cast changes the opaque observation's ID.
                    OldMachineTerm::Cast {
                        spelling: MachineCastSpelling::Generic,
                        value: Box::new(value),
                        from: *source,
                        to: *destination,
                    }
                } else if let Some(carrier) =
                    self.widened_narrowed_cast_carrier(original, &value, *source, *destination)
                {
                    carrier
                } else {
                    OldMachineTerm::machine_integer_cast(*source, *destination, value)
                }
            }

            OldMachineTerm::ThreadHandle(_)
            | OldMachineTerm::Constant { .. }
            | OldMachineTerm::Variable(_) => v.clone(),
            cast_term!(UInt32From64, v) => {
                let value = self.bits(v);
                if self.integer_exact.is_some() {
                    OldMachineTerm::legacy_cast(MachineCastSpelling::UInt32From64, Box::new(value))
                } else {
                    OldMachineTerm::uint32_from_64(value)
                }
            }
            OldMachineTerm::If {
                condition,
                then_term,
                else_term,
            } => {
                if let Some(conditions) = &mut self.collected_conditions {
                    conditions.push(condition.as_ref().clone());
                }
                // Binder substitution preserves a retained closed guard. Ordinary
                // computation can still decide it before walking an unselected arm.
                let preserve = self.preserves_machine_conditional(condition);
                let condition = self.condition(condition);
                let condition = if preserve {
                    condition
                } else {
                    folded_machine_condition(condition)
                };
                if !preserve && let OldConditionTerm::Constant(value) = condition {
                    return self.bits(if value { then_term } else { else_term });
                }
                let then_term = self.bits(then_term);
                let else_term = self.bits(else_term);
                if !preserve {
                    return OldMachineTerm::if_then_else(condition, then_term, else_term);
                }
                OldMachineTerm::If {
                    condition: Box::new(condition),
                    then_term: Box::new(then_term),
                    else_term: Box::new(else_term),
                }
            }
            OldMachineTerm::RangeFold {
                start,
                end,
                initial,
                accumulator,
                item,
                body,
            } => {
                self.reserve_bitvector_scope_variables(v);
                if self.checked_work_exhausted() {
                    return OldMachineTerm::constant(0);
                }
                let start = self.bits(start);
                if self.checked_work_exhausted() {
                    return OldMachineTerm::constant(0);
                }
                let end = self.bits(end);
                if self.checked_work_exhausted() {
                    return OldMachineTerm::constant(0);
                }
                let initial = self.bits(initial);
                if self.checked_work_exhausted() {
                    return OldMachineTerm::constant(0);
                }
                let saved_scope_id = self.scope_id;
                let saved_shadowed = self.integer_shadowed;
                let mut changes = Vec::new();
                let Some(accumulator) = self.rewrite_program_binder(*accumulator, &mut changes)
                else {
                    self.restore_scope(&changes, saved_scope_id, saved_shadowed);
                    return OldMachineTerm::constant(0);
                };
                let Some(item) = self.rewrite_program_binder(*item, &mut changes) else {
                    self.restore_scope(&changes, saved_scope_id, saved_shadowed);
                    return OldMachineTerm::constant(0);
                };
                let body = if self.conditions.is_some() {
                    body.clone()
                } else {
                    Box::new(self.bits(body))
                };
                self.restore_scope(&changes, saved_scope_id, saved_shadowed);
                if self.checked_work_exhausted() {
                    return OldMachineTerm::constant(0);
                }
                OldMachineTerm::RangeFold {
                    start: Box::new(start),
                    end: Box::new(end),
                    initial: Box::new(initial),
                    accumulator,
                    item,
                    body,
                }
            }
            OldMachineTerm::PureFunctionApplication { name, arguments } => {
                let mut rewritten = Vec::with_capacity(arguments.len());
                for argument in arguments {
                    rewritten.push(self.bits(argument));
                    if self.checked_work_exhausted() {
                        return OldMachineTerm::constant(0);
                    }
                }
                OldMachineTerm::rebuild_pure_application(name.clone(), rewritten)
            }
            OldMachineTerm::ClickFunctionApplication { name, arguments } => {
                let mut rewritten = Vec::with_capacity(arguments.len());
                for argument in arguments {
                    rewritten.push(self.argument(argument));
                    if self.checked_work_exhausted() {
                        return OldMachineTerm::constant(0);
                    }
                }
                OldMachineTerm::ClickFunctionApplication {
                    name: name.clone(),
                    arguments: rewritten,
                }
            }
            OldMachineTerm::AlgebraicMatch { scrutinee, arms } => {
                self.reserve_bitvector_scope_variables(v);
                if self.checked_work_exhausted() {
                    return OldMachineTerm::constant(0);
                }
                let scrutinee = self.algebraic(scrutinee);
                if self.checked_work_exhausted() {
                    return OldMachineTerm::constant(0);
                }
                let mut rewritten_arms = Vec::with_capacity(arms.len());
                for arm in arms {
                    let saved_scope_id = self.scope_id;
                    let saved_shadowed = self.integer_shadowed;
                    let mut changes = Vec::new();
                    let mut bindings = arm.bindings.clone();
                    if !self.rewrite_match_bindings(&mut bindings, &mut changes) {
                        self.restore_scope(&changes, saved_scope_id, saved_shadowed);
                        return OldMachineTerm::constant(0);
                    }
                    let body = if self.conditions.is_some() {
                        arm.body.clone()
                    } else {
                        self.bits(&arm.body)
                    };
                    self.restore_scope(&changes, saved_scope_id, saved_shadowed);
                    if self.checked_work_exhausted() {
                        return OldMachineTerm::constant(0);
                    }
                    rewritten_arms.push(AlgebraicBitvectorMatchArm {
                        binding_names: arm.binding_names.clone(),
                        variant: arm.variant.clone(),
                        bindings,
                        body,
                    });
                }
                if reduce_match
                    && let Some(value) =
                        self.rewrite_bitvector_match_iota(&scrutinee, &rewritten_arms)
                {
                    return value;
                }
                OldMachineTerm::AlgebraicMatch {
                    scrutinee: Box::new(scrutinee),
                    arms: rewritten_arms,
                }
            }
            OldMachineTerm::MemoryLoad(memory, pointer, kind) => {
                let rewritten = self.pointer(pointer);
                if rewritten == **pointer {
                    return v.clone();
                }
                if let Some(entry) = memory.entry_version_after_rewrite(&rewritten, *kind) {
                    return crate::kernel::eval::scalar_read_for_exact_cell_at(
                        &entry,
                        &rewritten,
                        *kind,
                        kind.byte_width(),
                    );
                }
                // A changed bound index, like a changed pointer, must read
                // its new cell in the producer state. A projected version
                // only describes the original address.
                let use_origin = self.resolve_registered_loads;
                let observation =
                    crate::kernel::eval::scalar_read_observation(MachineOperandView::Old(v));
                let bytes = observation
                    .as_ref()
                    .map(|read| read.bytes)
                    .unwrap_or_else(|| {
                        crate::kernel::load_term_access_width(
                            memory.shared_memory(),
                            pointer,
                            *kind,
                        )
                    });
                // Exact reads keep their written point. A pointer equality
                // can also keep the point of an indexed store read.
                // The store receipt applies only to the original address.
                let indexed_store_read =
                    self.pointer_exact.is_some() && memory.indexed_stored_value().is_some();
                if (memory.is_exact_read() || indexed_store_read)
                    && memory.has_certified_read_view()
                {
                    return crate::kernel::eval::scalar_read_for_exact_cell_at(
                        &memory.point().clone().for_exact_read(),
                        &rewritten,
                        *kind,
                        bytes,
                    );
                }
                // A projection belongs to the selected address. Instantiating
                // an index must select the new address from that projection's
                // recorded source, as direct lowering does. This is one indexed
                // lookup, independent of facts and memory-history length.
                if !use_origin
                    && let Some(source) = crate::kernel::prelude::canonical_load_projection_source(
                        memory.shared_memory(),
                        pointer,
                    )
                {
                    crate::kernel::eval::record_load_access_width(
                        source.memory(),
                        &rewritten,
                        bytes,
                    );
                    return crate::kernel::eval::canonical_term(
                        &crate::kernel::OldMachineTerm::read_named(
                            ProgramPoint::walked(&source, memory.point()),
                            rewritten,
                            *kind,
                        ),
                    );
                }
                let source_point = observation
                    .filter(|_| use_origin)
                    .and_then(|read| read.origin)
                    .unwrap_or_else(|| memory.point().clone());
                let memory = source_point.shared_memory().clone();
                if self.resolve_registered_loads
                    && let Some(value) = memory
                        .memory()
                        .known_value(&rewritten)
                        .and_then(|value| kind.read_cell(&value))
                        .and_then(|value| crate::kernel::spec::program_value_bitvector_term(&value))
                {
                    self.changed = true;
                    return value;
                }
                // Re-project the producer at the new address, retaining its
                // effect markers. A version selection for the symbolic
                // intermediate address can forget an effect before a later
                // substitution finishes instantiating that address.
                let memory = if use_origin
                    && self.pointer_variable.is_none()
                    && self.pointer_exact.is_none()
                    && self.pointer_offset_exact.is_none()
                {
                    crate::kernel::memory_history::canonical_projected_load_memory(
                        &memory, &rewritten,
                    )
                } else {
                    memory
                };
                crate::kernel::eval::scalar_read_for_exact_cell_at(
                    &ProgramPoint::viewing(&memory, &source_point),
                    &rewritten,
                    *kind,
                    bytes,
                )
            }
            OldMachineTerm::IntegerAddress(pointer, class) => {
                OldMachineTerm::object_pointer_address(self.pointer(pointer), class.class())
            }
            OldMachineTerm::IntegerToMachine { value, destination } => {
                OldMachineTerm::IntegerToMachine {
                    value: self.integer_shared(value).into(),
                    destination: *destination,
                }
            }
            // Rule C1: the cast of the rewritten `Bool`, folded when the
            // rewrite decided it. The `Bool` guards its cast's value.
            OldMachineTerm::BoolCast { to, value } => {
                if let Some(conditions) = &mut self.collected_conditions
                    && !matches!(value.as_ref(), OldConditionTerm::Constant(_))
                {
                    conditions.push(value.as_ref().clone());
                }
                let value = self.condition(value);
                if self.integer_exact.is_some() {
                    OldMachineTerm::BoolCast {
                        to: *to,
                        value: Box::new(value),
                    }
                } else {
                    OldMachineTerm::bool_cast(*to, folded_machine_condition(value))
                }
            }
            term => match (term.as_binary(), term.as_unary()) {
                (Some((op, left, right)), _) if self.comparison_arithmetic => {
                    let left = self.bits(left);
                    let right = self.bits(right);
                    if let crate::kernel::BitvectorBinaryOp::Machine(
                        format,
                        MachineBinaryOp::Subtract,
                    ) = op
                        && left == right
                    {
                        crate::kernel::machine_integer::range::constant_word(format, &0.into())
                            .expect("zero fits every machine format")
                    } else if matches!(
                        op,
                        crate::kernel::BitvectorBinaryOp::Machine(
                            _,
                            MachineBinaryOp::Add
                                | MachineBinaryOp::Subtract
                                | MachineBinaryOp::Multiply
                                | MachineBinaryOp::Divide
                                | MachineBinaryOp::Remainder
                                | MachineBinaryOp::ShiftLeft
                                | MachineBinaryOp::ShiftRight
                        )
                    ) {
                        op.build(left, right)
                    } else {
                        op.build_raw(left, right)
                    }
                }
                (Some((op, left, right)), _) => op.build_raw(self.bits(left), self.bits(right)),
                // A width conversion of a substituted constant is that
                // constant in the destination type, as for the casts above.
                (_, Some((op, value)))
                    if op.is_width_conversion() && self.integer_exact.is_none() =>
                {
                    op.build(self.bits(value))
                }
                (_, Some((op, value))) => op.build_raw(self.bits(value)),
                _ => unreachable!("every other variant has its own arm"),
            },
        };
        if let Some((guards, replacement)) = result.guarded_remainder_rewrite() {
            if let Some(conditions) = &mut self.collected_conditions {
                conditions.extend(guards.iter().cloned());
            }
            if self.conditions.is_some_and(|conditions| {
                guards.iter().all(|guard| {
                    *guard == OldConditionTerm::Constant(true)
                        || conditions.get(guard) == Some(&true)
                })
            }) {
                return replacement;
            }
        }
        if self.checked_work_exhausted() {
            OldMachineTerm::constant(0)
        } else {
            result
        }
    }
}

/// A checked pointer rewrite may expose a constant `IntegerToMachine` cast
/// after witness substitution. Pointer offsets use the canonical constant
/// form, while ordinary Integer-to-machine observations remain symbolic so
/// their surrounding range obligations are still visible to proof checking.
fn canonicalize_integer_to_machine_constant(value: OldMachineTerm) -> OldMachineTerm {
    let OldMachineTerm::IntegerToMachine { value, destination } = value else {
        return value;
    };
    let Some(constant) = value.as_ref().as_const() else {
        return OldMachineTerm::IntegerToMachine { value, destination };
    };
    let converted = MachineIntegerConstant::from_integer(destination.format(), constant)
        .and_then(|value| destination.constant_term(value));
    converted.unwrap_or(OldMachineTerm::IntegerToMachine { value, destination })
}

#[cfg(test)]
#[path = "term_rewrite/registered_load_tests.rs"]
mod registered_load_tests;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::{
        AlgebraicSchemas, AlgebraicType, AlgebraicValueType, AlgebraicVariantType,
    };

    #[test]
    fn shared_pointer_index_reconstruction_matches_native_rules() {
        let _session = VerificationSession::enter();
        let source = OldMachineTerm::Variable(Variable(1007300));
        let target = OldMachineTerm::Variable(Variable(1007301));
        for ty in [
            MachineIntegerType::Int32,
            MachineIntegerType::Int64,
            MachineIntegerType::UInt64,
        ] {
            let mut cases = vec![OldMachineTerm::Binary {
                format: ty,
                op: MachineBinaryOp::Add,
                left: source.clone().into(),
                right: source.clone().into(),
            }];
            if ty == MachineIntegerType::Int64 {
                let widened = OldMachineTerm::int64_from_32(OldMachineTerm::add(
                    source.clone(),
                    source.clone(),
                ));
                cases.push(widened.clone());
                cases.push(OldMachineTerm::int64_multiply(
                    widened,
                    OldMachineTerm::int64_constant(3),
                ));
            }
            for native in cases {
                for resolving in [false, true] {
                    for stride in [0, 4, -4] {
                        let container = if ty == MachineIntegerType::Int32 {
                            ty
                        } else {
                            MachineIntegerType::Int64
                        };
                        let root = KernelTermImport::default()
                            .machine_arithmetic(container, &native)
                            .unwrap();
                        let value = SharedMachineIntegerTerm::from_shared(container, root).unwrap();
                        let offset = if ty == MachineIntegerType::Int32 {
                            AddressOffset::int32_scaled(value, stride)
                        } else {
                            AddressOffset::int64_scaled(
                                value,
                                stride,
                                ty == MachineIntegerType::UInt64,
                            )
                        };
                        let mut reference = TermRewrite::for_bits_checked(&source, &target);
                        reference.resolve_registered_loads = resolving;
                        let expected = reference.bits(&native);
                        let expected = match (ty, resolving) {
                            (MachineIntegerType::Int32, false) => {
                                AddressOffset::scaled_int32_node(expected, stride)
                            }
                            (MachineIntegerType::Int32, true) => {
                                AddressOffset::scale_int32(expected, stride)
                            }
                            (_, false) => AddressOffset::scaled_int64_node(
                                expected,
                                stride,
                                ty == MachineIntegerType::UInt64,
                            ),
                            (_, true) => AddressOffset::scale_int64(
                                expected,
                                stride,
                                ty == MachineIntegerType::UInt64,
                            ),
                        };
                        let before = KernelTermExport::machine_export_count();
                        let mut rewrite = TermRewrite::for_bits_checked(&source, &target);
                        rewrite.resolve_registered_loads = resolving;
                        let actual = rewrite.offset(&offset.clone());
                        assert!(rewrite.refusal().is_none());
                        assert_eq!(KernelTermExport::machine_export_count(), before);
                        assert_eq!(actual, expected, "{ty:?}, {stride}, resolving={resolving}");
                    }
                }
            }
        }
    }

    #[test]
    fn shared_unsigned_index_narrowing_requires_the_original_bound() {
        let _session = VerificationSession::enter();
        let native = OldMachineTerm::uint64_add(
            OldMachineTerm::Variable(Variable(1007310)),
            OldMachineTerm::uint64_constant(1),
        );
        let root = KernelTermImport::default()
            .machine_arithmetic(MachineIntegerType::Int64, &native)
            .unwrap();
        let offset = AddressOffset::int64_scaled(
            SharedMachineIntegerTerm::from_shared(MachineIntegerType::Int64, root).unwrap(),
            4,
            true,
        );
        for limit in [i32::MAX as u64, i32::MAX as u64 + 1] {
            let conditions = HashMap::from([(
                OldConditionTerm::uint64_less_equal(
                    native.clone(),
                    OldMachineTerm::uint64_constant(limit),
                ),
                true,
            )]);
            let mut rewrite = TermRewrite::for_conditions(&conditions);
            let before = KernelTermExport::machine_export_count();
            let actual = rewrite.offset(&offset.clone());
            assert_eq!(KernelTermExport::machine_export_count(), before);
            assert_eq!(
                matches!(actual.view(), crate::kernel::OffsetView::Int32Scaled { .. }),
                limit == i32::MAX as u64
            );
        }
    }

    #[test]
    fn signed_byte_offset_constants_fold_only_inside_their_range() {
        for value in [-129, -128, -1, 0, 127, 128] {
            let input = OldMachineTerm::IntegerToMachine {
                value: IntegerTerm::constant_i64(value).into(),
                destination: MachineIntegerType::Int8,
            };
            let expected = if (-128..=127).contains(&value) {
                OldMachineTerm::narrow_constant(MachineIntegerType::Int8, value as i8 as u8 as u128)
            } else {
                input.clone()
            };
            assert_eq!(canonicalize_integer_to_machine_constant(input), expected);
        }
    }

    #[test]
    fn conditional_reduction_does_not_use_outer_facts_under_a_binder() {
        let variable = Variable(51);
        let condition = OldConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::Equal,
            left: Box::new(OldMachineTerm::Variable(variable)),
            right: Box::new(OldMachineTerm::constant(0)),
        };
        let conditions = HashMap::from([(condition.clone(), true)]);
        let input = OldMachineTerm::RangeFold {
            start: Box::new(OldMachineTerm::constant(0)),
            end: Box::new(OldMachineTerm::constant(2)),
            initial: Box::new(OldMachineTerm::constant(0)),
            accumulator: Variable(52),
            item: variable,
            body: Box::new(OldMachineTerm::If {
                condition: Box::new(condition),
                then_term: Box::new(OldMachineTerm::constant(7)),
                else_term: Box::new(OldMachineTerm::constant(0)),
            }),
        };
        assert_eq!(TermRewrite::for_conditions(&conditions).bits(&input), input);
    }

    #[test]
    fn mixed_algebraic_rewrite_visits_scale_with_the_selected_expression() {
        let variants: std::sync::Arc<[AlgebraicVariantType]> = vec![AlgebraicVariantType {
            name: "Unit".into(),
            fields: vec![],
        }]
        .into();
        let algebraic_type = AlgebraicType {
            rigid: false,
            name: "Marker".into(),
            arguments: vec![],
            variants: variants.clone(),
            schemas: std::sync::Arc::new(AlgebraicSchemas::new(BTreeMap::from([(
                AlgebraicValueType::Algebraic {
                    name: "Marker".into(),
                    arguments: vec![],
                },
                variants,
            )]))),
        };
        let from = AlgebraicTerm {
            algebraic_type: algebraic_type.clone(),
            node: AlgebraicTermNode::Variable(Variable(51)),
        };
        let to = AlgebraicTerm {
            algebraic_type,
            node: AlgebraicTermNode::Variable(Variable(52)),
        };
        for size in [16, 64, 256] {
            let argument = |value: &AlgebraicTerm| {
                PureFunctionArgument::Value(ProgramValue::Int32(
                    OldMachineTerm::ClickFunctionApplication {
                        name: "observe".into(),
                        arguments: vec![PureFunctionArgument::Algebraic(value.clone())],
                    },
                ))
            };
            let input = Term::Bitvector32(
                OldMachineTerm::ClickFunctionApplication {
                    name: "many".into(),
                    arguments: vec![argument(&from); size],
                }
                .into(),
            );
            let expected = Term::Bitvector32(
                OldMachineTerm::ClickFunctionApplication {
                    name: "many".into(),
                    arguments: vec![argument(&to); size],
                }
                .into(),
            );
            let mut rewrite = TermRewrite::new(&from, &to);
            assert_eq!(rewrite.term(&input), expected);
            assert!(rewrite.changed);
            assert_eq!(rewrite.visits, 2 + 2 * size);
        }
    }

    #[test]
    fn truncating_integer_rewrite_preserves_sharing_and_substitutes_variables() {
        let variable = Variable(65001);
        let replacement = IntegerTerm::var(Variable(65002));
        for depth in [2usize, 8, 32, 128] {
            let mut expression = IntegerTerm::var(variable);
            for level in 0..depth {
                let child: SharedIntegerTerm = expression.into();
                expression = if level % 2 == 0 {
                    IntegerTerm::TruncatingQuotient(child.clone(), child)
                } else {
                    IntegerTerm::TruncatingRemainder(child.clone(), child)
                };
            }
            let input = Term::Integer(expression.into());
            let renamings = BTreeMap::new();
            let mut rewrite =
                TermRewrite::for_integer_variables(variable, &replacement, false, &renamings);
            let Term::Integer(output) = rewrite.term(&input) else {
                unreachable!()
            };
            assert!(rewrite.visits <= 2 * depth + 8);
            let mut node: SharedIntegerTerm = output.into_native_compat().into();
            for _ in 0..depth {
                let (a, b) = match node.as_ref() {
                    IntegerTerm::TruncatingQuotient(a, b)
                    | IntegerTerm::TruncatingRemainder(a, b) => (a, b),
                    _ => unreachable!(),
                };
                assert_eq!(a.id(), b.id());
                node = a.clone();
            }
            assert_eq!(node.as_ref(), &replacement);
        }
    }

    #[test]
    fn truncating_integer_rewrite_freshens_colliding_fold_binders() {
        let source = Variable(65003);
        let accumulator = Variable(65004);
        let item = Variable(65005);
        for remainder in [false, true] {
            let a = IntegerTerm::var(source).into();
            let b = IntegerTerm::var(accumulator).into();
            let body = if remainder {
                IntegerTerm::TruncatingRemainder(a, b)
            } else {
                IntegerTerm::TruncatingQuotient(a, b)
            };
            let fold = IntegerTerm::range_fold(
                crate::kernel::IntegerRangeFoldIndex::Integer {
                    start: IntegerTerm::constant_i64(0).into(),
                    end: IntegerTerm::constant_i64(2).into(),
                },
                IntegerTerm::constant_i64(0),
                accumulator,
                item,
                body,
            );
            let program_values = BTreeMap::new();
            let integers = BTreeMap::from([(source, IntegerTerm::var(accumulator))]);
            let algebraic = BTreeMap::new();
            let mut rewrite =
                TermRewrite::for_typed_variables(&program_values, &integers, &algebraic);
            let term_source_0 @ Term::Integer(_) = rewrite.term(&Term::Integer(fold.into())) else {
                unreachable!()
            };
            let (Some(IntegerTerm::RangeFold {
                accumulator: renamed,
                body,
                ..
            }),) = (term_source_0.integer_native(),)
            else {
                unreachable!()
            };
            assert_ne!(*renamed, accumulator);
            let (a, b) = match body.as_ref() {
                IntegerTerm::TruncatingQuotient(a, b) | IntegerTerm::TruncatingRemainder(a, b) => {
                    (a, b)
                }
                _ => unreachable!(),
            };
            assert_eq!(a.as_ref(), &IntegerTerm::var(accumulator));
            assert_eq!(b.as_ref(), &IntegerTerm::var(*renamed));
        }
    }

    #[test]
    fn integer_rewrite_preserves_product_identities_and_scales() {
        let x = IntegerTerm::from_machine(
            MachineIntegerType::UInt32,
            OldMachineTerm::Variable(Variable(65006)),
        )
        .unwrap();
        let y = IntegerTerm::var(Variable(65007));
        let source: SharedIntegerTerm = x.clone().into();
        for identity in [0, 1] {
            let replacement = IntegerTerm::constant_i64(identity);
            let target: SharedIntegerTerm = replacement.clone().into();
            for (left, right) in [(x.clone(), y.clone()), (y.clone(), x.clone())] {
                let mut rewrite = TermRewrite::for_integer_exact(&source, &target);
                let input = Term::Integer(IntegerTerm::Multiply(left.into(), right.into()).into());
                let expected = match &input {
                    term_source_0 @ Term::Integer(_)
                        if let Some(IntegerTerm::Multiply(a, b)) =
                            term_source_0.integer_native() =>
                    {
                        IntegerTerm::Multiply(
                            if a == &source {
                                target.clone()
                            } else {
                                a.clone()
                            },
                            if b == &source {
                                target.clone()
                            } else {
                                b.clone()
                            },
                        )
                    }
                    _ => unreachable!(),
                };
                assert_eq!(rewrite.term(&input), Term::Integer(expected.into()));
                assert!(rewrite.changed);
                assert!(rewrite.refusal().is_none());
            }
            for depth in [8usize, 16, 32, 64] {
                let mut expression = x.clone();
                for _ in 0..depth {
                    let child: SharedIntegerTerm = expression.into();
                    expression = IntegerTerm::Multiply(child.clone(), child);
                }
                let mut rewrite = TermRewrite::for_integer_exact(&source, &target);
                let mut expected = replacement.clone();
                for _ in 0..depth {
                    let child: SharedIntegerTerm = expected.into();
                    expected = IntegerTerm::Multiply(child.clone(), child);
                }
                assert_eq!(
                    rewrite.term(&Term::Integer(expression.into())),
                    Term::Integer(expected.into())
                );
                assert!(rewrite.changed);
                assert!(rewrite.refusal().is_none());
                assert!(
                    rewrite.visits <= depth + 4,
                    "depth {depth}: {} visits",
                    rewrite.visits
                );
            }
        }
    }

    #[test]
    fn integer_rewrite_preserves_shared_repeated_squaring() {
        for depth in [8, 16, 32, 64] {
            let mut expression = IntegerTerm::constant_i64(2);
            for _ in 0..depth {
                let child: SharedIntegerTerm = expression.into();
                expression = IntegerTerm::Multiply(child.clone(), child);
            }
            let input = Term::Integer(expression.into());
            let conditions = HashMap::new();
            let mut rewrite = TermRewrite::for_conditions(&conditions);
            let Term::Integer(output) = rewrite.term(&input) else {
                unreachable!()
            };
            assert_eq!(&Term::Integer(output.clone()), &input);
            let root: SharedIntegerTerm = output.into_native_compat().into();
            let mut pending = vec![root];
            let mut seen = std::collections::BTreeSet::new();
            while let Some(node) = pending.pop() {
                if !seen.insert(node.id()) {
                    continue;
                }
                if let IntegerTerm::Multiply(left, right) = node.as_ref() {
                    pending.push(left.clone());
                    pending.push(right.clone());
                }
            }
            assert_eq!(seen.len(), depth + 1);
            assert!(rewrite.visits <= depth + 4);
        }
    }

    #[test]
    fn integer_to_machine_rewrite_descends_nested_math_payload() {
        let payload = SharedIntegerTerm::from(IntegerTerm::Machine(
            crate::kernel::SharedMachineIntegerTerm::intern(
                crate::kernel::MachineIntegerType::Int32,
                OldMachineTerm::Variable(Variable(880)),
            ),
        ));
        let input = Term::Bitvector32(
            OldMachineTerm::IntegerToMachine {
                value: payload,
                destination: crate::kernel::MachineIntegerType::UInt32,
            }
            .into(),
        );
        let from = OldMachineTerm::Variable(Variable(880));
        let to = OldMachineTerm::Variable(Variable(881));
        let mut rewrite = TermRewrite::for_bits(&from, &to);
        let output = rewrite.term(&input);
        assert!(
            matches!(&(output), term_source_0 @ Term::Bitvector32(_) if matches!((term_source_0.bitvector_native(),), (Some(OldMachineTerm::IntegerToMachine {
            destination: crate::kernel::MachineIntegerType::UInt32,
            value,
        }),) if matches!(value.as_ref(), IntegerTerm::Machine(machine)
            if machine.value() == &OldMachineTerm::Variable(Variable(881)))))
        );
    }

    #[test]
    fn retained_contract_offset_rewrite_preserves_index_rules() {
        let _session = VerificationSession::enter();
        let variable = OldMachineTerm::Variable(Variable(3_103_905));
        for (replacement, wide) in [
            (OldMachineTerm::constant(u32::MAX), None),
            (OldMachineTerm::int64_constant(-1), Some(false)),
            (OldMachineTerm::uint64_constant(1 << 63), Some(true)),
            (
                OldMachineTerm::PureFunctionApplication {
                    name: "opaque_index".into(),
                    arguments: vec![],
                },
                None,
            ),
        ] {
            let index = match wide {
                None => AddressOffset::scaled_int32_node(variable.clone(), 4),
                Some(unsigned) => AddressOffset::scaled_int64_node(variable.clone(), 8, unsigned),
            };
            let native = AddressOffset::raw_add(AddressOffset::constant(0), index);
            let input = StoredPointerOffset::from(native.clone());
            for resolve_registered_loads in [false, true] {
                let rewrite = || {
                    let mut rewrite = TermRewrite::for_bits_checked(&variable, &replacement);
                    if resolve_registered_loads {
                        rewrite.enable_registered_load_resolution();
                    }
                    rewrite
                };
                let mut reference = rewrite();
                let expected = reference.offset(&native.clone());
                let mut retained = rewrite();
                let Term::PointerOffset(actual) =
                    retained.term(&Term::PointerOffset(input.clone()))
                else {
                    unreachable!();
                };
                assert_eq!(retained.refusal(), reference.refusal());
                assert_eq!(retained.changed, reference.changed);
                assert!(!input.has_cached_native_offset());
                assert!(!actual.has_cached_native_offset());
                assert_eq!(actual.old_form(), &expected);
            }
        }
    }

    #[test]
    fn retained_contract_offset_uses_the_same_unsigned_narrowing_and_work_refusal() {
        let _session = VerificationSession::enter();
        let variable = OldMachineTerm::Variable(Variable(3_103_906));
        let native = AddressOffset::scaled_int64_node(variable.clone(), 8, true);
        let input = StoredPointerOffset::from(native.clone());
        let conditions = HashMap::from([(
            OldConditionTerm::Compare {
                format: MachineIntegerType::UInt64,
                relation: CompareRelation::LessEqual,
                left: Box::new(variable.clone()),
                right: Box::new(OldMachineTerm::uint64_constant(i32::MAX as u64)),
            },
            true,
        )]);
        let expected = TermRewrite::for_conditions(&conditions).offset(&native);
        assert!(matches!(
            expected.clone().view(),
            crate::kernel::OffsetView::Int32Scaled { byte_width: 8, .. }
        ));
        let Term::PointerOffset(actual) =
            TermRewrite::for_conditions(&conditions).term(&Term::PointerOffset(input.clone()))
        else {
            unreachable!();
        };
        assert!(!input.has_cached_native_offset());
        assert_eq!(actual.old_form(), &expected);

        let refused = with_checked_simple_budget(4, || {
            let replacement = OldMachineTerm::Variable(Variable(3_103_907));
            let mut rewrite = TermRewrite::for_bits_checked(&variable, &replacement);
            rewrite.term(&Term::PointerOffset(input.clone()));
            rewrite.refusal()
        });
        assert_eq!(refused, Some(RewriteRefusal::WorkExhausted));
        assert!(!input.has_cached_native_offset());
    }

    #[test]
    fn checked_integer_witness_keeps_out_of_range_pointer_cast_wrapped() {
        let source = Variable(3_103_901);
        let replacement = IntegerTerm::constant_i64(2_147_483_648);
        let renamings = BTreeMap::new();
        let mut rewrite =
            TermRewrite::for_integer_variables(source, &replacement, false, &renamings);
        rewrite.enable_registered_load_resolution();
        let offset = AddressOffset::scaled_int32_node(
            OldMachineTerm::IntegerToMachine {
                value: IntegerTerm::var(source).into(),
                destination: MachineIntegerType::Int32,
            },
            4,
        );
        let rewritten = rewrite.term(&Term::PointerOffset(offset.into()));
        assert!(matches!(
            rewritten,
            Term::PointerOffset(offset)
                if matches!(offset.old_form().view(), crate::kernel::OffsetView::Int32Scaled { index: value, .. } if matches!(value.structural_value(), OldMachineTerm::IntegerToMachine {
                    value,
                    destination: MachineIntegerType::Int32,
                } if value.as_ref().as_const().and_then(|value| value.to_i64())
                    == Some(2_147_483_648)))
        ));
    }

    #[test]
    fn checked_integer_witness_keeps_symbolic_pointer_cast_wrapped() {
        let source = Variable(3_103_902);
        let replacement = IntegerTerm::var(Variable(3_103_903));
        let renamings = BTreeMap::new();
        let mut rewrite =
            TermRewrite::for_integer_variables(source, &replacement, false, &renamings);
        rewrite.enable_registered_load_resolution();
        let offset = AddressOffset::scaled_int32_node(
            OldMachineTerm::IntegerToMachine {
                value: IntegerTerm::var(source).into(),
                destination: MachineIntegerType::Int32,
            },
            4,
        );
        let rewritten = rewrite.term(&Term::PointerOffset(offset.into()));
        assert!(matches!(
            rewritten,
            Term::PointerOffset(offset)
                if matches!(offset.old_form().view(), crate::kernel::OffsetView::Int32Scaled { index: value, .. } if matches!(value.structural_value(), OldMachineTerm::IntegerToMachine {
                    value,
                    destination: MachineIntegerType::Int32,
                } if matches!(value.as_ref(), IntegerTerm::Variable(variable) if *variable == Variable(3_103_903))))
        ));
    }

    #[test]
    fn checked_integer_witness_canonicalizes_negative_pointer_cast_constant() {
        let source = Variable(3_103_904);
        let replacement = IntegerTerm::constant_i64(-1);
        let renamings = BTreeMap::new();
        let mut rewrite =
            TermRewrite::for_integer_variables(source, &replacement, false, &renamings);
        rewrite.enable_registered_load_resolution();
        let offset = AddressOffset::scaled_int32_node(
            OldMachineTerm::IntegerToMachine {
                value: IntegerTerm::var(source).into(),
                destination: MachineIntegerType::Int32,
            },
            4,
        );
        let rewritten = rewrite.term(&Term::PointerOffset(offset.into()));
        assert_eq!(
            rewritten,
            Term::PointerOffset(AddressOffset::constant(-4).into())
        );
    }

    #[test]
    fn array_ref_rewrite_preserves_opaque_memory_and_ignores_unrelated_blocks() {
        let source = Variable(9880);
        let replacement = Address::new(
            AddressBase::Symbolic(Variable(9881)),
            AddressOffset::constant(3),
        );
        let expected_pointer = replacement.with_offset(AddressOffset::constant(4));
        let input_pointer = Address::new(AddressBase::Symbolic(source), AddressOffset::constant(1));
        let memory_with_unrelated_blocks = |count: u64| {
            let mut memory = SymbolicMemory::new().with_block("array", 8);
            for index in 0..count {
                memory = memory.with_block(AddressBase::Heap(index + 1), 8);
            }
            memory
        };
        let observed_array = |memory: SymbolicMemory, pointer: Address| {
            Term::Integer(
                IntegerTerm::PureFunctionApplication(SharedPureApplication::intern(
                    "observe_array".into(),
                    vec![PureFunctionArgument::ArrayRef {
                        point: crate::kernel::ProgramPoint::of_memory(&memory),
                        pointer: ProgramValue::Pointer(OldPointer::new(
                            pointer,
                            ProgramType::VoidPointer,
                        )),
                        element_type: ProgramType::UInt8,
                    }],
                ))
                .into(),
            )
        };
        let rewrite = |term: &Term| {
            let mut walker = TermRewrite::for_pointer_variable(source, &replacement);
            walker.term(term)
        };
        let small_memory = memory_with_unrelated_blocks(0);
        let large_memory = memory_with_unrelated_blocks(256);
        let small_input = observed_array(small_memory.clone(), input_pointer.clone());
        let large_input = observed_array(large_memory.clone(), input_pointer);
        let (small, small_work) =
            crate::instrumentation::measure_deterministic_work(|| rewrite(&small_input));
        let (large, large_work) =
            crate::instrumentation::measure_deterministic_work(|| rewrite(&large_input));

        let assert_rewrite = |output: &Term, original_memory: &SymbolicMemory| {
            let term_source_0 @ Term::Integer(_) = output else {
                unreachable!()
            };
            let (Some(IntegerTerm::PureFunctionApplication(application)),) =
                (term_source_0.integer_native(),)
            else {
                unreachable!()
            };
            let [
                PureFunctionArgument::ArrayRef {
                    point,
                    pointer: ProgramValue::Pointer(pointer),
                    element_type,
                },
            ] = application.arguments()
            else {
                unreachable!()
            };
            assert_eq!(pointer.address(), &expected_pointer);
            assert_eq!(*element_type, ProgramType::UInt8);
            let memory = point.memory();
            assert!(std::sync::Arc::ptr_eq(
                &memory.blocks,
                &original_memory.blocks
            ));
            assert!(std::sync::Arc::ptr_eq(
                &memory.cells,
                &original_memory.cells
            ));
            assert!(std::sync::Arc::ptr_eq(
                &memory.union_cells,
                &original_memory.union_cells
            ));
            assert!(std::sync::Arc::ptr_eq(
                &memory.forgotten,
                &original_memory.forgotten
            ));
            assert!(std::sync::Arc::ptr_eq(&memory.heap, &original_memory.heap));
        };
        assert_rewrite(&small, &small_memory);
        assert_rewrite(&large, &large_memory);
        assert_eq!(small_work, large_work);

        let mut program_replacements = BTreeMap::new();
        program_replacements.insert(
            source,
            TypedProgramValueReplacement::Pointer(OldPointer::new(
                replacement.clone(),
                ProgramType::Int32Pointer,
            )),
        );
        let empty_integer_replacements = BTreeMap::new();
        let empty_algebraic_replacements = BTreeMap::new();
        let mut typed_rewrite = TermRewrite::for_typed_variables(
            &program_replacements,
            &empty_integer_replacements,
            &empty_algebraic_replacements,
        );
        let typed_output = typed_rewrite.term(&small_input);
        assert_rewrite(&typed_output, &small_memory);
    }

    #[test]
    fn typed_condition_budget_stops_deep_program_and_ignores_state_size() {
        let limits = crate::instrumentation::TacticWorkLimits {
            simple: 16,
            smart: 16,
            control: 16,
        };
        let tactic = crate::instrumentation::TacticEvent {
            source_tactic_path: None,
            claim: "integer.typed_condition_budget".into(),
            tactic_index: 0,
            tactic_name: "typed_condition_budget".into(),
            class: "simple".into(),
            statement_index: 0,
            source_index: 0,
        };
        let source = Variable(9890);
        let replacement = Variable(9891);
        let pointer = Address::new(AddressBase::Symbolic(source), AddressOffset::constant(0));
        let condition_for = |memory: SymbolicMemory, depth: usize, fanout: usize| {
            let mut right = OldMachineTerm::Variable(source);
            for index in 0..depth as u64 {
                let mut arguments = Vec::with_capacity(fanout + 1);
                arguments.push(PureFunctionArgument::Value(ProgramValue::Int32(right)));
                arguments.extend((0..fanout).map(|_| {
                    PureFunctionArgument::Value(ProgramValue::Int32(OldMachineTerm::constant(0)))
                }));
                let fanout = OldMachineTerm::ClickFunctionApplication {
                    name: "wide_condition".into(),
                    arguments,
                };
                right = OldMachineTerm::If {
                    condition: Box::new(OldConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::Equal,
                        left: Box::new(OldMachineTerm::Variable(Variable(20_000 + index))),
                        right: Box::new(OldMachineTerm::constant(0)),
                    }),
                    then_term: Box::new(fanout),
                    else_term: Box::new(OldMachineTerm::constant(0)),
                };
            }
            OldConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: Box::new(crate::kernel::OldMachineTerm::read_named(
                    crate::kernel::ProgramPoint::of_memory(&memory),
                    pointer.clone(),
                    crate::kernel::LoadKind::Int32,
                )),
                right: Box::new(right),
            }
        };
        let memory_with_unrelated_blocks = |count: u64| {
            let mut memory = SymbolicMemory::new().with_block("array", 8);
            for index in 0..count {
                memory = memory.with_block(AddressBase::Heap(index + 1), 8);
            }
            memory
        };
        let run = |condition: OldConditionTerm, tactic: crate::instrumentation::TacticEvent| {
            let program_replacements = BTreeMap::from([(
                source,
                TypedProgramValueReplacement::Bitvector(OldMachineTerm::Variable(replacement)),
            )]);
            let integer_replacements = BTreeMap::new();
            let algebraic_replacements = BTreeMap::new();
            crate::instrumentation::with_tactic_work_limits(limits, || {
                crate::instrumentation::collect(|| {
                    crate::instrumentation::emit(
                        crate::instrumentation::VerificationEvent::TacticStarted(tactic.clone()),
                    );
                    let mut rewrite = TermRewrite::for_typed_variables(
                        &program_replacements,
                        &integer_replacements,
                        &algebraic_replacements,
                    );
                    let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                        rewrite.term(&Term::Condition(condition.into()))
                    });
                    let result = (
                        rewrite.integer_work_exhausted,
                        rewrite.visits,
                        rewrite.collector_visits,
                        work,
                    );
                    crate::instrumentation::emit(
                        crate::instrumentation::VerificationEvent::TacticFailed(tactic),
                    );
                    result
                })
                .0
            })
        };
        for (index, &(depth, fanout)) in [(8usize, 8usize), (16, 16), (32, 32), (64, 64)]
            .iter()
            .enumerate()
        {
            let mut small_tactic = tactic.clone();
            small_tactic.tactic_index = index * 2;
            let mut large_tactic = tactic.clone();
            large_tactic.tactic_index = index * 2 + 1;
            let small = run(
                condition_for(memory_with_unrelated_blocks(0), depth, fanout),
                small_tactic,
            );
            let large = run(
                condition_for(memory_with_unrelated_blocks(256), depth, fanout),
                large_tactic,
            );
            assert!(
                small.0 && large.0,
                "deep carrier collection must be bounded at depth {depth}"
            );
            assert!(small.1 <= 16 && large.1 <= 16);
            assert!(small.2 <= 32 && large.2 <= 32);
            assert!(small.3 <= 32 && large.3 <= 32);
            assert_eq!(
                small.2, large.2,
                "opaque states changed collector visits at depth {depth}"
            );
            assert_eq!(small.3, large.3, "opaque states changed rewrite work");
        }
    }

    #[test]
    fn integer_match_iota_rewrites_constructor_after_scrutinee_substitution() {
        let scrutinee_variable = Variable(9940);
        let bound_integer = Variable(9941);
        let bound_c = Variable(9942);
        let field_integer = Variable(9943);
        let field_c = Variable(9944);
        let variants: std::sync::Arc<[AlgebraicVariantType]> = vec![
            AlgebraicVariantType {
                name: "Empty".into(),
                fields: vec![],
            },
            AlgebraicVariantType {
                name: "Wrapped".into(),
                fields: vec![
                    AlgebraicValueType::Integer,
                    AlgebraicValueType::Program(ProgramType::Int32),
                ],
            },
        ]
        .into();
        let value_type = AlgebraicValueType::Algebraic {
            name: "Iota".into(),
            arguments: vec![],
        };
        let algebraic_type = AlgebraicType {
            rigid: false,
            name: "Iota".into(),
            arguments: vec![],
            variants: variants.clone(),
            schemas: std::sync::Arc::new(AlgebraicSchemas::new(BTreeMap::from([(
                value_type, variants,
            )]))),
        };
        let constructor = AlgebraicTerm {
            algebraic_type: algebraic_type.clone(),
            node: AlgebraicTermNode::Constructor {
                variant: "Wrapped".into(),
                fields: vec![
                    AlgebraicValue::Integer(IntegerTerm::var(field_integer)),
                    AlgebraicValue::Program(ProgramValue::Int32(OldMachineTerm::Variable(field_c))),
                ],
            },
        };
        let body = IntegerTerm::PureFunctionApplication(SharedPureApplication::intern(
            "observe".into(),
            vec![
                PureFunctionArgument::Integer(IntegerTerm::var(bound_integer).into()),
                PureFunctionArgument::Value(ProgramValue::Int32(OldMachineTerm::Variable(bound_c))),
            ],
        ));
        let input = IntegerTerm::AlgebraicMatch {
            scrutinee: Box::new(AlgebraicTerm {
                algebraic_type: algebraic_type.clone(),
                node: AlgebraicTermNode::Variable(scrutinee_variable),
            }),
            arms: vec![
                AlgebraicIntegerMatchArm {
                    binding_names: Default::default(),
                    variant: "Empty".into(),
                    bindings: vec![],
                    body: IntegerTerm::constant_i64(0).into(),
                },
                AlgebraicIntegerMatchArm {
                    binding_names: Default::default(),
                    variant: "Wrapped".into(),
                    bindings: vec![
                        AlgebraicValue::Integer(IntegerTerm::var(bound_integer)),
                        AlgebraicValue::Program(ProgramValue::Int32(OldMachineTerm::Variable(
                            bound_c,
                        ))),
                    ],
                    body: body.clone().into(),
                },
            ],
        };
        let program_replacements = BTreeMap::new();
        let integer_replacements = BTreeMap::new();
        let mut algebraic_replacements = BTreeMap::new();
        algebraic_replacements.insert(scrutinee_variable, constructor.clone());
        let mut rewrite = TermRewrite::for_typed_variables(
            &program_replacements,
            &integer_replacements,
            &algebraic_replacements,
        );
        let output = rewrite.integer(&input);
        let expected = IntegerTerm::PureFunctionApplication(SharedPureApplication::intern(
            "observe".into(),
            vec![
                PureFunctionArgument::Integer(IntegerTerm::var(field_integer).into()),
                PureFunctionArgument::Value(ProgramValue::Int32(OldMachineTerm::Variable(field_c))),
            ],
        ));
        assert_eq!(output, expected);
        assert!(!matches!(output, IntegerTerm::AlgebraicMatch { .. }));
        assert!(rewrite.changed);

        let malformed_constructor = AlgebraicTerm {
            algebraic_type: algebraic_type.clone(),
            node: AlgebraicTermNode::Constructor {
                variant: "Wrapped".into(),
                fields: vec![
                    AlgebraicValue::Integer(IntegerTerm::var(field_integer)),
                    AlgebraicValue::Program(ProgramValue::Int64(OldMachineTerm::Variable(field_c))),
                ],
            },
        };
        let mut malformed_replacements = BTreeMap::new();
        malformed_replacements.insert(scrutinee_variable, malformed_constructor);
        let mut malformed_rewrite = TermRewrite::for_typed_variables(
            &program_replacements,
            &integer_replacements,
            &malformed_replacements,
        );
        let malformed_output = malformed_rewrite.integer(&input);
        assert!(matches!(
            malformed_output,
            IntegerTerm::AlgebraicMatch { .. }
        ));

        let mut malformed_input = input.clone();
        let IntegerTerm::AlgebraicMatch { arms, .. } = &mut malformed_input else {
            unreachable!()
        };
        arms[1].bindings[1] = AlgebraicValue::Program(ProgramValue::Int32(binary_node!(
            Int32,
            Add,
            Box::new(OldMachineTerm::Variable(bound_c)),
            Box::new(OldMachineTerm::constant(1)),
        )));
        let mut malformed_binding_rewrite = TermRewrite::for_typed_variables(
            &program_replacements,
            &integer_replacements,
            &algebraic_replacements,
        );
        let malformed_binding_output = malformed_binding_rewrite.integer(&malformed_input);
        assert!(matches!(
            malformed_binding_output,
            IntegerTerm::AlgebraicMatch { .. }
        ));
    }

    #[test]
    fn bitvector_match_iota_rewrites_constructor_after_scrutinee_substitution() {
        let scrutinee_variable = Variable(9950);
        let bound = Variable(9951);
        let variants: std::sync::Arc<[AlgebraicVariantType]> = vec![AlgebraicVariantType {
            name: "Wrapped".into(),
            fields: vec![AlgebraicValueType::Program(ProgramType::Int32)],
        }]
        .into();
        let algebraic_type = AlgebraicType {
            rigid: false,
            name: "MachineIota".into(),
            arguments: vec![],
            variants: variants.clone(),
            schemas: std::sync::Arc::new(AlgebraicSchemas::new(BTreeMap::from([(
                AlgebraicValueType::Algebraic {
                    name: "MachineIota".into(),
                    arguments: vec![],
                },
                variants,
            )]))),
        };
        let scrutinee = AlgebraicTerm {
            algebraic_type: algebraic_type.clone(),
            node: AlgebraicTermNode::Variable(scrutinee_variable),
        };
        let constructor = AlgebraicTerm {
            algebraic_type,
            node: AlgebraicTermNode::Constructor {
                variant: "Wrapped".into(),
                fields: vec![AlgebraicValue::Program(ProgramValue::Int32(
                    OldMachineTerm::constant(7),
                ))],
            },
        };
        let goal = OldMachineTerm::AlgebraicMatch {
            scrutinee: Box::new(scrutinee.clone()),
            arms: vec![AlgebraicBitvectorMatchArm {
                binding_names: Default::default(),
                variant: "Wrapped".into(),
                bindings: vec![AlgebraicValue::Program(ProgramValue::Int32(
                    OldMachineTerm::Variable(bound),
                ))],
                body: OldMachineTerm::Variable(bound),
            }],
        };
        let mut rewrite = TermRewrite::new(&scrutinee, &constructor);
        assert_eq!(rewrite.bits(&goal), OldMachineTerm::constant(7));
        assert!(rewrite.changed);

        let malformed = AlgebraicTerm {
            algebraic_type: constructor.algebraic_type.clone(),
            node: AlgebraicTermNode::Constructor {
                variant: "Wrapped".into(),
                fields: vec![AlgebraicValue::Program(ProgramValue::Int64(
                    OldMachineTerm::constant(7),
                ))],
            },
        };
        let mut malformed_rewrite = TermRewrite::new(&scrutinee, &malformed);
        assert!(matches!(
            malformed_rewrite.bits(&goal),
            OldMachineTerm::AlgebraicMatch { .. }
        ));
    }

    /// A loaded pointer names its read, and its read's address can mention a
    /// binder. Missing that carrier would let a rewrite treat the binder as
    /// absent from a term that depends on it.
    #[test]
    fn a_loaded_pointer_carries_its_defining_address_variables() {
        let _session = crate::kernel::VerificationSession::enter();
        let index = Variable(9_904);
        let memory = crate::kernel::intern_memory(SymbolicMemory::new());
        let address = Address::new(
            AddressBase::ExternalArgument,
            AddressOffset::scale_int32(OldMachineTerm::Variable(index), 8),
        );
        let loaded = Address::loaded_value(&memory, &address);
        let mut carriers = CarrierVariables::default();
        collect_pointer_carriers(&loaded, &mut carriers);
        assert!(carriers.contains(BindingCarrier::Program, index));
    }

    #[test]
    fn typed_rewrite_is_simultaneous_across_integer_program_and_algebraic_carriers() {
        let replacement = Variable(9900);
        let integer_source = Variable(9901);
        let c_source = Variable(9902);
        let algebraic_source = Variable(9903);
        let variants: std::sync::Arc<[AlgebraicVariantType]> = vec![AlgebraicVariantType {
            name: "Unit".into(),
            fields: vec![],
        }]
        .into();
        let algebraic_type = AlgebraicType {
            rigid: false,
            name: "TypedRewrite".into(),
            arguments: vec![],
            variants: variants.clone(),
            schemas: std::sync::Arc::new(AlgebraicSchemas::new(BTreeMap::from([(
                AlgebraicValueType::Algebraic {
                    name: "TypedRewrite".into(),
                    arguments: vec![],
                },
                variants,
            )]))),
        };
        let algebraic_from = AlgebraicTerm {
            algebraic_type: algebraic_type.clone(),
            node: AlgebraicTermNode::Variable(algebraic_source),
        };
        let algebraic_to = AlgebraicTerm {
            algebraic_type,
            node: AlgebraicTermNode::Variable(replacement),
        };
        let mut program_replacements = BTreeMap::new();
        program_replacements.insert(
            c_source,
            TypedProgramValueReplacement::Bitvector(OldMachineTerm::Variable(replacement)),
        );
        let mut integer_replacements = BTreeMap::new();
        integer_replacements.insert(integer_source, IntegerTerm::var(replacement));
        integer_replacements.insert(replacement, IntegerTerm::constant_i64(7));
        let mut algebraic_replacements = BTreeMap::new();
        algebraic_replacements.insert(algebraic_source, algebraic_to.clone());
        let body = IntegerTerm::PureFunctionApplication(SharedPureApplication::intern(
            "observe".into(),
            vec![
                PureFunctionArgument::Integer(IntegerTerm::var(integer_source).into()),
                PureFunctionArgument::Integer(IntegerTerm::var(replacement).into()),
                PureFunctionArgument::Value(ProgramValue::Int32(OldMachineTerm::Variable(
                    c_source,
                ))),
                PureFunctionArgument::Algebraic(algebraic_from),
            ],
        ));
        let mut rewrite = TermRewrite::for_typed_variables(
            &program_replacements,
            &integer_replacements,
            &algebraic_replacements,
        );
        let term_source_0 @ Term::Integer(_) = rewrite.term(&Term::Integer(body.into())) else {
            unreachable!()
        };
        let (Some(IntegerTerm::PureFunctionApplication(application)),) =
            (term_source_0.integer_native(),)
        else {
            unreachable!()
        };
        assert_eq!(
            application.arguments(),
            &[
                PureFunctionArgument::Integer(IntegerTerm::var(replacement).into()),
                PureFunctionArgument::Integer(IntegerTerm::constant_i64(7).into()),
                PureFunctionArgument::Value(ProgramValue::Int32(OldMachineTerm::Variable(
                    replacement
                ))),
                PureFunctionArgument::Algebraic(algebraic_to.clone()),
            ]
        );

        let scoped = IntegerTerm::AlgebraicMatch {
            scrutinee: Box::new(AlgebraicTerm {
                algebraic_type: algebraic_to.algebraic_type.clone(),
                node: AlgebraicTermNode::Variable(Variable(9904)),
            }),
            arms: vec![AlgebraicIntegerMatchArm {
                binding_names: Default::default(),
                variant: "Unit".into(),
                bindings: vec![AlgebraicValue::Integer(IntegerTerm::var(replacement))],
                body: IntegerTerm::var(replacement).into(),
            }],
        };
        let mut scoped_rewrite = TermRewrite::for_typed_variables(
            &program_replacements,
            &integer_replacements,
            &algebraic_replacements,
        );
        let term_source_0 @ Term::Integer(_) = scoped_rewrite.term(&Term::Integer(scoped.into()))
        else {
            unreachable!()
        };
        let (Some(IntegerTerm::AlgebraicMatch { arms, .. }),) = (term_source_0.integer_native(),)
        else {
            unreachable!()
        };
        let AlgebraicValue::Integer(IntegerTerm::Variable(scoped_binding)) = &arms[0].bindings[0]
        else {
            panic!("Integer match binding was not retained as a variable")
        };
        assert_ne!(*scoped_binding, replacement);
        assert_eq!(
            arms[0].body.as_ref(),
            &IntegerTerm::var(*scoped_binding),
            "the bound occurrence must follow the freshened binder"
        );
    }

    fn with_checked_simple_budget<R>(limit: usize, operation: impl FnOnce() -> R) -> R {
        let limits = crate::instrumentation::TacticWorkLimits {
            simple: limit,
            smart: limit,
            control: limit,
        };
        let (result, _events) = crate::instrumentation::with_tactic_work_limits(limits, || {
            crate::instrumentation::collect(|| {
                let tactic = crate::instrumentation::TacticEvent {
                    source_tactic_path: None,
                    claim: "checked fold collector regression".into(),
                    tactic_index: 0,
                    tactic_name: "checked_fold_collector_regression".into(),
                    class: "simple".into(),
                    statement_index: 0,
                    source_index: 0,
                };
                crate::instrumentation::emit(
                    crate::instrumentation::VerificationEvent::TacticStarted(tactic.clone()),
                );
                let result = operation();
                crate::instrumentation::emit(
                    crate::instrumentation::VerificationEvent::TacticFailed(tactic),
                );
                result
            })
        });
        result
    }

    #[test]
    fn checked_machine_rewrite_stops_after_work_exhaustion() {
        let source = Variable(880);
        let mut payload = OldMachineTerm::Variable(source);
        for _ in 0..128 {
            payload = binary_node!(
                Int32,
                Add,
                Box::new(payload),
                Box::new(OldMachineTerm::constant(1))
            );
        }
        let input = Term::Integer(
            IntegerTerm::Machine(crate::kernel::SharedMachineIntegerTerm::intern(
                crate::kernel::MachineIntegerType::Int32,
                payload,
            ))
            .into(),
        );
        let (result, _events) = crate::instrumentation::with_tactic_work_limits(
            crate::instrumentation::TacticWorkLimits {
                simple: 4,
                smart: 4,
                control: 4,
            },
            || {
                crate::instrumentation::collect(|| {
                    let tactic = crate::instrumentation::TacticEvent {
                        source_tactic_path: None,
                        claim: "checked machine rewrite".into(),
                        tactic_index: 0,
                        tactic_name: "checked_machine_rewrite".into(),
                        class: "simple".into(),
                        statement_index: 0,
                        source_index: 0,
                    };
                    crate::instrumentation::emit(
                        crate::instrumentation::VerificationEvent::TacticStarted(tactic.clone()),
                    );
                    let source_term = OldMachineTerm::Variable(source);
                    let replacement = OldMachineTerm::constant(7);
                    let mut rewrite = TermRewrite::for_bits_checked(&source_term, &replacement);
                    let output = rewrite.term(&input);
                    let visits = rewrite.visits;
                    let exhausted = rewrite.integer_work_exhausted;
                    crate::instrumentation::emit(
                        crate::instrumentation::VerificationEvent::TacticFailed(tactic),
                    );
                    (output, visits, exhausted)
                })
            },
        );
        assert!(result.2);
        assert!(
            result.1 <= 6,
            "checked rewrite kept traversing after exhaustion: {} visits",
            result.1
        );
    }

    #[test]
    fn checked_machine_replacement_collection_stops_before_rewrite() {
        let source = OldMachineTerm::Variable(Variable(3_025_000));
        let mut replacement = OldMachineTerm::Variable(Variable(3_025_001));
        for _ in 0..128 {
            replacement = binary_node!(
                Int32,
                Add,
                Box::new(replacement),
                Box::new(OldMachineTerm::constant(1)),
            );
        }
        let (output, visits, exhausted) = with_checked_simple_budget(4, || {
            let mut rewrite = TermRewrite::for_bits_checked(&source, &replacement);
            let output = rewrite.term(&Term::Bitvector32(source.clone().into()));
            (output, rewrite.visits, rewrite.integer_work_exhausted)
        });
        assert!(
            exhausted,
            "replacement collection ignored its checked budget"
        );
        assert!(
            visits <= 1,
            "rewrite traversed after collection exhaustion: {visits}"
        );
        assert!(
            matches!(&(output), term_source_0 @ Term::Bitvector32(_) if matches!((term_source_0.bitvector_native(),), (Some(int32_constant!(0)),)))
        );
    }

    #[test]
    fn checked_rewrite_stops_before_wide_sibling_payloads() {
        let source = OldMachineTerm::Variable(Variable(3_020_000));
        let replacement = OldMachineTerm::constant(7);
        let input = Term::Bitvector32(
            OldMachineTerm::PureFunctionApplication {
                name: "wide_checked_payload".into(),
                arguments: vec![source.clone(); 256],
            }
            .into(),
        );
        let (output, visits, exhausted) = with_checked_simple_budget(4, || {
            let mut rewrite = TermRewrite::for_bits_checked(&source, &replacement);
            let output = rewrite.term(&input);
            (output, rewrite.visits, rewrite.integer_work_exhausted)
        });
        assert!(exhausted);
        assert!(visits <= 8, "rewrite kept visiting siblings: {visits}");
        assert!(
            matches!(&(output), term_source_0 @ Term::Bitvector32(_) if matches!((term_source_0.bitvector_native(),), (Some(int32_constant!(0)),)))
        );
    }

    #[test]
    fn integer_range_fold_rewrite_rewrites_free_machine_variables_for_integer_index() {
        let binder = Variable(990);
        let body = IntegerTerm::Machine(crate::kernel::SharedMachineIntegerTerm::intern(
            crate::kernel::MachineIntegerType::Int32,
            OldMachineTerm::Variable(binder),
        ));
        let fold = IntegerTerm::range_fold(
            crate::kernel::IntegerRangeFoldIndex::Integer {
                start: SharedIntegerTerm::from(IntegerTerm::constant_i64(0)),
                end: SharedIntegerTerm::from(IntegerTerm::constant_i64(2)),
            },
            IntegerTerm::constant_i64(0),
            Variable(991),
            binder,
            body,
        );
        let from = OldMachineTerm::Variable(binder);
        let to = OldMachineTerm::constant(7);
        let mut rewrite = TermRewrite::for_bits(&from, &to);
        let output = rewrite.term(&Term::Integer(fold.into()));
        let term_source_0 @ Term::Integer(_) = output else {
            unreachable!()
        };
        let (Some(IntegerTerm::RangeFold { body, .. }),) = (term_source_0.integer_native(),) else {
            unreachable!()
        };
        // The body observed a free machine variable, so the rewrite reached it.
        // Once the observed term is a literal the observation is decided, and
        // the body is the mathematical constant that `to_integer(7)` denotes.
        assert_eq!(body.as_ref(), &IntegerTerm::constant_i64(7));
    }

    #[test]
    fn integer_range_fold_rewrite_keeps_bound_machine_variables_scoped() {
        let binder = Variable(990);
        let body = IntegerTerm::Machine(crate::kernel::SharedMachineIntegerTerm::intern(
            crate::kernel::MachineIntegerType::Int32,
            OldMachineTerm::Variable(binder),
        ));
        let fold = IntegerTerm::range_fold(
            crate::kernel::IntegerRangeFoldIndex::Int32 {
                start: crate::kernel::SharedIntegerRangeEndpoint::intern(OldMachineTerm::constant(
                    0,
                )),
                end: crate::kernel::SharedIntegerRangeEndpoint::intern(OldMachineTerm::constant(2)),
            },
            IntegerTerm::constant_i64(0),
            Variable(991),
            binder,
            body,
        );
        let from = OldMachineTerm::Variable(binder);
        let to = OldMachineTerm::constant(7);
        let mut rewrite = TermRewrite::for_bits(&from, &to);
        let output = rewrite.term(&Term::Integer(fold.into()));
        let term_source_0 @ Term::Integer(_) = output else {
            unreachable!()
        };
        let (Some(IntegerTerm::RangeFold { item, body, .. }),) = (term_source_0.integer_native(),)
        else {
            unreachable!()
        };
        assert_eq!(*item, binder);
        assert!(matches!(body.as_ref(), IntegerTerm::Machine(machine)
            if machine.value() == &OldMachineTerm::Variable(binder)));
    }

    #[test]
    fn integer_range_fold_rewrite_freshens_a_colliding_free_replacement() {
        let binder = Variable(992);
        let body = IntegerTerm::Machine(crate::kernel::SharedMachineIntegerTerm::intern(
            crate::kernel::MachineIntegerType::Int32,
            OldMachineTerm::Variable(binder),
        ));
        let fold = IntegerTerm::range_fold(
            crate::kernel::IntegerRangeFoldIndex::Int32 {
                start: crate::kernel::SharedIntegerRangeEndpoint::intern(OldMachineTerm::Variable(
                    Variable(993),
                )),
                end: crate::kernel::SharedIntegerRangeEndpoint::intern(OldMachineTerm::Variable(
                    Variable(994),
                )),
            },
            IntegerTerm::constant_i64(0),
            Variable(995),
            binder,
            body,
        );
        let from = OldMachineTerm::Variable(Variable(996));
        let to = OldMachineTerm::Variable(binder);
        let mut rewrite = TermRewrite::for_bits(&from, &to);
        let term_source_0 @ Term::Integer(_) = rewrite.term(&Term::Integer(fold.into())) else {
            unreachable!()
        };
        let (Some(IntegerTerm::RangeFold { item, body, .. }),) = (term_source_0.integer_native(),)
        else {
            unreachable!()
        };
        assert_ne!(*item, binder);
        assert!(matches!(body.as_ref(), IntegerTerm::Machine(machine)
            if machine.value() == &OldMachineTerm::Variable(*item)));
    }

    #[test]
    fn integer_substitution_keeps_integer_source_when_int32_item_reuses_id() {
        let source = Variable(1_020);
        let body = IntegerTerm::Add(
            IntegerTerm::Variable(source).into(),
            IntegerTerm::Machine(crate::kernel::SharedMachineIntegerTerm::intern(
                crate::kernel::MachineIntegerType::Int32,
                OldMachineTerm::Variable(source),
            ))
            .into(),
        );
        let fold = IntegerTerm::range_fold(
            crate::kernel::IntegerRangeFoldIndex::Int32 {
                start: crate::kernel::SharedIntegerRangeEndpoint::intern(OldMachineTerm::constant(
                    0,
                )),
                end: crate::kernel::SharedIntegerRangeEndpoint::intern(OldMachineTerm::constant(1)),
            },
            IntegerTerm::constant_i64(0),
            Variable(1_021),
            source,
            body,
        );
        let replacement = IntegerTerm::constant_i64(7);
        let renamings = BTreeMap::new();
        let mut rewrite =
            TermRewrite::for_integer_variables(source, &replacement, false, &renamings);
        let term_source_0 @ Term::Integer(_) = rewrite.term(&Term::Integer(fold.into())) else {
            unreachable!()
        };
        let (Some(IntegerTerm::RangeFold { item, body, .. }),) = (term_source_0.integer_native(),)
        else {
            unreachable!()
        };
        assert_eq!(*item, source);
        let IntegerTerm::Add(integer, machine) = body.as_ref() else {
            panic!("source and Int32 item occurrences were not preserved")
        };
        assert!(matches!(integer.as_ref(), IntegerTerm::Constant(value) if value == &7.into()));
        assert!(matches!(machine.as_ref(), IntegerTerm::Machine(machine)
            if machine.value() == &OldMachineTerm::Variable(source)));
    }

    #[test]
    fn machine_fold_endpoint_rewrite_retains_shared_operands_and_scope() {
        for unsigned in [false, true] {
            let _session = VerificationSession::enter();
            let source = Variable(989901);
            let item = Variable(989902);
            let source_term = OldMachineTerm::Variable(source);
            let replacement = OldMachineTerm::Variable(item);
            let format = if unsigned {
                MachineIntegerType::UInt64
            } else {
                MachineIntegerType::Int32
            };
            let sum = |value: OldMachineTerm| OldMachineTerm::Binary {
                format,
                op: MachineBinaryOp::Add,
                left: value.into(),
                right: if unsigned {
                    OldMachineTerm::uint64_constant(1)
                } else {
                    OldMachineTerm::constant(1)
                }
                .into(),
            };
            let root = KernelTermImport::default()
                .machine_arithmetic(MachineIntegerType::Int32, &sum(source_term.clone()))
                .unwrap();
            let endpoint = SharedIntegerRangeEndpoint::intern(OldMachineTerm::constant(0))
                .with_shared_operand(root)
                .unwrap();
            let index = if unsigned {
                IntegerRangeFoldIndex::UInt64 {
                    start: endpoint.clone(),
                    end: endpoint,
                }
            } else {
                IntegerRangeFoldIndex::Int32 {
                    start: endpoint.clone(),
                    end: endpoint,
                }
            };
            let body = IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
                format,
                OldMachineTerm::Variable(item),
            ));
            let fold = IntegerTerm::range_fold(
                index,
                IntegerTerm::constant_i64(0),
                Variable(989903),
                item,
                body,
            );
            let exports = KernelTermExport::machine_export_count();
            let mut rewrite = TermRewrite::for_bits_checked(&source_term, &replacement);
            let output = rewrite.term(&Term::Integer(fold.into()));
            assert!(rewrite.refusal().is_none());
            assert_eq!(KernelTermExport::machine_export_count(), exports);
            let term_source_0 @ Term::Integer(_) = output else {
                panic!("fold")
            };
            let (Some(IntegerTerm::RangeFold {
                index,
                item: fresh,
                body,
                ..
            }),) = (term_source_0.integer_native(),)
            else {
                panic!("fold")
            };
            assert_ne!(
                *fresh, item,
                "body binder must avoid capturing the replacement"
            );
            let (start, end) = match index {
                IntegerRangeFoldIndex::Int32 { start, end } => {
                    assert!(!unsigned);
                    (start, end)
                }
                IntegerRangeFoldIndex::UInt64 { start, end } => {
                    assert!(unsigned);
                    (start, end)
                }
                _ => panic!("machine range"),
            };
            let expected = KernelTermImport::default()
                .machine_arithmetic(MachineIntegerType::Int32, &sum(replacement.clone()))
                .unwrap();
            assert_eq!(start.machine_operand().shared_operand(), Some(&expected));
            assert_eq!(end.machine_operand().shared_operand(), Some(&expected));
            let IntegerTerm::Machine(body) = body.as_ref() else {
                panic!("body observation")
            };
            assert_eq!(
                MachineOperandView::Shared(body.shared_operand().unwrap()).variable(),
                Some(fresh)
            );
        }
    }

    #[test]
    fn program_substitution_reserves_nested_machine_fold_binders_before_freshening() {
        let source = Variable(1_100);
        let replacement_item = Variable(1_101);
        let nested_item = Variable(1_102);
        let nested_accumulator = Variable(1_103);
        let leaf = IntegerTerm::Machine(crate::kernel::SharedMachineIntegerTerm::intern(
            crate::kernel::MachineIntegerType::Int32,
            OldMachineTerm::Variable(source),
        ));
        let nested = IntegerTerm::range_fold(
            crate::kernel::IntegerRangeFoldIndex::Int32 {
                start: crate::kernel::SharedIntegerRangeEndpoint::intern(OldMachineTerm::constant(
                    0,
                )),
                end: crate::kernel::SharedIntegerRangeEndpoint::intern(OldMachineTerm::constant(1)),
            },
            IntegerTerm::constant_i64(0),
            nested_accumulator,
            nested_item,
            leaf,
        );
        let fold = IntegerTerm::range_fold(
            crate::kernel::IntegerRangeFoldIndex::Int32 {
                start: crate::kernel::SharedIntegerRangeEndpoint::intern(OldMachineTerm::constant(
                    0,
                )),
                end: crate::kernel::SharedIntegerRangeEndpoint::intern(OldMachineTerm::constant(1)),
            },
            IntegerTerm::constant_i64(0),
            Variable(1_104),
            replacement_item,
            nested,
        );
        let source_term = OldMachineTerm::Variable(source);
        let replacement = OldMachineTerm::Variable(replacement_item);
        let mut rewrite = TermRewrite::for_bits(&source_term, &replacement);
        let term_source_0 @ Term::Integer(_) = rewrite.term(&Term::Integer(fold.into())) else {
            unreachable!()
        };
        let (Some(IntegerTerm::RangeFold { item, body, .. }),) = (term_source_0.integer_native(),)
        else {
            unreachable!()
        };
        let IntegerTerm::RangeFold {
            item: retained_item,
            body: retained_body,
            ..
        } = body.as_ref()
        else {
            unreachable!()
        };
        assert_ne!(*item, replacement_item);
        assert_ne!(*item, nested_item);
        assert_eq!(*retained_item, nested_item);
        assert!(
            matches!(retained_body.as_ref(), IntegerTerm::Machine(machine)
            if machine.value() == &replacement)
        );
    }

    #[test]
    fn program_substitution_freshens_integer_binder_in_integer_to_machine_replacement() {
        let source = Variable(1_030);
        let accumulator = Variable(1_031);
        let body = IntegerTerm::Add(
            IntegerTerm::Variable(accumulator).into(),
            IntegerTerm::Machine(crate::kernel::SharedMachineIntegerTerm::intern(
                crate::kernel::MachineIntegerType::Int32,
                OldMachineTerm::Variable(source),
            ))
            .into(),
        );
        let fold = IntegerTerm::range_fold(
            crate::kernel::IntegerRangeFoldIndex::Integer {
                start: IntegerTerm::constant_i64(0).into(),
                end: IntegerTerm::constant_i64(1).into(),
            },
            IntegerTerm::constant_i64(0),
            accumulator,
            Variable(1_032),
            body,
        );
        let replacement = OldMachineTerm::IntegerToMachine {
            value: SharedIntegerTerm::from(IntegerTerm::Variable(accumulator)),
            destination: crate::kernel::MachineIntegerType::Int32,
        };
        let source_term = OldMachineTerm::Variable(source);
        let mut rewrite = TermRewrite::for_bits(&source_term, &replacement);
        let term_source_0 @ Term::Integer(_) = rewrite.term(&Term::Integer(fold.into())) else {
            unreachable!()
        };
        let (Some(IntegerTerm::RangeFold {
            accumulator: fresh_accumulator,
            body,
            ..
        }),) = (term_source_0.integer_native(),)
        else {
            unreachable!()
        };
        assert_ne!(*fresh_accumulator, accumulator);
        let IntegerTerm::Add(integer, machine) = body.as_ref() else {
            panic!("missing Integer-to-machine replacement")
        };
        assert!(matches!(integer.as_ref(), IntegerTerm::Variable(variable)
            if *variable == *fresh_accumulator));
        assert!(matches!(machine.as_ref(), IntegerTerm::Machine(machine)
            if machine.value() == &replacement));
    }

    #[test]
    fn program_substitution_reserves_nested_integer_fold_binders_before_freshening() {
        let source = Variable(1_050);
        let accumulator = Variable(1_051);
        let nested_accumulator = Variable(1_052);
        let nested_item = Variable(1_053);
        let nested_body = IntegerTerm::add(
            IntegerTerm::var(nested_accumulator),
            IntegerTerm::var(nested_item),
        );
        let nested = IntegerTerm::range_fold(
            crate::kernel::IntegerRangeFoldIndex::Integer {
                start: IntegerTerm::constant_i64(0).into(),
                end: IntegerTerm::constant_i64(1).into(),
            },
            IntegerTerm::constant_i64(0),
            nested_accumulator,
            nested_item,
            nested_body,
        );
        let body = IntegerTerm::add(
            IntegerTerm::var(accumulator),
            IntegerTerm::add(
                nested,
                IntegerTerm::Machine(crate::kernel::SharedMachineIntegerTerm::intern(
                    crate::kernel::MachineIntegerType::Int32,
                    OldMachineTerm::Variable(source),
                )),
            ),
        );
        let fold = IntegerTerm::range_fold(
            crate::kernel::IntegerRangeFoldIndex::Integer {
                start: IntegerTerm::constant_i64(0).into(),
                end: IntegerTerm::constant_i64(1).into(),
            },
            IntegerTerm::constant_i64(0),
            accumulator,
            Variable(1_054),
            body,
        );
        let replacement = OldMachineTerm::IntegerToMachine {
            value: SharedIntegerTerm::from(IntegerTerm::Variable(accumulator)),
            destination: crate::kernel::MachineIntegerType::Int32,
        };
        let source_term = OldMachineTerm::Variable(source);
        let mut rewrite = TermRewrite::for_bits(&source_term, &replacement);
        let body = KernelTermImport::default().integer(&match &fold {
            IntegerTerm::RangeFold { body, .. } => body.clone(),
            _ => unreachable!(),
        });
        let exports = KernelTermExport::integer_export_count();
        assert_eq!(rewrite.body_variable_max(&body), Some(nested_item.0));
        assert_eq!(KernelTermExport::integer_export_count(), exports);
        let term_source_0 @ Term::Integer(_) = rewrite.term(&Term::Integer(fold.into())) else {
            unreachable!()
        };
        let (Some(IntegerTerm::RangeFold {
            accumulator: fresh_accumulator,
            body,
            ..
        }),) = (term_source_0.integer_native(),)
        else {
            unreachable!()
        };
        assert!(fresh_accumulator.0 > nested_item.0);
        let IntegerTerm::Add(_, nested_and_machine) = body.as_ref() else {
            panic!("missing nested Integer fold")
        };
        let IntegerTerm::Add(nested, _) = nested_and_machine.as_ref() else {
            panic!("missing nested Integer fold")
        };
        let IntegerTerm::RangeFold {
            accumulator: retained_accumulator,
            item: retained_item,
            ..
        } = nested.as_ref()
        else {
            panic!("nested fold was not retained")
        };
        assert_eq!(*retained_accumulator, nested_accumulator);
        assert_eq!(*retained_item, nested_item);
    }

    #[test]
    fn mixed_fold_and_integer_match_scopes_preserve_carriers() {
        let collision_integer = Variable(3_100_000);
        let collision_c = Variable(3_100_001);
        let integer_source = Variable(3_100_010);
        let c_source = Variable(3_100_011);
        let scrutinee = Variable(3_100_020);
        let variants: std::sync::Arc<[AlgebraicVariantType]> = vec![AlgebraicVariantType {
            name: "Wrapped".into(),
            fields: vec![
                AlgebraicValueType::Integer,
                AlgebraicValueType::Program(ProgramType::Int32),
            ],
        }]
        .into();
        let value_type = AlgebraicValueType::Algebraic {
            name: "MixedFoldMatch".into(),
            arguments: vec![],
        };
        let algebraic_type = AlgebraicType {
            rigid: false,
            name: "MixedFoldMatch".into(),
            arguments: vec![],
            variants: variants.clone(),
            schemas: std::sync::Arc::new(AlgebraicSchemas::new(BTreeMap::from([(
                value_type, variants,
            )]))),
        };
        let match_body = || {
            IntegerTerm::Add(
                IntegerTerm::var(integer_source).into(),
                IntegerTerm::Machine(crate::kernel::SharedMachineIntegerTerm::intern(
                    crate::kernel::MachineIntegerType::Int32,
                    OldMachineTerm::Variable(c_source),
                ))
                .into(),
            )
        };
        let make_match = || IntegerTerm::AlgebraicMatch {
            scrutinee: Box::new(AlgebraicTerm {
                algebraic_type: algebraic_type.clone(),
                node: AlgebraicTermNode::Variable(scrutinee),
            }),
            arms: vec![AlgebraicIntegerMatchArm {
                binding_names: Default::default(),
                variant: "Wrapped".into(),
                bindings: vec![
                    AlgebraicValue::Integer(IntegerTerm::var(collision_integer)),
                    AlgebraicValue::Program(ProgramValue::Int32(OldMachineTerm::Variable(
                        collision_c,
                    ))),
                ],
                body: match_body().into(),
            }],
        };
        let program_replacements = BTreeMap::from([(
            c_source,
            TypedProgramValueReplacement::Bitvector(OldMachineTerm::Variable(collision_c)),
        )]);
        let integer_replacements =
            BTreeMap::from([(integer_source, IntegerTerm::var(collision_integer))]);
        let algebraic_replacements = BTreeMap::new();

        // A machine-indexed fold contains an Integer-returning match.  Both
        // binders reuse IDs from the replacement's other carrier, so each
        // scope must freshen independently before walking the nested body.
        let fold_with_match = IntegerTerm::range_fold(
            crate::kernel::IntegerRangeFoldIndex::Int32 {
                start: crate::kernel::SharedIntegerRangeEndpoint::intern(OldMachineTerm::constant(
                    0,
                )),
                end: crate::kernel::SharedIntegerRangeEndpoint::intern(OldMachineTerm::constant(1)),
            },
            IntegerTerm::constant_i64(0),
            collision_integer,
            collision_c,
            make_match(),
        );
        let mut rewrite = TermRewrite::for_typed_variables(
            &program_replacements,
            &integer_replacements,
            &algebraic_replacements,
        );
        let term_source_0 @ Term::Integer(_) = rewrite.term(&Term::Integer(fold_with_match.into()))
        else {
            unreachable!()
        };
        let (Some(IntegerTerm::RangeFold {
            accumulator,
            item,
            body,
            ..
        }),) = (term_source_0.integer_native(),)
        else {
            unreachable!()
        };
        assert_ne!(*accumulator, collision_integer);
        assert_ne!(*item, collision_c);
        let IntegerTerm::AlgebraicMatch { arms, .. } = body.as_ref() else {
            panic!("nested Integer match was not retained")
        };
        let [arm] = arms.as_slice() else {
            unreachable!()
        };
        assert!(matches!(
            &arm.bindings[0],
            AlgebraicValue::Integer(IntegerTerm::Variable(variable)) if *variable != collision_integer
        ));
        assert!(matches!(
            &arm.bindings[1],
            AlgebraicValue::Program(ProgramValue::Int32(OldMachineTerm::Variable(variable)))
                if *variable != collision_c
        ));
        let mut free_integer = BTreeSet::new();
        crate::kernel::prelude::collect_integer_free_variables(
            &IntegerTerm::RangeFold {
                index: crate::kernel::IntegerRangeFoldIndex::Int32 {
                    start: crate::kernel::SharedIntegerRangeEndpoint::intern(
                        OldMachineTerm::constant(0),
                    ),
                    end: crate::kernel::SharedIntegerRangeEndpoint::intern(
                        OldMachineTerm::constant(1),
                    ),
                },
                initial: IntegerTerm::constant_i64(0).into(),
                accumulator: *accumulator,
                item: *item,
                body: body.clone(),
            },
            &mut free_integer,
        );
        assert!(free_integer.contains(&collision_integer));
        let mut free_c = BTreeSet::new();
        crate::kernel::prelude::collect_integer_capture_bitvector_variables(
            &IntegerTerm::RangeFold {
                index: crate::kernel::IntegerRangeFoldIndex::Int32 {
                    start: crate::kernel::SharedIntegerRangeEndpoint::intern(
                        OldMachineTerm::constant(0),
                    ),
                    end: crate::kernel::SharedIntegerRangeEndpoint::intern(
                        OldMachineTerm::constant(1),
                    ),
                },
                initial: IntegerTerm::constant_i64(0).into(),
                accumulator: *accumulator,
                item: *item,
                body: body.clone(),
            },
            &mut free_c,
        );
        assert!(free_c.contains(&collision_c));

        // Conversely, an Integer-returning match contains a fold in its arm.
        // This exercises the same carrier maps in the opposite nesting order.
        let match_with_fold = IntegerTerm::AlgebraicMatch {
            scrutinee: Box::new(AlgebraicTerm {
                algebraic_type,
                node: AlgebraicTermNode::Variable(scrutinee),
            }),
            arms: vec![AlgebraicIntegerMatchArm {
                binding_names: Default::default(),
                variant: "Wrapped".into(),
                bindings: vec![
                    AlgebraicValue::Integer(IntegerTerm::var(collision_integer)),
                    AlgebraicValue::Program(ProgramValue::Int32(OldMachineTerm::Variable(
                        collision_c,
                    ))),
                ],
                body: IntegerTerm::range_fold(
                    crate::kernel::IntegerRangeFoldIndex::Integer {
                        start: IntegerTerm::constant_i64(0).into(),
                        end: IntegerTerm::constant_i64(1).into(),
                    },
                    IntegerTerm::constant_i64(0),
                    collision_integer,
                    collision_c,
                    match_body(),
                )
                .into(),
            }],
        };
        let mut rewrite = TermRewrite::for_typed_variables(
            &program_replacements,
            &integer_replacements,
            &algebraic_replacements,
        );
        let IntegerTerm::AlgebraicMatch { arms, .. } = rewrite.integer(&match_with_fold) else {
            panic!("outer Integer match was not retained")
        };
        let [arm] = arms.as_slice() else {
            unreachable!()
        };
        assert!(matches!(
            &arm.bindings[0],
            AlgebraicValue::Integer(IntegerTerm::Variable(variable)) if *variable != collision_integer
        ));
        assert!(matches!(
            &arm.bindings[1],
            AlgebraicValue::Program(ProgramValue::Int32(OldMachineTerm::Variable(variable)))
                if *variable != collision_c
        ));
        let IntegerTerm::RangeFold {
            accumulator, item, ..
        } = arm.body.as_ref()
        else {
            panic!("nested Integer fold was not retained")
        };
        assert_ne!(*accumulator, collision_integer);
        // The fold item is an Integer carrier here.  A C replacement with
        // the same numeric ID must not force an Integer binder rename.
        assert_eq!(*item, collision_c);
        let mut free_integer = BTreeSet::new();
        crate::kernel::prelude::collect_integer_free_variables(
            arm.body.as_ref(),
            &mut free_integer,
        );
        assert!(free_integer.contains(&collision_integer));
        let mut free_c = BTreeSet::new();
        crate::kernel::prelude::collect_integer_capture_bitvector_variables(
            arm.body.as_ref(),
            &mut free_c,
        );
        assert!(free_c.contains(&collision_c));

        // A typed source may itself be shadowed while another source's
        // replacement mentions that same ID.  The shadowed source must not
        // suppress freshening needed to keep the other replacement free.
        let capture_accumulator = Variable(3_101_000);
        let capture_source = Variable(3_101_001);
        let capture_item = Variable(3_101_002);
        let capture_fold = IntegerTerm::range_fold(
            crate::kernel::IntegerRangeFoldIndex::Integer {
                start: IntegerTerm::constant_i64(0).into(),
                end: IntegerTerm::constant_i64(1).into(),
            },
            IntegerTerm::constant_i64(0),
            capture_accumulator,
            capture_item,
            IntegerTerm::var(capture_source),
        );
        let empty_c = BTreeMap::new();
        let capture_integer_replacements = BTreeMap::from([
            (capture_accumulator, IntegerTerm::constant_i64(0)),
            (capture_source, IntegerTerm::var(capture_accumulator)),
        ]);
        let empty_algebraic = BTreeMap::new();
        let mut capture_rewrite = TermRewrite::for_typed_variables(
            &empty_c,
            &capture_integer_replacements,
            &empty_algebraic,
        );
        let term_source_0 @ Term::Integer(_) =
            capture_rewrite.term(&Term::Integer(capture_fold.into()))
        else {
            unreachable!()
        };
        let (Some(IntegerTerm::RangeFold {
            accumulator, body, ..
        }),) = (term_source_0.integer_native(),)
        else {
            unreachable!()
        };
        assert_ne!(*accumulator, capture_accumulator);
        assert!(matches!(
            body.as_ref(),
            IntegerTerm::Variable(variable) if *variable == capture_accumulator
        ));
    }

    #[test]
    fn typed_match_binder_capture_precedes_source_shadowing() {
        let integer_x = Variable(3_102_000);
        let integer_y = Variable(3_102_001);
        let c_x = Variable(3_102_010);
        let c_y = Variable(3_102_011);
        let scrutinee = Variable(3_102_020);
        let variants: std::sync::Arc<[AlgebraicVariantType]> = vec![AlgebraicVariantType {
            name: "Wrapped".into(),
            fields: vec![
                AlgebraicValueType::Integer,
                AlgebraicValueType::Program(ProgramType::Int32),
            ],
        }]
        .into();
        let value_type = AlgebraicValueType::Algebraic {
            name: "TypedCaptureMatch".into(),
            arguments: vec![],
        };
        let algebraic_type = AlgebraicType {
            rigid: false,
            name: "TypedCaptureMatch".into(),
            arguments: vec![],
            variants: variants.clone(),
            schemas: std::sync::Arc::new(AlgebraicSchemas::new(BTreeMap::from([(
                value_type, variants,
            )]))),
        };
        let input = IntegerTerm::AlgebraicMatch {
            scrutinee: Box::new(AlgebraicTerm {
                algebraic_type,
                node: AlgebraicTermNode::Variable(scrutinee),
            }),
            arms: vec![AlgebraicIntegerMatchArm {
                binding_names: Default::default(),
                variant: "Wrapped".into(),
                bindings: vec![
                    AlgebraicValue::Integer(IntegerTerm::var(integer_x)),
                    AlgebraicValue::Program(ProgramValue::Int32(OldMachineTerm::Variable(c_x))),
                ],
                body: IntegerTerm::PureFunctionApplication(SharedPureApplication::intern(
                    "observe_typed_capture".into(),
                    vec![
                        PureFunctionArgument::Integer(IntegerTerm::var(integer_x).into()),
                        PureFunctionArgument::Integer(IntegerTerm::var(integer_y).into()),
                        PureFunctionArgument::Value(ProgramValue::Int32(OldMachineTerm::Variable(
                            c_x,
                        ))),
                        PureFunctionArgument::Value(ProgramValue::Int32(OldMachineTerm::Variable(
                            c_y,
                        ))),
                    ],
                ))
                .into(),
            }],
        };
        let program_replacements = BTreeMap::from([
            (
                c_x,
                TypedProgramValueReplacement::Bitvector(OldMachineTerm::constant(0)),
            ),
            (
                c_y,
                TypedProgramValueReplacement::Bitvector(OldMachineTerm::Variable(c_x)),
            ),
        ]);
        let integer_replacements = BTreeMap::from([
            (integer_x, IntegerTerm::constant_i64(0)),
            (integer_y, IntegerTerm::var(integer_x)),
        ]);
        let algebraic_replacements = BTreeMap::new();
        let mut rewrite = TermRewrite::for_typed_variables(
            &program_replacements,
            &integer_replacements,
            &algebraic_replacements,
        );
        let IntegerTerm::AlgebraicMatch { arms, .. } = rewrite.integer(&input) else {
            panic!("typed match was unexpectedly reduced")
        };
        let [arm] = arms.as_slice() else {
            unreachable!()
        };
        assert!(matches!(
            &arm.bindings[0],
            AlgebraicValue::Integer(IntegerTerm::Variable(variable)) if *variable != integer_x
        ));
        assert!(matches!(
            &arm.bindings[1],
            AlgebraicValue::Program(ProgramValue::Int32(OldMachineTerm::Variable(variable)))
                if *variable != c_x
        ));
        let IntegerTerm::PureFunctionApplication(application) = arm.body.as_ref() else {
            panic!("typed match body changed shape")
        };
        assert!(matches!(
            &application.arguments()[0],
            PureFunctionArgument::Integer(value)
                if matches!(value.as_ref(), IntegerTerm::Variable(variable) if *variable != integer_x)
        ));
        assert!(matches!(
            &application.arguments()[1],
            PureFunctionArgument::Integer(value)
                if matches!(value.as_ref(), IntegerTerm::Variable(variable) if *variable == integer_x)
        ));
        assert!(matches!(
            &application.arguments()[2],
            PureFunctionArgument::Value(ProgramValue::Int32(value))
                if matches!(value, OldMachineTerm::Variable(variable) if *variable != c_x)
        ));
        assert!(matches!(
            &application.arguments()[3],
            PureFunctionArgument::Value(ProgramValue::Int32(value))
                if matches!(value, OldMachineTerm::Variable(variable) if *variable == c_x)
        ));
    }

    /// The placeholder a refused scope leaves behind is only told from a
    /// rewritten term by asking. A debug build makes a caller that does not
    /// ask fail at the first test that reaches a refusing scope through it.
    #[cfg(debug_assertions)]
    #[test]
    #[should_panic(expected = "never read `refusal()`")]
    fn refused_scope_dropped_unread_panics_in_debug_builds() {
        let source_variable = Variable(3_104_000);
        let source = binary_node!(
            Int32,
            Add,
            Box::new(OldMachineTerm::Variable(source_variable)),
            Box::new(OldMachineTerm::constant(1)),
        );
        let replacement = OldMachineTerm::Variable(Variable(3_104_001));
        let fold = IntegerTerm::range_fold(
            crate::kernel::IntegerRangeFoldIndex::Int32 {
                start: crate::kernel::SharedIntegerRangeEndpoint::intern(OldMachineTerm::constant(
                    0,
                )),
                end: crate::kernel::SharedIntegerRangeEndpoint::intern(OldMachineTerm::constant(1)),
            },
            IntegerTerm::constant_i64(0),
            Variable(3_104_002),
            source_variable,
            IntegerTerm::Machine(crate::kernel::SharedMachineIntegerTerm::intern(
                crate::kernel::MachineIntegerType::Int32,
                source.clone(),
            )),
        );
        let mut rewrite = TermRewrite::for_bits(&source, &replacement);
        let _placeholder = rewrite.term(&Term::Integer(fold.into()));
    }

    #[test]
    fn composite_machine_source_is_rejected_under_program_binder() {
        let source_variable = Variable(3_103_000);
        let source = binary_node!(
            Int32,
            Add,
            Box::new(OldMachineTerm::Variable(source_variable)),
            Box::new(OldMachineTerm::constant(1)),
        );
        let replacement = OldMachineTerm::Variable(Variable(3_103_001));
        let fold = IntegerTerm::range_fold(
            crate::kernel::IntegerRangeFoldIndex::Int32 {
                start: crate::kernel::SharedIntegerRangeEndpoint::intern(OldMachineTerm::constant(
                    0,
                )),
                end: crate::kernel::SharedIntegerRangeEndpoint::intern(OldMachineTerm::constant(1)),
            },
            IntegerTerm::constant_i64(0),
            Variable(3_103_002),
            source_variable,
            IntegerTerm::Machine(crate::kernel::SharedMachineIntegerTerm::intern(
                crate::kernel::MachineIntegerType::Int32,
                source.clone(),
            )),
        );
        let mut rewrite = TermRewrite::for_bits(&source, &replacement);
        let output = rewrite.term(&Term::Integer(fold.into()));
        assert_eq!(rewrite.refusal(), Some(RewriteRefusal::UnsupportedScope));
        assert!(matches!(&(
            output), term_source_0 @ Term::Integer(_) if matches!((term_source_0.integer_native(),), (Some(IntegerTerm::Constant(value)),) if *value == 0.into())));
    }

    #[test]
    fn checked_substitution_collector_rejects_work_exhaustion() {
        let source = Variable(3_104_100);
        let atom = Proposition::MemoryLoadable {
            memory: SymbolicMemory::new(),
            base: Address::new(
                AddressBase::ExternalArgument,
                AddressOffset::scaled_int32_node(OldMachineTerm::Variable(source), 4),
            ),
            bytes: (OldMachineTerm::constant(4)).into(),
            wide: false,
        };
        let mut proposition = atom.clone();
        for _ in 0..64 {
            proposition = Proposition::And(Box::new(proposition), Box::new(atom.clone()));
        }

        let (exhausted, nodes) = with_checked_simple_budget(4, || {
            let mut collector = IntegerSubstitutionVariableCollector::checked();
            collector.collect(&proposition);
            (collector.exhausted(), collector.carriers.nodes)
        });
        assert!(exhausted, "checked collection must reject exhausted work");
        assert!(nodes <= 8, "collector continued after exhaustion: {nodes}");
    }

    #[cfg(test)]
    mod scaling_tests {
        include!("../../scaling_tests/kernel/proof/term_rewrite/tests.rs");
    }
}

#[cfg(test)]
mod pointer_integer_rewrite_tests {
    use super::*;

    #[test]
    fn a_generic_read_rewrite_keeps_the_substituted_cells_version_name() {
        let _session = crate::kernel::VerificationSession::enter();
        let from = OldPointer::new(
            Address::new(AddressBase::ExternalArgument, AddressOffset::constant(0)),
            ProgramType::Int32Pointer,
        );
        let to = OldPointer::new(
            Address::symbolic(Variable(996_021)),
            ProgramType::Int32Pointer,
        );
        let parameter = TypeParameterName::intern("RewriteReadT");
        let stored = ProgramValue::Parameter(Box::new(AlgebraicTerm {
            algebraic_type: parameter.algebraic_type(),
            node: AlgebraicTermNode::Variable(Variable(996_022)),
        }));
        let memory = crate::kernel::intern_memory(SymbolicMemory::new().store(
            Address::new(AddressBase::Heap(996_023), AddressOffset::constant(0)),
            stored.clone(),
        ));
        let read = AlgebraicTermNode::parameter_load_unsited(
            memory.clone(),
            from.address().clone(),
            parameter,
        );
        // A separate four-byte observation must not replace the generic
        // read's eight-byte origin when the same version name is reused.
        let partial = crate::kernel::intern_memory(memory.memory().clone().store(
            Address::new(AddressBase::Heap(996_023), AddressOffset::constant(0)),
            ProgramValue::UInt32(7u32.into()),
        ));
        let _ =
            crate::kernel::memory_history::canonical_value_load_memory(&partial, from.address(), 4);
        let expected =
            AlgebraicTermNode::parameter_load_unsited(memory, to.address().clone(), parameter);
        assert_ne!(expected, stored, "a rewritten logical read stays a read");
        let rewritten = TermRewrite::for_pointer_value_exact(&from, &to).value(&read);
        assert_eq!(rewritten, expected);
    }

    #[test]
    fn full_pointer_rewrite_keeps_the_read_version_and_state() {
        let _session = crate::kernel::VerificationSession::enter();
        let from = OldPointer::new(
            Address::symbolic(Variable(996_010)),
            ProgramType::Int32PointerPointer,
        );
        let to = OldPointer::new(
            Address::symbolic(Variable(996_011)),
            ProgramType::Int32PointerPointer,
        );
        let stored = ProgramValue::pointer(Address::symbolic(Variable(996_012)));
        let memory = SymbolicMemory::new().store(to.address().clone(), stored.clone());
        let read =
            memory.symbolic_pointer_version_load(None, from.address(), ProgramType::Int32Pointer);
        let expected =
            memory.symbolic_pointer_version_load(None, to.address(), ProgramType::Int32Pointer);
        assert_ne!(expected, stored, "a rewritten logical read stays a read");
        let rewrite = || TermRewrite::for_pointer_value_exact(&from, &to).value(&read);
        assert_eq!(rewrite(), expected);
        let later = memory.store(
            to.address().clone(),
            ProgramValue::pointer(Address::symbolic(Variable(996_013))),
        );
        let later_read =
            later.symbolic_pointer_version_load(None, to.address(), ProgramType::Int32Pointer);
        assert_ne!(later_read, expected);
        assert_eq!(
            rewrite(),
            expected,
            "later stores do not move the selected read"
        );
    }

    #[test]
    fn numeric_index_rewrite_keeps_nested_pointer_read_versions_and_states() {
        let _session = crate::kernel::VerificationSession::enter();
        let from = OldMachineTerm::Variable(Variable(996_020));
        let to = OldMachineTerm::Variable(Variable(996_021));
        let address = |index| {
            Address::new(
                AddressBase::ExternalArgument,
                AddressOffset::scale_int32(index, 8),
            )
        };
        let destination = address(to.clone());
        let stored = ProgramValue::pointer(Address::symbolic(Variable(996_022)));
        let memory = SymbolicMemory::new().store(destination.clone(), stored.clone());
        let shared = crate::kernel::intern_memory(memory.clone());
        let mut input = address(from.clone());
        let mut expected = destination.clone();
        for depth in 1..=32 {
            input = Address::version_read(&shared, &input);
            expected = Address::version_read(&shared, &expected);
            assert_eq!(
                TermRewrite::for_bits(&from, &to).pointer(&input),
                expected,
                "nested read depth {depth}",
            );
        }
        let later = memory.store(
            destination,
            ProgramValue::pointer(Address::symbolic(Variable(996_023))),
        );
        let _ = later.symbolic_pointer_version_load(
            None,
            &address(to.clone()),
            ProgramType::Int32Pointer,
        );
        assert_eq!(TermRewrite::for_bits(&from, &to).pointer(&input), expected);
        let value = ProgramValue::pointer(input);
        assert_eq!(
            TermRewrite::for_bits(&from, &to).value(&value),
            ProgramValue::pointer(expected),
            "all projections of the same read retain its version",
        );
    }

    #[test]
    fn numeric_rewriting_retains_the_existing_record_without_creating_one() {
        let context = PureFactContext::new();
        let pointer = OldPointer::new(
            Address::symbolic(Variable(996_001)),
            ProgramType::Int32Pointer,
        );
        let word = crate::kernel::eval::cast_program_value_to_type(
            ProgramValue::Pointer(pointer.clone()),
            ProgramType::UInt64,
            crate::kernel::eval::IntegerConversion::Modular,
            &mut Vec::new(),
            &context,
        )
        .unwrap();
        let from = crate::kernel::spec::program_value_bitvector_term(&word).unwrap();
        let alias = OldMachineTerm::Variable(Variable(996_002));
        let rewritten = TermRewrite::for_bits(&from, &alias).value(&word);
        let ProgramValue::PointerInteger(record) = &rewritten else {
            panic!("complete word")
        };
        assert_eq!(*record.pointer, pointer);
        assert_eq!(*record.numeric, ProgramValue::UInt64(alias.clone()));
        let back = crate::kernel::eval::cast_program_value_to_type(
            rewritten,
            ProgramType::Int32Pointer,
            crate::kernel::eval::IntegerConversion::Modular,
            &mut Vec::new(),
            &context,
        )
        .unwrap();
        assert_eq!(back, ProgramValue::Pointer(pointer));
        assert!(matches!(
            TermRewrite::for_bits(&alias, &from).value(&ProgramValue::UInt64(alias.clone())),
            ProgramValue::UInt64(_)
        ));
    }
}

thread_local! {
    /// Set while a rename runs: renaming a variable leaves a `match` on a
    /// known constructor as it was written instead of reducing it.
    static MATCH_REDUCTION_SUSPENDED: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// Whether a rename is running: a rewrite rebuilds changed nodes as they are
/// written, without folding or reducing them.
pub(crate) fn renaming() -> bool {
    MATCH_REDUCTION_SUSPENDED.with(std::cell::Cell::get)
}

/// Runs `operation` with match reduction suspended, as a rename does.
pub(crate) fn without_match_reduction<R>(operation: impl FnOnce() -> R) -> R {
    struct Restore(bool);
    impl Drop for Restore {
        fn drop(&mut self) {
            MATCH_REDUCTION_SUSPENDED.with(|flag| flag.set(self.0));
        }
    }
    let _restore = Restore(MATCH_REDUCTION_SUSPENDED.with(|flag| flag.replace(true)));
    operation()
}

#[cfg(test)]
mod comparison_read_batch_tests {
    use super::*;

    fn atom(value: OldMachineTerm) -> Proposition {
        Proposition::Predicate {
            name: "selected_read".into(),
            arguments: vec![Term::Bitvector32(value.into())],
        }
    }

    #[test]
    fn batch_read_comparison_retains_literal_machine_truth_and_falsehood() {
        let _session = crate::kernel::VerificationSession::enter();
        let memory = crate::kernel::intern_memory(SymbolicMemory::new());
        for (format, kind) in [
            (MachineIntegerType::Int32, LoadKind::Int32),
            (MachineIntegerType::UInt32, LoadKind::UInt32),
            (MachineIntegerType::Int64, LoadKind::Bits64),
            (MachineIntegerType::UInt64, LoadKind::Bits64),
        ] {
            let read = crate::kernel::OldMachineTerm::read_named(
                ProgramPoint::at(&memory),
                Address::symbolic(Variable(401_020)),
                kind,
            );
            let literal = |bits| {
                OldMachineTerm::machine_constant(
                    crate::kernel::MachineIntegerConstant::from_bits(format.format(), bits)
                        .unwrap(),
                )
            };
            let three = literal(3);
            for (relation, rhs, expected) in [
                (CompareRelation::Equal, 3, true),
                (CompareRelation::Equal, 4, false),
                (CompareRelation::LessThan, 4, true),
                (CompareRelation::LessThan, 3, false),
            ] {
                let input = Proposition::condition_is(
                    OldConditionTerm::Compare {
                        format,
                        relation,
                        left: Box::new(read.clone()),
                        right: Box::new(literal(rhs)),
                    },
                    true,
                );
                assert_eq!(
                    TermRewrite::comparison_read_batch(&input, [(read.clone(), three.clone())]),
                    Some(Proposition::condition_is(
                        OldConditionTerm::Constant(expected),
                        true
                    )),
                );
                // Ordinary rewriting retains the machine comparison syntax.
                let mut structural = TermRewrite::for_bits(&read, &three);
                let result = structural.proposition(&input);
                assert!(structural.refusal().is_none());
                assert!(
                    matches!(&result, condition_source_0 @ Proposition::ConditionIs(_, true) if matches!(condition_source_0.old_condition(), Some((OldConditionTerm::Compare { .. }, _))))
                );
            }
        }
    }

    #[test]
    fn batch_read_comparison_is_simultaneous_and_capture_avoiding() {
        let _session = crate::kernel::VerificationSession::enter();
        let memory = crate::kernel::intern_memory(SymbolicMemory::new());
        let read = |index| {
            crate::kernel::OldMachineTerm::read_named(
                ProgramPoint::at(&memory),
                Address::symbolic(Variable(index)),
                LoadKind::Int32,
            )
        };
        let first = read(401_001);
        let second = read(401_002);
        let input = Proposition::And(
            Box::new(atom(first.clone())),
            Box::new(atom(second.clone())),
        );
        let actual = TermRewrite::comparison_read_batch(
            &input,
            [
                (first, second.clone()),
                (second.clone(), OldMachineTerm::constant(7)),
            ],
        )
        .expect("selected carriers");
        assert_eq!(
            actual,
            Proposition::And(
                Box::new(atom(second)),
                Box::new(atom(OldMachineTerm::constant(7))),
            )
        );

        let source = Variable(401_010);
        let binder = Variable(401_011);
        let input = crate::kernel::quantifiers::test_forall(
            BinderName::written("k"),
            binder,
            Sort::ProgramInt32,
            Proposition::Predicate {
                name: "pair".into(),
                arguments: vec![
                    Term::Bitvector32(OldMachineTerm::Variable(source).into()),
                    Term::Bitvector32(OldMachineTerm::Variable(binder).into()),
                ],
            },
        );
        let actual = TermRewrite::comparison_read_batch(
            &input,
            [(
                OldMachineTerm::Variable(source),
                OldMachineTerm::Variable(binder),
            )],
        )
        .expect("quantified carrier");
        let Proposition::ForAll { var, body, .. } = actual else {
            panic!("quantifier")
        };
        assert_ne!(*var, binder);
        assert_eq!(
            *body,
            Proposition::Predicate {
                name: "pair".into(),
                arguments: vec![
                    Term::Bitvector32(OldMachineTerm::Variable(binder).into()),
                    Term::Bitvector32(OldMachineTerm::Variable(*var).into())
                ],
            }
        );
        // A descriptor depending on the bound address is not a global read
        // occurrence to replace using an outer selected substitution.
        let scoped_read = read(binder.0);
        let scoped = crate::kernel::quantifiers::test_forall(
            BinderName::written("address"),
            binder,
            Sort::ProgramInt32,
            atom(scoped_read.clone()),
        );
        assert_eq!(
            TermRewrite::comparison_read_batch(
                &scoped,
                [(scoped_read, OldMachineTerm::constant(9)),]
            ),
            Some(scoped)
        );

        let scoped_pointer = Address::symbolic(binder);
        let scoped_name =
            OldMachineTerm::Variable(crate::kernel::eval::load_variable_for_exact_cell(
                &memory,
                &scoped_pointer,
                LoadKind::Int32,
                4,
            ));
        let scoped_named = crate::kernel::quantifiers::test_forall(
            BinderName::written("address"),
            binder,
            Sort::ProgramInt32,
            atom(scoped_name.clone()),
        );
        for source in [scoped_name, read(binder.0)] {
            assert_eq!(
                TermRewrite::comparison_read_batch(
                    &scoped_named,
                    [(source, OldMachineTerm::constant(9)),]
                ),
                Some(scoped_named.clone())
            );
        }

        // Equal numeric IDs in different carriers are independent binders.
        let named_address_read =
            OldMachineTerm::Variable(crate::kernel::eval::load_variable_for_exact_cell(
                &memory,
                &scoped_pointer,
                LoadKind::Int32,
                4,
            ));
        for body_read in [read(binder.0), named_address_read.clone()] {
            let input = crate::kernel::quantifiers::test_forall(
                BinderName::written("integer_k"),
                binder,
                Sort::Integer,
                atom(body_read),
            );
            let expected = crate::kernel::quantifiers::test_forall(
                BinderName::written("integer_k"),
                binder,
                Sort::Integer,
                atom(OldMachineTerm::constant(9)),
            );
            for source in [read(binder.0), named_address_read.clone()] {
                assert_eq!(
                    TermRewrite::comparison_read_batch(
                        &input,
                        [(source, OldMachineTerm::constant(9)),]
                    ),
                    Some(expected.clone())
                );
            }
        }

        let shadowed = crate::kernel::quantifiers::test_exists(
            "read".into(),
            source,
            Sort::ProgramInt32,
            atom(OldMachineTerm::Variable(source)),
        );
        assert_eq!(
            TermRewrite::comparison_read_batch(
                &shadowed,
                [(
                    OldMachineTerm::Variable(source),
                    OldMachineTerm::constant(9)
                ),]
            ),
            Some(shadowed)
        );
    }

    #[test]
    fn batch_read_comparison_respects_internal_binders_for_raw_and_named_reads() {
        let _session = crate::kernel::VerificationSession::enter();
        let binder = Variable(403_001);
        let accumulator = Variable(403_002);
        let pointer = Address::symbolic(binder);
        let memory = crate::kernel::intern_memory(SymbolicMemory::new());
        let raw = crate::kernel::OldMachineTerm::read_named(
            ProgramPoint::at(&memory),
            pointer.clone(),
            LoadKind::Int32,
        );
        let named = OldMachineTerm::Variable(crate::kernel::eval::load_variable_for_exact_cell(
            &memory,
            &pointer,
            LoadKind::Int32,
            4,
        ));
        let variants: std::sync::Arc<[AlgebraicVariantType]> = vec![AlgebraicVariantType {
            name: "Bound".into(),
            fields: vec![AlgebraicValueType::Program(ProgramType::Int32)],
        }]
        .into();
        let algebraic_type = AlgebraicType {
            rigid: false,
            name: "BatchBound".into(),
            arguments: vec![],
            variants: variants.clone(),
            schemas: std::sync::Arc::new(AlgebraicSchemas::new(BTreeMap::from([(
                AlgebraicValueType::Algebraic {
                    name: "BatchBound".into(),
                    arguments: vec![],
                },
                variants,
            )]))),
        };
        for read in [&raw, &named] {
            let machine_fold = OldMachineTerm::RangeFold {
                start: Box::new(OldMachineTerm::constant(0)),
                end: Box::new(OldMachineTerm::constant(2)),
                initial: Box::new(OldMachineTerm::constant(0)),
                accumulator,
                item: binder,
                body: Box::new(read.clone()),
            };
            let machine_match = OldMachineTerm::AlgebraicMatch {
                scrutinee: Box::new(AlgebraicTerm {
                    algebraic_type: algebraic_type.clone(),
                    node: AlgebraicTermNode::Variable(Variable(403_003)),
                }),
                arms: vec![AlgebraicBitvectorMatchArm {
                    binding_names: Default::default(),
                    variant: "Bound".into(),
                    bindings: vec![AlgebraicValue::Program(ProgramValue::Int32(
                        OldMachineTerm::Variable(binder),
                    ))],
                    body: read.clone(),
                }],
            };
            let integer_fold = IntegerTerm::range_fold(
                IntegerRangeFoldIndex::Int32 {
                    start: SharedIntegerRangeEndpoint::intern(OldMachineTerm::constant(0)),
                    end: SharedIntegerRangeEndpoint::intern(OldMachineTerm::constant(2)),
                },
                IntegerTerm::constant_i64(0),
                accumulator,
                binder,
                IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
                    MachineIntegerType::Int32,
                    read.clone(),
                )),
            );
            for argument in [
                Term::Bitvector32(machine_fold.into()),
                Term::Bitvector32(machine_match.into()),
                Term::Integer(integer_fold.into()),
            ] {
                let input = Proposition::Predicate {
                    name: "scoped_read".into(),
                    arguments: vec![argument],
                };
                for source in [&raw, &named] {
                    let result = TermRewrite::comparison_read_batch(
                        &input,
                        [(source.clone(), OldMachineTerm::constant(9))],
                    )
                    .expect("internal bound read remains scoped");
                    assert_eq!(result, input);
                }
            }
        }
    }

    #[test]
    fn batch_read_comparison_preserves_states_and_sealed_resources() {
        let _session = crate::kernel::VerificationSession::enter();
        let source = Variable(402_001);
        let pointer = Address::symbolic(Variable(402_002));
        let memory = crate::kernel::intern_memory(SymbolicMemory::new().store(
            pointer.clone(),
            ProgramValue::Int32(OldMachineTerm::Variable(source)),
        ));
        let untouched = crate::kernel::OldMachineTerm::read_named(
            ProgramPoint::at(&memory),
            pointer,
            LoadKind::Int32,
        );
        let sealed = Resource::MutexGuard(MutexIdentity {
            epoch: Some(123),
            mutex: Address::new(
                "sealed".into(),
                AddressOffset::scaled_int32_node(OldMachineTerm::Variable(source), 1),
            ),
        });
        let input = Proposition::And(
            Box::new(atom(untouched)),
            Box::new(Proposition::ResourceContains {
                parent: Box::new(sealed),
                child: Box::new(Resource::Emp),
            }),
        );
        assert_eq!(
            TermRewrite::comparison_read_batch(
                &input,
                [(
                    OldMachineTerm::Variable(source),
                    OldMachineTerm::constant(9)
                ),]
            ),
            Some(input)
        );
    }
}

#[cfg(test)]
mod pointer_association_boundary_tests {
    use super::*;

    #[test]
    fn shared_pointer_association_requires_exact_nonoverflow_source() {
        let _session = VerificationSession::enter();
        let ty = MachineIntegerType::Int32;
        let x = OldMachineTerm::Variable(Variable(1081801));
        let y = OldMachineTerm::Variable(Variable(1081802));
        let z = OldMachineTerm::Variable(Variable(1081803));
        let native = OldMachineTerm::add(x, y);
        let left = KernelTerm::retained_machine_operand(ty, MachineOperandView::Old(&native));
        let right = KernelTerm::retained_machine_operand(ty, MachineOperandView::Old(&z));
        let sum = KernelTerm::machine_binary_shared(
            ty,
            MachineBinaryOp::Add,
            [left.clone(), right.clone()],
        );
        let scaled = |root| {
            AddressOffset::int32_scaled(SharedMachineIntegerTerm::from_shared(ty, root).unwrap(), 4)
        };
        let condition = OldConditionTerm::AddressOffsetEqual(
            Box::new(AddressOffset::raw_add(scaled(left), scaled(right))),
            Box::new(scaled(sum)),
        );
        let guard = OldConditionTerm::signed_add_overflows(native, z);
        let present = HashMap::from([(guard.clone(), false)]);
        let opposite = HashMap::from([(guard, true)]);
        let absent = HashMap::new();
        let exports = KernelTermExport::machine_export_count();
        assert_eq!(
            TermRewrite::for_conditions(&present).condition(&condition),
            OldConditionTerm::Constant(true)
        );
        for conditions in [&absent, &opposite] {
            assert_ne!(
                TermRewrite::for_conditions(conditions).condition(&condition),
                OldConditionTerm::Constant(true)
            );
        }
        assert_eq!(KernelTermExport::machine_export_count(), exports);
    }
}
