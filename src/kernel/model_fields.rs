//! What a fresh model-field variable stands for.
//!
//! A resource instance that survives a call keeps its identity and gets fresh
//! field variables, so a contract that promises nothing about a field leaves
//! the reader holding `v1000002`. There is nothing in the term to recover: the
//! field value is stored *inside* the instance fact, and a projection is
//! resolved at lowering to whatever instance carries that identity then.
//!
//! So the mint records it. Every fresh field variable is registered where it is
//! minted — with the instance it belongs to, the field of the schema it is, and
//! **why** it was minted, which the mint site is the only place that knows. A
//! refusal then spells the variable `c.rank` and says which step replaced it,
//! instead of printing a kernel name.
//!
//! This is the model-field counterpart of the load-variable registry
//! (`crate::kernel::eval::memory_loads`), and it is kept the same way: one map
//! insert per fresh field variable at the site that already mints it, bounded,
//! and emptied when a `VerificationSession` starts, because a field variable's
//! meaning belongs to the verification that issued it.
//!
//! Diagnostics and proof expansion use this provenance to recover a source
//! name. No kernel rule or premise depends on it.

use crate::kernel::primitives::{
    AlgebraicTerm, AlgebraicTermNode, InstanceId, IntegerTerm, OldMachineTerm, Variable,
};
use std::sync::Arc;

/// The variable a freshly minted field value is, for all three field kinds. A
/// value that is not a bare variable was not minted as an arbitrary model and
/// is not registered.
pub(crate) fn algebraic_value_variable<'a>(
    value: impl Into<crate::kernel::ResourceFieldValue<'a>>,
) -> Option<Variable> {
    match value.into() {
        crate::kernel::ResourceFieldValue::Integer(IntegerTerm::Variable(variable)) => {
            Some(*variable)
        }
        crate::kernel::ResourceFieldValue::Algebraic(AlgebraicTerm {
            node: AlgebraicTermNode::Variable(variable),
            ..
        }) => Some(*variable),
        crate::kernel::ResourceFieldValue::Program(value) => {
            match crate::kernel::spec::program_value_bitvector_term(value) {
                Some(OldMachineTerm::Variable(variable)) => Some(variable),
                _ => None,
            }
        }
        _ => None,
    }
}

/// The bound on each table, in the style of the other per-session memos: a
/// verification that somehow mints more field variables than this loses the
/// spellings rather than growing without limit.
const MAX_REGISTERED: usize = 100_000;

/// Which step replaced an instance's model, recorded at the mint.
///
/// This is not a guess reconstructed from a refusal site: the recorded memory
/// history says nothing about model fields (no `MemoryDerivation` edge carries it),
/// and the only place that knows why a field vector is fresh is the place that
/// made it fresh.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum ModelMint {
    /// A call returned ownership of the instance. Its identity survived and its
    /// field values did not, so only the callee's own `ensures` relate the two.
    CallReturn { callee: Arc<str> },
    /// A contract's `produces` created the instance at the call.
    Produced { callee: Arc<str> },
    /// A loop head havocked the model of a binder the loop declares, so the
    /// body starts from an arbitrary model of it.
    LoopHead,
    /// Contract/implementation refinement drew one arbitrary model for both
    /// sides of the comparison.
    Refinement,
    /// A join's `ensuring` interface named the instance. Its arms may hold
    /// different models, so the rejoined proof holds an arbitrary one and
    /// knows of it only what the interface's facts state.
    Join,
    /// The contract's own entry model, which `old(..)` names. This one is
    /// minted on the surface side, where the binder is elaborated. Keep its
    /// spelling with the variable because a resource identity can be reused
    /// by a different binder.
    ContractEntry { owner: Arc<str> },
}

/// One fresh model-field variable: which instance's field it is, and why it
/// exists.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ModelFieldOrigin {
    /// The instance the field belongs to, by the identity the state indexes.
    pub(crate) identity: InstanceId,
    /// The field's declared name, for spelling `c.rank`.
    pub(crate) field: Arc<str>,
    pub(crate) field_index: usize,
    pub(crate) minted_by: ModelMint,
}

impl ModelFieldOrigin {
    pub(crate) fn owner_spelling(&self) -> Option<Arc<str>> {
        match &self.minted_by {
            ModelMint::ContractEntry { owner } => Some(owner.clone()),
            _ => registered_instance_spelling(self.identity),
        }
    }
}

thread_local! {
    static OPENED_CHILD_IDS: std::cell::RefCell<
        std::collections::HashMap<crate::kernel::primitives::ResourceOccurrenceId, std::collections::HashMap<String, InstanceId>>,
    > = std::cell::RefCell::new(std::collections::HashMap::new());
    static OPENED_CHILD_COUNT: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
    static MODEL_FIELD_VARIABLES: std::cell::RefCell<
        std::collections::HashMap<Variable, ModelFieldOrigin>,
    > = std::cell::RefCell::new(std::collections::HashMap::new());
    static INSTANCE_SPELLINGS: std::cell::RefCell<
        std::collections::HashMap<InstanceId, Arc<str>>,
    > = std::cell::RefCell::new(std::collections::HashMap::new());
    /// The field of a schema an `(instance, index)` key is, so a refusal that
    /// holds the tracker's key rather than a term can still spell it. Filled by
    /// the same insert as the table above.
    static INSTANCE_FIELD_NAMES: std::cell::RefCell<
        std::collections::HashMap<(InstanceId, usize), Arc<str>>,
    > = std::cell::RefCell::new(std::collections::HashMap::new());
    /// The population whose function-entry count each variable is, so a
    /// diagnostic spells it `old(count(R(p, _)))`.
    static POPULATION_ENTRY_COUNTS: std::cell::RefCell<
        std::collections::HashMap<Variable, PopulationEntryCount>,
    > = std::cell::RefCell::new(std::collections::HashMap::new());
}

/// The default identity of a child exposed from this exact owned occurrence.
/// Replaying an opening selects the same ID; folding a replacement creates a
/// new occurrence. These instance-only IDs are disjoint from source IDs and
/// the kernel execution counter.
pub(super) fn opened_child_identity(
    parent: crate::kernel::primitives::ResourceOccurrenceId,
    slot: &str,
) -> Option<InstanceId> {
    crate::instrumentation::record_deterministic_work(1);
    OPENED_CHILD_IDS.with(|registry| {
        let mut registry = registry.borrow_mut();
        let children = registry.entry(parent).or_default();
        if let Some(identity) = children.get(slot) {
            return Some(*identity);
        }
        OPENED_CHILD_COUNT.with(|count| {
            static NEXT: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(1 << 62);
            if count.get() >= MAX_REGISTERED {
                return None;
            }
            count.set(count.get() + 1);
            let identity = InstanceId::from_variable(Variable(
                NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed),
            ));
            children.insert(slot.to_owned(), identity);
            Some(identity)
        })
    })
}

/// Records one fresh field variable. One insert, at the site that already
/// allocated the variable, so the cost is one entry per field of the instance
/// whose model was just replaced.
pub(crate) fn register_model_field_variable(variable: Variable, origin: ModelFieldOrigin) {
    INSTANCE_FIELD_NAMES.with(|registry| {
        let mut registry = registry.borrow_mut();
        if registry.len() >= MAX_REGISTERED {
            registry.clear();
        }
        registry.insert((origin.identity, origin.field_index), origin.field.clone());
    });
    MODEL_FIELD_VARIABLES.with(|registry| {
        let mut registry = registry.borrow_mut();
        if registry.len() >= MAX_REGISTERED {
            registry.clear();
        }
        registry.insert(variable, origin);
    });
}

/// The reader's own spelling of one field of one instance, `c.rank`, from the
/// tracker's key rather than from a term.
pub(crate) fn instance_field_surface(identity: InstanceId, field_index: usize) -> Option<String> {
    let owner = registered_instance_spelling(identity)?;
    let field = INSTANCE_FIELD_NAMES
        .with(|registry| registry.borrow().get(&(identity, field_index)).cloned())?;
    Some(format!("{owner}.{field}"))
}

/// What a model-field variable stands for, if this session minted it.
pub(crate) fn registered_model_field_origin(variable: Variable) -> Option<ModelFieldOrigin> {
    MODEL_FIELD_VARIABLES.with(|registry| registry.borrow().get(&variable).cloned())
}

/// Records the name a reader wrote for one resource instance — the contract's
/// binder, `c`. The surface supplies it where it resolves a field access,
/// because an instance identity is a kernel variable and only the surface knows
/// what it was called.
pub(crate) fn register_instance_spelling(identity: InstanceId, spelling: &str) {
    INSTANCE_SPELLINGS.with(|registry| {
        let mut registry = registry.borrow_mut();
        if registry.len() >= MAX_REGISTERED {
            registry.clear();
        }
        registry
            .entry(identity)
            .or_insert_with(|| Arc::from(spelling));
    });
}

pub(crate) fn registered_instance_spelling(identity: InstanceId) -> Option<Arc<str>> {
    INSTANCE_SPELLINGS.with(|registry| registry.borrow().get(&identity).cloned())
}

/// The reader's own spelling of a model-field variable: `c.rank`, or
/// `old(c.rank)` when the variable is the contract's entry model, which is the
/// version `old(..)` names in source.
///
/// `None` unless both halves are known: a half-spelled name would be worse
/// than the kernel variable it replaced, because it would look like source the
/// reader could search for.
pub(crate) fn model_field_surface(variable: Variable) -> Option<String> {
    let origin = registered_model_field_origin(variable)?;
    let owner = origin.owner_spelling()?;
    let field = format!("{owner}.{}", origin.field);
    Some(match origin.minted_by {
        ModelMint::ContractEntry { .. } => format!("old({field})"),
        _ => field,
    })
}

/// `old(owner.field)` for a variable minted as a contract's own entry model:
/// that spelling always denotes it, since the entry model never changes.
/// `None` for any other variable, including a model a later step replaced,
/// whose source name depends on the point it is read at.
pub(crate) fn entry_model_field_surface(variable: Variable) -> Option<String> {
    let origin = registered_model_field_origin(variable)?;
    let ModelMint::ContractEntry { owner } = &origin.minted_by else {
        return None;
    };
    Some(format!("old({owner}.{})", origin.field))
}

/// A population's function-entry count, as a diagnostic spells it: the
/// family, its anchor pointer, and how many wildcard arguments follow it.
#[derive(Clone, Debug)]
pub(crate) struct PopulationEntryCount {
    pub(crate) family: Arc<str>,
    pub(crate) anchor: crate::kernel::Address,
    pub(crate) wildcards: usize,
    /// An exact member's arguments, anchor first, for the entry count of
    /// one member, `old(count(R(a, k)))`; `None` for a population's total.
    pub(crate) member: Option<Arc<[crate::kernel::AlgebraicValue]>>,
}

/// Records that `variable` is the function-entry count of a population.
pub(crate) fn register_population_entry_count(variable: Variable, count: PopulationEntryCount) {
    POPULATION_ENTRY_COUNTS.with(|registry| {
        let mut registry = registry.borrow_mut();
        if registry.len() >= MAX_REGISTERED {
            registry.clear();
        }
        registry.insert(variable, count);
    });
}

pub(crate) fn registered_population_entry_count(
    variable: Variable,
) -> Option<PopulationEntryCount> {
    POPULATION_ENTRY_COUNTS.with(|registry| registry.borrow().get(&variable).cloned())
}

/// The model-field registry as one value a reusable session captures and
/// restores.
#[derive(Clone)]
pub(crate) struct ModelFieldRegistryState {
    variables: std::collections::HashMap<Variable, ModelFieldOrigin>,
    spellings: std::collections::HashMap<InstanceId, Arc<str>>,
    field_names: std::collections::HashMap<(InstanceId, usize), Arc<str>>,
    entry_counts: std::collections::HashMap<Variable, PopulationEntryCount>,
}

pub(crate) fn capture_model_field_registry() -> ModelFieldRegistryState {
    ModelFieldRegistryState {
        variables: MODEL_FIELD_VARIABLES.with(|registry| registry.borrow().clone()),
        spellings: INSTANCE_SPELLINGS.with(|registry| registry.borrow().clone()),
        field_names: INSTANCE_FIELD_NAMES.with(|registry| registry.borrow().clone()),
        entry_counts: POPULATION_ENTRY_COUNTS.with(|registry| registry.borrow().clone()),
    }
}

pub(crate) fn restore_model_field_registry(state: &ModelFieldRegistryState) {
    MODEL_FIELD_VARIABLES.with(|registry| *registry.borrow_mut() = state.variables.clone());
    INSTANCE_SPELLINGS.with(|registry| *registry.borrow_mut() = state.spellings.clone());
    INSTANCE_FIELD_NAMES.with(|registry| *registry.borrow_mut() = state.field_names.clone());
    POPULATION_ENTRY_COUNTS.with(|registry| *registry.borrow_mut() = state.entry_counts.clone());
}

pub(crate) fn clear_model_field_registry() {
    OPENED_CHILD_IDS.with(|registry| registry.borrow_mut().clear());
    OPENED_CHILD_COUNT.with(|count| count.set(0));
    MODEL_FIELD_VARIABLES.with(|registry| registry.borrow_mut().clear());
    INSTANCE_SPELLINGS.with(|registry| registry.borrow_mut().clear());
    INSTANCE_FIELD_NAMES.with(|registry| registry.borrow_mut().clear());
    POPULATION_ENTRY_COUNTS.with(|registry| registry.borrow_mut().clear());
}
