//! Checked read summaries for `Integer`-valued range-fold functions, and the
//! test-only application-framing rule they support
//! (`docs/internals/fold-read-ranges.md`).
//!
//! An `Integer` function over an `int32[]` argument is an opaque application
//! whose array argument names a whole-block state. A fact about
//! `unmarked(visited, 0, i)` therefore dies at `visited[i] = 1` even though
//! the fold reads only the cells below `i`. This module adds two independent
//! checks that together bridge that store, and nothing else:
//!
//! 1. **Definition checking** ([`CheckedFoldReadSummary::check`]). The body of
//!    one declared function, lowered to the kernel's
//!    specification vocabulary, is walked against an explicit whitelist. It is
//!    accepted only when it is a top-level `int32`-indexed range fold over
//!    an `int32[]` or `uint8[]` whose
//!    every memory read is exactly the one array parameter at the fold's own
//!    item binder. Anything else -- another index, a nested fold, a call, an
//!    address escape, a read in an endpoint or the initial accumulator --
//!    declines the *whole* definition. The resulting handle's fields are
//!    private, so the caller supplies a body and the checker constructs its summary.
//! 2. **Framing in tests.** Two applications of
//!    one summarized function whose arguments agree except for the array
//!    argument's state are equal when every recorded step between the two
//!    states is shown not to write a byte of the instantiated interval
//!    `base + 4*k` for `start <= k < end`. Each step is decided from its own
//!    recorded write set and the querying context's exact facts; nothing is
//!    recorded on the edge or cached, so the answer is a checked derivation of
//!    this query, never an assumption-free name.
//!
//! **Why this is sound.** The value of `f(array-ref(m, p), args)` is the fold
//! body evaluated with its reads at `m` (an `unfold` states it at a state whose
//! block version is `m`). Definition checking guarantees the body reads memory
//! only as its typed cell `p + width*k` for the fold item `k`, and the fold
//! visits exactly `start <= k < end`, so the value is a function of the
//! arguments and of those cells' contents alone (finite fold induction: equal
//! initial values, and each iteration sees the same accumulator, index and
//! cell). Framing guarantees those cells hold the same bytes at both
//! states. Pointer offsets are exact `i64` sums of sign-extended scaled
//! `int32` terms (`OldAddressOffset::Int32Scaled`), so the cells occupy the
//! contiguous bytes `[p + 4*start, p + 4*end)` with no wraparound, and a write
//! misses them exactly when it ends at or below the first byte or starts at or
//! above the last one. Emptiness is used only when a fact or the syntax proves
//! `end <= start`.
//!
//! **What it never does.** It inserts no viewability or initialization guard,
//! produces no resource fact, and grants no C access: the only thing it proves
//! is a logical equality between two opaque applications. It crosses no
//! allocation, free, lifetime end, loop havoc or claim edge except where
//! the kernel's assumption-free block rule already proves the whole block
//! untouched. Cache-only forgetting preserves bytes and may be crossed; it
//! supplies no evidence for a subsequent write.

#[cfg(test)]
use crate::kernel::MachineIntegerType;
use crate::kernel::{bits32_constant, constant_u32};

use super::primitives::*;

/// One declared `Integer` function body, in the kernel's specification
/// vocabulary, with its parameters left as the names the body refers to.
///
/// This is program data. The kernel decides
/// whether it admits a read summary.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct FoldReadDefinition {
    name: String,
    parameters: Vec<(String, ProgramType)>,
    body: SpecIntegerExpression,
}

impl FoldReadDefinition {
    pub fn new(
        name: impl Into<String>,
        parameters: Vec<(String, ProgramType)>,
        body: SpecIntegerExpression,
    ) -> Self {
        Self {
            name: name.into(),
            parameters,
            body,
        }
    }

    fn fingerprint(&self) -> u64 {
        use std::hash::{Hash, Hasher};
        crate::instrumentation::record_deterministic_work(1);
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        self.hash(&mut hasher);
        hasher.finish()
    }
}

/// Where one endpoint of the summarized fold comes from.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum FoldEndpointTemplate {
    /// The `int32` scalar parameter at this position.
    Parameter(usize),
    /// A literal `int32` value.
    Literal(u32),
}

/// A kernel-checked read summary of one declared function.
///
/// Its only constructor is [`Self::check`], which validates the declared body.
/// Every field is private: a caller outside this module can hold and pass a
/// summary but cannot state one, so no interval reaches the framing rule
/// except the one the body's own fold writes.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CheckedFoldReadSummary {
    name: String,
    fingerprint: u64,
    parameter_types: Vec<ProgramType>,
    array_parameter: usize,
    element_width: u32,
    start: FoldEndpointTemplate,
    end: FoldEndpointTemplate,
    accumulator: Variable,
    item: Variable,
}

/// Why a definition admits no read summary. Every reason declines the whole
/// definition; nothing is summarized partially.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum FoldReadDecline {
    /// The body is not a top-level range fold over `int32` endpoints.
    NotATopLevelInt32Fold,
    /// The parameters are not exactly one `int32[]` array and `int32` scalars.
    UnsupportedParameters(String),
    /// An endpoint is neither an `int32` scalar parameter nor a literal.
    UnsupportedEndpoint,
    /// The initial accumulator reads memory, the accumulator, or the item, or
    /// uses a constructor outside the whitelist.
    UnsupportedInitialValue(String),
    /// The body reads the array somewhere other than at the fold's own item.
    ReadOutsideFoldIndex,
    /// The body uses a constructor outside the whitelist: a call (opaque
    /// helper or recursion), a nested fold, another memory, an address
    /// escape, a quantifier, a resource or a free variable.
    UnsupportedConstruct(String),
}

impl std::fmt::Display for FoldReadDecline {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NotATopLevelInt32Fold => {
                formatter.write_str("its body is not a top-level `int32`-indexed range fold")
            }
            Self::UnsupportedParameters(detail) => write!(
                formatter,
                "its parameters are not one `int32[]` array plus `int32` scalars ({detail})"
            ),
            Self::UnsupportedEndpoint => formatter
                .write_str("a fold endpoint is not an `int32` scalar parameter or a literal"),
            Self::UnsupportedInitialValue(detail) => write!(
                formatter,
                "the fold's initial value is not a memory-independent term ({detail})"
            ),
            Self::ReadOutsideFoldIndex => formatter.write_str(
                "the fold body reads the array at an index other than the fold's own binder",
            ),
            Self::UnsupportedConstruct(detail) => write!(
                formatter,
                "the fold body uses a construct outside the checked subset ({detail})"
            ),
        }
    }
}

/// The instantiated support of one application: the typed `int32` cells
/// `base + element_width * k` for `start <= k < end`, read at `memory`.
#[cfg(test)]
#[derive(Clone, Debug)]
pub(crate) struct FoldReadInterval {
    pub(crate) memory: SymbolicMemory,
    pub(crate) base: OldAddress,
    pub(crate) start: SharedMachineIntegerTerm,
    pub(crate) end: SharedMachineIntegerTerm,
    pub(crate) element_width: u32,
}

/// What the body walk may see at one position.
#[derive(Clone, Copy, Eq, PartialEq)]
enum Scope {
    /// The endpoints and the initial value: no accumulator, item, or read.
    Outside,
    /// The fold body: the accumulator, the item and the exact array read.
    Body,
}

struct BodyChecker<'a> {
    parameters: &'a [(String, ProgramType)],
    array_name: &'a str,
    element_type: ProgramType,
    accumulator: Variable,
    item: Variable,
}

impl CheckedFoldReadSummary {
    /// Validates one declared body and returns its read summary, or the reason
    /// the definition declines. Work is one unit per visited specification
    /// node, so the check is linear in the selected body.
    pub fn check(definition: &FoldReadDefinition) -> Result<Self, FoldReadDecline> {
        let parameters = &definition.parameters;
        let mut array_parameter = None;
        for (index, (name, program_type)) in parameters.iter().enumerate() {
            crate::instrumentation::record_deterministic_work(1);
            match program_type {
                ProgramType::Int32Pointer | ProgramType::UInt8Pointer => {
                    if array_parameter.replace(index).is_some() {
                        return Err(FoldReadDecline::UnsupportedParameters(format!(
                            "a second array parameter `{name}`"
                        )));
                    }
                }
                ProgramType::Int32 => {}
                other => {
                    return Err(FoldReadDecline::UnsupportedParameters(format!(
                        "`{name}` has type {other:?}"
                    )));
                }
            }
        }
        let Some(array_parameter) = array_parameter else {
            return Err(FoldReadDecline::UnsupportedParameters(
                "no supported array parameter".into(),
            ));
        };
        let SpecIntegerExpression::RangeFold {
            index: SpecIntegerRangeFoldIndex::Int32 { start, end },
            initial,
            accumulator,
            item,
            body,
        } = &definition.body
        else {
            return Err(FoldReadDecline::NotATopLevelInt32Fold);
        };
        if accumulator == item {
            return Err(FoldReadDecline::UnsupportedConstruct(
                "the fold binders share one identity".into(),
            ));
        }
        let checker = BodyChecker {
            parameters,
            array_name: &parameters[array_parameter].0,
            accumulator: *accumulator,
            item: *item,
            element_type: if parameters[array_parameter].1 == ProgramType::UInt8Pointer {
                ProgramType::UInt8
            } else {
                ProgramType::Int32
            },
        };
        let start = checker.endpoint(start)?;
        let end = checker.endpoint(end)?;
        checker
            .integer(initial, Scope::Outside)
            .map_err(|decline| match decline {
                FoldReadDecline::UnsupportedConstruct(detail) => {
                    FoldReadDecline::UnsupportedInitialValue(detail)
                }
                FoldReadDecline::ReadOutsideFoldIndex => {
                    FoldReadDecline::UnsupportedInitialValue("it reads the array".into())
                }
                other => other,
            })?;
        checker.integer(body, Scope::Body)?;
        Ok(Self {
            name: definition.name.clone(),
            fingerprint: definition.fingerprint(),
            parameter_types: parameters
                .iter()
                .map(|(_, program_type)| *program_type)
                .collect(),
            array_parameter,
            element_width: checker.element_type.byte_width(),
            start,
            end,
            accumulator: *accumulator,
            item: *item,
        })
    }

    /// The support of one application of this function, or `None` when the
    /// application is not one this summary describes: another name, another
    /// arity, an argument of the wrong sort, or an array argument that is not
    /// an array reference with the declared element type.
    ///
    /// The endpoints are the application's own already-evaluated scalar
    /// arguments (or the literal the body writes); a historical endpoint keeps
    /// the load identity it was built with and is never reloaded.
    #[cfg(test)]
    pub(crate) fn instantiate(
        &self,
        application: &SharedPureApplication,
    ) -> Option<FoldReadInterval> {
        crate::instrumentation::record_deterministic_work(1);
        let arguments = application.arguments();
        if application.name() != self.name || arguments.len() != self.parameter_types.len() {
            return None;
        }
        for (position, (argument, program_type)) in
            arguments.iter().zip(&self.parameter_types).enumerate()
        {
            crate::instrumentation::record_deterministic_work(1);
            let fits = match argument {
                PureFunctionArgument::ArrayRef {
                    pointer,
                    element_type,
                    ..
                } => {
                    position == self.array_parameter
                        && element_type.byte_width() == self.element_width
                        && self.parameter_types[position].pointee_type() == Some(*element_type)
                        && matches!(pointer, ProgramValue::Pointer(_))
                }
                PureFunctionArgument::SharedMachine(value) => {
                    position != self.array_parameter
                        && *program_type == ProgramType::Int32
                        && value.ty() == MachineIntegerType::Int32
                }
                PureFunctionArgument::Value(ProgramValue::Int32(_)) => {
                    position != self.array_parameter && *program_type == ProgramType::Int32
                }
                _ => false,
            };
            if !fits {
                return None;
            }
        }
        let PureFunctionArgument::ArrayRef {
            point,
            pointer: ProgramValue::Pointer(pointer),
            ..
        } = &arguments[self.array_parameter]
        else {
            return None;
        };
        let endpoint = |template: FoldEndpointTemplate| match template {
            FoldEndpointTemplate::Literal(value) => Some(SharedMachineIntegerTerm::index(
                MachineIntegerType::Int32,
                OldMachineTerm::constant(value),
            )),
            FoldEndpointTemplate::Parameter(position) => match &arguments[position] {
                PureFunctionArgument::SharedMachine(value)
                    if value.ty() == MachineIntegerType::Int32 =>
                {
                    Some(value.clone())
                }
                PureFunctionArgument::Value(ProgramValue::Int32(value)) => Some(
                    SharedMachineIntegerTerm::index(MachineIntegerType::Int32, value.clone()),
                ),
                _ => None,
            },
        };
        Some(FoldReadInterval {
            memory: point.memory().clone(),
            base: pointer.address().clone(),
            start: endpoint(self.start)?,
            end: endpoint(self.end)?,
            element_width: self.element_width,
        })
    }
}

impl BodyChecker<'_> {
    fn scalar_parameter(&self, name: &str) -> Option<usize> {
        self.parameters
            .iter()
            .position(|(parameter, program_type)| {
                parameter == name && *program_type == ProgramType::Int32
            })
    }

    fn endpoint(&self, endpoint: &SpecExpression) -> Result<FoldEndpointTemplate, FoldReadDecline> {
        crate::instrumentation::record_deterministic_work(1);
        match endpoint {
            SpecExpression::ProgramExpression(ProgramExpression::Variable(name)) => name
                .named()
                .and_then(|name| self.scalar_parameter(name))
                .map(FoldEndpointTemplate::Parameter)
                .ok_or(FoldReadDecline::UnsupportedEndpoint),
            SpecExpression::Value(ProgramValue::Int32(bits32_constant!(value))) => {
                Ok(FoldEndpointTemplate::Literal(constant_u32(*value)))
            }
            _ => Err(FoldReadDecline::UnsupportedEndpoint),
        }
    }

    fn unsupported(what: &str) -> FoldReadDecline {
        FoldReadDecline::UnsupportedConstruct(what.to_string())
    }

    /// A mathematical Integer term: literals, the accumulator inside the body,
    /// and total arithmetic over those. A machine-backed term is refused
    /// because its bitvector could hold a read this walk does not see.
    fn integer_term(&self, term: &IntegerTerm, scope: Scope) -> Result<(), FoldReadDecline> {
        let mut pending = vec![term];
        while let Some(term) = pending.pop() {
            crate::instrumentation::record_deterministic_work(1);
            match term {
                IntegerTerm::Constant(_) => {}
                IntegerTerm::Variable(variable)
                    if scope == Scope::Body && *variable == self.accumulator => {}
                IntegerTerm::Variable(_) => {
                    return Err(Self::unsupported("a free Integer variable"));
                }
                IntegerTerm::Negate(inner) => pending.push(inner.as_ref()),
                IntegerTerm::Add(left, right)
                | IntegerTerm::Subtract(left, right)
                | IntegerTerm::Multiply(left, right) => {
                    pending.push(left.as_ref());
                    pending.push(right.as_ref());
                }
                IntegerTerm::TruncatingQuotient(_, _) | IntegerTerm::TruncatingRemainder(_, _) => {
                    return Err(Self::unsupported(
                        "a truncating division without native guards",
                    ));
                }
                IntegerTerm::Machine(_) => {
                    return Err(Self::unsupported("an unevaluated machine value"));
                }
                IntegerTerm::PureFunctionApplication(_) => {
                    return Err(Self::unsupported("a function call"));
                }
                IntegerTerm::AlgebraicMatch { .. } => {
                    return Err(Self::unsupported("an algebraic match"));
                }
                // An evaluated conditional's condition holds machine terms,
                // which this walk refuses as it refuses an evaluated machine
                // conditional.
                IntegerTerm::If { .. } => {
                    return Err(Self::unsupported("an evaluated conditional"));
                }
                IntegerTerm::RangeFold { .. } => return Err(Self::unsupported("a nested fold")),
            }
        }
        Ok(())
    }

    fn integer(
        &self,
        expression: &SpecIntegerExpression,
        scope: Scope,
    ) -> Result<(), FoldReadDecline> {
        crate::instrumentation::record_deterministic_work(1);
        match expression {
            SpecIntegerExpression::Term(term) => self.integer_term(term, scope),
            SpecIntegerExpression::FromMachine(machine) => self.machine(machine, scope),
            SpecIntegerExpression::Negate(inner) => self.integer(inner, scope),
            SpecIntegerExpression::Add(left, right)
            | SpecIntegerExpression::Subtract(left, right)
            | SpecIntegerExpression::Multiply(left, right) => {
                self.integer(left, scope)?;
                self.integer(right, scope)
            }
            SpecIntegerExpression::TruncatingQuotient(_, _)
            | SpecIntegerExpression::TruncatingRemainder(_, _) => {
                Err(Self::unsupported("a deferred truncating division"))
            }
            SpecIntegerExpression::RangeFold { .. } => Err(Self::unsupported("a nested fold")),
            SpecIntegerExpression::PureFunctionApplication { .. } => {
                Err(Self::unsupported("a function call"))
            }
            SpecIntegerExpression::ResourceField(_) => Err(Self::unsupported("a resource field")),
            SpecIntegerExpression::AlgebraicMatch { .. } => {
                Err(Self::unsupported("an algebraic match"))
            }
            SpecIntegerExpression::If {
                condition,
                then_branch,
                else_branch,
            } => {
                self.proposition(condition, scope)?;
                self.integer(then_branch, scope)?;
                self.integer(else_branch, scope)
            }
        }
    }

    fn bitvector(&self, term: &OldMachineTerm, scope: Scope) -> Result<(), FoldReadDecline> {
        match term {
            bits32_constant!(_) => Ok(()),
            OldMachineTerm::Variable(variable)
                if scope == Scope::Body && *variable == self.item =>
            {
                Ok(())
            }
            _ => Err(Self::unsupported("an evaluated machine term")),
        }
    }

    /// Whether `pointer` is exactly the array parameter at the fold's item:
    /// `v + element_width * k`, matched by the item's identity rather than
    /// its spelling.
    fn is_exact_array_cell(&self, pointer: &SpecExpression) -> bool {
        let SpecExpression::PointerOffset {
            pointer,
            elements,
            byte_width,
        } = pointer
        else {
            return false;
        };
        *byte_width == self.element_type.byte_width()
            && matches!(
                pointer.as_ref(),
                SpecExpression::ProgramExpression(ProgramExpression::Variable(name)) if name.is_named(self.array_name)
            )
            && matches!(
                elements.as_ref(),
                SpecExpression::Value(ProgramValue::Int32(OldMachineTerm::Variable(variable)))
                    if *variable == self.item
            )
    }

    fn machine(&self, expression: &SpecExpression, scope: Scope) -> Result<(), FoldReadDecline> {
        crate::instrumentation::record_deterministic_work(1);
        match expression {
            SpecExpression::Value(ProgramValue::Int32(term) | ProgramValue::Bool(term)) => {
                self.bitvector(term, scope)
            }
            SpecExpression::Value(_) => Err(Self::unsupported("a non-int32 value")),
            SpecExpression::ProgramExpression(ProgramExpression::Variable(name)) => {
                if name
                    .named()
                    .and_then(|name| self.scalar_parameter(name))
                    .is_some()
                {
                    Ok(())
                } else if name.is_named(self.array_name) {
                    Err(Self::unsupported("the array pointer used as a value"))
                } else {
                    Err(Self::unsupported("a name that is not an int32 parameter"))
                }
            }
            SpecExpression::ProgramExpression(_) => {
                Err(Self::unsupported("an unlowered C expression"))
            }
            SpecExpression::MemoryLoad {
                point: memory,
                pointer,
                value_type,
                exact,
            } => {
                if *exact {
                    return Err(Self::unsupported("an exact read"));
                }
                if scope != Scope::Body {
                    return Err(FoldReadDecline::ReadOutsideFoldIndex);
                }
                if *memory != SpecPoint::Current {
                    return Err(Self::unsupported("a read at another program point"));
                }
                if *value_type != self.element_type || !self.is_exact_array_cell(pointer) {
                    return Err(FoldReadDecline::ReadOutsideFoldIndex);
                }
                Ok(())
            }
            SpecExpression::Cast(inner, ProgramType::Int32)
                if self.element_type == ProgramType::UInt8 =>
            {
                self.machine(inner, scope)
            }
            SpecExpression::Add(left, right)
            | SpecExpression::Subtract(left, right)
            | SpecExpression::Multiply(left, right) => {
                self.machine(left, scope)?;
                self.machine(right, scope)
            }
            SpecExpression::If {
                condition,
                then_branch,
                else_branch,
            } => {
                self.proposition(condition, scope)?;
                self.machine(then_branch, scope)?;
                self.machine(else_branch, scope)
            }
            SpecExpression::PointerOffset { .. } => {
                Err(Self::unsupported("a pointer value outside a read"))
            }
            SpecExpression::PureFunctionApplication { .. } => {
                Err(Self::unsupported("a function call"))
            }
            SpecExpression::RangeFold { .. } => Err(Self::unsupported("a nested fold")),
            _ => Err(Self::unsupported(
                "a machine expression outside the whitelist",
            )),
        }
    }

    fn proposition(
        &self,
        proposition: &SpecProposition,
        scope: Scope,
    ) -> Result<(), FoldReadDecline> {
        crate::instrumentation::record_deterministic_work(1);
        match proposition {
            SpecProposition::Comparison { left, right, .. } => {
                self.machine(left, scope)?;
                self.machine(right, scope)
            }
            SpecProposition::IntegerComparison { left, right, .. } => {
                self.integer(left, scope)?;
                self.integer(right, scope)
            }
            SpecProposition::And(left, right)
            | SpecProposition::Or(left, right)
            | SpecProposition::Implies(left, right) => {
                self.proposition(left, scope)?;
                self.proposition(right, scope)
            }
            SpecProposition::Not(inner) => self.proposition(inner, scope),
            _ => Err(Self::unsupported("a proposition outside the whitelist")),
        }
    }
}

#[cfg(test)]
mod framing;
#[cfg(test)]
pub(crate) use framing::{
    clear_fold_read_summaries, register_fold_read_definition, registered_fold_read_summary,
};
