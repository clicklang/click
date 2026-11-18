//! Pointer indices are raised in their existing address context. Keep their
//! numeric children shared; no independent offset syntax or fact-based narrowing.
use super::*;
use crate::kernel::{KernelTermNode as N, MachineOperandView as V, SharedMachineIntegerTerm};
use std::collections::HashSet;

/// A source index may already be native. Do not import a newly computed
/// native displacement merely to hand it straight to the native raiser.
pub(super) enum SourceIndex {
    Native(MachineTerm),
    Shared(SharedMachineIntegerTerm),
}
impl SourceIndex {
    pub(super) fn operand_view(&self) -> V<'_> {
        match self {
            Self::Native(term) => V::Legacy(term),
            Self::Shared(term) => term.operand_view(),
        }
    }
    #[cfg(test)]
    pub(super) fn shared_operand(&self) -> Option<&crate::kernel::KernelTerm> {
        match self {
            Self::Native(_) => None,
            Self::Shared(term) => term.shared_operand(),
        }
    }
}

/// Structural inverse of the existing uint32 index widening. A signed-wide
/// index and every other cast retain their exact original carrier.
pub(super) fn source_index(
    value: &SharedMachineIntegerTerm,
    unsigned: bool,
) -> SharedMachineIntegerTerm {
    fn widened(view: V<'_>) -> Option<SharedMachineIntegerTerm> {
        match view {
            V::Shared(root) => match root.node() {
                N::MachineCast {
                    encoding: MachineCastSpelling::UInt64From32,
                    source: MachineIntegerType::UInt32,
                    operand,
                    ..
                } => Some(V::Shared(operand).retain(MachineIntegerType::UInt32)),
                N::Legacy(_) => widened(V::Legacy(root.machine_conversion_leaf()?)),
                _ => None,
            },
            V::Legacy(cast_term!(UInt64From32, index)) => {
                Some(V::Legacy(index).retain(MachineIntegerType::UInt32))
            }
            _ => None,
        }
    }
    if unsigned {
        widened(value.operand_view()).unwrap_or_else(|| value.clone())
    } else {
        value.clone()
    }
}

/// Inspect a literal without asking opaque common calls for a native adapter.
pub(super) fn literal(view: V<'_>) -> Option<MachineTerm> {
    match view {
        V::Shared(root) if !matches!(root.node(), N::MachineLiteral(_) | N::Legacy(_)) => None,
        view => view.literal(),
    }
}

pub(super) fn raise(
    value: V<'_>,
    parameters: ParameterBinding<'_>,
    state: &ExecutionState,
    names: &BTreeMap<Variable, SurfaceBinder>,
) -> Option<SurfaceTerm> {
    match value {
        V::Shared(root) => raise_kernel_term(root, parameters, state, names),
        V::Legacy(value) => synthesize_surface_bitvector(value, parameters, state, names),
    }
}

/// Preserve the native local-index reader's policy, including opaque-call
/// refusals and the fact that it does not inspect conditional guards or load
/// registries. The shared memo belongs to this selected input only.
pub(super) fn load_free(root: V<'_>) -> bool {
    let mut pending = vec![root];
    let mut seen = HashSet::new();
    while let Some(view) = pending.pop() {
        if let V::Shared(root) = view {
            crate::instrumentation::record_deterministic_work(1);
            if !seen.insert(root.id()) {
                continue;
            }
        }
        if !consume_surface_synthesis_work("local-index") {
            return false;
        }
        match view {
            V::Shared(root) => match root.node() {
                N::MachineLiteral(_) | N::Variable(_) => {}
                N::MachineBinary { arguments, .. } => {
                    pending.extend(arguments.iter().map(V::Shared))
                }
                N::MachineUnary { operand, .. } | N::MachineCast { operand, .. } => {
                    pending.push(V::Shared(operand))
                }
                N::MachineIf { arguments } => pending.extend(arguments[1..].iter().map(V::Shared)),
                N::Fold(fold) => pending.extend(fold.arguments.iter().map(V::Shared)),
                N::Legacy(_) | N::IntegerAddress { .. } => match root.machine_conversion_leaf() {
                    Some(value) => pending.push(V::Legacy(value)),
                    None => return false,
                },
                _ => return false,
            },
            V::Legacy(term) => match term {
                MachineTerm::ThreadHandle(_) => {}
                MachineTerm::MemoryLoad(..) => return false,
                MachineTerm::IntegerAddress(pointer, _) => pending.extend(
                    pointer
                        .offset
                        .scaled_operands()
                        .into_iter()
                        .map(|v| v.operand_view()),
                ),
                MachineTerm::Constant { .. } | MachineTerm::Variable(_) => {}
                crate::kernel::binary_bitvector32_term!(left, right)
                | crate::kernel::binary_wide_term!(left, right) => {
                    pending.push(V::Legacy(left));
                    pending.push(V::Legacy(right));
                }
                MachineTerm::Float32Binary { left, right, .. }
                | MachineTerm::Float64Binary { left, right, .. } => {
                    pending.push(V::Legacy(left));
                    pending.push(V::Legacy(right));
                }
                crate::kernel::unary_machine_term!(value) => pending.push(V::Legacy(value)),
                MachineTerm::If {
                    then_term,
                    else_term,
                    ..
                } => {
                    pending.push(V::Legacy(then_term));
                    pending.push(V::Legacy(else_term));
                }
                MachineTerm::RangeFold {
                    start,
                    end,
                    initial,
                    body,
                    ..
                } => pending.extend([start, end, initial, body].map(|value| V::Legacy(value))),
                MachineTerm::PureFunctionApplication { arguments, .. } => {
                    pending.extend(arguments.iter().map(V::Legacy))
                }
                MachineTerm::ClickFunctionApplication { .. }
                | MachineTerm::AlgebraicMatch { .. }
                | MachineTerm::IntegerToMachine { .. }
                | MachineTerm::BoolCast { .. } => return false,
            },
        }
    }
    true
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::{KernelTerm, KernelTermExport, KernelType, VerificationSession};
    #[test]
    fn load_free_reader_keeps_existing_opaque_and_guard_policy() {
        let _session = VerificationSession::enter();
        let _scope = SurfaceSynthesisScope::enter();
        let load = MachineTerm::MemoryLoad(
            crate::kernel::ProgramPoint::at(&(crate::kernel::intern_memory(SymbolicMemory::new()))),
            Box::new(Address::symbolic(Variable(1014000))),
            crate::kernel::LoadKind::Int32,
        );
        let variable = MachineTerm::Variable(Variable(1014001));
        let cases = vec![
            (variable.clone(), true),
            (load.clone(), false),
            (
                MachineTerm::If {
                    condition: Box::new(ConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::Equal,
                        left: Box::new(load.clone()),
                        right: Box::new(MachineTerm::constant(0)),
                    }),
                    then_term: Box::new(variable.clone()),
                    else_term: Box::new(MachineTerm::constant(1)),
                },
                true,
            ),
            (
                MachineTerm::If {
                    condition: Box::new(ConditionTerm::Variable(Variable(1014002))),
                    then_term: Box::new(variable.clone()),
                    else_term: Box::new(load.clone()),
                },
                false,
            ),
            (
                MachineTerm::RangeFold {
                    start: Box::new(MachineTerm::constant(0)),
                    end: Box::new(MachineTerm::constant(2)),
                    initial: Box::new(variable.clone()),
                    accumulator: Variable(1014003),
                    item: Variable(1014004),
                    body: Box::new(load),
                },
                false,
            ),
            (
                MachineTerm::PureFunctionApplication {
                    name: "opaque-machine".into(),
                    arguments: vec![variable.clone()],
                },
                true,
            ),
            (
                MachineTerm::ClickFunctionApplication {
                    name: "opaque-click".into(),
                    arguments: vec![],
                },
                false,
            ),
        ];
        for (native, expected) in cases {
            let shared =
                KernelTerm::retained_machine_operand(MachineIntegerType::Int32, V::Legacy(&native));
            let exports = KernelTermExport::machine_export_count();
            assert_eq!(load_free(V::Legacy(&native)), expected, "{native:?}");
            assert_eq!(load_free(V::Shared(&shared)), expected, "{native:?}");
            assert_eq!(KernelTermExport::machine_export_count(), exports);
        }
    }
    #[test]
    fn wide_source_index_only_removes_the_existing_unsigned32_widening() {
        let _session = VerificationSession::enter();
        let variable =
            KernelTerm::variable(KernelType::Program(ProgramType::UInt32), Variable(1014010));
        for spelling in [
            MachineCastSpelling::UInt64From32,
            MachineCastSpelling::Generic,
        ] {
            let root = KernelTerm::machine_cast_shared(
                spelling,
                MachineIntegerType::UInt32,
                MachineIntegerType::UInt64,
                variable.clone(),
            );
            let value =
                SharedMachineIntegerTerm::from_shared(MachineIntegerType::UInt64, root).unwrap();
            for unsigned in [false, true] {
                let exports = KernelTermExport::machine_export_count();
                let index = source_index(&value, unsigned);
                if unsigned && spelling == MachineCastSpelling::UInt64From32 {
                    assert_eq!(index.shared_operand(), Some(&variable));
                    assert_eq!(index.ty(), MachineIntegerType::UInt32);
                } else {
                    assert_eq!(index, value);
                }
                assert_eq!(KernelTermExport::machine_export_count(), exports);
            }
        }
    }
}
#[cfg(test)]
mod scaling_tests {
    include!("../../../scaling_tests/surface/proof/surface_synthesis/pointer_indices.rs");
}
