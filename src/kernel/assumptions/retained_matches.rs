//! Current-memory dependencies of selected common match operands. Declarations
//! keep their native typed-value widths; arm bodies keep the caller's width.
use super::*;
use crate::kernel::{KernelMatch, KernelType};

pub(super) fn collect_match_memory_loads(
    matched: &KernelMatch,
    current_memory: &CMemory,
    loads: &mut Vec<(Pointer, u32)>,
    width: Option<u32>,
    seen_integers: &mut BTreeSet<u64>,
) -> Result<(), String> {
    let mut pending = Vec::new();
    pending.push((&matched.arguments[0], None));
    for (arm, body) in matched.arms.iter().zip(&matched.arguments[1..]) {
        for binding in &arm.bindings {
            let width = match binding.ty() {
                KernelType::C(ty) => Some(ty.byte_width()),
                _ => None,
            };
            pending.push((binding, width));
        }
        pending.push((body, width));
    }
    pending.reverse();
    super::retained_folds::collect_common_memory_loads(
        pending,
        current_memory,
        loads,
        seen_integers,
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::KernelTermImport;

    #[test]
    fn common_match_dependencies_preserve_widths_and_opaque_refusals() {
        for format in [MachineIntegerType::Int32, MachineIntegerType::UInt64] {
            for opaque in [false, true] {
                let _session = crate::kernel::VerificationSession::enter();
                let current = CMemory::new();
                let memory = intern_c_memory_ref(&current);
                let read = MachineTerm::MemoryLoad(
                    memory,
                    Box::new(Pointer::symbolic(Variable(991901))),
                    LoadKind::Bits64,
                );
                let body = if opaque {
                    MachineTerm::ClickFunctionApplication {
                        name: "opaque".into(),
                        arguments: vec![],
                    }
                } else {
                    read
                };
                let native = MachineTerm::AlgebraicMatch {
                    scrutinee: Box::new(KernelMatch::test_scrutinee(vec![
                        AlgebraicValueType::Integer,
                    ])),
                    arms: vec![AlgebraicBitvectorMatchArm {
                        variant: "Arm".into(),
                        binding_names: Default::default(),
                        bindings: vec![AlgebraicValue::Integer(IntegerTerm::Variable(Variable(2)))],
                        body,
                    }],
                };
                let common =
                    KernelMatch::import_machine(&mut KernelTermImport::default(), format, &native)
                        .unwrap();
                for width in [None, Some(4), Some(8)] {
                    let mut expected = Vec::new();
                    let old = collect_bitvector_memory_loads_with_width(
                        &native,
                        &current,
                        &mut expected,
                        width,
                        &mut BTreeSet::new(),
                    );
                    let mut actual = Vec::new();
                    let new = collect_match_memory_loads(
                        &common,
                        &current,
                        &mut actual,
                        width,
                        &mut BTreeSet::new(),
                    );
                    assert_eq!(new, old, "format={format:?}, width={width:?}");
                    assert_eq!(actual, expected, "format={format:?}, width={width:?}");
                }
            }
        }
    }
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/assumptions/retained_matches.rs");
}
