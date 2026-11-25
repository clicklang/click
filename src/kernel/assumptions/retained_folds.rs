//! Read dependencies of the explicitly selected common fold children.
//! SymbolicMemory state checks, opaque-call refusals and address handling stay in the
//! existing leaf readers; no registry or memory history is searched here.
use super::*;
use crate::kernel::{KernelFold, KernelTermNode, KernelType};

pub(super) fn collect_fold_memory_loads(
    fold: &KernelFold,
    current_memory: &SymbolicMemory,
    loads: &mut Vec<(Address, u32)>,
    width: Option<u32>,
    seen_integers: &mut BTreeSet<u64>,
) -> Result<(), String> {
    let endpoint_width = match fold.index.ty() {
        KernelType::Program(ty) => Some(ty.byte_width()),
        _ => width,
    };
    let result_width = match fold.result_type() {
        KernelType::Program(ty) => Some(ty.byte_width()),
        _ => width,
    };
    let pending = vec![
        (&fold.arguments[3], result_width),
        (&fold.arguments[2], result_width),
        (&fold.arguments[1], endpoint_width),
        (&fold.arguments[0], endpoint_width),
    ];
    collect_common_memory_loads(pending, current_memory, loads, seen_integers)
}

pub(super) fn collect_common_memory_loads(
    mut pending: Vec<(&KernelTerm, Option<u32>)>,
    current_memory: &SymbolicMemory,
    loads: &mut Vec<(Address, u32)>,
    seen_integers: &mut BTreeSet<u64>,
) -> Result<(), String> {
    let mut seen = BTreeSet::new();
    while let Some((term, width)) = pending.pop() {
        if crate::instrumentation::deadline_exceeded_with_work(1) {
            return Err("memory-load collection exceeded its checking budget".into());
        }
        if !seen.insert((term.id(), width)) {
            continue;
        }
        // Keep nested machine folds in this query's worklist. Delegating each
        // arithmetic parent separately would revisit a fold shared by the
        // initial value and body, recursively doubling the same dependency work.
        if !term.has_machine_folds()
            && !term.has_machine_matches()
            && !matches!(
                term.node(),
                KernelTermNode::Fold(_) | KernelTermNode::Match(_)
            )
            && let KernelType::Program(ty) = term.ty()
            && let Some(format) = MachineIntegerType::from_program_type(*ty)
            && let Some(value) = SharedMachineIntegerTerm::from_shared(format, term.clone())
        {
            collect_shared_machine_memory_loads(
                &value,
                current_memory,
                loads,
                width,
                seen_integers,
            )?;
            continue;
        }
        match term.node() {
            KernelTermNode::Match(matched) => {
                for (arm, body) in matched.arms.iter().zip(&matched.arguments[1..]).rev() {
                    pending.push((body, width));
                    for binding in arm.bindings.iter().rev() {
                        let width = match binding.ty() {
                            KernelType::Program(ty) => Some(ty.byte_width()),
                            _ => None,
                        };
                        pending.push((binding, width));
                    }
                }
                pending.push((&matched.arguments[0], None));
            }
            KernelTermNode::Fold(fold) => {
                let endpoint_width = match fold.index.ty() {
                    KernelType::Program(ty) => Some(ty.byte_width()),
                    _ => width,
                };
                let width = match fold.result_type() {
                    KernelType::Program(ty) => Some(ty.byte_width()),
                    _ => width,
                };
                pending.push((&fold.arguments[3], width));
                pending.push((&fold.arguments[2], width));
                pending.push((&fold.arguments[1], endpoint_width));
                pending.push((&fold.arguments[0], endpoint_width));
            }
            KernelTermNode::ImportedScalar(input) => collect_bitvector_memory_loads_with_width(
                input.value(),
                current_memory,
                loads,
                Some(input.carrier().byte_width()),
                seen_integers,
            )?,
            KernelTermNode::NativeDescriptor(_)
            | KernelTermNode::ObservedArgument(_)
            | KernelTermNode::CallArgument(_) => match term.written_argument().unwrap() {
                PureFunctionArgument::Integer(value) => collect_integer_memory_loads_with_width(
                    value,
                    current_memory,
                    loads,
                    width,
                    seen_integers,
                )?,
                PureFunctionArgument::SharedMachine(value) => collect_shared_machine_memory_loads(
                    value,
                    current_memory,
                    loads,
                    width,
                    seen_integers,
                )?,
                PureFunctionArgument::Value(value) => {
                    collect_cvalue_memory_loads(value, current_memory, loads, seen_integers)?
                }
                PureFunctionArgument::Algebraic(value) => {
                    collect_algebraic_memory_loads(value, current_memory, loads, seen_integers)?
                }
                PureFunctionArgument::ArrayRef { .. } => {
                    return Err("opaque fold operand may hide a current memory load".into());
                }
            },
            KernelTermNode::ObservedPointer(value) => {
                let Some(pointer) = value.source().pointer_payload() else {
                    return Err("opaque fold operand may hide a current memory load".into());
                };
                push_offset_memory_loads(
                    std::iter::once(&pointer.node().address.node().offset),
                    &mut pending,
                )?;
            }
            KernelTermNode::MachineObservation { format, operand } => {
                pending.push((operand, Some(format.format().byte_width())));
            }
            KernelTermNode::BoolCompare {
                format, arguments, ..
            }
            | KernelTermNode::BoolOverflow {
                format, arguments, ..
            } => {
                pending.extend(
                    arguments
                        .iter()
                        .rev()
                        .map(|child| (child, Some(format.carrier_bytes()))),
                );
            }
            KernelTermNode::AddressOffsetEqual { arguments } => {
                push_offset_memory_loads(arguments.iter(), &mut pending)?;
            }
            KernelTermNode::PointerEqual(pair) => {
                push_offset_memory_loads(
                    pair.arguments()
                        .iter()
                        .flat_map(|value| value.addresses())
                        .map(|address| &address.node().offset),
                    &mut pending,
                )?;
            }
            KernelTermNode::AddressEqual { arguments } => {
                push_offset_memory_loads(
                    arguments.iter().map(|address| &address.node().offset),
                    &mut pending,
                )?;
            }
            KernelTermNode::IntegerCompare { arguments, .. }
            | KernelTermNode::BoolEqual { arguments } => {
                pending.extend(arguments.iter().rev().map(|child| (child, None)));
            }
            KernelTermNode::BoolIf { arguments } => {
                pending.extend(arguments.iter().rev().map(|child| (child, None)));
            }
            KernelTermNode::IntegerIf { arguments } | KernelTermNode::MachineIf { arguments } => {
                pending.push((&arguments[2], width));
                pending.push((&arguments[1], width));
                pending.push((&arguments[0], None));
            }
            KernelTermNode::BoolCast { operand, .. } => pending.push((operand, None)),
            KernelTermNode::IntegerToMachine {
                destination,
                operand,
            } => {
                pending.push((operand, Some(destination.format().byte_width())));
            }
            KernelTermNode::MachineBinary {
                format, arguments, ..
            } => {
                let width = if matches!(
                    format,
                    MachineIntegerType::Int32 | MachineIntegerType::UInt32
                ) {
                    width
                } else {
                    Some(8)
                };
                pending.extend(arguments.iter().rev().map(|child| (child, width)));
            }
            KernelTermNode::MachineCast {
                encoding: MachineCastSpelling::Generic,
                source,
                operand,
                ..
            } => {
                pending.push((operand, Some(source.format().byte_width())));
            }
            KernelTermNode::FloatConvert { .. } => {
                return Err("opaque pure function may hide a current memory load".into());
            }
            KernelTermNode::Call { .. } => {
                return Err(if term.ty() == &KernelType::Integer {
                    "opaque integer function may hide a current memory load"
                } else {
                    "opaque Click function may hide a current memory load"
                }
                .into());
            }
            _ => pending.extend(term.children().iter().rev().map(|child| (child, width))),
        }
    }
    Ok(())
}

pub(super) fn collect_offset_memory_loads(
    offset: &crate::kernel::SharedAddressOffset,
    current_memory: &SymbolicMemory,
    loads: &mut Vec<(Address, u32)>,
    seen_integers: &mut BTreeSet<u64>,
) -> Result<(), String> {
    let mut pending = Vec::new();
    push_offset_memory_loads(std::iter::once(offset), &mut pending)?;
    for (index, width) in pending.into_iter().rev() {
        collect_shared_machine_root_memory_loads(
            index,
            current_memory,
            loads,
            width,
            seen_integers,
        )?;
    }
    Ok(())
}

fn push_offset_memory_loads<'a>(
    roots: impl IntoIterator<Item = &'a crate::kernel::SharedAddressOffset>,
    pending: &mut Vec<(&'a KernelTerm, Option<u32>)>,
) -> Result<(), String> {
    let mut offsets: Vec<_> = roots.into_iter().collect();
    offsets.reverse();
    let mut seen_offsets = std::collections::HashSet::new();
    let mut indices = Vec::new();
    while let Some(offset) = offsets.pop() {
        if !seen_offsets.insert(offset) {
            continue;
        }
        if crate::instrumentation::deadline_exceeded_with_work(1) {
            return Err("memory-load collection exceeded its checking budget".into());
        }
        match offset.node() {
            crate::kernel::KernelAddressOffset::Add(children) => {
                offsets.extend(children.iter().rev())
            }
            crate::kernel::KernelAddressOffset::Int32Scaled { value, .. } => {
                indices.push((value, Some(4)))
            }
            crate::kernel::KernelAddressOffset::Int64Scaled { value, .. } => {
                indices.push((value, Some(8)))
            }
            _ => {}
        }
    }
    pending.extend(indices.into_iter().rev());
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::KernelTermImport;

    #[test]
    fn contract_offset_loads_use_retained_widths_and_states() {
        let _session = crate::kernel::VerificationSession::enter();
        let memory = SymbolicMemory::new();
        let point = ProgramPoint::at(&crate::kernel::intern_memory_ref(&memory));
        let word = Address::symbolic(Variable(999967));
        let wide = Address::symbolic(Variable(999968));
        let offset = OldAddressOffset::Add(
            Box::new(OldAddressOffset::scaled_int32_node(
                OldMachineTerm::read_named(point.clone(), Box::new(word.clone()), LoadKind::Int32),
                4,
            )),
            Box::new(OldAddressOffset::scaled_int64_node(
                OldMachineTerm::read_named(point, Box::new(wide.clone()), LoadKind::Bits64),
                8,
                true,
            )),
        );
        let stored = crate::kernel::StoredPointerOffset::from(offset.clone());
        assert!(stored.root().is_some());
        let mut native = Vec::new();
        collect_pointer_offset_memory_loads(&offset, &memory, &mut native, &mut BTreeSet::new())
            .unwrap();
        let term = Term::PointerOffset(stored);
        let actual = current_memory_loads_in_term(&term, &memory).unwrap();
        assert_eq!(actual, native);
        assert_eq!(actual, [(word, 4), (wide, 8)]);
        let later = memory.with_block("later offset memory", 4);
        assert!(
            current_memory_loads_in_term(&term, &later)
                .unwrap()
                .is_empty()
        );
    }

    #[test]
    fn common_float_conversions_preserve_native_memory_collection_refusal() {
        let _session = crate::kernel::VerificationSession::enter();
        for (source, target, name) in [
            (
                ProgramType::Float32,
                ProgramType::Int32,
                "c_float32_to_int32",
            ),
            (
                ProgramType::Float64,
                ProgramType::UInt64,
                "c_float64_to_uint64",
            ),
            (
                ProgramType::Int32,
                ProgramType::Float32,
                "c_int32_to_float32",
            ),
        ] {
            let native = OldMachineTerm::PureFunctionApplication {
                name: name.into(),
                arguments: vec![OldMachineTerm::Variable(Variable(999973))],
            };
            let operand = KernelTerm::variable(KernelType::Program(source), Variable(999973));
            let root = KernelTerm::numeric_float_convert(target, source, operand).unwrap();
            let current = SymbolicMemory::new();
            let expected = collect_bitvector_memory_loads_with_width(
                &native,
                &current,
                &mut Vec::new(),
                None,
                &mut BTreeSet::new(),
            );
            let actual = collect_common_memory_loads(
                vec![(&root, None)],
                &current,
                &mut Vec::new(),
                &mut BTreeSet::new(),
            );
            assert!(expected.is_err());
            assert_eq!(actual, expected);
        }
    }

    #[test]
    fn retained_fold_guard_reads_keep_their_comparison_width() {
        for format in [
            MachineIntegerType::Int8,
            MachineIntegerType::Int16,
            MachineIntegerType::Int32,
            MachineIntegerType::UInt64,
        ] {
            let _session = crate::kernel::VerificationSession::enter();
            let current = SymbolicMemory::new();
            let pointer = Address::symbolic(Variable(991510));
            let source = IntegerTerm::RangeFold {
                index: IntegerRangeFoldIndex::Integer {
                    start: IntegerTerm::constant_i64(0).into(),
                    end: IntegerTerm::Variable(Variable(991511)).into(),
                },
                initial: IntegerTerm::constant_i64(0).into(),
                accumulator: Variable(991512),
                item: Variable(991513),
                body: IntegerTerm::If {
                    condition: Box::new(OldConditionTerm::Compare {
                        format,
                        relation: CompareRelation::LessThan,
                        left: Box::new(OldMachineTerm::read_named(
                            ProgramPoint::at(&(crate::kernel::intern_memory_ref(&current))),
                            Box::new(pointer.clone()),
                            LoadKind::Int32,
                        )),
                        right: Box::new(OldMachineTerm::constant(0)),
                    }),
                    then_term: IntegerTerm::constant_i64(1).into(),
                    else_term: IntegerTerm::constant_i64(2).into(),
                }
                .into(),
            };
            let common =
                KernelFold::import_integer(&mut KernelTermImport::default(), &source).unwrap();
            let mut actual = Vec::new();
            collect_fold_memory_loads(&common, &current, &mut actual, None, &mut BTreeSet::new())
                .unwrap();
            let mut expected = Vec::new();
            collect_integer_node_memory_loads(
                &source,
                &current,
                &mut expected,
                None,
                &mut BTreeSet::new(),
            )
            .unwrap();
            assert_eq!(actual, expected);
            assert_eq!(actual, vec![(pointer, format.carrier_bytes())]);
        }
    }

    #[test]
    fn retained_fold_read_collection_preserves_states_widths_and_opaque_refusals() {
        let _session = crate::kernel::VerificationSession::enter();
        let current = SymbolicMemory::new();
        let memory = crate::kernel::intern_memory_ref(&current);
        let pointer = Address::symbolic(Variable(991501));
        let read = OldMachineTerm::read_named(
            ProgramPoint::at(&memory),
            Box::new(pointer),
            LoadKind::Bits64,
        );
        let bound = SharedIntegerRangeEndpoint::intern(read.clone());
        let source = IntegerTerm::RangeFold {
            index: IntegerRangeFoldIndex::UInt64 {
                start: bound.clone(),
                end: bound,
            },
            initial: IntegerTerm::constant_i64(0).into(),
            accumulator: Variable(991502),
            item: Variable(991503),
            body: IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
                MachineIntegerType::UInt64,
                read,
            ))
            .into(),
        };
        for body_is_call in [false, true] {
            let mut source = source.clone();
            if body_is_call {
                let IntegerTerm::RangeFold { body, .. } = &mut source else {
                    unreachable!()
                };
                *body = IntegerTerm::PureFunctionApplication(SharedPureApplication::intern(
                    "opaque".into(),
                    vec![],
                ))
                .into();
            }
            let common =
                KernelFold::import_integer(&mut KernelTermImport::default(), &source).unwrap();
            let mut expected = Vec::new();
            let old = collect_integer_node_memory_loads(
                &source,
                &current,
                &mut expected,
                None,
                &mut BTreeSet::new(),
            );
            let mut actual = Vec::new();
            let new = collect_fold_memory_loads(
                &common,
                &current,
                &mut actual,
                None,
                &mut BTreeSet::new(),
            );
            assert_eq!(new, old);
            // Collection is a set of selected read dependencies; shared DAG
            // readings need not repeat an identical descriptor occurrence.
            actual.sort();
            actual.dedup();
            expected.sort();
            expected.dedup();
            assert_eq!(actual, expected);
            assert_eq!(actual.len(), 1);
        }
    }
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/assumptions/retained_folds.rs");
}

#[cfg(test)]
mod offset_condition_tests {
    use super::*;
    #[test]
    fn offset_condition_dependencies_preserve_widths() {
        let _session = crate::kernel::VerificationSession::enter();
        let current = SymbolicMemory::new();
        let read = |id, kind| {
            OldMachineTerm::read_named(
                ProgramPoint::at(&(crate::kernel::intern_memory_ref(&current))),
                Box::new(Address::symbolic(Variable(id))),
                kind,
            )
        };
        let source = OldConditionTerm::AddressOffsetEqual(
            Box::new(OldAddressOffset::scaled_int32_node(
                read(998500, LoadKind::Int32),
                4,
            )),
            Box::new(OldAddressOffset::scaled_int64_node(
                read(998501, LoadKind::Bits64),
                8,
                false,
            )),
        );
        let root = crate::kernel::KernelTermImport::default().condition(&source);
        let mut expected = Vec::new();
        let mut actual = Vec::new();
        collect_condition_memory_loads(&source, &current, &mut expected, &mut BTreeSet::new())
            .unwrap();
        collect_common_memory_loads(
            vec![(&root, None)],
            &current,
            &mut actual,
            &mut BTreeSet::new(),
        )
        .unwrap();
        assert_eq!(actual, expected);
        assert_eq!(
            actual.iter().map(|(_, width)| *width).collect::<Vec<_>>(),
            [4, 8]
        );
    }
}

#[cfg(test)]
mod boolean_read_tests {
    use super::*;
    #[test]
    fn boolean_reads_keep_own_and_index_dependency_widths() {
        let _session = crate::kernel::VerificationSession::enter();
        let current = SymbolicMemory::new().with_block("bool-index", 4);
        let memory = crate::kernel::intern_memory(current.clone());
        let address = Address {
            base: AddressBase::Symbolic(Variable(999360)),
            offset: OldAddressOffset::scaled_int32_node(
                OldMachineTerm::read_named(
                    ProgramPoint::at(&memory),
                    Box::new(SymbolicMemory::global_pointer("bool-index")),
                    LoadKind::Int32,
                ),
                4,
            ),
        };
        let byte =
            crate::kernel::eval::scalar_read_for_exact_cell(&memory, &address, LoadKind::UInt8, 1);
        let source = OldConditionTerm::nonzero_bool_word(&byte);
        let root = crate::kernel::KernelTermImport::default().condition(&source);
        let mut expected = Vec::new();
        let mut actual = Vec::new();
        collect_condition_memory_loads(&source, &current, &mut expected, &mut BTreeSet::new())
            .unwrap();
        collect_common_memory_loads(
            vec![(&root, None)],
            &current,
            &mut actual,
            &mut BTreeSet::new(),
        )
        .unwrap();
        assert_eq!(actual, expected);
        assert_eq!(
            actual.iter().map(|(_, width)| *width).collect::<Vec<_>>(),
            vec![1, 4]
        );
    }
}
