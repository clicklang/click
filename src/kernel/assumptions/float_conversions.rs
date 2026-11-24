//! Borrowed conversion operands at the existing pointer-index selectors.
//! Fingerprints select candidates only; their policies and cache are unchanged.
use super::*;
use crate::kernel::{FloatOperandView, KernelFloatType};
use std::hash::{Hash, Hasher};

pub(super) fn machine_conversion(
    value: MachineOperandView<'_>,
) -> Option<(ProgramType, ProgramType, FloatOperandView<'_>)> {
    match value {
        MachineOperandView::Shared(root) => {
            let KernelTermNode::FloatConvert {
                source,
                destination,
                operand,
            } = root.node()
            else {
                return None;
            };
            MachineIntegerType::from_program_type(*destination)?;
            Some((
                *source,
                *destination,
                FloatOperandView::from_shared(operand)?,
            ))
        }
        MachineOperandView::Legacy(MachineTerm::PureFunctionApplication { name, arguments }) => {
            let [operand] = arguments.as_slice() else {
                return None;
            };
            let (source, destination) =
                crate::kernel::primitives::float_conversion::numeric_float_conversion_types(name)?;
            MachineIntegerType::from_program_type(destination)?;
            Some((
                source,
                destination,
                FloatOperandView::Native(KernelFloatType::from_program_type(source)?, operand),
            ))
        }
        _ => None,
    }
}

pub(super) fn fingerprint(root: FloatOperandView<'_>, policy: OperandFingerprintPolicy) -> u64 {
    let key = |value: FloatOperandView<'_>, policy| match value {
        FloatOperandView::Shared(root) => (policy, true, root.id(), value.format()),
        FloatOperandView::Native(format, value) => (
            policy,
            false,
            value as *const MachineTerm as usize as u64,
            format,
        ),
    };
    let mut values = std::collections::HashMap::new();
    let mut pending = vec![(root, policy, false)];
    while let Some((value, policy, finish)) = pending.pop() {
        crate::instrumentation::record_deterministic_work(1);
        if values.contains_key(&key(value, policy)) {
            continue;
        }
        if let FloatOperandView::Shared(root) = value
            && let Some(hash) =
                OPERAND_FINGERPRINTS.with(|memo| memo.borrow().get(&(policy, root.id())).copied())
        {
            values.insert(key(value, policy), hash);
            continue;
        }
        let mut hash = std::collections::hash_map::DefaultHasher::new();
        value.format().hash(&mut hash);
        let children = if let Some(conversion) = value.conversion() {
            0u8.hash(&mut hash);
            conversion.source_type().hash(&mut hash);
            if let Some(format) = KernelFloatType::from_program_type(conversion.source_type()) {
                vec![match conversion.shared() {
                    Some(root) => FloatOperandView::Shared(root),
                    None => FloatOperandView::Native(
                        format,
                        conversion.native().expect("native conversion"),
                    ),
                }]
            } else {
                let operand = match conversion.shared() {
                    Some(root) => MachineOperandView::Shared(root),
                    None => {
                        MachineOperandView::Legacy(conversion.native().expect("native conversion"))
                    }
                };
                // The existing scalar selector owns integer syntax. Scoped scalar
                // forms retain its selected native boundary until the closure audit.
                let scalar = if let MachineOperandView::Shared(root) = operand
                    && matches!(
                        root.node(),
                        KernelTermNode::ImportedScalar(_)
                            | KernelTermNode::MachineObservationInput { .. }
                            | KernelTermNode::WrittenMachine(_)
                    ) {
                    operand_fingerprint(MachineOperandView::Legacy(legacy_numeric(root)), policy)
                } else if let MachineOperandView::Shared(root) = operand
                    && matches!(
                        root.node(),
                        KernelTermNode::MachineIf { .. }
                            | KernelTermNode::Fold(_)
                            | KernelTermNode::Match(_)
                    )
                {
                    let native = crate::kernel::KernelTermExport::machine(root)
                        .expect("scoped integer operand");
                    operand_fingerprint(MachineOperandView::Legacy(&native), policy)
                } else {
                    operand_fingerprint(operand, policy)
                };
                scalar.hash(&mut hash);
                Vec::new()
            }
        } else if let Some(operand) = value.negate() {
            1u8.hash(&mut hash);
            vec![operand]
        } else if let Some((operator, arguments)) = value.binary() {
            2u8.hash(&mut hash);
            // The existing memory-blind selector omits float operators;
            // exact state syntax keeps them. Preserve both candidate policies.
            if matches!(policy, OperandFingerprintPolicy::MemoryState(_)) {
                operator.hash(&mut hash);
            }
            arguments.to_vec()
        } else if value.is_call() {
            // Calls keep exact argument syntax even under the memory-blind
            // selector. Child fingerprints are stable across sessions; root
            // ids are only memo keys, never fingerprint values.
            4u8.hash(&mut hash);
            let mut children = Vec::new();
            match value {
                FloatOperandView::Native(
                    _,
                    MachineTerm::ClickFunctionApplication { name, arguments },
                ) => {
                    name.hash(&mut hash);
                    arguments.len().hash(&mut hash);
                    for argument in arguments {
                        if let PureFunctionArgument::Value(value) = argument
                            && let Some(view) = FloatOperandView::from_value(value)
                        {
                            1u8.hash(&mut hash);
                            children.push(view);
                        } else {
                            0u8.hash(&mut hash);
                            argument.hash(&mut hash);
                        }
                    }
                }
                FloatOperandView::Shared(root) => {
                    let KernelTermNode::FloatCall(call) = root.node() else {
                        unreachable!("float call");
                    };
                    call.name.hash(&mut hash);
                    call.arguments.len().hash(&mut hash);
                    for (argument, carrier) in
                        call.arguments.iter().zip(&call.shared_machine_arguments)
                    {
                        if let Some(view) = FloatOperandView::from_shared(argument) {
                            1u8.hash(&mut hash);
                            children.push(view);
                        } else {
                            0u8.hash(&mut hash);
                            if let Some(carrier) = carrier {
                                PureFunctionArgument::SharedMachine(carrier.clone())
                                    .hash(&mut hash);
                            } else {
                                // Selected mixed-family exact-payload adapter;
                                // typed float children above never export.
                                crate::kernel::KernelTermExport::default()
                                    .argument(argument)
                                    .expect("non-float call argument")
                                    .hash(&mut hash);
                            }
                        }
                    }
                }
                _ => unreachable!("float call"),
            }
            children
        } else {
            3u8.hash(&mut hash);
            let native = value.native_compat().expect("float atom");
            match policy {
                OperandFingerprintPolicy::MemoryBlind => {
                    hash_memory_blind_bitvector(native, &mut hash)
                }
                OperandFingerprintPolicy::MemoryState(_) => native.hash(&mut hash),
            }
            Vec::new()
        };
        let child_policy = if value.is_call() {
            OperandFingerprintPolicy::MemoryState(false)
        } else {
            policy
        };
        if !finish && !children.is_empty() {
            pending.push((value, policy, true));
            pending.extend(
                children
                    .into_iter()
                    .rev()
                    .map(|child| (child, child_policy, false)),
            );
            continue;
        }
        for child in children {
            values[&key(child, child_policy)].hash(&mut hash);
        }
        let hash = hash.finish();
        values.insert(key(value, policy), hash);
        if let FloatOperandView::Shared(root) = value {
            OPERAND_FINGERPRINTS.with(|memo| memo.borrow_mut().insert((policy, root.id()), hash));
        }
    }
    values[&key(root, policy)]
}

pub(super) fn collect_load_keys(root: &KernelTerm, keys: &mut BTreeSet<(AddressBase, u64)>) {
    let mut pending = vec![root];
    let mut seen = std::collections::HashSet::new();
    while let Some(root) = pending.pop() {
        if !seen.insert(root.id()) {
            continue;
        }
        crate::instrumentation::record_deterministic_work(1);
        if root.ty() == &KernelType::Bool {
            collect_condition_memory_load_keys(
                &crate::kernel::KernelTermExport::condition(root).expect("selected guard"),
                keys,
            );
            continue;
        }
        match root.node() {
            KernelTermNode::FloatRead(read) => {
                collect_float_read_load_keys(read.parts().1.exact_cell_key(), keys);
            }
            // Scalar read leaves cannot contribute to the float transport index.
            KernelTermNode::MemoryLoad { .. } => {}
            KernelTermNode::IntegerAddress { .. } => collect_bitvector_memory_load_keys(
                root.machine_conversion_leaf().expect("address"),
                keys,
            ),
            // These are opaque to the native memory-key walker too.
            KernelTermNode::Call { .. }
            | KernelTermNode::FloatCall(_)
            | KernelTermNode::Match(_)
            | KernelTermNode::IntegerToMachine { .. } => {}
            KernelTermNode::ImportedScalar(_)
            | KernelTermNode::MachineObservationInput { .. }
            | KernelTermNode::WrittenMachine(_) => {
                let native = legacy_numeric(root);
                collect_bitvector_memory_load_keys(native, keys);
            }
            _ => pending.extend(root.children()),
        }
    }
}

fn legacy_numeric(root: &KernelTerm) -> &MachineTerm {
    if let KernelTermNode::ImportedScalar(input) = root.node() {
        return input.value();
    }
    root.retained_machine_input().expect("numeric input")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn conversion_index_fingerprints_preserve_float_operator_policy() {
        let _session = crate::kernel::VerificationSession::enter();
        let mut fingerprints = Vec::new();
        for operator in [
            crate::kernel::FloatBinaryOperator::Add,
            crate::kernel::FloatBinaryOperator::Multiply,
        ] {
            let native = MachineTerm::opaque_conversion(
                "c_float32_to_int32",
                MachineTerm::Float32Binary {
                    operator,
                    left: Box::new(MachineTerm::Variable(Variable(999990))),
                    right: Box::new(MachineTerm::Variable(Variable(999991))),
                },
            );
            let root = crate::kernel::KernelTermImport::default()
                .machine(MachineIntegerType::Int32, &native);
            let pair = (
                operand_fingerprint(
                    MachineOperandView::Shared(&root),
                    OperandFingerprintPolicy::MemoryBlind,
                ),
                operand_fingerprint(
                    MachineOperandView::Shared(&root),
                    OperandFingerprintPolicy::MemoryState(false),
                ),
            );
            assert_eq!(
                pair.0,
                operand_fingerprint(
                    MachineOperandView::Legacy(&native),
                    OperandFingerprintPolicy::MemoryBlind
                )
            );
            assert_eq!(
                pair.1,
                operand_fingerprint(
                    MachineOperandView::Legacy(&native),
                    OperandFingerprintPolicy::MemoryState(false)
                )
            );
            fingerprints.push(pair);
        }
        assert_eq!(fingerprints[0].0, fingerprints[1].0);
        assert_ne!(fingerprints[0].1, fingerprints[1].1);
    }

    #[test]
    fn conversion_index_fingerprints_preserve_integer_source_forms() {
        let _session = crate::kernel::VerificationSession::enter();
        let variable = MachineTerm::Variable(Variable(999986));
        for (source, scoped) in [
            (variable.clone(), false),
            (
                MachineTerm::PureFunctionApplication {
                    name: "integer_source".into(),
                    arguments: vec![variable.clone()],
                },
                false,
            ),
            (
                MachineTerm::If {
                    condition: Box::new(ConditionTerm::Variable(Variable(999987))),
                    then_term: Box::new(variable.clone()),
                    else_term: Box::new(MachineTerm::constant(0)),
                },
                true,
            ),
            (
                MachineTerm::RangeFold {
                    start: Box::new(MachineTerm::constant(0)),
                    end: Box::new(variable.clone()),
                    initial: Box::new(MachineTerm::constant(0)),
                    accumulator: Variable(999988),
                    item: Variable(999989),
                    body: Box::new(variable),
                },
                true,
            ),
        ] {
            let native = MachineTerm::opaque_conversion(
                "c_float32_to_int32",
                MachineTerm::opaque_conversion("c_int32_to_float32", source),
            );
            let root = crate::kernel::KernelTermImport::default()
                .machine(MachineIntegerType::Int32, &native);
            let exports = crate::kernel::KernelTermExport::machine_export_count();
            for policy in [
                OperandFingerprintPolicy::MemoryBlind,
                OperandFingerprintPolicy::MemoryState(false),
                OperandFingerprintPolicy::MemoryState(true),
            ] {
                assert_eq!(
                    operand_fingerprint(MachineOperandView::Shared(&root), policy),
                    operand_fingerprint(MachineOperandView::Legacy(&native), policy)
                );
            }
            if !scoped {
                assert_eq!(
                    crate::kernel::KernelTermExport::machine_export_count(),
                    exports
                );
            }
        }
    }

    #[test]
    fn conversion_load_keys_do_not_build_a_native_float_read() {
        let _session = crate::kernel::VerificationSession::enter();
        let point = ProgramPoint::at(&crate::kernel::intern_memory(SymbolicMemory::new()));
        for (format, name) in [
            (KernelFloatType::Float32, "c_float32_to_int32"),
            (KernelFloatType::Float64, "c_float64_to_int32"),
        ] {
            let pointer = Address::symbolic(Variable(999978));
            let native = MachineTerm::opaque_conversion(
                name,
                MachineTerm::read_named(point.clone(), Box::new(pointer), format.load_kind()),
            );
            let root = KernelTermImport::default().machine(MachineIntegerType::Int32, &native);
            let KernelTermNode::FloatConvert { operand, .. } = root.node() else {
                panic!("float conversion");
            };
            let mut expected = BTreeSet::new();
            collect_bitvector_memory_load_keys(&native, &mut expected);
            let mut actual = BTreeSet::new();
            collect_load_keys(&root, &mut actual);
            assert_eq!(actual, expected);
            assert_eq!(actual.len(), 1);
            assert!(!operand.has_cached_native_argument());
        }
    }

    #[test]
    fn conversion_index_fingerprints_and_load_keys_match_native_policies() {
        let _session = crate::kernel::VerificationSession::enter();
        let pointer = Address::symbolic(Variable(999979));
        let mut policies = Vec::new();
        for memory in [
            SymbolicMemory::new(),
            SymbolicMemory::new().with_block("different", 4),
        ] {
            let source = MachineTerm::Float32Binary {
                operator: crate::kernel::FloatBinaryOperator::Add,
                left: Box::new(MachineTerm::read_named(
                    ProgramPoint::at(&(crate::kernel::intern_memory(memory))),
                    Box::new(pointer.clone()),
                    LoadKind::Float32,
                )),
                right: Box::new(MachineTerm::Variable(Variable(999980))),
            };
            let native = MachineTerm::opaque_conversion("c_float32_to_int32", source);
            let root = crate::kernel::KernelTermImport::default()
                .machine(MachineIntegerType::Int32, &native);
            for policy in [
                OperandFingerprintPolicy::MemoryBlind,
                OperandFingerprintPolicy::MemoryState(false),
                OperandFingerprintPolicy::MemoryState(true),
            ] {
                assert_eq!(
                    operand_fingerprint(MachineOperandView::Shared(&root), policy),
                    operand_fingerprint(MachineOperandView::Legacy(&native), policy)
                );
            }
            policies.push((
                operand_fingerprint(
                    MachineOperandView::Shared(&root),
                    OperandFingerprintPolicy::MemoryBlind,
                ),
                operand_fingerprint(
                    MachineOperandView::Shared(&root),
                    OperandFingerprintPolicy::MemoryState(false),
                ),
            ));
            let mut expected = BTreeSet::new();
            collect_bitvector_memory_load_keys(&native, &mut expected);
            let mut actual = BTreeSet::new();
            collect_scoped_leaf_memory_load_keys(MachineOperandView::Shared(&root), &mut actual);
            assert!(!expected.is_empty());
            assert_eq!(actual, expected);
        }
        assert_eq!(policies[0].0, policies[1].0);
        assert_ne!(policies[0].1, policies[1].1);
    }
}

#[cfg(test)]
mod float_call_tests {
    use super::*;
    #[test]
    fn float_call_index_fingerprints_and_load_policies_match_native() {
        let _session = crate::kernel::VerificationSession::enter();
        let native = MachineTerm::opaque_conversion(
            "c_float32_to_int32",
            MachineTerm::ClickFunctionApplication {
                name: "float_index".into(),
                arguments: vec![PureFunctionArgument::Value(ProgramValue::Float32(
                    MachineTerm::Variable(Variable(1008209)),
                ))],
            },
        );
        let root =
            crate::kernel::KernelTermImport::default().machine(MachineIntegerType::Int32, &native);
        for policy in [
            OperandFingerprintPolicy::MemoryBlind,
            OperandFingerprintPolicy::MemoryState(false),
            OperandFingerprintPolicy::MemoryState(true),
        ] {
            assert_eq!(
                operand_fingerprint(MachineOperandView::Shared(&root), policy),
                operand_fingerprint(MachineOperandView::Legacy(&native), policy)
            );
        }
        let mut actual = BTreeSet::new();
        collect_load_keys(&root, &mut actual);
        let mut expected = BTreeSet::new();
        collect_bitvector_memory_load_keys(&native, &mut expected);
        assert_eq!(actual, expected);
    }
}

#[cfg(test)]
mod float_call_identity_tests {
    use super::*;
    #[test]
    fn float_call_fingerprints_are_session_independent_and_keep_argument_operators() {
        let native = |operator| {
            MachineTerm::opaque_conversion(
                "c_float32_to_int32",
                MachineTerm::ClickFunctionApplication {
                    name: "float_identity".into(),
                    arguments: vec![PureFunctionArgument::Value(ProgramValue::Float32(
                        MachineTerm::Float32Binary {
                            operator,
                            left: Box::new(MachineTerm::Variable(Variable(1008213))),
                            right: Box::new(MachineTerm::Variable(Variable(1008214))),
                        },
                    ))],
                },
            )
        };
        let mut sessions = Vec::new();
        for _ in 0..2 {
            let _session = crate::kernel::VerificationSession::enter();
            let mut hashes = Vec::new();
            for operator in [
                crate::kernel::FloatBinaryOperator::Add,
                crate::kernel::FloatBinaryOperator::Multiply,
            ] {
                let source = native(operator);
                let root = crate::kernel::KernelTermImport::default()
                    .machine(MachineIntegerType::Int32, &source);
                let exports = crate::kernel::KernelTermExport::float_export_count();
                for policy in [
                    OperandFingerprintPolicy::MemoryBlind,
                    OperandFingerprintPolicy::MemoryState(false),
                ] {
                    let hash = operand_fingerprint(MachineOperandView::Shared(&root), policy);
                    assert_eq!(
                        hash,
                        operand_fingerprint(MachineOperandView::Legacy(&source), policy)
                    );
                    hashes.push(hash);
                }
                assert_eq!(
                    crate::kernel::KernelTermExport::float_export_count(),
                    exports
                );
            }
            assert_ne!(hashes[0], hashes[2]);
            assert_ne!(hashes[1], hashes[3]);
            sessions.push(hashes);
        }
        assert_eq!(sessions[0], sessions[1]);
    }
}
