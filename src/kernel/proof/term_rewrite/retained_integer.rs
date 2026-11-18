//! Raw retained Integer arithmetic uses the native walker's substitution and
//! accounting rules. Scoped folds, matches and other families are integrated
//! separately; this entry point does not export an unsupported prefix.
use super::*;

impl TermRewrite<'_> {
    #[allow(dead_code)] // Term dispatch activation follows its remaining node families.
    pub(in crate::kernel) fn shared_integer_operand(
        &mut self,
        root: &KernelTerm,
    ) -> Option<KernelTerm> {
        if root.ty() != &KernelType::Integer || self.integer_exact.is_some() {
            // This partial entry point admits variable/typed substitutions.
            // Exact-source/read-through matching is required before Term use.
            return None;
        }
        if !self.source_variables_reserved {
            let mut variables = self.new_carrier_variables();
            let mut pending = vec![root];
            let mut seen = BTreeSet::new();
            while let Some(term) = pending.pop() {
                if !seen.insert(term.id()) {
                    continue;
                }
                if !variables.visit() {
                    self.reserve_source_variables(variables);
                    return None;
                }
                match term.node() {
                    KernelTermNode::Variable(variable) => {
                        variables.integer.insert(*variable);
                    }
                    KernelTermNode::IntegerLiteral(_) => {}
                    KernelTermNode::IntegerOperation { arguments, .. } => pending.extend(arguments),
                    KernelTermNode::MachineObservation { operand, .. } => {
                        collect_machine_operand_carriers(
                            MachineOperandView::Shared(operand),
                            &mut variables,
                        );
                        if variables.exhausted() {
                            self.reserve_source_variables(variables);
                            return None;
                        }
                    }
                    _ => return None,
                }
            }
            self.reserve_source_variables(variables);
        }
        self.visit(); // The native integer entry charges before its shared walk.
        if self.checked_work_exhausted() {
            return None;
        }
        let memo = self
            .shared_machine_cache
            .get_or_insert_with(Default::default)
            .clone();
        let scope_id = self.scope_id;
        let disabled = self.source_disabled;
        let shadowed = self.integer_shadowed;
        let reads = self.resolve_registered_loads;
        let key = |term: &KernelTerm| (term.id(), scope_id, disabled, shadowed, reads);
        let mut import = KernelTermImport::default();
        let mut pending = vec![(root.clone(), false)];
        while let Some((term, finish)) = pending.pop() {
            if self.checked_work_exhausted() {
                return None;
            }
            if memo.borrow().contains_key(&key(&term)) {
                continue;
            }
            if !finish {
                self.visit();
                if self.checked_work_exhausted() {
                    return None;
                }
            }
            let value = match term.node() {
                KernelTermNode::IntegerLiteral(value) => {
                    if self.integer_variables.is_some()
                        || self.typed_variables.is_some()
                        || self.enforce_integer_work_limit
                    {
                        self.charge_rewrite_work(value.bits() as usize + 1);
                        if self.checked_work_exhausted() {
                            return None;
                        }
                    }
                    term.clone()
                }
                KernelTermNode::Variable(variable) => {
                    let rewritten = self.rewrite_integer_variable(*variable);
                    if self.checked_work_exhausted() {
                        return None;
                    }
                    if matches!(rewritten, IntegerTerm::Variable(result) if result == *variable) {
                        term.clone()
                    } else {
                        import.integer(&rewritten.into())
                    }
                }
                KernelTermNode::MachineObservation { format, operand } => {
                    let rewritten = self.shared_machine_operand(operand)?;
                    let changed = rewritten != *operand;
                    let view = MachineOperandView::Shared(&rewritten);
                    let observed = view
                        .observe(*format)
                        .unwrap_or_else(|| IntegerTerm::Machine(view.retain(*format)));
                    let observed = match observed {
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
                        observed => observed,
                    };
                    if !changed && matches!(observed, IntegerTerm::Machine(_)) {
                        // A no-op keeps the producer's exact observation handle.
                        term.clone()
                    } else {
                        import.integer(&observed.into())
                    }
                }
                KernelTermNode::IntegerOperation {
                    operator,
                    arguments,
                } => {
                    if !finish {
                        pending.push((term.clone(), true));
                        pending.extend(arguments.iter().rev().cloned().map(|child| (child, false)));
                        continue;
                    }
                    let rewritten = arguments
                        .iter()
                        .map(|child| memo.borrow()[&key(child)].clone())
                        .collect();
                    KernelTerm::integer_operation(*operator, rewritten).ok()?
                }
                _ => return None,
            };
            memo.borrow_mut().insert(key(&term), value);
        }
        memo.borrow().get(&key(root)).cloned()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn native(operator: KernelIntegerOperator, children: &[IntegerTerm]) -> IntegerTerm {
        let a = children[0].clone().into();
        if operator == KernelIntegerOperator::Negate {
            return IntegerTerm::Negate(a);
        }
        let b = children[1].clone().into();
        match operator {
            KernelIntegerOperator::Add => IntegerTerm::Add(a, b),
            KernelIntegerOperator::Subtract => IntegerTerm::Subtract(a, b),
            KernelIntegerOperator::Multiply => IntegerTerm::Multiply(a, b),
            KernelIntegerOperator::TruncatingQuotient => IntegerTerm::TruncatingQuotient(a, b),
            KernelIntegerOperator::TruncatingRemainder => IntegerTerm::TruncatingRemainder(a, b),
            KernelIntegerOperator::Negate => unreachable!(),
        }
    }

    #[test]
    fn retained_integer_arithmetic_matches_native_variable_substitution() {
        let _session = VerificationSession::enter();
        let from = Variable(991900);
        let other = Variable(991901);
        for operator in [
            KernelIntegerOperator::Negate,
            KernelIntegerOperator::Add,
            KernelIntegerOperator::Subtract,
            KernelIntegerOperator::Multiply,
            KernelIntegerOperator::TruncatingQuotient,
            KernelIntegerOperator::TruncatingRemainder,
        ] {
            let count = if operator == KernelIntegerOperator::Negate {
                1
            } else {
                2
            };
            let children = [IntegerTerm::Variable(from), IntegerTerm::constant_i64(3)];
            let native = native(operator, &children[..count]);
            let root = KernelTerm::integer_operation(
                operator,
                vec![
                    KernelTerm::variable(KernelType::Integer, from),
                    KernelTerm::integer_literal(3.into()),
                ][..count]
                    .to_vec(),
            )
            .unwrap();
            for replacement in [IntegerTerm::constant_i64(7), IntegerTerm::Variable(other)] {
                for renamings in [BTreeMap::new(), BTreeMap::from([(from, Variable(991902))])] {
                    let mut baseline =
                        TermRewrite::for_integer_variables(from, &replacement, false, &renamings);
                    let expected = baseline.integer(&native);
                    let mut rewrite =
                        TermRewrite::for_integer_variables(from, &replacement, false, &renamings);
                    let exports = KernelTermExport::machine_export_count();
                    let was_cached = root.has_cached_native_argument();
                    let actual = rewrite
                        .shared_integer_operand(&root)
                        .expect("raw Integer arithmetic");
                    assert_eq!(root.has_cached_native_argument(), was_cached);
                    assert_eq!(KernelTermExport::machine_export_count(), exports);
                    assert_eq!(rewrite.refusal_status(), baseline.refusal_status());
                    assert_eq!(actual.integer_native_compat().unwrap(), &expected);
                }
            }
        }
    }
    #[test]
    fn retained_integer_replacements_preserve_registered_and_structural_observations() {
        let _session = VerificationSession::enter();
        let from = Variable(991930);
        let address = Address::symbolic(Variable(991931));
        let memory = intern_memory(SymbolicMemory::new());
        let load = crate::kernel::eval::load_variable_for_exact_cell(
            &memory,
            &address,
            LoadKind::Int32,
            4,
        );
        let replacements = [
            MachineTerm::Variable(load),
            MachineTerm::MemoryLoad(
                ProgramPoint::at(&memory),
                Box::new(address),
                LoadKind::Int32,
            ),
        ]
        .map(|machine| IntegerTerm::from_machine(MachineIntegerType::Int32, machine).unwrap());
        let root = KernelTerm::integer_operation(
            KernelIntegerOperator::Add,
            vec![
                KernelTerm::variable(KernelType::Integer, from),
                KernelTerm::integer_literal(3.into()),
            ],
        )
        .unwrap();
        let input = IntegerTerm::Add(
            IntegerTerm::Variable(from).into(),
            IntegerTerm::constant_i64(3).into(),
        );
        let mut outputs = Vec::new();
        for replacement in &replacements {
            let renamings = BTreeMap::new();
            let expected = TermRewrite::for_integer_variables(from, replacement, false, &renamings)
                .integer(&input);
            let mut rewrite =
                TermRewrite::for_integer_variables(from, replacement, false, &renamings);
            let exports = KernelTermExport::machine_export_count();
            let output = rewrite.shared_integer_operand(&root).unwrap();
            assert_eq!(KernelTermExport::machine_export_count(), exports);
            // Scope is queried through a fresh common condition, before any
            // native DTO read can warm a compatibility slot.
            let comparison = KernelTerm::integer_comparison(
                IntegerComparisonOperator::Equal,
                [output.clone(), KernelTerm::integer_literal(0.into())],
            )
            .unwrap();
            let proposition = Proposition::condition_is(
                StoredConditionTerm::from_root(comparison).unwrap(),
                true,
            );
            let mut actual_variables = BTreeSet::new();
            crate::kernel::prelude::collect_proposition_bitvector_variables(
                &proposition,
                &mut actual_variables,
            );
            let mut expected_variables = BTreeSet::new();
            crate::kernel::prelude::collect_integer_variables(&expected, &mut expected_variables);
            assert_eq!(actual_variables, expected_variables);
            let actual = output.integer_native_compat().unwrap();
            assert_eq!(actual, &expected);
            assert_eq!(format!("{actual:?}"), format!("{expected:?}"));
            outputs.push(output);
        }
        assert_eq!(outputs.len(), 2); // Keep both observation spellings alive.
    }

    #[test]
    fn partial_integer_dispatch_does_not_admit_exact_mode_or_other_nodes() {
        let _session = VerificationSession::enter();
        let source = SharedIntegerTerm::from(IntegerTerm::Variable(Variable(991940)));
        let target = SharedIntegerTerm::from(IntegerTerm::constant_i64(7));
        let root = KernelTerm::variable(KernelType::Integer, Variable(991940));
        let mut exact = TermRewrite::for_integer_exact(&source, &target);
        assert!(exact.shared_integer_operand(&root).is_none());
        assert!(exact.refusal_status().is_none());
        assert!(!root.has_cached_native_argument());
        let guard = KernelTerm::variable(KernelType::Bool, Variable(991941));
        let conditional = KernelTerm::integer_if_raw([guard, root.clone(), root.clone()]);
        let renamings = BTreeMap::new();
        let replacement = IntegerTerm::constant_i64(7);
        let mut variables =
            TermRewrite::for_integer_variables(Variable(991940), &replacement, false, &renamings);
        assert!(variables.shared_integer_operand(&conditional).is_none());
        assert!(variables.refusal_status().is_none());
        assert!(!conditional.has_cached_native_argument());
    }
    #[test]
    fn retained_machine_observations_match_native_widths_literals_reads_and_changes() {
        let _session = VerificationSession::enter();
        let from = Variable(991970);
        let address = Address {
            base: AddressBase::Symbolic(Variable(991971)),
            offset: AddressOffset::scaled_int32_node(MachineTerm::Variable(from), 4),
        };
        let memory = intern_memory(SymbolicMemory::new());
        let read = MachineTerm::MemoryLoad(
            ProgramPoint::at(&memory),
            Box::new(address),
            LoadKind::Int32,
        );
        let mut cases = Vec::new();
        for format in [
            MachineIntegerType::Int8,
            MachineIntegerType::UInt8,
            MachineIntegerType::Int16,
            MachineIntegerType::UInt16,
            MachineIntegerType::Int32,
            MachineIntegerType::UInt32,
            MachineIntegerType::Int64,
            MachineIntegerType::UInt64,
            MachineIntegerType::Int128,
            MachineIntegerType::UInt128,
        ] {
            let bits = format.format().bits();
            let mask = if bits == 128 {
                u128::MAX
            } else {
                (1u128 << bits) - 1
            };
            cases.extend([
                (format, MachineTerm::Variable(from)),
                (format, MachineTerm::Constant { format, bits: 0 }),
                (format, MachineTerm::Constant { format, bits: mask }),
            ]);
        }
        // The observation may reject a numeric literal reading and retain its
        // original typed handle. Do not introduce a new signedness policy.
        cases.push((
            MachineIntegerType::Int64,
            MachineTerm::uint64_constant(u64::MAX),
        ));
        cases.push((MachineIntegerType::Int32, read));
        for (format, machine) in cases {
            let input = IntegerTerm::Machine(SharedMachineIntegerTerm::intern(format, machine));
            let root = KernelTermImport::default().integer(&input.clone().into());
            assert!(matches!(
                root.node(),
                KernelTermNode::MachineObservation { .. }
            ));
            for replacement in [
                MachineTerm::constant(7),
                MachineTerm::Variable(Variable(991972)),
            ] {
                for source in [
                    MachineTerm::Variable(from),
                    MachineTerm::Variable(Variable(991973)),
                ] {
                    let mut baseline = TermRewrite::for_bits_checked(&source, &replacement);
                    let expected = baseline.integer(&input);
                    let expected_debug = format!("{expected:?}");
                    let mut rewrite = TermRewrite::for_bits_checked(&source, &replacement);
                    let exports = KernelTermExport::machine_export_count();
                    let was_cached = root.has_cached_native_argument();
                    let actual = rewrite.shared_integer_operand(&root);
                    assert_eq!(
                        rewrite.refusal_status(),
                        baseline.refusal_status(),
                        "format={format:?}"
                    );
                    let actual = actual.expect("selected numeric observation");
                    assert_eq!(
                        KernelTermExport::machine_export_count(),
                        exports,
                        "format={format:?}"
                    );
                    assert_eq!(root.has_cached_native_argument(), was_cached);
                    let output = actual.integer_native_compat().unwrap();
                    assert_eq!(output, &expected, "format={format:?}");
                    assert_eq!(format!("{output:?}"), expected_debug, "format={format:?}");
                }
            }
        }
    }
}

#[cfg(test)]
mod scaling_tests {
    include!("../../../scaling_tests/kernel/proof/term_rewrite/retained_integer.rs");
}
