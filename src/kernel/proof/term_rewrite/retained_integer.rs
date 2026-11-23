//! Retained Integer arithmetic, observations and conditionals preserve the
//! native walker's substitution, selection and accounting rules. Scoped folds, matches and other families are integrated
//! separately; this entry point does not export an unsupported prefix.
use super::*;

impl TermRewrite<'_> {
    pub(super) fn reserve_shared_rewrite_variables_once(
        &mut self,
        root: &KernelTerm,
    ) -> Option<()> {
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
                        if term.ty() == &KernelType::Integer {
                            variables.integer.insert(*variable);
                        }
                    }
                    KernelTermNode::IntegerLiteral(_) | KernelTermNode::BoolLiteral(_) => {}
                    KernelTermNode::IntegerIf { arguments } => {
                        if self.collected_conditions.is_some() {
                            // Native IntegerIf also emits its written guard as
                            // a candidate; common candidate output is separate.
                            return None;
                        }
                        pending.extend(arguments);
                    }
                    KernelTermNode::BoolIf { arguments } => pending.extend(arguments),
                    KernelTermNode::BoolEqual { arguments } => pending.extend(arguments),
                    KernelTermNode::IntegerOperation { arguments, .. } => pending.extend(arguments),
                    KernelTermNode::IntegerCompare { arguments, .. } => pending.extend(arguments),
                    KernelTermNode::BoolCompare { arguments, .. }
                    | KernelTermNode::BoolOverflow { arguments, .. } => {
                        for operand in arguments {
                            collect_machine_operand_carriers(
                                MachineOperandView::Shared(operand),
                                &mut variables,
                            );
                            if variables.exhausted() {
                                self.reserve_source_variables(variables);
                                return None;
                            }
                        }
                    }
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
        Some(())
    }

    #[allow(dead_code)] // Term dispatch activation follows its remaining node families.
    pub(in crate::kernel) fn shared_integer_operand(
        &mut self,
        root: &KernelTerm,
    ) -> Option<KernelTerm> {
        self.shared_integer_operand_in(root, false)
    }

    /// Fold scope already performs capture checks. Rewrite arithmetic and
    /// nested folds here, bridging the remaining node families.
    pub(super) fn shared_fold_integer_child(&mut self, root: &KernelTerm) -> Option<KernelTerm> {
        self.shared_integer_operand_in(root, true)
    }

    fn shared_integer_operand_in(
        &mut self,
        root: &KernelTerm,
        fold_child: bool,
    ) -> Option<KernelTerm> {
        if root.ty() != &KernelType::Integer || self.integer_exact.is_some() {
            // This partial entry point admits variable/typed substitutions.
            // Exact-source/read-through matching is required before Term use.
            return None;
        }
        if !fold_child {
            self.reserve_shared_rewrite_variables_once(root)?;
            self.visit(); // The native integer entry charges before its shared walk.
        }
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
        let key = |term: &KernelTerm| (term.id(), scope_id, disabled, shadowed, reads, fold_child);
        let mut import = KernelTermImport::default();
        let mut pending = vec![(root.clone(), false)];
        let mut guards = HashMap::new();
        while let Some((term, finish)) = pending.pop() {
            if self.checked_work_exhausted() {
                return None;
            }
            if memo.borrow().contains_key(&key(&term)) {
                continue;
            }
            let retained_fold_if = self.condition_exact.is_none()
                && matches!(
                    term.node(),
                    KernelTermNode::IntegerIf { arguments }
                        if matches!(arguments[0].node(), KernelTermNode::BoolLiteral(_))
                );
            if fold_child
                && !retained_fold_if
                && !matches!(
                    term.node(),
                    KernelTermNode::IntegerLiteral(_)
                        | KernelTermNode::Variable(_)
                        | KernelTermNode::IntegerOperation { .. }
                        | KernelTermNode::Fold(_)
                )
            {
                let native = self.fold_integer_bridge.integer(&term).ok()?;
                let rewritten = self.integer_shared(&native);
                if self.refusal_status().is_some() {
                    return None;
                }
                memo.borrow_mut()
                    .insert(key(&term), import.integer(&rewritten.into()));
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
                KernelTermNode::Fold(fold) if fold_child => {
                    self.retained_fold_in(fold).ok()?.into_term()
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
                KernelTermNode::IntegerIf { arguments } => {
                    if self.collected_conditions.is_some() && !fold_child {
                        return None;
                    }
                    if !finish {
                        let (guard, preserve) = if fold_child {
                            // Keep the native guard check and its collection
                            // rules while the Integer arms stay in the DAG.
                            let guard = KernelTermExport::condition(&arguments[0]).ok()?;
                            if let Some(conditions) = &mut self.collected_conditions {
                                conditions.push(guard.clone());
                            }
                            let preserve = self.preserves_closed_value_conditional(&guard);
                            let guard = self.condition(&guard);
                            if self.checked_work_exhausted() {
                                return None;
                            }
                            (import.condition(&guard), preserve)
                        } else {
                            let preserve = self.integer_variables.is_some()
                                && crate::kernel::proof::fact_reasoning::is_literal_value_if_guard_root(
                                    &arguments[0],
                                );
                            let guard = self.shared_boolean_operand(&arguments[0])?;
                            let guard = if preserve {
                                guard
                            } else {
                                common_boolean::folded_shared_machine_condition(guard)
                            };
                            (guard, preserve)
                        };
                        guards.insert(term.id(), (guard.clone(), preserve));
                        pending.push((term.clone(), true));
                        if !preserve
                            && let Some(value) = BooleanOperandView::Shared(&guard).constant()
                        {
                            pending.push((arguments[if value { 1 } else { 2 }].clone(), false));
                        } else {
                            pending.push((arguments[2].clone(), false));
                            pending.push((arguments[1].clone(), false));
                        }
                        continue;
                    }
                    let (guard, preserve) =
                        guards.remove(&term.id()).expect("rewritten Integer guard");
                    if !preserve && let Some(value) = BooleanOperandView::Shared(&guard).constant()
                    {
                        memo.borrow()[&key(&arguments[if value { 1 } else { 2 }])].clone()
                    } else {
                        let yes = memo.borrow()[&key(&arguments[1])].clone();
                        let no = memo.borrow()[&key(&arguments[2])].clone();
                        crate::instrumentation::record_deterministic_work(1);
                        if !preserve && yes.integer_native_syntax_equal(&no) {
                            yes
                        } else {
                            KernelTerm::integer_if_raw([guard, yes, no])
                        }
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
    fn partial_integer_dispatch_does_not_admit_exact_mode_or_unsupported_guards() {
        let _session = VerificationSession::enter();
        let source = SharedIntegerTerm::from(IntegerTerm::Variable(Variable(991940)));
        let target = SharedIntegerTerm::from(IntegerTerm::constant_i64(7));
        let root = KernelTerm::variable(KernelType::Integer, Variable(991940));
        let mut exact = TermRewrite::for_integer_exact(&source, &target);
        assert!(exact.shared_integer_operand(&root).is_none());
        assert!(exact.refusal_status().is_none());
        assert!(!root.has_cached_native_argument());
        let guard = KernelTermImport::default().condition(&ConditionTerm::bool_application(
            "unsupported_integer_rewrite_guard",
            Vec::new(),
        ));
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

#[cfg(test)]
mod conditional_tests {
    use super::*;

    #[test]
    fn retained_integer_conditionals_match_native_guard_scope_and_arm_rules() {
        let _session = VerificationSession::enter();
        let from = Variable(995100);
        let other = Variable(995101);
        let guard = Variable(995102);
        for condition in [
            ConditionTerm::Constant(false),
            ConditionTerm::Constant(true),
            ConditionTerm::Variable(guard),
            ConditionTerm::BoolEqual(
                Box::new(ConditionTerm::Variable(guard)),
                Box::new(ConditionTerm::Variable(guard)),
            ),
        ] {
            for no in [IntegerTerm::Variable(other), IntegerTerm::constant_i64(3)] {
                let input = IntegerTerm::If {
                    condition: Box::new(condition.clone()),
                    then_term: IntegerTerm::Variable(from).into(),
                    else_term: no.into(),
                };
                let root = KernelTermImport::default().integer(&input.clone().into());
                for truth in [
                    ConditionTerm::Constant(false),
                    ConditionTerm::Constant(true),
                    ConditionTerm::Variable(Variable(995103)),
                ] {
                    let program = BTreeMap::from([(
                        guard,
                        TypedProgramValueReplacement::Bitvector(MachineTerm::bool_cast(
                            MachineIntegerType::UInt8,
                            truth,
                        )),
                    )]);
                    let integers = BTreeMap::from([(from, IntegerTerm::Variable(other))]);
                    let algebraic = BTreeMap::new();
                    let mut baseline =
                        TermRewrite::for_typed_variables(&program, &integers, &algebraic);
                    let mut rewrite =
                        TermRewrite::for_typed_variables(&program, &integers, &algebraic);
                    for scoped in [false, true, false] {
                        let a = scoped.then(|| {
                            baseline.push_program_substitution_scope(guard, Variable(995104))
                        });
                        let b = scoped.then(|| {
                            rewrite.push_program_substitution_scope(guard, Variable(995104))
                        });
                        let c = scoped.then(|| {
                            baseline.push_integer_substitution_scope(from, Variable(995105), false)
                        });
                        let d = scoped.then(|| {
                            rewrite.push_integer_substitution_scope(from, Variable(995105), false)
                        });
                        let expected = baseline.integer(&input);
                        let exports = KernelTermExport::machine_export_count();
                        let cached = root.has_cached_native_argument();
                        let actual = rewrite.shared_integer_operand(&root).unwrap();
                        assert_eq!(KernelTermExport::machine_export_count(), exports);
                        assert_eq!(root.has_cached_native_argument(), cached);
                        assert!(!actual.has_cached_native_argument());
                        assert_eq!(rewrite.changed, baseline.changed);
                        assert_eq!(rewrite.refusal(), baseline.refusal());
                        assert_eq!(
                            rewrite.reserved_variables, baseline.reserved_variables,
                            "Boolean guard names must not enter Integer source reservation"
                        );
                        let actual = KernelTermExport::default().integer(&actual).unwrap();
                        assert_eq!(
                            actual.as_ref(),
                            &expected,
                            "input={input:?}, scoped={scoped}"
                        );
                        assert_eq!(format!("{:?}", actual.as_ref()), format!("{expected:?}"));
                        if let Some(scope) = d {
                            rewrite.pop_integer_substitution_scope(scope);
                        }
                        if let Some(scope) = c {
                            baseline.pop_integer_substitution_scope(scope);
                        }
                        if let Some(scope) = b {
                            rewrite.pop_program_substitution_scope(scope);
                        }
                        if let Some(scope) = a {
                            baseline.pop_program_substitution_scope(scope);
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn retained_integer_equal_native_arms_keep_the_left_producer() {
        let _session = VerificationSession::enter();
        let ProgramValue::Pointer(pointer) =
            crate::kernel::symbolic_call_result(ProgramType::Int32Pointer, Variable(995120))
        else {
            unreachable!("typed pointer")
        };
        let calls = [false, true].map(|constant| {
            IntegerTerm::PureFunctionApplication(SharedPureApplication::intern(
                "retained_if_arm".into(),
                vec![PureFunctionArgument::Value(ProgramValue::Pointer(
                    pointer
                        .clone()
                        .with_declared_object_class(constant.then(|| {
                            crate::kernel::effective_type::CAccessClass::Scalar(
                                crate::kernel::effective_type::CScalarClass::Int,
                            )
                        })),
                ))],
            ))
        });
        assert_eq!(calls[0], calls[1]);
        let arms = calls
            .clone()
            .map(|call| KernelTermImport::default().integer(&call.into()));
        assert_ne!(arms[0], arms[1], "distinct retained pointer qualifiers");
        let from = Variable(995121);
        let to = Variable(995122);
        let input = IntegerTerm::If {
            condition: Box::new(ConditionTerm::Variable(Variable(995123))),
            then_term: IntegerTerm::Variable(from).into(),
            else_term: IntegerTerm::Variable(to).into(),
        };
        let root = KernelTermImport::default().integer(&input.clone().into());
        let program = BTreeMap::new();
        let integers = BTreeMap::from([(from, calls[0].clone()), (to, calls[1].clone())]);
        let algebraic = BTreeMap::new();
        let mut baseline = TermRewrite::for_typed_variables(&program, &integers, &algebraic);
        let expected = baseline.integer(&input);
        let mut rewrite = TermRewrite::for_typed_variables(&program, &integers, &algebraic);
        let actual = rewrite.shared_integer_operand(&root).unwrap();
        assert_eq!(
            actual.id(),
            arms[0].id(),
            "native equal-arm reduction retains the left producer"
        );
        assert!(!root.has_cached_native_argument());
        assert_eq!(rewrite.refusal(), baseline.refusal());
        assert_eq!(
            KernelTermExport::default()
                .integer(&actual)
                .unwrap()
                .as_ref(),
            &expected
        );
    }

    #[test]
    fn retained_integer_conditionals_skip_unreachable_literal_work_and_preserve_refusal() {
        let _session = VerificationSession::enter();
        let large = IntegerTerm::Constant(num_bigint::BigInt::from(1) << 1024usize);
        let guard = Variable(995140);
        for truth in [false, true] {
            for selected_large in [false, true] {
                let arms = if truth == selected_large {
                    [large.clone(), IntegerTerm::constant_i64(3)]
                } else {
                    [IntegerTerm::constant_i64(3), large.clone()]
                };
                let input = IntegerTerm::If {
                    condition: Box::new(ConditionTerm::Variable(guard)),
                    then_term: arms[0].clone().into(),
                    else_term: arms[1].clone().into(),
                };
                let root = KernelTermImport::default().integer(&input.clone().into());
                let program = BTreeMap::from([(
                    guard,
                    TypedProgramValueReplacement::Bitvector(MachineTerm::bool_cast(
                        MachineIntegerType::UInt8,
                        ConditionTerm::Constant(truth),
                    )),
                )]);
                let integer = BTreeMap::new();
                let algebraic = BTreeMap::new();
                let (expected, native_refusal) =
                    crate::instrumentation::with_run_work_limit(128, || {
                        let mut rewrite =
                            TermRewrite::for_typed_variables(&program, &integer, &algebraic);
                        let result = rewrite.integer(&input);
                        (result, rewrite.refusal())
                    });
                let exports = KernelTermExport::machine_export_count();
                let (result, refusal, reserved) =
                    crate::instrumentation::with_run_work_limit(128, || {
                        let mut rewrite =
                            TermRewrite::for_typed_variables(&program, &integer, &algebraic);
                        let result = rewrite.shared_integer_operand(&root);
                        (result, rewrite.refusal(), rewrite.source_variables_reserved)
                    });
                assert!(
                    reserved,
                    "both arms' carrier collection completes before guard selection"
                );
                assert_eq!(refusal, native_refusal);
                assert_eq!(
                    refusal,
                    selected_large.then_some(RewriteRefusal::WorkExhausted)
                );
                assert_eq!(KernelTermExport::machine_export_count(), exports);
                assert!(!root.has_cached_native_argument());
                if selected_large {
                    assert!(result.is_none());
                } else {
                    assert_eq!(
                        KernelTermExport::default()
                            .integer(&result.unwrap())
                            .unwrap()
                            .as_ref(),
                        &expected
                    );
                }
            }
        }
    }
    #[test]
    fn retained_dispatch_memos_do_not_widen_machine_input_domains() {
        let _session = VerificationSession::enter();
        let roots = [
            KernelTerm::variable(KernelType::Integer, Variable(995180)),
            KernelTerm::variable(KernelType::Bool, Variable(995181)),
        ];
        let mut rejected_after_caching = Vec::new();
        for root in roots {
            let mut rewrite = TermRewrite::empty();
            assert!(
                rewrite.shared_machine_operand(&root).is_none(),
                "cold numeric admission"
            );
            if root.ty() == &KernelType::Integer {
                rewrite.shared_integer_operand(&root).unwrap();
            } else {
                rewrite.shared_boolean_operand(&root).unwrap();
            }
            rejected_after_caching.push(rewrite.shared_machine_operand(&root).is_none());
            assert!(rewrite.refusal().is_none());
        }
        assert_eq!(
            rejected_after_caching,
            vec![true, true],
            "a retained result is not evidence of numeric input admission"
        );
    }
}
