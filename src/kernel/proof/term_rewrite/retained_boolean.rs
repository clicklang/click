//! Bounded retained Boolean value rewriting on the active substitution scope.
//! Scalar predicate leaves and native whole-condition lookup modes are admitted
//! separately; an unsupported common guard is never exported as a fallback.
use super::*;
use std::cell::RefCell;

impl TermRewrite<'_> {
    #[allow(dead_code)] // Activated after the remaining Term node families.
    pub(in crate::kernel) fn shared_boolean_operand(
        &mut self,
        root: &KernelTerm,
    ) -> Option<KernelTerm> {
        if root.ty() != &KernelType::Bool {
            return None;
        }
        if matches!(
            root.node(),
            KernelTermNode::BoolIf { .. } | KernelTermNode::BoolEqual { .. }
        ) && (self.condition_exact.is_some()
            || self.conditions.is_some()
            || self.cited_conditions.is_some()
            || self.collected_conditions.is_some())
        {
            // Native lookup precedes descent, including at internal guards.
            // Its retained dispatch must be implemented before admitting it.
            return None;
        }
        self.reserve_shared_rewrite_variables_once(root)?;
        if self.checked_work_exhausted() {
            return None;
        }
        // Both callbacks share this exact active scope. The traversal's local
        // node memo retains common connectives and avoids unfolding DAGs.
        let memo = self
            .shared_machine_cache
            .get_or_insert_with(Default::default)
            .clone();
        let scope = (
            self.scope_id,
            self.source_disabled,
            self.integer_shadowed,
            self.resolve_registered_loads,
        );
        let key = |term: &KernelTerm| (term.id(), scope.0, scope.1, scope.2, scope.3, false);
        let reuse = self.integer_exact.is_none()
            && self.condition_exact.is_none()
            && self.conditions.is_none()
            && self.cited_conditions.is_none()
            && self.collected_conditions.is_none();
        let rewrite = RefCell::new(self);
        root.map_boolean_with_connectives_cached(
            |term| {
                reuse
                    .then(|| memo.borrow().get(&key(term)).cloned())
                    .flatten()
            },
            |term| {
                let result = rewrite
                    .borrow_mut()
                    .shared_boolean_scalar_leaf(term)
                    .ok_or(())?;
                memo.borrow_mut().insert(key(term), result.clone());
                Ok(result)
            },
            |term, children| {
                let mut rewrite = rewrite.borrow_mut();
                rewrite.visit();
                if rewrite.checked_work_exhausted() {
                    return Err(());
                }
                let raw = rewrite.integer_exact.is_some();
                let result = match (term.node(), children) {
                    (KernelTermNode::BoolIf { .. }, [guard, yes, no]) => {
                        let guard = if raw {
                            guard.clone()
                        } else {
                            common_boolean::folded_shared_machine_condition(guard.clone())
                        };
                        let arguments = [guard, yes.clone(), no.clone()];
                        Ok(if raw {
                            KernelTerm::boolean_if_raw(arguments)
                        } else {
                            KernelTerm::boolean_if(arguments)
                        })
                    }
                    (KernelTermNode::BoolEqual { .. }, [left, right]) => {
                        let arguments = [left.clone(), right.clone()];
                        Ok(if raw {
                            KernelTerm::boolean_equal_raw(arguments)
                        } else {
                            KernelTerm::boolean_equal(arguments)
                        })
                    }
                    _ => Err(()),
                }?;
                memo.borrow_mut().insert(key(term), result.clone());
                Ok(result)
            },
        )
        .ok()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn cases() -> Vec<OldConditionTerm> {
        let a = OldConditionTerm::Variable(Variable(992100));
        let b = OldConditionTerm::Variable(Variable(992101));
        let leaves = [
            OldConditionTerm::Constant(false),
            OldConditionTerm::Constant(true),
            a,
            b,
        ];
        let mut cases = leaves.to_vec();
        for left in &leaves {
            for right in &leaves {
                cases.push(OldConditionTerm::BoolEqual(
                    Box::new(left.clone()),
                    Box::new(right.clone()),
                ));
                for guard in &leaves {
                    cases.push(OldConditionTerm::BoolIf {
                        condition: Box::new(guard.clone()),
                        then_condition: Box::new(left.clone()),
                        else_condition: Box::new(right.clone()),
                    });
                }
            }
        }
        cases.push(OldConditionTerm::BoolIf {
            condition: Box::new(cases[12].clone()),
            then_condition: Box::new(cases[29].clone()),
            else_condition: Box::new(cases[41].clone()),
        });
        cases
    }

    #[test]
    fn retained_boolean_values_preserve_native_substitution_and_active_scope() {
        let _session = VerificationSession::enter();
        let from = Variable(992100);
        for replacement in [
            OldMachineTerm::bool_cast(MachineIntegerType::UInt8, OldConditionTerm::Constant(false)),
            OldMachineTerm::bool_cast(MachineIntegerType::UInt8, OldConditionTerm::Constant(true)),
            OldMachineTerm::bool_cast(
                MachineIntegerType::UInt8,
                OldConditionTerm::Variable(Variable(992102)),
            ),
        ] {
            let program =
                BTreeMap::from([(from, TypedProgramValueReplacement::Bitvector(replacement))]);
            let integer = BTreeMap::new();
            let algebraic = BTreeMap::new();
            for input in cases() {
                for scoped in [false, true] {
                    let root = KernelTermImport::for_exact_field_inputs().condition(&input);
                    let mut baseline =
                        TermRewrite::for_typed_variables(&program, &integer, &algebraic);
                    let mut rewrite =
                        TermRewrite::for_typed_variables(&program, &integer, &algebraic);
                    let native_scope = scoped
                        .then(|| baseline.push_program_substitution_scope(from, Variable(992103)));
                    let root_scope = scoped
                        .then(|| rewrite.push_program_substitution_scope(from, Variable(992103)));
                    let expected = baseline.condition(&input);
                    let exports = KernelTermExport::machine_export_count();
                    let actual = rewrite
                        .shared_boolean_operand(&root)
                        .expect("supported Boolean value");
                    assert_eq!(KernelTermExport::machine_export_count(), exports);
                    assert!(!root.has_cached_native_argument());
                    assert!(!actual.has_cached_native_argument());
                    assert_eq!(rewrite.refusal_status(), baseline.refusal_status());
                    assert_eq!(rewrite.changed, baseline.changed);
                    // Compatibility reads deliberately follow the retention assertions.
                    let actual = KernelTermExport::condition(&actual).unwrap();
                    assert_eq!(actual, expected, "input={input:?}, scoped={scoped}");
                    assert_eq!(format!("{actual:?}"), format!("{expected:?}"));
                    if let Some(scope) = root_scope {
                        rewrite.pop_program_substitution_scope(scope);
                    }
                    if let Some(scope) = native_scope {
                        baseline.pop_program_substitution_scope(scope);
                    }
                }
            }
        }
    }

    #[test]
    fn retained_boolean_exact_integer_mode_keeps_raw_connectives() {
        let _session = VerificationSession::enter();
        let from = IntegerTerm::Variable(Variable(992110)).into();
        let to = IntegerTerm::constant_i64(9).into();
        for input in cases() {
            let root = KernelTermImport::for_exact_field_inputs().condition(&input);
            let mut baseline = TermRewrite::for_integer_exact(&from, &to);
            let expected = baseline.condition(&input);
            let mut rewrite = TermRewrite::for_integer_exact(&from, &to);
            let exports = KernelTermExport::machine_export_count();
            let actual = rewrite.shared_boolean_operand(&root).unwrap();
            assert_eq!(actual.id(), root.id());
            assert!(!actual.has_cached_native_argument());
            assert_eq!(KernelTermExport::machine_export_count(), exports);
            assert_eq!(rewrite.refusal_status(), baseline.refusal_status());
            assert_eq!(KernelTermExport::condition(&actual).unwrap(), expected);
        }
    }

    #[test]
    fn retained_boolean_checked_collection_preserves_work_refusal() {
        let _session = VerificationSession::enter();
        let mut input = OldConditionTerm::Variable(Variable(992130));
        for index in 0..32 {
            input = OldConditionTerm::BoolEqual(
                Box::new(input),
                Box::new(OldConditionTerm::Variable(Variable(992131 + index))),
            );
        }
        let root = KernelTermImport::for_exact_field_inputs().condition(&input);
        let from = IntegerTerm::Variable(Variable(992170)).into();
        let to = IntegerTerm::constant_i64(9).into();
        let native_refusal = crate::instrumentation::with_run_work_limit(4, || {
            let mut rewrite = TermRewrite::for_integer_exact(&from, &to);
            rewrite.condition(&input);
            rewrite.refusal()
        });
        let (result, refusal, visits) = crate::instrumentation::with_run_work_limit(4, || {
            let mut rewrite = TermRewrite::for_integer_exact(&from, &to);
            let result = rewrite.shared_boolean_operand(&root);
            (result, rewrite.refusal(), rewrite.visits)
        });
        assert!(result.is_none());
        assert_eq!(refusal, Some(RewriteRefusal::WorkExhausted));
        assert_eq!(refusal, native_refusal);
        assert_eq!(
            visits, 0,
            "exhausted source collection must stop before rewriting"
        );
        assert!(!root.has_cached_native_argument());
    }

    #[test]
    fn retained_boolean_atom_collection_is_replayed_on_cached_reads() {
        let _session = VerificationSession::enter();
        let input = OldConditionTerm::Variable(Variable(992180));
        let root = KernelTermImport::default().condition(&input);
        let mut baseline = TermRewrite::empty();
        baseline.collected_conditions = Some(Vec::new());
        let mut rewrite = TermRewrite::empty();
        rewrite.collected_conditions = Some(Vec::new());
        for _ in 0..2 {
            baseline.condition(&input);
            rewrite.shared_boolean_operand(&root).unwrap();
        }
        assert_eq!(rewrite.collected_conditions, baseline.collected_conditions);
        assert_eq!(rewrite.collected_conditions.as_ref().unwrap().len(), 2);
        assert!(!root.has_cached_native_argument());
    }

    #[test]
    fn retained_boolean_nonadmission_preserves_lookup_and_leaf_boundaries() {
        let _session = VerificationSession::enter();
        let from = OldConditionTerm::Variable(Variable(992120));
        let to = OldConditionTerm::Constant(true);
        let input = OldConditionTerm::BoolEqual(Box::new(from.clone()), Box::new(from.clone()));
        let root = KernelTermImport::for_exact_field_inputs().condition(&input);
        let mut exact = TermRewrite::for_condition_exact(&input, &to);
        assert!(exact.shared_boolean_operand(&root).is_none());
        assert!(exact.refusal_status().is_none());
        let cited = HashMap::from([(input.clone(), true)]);
        let mut facts = TermRewrite::for_conditions(&cited);
        assert!(facts.shared_boolean_operand(&root).is_none());
        assert!(facts.refusal_status().is_none());
        // Atomic exact lookup still goes through the native selected leaf.
        let atom = KernelTermImport::default().condition(&from);
        let mut exact = TermRewrite::for_condition_exact(&from, &to);
        let output = exact.shared_boolean_operand(&atom).unwrap();
        assert!(matches!(output.node(), KernelTermNode::BoolLiteral(true)));
        assert!(exact.refusal_status().is_none());
        // Truth-word replacement preserves the native produced scalar value;
        // it is not recursively substituted or folded as an ordinary input.
        let integer = BTreeMap::new();
        let algebraic = BTreeMap::new();
        for replacement in [
            OldMachineTerm::constant(0),
            OldMachineTerm::constant(1),
            OldMachineTerm::Variable(Variable(992121)),
        ] {
            let program = BTreeMap::from([(
                Variable(992120),
                TypedProgramValueReplacement::Bitvector(replacement),
            )]);
            let mut baseline = TermRewrite::for_typed_variables(&program, &integer, &algebraic);
            let expected = baseline.condition(&from);
            assert!(
                !matches!(
                    expected,
                    OldConditionTerm::Constant(_) | OldConditionTerm::Variable(_)
                ),
                "the non-UInt8 truth-word path requires scalar/compound leaf support"
            );
            let mut rewrite = TermRewrite::for_typed_variables(&program, &integer, &algebraic);
            let exports = KernelTermExport::machine_export_count();
            let actual = rewrite.shared_boolean_operand(&atom).unwrap();
            assert_eq!(rewrite.refusal_status(), baseline.refusal_status());
            assert_eq!(KernelTermExport::machine_export_count(), exports);
            assert!(!atom.has_cached_native_argument());
            assert_eq!(KernelTermExport::condition(&actual).unwrap(), expected);
            let expected_root = KernelTermImport::for_exact_field_inputs().condition(&expected);
            assert_eq!(
                actual.condition_storage_key(),
                expected_root.condition_storage_key()
            );
        }
        let read = KernelTermImport::default().condition(&OldConditionTerm::boolean_cell_read(
            ProgramPoint::at(&intern_memory(SymbolicMemory::new())),
            Address::symbolic(Variable(992122)),
        ));
        let mut rewrite = TermRewrite::empty();
        assert_eq!(rewrite.shared_boolean_operand(&read), Some(read.clone()));
        assert!(rewrite.refusal_status().is_none());
        assert!(!root.has_cached_native_argument());
        assert!(!read.has_cached_native_argument());
    }
}

#[cfg(test)]
mod scaling_tests {
    include!("../../../scaling_tests/kernel/proof/term_rewrite/retained_boolean.rs");
}
