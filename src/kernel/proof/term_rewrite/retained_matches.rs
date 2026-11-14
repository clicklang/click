//! Scoped rewrites of prepared match payloads. Constructor selection is a
//! separate checking step; this walk preserves arm order and body scopes.
use super::*;

impl TermRewrite<'_> {
    pub(crate) fn retained_match(
        &mut self,
        matched: &KernelMatch,
    ) -> Result<KernelMatch, RewriteRefusal> {
        let result = self.retained_match_in(matched);
        self.refusal_observed.set(true);
        result
    }

    pub(super) fn retained_match_in(
        &mut self,
        matched: &KernelMatch,
    ) -> Result<KernelMatch, RewriteRefusal> {
        let result = self.rewrite_retained_match_scopes(matched);
        if let Some(refusal) = self.refusal_status() {
            return Err(refusal);
        }
        result.ok_or(RewriteRefusal::UnsupportedScope)
    }

    fn reserve_retained_match_variables(&mut self, matched: &KernelMatch) -> Option<()> {
        self.ensure_replacement_carriers();
        if self.source_variables_reserved {
            return Some(());
        }
        let mut variables = self.new_carrier_variables();
        let mut seen = BTreeSet::new();
        let mut common_seen = BTreeSet::new();
        for child in matched
            .arguments
            .iter()
            .chain(matched.arms.iter().flat_map(|arm| &arm.bindings))
        {
            if !common_seen.insert(child.id()) {
                continue;
            }
            if let KernelType::C(ty) = child.ty()
                && MachineIntegerType::from_c_type(*ty).is_some()
            {
                collect_machine_operand_carriers(MachineOperandView::Shared(child), &mut variables);
            } else {
                // Integer reads retain common operands through the memoized
                // compatibility bridge; algebraic descriptors migrate in 6m.
                let argument = self.fold_integer_bridge.argument(child).ok()?;
                collect_argument_carriers(&argument, &mut variables, &mut seen);
            }
            if variables.exhausted() {
                break;
            }
        }
        self.reserve_source_variables(variables);
        (!self.checked_work_exhausted()).then_some(())
    }

    fn rewrite_retained_match_child(&mut self, child: &KernelTerm) -> Option<KernelTerm> {
        if let KernelType::C(ty) = child.ty()
            && MachineIntegerType::from_c_type(*ty).is_some()
        {
            return self.shared_machine_operand(child);
        }
        let argument = self.fold_integer_bridge.argument(child).ok()?;
        let rewritten = self.argument(&argument);
        if self.refusal_status().is_some() {
            return None;
        }
        // Variable descriptors have no field payload to transport. Other
        // algebraic values may carry pointer evidence that value equality
        // deliberately ignores, so retain the rewritten payload in that case.
        if let (PureFunctionArgument::Algebraic(before), PureFunctionArgument::Algebraic(after)) =
            (&argument, &rewritten)
            && matches!((&before.node, &after.node), (AlgebraicTermNode::Variable(a), AlgebraicTermNode::Variable(b)) if a == b)
            && before.algebraic_type == after.algebraic_type
        {
            return Some(child.clone());
        }
        Some(KernelTermImport::default().argument(&rewritten))
    }

    fn rewrite_retained_match_scopes(&mut self, matched: &KernelMatch) -> Option<KernelMatch> {
        self.reserve_retained_match_variables(matched)?;
        let scrutinee = self.rewrite_retained_match_child(&matched.arguments[0])?;
        let mut arms = Vec::with_capacity(matched.arms.len());
        let mut import = KernelTermImport::default();
        for (arm, body) in matched.arms.iter().zip(&matched.arguments[1..]) {
            let saved_scope_id = self.scope_id;
            let saved_shadowed = self.integer_shadowed;
            let mut changes = Vec::new();
            let result = (|| {
                let original = arm.export_bindings(&mut self.fold_integer_bridge).ok()?;
                let mut bindings = original.clone();
                if !self.rewrite_match_bindings(&mut bindings, &mut changes) {
                    return None;
                }
                let body = if self.conditions.is_some() {
                    body.clone()
                } else {
                    self.rewrite_retained_match_child(body)?
                };
                let mut retained = arm.clone();
                for ((child, before), after) in
                    retained.bindings.iter_mut().zip(&original).zip(&bindings)
                {
                    if before != after {
                        *child = import.match_field(after);
                    }
                }
                Some((retained, body))
            })();
            self.restore_scope(&changes, saved_scope_id, saved_shadowed);
            arms.push(result?);
            if self.checked_work_exhausted() {
                return None;
            }
        }
        KernelMatch::new(matched.result_type.clone(), scrutinee, arms).ok()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn common_match_rewrite_preserves_integer_capture_and_machine_scopes() {
        let native = IntegerTerm::AlgebraicMatch {
            scrutinee: Box::new(KernelMatch::test_scrutinee(vec![
                AlgebraicValueType::Integer,
            ])),
            arms: vec![AlgebraicIntegerMatchArm {
                variant: "Arm".into(),
                binding_names: Default::default(),
                bindings: vec![AlgebraicValue::Integer(IntegerTerm::Variable(Variable(2)))],
                body: IntegerTerm::Add(
                    IntegerTerm::Variable(Variable(1)).into(),
                    IntegerTerm::Variable(Variable(2)).into(),
                )
                .into(),
            }],
        };
        let common =
            KernelMatch::import_integer(&mut KernelTermImport::default(), &native).unwrap();
        let replacement = IntegerTerm::Variable(Variable(2));
        let renamings = BTreeMap::new();
        let mut old =
            TermRewrite::for_integer_variables(Variable(1), &replacement, false, &renamings);
        let expected = old.integer(&native);
        assert_eq!(old.refusal(), None);
        let mut new =
            TermRewrite::for_integer_variables(Variable(1), &replacement, false, &renamings);
        let actual = new.retained_match(&common).unwrap();
        assert_eq!(
            actual
                .export_integer(&mut KernelTermExport::default())
                .unwrap(),
            expected
        );
        assert!(new.scope.integer.is_empty());
        assert!(!new.integer_shadowed);

        let native = MachineTerm::AlgebraicMatch {
            scrutinee: Box::new(KernelMatch::test_scrutinee(vec![AlgebraicValueType::C(
                CType::Int32,
            )])),
            arms: vec![AlgebraicBitvectorMatchArm {
                variant: "Arm".into(),
                binding_names: Default::default(),
                bindings: vec![AlgebraicValue::C(CValue::Int32(MachineTerm::Variable(
                    Variable(2),
                )))],
                body: MachineTerm::Binary {
                    format: MachineIntegerType::Int32,
                    op: MachineBinaryOp::Add,
                    left: Box::new(MachineTerm::Variable(Variable(1))),
                    right: Box::new(MachineTerm::Variable(Variable(2))),
                },
            }],
        };
        let common = KernelMatch::import_machine(
            &mut KernelTermImport::default(),
            MachineIntegerType::Int32,
            &native,
        )
        .unwrap();
        for target in [Variable(1), Variable(2)] {
            let source = MachineTerm::Variable(target);
            let replacement = MachineTerm::Variable(Variable(2));
            let mut old = TermRewrite::for_bits(&source, &replacement);
            let expected = old.bits(&native);
            assert_eq!(old.refusal(), None);
            let mut new = TermRewrite::for_bits(&source, &replacement);
            let exports = KernelTermExport::machine_export_count();
            let actual = new.retained_match(&common).unwrap();
            assert_eq!(KernelTermExport::machine_export_count(), exports);
            assert_eq!(
                actual
                    .export_machine(&mut KernelTermExport::default())
                    .unwrap(),
                expected
            );
            assert!(new.scope.c.is_empty());
        }
    }

    #[test]
    fn common_match_pointer_transport_preserves_snapshots_and_avoids_capture() {
        let _session = VerificationSession::enter();
        let memory = intern_c_memory(CMemory::new());
        let source = Variable(3);
        let bound = Variable(2);
        let read = |variable| {
            MachineTerm::MemoryLoad(
                memory.clone(),
                Box::new(Pointer::symbolic(variable)),
                LoadKind::Int32,
            )
        };
        let native = MachineTerm::AlgebraicMatch {
            scrutinee: Box::new(KernelMatch::test_scrutinee(vec![AlgebraicValueType::C(
                CType::Int32Pointer,
            )])),
            arms: vec![AlgebraicBitvectorMatchArm {
                variant: "Arm".into(),
                binding_names: Default::default(),
                bindings: vec![AlgebraicValue::C(CValue::typed_pointer(
                    Pointer::symbolic(bound),
                    CType::Int32Pointer,
                ))],
                body: MachineTerm::Binary {
                    format: MachineIntegerType::Int32,
                    op: MachineBinaryOp::Add,
                    left: Box::new(read(source)),
                    right: Box::new(read(bound)),
                },
            }],
        };
        let common = KernelMatch::import_machine(
            &mut KernelTermImport::default(),
            MachineIntegerType::Int32,
            &native,
        )
        .unwrap();
        let replacement = Pointer::symbolic(bound);
        let mut old = TermRewrite::for_pointer_variable(source, &replacement);
        let expected = old.bits(&native);
        assert_eq!(old.refusal(), None);
        let mut new = TermRewrite::for_pointer_variable(source, &replacement);
        let actual = new.retained_match(&common).unwrap();
        assert_eq!(
            actual
                .export_machine(&mut KernelTermExport::default())
                .unwrap(),
            expected
        );
        assert!(new.scope.c.is_empty());
    }

    #[test]
    fn retained_algebraic_match_keeps_rewritten_pointer_evidence() {
        use crate::kernel::effective_type::{CAccessClass, CStructClass};
        let class = CAccessClass::Struct(CStructClass::opaque("RetainedPointer"));
        let original =
            CValue::typed_pointer(Pointer::symbolic(Variable(991940)), CType::Int32Pointer);
        let replacement = original
            .clone()
            .with_pointer_object_class(Some(class.clone()));
        assert_eq!(
            original, replacement,
            "value equality intentionally omits pointer evidence"
        );
        let key = AlgebraicValueType::Algebraic {
            name: "PointerBox".into(),
            arguments: vec![],
        };
        let variants: std::sync::Arc<[AlgebraicVariantType]> = vec![AlgebraicVariantType {
            name: "Box".into(),
            fields: vec![AlgebraicValueType::C(CType::Int32Pointer)],
        }]
        .into();
        let ty = AlgebraicType {
            rigid: false,
            name: "PointerBox".into(),
            arguments: vec![],
            variants: variants.clone(),
            schemas: std::sync::Arc::new(AlgebraicSchemas::new(BTreeMap::from([(key, variants)]))),
        };
        let native = AlgebraicTerm {
            algebraic_type: ty.clone(),
            node: AlgebraicTermNode::Match {
                scrutinee: Box::new(KernelMatch::test_scrutinee(vec![])),
                arms: vec![AlgebraicResultMatchArm {
                    variant: "Arm".into(),
                    binding_names: Default::default(),
                    bindings: vec![],
                    body: AlgebraicTerm {
                        algebraic_type: ty,
                        node: AlgebraicTermNode::Constructor {
                            variant: "Box".into(),
                            fields: vec![AlgebraicValue::C(original.clone())],
                        },
                    },
                }],
            },
        };
        let common =
            KernelMatch::import_algebraic(&mut KernelTermImport::default(), &native).unwrap();
        let (CValue::Pointer(from), CValue::Pointer(to)) = (&original, &replacement) else {
            unreachable!()
        };
        let mut rewrite = TermRewrite::for_pointer_value_exact(from, to);
        let result = rewrite
            .retained_match(&common)
            .unwrap()
            .export_algebraic(&mut KernelTermExport::default())
            .unwrap();
        let AlgebraicTermNode::Match { arms, .. } = result.node else {
            unreachable!()
        };
        let AlgebraicTermNode::Constructor { fields, .. } = &arms[0].body.node else {
            unreachable!()
        };
        let AlgebraicValue::C(CValue::Pointer(pointer)) = &fields[0] else {
            unreachable!()
        };
        assert!(pointer.supports_object_class(&class));
    }

    #[test]
    fn common_match_refusal_restores_scope_and_keeps_the_native_refusal() {
        let source = MachineTerm::Binary {
            format: MachineIntegerType::Int32,
            op: MachineBinaryOp::Add,
            left: Box::new(MachineTerm::Variable(Variable(1))),
            right: Box::new(MachineTerm::Variable(Variable(2))),
        };
        let native = MachineTerm::AlgebraicMatch {
            scrutinee: Box::new(KernelMatch::test_scrutinee(vec![AlgebraicValueType::C(
                CType::Int32,
            )])),
            arms: vec![AlgebraicBitvectorMatchArm {
                variant: "Arm".into(),
                binding_names: Default::default(),
                bindings: vec![AlgebraicValue::C(CValue::Int32(MachineTerm::Variable(
                    Variable(2),
                )))],
                body: source.clone(),
            }],
        };
        let common = KernelMatch::import_machine(
            &mut KernelTermImport::default(),
            MachineIntegerType::Int32,
            &native,
        )
        .unwrap();
        let replacement = MachineTerm::constant(7);
        let mut old = TermRewrite::for_bits(&source, &replacement);
        let _ = old.bits(&native);
        let expected = old
            .refusal()
            .expect("composite source under a C binder refuses");
        let mut new = TermRewrite::for_bits(&source, &replacement);
        assert_eq!(new.retained_match(&common), Err(expected));
        assert!(new.scope.c.is_empty());
    }
}

#[cfg(test)]
mod scaling_tests {
    include!("../../../scaling_tests/kernel/proof/term_rewrite/retained_matches.rs");
}
