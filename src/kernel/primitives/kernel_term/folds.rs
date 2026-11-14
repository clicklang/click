//! Typed fold payloads with common expression children.
//! Bounds and initial value are outside the two binders; only the body is in
//! their scope. Construction reads no facts and performs no fold reduction.
use super::*;

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub(crate) enum KernelFoldIndex {
    Int32,
    UInt64,
    Integer,
}

impl KernelFoldIndex {
    pub(crate) fn ty(self) -> KernelType {
        match self {
            Self::Int32 => KernelType::C(MachineIntegerType::Int32.c_type()),
            Self::UInt64 => KernelType::C(MachineIntegerType::UInt64.c_type()),
            Self::Integer => KernelType::Integer,
        }
    }
}

/// A shallow payload: expression children are common handles, not native
/// expression trees. Exact binder identities remain distinct from alpha keys.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct KernelFold {
    pub(crate) index: KernelFoldIndex,
    pub(crate) accumulator: Variable,
    pub(crate) item: Variable,
    /// Start, end, initial value, body, in that order.
    pub(crate) arguments: [KernelTerm; 4],
}

impl KernelFold {
    pub(crate) fn new(
        index: KernelFoldIndex,
        accumulator: Variable,
        item: Variable,
        arguments: [KernelTerm; 4],
    ) -> Result<Self, &'static str> {
        crate::instrumentation::record_deterministic_work(1);
        if arguments[0].ty() != &index.ty() || arguments[1].ty() != &index.ty() {
            return Err("fold bounds have the wrong index type");
        }
        if arguments[2].ty() != arguments[3].ty() {
            return Err("fold initial value and body have different types");
        }
        if arguments[2].ty() != &KernelType::Integer
            && !(index == KernelFoldIndex::Int32
                && arguments[2].ty() == &KernelType::C(CType::Int32))
        {
            return Err("unsupported fold result type");
        }
        Ok(Self {
            index,
            accumulator,
            item,
            arguments,
        })
    }

    /// Existing machine fold evaluation, used only by checking. Construction
    /// and lowering keep a symbolic fold unchanged.
    pub(crate) fn simplify_machine(&self) -> Option<KernelTerm> {
        use crate::kernel::proof::term_rewrite::TermRewrite;
        let [start, end, initial, body] = &self.arguments;
        if crate::kernel::shared_machine_syntax_equal(start, end) {
            return Some(initial.clone());
        }
        let constant = |root| {
            MachineOperandView::Shared(root)
                .literal()?
                .as_const()
                .map(|bits| i64::from(bits as i32))
        };
        let (Some(start), Some(end)) = (constant(start), constant(end)) else {
            return Some(self.clone().into_term());
        };
        let mut value = initial.clone();
        for index in start..end {
            crate::instrumentation::record_deterministic_work(1);
            let source = MachineTerm::Variable(self.accumulator);
            let mut rewrite =
                TermRewrite::for_machine_operand(&source, MachineOperandView::Shared(&value));
            let step = rewrite.shared_machine_operand(body);
            let refusal = rewrite.refusal();
            drop(rewrite);
            let step = step.filter(|_| refusal.is_none())?;
            let source = MachineTerm::Variable(self.item);
            let item = MachineTerm::constant(index as u32);
            let mut rewrite = TermRewrite::for_bits(&source, &item);
            let result = rewrite.shared_machine_operand(&step);
            let refusal = rewrite.refusal();
            let result = result.filter(|_| refusal.is_none())?;
            let retained =
                SharedMachineIntegerTerm::from_shared(MachineIntegerType::Int32, result)?;
            value = crate::kernel::memory_provenance::map_shared_pointer_index(
                &retained,
                |leaf| Some(leaf.clone()),
                crate::kernel::proof::equality_rewrite::rebuild_normalized_machine_node,
            )?
            .shared_operand()?
            .clone();
        }
        Some(value)
    }

    pub(crate) fn into_term(self) -> KernelTerm {
        KernelTerm::intern(self.result_type().clone(), KernelTermNode::Fold(self))
    }

    pub(crate) fn result_type(&self) -> &KernelType {
        self.arguments[2].ty()
    }

    fn import_endpoint(
        _import: &mut KernelTermImport,
        format: MachineIntegerType,
        endpoint: &SharedIntegerRangeEndpoint,
    ) -> KernelTerm {
        match endpoint.machine_operand().shared_operand() {
            Some(root) => root.with_machine_observation_type(format),
            // A range endpoint already owns a numeric observation identity.
            // Reimporting an opaque call must not mint a new producer identity.
            None => KernelTerm::machine_observation_leaf(
                format,
                endpoint.value().clone(),
                endpoint.machine_operand().clone(),
            ),
        }
    }

    pub(crate) fn import_integer(
        import: &mut KernelTermImport,
        source: &IntegerTerm,
    ) -> Option<Self> {
        let IntegerTerm::RangeFold {
            index,
            initial,
            accumulator,
            item,
            body,
        } = source
        else {
            return None;
        };
        let (index, start, end) = match index {
            IntegerRangeFoldIndex::Int32 { start, end } => (
                KernelFoldIndex::Int32,
                Self::import_endpoint(import, MachineIntegerType::Int32, start),
                Self::import_endpoint(import, MachineIntegerType::Int32, end),
            ),
            IntegerRangeFoldIndex::UInt64 { start, end } => (
                KernelFoldIndex::UInt64,
                Self::import_endpoint(import, MachineIntegerType::UInt64, start),
                Self::import_endpoint(import, MachineIntegerType::UInt64, end),
            ),
            IntegerRangeFoldIndex::Integer { start, end } => (
                KernelFoldIndex::Integer,
                import.integer(start),
                import.integer(end),
            ),
        };
        Some(
            Self::new(
                index,
                *accumulator,
                *item,
                [start, end, import.integer(initial), import.integer(body)],
            )
            .expect("native Integer fold types"),
        )
    }

    pub(crate) fn import_machine(
        _import: &mut KernelTermImport,
        source: &MachineTerm,
    ) -> Option<Self> {
        let MachineTerm::RangeFold {
            start,
            end,
            initial,
            accumulator,
            item,
            body,
        } = source
        else {
            return None;
        };
        let read = |term| {
            KernelTerm::retained_machine_operand(
                MachineIntegerType::Int32,
                MachineOperandView::Legacy(term),
            )
        };
        Some(
            Self::new(
                KernelFoldIndex::Int32,
                *accumulator,
                *item,
                [read(start), read(end), read(initial), read(body)],
            )
            .expect("native machine fold types"),
        )
    }

    /// Explicit compatibility boundary for the remaining Integer consumers.
    /// Machine endpoints retain common operands instead of exporting prefixes.
    pub(crate) fn integer_compatibility(
        &self,
        export: &mut KernelTermExport,
    ) -> Result<IntegerTerm, &'static str> {
        if self.result_type() != &KernelType::Integer {
            return Err("expected Integer fold result");
        }
        let [start, end, initial, body] = &self.arguments;
        let index = match self.index {
            KernelFoldIndex::Int32 | KernelFoldIndex::UInt64 => {
                let start = SharedIntegerRangeEndpoint::from_shared(start.clone())
                    .ok_or("unsupported shared fold endpoint")?;
                let end = SharedIntegerRangeEndpoint::from_shared(end.clone())
                    .ok_or("unsupported shared fold endpoint")?;
                if self.index == KernelFoldIndex::Int32 {
                    IntegerRangeFoldIndex::Int32 { start, end }
                } else {
                    IntegerRangeFoldIndex::UInt64 { start, end }
                }
            }
            KernelFoldIndex::Integer => IntegerRangeFoldIndex::Integer {
                start: export.integer(start)?,
                end: export.integer(end)?,
            },
        };
        Ok(IntegerTerm::RangeFold {
            index,
            initial: export.integer(initial)?,
            accumulator: self.accumulator,
            item: self.item,
            body: export.integer(body)?,
        })
    }

    pub(crate) fn export_integer(
        &self,
        export: &mut KernelTermExport,
    ) -> Result<IntegerTerm, &'static str> {
        if self.result_type() != &KernelType::Integer {
            return Err("expected Integer fold result");
        }
        let [start, end, initial, body] = &self.arguments;
        let index = match self.index {
            KernelFoldIndex::Int32 | KernelFoldIndex::UInt64 => {
                let start = SharedIntegerRangeEndpoint::intern(KernelTermExport::machine(start)?);
                let end = SharedIntegerRangeEndpoint::intern(KernelTermExport::machine(end)?);
                if self.index == KernelFoldIndex::Int32 {
                    IntegerRangeFoldIndex::Int32 { start, end }
                } else {
                    IntegerRangeFoldIndex::UInt64 { start, end }
                }
            }
            KernelFoldIndex::Integer => IntegerRangeFoldIndex::Integer {
                start: export.integer(start)?,
                end: export.integer(end)?,
            },
        };
        Ok(IntegerTerm::RangeFold {
            index,
            initial: export.integer(initial)?,
            accumulator: self.accumulator,
            item: self.item,
            body: export.integer(body)?,
        })
    }

    pub(crate) fn export_machine(&self) -> Result<MachineTerm, &'static str> {
        if self.result_type() != &KernelType::C(CType::Int32) {
            return Err("expected int32 fold result");
        }
        let [start, end, initial, body] = &self.arguments;
        Ok(MachineTerm::RangeFold {
            start: Box::new(KernelTermExport::machine(start)?),
            end: Box::new(KernelTermExport::machine(end)?),
            initial: Box::new(KernelTermExport::machine(initial)?),
            accumulator: self.accumulator,
            item: self.item,
            body: Box::new(KernelTermExport::machine(body)?),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fold_payload_roundtrips_preserve_ranges_binders_and_unreduced_bodies() {
        let start = SharedIntegerRangeEndpoint::intern(MachineTerm::Variable(Variable(10)));
        let end = SharedIntegerRangeEndpoint::intern(MachineTerm::constant(0));
        let indices = [
            IntegerRangeFoldIndex::Int32 {
                start: start.clone(),
                end: end.clone(),
            },
            IntegerRangeFoldIndex::UInt64 { start, end },
            IntegerRangeFoldIndex::Integer {
                start: IntegerTerm::Variable(Variable(10)).into(),
                end: IntegerTerm::constant_i64(-3).into(),
            },
        ];
        for index in indices {
            let native = IntegerTerm::RangeFold {
                index,
                initial: IntegerTerm::constant_i64(7).into(),
                accumulator: Variable(11),
                item: Variable(12),
                body: IntegerTerm::Add(
                    IntegerTerm::Variable(Variable(11)).into(),
                    IntegerTerm::constant_i64(0).into(),
                )
                .into(),
            };
            let common =
                KernelFold::import_integer(&mut KernelTermImport::default(), &native).unwrap();
            assert_eq!(
                common
                    .export_integer(&mut KernelTermExport::default())
                    .unwrap(),
                native
            );
            assert_eq!(common.result_type(), &KernelType::Integer);
            assert!(common.export_machine().is_err());
            let mut changed = common.clone();
            changed.item = Variable(13);
            assert_ne!(common, changed);
        }
        let native = MachineTerm::RangeFold {
            start: Box::new(MachineTerm::constant(9)),
            end: Box::new(MachineTerm::constant(2)),
            initial: Box::new(MachineTerm::constant(7)),
            accumulator: Variable(11),
            item: Variable(12),
            body: Box::new(MachineTerm::Variable(Variable(11))),
        };
        let common = KernelFold::import_machine(&mut KernelTermImport::default(), &native).unwrap();
        assert_eq!(common.export_machine().unwrap(), native);
        assert!(
            common
                .export_integer(&mut KernelTermExport::default())
                .is_err()
        );
    }

    #[test]
    fn fold_payload_rejects_mixed_bounds_results_and_unsupported_machine_sorts() {
        let int = KernelTerm::variable(KernelType::Integer, Variable(1));
        let machine = KernelTerm::variable(KernelType::C(CType::Int32), Variable(2));
        let wide = KernelTerm::variable(KernelType::C(CType::UInt64), Variable(3));
        for (index, args) in [
            (
                KernelFoldIndex::Integer,
                [int.clone(), machine.clone(), int.clone(), int.clone()],
            ),
            (
                KernelFoldIndex::Int32,
                [
                    machine.clone(),
                    machine.clone(),
                    machine.clone(),
                    int.clone(),
                ],
            ),
            (
                KernelFoldIndex::UInt64,
                [wide.clone(), wide.clone(), wide.clone(), wide],
            ),
        ] {
            assert!(KernelFold::new(index, Variable(4), Variable(5), args).is_err());
        }
    }
}

#[cfg(test)]
mod scaling_tests {
    include!("../../../scaling_tests/kernel/primitives/kernel_term/folds.rs");
}

#[cfg(test)]
mod producer_tests {
    use super::*;

    #[test]
    fn fold_syntax_order_preserves_native_conditional_bodies() {
        let _session = crate::kernel::VerificationSession::enter();
        let make = |guard, branch| MachineTerm::RangeFold {
            start: Box::new(MachineTerm::constant(0)),
            end: Box::new(MachineTerm::Variable(Variable(991131))),
            initial: Box::new(MachineTerm::constant(0)),
            accumulator: Variable(991132),
            item: Variable(991133),
            body: Box::new(MachineTerm::If {
                condition: Box::new(ConditionTerm::Variable(Variable(guard))),
                then_term: Box::new(MachineTerm::Variable(Variable(branch))),
                else_term: Box::new(MachineTerm::Variable(Variable(991132))),
            }),
        };
        let first = make(991134, 991135);
        for second in [first.clone(), make(991136, 991135), make(991134, 991137)] {
            let root = KernelTermImport::default().machine(MachineIntegerType::Int32, &first);
            let other = KernelTermImport::default().machine(MachineIntegerType::Int32, &second);
            let before = KernelTermExport::machine_export_count();
            for (a, b) in [
                (
                    MachineOperandView::Shared(&root),
                    MachineOperandView::Legacy(&second),
                ),
                (
                    MachineOperandView::Shared(&root),
                    MachineOperandView::Shared(&other),
                ),
            ] {
                assert_eq!(
                    crate::kernel::machine_operand_syntax_cmp(a, b),
                    first.cmp(&second)
                );
            }
            assert_eq!(KernelTermExport::machine_export_count(), before);
        }
    }

    #[test]
    fn shared_machine_fold_pointer_index_substitution_avoids_capture() {
        let _session = crate::kernel::VerificationSession::enter();
        let free = Variable(991121);
        let acc = Variable(991122);
        let native = MachineTerm::RangeFold {
            start: Box::new(MachineTerm::constant(0)),
            end: Box::new(MachineTerm::Variable(free)),
            initial: Box::new(MachineTerm::Variable(acc)),
            accumulator: acc,
            item: Variable(991123),
            body: Box::new(MachineTerm::add(
                MachineTerm::Variable(free),
                MachineTerm::Variable(acc),
            )),
        };
        let replacement = MachineTerm::Variable(acc);
        let expected =
            crate::kernel::reasoning::substitute_bitvector_variable(&native, free, &replacement);
        let root = KernelTermImport::default().machine(MachineIntegerType::Int32, &native);
        let offset = PointerOffsetTerm::Int32Scaled {
            value: SharedMachineIntegerTerm::from_shared(MachineIntegerType::Int32, root).unwrap(),
            byte_width: 4,
        };
        let before = KernelTermExport::machine_export_count();
        let result = crate::kernel::reasoning::substitute_bitvector_variable_in_pointer_offset(
            &offset,
            free,
            &replacement,
        );
        assert_eq!(KernelTermExport::machine_export_count(), before);
        let PointerOffsetTerm::Int32Scaled { value, .. } = result else {
            panic!("fold index")
        };
        let actual = KernelTermExport::machine(value.shared_operand().unwrap()).unwrap();
        assert_eq!(
            crate::kernel::proof::fact_keys::bitvector_folds_alpha_equivalent(&actual, &expected),
            Some(true)
        );
    }

    #[test]
    fn common_machine_fold_checking_preserves_concrete_evaluation() {
        let _session = crate::kernel::VerificationSession::enter();
        let accumulator = Variable(991101);
        let item = Variable(991102);
        let body = MachineTerm::add(
            MachineTerm::Variable(accumulator),
            MachineTerm::Variable(item),
        );
        for (start, end) in [(0, 0), (0, 1), (0, 4), (4, 0)] {
            let native = MachineTerm::RangeFold {
                start: Box::new(MachineTerm::constant(start)),
                end: Box::new(MachineTerm::constant(end)),
                initial: Box::new(MachineTerm::constant(7)),
                accumulator,
                item,
                body: Box::new(body.clone()),
            };
            let fold =
                KernelFold::import_machine(&mut KernelTermImport::default(), &native).unwrap();
            let before = KernelTermExport::machine_export_count();
            let result = fold.simplify_machine().unwrap();
            assert_eq!(KernelTermExport::machine_export_count(), before);
            let expected = MachineTerm::range_fold(
                MachineTerm::constant(start),
                MachineTerm::constant(end),
                MachineTerm::constant(7),
                accumulator,
                item,
                body.clone(),
            );
            assert_eq!(KernelTermExport::machine(&result).unwrap(), expected);
        }
    }

    #[test]
    fn machine_fold_observations_keep_opaque_endpoint_identity() {
        let _session = crate::kernel::VerificationSession::enter();
        let native = MachineTerm::RangeFold {
            start: Box::new(MachineTerm::constant(0)),
            end: Box::new(MachineTerm::PureFunctionApplication {
                name: "fold_end".into(),
                arguments: vec![MachineTerm::Variable(Variable(991111))],
            }),
            initial: Box::new(MachineTerm::constant(0)),
            accumulator: Variable(991112),
            item: Variable(991113),
            body: Box::new(MachineTerm::Variable(Variable(991112))),
        };
        let first = KernelTermImport::default().machine(MachineIntegerType::Int32, &native);
        let second = KernelTermImport::default().machine(MachineIntegerType::Int32, &native);
        let before = KernelTermExport::machine_export_count();
        let observe = |root| {
            SharedMachineIntegerTerm::observe_shared(MachineIntegerType::Int32, root).unwrap()
        };
        assert_eq!(observe(first.clone()), observe(second.clone()));
        assert!(crate::kernel::shared_machine_syntax_equal(&first, &second));
        assert_eq!(KernelTermExport::machine_export_count(), before);
    }

    #[test]
    fn integer_fold_producer_retains_common_children_and_scoped_identity() {
        let _session = crate::kernel::VerificationSession::enter();
        let acc = Variable(970001);
        let item = Variable(970002);
        let free = Variable(970003);
        let body = IntegerTerm::Add(
            IntegerTerm::Variable(acc).into(),
            IntegerTerm::Variable(free).into(),
        );
        let body_shared: SharedIntegerTerm = body.clone().into();
        let body_root = KernelTermImport::default().integer(&body_shared);
        let value = IntegerTerm::range_fold(
            IntegerRangeFoldIndex::Integer {
                start: IntegerTerm::constant_i64(0).into(),
                end: IntegerTerm::Variable(Variable(970004)).into(),
            },
            IntegerTerm::Variable(acc),
            acc,
            item,
            body,
        );
        let root = KernelTermImport::default().integer(&value.clone().into());
        let KernelTermNode::Fold(fold) = root.node() else {
            panic!("Integer fold kept as legacy payload")
        };
        assert_eq!(fold.arguments[3], body_root);
        assert_eq!(
            KernelTermExport::default().integer(&root).unwrap().as_ref(),
            &value
        );
        let mut variables = std::collections::BTreeSet::new();
        crate::kernel::reasoning::collect_integer_free_variables(&value, &mut variables);
        assert!(
            variables.contains(&acc),
            "initial value is outside body binders"
        );
        assert!(variables.contains(&free));
        assert!(!variables.contains(&item));
    }
    #[test]
    fn opaque_integer_fold_endpoints_keep_their_existing_observation_identity() {
        let _session = crate::kernel::VerificationSession::enter();
        let call = MachineTerm::PureFunctionApplication {
            name: "opaque_fold_bound".into(),
            arguments: vec![MachineTerm::Variable(Variable(990001))],
        };
        let endpoint = SharedIntegerRangeEndpoint::intern(call.clone());
        assert!(endpoint.machine_operand().shared_operand().is_none());
        let produce = |end| {
            IntegerTerm::range_fold(
                IntegerRangeFoldIndex::UInt64 {
                    start: SharedIntegerRangeEndpoint::intern(MachineTerm::constant(0)),
                    end,
                },
                IntegerTerm::constant_i64(0),
                Variable(990002),
                Variable(990003),
                IntegerTerm::Variable(Variable(990002)),
            )
        };
        let first = produce(endpoint);
        let second = produce(SharedIntegerRangeEndpoint::intern(call));
        let first_root = KernelTermImport::default().integer(&first.into());
        let second_root = KernelTermImport::default().integer(&second.into());
        assert_eq!(first_root, second_root);
        let changed = produce(SharedIntegerRangeEndpoint::intern(
            MachineTerm::PureFunctionApplication {
                name: "opaque_fold_bound".into(),
                arguments: vec![MachineTerm::Variable(Variable(990004))],
            },
        ));
        assert_ne!(
            first_root,
            KernelTermImport::default().integer(&changed.into())
        );
    }
}
