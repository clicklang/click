//! Logical Bool operands of machine conversions. Import/export preserves the
//! written comparison format, even when fact equality identifies formats.
use super::*;

/// Borrow a Boolean root or an exact native compatibility payload. Inspecting
/// this view never exports children, consults facts, or selects a branch.
#[derive(Clone, Copy)]
pub(crate) enum BooleanOperandView<'a> {
    Shared(&'a KernelTerm),
    Native(&'a ConditionTerm),
}

impl<'a> BooleanOperandView<'a> {
    /// Visit dependency-bearing Boolean leaves, sharing a common connective
    /// once. Call arguments and native opaque leaves keep the reader's rules.
    pub(crate) fn for_each_dependency_leaf(self, mut visit: impl FnMut(Self)) {
        let mut pending = vec![self];
        let mut seen = std::collections::HashSet::new();
        while let Some(view) = pending.pop() {
            if let Self::Shared(root) = view
                && !seen.insert(root.id())
            {
                continue;
            }
            crate::instrumentation::record_deterministic_work(1);
            if let Some(children) = view.conditional() {
                pending.extend(children.into_iter().rev());
            } else if let Some(children) = view.equality() {
                pending.extend(children.into_iter().rev());
            } else {
                visit(view);
            }
        }
    }

    pub(crate) fn native_leaf(self) -> Option<&'a ConditionTerm> {
        match self {
            Self::Native(value) => Some(value),
            Self::Shared(root) => {
                let KernelTermNode::LegacyBool(payload) = root.node() else {
                    return None;
                };
                let PureFunctionArgument::Value(ProgramValue::Bool(MachineTerm::BoolCast {
                    value,
                    ..
                })) = payload.value()
                else {
                    return None;
                };
                Some(value)
            }
        }
    }

    /// Explicit compatibility boundary for callers that still need a native
    /// condition. Borrow existing leaves; only common compound roots export.
    pub(crate) fn native(self) -> std::borrow::Cow<'a, ConditionTerm> {
        if let Some(value) = self.native_leaf() {
            return std::borrow::Cow::Borrowed(value);
        }
        let Self::Shared(root) = self else {
            unreachable!()
        };
        std::borrow::Cow::Owned(KernelTermExport::condition(root).expect("Boolean operand"))
    }

    pub(crate) fn constant(self) -> Option<bool> {
        match self {
            Self::Shared(root) if matches!(root.node(), KernelTermNode::BoolLiteral(_)) => {
                let KernelTermNode::BoolLiteral(value) = root.node() else {
                    unreachable!()
                };
                Some(*value)
            }
            _ => match self.native_leaf()? {
                ConditionTerm::Constant(value) => Some(*value),
                _ => None,
            },
        }
    }

    pub(crate) fn conditional(self) -> Option<[Self; 3]> {
        match self {
            Self::Shared(root) => match root.node() {
                KernelTermNode::BoolIf { arguments } => {
                    Some(arguments.each_ref().map(Self::Shared))
                }
                _ => Self::Native(self.native_leaf()?).conditional(),
            },
            Self::Native(ConditionTerm::BoolIf {
                condition,
                then_condition,
                else_condition,
            }) => Some([
                Self::Native(condition),
                Self::Native(then_condition),
                Self::Native(else_condition),
            ]),
            _ => None,
        }
    }

    pub(crate) fn equality(self) -> Option<[Self; 2]> {
        match self {
            Self::Shared(root) => match root.node() {
                KernelTermNode::BoolEqual { arguments } => {
                    Some(arguments.each_ref().map(Self::Shared))
                }
                _ => Self::Native(self.native_leaf()?).equality(),
            },
            Self::Native(ConditionTerm::BoolEqual(left, right)) => {
                Some([Self::Native(left), Self::Native(right)])
            }
            _ => None,
        }
    }

    pub(crate) fn comparison(
        self,
    ) -> Option<(
        MachineIntegerType,
        CompareRelation,
        [MachineOperandView<'a>; 2],
    )> {
        match self {
            Self::Shared(root) => match root.node() {
                KernelTermNode::BoolCompare {
                    format,
                    relation,
                    arguments,
                } => Some((
                    *format,
                    *relation,
                    arguments.each_ref().map(MachineOperandView::Shared),
                )),
                _ => Self::Native(self.native_leaf()?).comparison(),
            },
            Self::Native(ConditionTerm::Compare {
                format,
                relation,
                left,
                right,
            }) => Some((
                *format,
                *relation,
                [
                    MachineOperandView::Legacy(left),
                    MachineOperandView::Legacy(right),
                ],
            )),
            _ => None,
        }
    }
}

impl KernelTermImport {
    pub(crate) fn condition(&mut self, condition: &ConditionTerm) -> KernelTerm {
        use ConditionTerm as Old;
        use KernelTermNode as Node;
        crate::instrumentation::record_deterministic_work(1);
        let node = match condition {
            Old::Constant(value) => Node::BoolLiteral(*value),
            Old::Variable(variable) => Node::Variable(*variable),
            Old::Compare {
                format,
                relation,
                left,
                right,
            } => Node::BoolCompare {
                format: *format,
                relation: *relation,
                arguments: [self.machine(*format, left), self.machine(*format, right)],
            },
            Old::IntegerLessThan(left, right)
            | Old::IntegerLessEqual(left, right)
            | Old::IntegerGreaterThan(left, right)
            | Old::IntegerGreaterEqual(left, right)
            | Old::IntegerEqual(left, right)
            | Old::IntegerNotEqual(left, right) => {
                use IntegerComparisonOperator as Op;
                let operator = match condition {
                    Old::IntegerLessThan(..) => Op::LessThan,
                    Old::IntegerLessEqual(..) => Op::LessEqual,
                    Old::IntegerGreaterThan(..) => Op::GreaterThan,
                    Old::IntegerGreaterEqual(..) => Op::GreaterEqual,
                    Old::IntegerEqual(..) => Op::Equal,
                    Old::IntegerNotEqual(..) => Op::NotEqual,
                    _ => unreachable!(),
                };
                Node::IntegerCompare {
                    operator,
                    arguments: [self.integer(left), self.integer(right)],
                }
            }
            Old::BoolEqual(left, right) => Node::BoolEqual {
                arguments: [self.condition(left), self.condition(right)],
            },
            Old::BoolIf {
                condition,
                then_condition,
                else_condition,
            } => Node::BoolIf {
                arguments: [
                    self.condition(condition),
                    self.condition(then_condition),
                    self.condition(else_condition),
                ],
            },
            Old::BoolApplication(application) => Node::Call {
                name: application.name().into(),
                arguments: application
                    .arguments()
                    .iter()
                    .enumerate()
                    .map(|(index, arg)| match arg {
                        PureFunctionArgument::Integer(_) => self.argument(arg),
                        PureFunctionArgument::Value(integer_c_value!(_))
                        | PureFunctionArgument::SharedMachine(_) => self.argument(arg),
                        _ => KernelTerm::legacy_at(
                            arg.clone(),
                            LegacyIdentity::ApplicationArgument(application.clone(), index),
                        ),
                    })
                    .collect(),
            },
            _ => {
                // Keep the entire condition, including pointer metadata. Do not
                // key this payload by ConditionTerm's semantic equality.
                let leaf = KernelTerm::legacy(PureFunctionArgument::Value(ProgramValue::Bool(
                    MachineTerm::BoolCast {
                        to: MachineIntegerType::UInt8,
                        value: Box::new(condition.clone()),
                    },
                )));
                let Node::Legacy(payload) = leaf.node() else {
                    unreachable!()
                };
                Node::LegacyBool(payload.clone())
            }
        };
        KernelTerm::intern(KernelType::Bool, node)
    }
}

impl KernelTermExport {
    pub(crate) fn condition(term: &KernelTerm) -> Result<ConditionTerm, &'static str> {
        use ConditionTerm as Old;
        use KernelTermNode as Node;
        if term.ty() != &KernelType::Bool {
            return Err("expected Bool kernel term");
        }
        crate::instrumentation::record_deterministic_work(1);
        Ok(match term.node() {
            Node::BoolLiteral(value) => Old::Constant(*value),
            Node::Variable(variable) => Old::Variable(*variable),
            Node::BoolCompare {
                format,
                relation,
                arguments,
            } => Old::Compare {
                format: *format,
                relation: *relation,
                left: Box::new(Self::condition_machine_operand(&arguments[0])?),
                right: Box::new(Self::condition_machine_operand(&arguments[1])?),
            },
            Node::IntegerCompare {
                operator,
                arguments,
            } => {
                use IntegerComparisonOperator as Op;
                let mut export = Self::default();
                let left = export.integer(&arguments[0])?;
                let right = export.integer(&arguments[1])?;
                match operator {
                    Op::LessThan => Old::IntegerLessThan(left, right),
                    Op::LessEqual => Old::IntegerLessEqual(left, right),
                    Op::GreaterThan => Old::IntegerGreaterThan(left, right),
                    Op::GreaterEqual => Old::IntegerGreaterEqual(left, right),
                    Op::Equal => Old::IntegerEqual(left, right),
                    Op::NotEqual => Old::IntegerNotEqual(left, right),
                }
            }
            Node::BoolEqual { arguments } => Old::BoolEqual(
                Box::new(Self::condition(&arguments[0])?),
                Box::new(Self::condition(&arguments[1])?),
            ),
            Node::BoolIf { arguments } => Old::BoolIf {
                condition: Box::new(Self::condition(&arguments[0])?),
                then_condition: Box::new(Self::condition(&arguments[1])?),
                else_condition: Box::new(Self::condition(&arguments[2])?),
            },
            Node::Call { name, arguments } => Old::BoolApplication(SharedPureApplication::intern(
                name.clone(),
                arguments
                    .iter()
                    .map(|arg| Self::default().argument(arg))
                    .collect::<Result<Vec<_>, _>>()?,
            )),
            Node::LegacyBool(payload) => {
                let PureFunctionArgument::Value(ProgramValue::Bool(MachineTerm::BoolCast {
                    value,
                    ..
                })) = payload.value()
                else {
                    return Err("expected exact legacy Bool payload");
                };
                *value.clone()
            }
            _ => return Err("expected Bool kernel node"),
        })
    }

    fn condition_machine_operand(term: &KernelTerm) -> Result<MachineTerm, &'static str> {
        // Fixed-size atoms have their exact written form already. Only a
        // compound guard operand needs the remaining Boolean export boundary.
        match term.node() {
            KernelTermNode::Variable(variable) => Ok(MachineTerm::Variable(*variable)),
            KernelTermNode::MachineLiteral(value) => Ok(value.legacy_term()),
            KernelTermNode::MemoryLoad { .. } => {
                Ok(term.machine_read_leaf().expect("read descriptor").clone())
            }
            _ => Self::machine(term),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn boolean_views_keep_written_comparison_and_shared_children() {
        let source = ConditionTerm::BoolIf {
            condition: Box::new(ConditionTerm::Compare {
                format: MachineIntegerType::UInt32,
                relation: CompareRelation::Equal,
                left: Box::new(MachineTerm::Variable(Variable(964_090))),
                right: Box::new(MachineTerm::constant(1)),
            }),
            then_condition: Box::new(ConditionTerm::Constant(true)),
            else_condition: Box::new(ConditionTerm::BoolEqual(
                Box::new(ConditionTerm::Constant(false)),
                Box::new(ConditionTerm::Constant(true)),
            )),
        };
        let common = KernelTermImport::default().condition(&source);
        for view in [
            BooleanOperandView::Native(&source),
            BooleanOperandView::Shared(&common),
        ] {
            let [guard, yes, no] = view.conditional().unwrap();
            let (format, relation, operands) = guard.comparison().unwrap();
            assert_eq!(format, MachineIntegerType::UInt32);
            assert_eq!(relation, CompareRelation::Equal);
            assert_eq!(operands[0].variable(), Some(&Variable(964_090)));
            assert_eq!(yes.constant(), Some(true));
            let [left, right] = no.equality().unwrap();
            assert_eq!(left.constant(), Some(false));
            assert_eq!(right.constant(), Some(true));
            assert_eq!(view.native().as_ref(), &source);
        }
        let [guard, _, _] = BooleanOperandView::Shared(&common).conditional().unwrap();
        assert!(matches!(
            guard.comparison().unwrap().2[0],
            MachineOperandView::Shared(_)
        ));
    }

    #[test]
    fn boolean_view_borrows_exact_legacy_payload() {
        let source = ConditionTerm::PointerEqual(
            Box::new(Pointer::symbolic(Variable(964_091))),
            Box::new(Pointer::symbolic(Variable(964_092))),
        );
        let root = KernelTermImport::default().condition(&source);
        let view = BooleanOperandView::Shared(&root);
        assert!(matches!(view.native(), std::borrow::Cow::Borrowed(_)));
        assert_eq!(view.native_leaf(), Some(&source));
        assert!(view.conditional().is_none());
        assert!(view.comparison().is_none());
    }

    #[test]
    fn integer_comparisons_preserve_all_operators_and_order_after_source_drop() {
        use IntegerComparisonOperator as Op;
        type Constructor = fn(SharedIntegerTerm, SharedIntegerTerm) -> ConditionTerm;
        let constructors: [(Op, Constructor); 6] = [
            (Op::LessThan, ConditionTerm::IntegerLessThan),
            (Op::LessEqual, ConditionTerm::IntegerLessEqual),
            (Op::GreaterThan, ConditionTerm::IntegerGreaterThan),
            (Op::GreaterEqual, ConditionTerm::IntegerGreaterEqual),
            (Op::Equal, ConditionTerm::IntegerEqual),
            (Op::NotEqual, ConditionTerm::IntegerNotEqual),
        ];
        let mut distinct = std::collections::HashSet::new();
        for (operator, constructor) in constructors {
            let left: SharedIntegerTerm = IntegerTerm::Add(
                IntegerTerm::Variable(Variable(964_001)).into(),
                IntegerTerm::constant_i64(1).into(),
            )
            .into();
            let right: SharedIntegerTerm = IntegerTerm::constant_i64(0).into();
            let source = constructor(left, right);
            let term = KernelTermImport::default().condition(&source);
            assert_eq!(term.ty(), &KernelType::Bool);
            assert!(
                matches!(term.node(), KernelTermNode::IntegerCompare { operator: actual, .. } if *actual == operator)
            );
            assert_eq!(term.children().len(), 2);
            assert!(
                term.children()
                    .iter()
                    .all(|child| child.ty() == &KernelType::Integer)
            );
            assert!(matches!(
                term.children()[0].node(),
                KernelTermNode::IntegerOperation { .. }
            ));
            assert!(matches!(
                term.children()[1].node(),
                KernelTermNode::IntegerLiteral(_)
            ));
            assert!(distinct.insert(term.clone()));
            assert_eq!(KernelTermImport::default().condition(&source), term);
            drop(source);
            let restored = KernelTermExport::condition(&term).unwrap();
            // Reconstructed old objects may have new allocation IDs; the
            // common operator and ordered operands must retain their identity.
            assert_eq!(KernelTermImport::default().condition(&restored), term);
        }
    }

    #[test]
    fn boolean_bridge_preserves_structure_and_comparison_format() {
        let comparison = |format| ConditionTerm::Compare {
            format,
            relation: CompareRelation::Equal,
            left: Box::new(MachineTerm::Variable(Variable(961_001))),
            right: Box::new(MachineTerm::constant(0)),
        };
        let signed = comparison(MachineIntegerType::Int32);
        let unsigned = comparison(MachineIntegerType::UInt32);
        // Fact equality deliberately identifies these. Term identity must not.
        assert_eq!(signed, unsigned);
        assert_ne!(
            KernelTermImport::default().condition(&signed),
            KernelTermImport::default().condition(&unsigned)
        );
        for condition in [
            signed,
            unsigned,
            ConditionTerm::Constant(false),
            ConditionTerm::Variable(Variable(961_002)),
            ConditionTerm::BoolEqual(
                Box::new(ConditionTerm::Constant(true)),
                Box::new(ConditionTerm::Constant(true)),
            ),
            ConditionTerm::BoolIf {
                condition: Box::new(ConditionTerm::Constant(false)),
                then_condition: Box::new(ConditionTerm::Constant(true)),
                else_condition: Box::new(ConditionTerm::Constant(false)),
            },
            ConditionTerm::BoolApplication(SharedPureApplication::intern(
                "predicate".into(),
                vec![PureFunctionArgument::Value(ProgramValue::Int32(
                    MachineTerm::Variable(Variable(961_003)),
                ))],
            )),
            ConditionTerm::IntegerEqual(
                IntegerTerm::constant_i64(1).into(),
                IntegerTerm::constant_i64(2).into(),
            ),
        ] {
            for destination in [
                MachineIntegerType::Int8,
                MachineIntegerType::Int32,
                MachineIntegerType::UInt64,
                MachineIntegerType::UInt128,
            ] {
                let source = PureFunctionArgument::Value(super::super::machine::wrap_exact(
                    destination,
                    MachineTerm::BoolCast {
                        to: destination,
                        value: Box::new(condition.clone()),
                    },
                ));
                let term = KernelTermImport::default().argument(&source);
                assert!(matches!(term.node(), KernelTermNode::BoolCast { .. }));
                assert_eq!(term.children()[0].ty(), &KernelType::Bool);
                let restored = KernelTermExport::default().argument(&term).unwrap();
                // Debug retains the comparison format that equality omits.
                assert_eq!(format!("{restored:?}"), format!("{source:?}"));
            }
        }
    }
}
