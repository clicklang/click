//! Logical Bool operands of machine conversions. Import/export preserves the
//! written comparison format, even when fact equality identifies formats.
use super::*;

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
                        PureFunctionArgument::Value(value)
                            if matches!(value, integer_c_value!(_)) =>
                        {
                            self.argument(arg)
                        }
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
                let leaf = KernelTerm::legacy(PureFunctionArgument::Value(CValue::Bool(
                    Bitvector32Term::BoolCast {
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
                left: Box::new(Self::machine(&arguments[0])?),
                right: Box::new(Self::machine(&arguments[1])?),
            },
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
                let PureFunctionArgument::Value(CValue::Bool(Bitvector32Term::BoolCast {
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
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn boolean_bridge_preserves_structure_and_comparison_format() {
        let comparison = |format| ConditionTerm::Compare {
            format,
            relation: CompareRelation::Equal,
            left: Box::new(Bitvector32Term::Variable(Variable(961_001))),
            right: Box::new(Bitvector32Term::Constant(0)),
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
                vec![PureFunctionArgument::Value(CValue::Int32(
                    Bitvector32Term::Variable(Variable(961_003)),
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
                    Bitvector32Term::BoolCast {
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
