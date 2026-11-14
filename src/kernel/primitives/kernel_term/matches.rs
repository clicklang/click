//! Prepared typed match and constructor payloads. Arm bindings scope only the
//! corresponding body; the scrutinee is outside every arm. No constructor
//! selection or schema checking happens at this representation boundary.
use super::*;

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct KernelMatchArm {
    pub(crate) variant: String,
    pub(crate) bindings: Vec<KernelTerm>,
    pub(crate) binding_names: BindingNames,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct KernelMatch {
    pub(crate) result_type: KernelType,
    /// Scrutinee followed by arm bodies, in arm order. Declarations live
    /// in their arm scopes and are not ordinary expression children.
    pub(crate) arguments: Vec<KernelTerm>,
    pub(crate) arms: Vec<KernelMatchArm>,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct KernelConstructor {
    pub(crate) algebraic_type: AlgebraicType,
    pub(crate) variant: String,
    pub(crate) fields: Vec<KernelTerm>,
}

fn import_value(import: &mut KernelTermImport, value: &AlgebraicValue) -> KernelTerm {
    match value {
        AlgebraicValue::Program(value) => {
            import.argument(&PureFunctionArgument::Value(value.clone()))
        }
        AlgebraicValue::Integer(value) => import.integer(&value.clone().into()),
        AlgebraicValue::Algebraic(value) => {
            import.argument(&PureFunctionArgument::Algebraic(value.clone()))
        }
    }
}

fn export_value(
    export: &mut KernelTermExport,
    value: &KernelTerm,
) -> Result<AlgebraicValue, &'static str> {
    match export.argument(value)? {
        PureFunctionArgument::Value(value) => Ok(AlgebraicValue::Program(value)),
        PureFunctionArgument::Integer(value) => Ok(AlgebraicValue::Integer(value.as_ref().clone())),
        PureFunctionArgument::Algebraic(value) => Ok(AlgebraicValue::Algebraic(value)),
        _ => Err("unsupported match field carrier"),
    }
}

impl KernelMatchArm {
    pub(crate) fn import(
        import: &mut KernelTermImport,
        variant: &str,
        bindings: &[AlgebraicValue],
        body: KernelTerm,
        binding_names: &BindingNames,
    ) -> (Self, KernelTerm) {
        (
            Self {
                variant: variant.into(),
                bindings: bindings
                    .iter()
                    .map(|value| import_value(import, value))
                    .collect(),
                binding_names: binding_names.clone(),
            },
            body,
        )
    }
    pub(crate) fn export_bindings(
        &self,
        export: &mut KernelTermExport,
    ) -> Result<Vec<AlgebraicValue>, &'static str> {
        self.bindings
            .iter()
            .map(|value| {
                // A word variable declaration has no expression tree to
                // export. Reify its existing typed descriptor directly.
                if let (KernelType::Program(ty), KernelTermNode::Variable(variable)) =
                    (value.ty(), value.node())
                    && let Some(format) = MachineIntegerType::from_c_type(*ty)
                {
                    crate::instrumentation::record_deterministic_work(1);
                    return Ok(AlgebraicValue::Program(machine::wrap_exact(
                        format,
                        MachineTerm::Variable(*variable),
                    )));
                }
                export_value(export, value)
            })
            .collect()
    }
}

impl KernelMatch {
    pub(crate) fn into_term(self) -> KernelTerm {
        KernelTerm::intern(self.result_type.clone(), KernelTermNode::Match(self))
    }

    pub(crate) fn new(
        result_type: KernelType,
        scrutinee: KernelTerm,
        arms: Vec<(KernelMatchArm, KernelTerm)>,
    ) -> Result<Self, &'static str> {
        crate::instrumentation::record_deterministic_work(arms.len() + 1);
        if !matches!(scrutinee.ty(), KernelType::Algebraic(_)) {
            return Err("match scrutinee is not algebraic");
        }
        if arms.iter().any(|(_, body)| body.ty() != &result_type) {
            return Err("match arm result type differs");
        }
        let mut arguments = Vec::with_capacity(arms.len() + 1);
        arguments.push(scrutinee);
        let arms = arms
            .into_iter()
            .map(|(arm, body)| {
                arguments.push(body);
                arm
            })
            .collect();
        Ok(Self {
            result_type,
            arguments,
            arms,
        })
    }
    pub(crate) fn import_integer(
        import: &mut KernelTermImport,
        value: &IntegerTerm,
    ) -> Option<Self> {
        let IntegerTerm::AlgebraicMatch { scrutinee, arms } = value else {
            return None;
        };
        let scrutinee = import.argument(&PureFunctionArgument::Algebraic((**scrutinee).clone()));
        let arms = arms
            .iter()
            .map(|arm| {
                let body = import.integer(&arm.body);
                KernelMatchArm::import(
                    import,
                    &arm.variant,
                    &arm.bindings,
                    body,
                    &arm.binding_names,
                )
            })
            .collect();
        Some(Self::new(KernelType::Integer, scrutinee, arms).expect("native Integer match types"))
    }
    pub(crate) fn import_machine(
        import: &mut KernelTermImport,
        format: MachineIntegerType,
        value: &MachineTerm,
    ) -> Option<Self> {
        let MachineTerm::AlgebraicMatch { scrutinee, arms } = value else {
            return None;
        };
        let scrutinee = import.argument(&PureFunctionArgument::Algebraic((**scrutinee).clone()));
        let arms = arms
            .iter()
            .map(|arm| {
                // Arithmetic carriers retain unsupported syntax as opaque
                // leaves, just as they do outside a match arm.
                let body = KernelTerm::retained_machine_operand(
                    format,
                    MachineOperandView::Legacy(&arm.body),
                );
                KernelMatchArm::import(
                    import,
                    &arm.variant,
                    &arm.bindings,
                    body,
                    &arm.binding_names,
                )
            })
            .collect();
        Some(
            Self::new(KernelType::Program(format.c_type()), scrutinee, arms)
                .expect("native machine match types"),
        )
    }
    pub(crate) fn import_algebraic(
        import: &mut KernelTermImport,
        value: &AlgebraicTerm,
    ) -> Option<Self> {
        let AlgebraicTermNode::Match { scrutinee, arms } = &value.node else {
            return None;
        };
        let scrutinee = import.argument(&PureFunctionArgument::Algebraic((**scrutinee).clone()));
        let arms = arms
            .iter()
            .map(|arm| {
                let body = import.argument(&PureFunctionArgument::Algebraic(arm.body.clone()));
                KernelMatchArm::import(
                    import,
                    &arm.variant,
                    &arm.bindings,
                    body,
                    &arm.binding_names,
                )
            })
            .collect();
        Some(
            Self::new(
                KernelType::Algebraic(value.algebraic_type.clone()),
                scrutinee,
                arms,
            )
            .expect("native algebraic match types"),
        )
    }
    fn export_scrutinee(
        &self,
        export: &mut KernelTermExport,
    ) -> Result<Box<AlgebraicTerm>, &'static str> {
        match export.argument(&self.arguments[0])? {
            PureFunctionArgument::Algebraic(value) => Ok(Box::new(value)),
            _ => Err("expected algebraic scrutinee"),
        }
    }
    pub(crate) fn export_integer(
        &self,
        export: &mut KernelTermExport,
    ) -> Result<IntegerTerm, &'static str> {
        if self.result_type != KernelType::Integer {
            return Err("expected Integer match");
        }
        Ok(IntegerTerm::AlgebraicMatch {
            scrutinee: self.export_scrutinee(export)?,
            arms: self
                .arms
                .iter()
                .zip(&self.arguments[1..])
                .map(|(arm, body)| {
                    Ok(AlgebraicIntegerMatchArm {
                        variant: arm.variant.clone(),
                        bindings: arm.export_bindings(export)?,
                        body: export.integer(body)?,
                        binding_names: arm.binding_names.clone(),
                    })
                })
                .collect::<Result<_, &'static str>>()?,
        })
    }
    pub(crate) fn export_machine(
        &self,
        export: &mut KernelTermExport,
    ) -> Result<MachineTerm, &'static str> {
        let KernelType::Program(ty) = self.result_type else {
            return Err("expected machine match");
        };
        if MachineIntegerType::from_c_type(ty).is_none() {
            return Err("expected machine integer match");
        }
        Ok(MachineTerm::AlgebraicMatch {
            scrutinee: self.export_scrutinee(export)?,
            arms: self
                .arms
                .iter()
                .zip(&self.arguments[1..])
                .map(|(arm, body)| {
                    Ok(AlgebraicBitvectorMatchArm {
                        variant: arm.variant.clone(),
                        bindings: arm.export_bindings(export)?,
                        body: KernelTermExport::machine(body)?,
                        binding_names: arm.binding_names.clone(),
                    })
                })
                .collect::<Result<_, &'static str>>()?,
        })
    }
}

impl KernelConstructor {
    pub(crate) fn import(import: &mut KernelTermImport, value: &AlgebraicTerm) -> Option<Self> {
        let AlgebraicTermNode::Constructor { variant, fields } = &value.node else {
            return None;
        };
        Some(Self {
            algebraic_type: value.algebraic_type.clone(),
            variant: variant.clone(),
            fields: fields
                .iter()
                .map(|field| import_value(import, field))
                .collect(),
        })
    }
    pub(crate) fn export(
        &self,
        export: &mut KernelTermExport,
    ) -> Result<AlgebraicTerm, &'static str> {
        Ok(AlgebraicTerm {
            algebraic_type: self.algebraic_type.clone(),
            node: AlgebraicTermNode::Constructor {
                variant: self.variant.clone(),
                fields: self
                    .fields
                    .iter()
                    .map(|field| export_value(export, field))
                    .collect::<Result<_, _>>()?,
            },
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn datatype() -> AlgebraicType {
        let key = AlgebraicValueType::Algebraic {
            name: "Box".into(),
            arguments: vec![],
        };
        let variants: Arc<[AlgebraicVariantType]> = vec![AlgebraicVariantType {
            name: "Box".into(),
            fields: vec![AlgebraicValueType::Integer],
        }]
        .into();
        AlgebraicType {
            rigid: false,
            name: "Box".into(),
            arguments: vec![],
            variants: variants.clone(),
            schemas: Arc::new(AlgebraicSchemas::new(std::collections::BTreeMap::from([(
                key, variants,
            )]))),
        }
    }
    pub(super) fn scrutinee() -> AlgebraicTerm {
        AlgebraicTerm {
            algebraic_type: datatype(),
            node: AlgebraicTermNode::Variable(Variable(1)),
        }
    }
    fn binding() -> Vec<AlgebraicValue> {
        vec![AlgebraicValue::Integer(IntegerTerm::Variable(Variable(2)))]
    }
    fn names() -> BindingNames {
        BindingNames::written(&["field".into()])
    }
    #[test]
    fn numeric_match_roots_preserve_observation_identity_and_typed_arms() {
        let _session = crate::kernel::VerificationSession::enter();
        let native = MachineTerm::AlgebraicMatch {
            scrutinee: Box::new(scrutinee()),
            arms: vec![AlgebraicBitvectorMatchArm {
                variant: "Box".into(),
                bindings: binding(),
                binding_names: names(),
                body: MachineTerm::add(
                    MachineTerm::Variable(Variable(991981)),
                    MachineTerm::constant(1),
                ),
            }],
        };
        for format in [MachineIntegerType::Int32, MachineIntegerType::UInt64] {
            let a = KernelTermImport::default().machine(format, &native);
            let b = KernelTermImport::default().machine(format, &native);
            assert!(matches!(a.node(), KernelTermNode::Match(_)));
            let exports = KernelTermExport::machine_export_count();
            let observed = SharedMachineIntegerTerm::observe_shared(format, a.clone()).unwrap();
            assert_eq!(
                observed,
                SharedMachineIntegerTerm::observe_shared(format, b.clone()).unwrap()
            );
            assert_eq!(
                observed,
                SharedMachineIntegerTerm::intern(format, native.clone())
            );
            assert!(crate::kernel::shared_machine_syntax_equal(&a, &b));
            let other = if format == MachineIntegerType::Int32 {
                MachineIntegerType::UInt64
            } else {
                MachineIntegerType::Int32
            };
            let reread = a.with_machine_observation_type(other);
            assert_eq!(
                SharedMachineIntegerTerm::observe_shared(other, reread).unwrap(),
                SharedMachineIntegerTerm::intern(other, native.clone())
            );
            assert_eq!(KernelTermExport::machine_export_count(), exports);
            assert_eq!(KernelTermExport::machine(&a).unwrap(), native);
        }
    }

    #[test]
    fn numeric_match_arms_retain_boolean_casts_in_arithmetic_storage() {
        let _session = crate::kernel::VerificationSession::enter();
        for format in [MachineIntegerType::Int32, MachineIntegerType::UInt64] {
            let cast = MachineTerm::BoolCast {
                to: format,
                value: Box::new(ConditionTerm::Variable(Variable(991982))),
            };
            for body in [
                cast.clone(),
                MachineTerm::add(cast, MachineTerm::constant(1)),
            ] {
                let native = MachineTerm::AlgebraicMatch {
                    scrutinee: Box::new(scrutinee()),
                    arms: vec![AlgebraicBitvectorMatchArm {
                        variant: "Box".into(),
                        bindings: binding(),
                        binding_names: names(),
                        body,
                    }],
                };
                let root = KernelTermImport::default().machine(format, &native);
                let observed = SharedMachineIntegerTerm::observe_shared(format, root.clone())
                    .expect("opaque arm leaves fit arithmetic storage");
                assert_eq!(
                    observed,
                    SharedMachineIntegerTerm::intern(format, native.clone())
                );
                assert_eq!(KernelTermExport::machine(&root).unwrap(), native);
            }
        }
    }

    #[test]
    fn numeric_match_imports_share_opaque_body_observation_identity() {
        let _session = crate::kernel::VerificationSession::enter();
        let native = MachineTerm::AlgebraicMatch {
            scrutinee: Box::new(scrutinee()),
            arms: vec![AlgebraicBitvectorMatchArm {
                variant: "Box".into(),
                bindings: binding(),
                binding_names: names(),
                body: MachineTerm::ClickFunctionApplication {
                    name: "opaque_body".into(),
                    arguments: vec![],
                },
            }],
        };
        let format = MachineIntegerType::Int32;
        let root = KernelTermImport::default().machine(format, &native);
        let exports = KernelTermExport::machine_export_count();
        let observed = SharedMachineIntegerTerm::observe_shared(format, root).unwrap();
        // Exercise a cold arithmetic import before `intern` records an alias.
        let imported = SharedMachineIntegerTerm::import_arithmetic(format, &native).unwrap();
        assert_eq!(observed, imported);
        assert_eq!(observed, SharedMachineIntegerTerm::intern(format, native));
        assert_eq!(KernelTermExport::machine_export_count(), exports);
    }

    #[test]
    fn match_payload_round_trips_each_result_family_and_binding_names() {
        let mut import = KernelTermImport::default();
        let mut export = KernelTermExport::default();
        let integer = IntegerTerm::AlgebraicMatch {
            scrutinee: Box::new(scrutinee()),
            arms: vec![AlgebraicIntegerMatchArm {
                variant: "Box".into(),
                bindings: binding(),
                body: IntegerTerm::Variable(Variable(2)).into(),
                binding_names: names(),
            }],
        };
        let common = KernelMatch::import_integer(&mut import, &integer).unwrap();
        assert_eq!(common.arms[0].bindings[0].ty(), &KernelType::Integer);
        assert_eq!(common.arms[0].binding_names.get(0), Some("field"));
        assert_eq!(common.export_integer(&mut export).unwrap(), integer);
        assert!(common.export_machine(&mut export).is_err());
        for format in [MachineIntegerType::Int32, MachineIntegerType::UInt64] {
            let native = MachineTerm::AlgebraicMatch {
                scrutinee: Box::new(scrutinee()),
                arms: vec![AlgebraicBitvectorMatchArm {
                    variant: "Box".into(),
                    bindings: binding(),
                    body: MachineTerm::constant(7),
                    binding_names: names(),
                }],
            };
            let common = KernelMatch::import_machine(&mut import, format, &native).unwrap();
            assert_eq!(
                common.arguments[1].ty(),
                &KernelType::Program(format.c_type())
            );
            assert_eq!(common.export_machine(&mut export).unwrap(), native);
        }
        let native = AlgebraicTerm {
            algebraic_type: datatype(),
            node: AlgebraicTermNode::Match {
                scrutinee: Box::new(scrutinee()),
                arms: vec![AlgebraicResultMatchArm {
                    variant: "Box".into(),
                    bindings: binding(),
                    body: scrutinee(),
                    binding_names: names(),
                }],
            },
        };
        let common = KernelMatch::import_algebraic(&mut import, &native).unwrap();
        assert_eq!(export.algebraic(&common.into_term()).unwrap(), native);
    }
    #[test]
    fn match_payload_preserves_arm_order_and_rejects_mixed_result_sorts() {
        let scrutinee =
            KernelTermImport::default().argument(&PureFunctionArgument::Algebraic(scrutinee()));
        let arm = |name: &str, ty| {
            (
                KernelMatchArm {
                    variant: name.into(),
                    bindings: vec![],
                    binding_names: Default::default(),
                },
                KernelTerm::variable(ty, Variable(if name == "second" { 4 } else { 5 })),
            )
        };
        let arms = vec![
            arm("second", KernelType::Integer),
            arm("first", KernelType::Integer),
        ];
        let common = KernelMatch::new(KernelType::Integer, scrutinee.clone(), arms).unwrap();
        assert_eq!(
            common
                .arms
                .iter()
                .map(|arm| arm.variant.as_str())
                .collect::<Vec<_>>(),
            ["second", "first"]
        );
        assert_eq!(common.arguments.len(), common.arms.len() + 1);
        assert_eq!(
            common.arguments[1],
            KernelTerm::variable(KernelType::Integer, Variable(4))
        );
        assert_eq!(
            common.arguments[2],
            KernelTerm::variable(KernelType::Integer, Variable(5))
        );
        assert!(
            KernelMatch::new(
                KernelType::Integer,
                scrutinee,
                vec![arm("Box", KernelType::Program(ProgramType::Int32))]
            )
            .is_err()
        );
        assert!(
            KernelMatch::new(
                KernelType::Integer,
                KernelTerm::integer_literal(0.into()),
                vec![]
            )
            .is_err()
        );
    }
    #[test]
    fn constructor_payload_retains_common_numeric_fields() {
        let field = IntegerTerm::Add(
            IntegerTerm::Variable(Variable(3)).into(),
            IntegerTerm::Constant(1.into()).into(),
        );
        let native = AlgebraicTerm {
            algebraic_type: datatype(),
            node: AlgebraicTermNode::Constructor {
                variant: "Box".into(),
                fields: vec![AlgebraicValue::Integer(field)],
            },
        };
        let common = KernelConstructor::import(&mut KernelTermImport::default(), &native).unwrap();
        assert!(matches!(
            common.fields[0].node(),
            KernelTermNode::IntegerOperation { .. }
        ));
        assert_eq!(
            common.export(&mut KernelTermExport::default()).unwrap(),
            native
        );
    }
}

#[cfg(test)]
mod scaling_tests {
    include!("../../../scaling_tests/kernel/primitives/kernel_term/matches.rs");
}

impl KernelTermImport {
    /// Temporary native field-descriptor boundary for scoped match consumers.
    pub(crate) fn match_field(&mut self, value: &AlgebraicValue) -> KernelTerm {
        import_value(self, value)
    }
}

#[cfg(test)]
impl KernelMatch {
    pub(crate) fn test_scrutinee(fields: Vec<AlgebraicValueType>) -> AlgebraicTerm {
        let key = AlgebraicValueType::Algebraic {
            name: "MatchScope".into(),
            arguments: vec![],
        };
        let variants: Arc<[AlgebraicVariantType]> = vec![AlgebraicVariantType {
            name: "Arm".into(),
            fields,
        }]
        .into();
        AlgebraicTerm {
            algebraic_type: AlgebraicType {
                rigid: false,
                name: "MatchScope".into(),
                arguments: vec![],
                variants: variants.clone(),
                schemas: Arc::new(AlgebraicSchemas::new(std::collections::BTreeMap::from([(
                    key, variants,
                )]))),
            },
            node: AlgebraicTermNode::Variable(Variable(991900)),
        }
    }
}
