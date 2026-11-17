//! Explicit native output for retained algebraic matches. Consume completed
//! children once; caching boxed prefixes would clone every nested match again.
use super::*;

#[cfg(test)]
thread_local! {
    static ALGEBRAIC_EXPORT_COUNT: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

impl KernelTermImport {
    /// Import constructor fields in source order without recursive boxed-prefix
    /// copies. Unmigrated families keep their exact producer-owned payload.
    pub(crate) fn algebraic(&mut self, source: &AlgebraicTerm) -> KernelTerm {
        enum Task<'a> {
            Term(&'a AlgebraicTerm),
            If(&'a AlgebraicType, &'a ConditionTerm),
            Field(&'a AlgebraicValue),
            Argument(&'a PureFunctionArgument),
            Call(&'a AlgebraicType, &'a str, &'a [PureFunctionArgument]),
            Match(&'a AlgebraicType, &'a [AlgebraicResultMatchArm]),
            Finish(&'a AlgebraicType, &'a str, usize),
        }
        let mut pending = vec![Task::Term(source)];
        let mut values = Vec::new();
        while let Some(task) = pending.pop() {
            crate::instrumentation::record_deterministic_work(1);
            match task {
                Task::Term(term) => match &term.node {
                    AlgebraicTermNode::Variable(variable) => values.push(KernelTerm::variable(
                        KernelType::Algebraic(term.algebraic_type.clone()),
                        *variable,
                    )),
                    AlgebraicTermNode::Constructor { variant, fields } => {
                        pending.push(Task::Finish(&term.algebraic_type, variant, fields.len()));
                        pending.extend(fields.iter().rev().map(Task::Field));
                    }
                    AlgebraicTermNode::If {
                        condition,
                        then_term,
                        else_term,
                    } => {
                        pending.push(Task::If(&term.algebraic_type, condition));
                        pending.push(Task::Term(else_term));
                        pending.push(Task::Term(then_term));
                    }
                    AlgebraicTermNode::Match { scrutinee, arms } => {
                        pending.push(Task::Match(&term.algebraic_type, arms));
                        // Arguments precede declarations, matching the prepared
                        // payload and explicit output walker.
                        let mut children = vec![Task::Term(scrutinee)];
                        children.extend(arms.iter().map(|arm| Task::Term(&arm.body)));
                        children.extend(
                            arms.iter()
                                .flat_map(|arm| arm.bindings.iter().map(Task::Field)),
                        );
                        pending.extend(children.into_iter().rev());
                    }
                    AlgebraicTermNode::PureFunctionApplication { name, arguments } => {
                        pending.push(Task::Call(&term.algebraic_type, name, arguments));
                        pending.extend(arguments.iter().rev().map(Task::Argument));
                    }
                    AlgebraicTermNode::MemoryLoad { memory, pointer } => {
                        values.push(KernelTerm::algebraic_read(
                            term.algebraic_type.clone(),
                            ProgramPoint::at(memory),
                            SharedAddress::import(pointer),
                        ))
                    }
                },
                Task::If(ty, condition) => {
                    let else_term = values.pop().expect("else branch");
                    let then_term = values.pop().expect("then branch");
                    values.push(KernelTerm::algebraic_if_raw(
                        ty.clone(),
                        [self.condition(condition), then_term, else_term],
                    ));
                }
                Task::Match(ty, arms) => {
                    let count =
                        arms.len() + 1 + arms.iter().map(|arm| arm.bindings.len()).sum::<usize>();
                    let mut children = values.split_off(values.len() - count).into_iter();
                    let arguments = children.by_ref().take(arms.len() + 1).collect();
                    let arms = arms
                        .iter()
                        .map(|arm| KernelMatchArm {
                            variant: arm.variant.clone(),
                            binding_names: arm.binding_names.clone(),
                            bindings: children.by_ref().take(arm.bindings.len()).collect(),
                        })
                        .collect();
                    values.push(
                        KernelMatch {
                            result_type: KernelType::Algebraic(ty.clone()),
                            arguments,
                            arms,
                        }
                        .into_term(),
                    );
                }
                Task::Argument(PureFunctionArgument::Algebraic(term)) => {
                    pending.push(Task::Term(term))
                }
                Task::Argument(argument) => values.push(self.argument(argument)),
                Task::Call(ty, name, arguments) => {
                    let roots = values.split_off(values.len() - arguments.len());
                    values.push(KernelTerm::algebraic_call(
                        ty.clone(),
                        name.into(),
                        roots
                            .into_iter()
                            .zip(arguments.iter().map(|arg| match arg {
                                PureFunctionArgument::SharedMachine(value) => Some(value.clone()),
                                _ => None,
                            }))
                            .collect(),
                    ));
                }
                Task::Field(AlgebraicValue::Algebraic(term)) => pending.push(Task::Term(term)),
                Task::Field(AlgebraicValue::Integer(value)) => {
                    values.push(self.integer(&value.clone().into()))
                }
                Task::Field(AlgebraicValue::Program(value)) => {
                    values.push(self.argument(&PureFunctionArgument::Value(value.clone())))
                }
                Task::Finish(ty, variant, count) => {
                    let fields = values.split_off(values.len() - count);
                    values.push(
                        KernelConstructor {
                            algebraic_type: ty.clone(),
                            variant: variant.into(),
                            fields,
                        }
                        .into_term(),
                    );
                }
            }
        }
        values.pop().expect("algebraic source")
    }
}

impl KernelTerm {
    /// Explicit selected-value compatibility view for native storage keys and
    /// APIs. Ordinary handoffs keep the common root and do not request it.
    pub(crate) fn algebraic_native_value(&self) -> Option<&ProgramValue> {
        if !matches!(self.ty(), KernelType::Algebraic(_)) {
            return None;
        }
        let PureFunctionArgument::Value(value) = self
            .0
            .argument_leaf
            .get_or_init(|| {
                Box::new(PureFunctionArgument::Value(ProgramValue::Parameter(
                    Box::new(
                        if let (KernelType::Algebraic(ty), KernelTermNode::Variable(variable)) =
                            (self.ty(), self.node())
                        {
                            AlgebraicTerm {
                                algebraic_type: ty.clone(),
                                node: AlgebraicTermNode::Variable(*variable),
                            }
                        } else {
                            KernelTermExport::default()
                                .algebraic(self)
                                .expect("algebraic value output")
                        },
                    ),
                )))
            })
            .as_ref()
        else {
            unreachable!("algebraic value descriptor")
        };
        Some(value)
    }
}

impl KernelTermExport {
    #[cfg(test)]
    pub(crate) fn algebraic_export_count() -> usize {
        ALGEBRAIC_EXPORT_COUNT.with(std::cell::Cell::get)
    }

    pub(crate) fn algebraic(&mut self, term: &KernelTerm) -> Result<AlgebraicTerm, &'static str> {
        #[cfg(test)]
        ALGEBRAIC_EXPORT_COUNT.with(|count| count.set(count.get() + 1));
        enum Task<'a> {
            Enter(&'a KernelTerm),
            If(&'a AlgebraicType, &'a KernelTerm),
            Finish(&'a KernelMatch),
            Constructor(&'a KernelConstructor),
            Call(&'a KernelAlgebraicCall),
            SharedMachine(&'a SharedMachineIntegerTerm),
        }
        fn algebraic(value: PureFunctionArgument) -> Result<AlgebraicTerm, &'static str> {
            match value {
                PureFunctionArgument::Algebraic(value) => Ok(value),
                _ => Err("expected algebraic match operand"),
            }
        }
        let mut pending = vec![Task::Enter(term)];
        let mut values = Vec::new();
        while let Some(task) = pending.pop() {
            crate::instrumentation::record_deterministic_work(1);
            match task {
                Task::Enter(root) => {
                    if let KernelTermNode::Match(matched) = root.node()
                        && matches!(root.ty(), KernelType::Algebraic(_))
                    {
                        pending.push(Task::Finish(matched));
                        pending.extend(
                            matched
                                .arms
                                .iter()
                                .flat_map(|arm| &arm.bindings)
                                .rev()
                                .map(Task::Enter),
                        );
                        pending.extend(matched.arguments.iter().rev().map(Task::Enter));
                    } else if let KernelTermNode::AlgebraicRead(read) = root.node() {
                        let KernelType::Algebraic(ty) = root.ty() else {
                            unreachable!()
                        };
                        let (point, address) = read.parts();
                        values.push(PureFunctionArgument::Algebraic(AlgebraicTerm {
                            algebraic_type: ty.clone(),
                            node: AlgebraicTermNode::MemoryLoad {
                                memory: point.shared_memory().clone(),
                                pointer: Box::new(address.export()?),
                            },
                        }));
                    } else if let KernelTermNode::AlgebraicIf { arguments } = root.node() {
                        let KernelType::Algebraic(ty) = root.ty() else {
                            unreachable!()
                        };
                        pending.push(Task::If(ty, &arguments[0]));
                        pending.extend(arguments[1..].iter().rev().map(Task::Enter));
                    } else if let KernelTermNode::AlgebraicCall(call) = root.node() {
                        pending.push(Task::Call(call));
                        pending.extend(
                            call.arguments
                                .iter()
                                .zip(&call.shared_machine_arguments)
                                .rev()
                                .map(|(arg, shared)| {
                                    if let Some(value) = shared {
                                        Task::SharedMachine(value)
                                    } else {
                                        Task::Enter(arg)
                                    }
                                }),
                        );
                    } else if let KernelTermNode::Constructor(constructor) = root.node() {
                        pending.push(Task::Constructor(constructor));
                        pending.extend(constructor.fields.iter().rev().map(Task::Enter));
                    } else if let (KernelType::Algebraic(ty), KernelTermNode::Variable(variable)) =
                        (root.ty(), root.node())
                    {
                        values.push(PureFunctionArgument::Algebraic(AlgebraicTerm {
                            algebraic_type: ty.clone(),
                            node: AlgebraicTermNode::Variable(*variable),
                        }));
                    } else {
                        values.push(self.argument(root)?);
                    }
                }
                Task::If(ty, condition) => {
                    let else_term = algebraic(values.pop().ok_or("else branch")?)?;
                    let then_term = algebraic(values.pop().ok_or("then branch")?)?;
                    values.push(PureFunctionArgument::Algebraic(AlgebraicTerm {
                        algebraic_type: ty.clone(),
                        node: AlgebraicTermNode::If {
                            condition: Box::new(Self::condition(condition)?),
                            then_term: Box::new(then_term),
                            else_term: Box::new(else_term),
                        },
                    }));
                }
                Task::SharedMachine(value) => {
                    values.push(PureFunctionArgument::SharedMachine(value.clone()));
                }
                Task::Call(call) => {
                    let arguments = values.split_off(
                        values
                            .len()
                            .checked_sub(call.arguments.len())
                            .ok_or("missing call argument")?,
                    );
                    values.push(PureFunctionArgument::Algebraic(AlgebraicTerm {
                        algebraic_type: call.algebraic_type.clone(),
                        node: AlgebraicTermNode::PureFunctionApplication {
                            name: call.name.clone(),
                            arguments,
                        },
                    }));
                }
                Task::Constructor(constructor) => {
                    let fields = values
                        .split_off(
                            values
                                .len()
                                .checked_sub(constructor.fields.len())
                                .ok_or("missing constructor field")?,
                        )
                        .into_iter()
                        .map(|value| match value {
                            PureFunctionArgument::Value(value) => {
                                Ok(AlgebraicValue::Program(value))
                            }
                            PureFunctionArgument::Integer(value) => {
                                Ok(AlgebraicValue::Integer(value.as_ref().clone()))
                            }
                            PureFunctionArgument::Algebraic(value) => {
                                Ok(AlgebraicValue::Algebraic(value))
                            }
                            _ => Err("unsupported constructor field"),
                        })
                        .collect::<Result<Vec<_>, _>>()?;
                    values.push(PureFunctionArgument::Algebraic(AlgebraicTerm {
                        algebraic_type: constructor.algebraic_type.clone(),
                        node: AlgebraicTermNode::Constructor {
                            variant: constructor.variant.clone(),
                            fields,
                        },
                    }));
                }
                Task::Finish(matched) => {
                    let KernelType::Algebraic(ty) = &matched.result_type else {
                        return Err("expected algebraic match result");
                    };
                    let count = matched.arguments.len()
                        + matched
                            .arms
                            .iter()
                            .map(|arm| arm.bindings.len())
                            .sum::<usize>();
                    let mut children = values
                        .split_off(
                            values
                                .len()
                                .checked_sub(count)
                                .ok_or("missing algebraic match child")?,
                        )
                        .into_iter();
                    let scrutinee =
                        Box::new(algebraic(children.next().ok_or("missing scrutinee")?)?);
                    let bodies = children
                        .by_ref()
                        .take(matched.arms.len())
                        .map(algebraic)
                        .collect::<Result<Vec<_>, _>>()?;
                    let mut arms = Vec::with_capacity(matched.arms.len());
                    for (arm, body) in matched.arms.iter().zip(bodies) {
                        let mut bindings = Vec::with_capacity(arm.bindings.len());
                        for _ in &arm.bindings {
                            bindings.push(match children.next().ok_or("missing declaration")? {
                                PureFunctionArgument::Value(value) => {
                                    AlgebraicValue::Program(value)
                                }
                                PureFunctionArgument::Integer(value) => {
                                    AlgebraicValue::Integer(value.as_ref().clone())
                                }
                                PureFunctionArgument::Algebraic(value) => {
                                    AlgebraicValue::Algebraic(value)
                                }
                                _ => return Err("unsupported match declaration"),
                            });
                        }
                        arms.push(AlgebraicResultMatchArm {
                            variant: arm.variant.clone(),
                            bindings,
                            body,
                            binding_names: arm.binding_names.clone(),
                        });
                    }
                    values.push(PureFunctionArgument::Algebraic(AlgebraicTerm {
                        algebraic_type: ty.clone(),
                        node: AlgebraicTermNode::Match { scrutinee, arms },
                    }));
                }
            }
        }
        algebraic(values.pop().ok_or("missing algebraic output")?)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn algebraic_constructor_match_keys_keep_native_field_identity() {
        let _session = crate::kernel::VerificationSession::enter();
        let pointer = PointerValue::new(
            Address::symbolic(Variable(999620)),
            ProgramType::Int32Pointer,
        );
        let make = |pointer| {
            let mut source = KernelMatch::test_scrutinee(vec![
                AlgebraicValueType::Program(ProgramType::Int32Pointer),
                AlgebraicValueType::Program(ProgramType::Int32),
            ]);
            source.node = AlgebraicTermNode::Constructor {
                variant: "Arm".into(),
                fields: vec![
                    AlgebraicValue::Program(ProgramValue::Pointer(pointer)),
                    AlgebraicValue::Program(ProgramValue::Int32(MachineTerm::add(
                        MachineTerm::Variable(Variable(999621)),
                        MachineTerm::constant(1),
                    ))),
                ],
            };
            MachineTerm::AlgebraicMatch {
                scrutinee: Box::new(source),
                arms: vec![AlgebraicBitvectorMatchArm {
                    variant: "Arm".into(),
                    bindings: vec![
                        AlgebraicValue::Program(ProgramValue::Pointer(PointerValue::new(
                            Address::symbolic(Variable(999623)),
                            ProgramType::Int32Pointer,
                        ))),
                        AlgebraicValue::Program(ProgramValue::Int32(MachineTerm::Variable(
                            Variable(999624),
                        ))),
                    ],
                    binding_names: Default::default(),
                    body: MachineTerm::Variable(Variable(999622)),
                }],
            }
        };
        let native = [
            make(pointer.clone()),
            make(pointer.with_pointee_constant(true)),
        ];
        let roots = native
            .each_ref()
            .map(|value| KernelTermImport::default().machine(MachineIntegerType::Int32, value));
        assert_ne!(roots[0], roots[1]);
        let exports = KernelTermExport::machine_export_count();
        let observed = roots.map(|root| {
            SharedMachineIntegerTerm::observe_shared(MachineIntegerType::Int32, root).unwrap()
        });
        assert_eq!(observed[0], observed[1]);
        for (observed, native) in observed.iter().zip(native) {
            assert_eq!(
                observed,
                &SharedMachineIntegerTerm::intern(MachineIntegerType::Int32, native)
            );
        }
        assert_eq!(KernelTermExport::machine_export_count(), exports);
    }

    #[test]
    fn algebraic_atoms_and_constructor_fields_preserve_types_and_exact_payloads() {
        let _session = crate::kernel::VerificationSession::enter();
        let variable = KernelMatch::test_scrutinee(vec![AlgebraicValueType::Integer]);
        let root = KernelTermImport::default().algebraic(&variable);
        assert!(matches!(root.node(), KernelTermNode::Variable(_)));
        assert_eq!(
            root.ty(),
            &KernelType::Algebraic(variable.algebraic_type.clone())
        );
        assert_eq!(
            KernelTermExport::default().algebraic(&root).unwrap(),
            variable
        );
        let other =
            KernelMatch::test_scrutinee(vec![AlgebraicValueType::Program(ProgramType::Bool)]);
        assert_ne!(root, KernelTermImport::default().algebraic(&other));

        let pointer = PointerValue::new(
            Address::symbolic(Variable(999600)),
            ProgramType::Int32Pointer,
        );
        let values = [pointer.clone(), pointer.with_pointee_constant(true)].map(|pointer| {
            let mut value = KernelMatch::test_scrutinee(vec![
                AlgebraicValueType::Integer,
                AlgebraicValueType::Program(ProgramType::Int32Pointer),
            ]);
            value.node = AlgebraicTermNode::Constructor {
                variant: "Arm".into(),
                fields: vec![
                    AlgebraicValue::Integer(IntegerTerm::Variable(Variable(999601))),
                    AlgebraicValue::Program(ProgramValue::Pointer(pointer)),
                ],
            };
            value
        });
        assert_eq!(values[0], values[1]);
        let roots = values
            .each_ref()
            .map(|value| KernelTermImport::default().algebraic(value));
        assert_ne!(roots[0], roots[1]);
        for (root, value) in roots.iter().zip(&values) {
            let KernelTermNode::Constructor(constructor) = root.node() else {
                panic!()
            };
            assert_eq!(constructor.fields[0].ty(), &KernelType::Integer);
            assert!(matches!(
                constructor.fields[0].node(),
                KernelTermNode::Variable(_)
            ));
            assert_eq!(
                format!("{:?}", KernelTermExport::default().algebraic(root).unwrap()),
                format!("{value:?}")
            );
        }
    }
}

#[cfg(test)]
mod scaling_tests {
    include!("../../../scaling_tests/kernel/primitives/kernel_term/algebraic.rs");
}

impl KernelTerm {
    pub(crate) fn program_parameter(operand: Self) -> Self {
        let KernelType::Algebraic(ty) = operand.ty() else {
            panic!("program parameter requires an algebraic operand");
        };
        Self::intern(
            KernelType::Program(ProgramType::Parameter(TypeParameterName::of(ty))),
            KernelTermNode::ProgramParameter { operand },
        )
    }
}
