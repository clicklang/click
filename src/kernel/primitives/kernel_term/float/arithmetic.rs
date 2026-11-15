//! Structural float arithmetic boundaries. Evaluation and constant folding stay
//! in the existing producer; importing or exporting a node never evaluates it.
use super::*;

impl KernelTerm {
    pub(crate) fn float_negate(
        format: KernelFloatType,
        operand: Self,
    ) -> Result<Self, &'static str> {
        let ty = KernelType::Program(format.program_type());
        if operand.ty() != &ty {
            return Err("float negation width");
        }
        Ok(Self::intern(ty, KernelTermNode::FloatNegate { operand }))
    }
    pub(crate) fn float_binary(
        format: KernelFloatType,
        operator: FloatBinaryOperator,
        arguments: [Self; 2],
    ) -> Result<Self, &'static str> {
        let ty = KernelType::Program(format.program_type());
        if arguments.iter().any(|argument| argument.ty() != &ty) {
            return Err("float arithmetic width");
        }
        Ok(Self::intern(
            ty,
            KernelTermNode::FloatBinary {
                operator,
                arguments,
            },
        ))
    }
}

impl<'a> FloatOperandView<'a> {
    pub(crate) fn negate(self) -> Option<Self> {
        match self {
            Self::Native(KernelFloatType::Float32, MachineTerm::Float32Negate(value)) => {
                Some(Self::Native(KernelFloatType::Float32, value))
            }
            Self::Native(KernelFloatType::Float64, MachineTerm::Float64Negate(value)) => {
                Some(Self::Native(KernelFloatType::Float64, value))
            }
            Self::Shared(root) => match root.node() {
                KernelTermNode::FloatNegate { operand } => Some(Self::Shared(operand)),
                _ => None,
            },
            _ => None,
        }
    }
    pub(crate) fn binary(self) -> Option<(FloatBinaryOperator, [Self; 2])> {
        match self {
            Self::Native(
                format,
                MachineTerm::Float32Binary {
                    operator,
                    left,
                    right,
                },
            ) if format == KernelFloatType::Float32 => Some((
                *operator,
                [Self::Native(format, left), Self::Native(format, right)],
            )),
            Self::Native(
                format,
                MachineTerm::Float64Binary {
                    operator,
                    left,
                    right,
                },
            ) if format == KernelFloatType::Float64 => Some((
                *operator,
                [Self::Native(format, left), Self::Native(format, right)],
            )),
            Self::Shared(root) => match root.node() {
                KernelTermNode::FloatBinary {
                    operator,
                    arguments,
                } => Some((*operator, arguments.each_ref().map(Self::Shared))),
                _ => None,
            },
            _ => None,
        }
    }
}

impl KernelTermImport {
    pub(crate) fn float(&mut self, format: KernelFloatType, source: &MachineTerm) -> KernelTerm {
        enum Task<'a> {
            Enter(&'a MachineTerm),
            Negate,
            Binary(FloatBinaryOperator),
        }
        let mut pending = vec![Task::Enter(source)];
        let mut values = Vec::new();
        while let Some(task) = pending.pop() {
            crate::instrumentation::record_deterministic_work(1);
            match task {
                Task::Enter(term) => {
                    let view = FloatOperandView::Native(format, term);
                    if let Some(operand) = view.negate() {
                        pending.push(Task::Negate);
                        pending.push(Task::Enter(
                            operand.native_compat().expect("native operand"),
                        ));
                    } else if let Some((operator, arguments)) = view.binary() {
                        pending.push(Task::Binary(operator));
                        pending.extend(arguments.into_iter().rev().map(|argument| {
                            Task::Enter(argument.native_compat().expect("native operand"))
                        }));
                    } else {
                        values.push(self.float_atom(format, term));
                    }
                }
                Task::Negate => {
                    let operand = values.pop().expect("negation operand");
                    values.push(
                        KernelTerm::float_negate(format, operand).expect("imported float width"),
                    );
                }
                Task::Binary(operator) => {
                    let right = values.pop().expect("right operand");
                    let left = values.pop().expect("left operand");
                    values.push(
                        KernelTerm::float_binary(format, operator, [left, right])
                            .expect("imported float width"),
                    );
                }
            }
        }
        values.pop().expect("float import root")
    }
}

impl KernelTermExport {
    pub(super) fn float_machine(source: &KernelTerm) -> Result<MachineTerm, &'static str> {
        enum Task<'a> {
            Enter(&'a KernelTerm),
            Negate(KernelFloatType),
            Binary(KernelFloatType, FloatBinaryOperator),
        }
        let mut pending = vec![Task::Enter(source)];
        let mut values = Vec::new();
        while let Some(task) = pending.pop() {
            crate::instrumentation::record_deterministic_work(1);
            match task {
                Task::Enter(root) => {
                    let view = FloatOperandView::from_shared(root).ok_or("float operand type")?;
                    match root.node() {
                        KernelTermNode::FloatNegate { operand } => {
                            pending.push(Task::Negate(view.format()));
                            pending.push(Task::Enter(operand));
                        }
                        KernelTermNode::FloatBinary {
                            operator,
                            arguments,
                        } => {
                            pending.push(Task::Binary(view.format(), *operator));
                            pending.extend(arguments.iter().rev().map(Task::Enter));
                        }
                        _ => values.push(
                            view.native_compat()
                                .ok_or("unsupported float node")?
                                .clone(),
                        ),
                    }
                }
                Task::Negate(format) => {
                    let value = Box::new(values.pop().expect("negation operand"));
                    values.push(match format {
                        KernelFloatType::Float32 => MachineTerm::Float32Negate(value),
                        KernelFloatType::Float64 => MachineTerm::Float64Negate(value),
                    });
                }
                Task::Binary(format, operator) => {
                    let right = Box::new(values.pop().expect("right operand"));
                    let left = Box::new(values.pop().expect("left operand"));
                    values.push(match format {
                        KernelFloatType::Float32 => MachineTerm::Float32Binary {
                            operator,
                            left,
                            right,
                        },
                        KernelFloatType::Float64 => MachineTerm::Float64Binary {
                            operator,
                            left,
                            right,
                        },
                    });
                }
            }
        }
        values.pop().ok_or("missing float export root")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn float_arithmetic_preserves_width_order_bits_and_raw_structure() {
        let _session = crate::kernel::VerificationSession::enter();
        for format in [KernelFloatType::Float32, KernelFloatType::Float64] {
            let variable = MachineTerm::Variable(Variable(999930));
            let literal = match format {
                KernelFloatType::Float32 => MachineTerm::constant(0xffc01234),
                KernelFloatType::Float64 => MachineTerm::uint64_constant(0xfff8000000001234),
            };
            for operator in [
                FloatBinaryOperator::Add,
                FloatBinaryOperator::Subtract,
                FloatBinaryOperator::Multiply,
                FloatBinaryOperator::Divide,
            ] {
                let raw = match format {
                    KernelFloatType::Float32 => MachineTerm::Float32Binary {
                        operator,
                        left: Box::new(variable.clone()),
                        right: Box::new(literal.clone()),
                    },
                    KernelFloatType::Float64 => MachineTerm::Float64Binary {
                        operator,
                        left: Box::new(variable.clone()),
                        right: Box::new(literal.clone()),
                    },
                };
                let source = match format {
                    KernelFloatType::Float32 => MachineTerm::Float32Negate(Box::new(raw)),
                    KernelFloatType::Float64 => MachineTerm::Float64Negate(Box::new(raw)),
                };
                let root = KernelTermImport::default().float(format, &source);
                let view = FloatOperandView::from_shared(&root).unwrap();
                let binary = view.negate().unwrap();
                let (actual, arguments) = binary.binary().unwrap();
                assert_eq!(actual, operator);
                assert_eq!(arguments[0].variable(), Some(Variable(999930)));
                assert_eq!(
                    arguments[1].literal(),
                    FloatOperandView::Native(format, &literal).literal()
                );
                assert!(view.native_compat().is_none());
                assert!(root.0.machine_leaf.0.get().is_none());
                assert_eq!(
                    KernelTermExport::float(&root).unwrap(),
                    format.value(source)
                );
                assert!(
                    root.0.machine_leaf.0.get().is_none(),
                    "explicit output must not cache every boxed prefix"
                );
            }
        }
        let f32_root =
            KernelTerm::variable(KernelType::Program(ProgramType::Float32), Variable(999930));
        let f64_root =
            KernelTerm::variable(KernelType::Program(ProgramType::Float64), Variable(999930));
        assert!(KernelTerm::float_negate(KernelFloatType::Float64, f32_root.clone()).is_err());
        assert!(
            KernelTerm::float_binary(
                KernelFloatType::Float32,
                FloatBinaryOperator::Add,
                [f32_root, f64_root]
            )
            .is_err()
        );
    }
}
