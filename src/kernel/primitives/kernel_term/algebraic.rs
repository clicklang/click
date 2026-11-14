//! Explicit native output for retained algebraic matches. Consume completed
//! children once; caching boxed prefixes would clone every nested match again.
use super::*;

#[cfg(test)]
thread_local! {
    static ALGEBRAIC_EXPORT_COUNT: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
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
            Finish(&'a KernelMatch),
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
                    } else {
                        values.push(self.argument(root)?);
                    }
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
