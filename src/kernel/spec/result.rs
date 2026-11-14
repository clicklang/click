//! Expression results retain produced machine DAGs across deferred evaluation.
//! Native inputs and unmigrated sorts cross an explicit compatibility boundary;
//! there is no implicit dereference or cached parallel expression tree.
use super::*;

pub(in crate::kernel) use crate::kernel::execution_value::ExecutionValue as SpecValue;

impl SpecValue {
    pub(super) fn conditional(
        proposition: &Proposition,
        then_value: &Self,
        else_value: &Self,
        retain: bool,
    ) -> ExecutionResult<Option<Self>> {
        if then_value == else_value {
            return Ok(Some(if retain {
                then_value.clone().retain_pointer_result()
            } else {
                then_value.clone()
            }));
        }
        let is_bool = |value: &Self| value.program_type() == ProgramType::Bool;
        if (is_bool(then_value) && else_value.machine().is_some())
            || (is_bool(else_value) && then_value.machine().is_some())
        {
            return Err(ExecutionLimit::MixedBoolArms);
        }
        if !retain {
            return Ok(conditional_spec_value(
                proposition,
                then_value.clone().into_native(),
                else_value.clone().into_native(),
            )
            .map(Self::Native));
        }
        if let (Some((left_format, left)), Some((right_format, right))) =
            (then_value.machine(), else_value.machine())
        {
            let format = if left_format == right_format {
                left_format
            } else if matches!(
                (left_format, right_format),
                (MachineIntegerType::Int32, MachineIntegerType::UInt32)
                    | (MachineIntegerType::UInt32, MachineIntegerType::Int32)
            ) {
                MachineIntegerType::UInt32
            } else {
                return Ok(None);
            };
            let Some((condition, expected)) = proposition_as_single_condition(proposition)
                .or_else(|| compound_spec_value_condition(proposition))
            else {
                return Ok(None);
            };
            let left = KernelTerm::retained_machine_operand(format, left);
            let right = KernelTerm::retained_machine_operand(format, right);
            let (left, right) = if expected {
                (left, right)
            } else {
                (right, left)
            };
            let result = match condition {
                ConditionTerm::Constant(true) => left,
                ConditionTerm::Constant(false) => right,
                _ if crate::kernel::shared_machine_syntax_equal(&left, &right) => left,
                condition => KernelTerm::machine_if_shared(
                    format,
                    [
                        KernelTermImport::default().condition(&condition),
                        left,
                        right,
                    ],
                ),
            };
            return Ok(Some(Self::Shared(result)));
        }
        Ok(conditional_spec_value(
            proposition,
            then_value.clone().into_native(),
            else_value.clone().into_native(),
        )
        .map(|value| {
            if value.program_type().is_pointer() {
                // The native constructor accepts pointer arms only when equal,
                // selecting the complete left payload. Keep its original root.
                then_value.clone().retain_pointer_result()
            } else {
                Self::Native(value)
            }
        }))
    }

    pub(super) fn numeric(self) -> Self {
        match self {
            // This is an explicit numeric projection. The complete C-value
            // record remains in its execution carrier; it is not an integer term.
            Self::Native(ProgramValue::PointerInteger(record)) => {
                let numeric = *record.numeric;
                if matches!(
                    &numeric,
                    ProgramValue::Int64(MachineTerm::PointerAddress(..))
                        | ProgramValue::UInt64(MachineTerm::PointerAddress(..))
                ) {
                    let root = KernelTermImport::default()
                        .argument(&PureFunctionArgument::Value(numeric.clone()));
                    if matches!(root.node(), KernelTermNode::PointerAddress { .. }) {
                        return root.into();
                    }
                }
                // Other complete-word payloads keep their established numeric
                // admission policy; this slice activates address observations.
                Self::Native(numeric)
            }
            Self::Native(value) => Self::Native(value.numeric_value().clone()),
            shared => shared,
        }
    }

    pub(super) fn observe(&self) -> Option<IntegerTerm> {
        // Numeric observation identity is memoized separately from the exact
        // producer payload; extending a shared prefix visits only new nodes.
        if let Self::Shared(_) = self {
            let (format, view) = self.machine()?;
            let observed = view.observe(format)?;
            return Some(match observed {
                IntegerTerm::Machine(machine) if machine.shared_operand().is_some() => {
                    IntegerTerm::Machine(SharedMachineIntegerTerm::observe_shared(
                        machine.ty(),
                        machine.shared_operand().unwrap().clone(),
                    )?)
                }
                observed => observed,
            });
        }
        let value = self.native();
        IntegerTerm::from_machine(
            MachineIntegerType::from_program_type(value.program_type())?,
            program_value_bitvector_term(&value)?,
        )
    }
    pub(super) fn comparison(
        &self,
        op: ComparisonOperator,
        right: &Self,
    ) -> ExecutionResult<Option<Proposition>> {
        if let (Some((format, left)), Some((right_format, right))) =
            (self.machine(), right.machine())
            && format == right_format
            && matches!(
                format,
                MachineIntegerType::Int32
                    | MachineIntegerType::UInt32
                    | MachineIntegerType::Int64
                    | MachineIntegerType::UInt64
            )
        {
            let relation = match op {
                ComparisonOperator::Equal | ComparisonOperator::NotEqual => CompareRelation::Equal,
                ComparisonOperator::LessThan => CompareRelation::LessThan,
                ComparisonOperator::LessEqual => CompareRelation::LessEqual,
                ComparisonOperator::GreaterThan => CompareRelation::GreaterThan,
                ComparisonOperator::GreaterEqual => CompareRelation::GreaterEqual,
            };
            return Ok(Some(Proposition::ConditionIs(
                crate::kernel::machine_integer::comparison::condition_for_operand_views(
                    format,
                    relation,
                    [left, right],
                ),
                op != ComparisonOperator::NotEqual,
            )));
        }
        let left = self.native();
        let right = right.native();
        Ok(bool_comparison_proposition(&left, op, &right)
            .transpose()?
            .or_else(|| program_value_comparison_proposition(&left, op, &right)))
    }
}

/// Call assembly retains machine results while subsequent arguments branch.
/// Opaque argument descriptors remain native until their domain migration.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum SpecCallArgument {
    Native(PureFunctionArgument),
    Shared(KernelTerm),
}

impl SpecCallArgument {
    pub(super) fn from_value(value: SpecValue) -> Self {
        match value {
            SpecValue::Native(value) => Self::Native(PureFunctionArgument::Value(value)),
            SpecValue::Shared(value)
                if matches!(value.node(), KernelTermNode::PointerAddress { .. }) =>
            {
                let KernelType::Program(ty) = value.ty() else {
                    unreachable!()
                };
                let format =
                    MachineIntegerType::from_program_type(*ty).expect("address observation type");
                Self::Native(PureFunctionArgument::Value(
                    format.value_from_term(
                        value
                            .machine_conversion_leaf()
                            .expect("address observation")
                            .clone(),
                    ),
                ))
            }
            SpecValue::Shared(value) => Self::Shared(value),
        }
    }

    pub(super) fn native_descriptor(&self) -> Option<&PureFunctionArgument> {
        match self {
            Self::Native(value) => Some(value),
            Self::Shared(value) => value.pointer_argument_native(),
        }
    }

    fn into_payload(self) -> PureFunctionArgument {
        match self {
            Self::Native(value) => value,
            Self::Shared(value) => {
                if let Some(descriptor) = value.pointer_argument_native() {
                    return descriptor.clone();
                }
                let KernelType::Program(ty) = value.ty() else {
                    unreachable!("machine argument");
                };
                let format =
                    MachineIntegerType::from_program_type(*ty).expect("machine argument type");
                PureFunctionArgument::SharedMachine(
                    SharedMachineIntegerTerm::from_shared(format, value)
                        .expect("retained pure-call argument"),
                )
            }
        }
    }
}

/// Call payloads retain word expressions and preserve opaque descriptors.
pub(super) fn call_arguments(arguments: Vec<SpecCallArgument>) -> Vec<PureFunctionArgument> {
    arguments
        .into_iter()
        .map(SpecCallArgument::into_payload)
        .collect()
}

#[cfg(test)]
mod pointer_observation_tests {
    use super::*;
    #[test]
    fn numeric_pointer_projection_retains_the_address_without_changing_complete_values() {
        let _session = crate::kernel::VerificationSession::enter();
        let pointer = PointerValue::new(
            Pointer::symbolic(Variable(1024900)),
            ProgramType::Int32Pointer,
        )
        .with_pointee_constant(true)
        .with_pointee_volatile(true);
        let numeric = ProgramValue::UInt64(MachineTerm::object_pointer_address(
            pointer.pointer().clone(),
            pointer.object_class(),
        ));
        let value = ProgramValue::PointerInteger(PointerIntegerValue {
            numeric: Box::new(numeric.clone()),
            pointer: Box::new(pointer),
            kind: PointerIntegerKind::Exact,
        });
        let complete = SpecValue::Native(value.clone());
        let projected = complete.clone().numeric();
        assert!(matches!(
            projected.shared().unwrap().node(),
            KernelTermNode::PointerAddress { .. }
        ));
        assert_eq!(projected.clone().into_native(), numeric);
        assert_eq!(
            SpecCallArgument::from_value(projected.clone()).native_descriptor(),
            Some(&PureFunctionArgument::Value(numeric.clone())),
            "opaque call arguments keep their exact native descriptor"
        );
        let other = SpecValue::Native(ProgramValue::UInt64(MachineTerm::Variable(Variable(
            1024902,
        ))));
        assert_eq!(
            projected
                .comparison(ComparisonOperator::Equal, &other)
                .unwrap(),
            SpecValue::Native(numeric.clone())
                .comparison(ComparisonOperator::Equal, &other)
                .unwrap(),
            "exact fact kind remains the native address comparison"
        );
        assert_eq!(projected.observe(), SpecValue::Native(numeric).observe());
        assert_eq!(complete.into_native(), value);
    }
}
