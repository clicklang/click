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
            return Ok(Some(then_value.clone()));
        }
        let is_bool = |value: &Self| value.c_type() == ProgramType::Bool;
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
        .map(Self::Native))
    }

    pub(super) fn numeric(self) -> Self {
        match self {
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
            MachineIntegerType::from_c_type(value.c_type())?,
            c_value_bitvector_term(&value)?,
        )
    }
    pub(super) fn comparison(
        &self,
        op: CComparisonOperator,
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
                CComparisonOperator::Equal | CComparisonOperator::NotEqual => {
                    CompareRelation::Equal
                }
                CComparisonOperator::LessThan => CompareRelation::LessThan,
                CComparisonOperator::LessEqual => CompareRelation::LessEqual,
                CComparisonOperator::GreaterThan => CompareRelation::GreaterThan,
                CComparisonOperator::GreaterEqual => CompareRelation::GreaterEqual,
            };
            return Ok(Some(Proposition::ConditionIs(
                crate::kernel::machine_integer::comparison::condition_for_operand_views(
                    format,
                    relation,
                    [left, right],
                ),
                op != CComparisonOperator::NotEqual,
            )));
        }
        let left = self.native();
        let right = right.native();
        Ok(bool_comparison_proposition(&left, op, &right)
            .transpose()?
            .or_else(|| c_value_comparison_proposition(&left, op, &right)))
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
            SpecValue::Shared(value) => Self::Shared(value),
        }
    }

    pub(super) fn native_descriptor(&self) -> Option<&PureFunctionArgument> {
        match self {
            Self::Native(value) => Some(value),
            Self::Shared(_) => None,
        }
    }

    fn into_payload(self) -> PureFunctionArgument {
        match self {
            Self::Native(value) => value,
            Self::Shared(value) => {
                let KernelType::C(ty) = value.ty() else {
                    unreachable!("machine argument");
                };
                let format = MachineIntegerType::from_c_type(*ty).expect("machine argument type");
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
