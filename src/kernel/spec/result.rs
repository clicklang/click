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
                then_value
                    .clone()
                    .retain_pointer_result()
                    .retain_algebraic_result()
                    .retain_float_result()
                    .retain_boolean_result()
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
        if let (Some(left), Some(right)) = (then_value.boolean(), else_value.boolean()) {
            let Some((condition, expected)) = proposition_as_single_condition(proposition)
                .or_else(|| compound_spec_value_condition(proposition))
            else {
                return Ok(None);
            };
            let (left, right) = if expected {
                (left, right)
            } else {
                (right, left)
            };
            return Ok(Some(
                KernelTerm::boolean_if([
                    KernelTermImport::default().condition(&condition),
                    left,
                    right,
                ])
                .into(),
            ));
        }
        if let (Some(left), Some(right)) = (then_value.float(), else_value.float()) {
            // Native float specification arms join only when their exact values
            // agree. Retain that root without introducing float If semantics.
            return Ok(left
                .syntax_equal(right)
                .then(|| then_value.clone().retain_float_result()));
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
            } else if matches!(value, ProgramValue::Parameter(_)) {
                // Program-carried algebraic arms join only when equal.
                then_value.clone().retain_algebraic_result()
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
                    ProgramValue::Int64(MachineTerm::IntegerAddress(..))
                        | ProgramValue::UInt64(MachineTerm::IntegerAddress(..))
                ) {
                    let root = KernelTermImport::default()
                        .argument(&PureFunctionArgument::Value(numeric.clone()));
                    if matches!(root.node(), KernelTermNode::IntegerAddress { .. }) {
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
    #[cfg(test)]
    pub(super) fn comparison(
        &self,
        op: ComparisonOperator,
        right: &Self,
    ) -> ExecutionResult<Option<Proposition>> {
        self.comparison_in(op, right, false)
    }

    pub(super) fn comparison_in(
        &self,
        op: ComparisonOperator,
        right: &Self,
        conditional_guard: bool,
    ) -> ExecutionResult<Option<Proposition>> {
        if let (Some((format, left)), Some((right_format, right))) =
            (self.machine(), right.machine())
            && format == right_format
            && (matches!(
                format,
                MachineIntegerType::Int32
                    | MachineIntegerType::UInt32
                    | MachineIntegerType::Int64
                    | MachineIntegerType::UInt64
            ) || (matches!(
                format,
                MachineIntegerType::Int8
                    | MachineIntegerType::UInt8
                    | MachineIntegerType::Int16
                    | MachineIntegerType::UInt16
            ) && left.literal().is_some()
                && right.literal().is_some()))
        {
            let relation = match op {
                ComparisonOperator::Equal | ComparisonOperator::NotEqual => CompareRelation::Equal,
                ComparisonOperator::LessThan => CompareRelation::LessThan,
                ComparisonOperator::LessEqual => CompareRelation::LessEqual,
                ComparisonOperator::GreaterThan => CompareRelation::GreaterThan,
                ComparisonOperator::GreaterEqual => CompareRelation::GreaterEqual,
            };
            use crate::kernel::machine_integer::comparison;
            let condition = if conditional_guard {
                comparison::logical_conditional_guard_for_operand_views(
                    format,
                    relation,
                    [left, right],
                )
            } else {
                comparison::logical_condition_for_operand_views(format, relation, [left, right])
            };
            return Ok(Some(Proposition::ConditionIs(
                condition,
                op != ComparisonOperator::NotEqual,
            )));
        }
        // Logical Bool equality builds its common operands before the explicit
        // proposition output boundary. Raw C words retain their nonzero policy.
        let logical = |value: &Self| match value {
            Self::Shared(root)
                if root.ty() == &KernelType::Bool
                    && !matches!(root.node(), KernelTermNode::BoolLiteral(_)) =>
            {
                Some(root.clone())
            }
            Self::Native(ProgramValue::Bool(word)) => word
                .bool_cast_operand()
                .map(|condition| KernelTermImport::default().condition(condition)),
            _ => None,
        };
        if matches!(op, ComparisonOperator::Equal | ComparisonOperator::NotEqual)
            && let (Some(left), Some(right)) = (logical(self), logical(right))
        {
            let root = KernelTerm::boolean_equal([left, right]);
            return Ok(Some(Proposition::ConditionIs(
                KernelTermExport::condition(&root).expect("Boolean equality"),
                op == ComparisonOperator::Equal,
            )));
        }
        let left = self.native();
        let right = right.native();
        if let (ProgramValue::Pointer(a), ProgramValue::Pointer(b)) =
            (left.numeric_value(), right.numeric_value())
            && a == b
            && !a.is_null()
            && let Some(held) = match op {
                ComparisonOperator::Equal => Some(true),
                ComparisonOperator::NotEqual => Some(false),
                _ => None,
            }
        {
            // Lowering is structural: `p == p` keeps its comparison.
            return Ok(Some(Proposition::ConditionIs(
                ConditionTerm::logical_pointer_equal(a.clone(), b.clone()),
                held,
            )));
        }
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
            SpecValue::Shared(root) if matches!(root.ty(), KernelType::Algebraic(_)) => {
                Self::Shared(KernelTerm::program_parameter(root))
            }
            SpecValue::Shared(value)
                if matches!(value.node(), KernelTermNode::IntegerAddress { .. }) =>
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
            Self::Shared(value) => value
                .pointer_argument_native()
                .or_else(|| value.boolean_argument_native()),
        }
    }

    pub(super) fn into_typed_call_operand(self) -> (KernelTerm, Option<SharedMachineIntegerTerm>) {
        match self {
            Self::Shared(root) if matches!(root.ty(), KernelType::Program(ty) if MachineIntegerType::from_program_type(*ty).is_some()) =>
            {
                let KernelType::Program(ty) = root.ty() else {
                    unreachable!()
                };
                let format = MachineIntegerType::from_program_type(*ty).expect("numeric argument");
                let carrier = SharedMachineIntegerTerm::from_shared(format, root.clone())
                    .expect("retained argument");
                (root, Some(carrier))
            }
            Self::Shared(root) => (root, None),
            value => {
                let argument = value.into_payload();
                let shared = match &argument {
                    PureFunctionArgument::SharedMachine(value) => Some(value.clone()),
                    _ => None,
                };
                (KernelTermImport::default().argument(&argument), shared)
            }
        }
    }

    fn into_payload(self) -> PureFunctionArgument {
        match self {
            Self::Native(value) => value,
            Self::Shared(value) => {
                if matches!(value.node(), KernelTermNode::ProgramParameter { .. }) {
                    return KernelTermExport::default()
                        .argument(&value)
                        .expect("program parameter argument");
                }
                if FloatOperandView::from_shared(&value).is_some() {
                    return PureFunctionArgument::Value(
                        KernelTermExport::float(&value).expect("selected float argument boundary"),
                    );
                }
                if matches!(value.ty(), KernelType::Algebraic(_)) {
                    return PureFunctionArgument::Algebraic(
                        KernelTermExport::default()
                            .algebraic(&value)
                            .expect("algebraic argument compatibility boundary"),
                    );
                }
                if let Some(descriptor) = value
                    .pointer_argument_native()
                    .or_else(|| value.boolean_argument_native())
                {
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

/// Assemble supported typed arguments without a native call payload. Exact
/// opaque descriptors keep the existing application-owned compatibility path.
pub(super) fn common_call_arguments(arguments: &[SpecCallArgument]) -> Option<Vec<KernelTerm>> {
    let mut importer = KernelTermImport::default();
    arguments
        .iter()
        .map(|argument| match argument {
            SpecCallArgument::Shared(root) => Some(root.clone()),
            SpecCallArgument::Native(PureFunctionArgument::Value(
                ProgramValue::Pointer(_) | ProgramValue::PointerInteger(_) | ProgramValue::Void,
            ))
            | SpecCallArgument::Native(PureFunctionArgument::ArrayRef { .. }) => None,
            SpecCallArgument::Native(PureFunctionArgument::Value(
                crate::kernel::integer_c_value!(term),
            )) if matches!(term, MachineTerm::IntegerAddress(..)) => None,
            SpecCallArgument::Native(value) => {
                let root = importer.argument(value);
                (!matches!(root.node(), KernelTermNode::Legacy(_))).then_some(root)
            }
        })
        .collect()
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
    fn shared_float_atoms_keep_mixed_call_roots() {
        let _session = crate::kernel::VerificationSession::enter();
        for value in [
            ProgramValue::Float32(MachineTerm::uint32_constant(0x7f800123)),
            ProgramValue::Float64(MachineTerm::uint64_constant(0x8000000000000000)),
        ] {
            let expected = PureFunctionArgument::Value(value.clone());
            let root = KernelTermImport::default().argument(&expected);
            let shared = SpecValue::Shared(root.clone());
            assert_eq!(shared.clone().into_native(), value);
            let argument = SpecCallArgument::from_value(shared);
            assert!(matches!(&argument, SpecCallArgument::Shared(selected) if selected == &root));
            assert_eq!(call_arguments(vec![argument.clone()]), vec![expected]);
            let (restored, carrier) = argument.into_typed_call_operand();
            assert_eq!(restored, root);
            assert!(carrier.is_none());
        }
    }

    #[test]
    fn numeric_pointer_projection_retains_the_address_without_changing_complete_values() {
        let _session = crate::kernel::VerificationSession::enter();
        let pointer = Pointer::new(
            Address::symbolic(Variable(1024900)),
            ProgramType::Int32Pointer,
        )
        .with_pointee_constant(true)
        .with_pointee_volatile(true);
        let numeric = ProgramValue::UInt64(MachineTerm::object_pointer_address(
            pointer.address().clone(),
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
            KernelTermNode::IntegerAddress { .. }
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
