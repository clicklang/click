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
        let preserve_equal_arms = retain
            && matches!(
                then_value.program_type(),
                ProgramType::Bool
                    | ProgramType::Int32
                    | ProgramType::UInt32
                    | ProgramType::Int64
                    | ProgramType::UInt64
            );
        if !preserve_equal_arms && then_value == else_value {
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
                return Ok(
                    (then_value == else_value).then(|| then_value.clone().retain_boolean_result())
                );
            };
            let (left, right) = if expected {
                (left, right)
            } else {
                (right, left)
            };
            // Exact rewrites can make the arms equal while retaining the if.
            return Ok(Some(
                KernelTerm::boolean_if_preserving_equal_arms([
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
                return Ok((then_value == else_value).then(|| then_value.clone()));
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
                _ if !preserve_equal_arms
                    && crate::kernel::shared_machine_syntax_equal(&left, &right) =>
                {
                    left
                }
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
            return Ok(Some(Proposition::condition_is(
                StoredConditionTerm::from_minted(condition),
                op != ComparisonOperator::NotEqual,
            )));
        }
        if matches!(op, ComparisonOperator::Equal | ComparisonOperator::NotEqual) {
            let literal = |value: &Self| match value {
                Self::Shared(root) if root.ty() == &KernelType::Bool => match root.node() {
                    KernelTermNode::BoolLiteral(value) => Some(*value),
                    _ => None,
                },
                Self::Native(ProgramValue::Bool(word)) => word.bool_constant_value(),
                _ => None,
            };
            let logical_root = |value: &Self| {
                value
                    .shared()
                    .filter(|root| {
                        root.ty() == &KernelType::Bool
                            && !matches!(root.node(), KernelTermNode::BoolLiteral(_))
                    })
                    .cloned()
            };
            if let Some((mut root, literal)) = logical_root(self)
                .zip(literal(right))
                .or_else(|| logical_root(right).zip(literal(self)))
            {
                let mut truth = literal == (op == ComparisonOperator::Equal);
                // The existing truth-claim rule removes outer logical
                // negations only; it does not evaluate a compound guard.
                while let KernelTermNode::BoolIf { arguments } = root.node() {
                    if !matches!(arguments[1].node(), KernelTermNode::BoolLiteral(false))
                        || !matches!(arguments[2].node(), KernelTermNode::BoolLiteral(true))
                    {
                        break;
                    }
                    root = arguments[0].clone();
                    truth = !truth;
                }
                return Ok(Some(Proposition::condition_is(
                    StoredConditionTerm::from_root(root).expect("logical truth claim"),
                    truth,
                )));
            }
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
            return Ok(Some(Proposition::condition_is(
                StoredConditionTerm::from_root(root).expect("Boolean equality"),
                op == ComparisonOperator::Equal,
            )));
        }
        if let (Some(left), Some(right_view)) = (self.float(), right.float())
            && left.format() == right_view.format()
            && self.shared().is_some()
            && right.shared().is_some()
        {
            let format = left.format();
            // Preserve the native producer's IEEE literal folding. The shared
            // float reader uses the same bit operations without exporting trees.
            let condition = match (
                float_condition_constant_bits(left),
                float_condition_constant_bits(right_view),
            ) {
                (Some(left), Some(right)) => {
                    let native = match format {
                        KernelFloatType::Float32 => ConditionTerm::float32_compare(
                            MachineTerm::uint32_constant(left as u32),
                            MachineTerm::uint32_constant(right as u32),
                            op,
                        ),
                        KernelFloatType::Float64 => ConditionTerm::float64_compare(
                            MachineTerm::uint64_constant(left),
                            MachineTerm::uint64_constant(right),
                            op,
                        ),
                    };
                    StoredConditionTerm::from_minted(native)
                }
                _ => StoredConditionTerm::from_root(
                    KernelTerm::float_compare(
                        format,
                        op,
                        [self.common_operand(), right.common_operand()],
                    )
                    .expect("same float format"),
                )
                .expect("logical float comparison"),
            };
            return Ok(Some(Proposition::condition_is(condition, true)));
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
            return Ok(Some(Proposition::condition_is(
                ConditionTerm::logical_pointer_equal(a.clone(), b.clone()),
                held,
            )));
        }
        let proposition = bool_comparison_proposition(&left, op, &right)
            .transpose()?
            .or_else(|| program_value_comparison_proposition(&left, op, &right));
        // Lowering is structural: when the native constructor decides a
        // comparison of two identical or literal machine words of one
        // format, such as `address(p) + 3u64 == address(p) + 3u64`, keep
        // the comparison; checking decides it.
        if let Some(Proposition::ConditionIs(condition, _)) = &proposition
            && matches!(condition.native_compat(), ConditionTerm::Constant(_))
            && let Some(retained) = retained_word_comparison(&left, op, &right)
        {
            return Ok(Some(retained));
        }
        Ok(proposition)
    }
}

/// The undecided native comparison of two machine words of one 32- or
/// 64-bit format, as logical lowering builds it.
fn retained_word_comparison(
    left: &ProgramValue,
    op: ComparisonOperator,
    right: &ProgramValue,
) -> Option<Proposition> {
    let word = |value: &ProgramValue| -> Option<(MachineIntegerType, MachineTerm)> {
        Some(match value.numeric_value() {
            ProgramValue::Int32(term) => (MachineIntegerType::Int32, term.clone()),
            ProgramValue::UInt32(term) => (MachineIntegerType::UInt32, term.clone()),
            ProgramValue::Int64(term) => (MachineIntegerType::Int64, term.clone()),
            ProgramValue::UInt64(term) => (MachineIntegerType::UInt64, term.clone()),
            _ => return None,
        })
    };
    let ((format, left), (right_format, right)) = (word(left)?, word(right)?);
    // Identical or literal words only; a comparison the type range decides
    // keeps its established decision.
    if format != right_format
        || !(left == right
            || (format.constant_from_term(&left).is_some()
                && format.constant_from_term(&right).is_some()))
    {
        return None;
    }
    let relation = match op {
        ComparisonOperator::Equal | ComparisonOperator::NotEqual => CompareRelation::Equal,
        ComparisonOperator::LessThan => CompareRelation::LessThan,
        ComparisonOperator::LessEqual => CompareRelation::LessEqual,
        ComparisonOperator::GreaterThan => CompareRelation::GreaterThan,
        ComparisonOperator::GreaterEqual => CompareRelation::GreaterEqual,
    };
    let condition = crate::kernel::machine_integer::comparison::logical_condition_for_operand_views(
        format,
        relation,
        [
            crate::kernel::MachineOperandView::Legacy(&left),
            crate::kernel::MachineOperandView::Legacy(&right),
        ],
    );
    (!matches!(condition, ConditionTerm::Constant(_)))
        .then(|| Proposition::condition_is(condition, op != ComparisonOperator::NotEqual))
}

/// The existing float predicate producer folds literal arithmetic before
/// constructing its condition. Read a retained DAG once per selected operand;
/// repeated children share their result, including nonconstant refusals.
pub(super) fn float_condition_constant_bits(view: FloatOperandView<'_>) -> Option<u64> {
    let FloatOperandView::Shared(root) = view else {
        return view.constant_bits();
    };
    enum Task<'a> {
        Enter(&'a KernelTerm),
        Negate(&'a KernelTerm, &'a KernelTerm),
        BinaryLeft(&'a KernelTerm, FloatBinaryOperator, [&'a KernelTerm; 2]),
        BinaryRight(&'a KernelTerm, FloatBinaryOperator, [&'a KernelTerm; 2]),
    }
    let mut values = std::collections::HashMap::new();
    let mut pending = vec![Task::Enter(root)];
    while let Some(task) = pending.pop() {
        match task {
            Task::Enter(root) => {
                if values.contains_key(&root.id()) {
                    continue;
                }
                crate::instrumentation::record_deterministic_work(1);
                match root.node() {
                    KernelTermNode::FloatNegate { operand } => {
                        pending.push(Task::Negate(root, operand));
                        pending.push(Task::Enter(operand));
                    }
                    KernelTermNode::FloatBinary {
                        operator,
                        arguments,
                    } => {
                        pending.push(Task::BinaryLeft(root, *operator, arguments.each_ref()));
                        pending.push(Task::Enter(&arguments[0]));
                    }
                    _ => {
                        values.insert(root.id(), FloatOperandView::Shared(root).constant_bits());
                    }
                }
            }
            Task::Negate(root, operand) => {
                let sign = match FloatOperandView::Shared(root).format() {
                    KernelFloatType::Float32 => 0x8000_0000,
                    KernelFloatType::Float64 => 0x8000_0000_0000_0000,
                };
                values.insert(root.id(), values[&operand.id()].map(|bits| bits ^ sign));
            }
            Task::BinaryLeft(root, operator, arguments) => {
                if values[&arguments[0].id()].is_none() {
                    values.insert(root.id(), None);
                } else {
                    pending.push(Task::BinaryRight(root, operator, arguments));
                    pending.push(Task::Enter(arguments[1]));
                }
            }
            Task::BinaryRight(root, operator, arguments) => {
                let value = values[&arguments[0].id()]
                    .zip(values[&arguments[1].id()])
                    .and_then(|(left, right)| {
                        let format = FloatOperandView::Shared(root).format();
                        let native = match format {
                            KernelFloatType::Float32 => MachineTerm::float32_binary(
                                MachineTerm::constant(left as u32),
                                MachineTerm::constant(right as u32),
                                operator,
                            ),
                            KernelFloatType::Float64 => MachineTerm::float64_binary(
                                MachineTerm::uint64_constant(left),
                                MachineTerm::uint64_constant(right),
                                operator,
                            ),
                        };
                        FloatOperandView::Native(format, &native).constant_bits()
                    });
                values.insert(root.id(), value);
            }
        }
    }
    values[&root.id()]
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

#[cfg(test)]
mod condition_output_tests {
    use super::*;
    #[test]
    fn evaluated_machine_comparisons_retain_roots_and_exact_native_outputs() {
        let _session = crate::kernel::VerificationSession::enter();
        for format in [
            MachineIntegerType::Int32,
            MachineIntegerType::UInt32,
            MachineIntegerType::Int64,
            MachineIntegerType::UInt64,
        ] {
            let left = SpecValue::Shared(KernelTerm::variable(
                KernelType::Program(format.program_type()),
                Variable(10993720),
            ));
            let right = SpecValue::Shared(KernelTerm::variable(
                KernelType::Program(format.program_type()),
                Variable(10993721),
            ));
            for (operator, relation) in [
                (ComparisonOperator::Equal, CompareRelation::Equal),
                (ComparisonOperator::NotEqual, CompareRelation::Equal),
                (ComparisonOperator::LessThan, CompareRelation::LessThan),
                (ComparisonOperator::LessEqual, CompareRelation::LessEqual),
                (
                    ComparisonOperator::GreaterThan,
                    CompareRelation::GreaterThan,
                ),
                (
                    ComparisonOperator::GreaterEqual,
                    CompareRelation::GreaterEqual,
                ),
            ] {
                for guard in [false, true] {
                    use crate::kernel::machine_integer::comparison;
                    let operands = [left.machine().unwrap().1, right.machine().unwrap().1];
                    let expected = if guard {
                        comparison::logical_conditional_guard_for_operand_views(
                            format, relation, operands,
                        )
                    } else {
                        comparison::logical_condition_for_operand_views(format, relation, operands)
                    };
                    let Proposition::ConditionIs(condition, truth) = left
                        .comparison_in(operator, &right, guard)
                        .unwrap()
                        .unwrap()
                    else {
                        unreachable!()
                    };
                    assert!(condition.root().is_some());
                    assert_eq!(condition.native_compat(), &expected);
                    assert_eq!(
                        condition.root(),
                        Some(&KernelTermImport::for_exact_field_inputs().condition(&expected))
                    );
                    assert_eq!(truth, operator != ComparisonOperator::NotEqual);
                    let exports = KernelTermExport::machine_export_count();
                    for _ in 0..4 {
                        assert_eq!(condition.native_compat(), &expected);
                    }
                    assert_eq!(KernelTermExport::machine_export_count(), exports);
                }
            }
        }
    }

    #[test]
    fn evaluated_boolean_comparison_outputs_retain_the_produced_root() {
        let _session = crate::kernel::VerificationSession::enter();
        let left = KernelTerm::variable(KernelType::Bool, Variable(10993721));
        let right = KernelTerm::variable(KernelType::Bool, Variable(10993722));
        for operator in [ComparisonOperator::Equal, ComparisonOperator::NotEqual] {
            let expected = KernelTerm::boolean_equal([left.clone(), right.clone()]);
            let output = SpecValue::Shared(left.clone())
                .comparison(operator, &SpecValue::Shared(right.clone()))
                .unwrap()
                .unwrap();
            let Proposition::ConditionIs(condition, truth) = output else {
                unreachable!();
            };
            assert_eq!(condition.root(), Some(&expected));
            assert_eq!(truth, operator == ComparisonOperator::Equal);
            assert!(!left.has_cached_native_argument());
            assert!(!right.has_cached_native_argument());
            assert!(!expected.has_cached_native_argument());
        }
    }
    #[test]
    fn evaluated_float_comparison_outputs_retain_shared_operands() {
        let _session = crate::kernel::VerificationSession::enter();
        for format in [KernelFloatType::Float32, KernelFloatType::Float64] {
            let left = KernelTerm::variable(
                KernelType::Program(format.program_type()),
                Variable(10993723),
            );
            let right = KernelTerm::variable(
                KernelType::Program(format.program_type()),
                Variable(10993724),
            );
            for operator in [
                ComparisonOperator::Equal,
                ComparisonOperator::NotEqual,
                ComparisonOperator::LessThan,
                ComparisonOperator::LessEqual,
                ComparisonOperator::GreaterThan,
                ComparisonOperator::GreaterEqual,
            ] {
                let expected =
                    KernelTerm::float_compare(format, operator, [left.clone(), right.clone()])
                        .unwrap();
                let exports = KernelTermExport::float_export_count();
                let output = SpecValue::Shared(left.clone())
                    .comparison(operator, &SpecValue::Shared(right.clone()))
                    .unwrap()
                    .unwrap();
                let Proposition::ConditionIs(condition, truth) = output else {
                    unreachable!();
                };
                assert_eq!(condition.root(), Some(&expected));
                assert!(truth);
                assert_eq!(KernelTermExport::float_export_count(), exports);
                assert!(!left.has_cached_native_argument());
                assert!(!right.has_cached_native_argument());
            }
        }
    }

    #[test]
    fn integer_comparison_outputs_keep_native_observation_spelling_and_roots() {
        let _session = crate::kernel::VerificationSession::enter();
        let values = [
            IntegerTerm::Variable(Variable(10993725)),
            IntegerTerm::constant_i64(7),
            IntegerTerm::from_machine(
                MachineIntegerType::Int32,
                MachineTerm::Variable(Variable(10993726)),
            )
            .unwrap(),
            IntegerTerm::from_machine(
                MachineIntegerType::UInt64,
                MachineTerm::Variable(Variable(10993727)),
            )
            .unwrap(),
            IntegerTerm::Add(
                IntegerTerm::Variable(Variable(10993728)).into(),
                IntegerTerm::constant_i64(3).into(),
            ),
        ];
        for left in &values {
            for right in &values {
                for operator in [
                    IntegerComparisonOperator::Equal,
                    IntegerComparisonOperator::NotEqual,
                    IntegerComparisonOperator::LessThan,
                    IntegerComparisonOperator::LessEqual,
                    IntegerComparisonOperator::GreaterThan,
                    IntegerComparisonOperator::GreaterEqual,
                ] {
                    let native = match operator {
                        IntegerComparisonOperator::Equal => {
                            ConditionTerm::IntegerEqual(left.clone().into(), right.clone().into())
                        }
                        IntegerComparisonOperator::NotEqual => ConditionTerm::IntegerNotEqual(
                            left.clone().into(),
                            right.clone().into(),
                        ),
                        IntegerComparisonOperator::LessThan => ConditionTerm::IntegerLessThan(
                            left.clone().into(),
                            right.clone().into(),
                        ),
                        IntegerComparisonOperator::LessEqual => ConditionTerm::IntegerLessEqual(
                            left.clone().into(),
                            right.clone().into(),
                        ),
                        IntegerComparisonOperator::GreaterThan => {
                            ConditionTerm::IntegerGreaterThan(
                                left.clone().into(),
                                right.clone().into(),
                            )
                        }
                        IntegerComparisonOperator::GreaterEqual => {
                            ConditionTerm::IntegerGreaterEqual(
                                left.clone().into(),
                                right.clone().into(),
                            )
                        }
                    };
                    let expected = match crate::kernel::machine_integer::comparison::structural_native_comparison_of_integer_observation(&native, true) {
                        Some((ConditionTerm::Constant(_), _)) | None => (native, true),
                        Some(result) => result,
                    };
                    let actual = retained_integer_comparison(
                        &left.clone().into(),
                        operator,
                        &right.clone().into(),
                    );
                    assert!(actual.0.root().is_some());
                    assert_eq!(
                        (actual.0.native_compat(), actual.1),
                        (&expected.0, expected.1)
                    );
                    let expected_root =
                        KernelTermImport::for_exact_field_inputs().condition(&expected.0);
                    assert_eq!(actual.0.root(), Some(&expected_root));
                }
            }
        }
    }

    #[test]
    fn evaluated_predicate_arguments_keep_the_original_program_root() {
        let _session = crate::kernel::VerificationSession::enter();
        let format = MachineIntegerType::Int32;
        let operand =
            KernelTerm::variable(KernelType::Program(ProgramType::Int32), Variable(10993746));
        let root = KernelTerm::machine_binary_shared(
            format,
            MachineBinaryOp::Add,
            [operand.clone(), operand],
        );
        let state = ExecutionState::new().with_retained_local("x", root.clone().into());
        let expression = SpecProposition::Predicate {
            name: "retained_argument".into(),
            arguments: vec![SpecPredicateArgument::Value(
                SpecExpression::ProgramExpression(ProgramExpression::Variable("x".into())),
            )],
            resource_state_dependent: false,
        };
        let exports = KernelTermExport::machine_export_count();
        let paths = lower_spec_proposition_at_state_with_loop_entry(
            &state,
            &expression,
            None,
            &PureFactContext::new(),
            &mut ExecutionBudget::new(),
        )
        .unwrap();
        let [path] = paths.as_slice() else {
            panic!("one predicate path")
        };
        let Proposition::Predicate { arguments, .. } = &path.proposition else {
            panic!("predicate output")
        };
        let [Term::ExecutionState(_), Term::ProgramValue(argument)] = arguments.as_slice() else {
            panic!("one evaluated program argument")
        };
        assert_eq!(argument.root(), Some(&root));
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        assert!(!root.has_cached_native_argument());
        let native = ProgramValue::Int32(MachineTerm::Binary {
            format,
            op: MachineBinaryOp::Add,
            left: Box::new(MachineTerm::Variable(Variable(10993746))),
            right: Box::new(MachineTerm::Variable(Variable(10993746))),
        });
        let mut expected = path.proposition.clone();
        let Proposition::Predicate { arguments, .. } = &mut expected else {
            unreachable!()
        };
        arguments[1] = Term::ProgramValue(native.into());
        assert_eq!(path.proposition, expected);
        assert_eq!(path.proposition.cmp(&expected), std::cmp::Ordering::Equal);
        fn hash(value: &impl std::hash::Hash) -> u64 {
            use std::hash::Hasher;
            let mut state = std::collections::hash_map::DefaultHasher::new();
            value.hash(&mut state);
            state.finish()
        }
        assert_eq!(hash(&path.proposition), hash(&expected));
    }

    #[test]
    fn lowered_float_classification_keeps_the_execution_value_root() {
        let _session = crate::kernel::VerificationSession::enter();
        for format in [KernelFloatType::Float32, KernelFloatType::Float64] {
            let root = KernelTerm::float_call(format, "classification_source".into(), vec![]);
            let state = ExecutionState::new().with_retained_local("x", root.clone().into());
            for classification in [
                FloatClassification::Finite,
                FloatClassification::Infinite,
                FloatClassification::Zero,
                FloatClassification::Subnormal,
                FloatClassification::Nan,
            ] {
                let expression = SpecProposition::FloatClassification {
                    expression: SpecExpression::ProgramExpression(ProgramExpression::Variable(
                        "x".into(),
                    )),
                    classification,
                };
                let exports = KernelTermExport::float_export_count();
                let paths = lower_spec_proposition_at_state_with_loop_entry(
                    &state,
                    &expression,
                    None,
                    &PureFactContext::new(),
                    &mut ExecutionBudget::new(),
                )
                .unwrap();
                assert_eq!(paths.len(), 1);
                let Proposition::ConditionIs(condition, truth) = &paths[0].proposition else {
                    unreachable!();
                };
                let expected =
                    KernelTerm::float_classify(format, classification, root.clone()).unwrap();
                assert_eq!(condition.root(), Some(&expected));
                assert!(*truth);
                assert_eq!(KernelTermExport::float_export_count(), exports);
            }
        }
    }

    #[test]
    fn logical_literal_comparisons_keep_roots_polarity_and_outer_negation_rules() {
        let _session = crate::kernel::VerificationSession::enter();
        let base = KernelTerm::variable(KernelType::Bool, Variable(10993736));
        for depth in [0, 1, 2, 3] {
            let mut root = base.clone();
            for _ in 0..depth {
                root = KernelTerm::boolean_if_raw([
                    root,
                    KernelTermImport::default().condition(&ConditionTerm::Constant(false)),
                    KernelTermImport::default().condition(&ConditionTerm::Constant(true)),
                ]);
            }
            for literal in [false, true] {
                for shared_literal in [false, true] {
                    let value = if shared_literal {
                        SpecValue::Shared(
                            KernelTermImport::default()
                                .condition(&ConditionTerm::Constant(literal)),
                        )
                    } else {
                        SpecValue::Native(ProgramValue::bool_constant(literal))
                    };
                    for operator in [ComparisonOperator::Equal, ComparisonOperator::NotEqual] {
                        for reverse in [false, true] {
                            let exports = KernelTermExport::machine_export_count();
                            let logical = SpecValue::Shared(root.clone());
                            let output = if reverse {
                                value.comparison(operator, &logical)
                            } else {
                                logical.comparison(operator, &value)
                            }
                            .unwrap()
                            .unwrap();
                            let Proposition::ConditionIs(condition, truth) = output else {
                                unreachable!();
                            };
                            assert_eq!(condition.root(), Some(&base));
                            assert_eq!(
                                truth,
                                (literal == (operator == ComparisonOperator::Equal))
                                    ^ (depth % 2 == 1)
                            );
                            assert_eq!(KernelTermExport::machine_export_count(), exports);
                            assert!(!root.has_cached_native_argument());
                        }
                    }
                }
            }
        }
    }

    mod scaling_tests {
        use super::*;
        include!("../../scaling_tests/kernel/spec/condition_output_storage.rs");
    }
}
