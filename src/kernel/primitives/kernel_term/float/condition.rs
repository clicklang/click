//! Structural floating-point predicates. Comparison and classification are
//! distinct operations: neither import nor a shape read evaluates IEEE values.
use super::*;

impl KernelFloatType {
    pub(in crate::kernel::primitives) fn exponent_and_fraction_widths(self) -> (u32, u32) {
        match self {
            Self::Float32 => (8, 23),
            Self::Float64 => (11, 52),
        }
    }

    pub(crate) fn classify_bits(self, bits: u64, classification: FloatClassification) -> bool {
        let (exponent_bits, fraction_bits) = self.exponent_and_fraction_widths();
        let exponent_mask = (1u64 << exponent_bits) - 1;
        let exponent = (bits >> fraction_bits) & exponent_mask;
        let fraction = bits & ((1u64 << fraction_bits) - 1);
        let all_ones = exponent == exponent_mask;
        let zero_exponent = exponent == 0;
        match classification {
            FloatClassification::Finite => !all_ones,
            FloatClassification::Infinite => all_ones && fraction == 0,
            FloatClassification::Zero => zero_exponent && fraction == 0,
            FloatClassification::Subnormal => zero_exponent && fraction != 0,
            FloatClassification::Nan => all_ones && fraction != 0,
        }
    }

    pub(crate) fn compare_bits(self, left: u64, right: u64, operator: ComparisonOperator) -> bool {
        let nan = FloatClassification::Nan;
        let left_nan = self.classify_bits(left, nan);
        let right_nan = self.classify_bits(right, nan);
        if left_nan || right_nan {
            return matches!(operator, ComparisonOperator::NotEqual);
        }

        let left_zero = self.classify_bits(left, FloatClassification::Zero);
        let right_zero = self.classify_bits(right, FloatClassification::Zero);
        let equal = (left_zero && right_zero) || left == right;
        if equal {
            return matches!(
                operator,
                ComparisonOperator::Equal
                    | ComparisonOperator::LessEqual
                    | ComparisonOperator::GreaterEqual
            );
        }

        // Order the two payloads by the usual monotone key: complement a negative
        // encoding, set the sign bit of a non-negative one. The complement has to
        // stay inside the format's own width, since these payloads sit in a `u64`
        // that is wider than every format except binary64. Complementing all 64
        // bits of a binary32 payload would raise every negative value above every
        // non-negative one, making `-1.0f < 1.0f` false.
        let (exponent_bits, fraction_bits) = self.exponent_and_fraction_widths();
        let width = exponent_bits + fraction_bits + 1;
        let payload_mask = if width >= u64::BITS {
            u64::MAX
        } else {
            (1u64 << width) - 1
        };
        let sign_bit = 1u64 << (exponent_bits + fraction_bits);
        let ordering_key = |bits: u64| {
            if bits & sign_bit != 0 {
                !bits & payload_mask
            } else {
                bits ^ sign_bit
            }
        };
        let left_key = ordering_key(left);
        let right_key = ordering_key(right);
        match operator {
            ComparisonOperator::Equal => false,
            ComparisonOperator::NotEqual => true,
            ComparisonOperator::LessThan => left_key < right_key,
            ComparisonOperator::LessEqual => left_key <= right_key,
            ComparisonOperator::GreaterThan => left_key > right_key,
            ComparisonOperator::GreaterEqual => left_key >= right_key,
        }
    }
}

impl KernelTerm {
    pub(crate) fn float_compare(
        format: KernelFloatType,
        operator: ComparisonOperator,
        arguments: [Self; 2],
    ) -> Result<Self, &'static str> {
        if arguments
            .iter()
            .any(|arg| arg.ty() != &KernelType::Program(format.program_type()))
        {
            return Err("float comparison operand type");
        }
        Ok(Self::intern(
            KernelType::Bool,
            KernelTermNode::FloatCompare {
                format,
                operator,
                arguments,
            },
        ))
    }

    pub(crate) fn float_classify(
        format: KernelFloatType,
        classification: FloatClassification,
        operand: Self,
    ) -> Result<Self, &'static str> {
        if operand.ty() != &KernelType::Program(format.program_type()) {
            return Err("float classification operand type");
        }
        Ok(Self::intern(
            KernelType::Bool,
            KernelTermNode::FloatClassify {
                format,
                classification,
                operand,
            },
        ))
    }
}

impl KernelTermImport {
    pub(in crate::kernel::primitives::kernel_term) fn float_condition(
        &mut self,
        format: KernelFloatType,
        value: &FloatCondition,
    ) -> KernelTerm {
        match value {
            FloatCondition::Comparison {
                operator,
                left,
                right,
            } => KernelTerm::float_compare(
                format,
                *operator,
                [self.float(format, left), self.float(format, right)],
            ),
            FloatCondition::Classification {
                classification,
                value,
            } => KernelTerm::float_classify(format, *classification, self.float(format, value)),
        }
        .expect("imported float predicate operands")
    }
}

impl KernelTermExport {
    pub(in crate::kernel::primitives::kernel_term) fn float_condition(
        root: &KernelTerm,
    ) -> Result<OldConditionTerm, &'static str> {
        let (format, value) = match root.node() {
            KernelTermNode::FloatCompare {
                format,
                operator,
                arguments,
            } => (
                *format,
                FloatCondition::Comparison {
                    operator: *operator,
                    left: Box::new(Self::float_machine(&arguments[0])?),
                    right: Box::new(Self::float_machine(&arguments[1])?),
                },
            ),
            KernelTermNode::FloatClassify {
                format,
                classification,
                operand,
            } => (
                *format,
                FloatCondition::Classification {
                    classification: *classification,
                    value: Box::new(Self::float_machine(operand)?),
                },
            ),
            _ => return Err("expected float predicate"),
        };
        Ok(match format {
            KernelFloatType::Float32 => OldConditionTerm::Float32(value),
            KernelFloatType::Float64 => OldConditionTerm::Float64(value),
        })
    }
}

impl FloatOperandView<'_> {
    /// Classify an evaluated operand. The native evaluator can select a
    /// constant arm of an If. Shared roots fold only closed arithmetic.
    pub(crate) fn evaluated_classification(
        self,
        classification: FloatClassification,
    ) -> KernelTerm {
        let format = self.format();
        let bits = match self {
            Self::Native(..) => self.constant_bits(),
            Self::Shared(_) => self.closed_arithmetic_bits(),
        };
        if let Some(bits) = bits {
            return KernelTerm::boolean_literal(format.classify_bits(bits, classification));
        }
        let operand = match self {
            Self::Native(_, term) => KernelTermImport::for_exact_field_inputs().float(format, term),
            Self::Shared(root) => root.clone(),
        };
        KernelTerm::float_classify(format, classification, operand)
            .expect("float classification operand")
    }
}

impl<'a> BooleanOperandView<'a> {
    /// Check a closed float predicate at its written precision. Symbolic
    /// leaves keep their ordinary comparison and classification rules.
    pub(crate) fn closed_float_predicate_value(self) -> Option<bool> {
        if let Some((format, operator, [left, right])) = self.float_comparison() {
            return Some(format.compare_bits(
                left.closed_arithmetic_bits()?,
                right.closed_arithmetic_bits()?,
                operator,
            ));
        }
        let (format, classification, operand) = self.float_classification()?;
        Some(format.classify_bits(operand.closed_arithmetic_bits()?, classification))
    }

    pub(crate) fn float_comparison(
        self,
    ) -> Option<(
        KernelFloatType,
        ComparisonOperator,
        [FloatOperandView<'a>; 2],
    )> {
        if let Self::Shared(root) = self
            && let KernelTermNode::FloatCompare {
                format,
                operator,
                arguments,
            } = root.node()
        {
            return Some((
                *format,
                *operator,
                arguments.each_ref().map(FloatOperandView::Shared),
            ));
        }
        let (format, condition) = match self.native_leaf()? {
            OldConditionTerm::Float32(value) => (KernelFloatType::Float32, value),
            OldConditionTerm::Float64(value) => (KernelFloatType::Float64, value),
            _ => return None,
        };
        let FloatCondition::Comparison {
            operator,
            left,
            right,
        } = condition
        else {
            return None;
        };
        Some((
            format,
            *operator,
            [
                FloatOperandView::Native(format, left),
                FloatOperandView::Native(format, right),
            ],
        ))
    }

    pub(crate) fn float_classification(
        self,
    ) -> Option<(KernelFloatType, FloatClassification, FloatOperandView<'a>)> {
        if let Self::Shared(root) = self
            && let KernelTermNode::FloatClassify {
                format,
                classification,
                operand,
            } = root.node()
        {
            return Some((*format, *classification, FloatOperandView::Shared(operand)));
        }
        let (format, condition) = match self.native_leaf()? {
            OldConditionTerm::Float32(value) => (KernelFloatType::Float32, value),
            OldConditionTerm::Float64(value) => (KernelFloatType::Float64, value),
            _ => return None,
        };
        let FloatCondition::Classification {
            classification,
            value,
        } = condition
        else {
            return None;
        };
        Some((
            format,
            *classification,
            FloatOperandView::Native(format, value),
        ))
    }
}

impl FloatOperandView<'_> {
    /// Native syntax identity, not IEEE numeric equality (NaNs and signed zero
    /// are therefore never folded here). Normalize only observation metadata.
    pub(crate) fn syntax_equal(self, other: Self) -> bool {
        if self.format() != other.format() {
            return false;
        }
        let root = |view| match view {
            Self::Shared(root) => root.clone(),
            Self::Native(format, value) => KernelTermImport::default().float(format, value),
        };
        let a = root(self);
        let b = root(other);
        crate::kernel::primitives::integer::observation_identity::normalize(&a)
            == crate::kernel::primitives::integer::observation_identity::normalize(&b)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn float_predicates_retain_raw_nan_zero_and_conversion_operands() {
        let _session = crate::kernel::VerificationSession::enter();
        for format in [KernelFloatType::Float32, KernelFloatType::Float64] {
            let mut values = match format {
                KernelFloatType::Float32 => [
                    OldMachineTerm::constant(0x7fc01234),
                    OldMachineTerm::constant(0x80000000),
                    OldMachineTerm::constant(0),
                ],
                KernelFloatType::Float64 => [
                    OldMachineTerm::uint64_constant(0x7ff8000000001234),
                    OldMachineTerm::uint64_constant(0x8000000000000000),
                    OldMachineTerm::uint64_constant(0),
                ],
            }
            .to_vec();
            values.push(OldMachineTerm::opaque_conversion(
                match format {
                    KernelFloatType::Float32 => "c_int32_to_float32",
                    KernelFloatType::Float64 => "c_int32_to_float64",
                },
                OldMachineTerm::Variable(Variable(999979)),
            ));
            for value in values {
                let mut predicates = vec![];
                for operator in [
                    ComparisonOperator::Equal,
                    ComparisonOperator::NotEqual,
                    ComparisonOperator::LessThan,
                    ComparisonOperator::LessEqual,
                    ComparisonOperator::GreaterThan,
                    ComparisonOperator::GreaterEqual,
                ] {
                    predicates.push(FloatCondition::Comparison {
                        operator,
                        left: Box::new(value.clone()),
                        right: Box::new(value.clone()),
                    });
                }
                for classification in [
                    FloatClassification::Finite,
                    FloatClassification::Infinite,
                    FloatClassification::Zero,
                    FloatClassification::Subnormal,
                    FloatClassification::Nan,
                ] {
                    predicates.push(FloatCondition::Classification {
                        classification,
                        value: Box::new(value.clone()),
                    });
                }
                for predicate in predicates {
                    let native = match format {
                        KernelFloatType::Float32 => OldConditionTerm::Float32(predicate),
                        KernelFloatType::Float64 => OldConditionTerm::Float64(predicate),
                    };
                    let root = KernelTermImport::default().condition(&native);
                    let before = KernelTermExport::machine_export_count();
                    assert!(
                        BooleanOperandView::Shared(&root)
                            .syntax_equal(BooleanOperandView::Native(&native))
                    );
                    assert_eq!(KernelTermExport::machine_export_count(), before);
                    assert_eq!(KernelTermExport::condition(&root).unwrap(), native);
                }
            }
        }
    }

    #[test]
    fn float_predicate_syntax_keeps_width_operator_and_zero_bits() {
        let _session = crate::kernel::VerificationSession::enter();
        let predicate = |format, value| {
            KernelTermImport::default().float_condition(
                format,
                &FloatCondition::Classification {
                    classification: FloatClassification::Zero,
                    value: Box::new(value),
                },
            )
        };
        let positive = predicate(KernelFloatType::Float32, OldMachineTerm::constant(0));
        let negative = predicate(
            KernelFloatType::Float32,
            OldMachineTerm::constant(0x80000000),
        );
        let wide = predicate(KernelFloatType::Float64, OldMachineTerm::uint64_constant(0));
        assert!(
            !BooleanOperandView::Shared(&positive)
                .syntax_equal(BooleanOperandView::Shared(&negative))
        );
        assert!(
            !BooleanOperandView::Shared(&positive).syntax_equal(BooleanOperandView::Shared(&wide))
        );
    }
}
