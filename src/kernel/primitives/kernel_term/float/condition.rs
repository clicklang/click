//! Structural floating-point predicates. Comparison and classification are
//! distinct operations: neither import nor a shape read evaluates IEEE values.
use super::*;

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
    ) -> Result<ConditionTerm, &'static str> {
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
            KernelFloatType::Float32 => ConditionTerm::Float32(value),
            KernelFloatType::Float64 => ConditionTerm::Float64(value),
        })
    }
}

impl<'a> BooleanOperandView<'a> {
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
            ConditionTerm::Float32(value) => (KernelFloatType::Float32, value),
            ConditionTerm::Float64(value) => (KernelFloatType::Float64, value),
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
            ConditionTerm::Float32(value) => (KernelFloatType::Float32, value),
            ConditionTerm::Float64(value) => (KernelFloatType::Float64, value),
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
                    MachineTerm::constant(0x7fc01234),
                    MachineTerm::constant(0x80000000),
                    MachineTerm::constant(0),
                ],
                KernelFloatType::Float64 => [
                    MachineTerm::uint64_constant(0x7ff8000000001234),
                    MachineTerm::uint64_constant(0x8000000000000000),
                    MachineTerm::uint64_constant(0),
                ],
            }
            .to_vec();
            values.push(MachineTerm::opaque_conversion(
                match format {
                    KernelFloatType::Float32 => "c_int32_to_float32",
                    KernelFloatType::Float64 => "c_int32_to_float64",
                },
                MachineTerm::Variable(Variable(999979)),
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
                        KernelFloatType::Float32 => ConditionTerm::Float32(predicate),
                        KernelFloatType::Float64 => ConditionTerm::Float64(predicate),
                    };
                    let root = KernelTermImport::default().condition(&native);
                    assert!(!matches!(root.node(), KernelTermNode::LegacyBool(_)));
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
        let positive = predicate(KernelFloatType::Float32, MachineTerm::constant(0));
        let negative = predicate(KernelFloatType::Float32, MachineTerm::constant(0x80000000));
        let wide = predicate(KernelFloatType::Float64, MachineTerm::uint64_constant(0));
        assert!(
            !BooleanOperandView::Shared(&positive)
                .syntax_equal(BooleanOperandView::Shared(&negative))
        );
        assert!(
            !BooleanOperandView::Shared(&positive).syntax_equal(BooleanOperandView::Shared(&wide))
        );
    }
}
