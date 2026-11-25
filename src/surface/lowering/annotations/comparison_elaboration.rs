//! Elaborating and lowering a written comparison.
//!
//! Elaboration chooses the comparison's kind from both operands
//! (`design/typed-surface.md`); lowering then reads the kind and lowers each
//! operand the way the kind says, without inspecting the operands again.
use super::*;

impl AnnotationLowerer<'_> {
    /// The typed Surface form of `left operator right`.
    pub(super) fn elaborate_comparison(
        &mut self,
        left: &SyntaxTerm,
        operator: ComparisonOperator,
        right: &SyntaxTerm,
        environment: &SpecElaborationContext,
    ) -> Result<SurfaceProposition, String> {
        let comparison = |kind| {
            Ok(SurfaceProposition::Comparison {
                kind,
                left: SurfaceTerm::Untyped(left.clone()),
                operator,
                right: SurfaceTerm::Untyped(right.clone()),
            })
        };
        if let (Some(left_element), Some(right_element)) = (
            self.contract_pointer_element_type(left, &TypingEnvironment::of(environment)),
            self.contract_pointer_element_type(right, &TypingEnvironment::of(environment)),
        ) && left_element != right_element
        {
            return Err(format!(
                "incompatible pointer comparison: {:?} pointer and {:?} pointer; use a checked byte-view cast to compare byte views",
                left_element, right_element
            ));
        }
        if operator == ComparisonOperator::In {
            return comparison(ComparisonKind::Sequence);
        }
        let left_is_integer =
            self.contract_expression_is_integer(left, &TypingEnvironment::of(environment));
        let right_is_integer =
            self.contract_expression_is_integer(right, &TypingEnvironment::of(environment));
        let left_is_integer = left_is_integer
            || (right_is_integer && matches!(left, SyntaxTerm::AlgebraicMatch { .. }));
        let right_is_integer = right_is_integer
            || (left_is_integer && matches!(right, SyntaxTerm::AlgebraicMatch { .. }));
        if left_is_integer || right_is_integer {
            if left_is_integer != right_is_integer
                && !(if left_is_integer {
                    is_unsuffixed_integer_literal_expression(right)
                } else {
                    is_unsuffixed_integer_literal_expression(left)
                })
            {
                return Err(
                    "mathematical Integer expressions cannot be compared with C values".to_string(),
                );
            }
            return comparison(ComparisonKind::Integer);
        }
        // Two values of one struct are equal when each field is: the
        // constructor is injective, so the comparison is its fields'.
        if matches!(
            operator,
            ComparisonOperator::Equal | ComparisonOperator::NotEqual
        ) && let (Some((left_type, left_fields)), Some((right_type, right_fields))) = (
            struct_constructor_fields(left),
            struct_constructor_fields(right),
        ) && left_type == right_type
            && left_fields.len() == right_fields.len()
            && !left_fields.is_empty()
            && crate::surface::struct_values::field_names(&left_type).is_some()
        {
            let mut fields = None;
            for (left, right) in left_fields.iter().zip(&right_fields) {
                let field =
                    self.elaborate_comparison(left, ComparisonOperator::Equal, right, environment)?;
                fields = Some(match fields {
                    None => field,
                    Some(before) => SurfaceProposition::And(Box::new(before), Box::new(field)),
                });
            }
            let equal = fields.expect("a struct value has a field");
            return Ok(if operator == ComparisonOperator::Equal {
                equal
            } else {
                SurfaceProposition::Not(Box::new(equal))
            });
        }
        let has_algebraic = self.enum_program_value_type(left, environment).is_some()
            || self.enum_program_value_type(right, environment).is_some()
            || contract_expression_is_algebraic(
                left,
                self.spec_definitions.functions,
                &TypingEnvironment::of(environment),
                &mut Vec::new(),
            )
            || contract_expression_is_algebraic(
                right,
                self.spec_definitions.functions,
                &TypingEnvironment::of(environment),
                &mut Vec::new(),
            )
            || self.generic_call_returns_algebraic(left, environment)
            || self.generic_call_returns_algebraic(right, environment);
        let equality_only = |kind, message: &str| {
            if matches!(
                operator,
                ComparisonOperator::Equal | ComparisonOperator::NotEqual
            ) {
                comparison(kind)
            } else {
                Err(message.to_string())
            }
        };
        if has_algebraic {
            return equality_only(
                ComparisonKind::Algebraic,
                "algebraic values support only `==` and `!=` comparisons",
            );
        }
        if contract_expression_is_sequence(left) || contract_expression_is_sequence(right) {
            return equality_only(
                ComparisonKind::Sequence,
                "sequences support only `==` and `!=` comparisons",
            );
        }
        comparison(ComparisonKind::Native)
    }

    /// Lower an elaborated comparison. Each operand is lowered as its
    /// comparison's kind says; nothing here looks at the operands to decide.
    pub(super) fn lower_surface_proposition(
        &mut self,
        proposition: &SurfaceProposition,
        environment: &SpecElaborationContext,
    ) -> Result<SpecProposition, String> {
        match proposition {
            SurfaceProposition::And(left, right) => Ok(SpecProposition::And(
                Box::new(self.lower_surface_proposition(left, environment)?),
                Box::new(self.lower_surface_proposition(right, environment)?),
            )),
            SurfaceProposition::Not(body) => Ok(SpecProposition::Not(Box::new(
                self.lower_surface_proposition(body, environment)?,
            ))),
            SurfaceProposition::Comparison {
                kind,
                left,
                operator,
                right,
            } => {
                let (left, right) = (left.syntax(), right.syntax());
                let equal = *operator == ComparisonOperator::Equal;
                match kind {
                    ComparisonKind::Integer => Ok(SpecProposition::IntegerComparison {
                        left: self.lower_contract_integer_to_spec(left, environment)?,
                        operator: integer_comparison_operator(*operator)?,
                        right: self.lower_contract_integer_to_spec(right, environment)?,
                    }),
                    ComparisonKind::Algebraic => Ok(SpecProposition::AlgebraicComparison {
                        left: self.lower_contract_algebraic_to_spec(left, environment)?,
                        equal,
                        right: self.lower_contract_algebraic_to_spec(right, environment)?,
                    }),
                    ComparisonKind::Sequence if *operator == ComparisonOperator::In => {
                        Ok(SpecProposition::SequenceMembership {
                            element: self.lower_contract_expression_to_spec(left, environment)?,
                            sequence: self.lower_contract_sequence_to_spec(right, environment)?,
                        })
                    }
                    ComparisonKind::Sequence => Ok(SpecProposition::SequenceComparison {
                        left: self.lower_contract_sequence_to_spec(left, environment)?,
                        equal,
                        right: self.lower_contract_sequence_to_spec(right, environment)?,
                    }),
                    ComparisonKind::Native => Ok(SpecProposition::Comparison {
                        left: self.lower_contract_expression_to_spec(left, environment)?,
                        operator: c_comparison_operator(*operator),
                        right: self.lower_contract_expression_to_spec(right, environment)?,
                    }),
                }
            }
        }
    }
}
