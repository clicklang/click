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
    ) -> Result<SurfaceProposition<'static>, String> {
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
        let has_algebraic = self
            .enum_program_value_type(left, &TypingEnvironment::of(environment))
            .is_some()
            || self
                .enum_program_value_type(right, &TypingEnvironment::of(environment))
                .is_some()
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

    /// Lower a Surface proposition. Connectives are lowered here, each over
    /// its operands' lowerings; a comparison by its elaborated kind; an
    /// `Untyped` construct by the Syntax lowering it had before it moved to
    /// Surface. Iterative, so a long chain needs no deep stack.
    pub(super) fn lower_surface_proposition(
        &mut self,
        proposition: &SurfaceProposition<'_>,
        environment: &SpecElaborationContext,
    ) -> Result<SpecProposition, String> {
        enum Frame<'p, 's> {
            Visit(&'p SurfaceProposition<'s>),
            BuildAnd,
            BuildOr,
            BuildImplies,
            BuildNot,
        }
        let mut frames = vec![Frame::Visit(proposition)];
        let mut lowered = Vec::new();
        while let Some(frame) = frames.pop() {
            let visit = match frame {
                Frame::Visit(visit) => visit,
                Frame::BuildNot => {
                    let body = lowered.pop().expect("lowered negation body");
                    lowered.push(SpecProposition::Not(Box::new(body)));
                    continue;
                }
                frame => {
                    let right = Box::new(lowered.pop().expect("lowered right operand"));
                    let left = Box::new(lowered.pop().expect("lowered left operand"));
                    lowered.push(match frame {
                        Frame::BuildAnd => SpecProposition::And(left, right),
                        Frame::BuildOr => SpecProposition::Or(left, right),
                        _ => SpecProposition::Implies(left, right),
                    });
                    continue;
                }
            };
            // One visit per connective and per Syntax construct, as before
            // connectives moved to Surface. A comparison node is lowered
            // inside its own construct's visit.
            #[cfg(test)]
            if !matches!(visit, SurfaceProposition::Comparison { .. }) {
                super::tests::PROPOSITION_VISITS.with(|visits| visits.set(visits.get() + 1));
            }
            match visit {
                SurfaceProposition::And(left, right) => {
                    frames.extend([Frame::BuildAnd, Frame::Visit(right), Frame::Visit(left)]);
                }
                SurfaceProposition::Or(left, right) => {
                    frames.extend([Frame::BuildOr, Frame::Visit(right), Frame::Visit(left)]);
                }
                SurfaceProposition::Implies(left, right) => {
                    frames.extend([Frame::BuildImplies, Frame::Visit(right), Frame::Visit(left)]);
                }
                SurfaceProposition::Not(body) => {
                    frames.extend([Frame::BuildNot, Frame::Visit(body)]);
                }
                SurfaceProposition::Untyped(syntax) => {
                    lowered
                        .push(self.click_proposition_to_spec_proposition_one(syntax, environment)?);
                }
                SurfaceProposition::Comparison {
                    kind,
                    left,
                    operator,
                    right,
                } => {
                    lowered.push(self.lower_surface_comparison(
                        *kind,
                        left,
                        *operator,
                        right,
                        environment,
                    )?);
                }
            }
        }
        Ok(lowered.pop().expect("lowered proposition has one root"))
    }

    /// Lower an elaborated comparison. Each operand is lowered as its
    /// comparison's kind says; nothing here looks at the operands to decide.
    fn lower_surface_comparison(
        &mut self,
        kind: ComparisonKind,
        left: &SurfaceTerm,
        operator: ComparisonOperator,
        right: &SurfaceTerm,
        environment: &SpecElaborationContext,
    ) -> Result<SpecProposition, String> {
        let (left, right) = (left.syntax(), right.syntax());
        let equal = operator == ComparisonOperator::Equal;
        match kind {
            ComparisonKind::Integer => Ok(SpecProposition::IntegerComparison {
                left: self.lower_contract_integer_to_spec(left, environment)?,
                operator: integer_comparison_operator(operator)?,
                right: self.lower_contract_integer_to_spec(right, environment)?,
            }),
            ComparisonKind::Algebraic => Ok(SpecProposition::AlgebraicComparison {
                left: self.lower_contract_algebraic_to_spec(left, environment)?,
                equal,
                right: self.lower_contract_algebraic_to_spec(right, environment)?,
            }),
            ComparisonKind::Sequence if operator == ComparisonOperator::In => {
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
                operator: c_comparison_operator(operator),
                right: self.lower_contract_expression_to_spec(right, environment)?,
            }),
        }
    }
}
