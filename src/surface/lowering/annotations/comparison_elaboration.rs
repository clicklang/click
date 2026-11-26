//! Elaborating and lowering a written comparison.
//!
//! Elaboration chooses the comparison's kind from both operands
//! (`design/typed-surface.md`); lowering then reads the kind and lowers each
//! operand the way the kind says, without inspecting the operands again.
use super::*;

impl AnnotationLowerer<'_> {
    /// Elaborate a proposition to Surface in the lowering context it is
    /// lowered in: its connectives, and each comparison directly under them
    /// with its kind. A comparison whose elaboration fails stays `Untyped`,
    /// so lowering reaches it where it did before and reports the same error
    /// in the same order. Connectives do not change the context, so each
    /// comparison is elaborated in the context lowering would use for it.
    pub(super) fn elaborate_proposition<'s>(
        &mut self,
        proposition: &'s SyntaxProposition,
        environment: &SpecElaborationContext,
    ) -> SurfaceProposition<'s> {
        let mut surface = crate::surface::elaborate_connectives(proposition);
        let mut pending = vec![&mut surface];
        while let Some(node) = pending.pop() {
            match node {
                SurfaceProposition::And(left, right)
                | SurfaceProposition::Or(left, right)
                | SurfaceProposition::Implies(left, right) => {
                    pending.push(right);
                    pending.push(left);
                }
                SurfaceProposition::Not(body) => pending.push(body),
                SurfaceProposition::Untyped(SyntaxProposition::Comparison {
                    left,
                    operator,
                    right,
                }) => {
                    if let Ok(comparison) =
                        self.elaborate_comparison(left, *operator, right, environment)
                    {
                        *node = comparison;
                    }
                }
                _ => {}
            }
        }
        surface
    }

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
            return Ok(SurfaceProposition::Comparison {
                kind: ComparisonKind::Integer,
                left: integer_surface_term(left.clone()),
                operator,
                right: integer_surface_term(right.clone()),
            });
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
            // One visit per node: a connective, an elaborated comparison, or
            // an untyped construct.
            #[cfg(test)]
            super::tests::PROPOSITION_VISITS.with(|visits| visits.set(visits.get() + 1));
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

    /// Lower an Integer Surface term. Integer arithmetic is lowered as
    /// `lower_contract_integer_to_spec` lowers it: one unit of integer work,
    /// then the operands, combined over Integer terms when both are terms.
    /// An `Untyped` term is lowered by that Syntax lowering.
    fn lower_surface_integer(
        &mut self,
        term: &SurfaceTerm,
        environment: &SpecElaborationContext,
    ) -> Result<crate::kernel::SpecIntegerExpression, String> {
        use crate::kernel::SpecIntegerExpression;
        match term {
            SurfaceTerm::Untyped(syntax) => {
                self.lower_contract_integer_to_spec(syntax, environment)
            }
            SurfaceTerm::Negate {
                kind: ArithmeticKind::Integer,
                operand,
            } => {
                check_integer_lowering_work(1)?;
                match self.lower_surface_integer(operand, environment)? {
                    SpecIntegerExpression::Term(term) => {
                        check_integer_lowering_work(integer_root_work(&term))?;
                        construct_integer_operation(
                            crate::kernel::KernelIntegerOperator::Negate,
                            vec![term],
                        )
                    }
                    inner => Ok(SpecIntegerExpression::Negate(Box::new(inner))),
                }
            }
            SurfaceTerm::Binary {
                op,
                kind: ArithmeticKind::Integer,
                left,
                right,
            } => {
                check_integer_lowering_work(1)?;
                let left = self.lower_surface_integer(left, environment)?;
                let right = self.lower_surface_integer(right, environment)?;
                let operation = match op {
                    ArithmeticOperator::Add => IntegerOperation::Add,
                    ArithmeticOperator::Subtract => IntegerOperation::Subtract,
                    ArithmeticOperator::Multiply => IntegerOperation::Multiply,
                };
                match (&left, &right) {
                    (SpecIntegerExpression::Term(_), SpecIntegerExpression::Term(_)) => {
                        lower_integer_operation(left, right, operation)
                    }
                    _ => Ok(match operation {
                        IntegerOperation::Add => {
                            SpecIntegerExpression::Add(Box::new(left), Box::new(right))
                        }
                        IntegerOperation::Subtract => {
                            SpecIntegerExpression::Subtract(Box::new(left), Box::new(right))
                        }
                        IntegerOperation::Multiply => {
                            SpecIntegerExpression::Multiply(Box::new(left), Box::new(right))
                        }
                    }),
                }
            }
        }
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
        if kind == ComparisonKind::Integer {
            return Ok(SpecProposition::IntegerComparison {
                left: self.lower_surface_integer(left, environment)?,
                operator: integer_comparison_operator(operator)?,
                right: self.lower_surface_integer(right, environment)?,
            });
        }
        let (left, right) = (left.untyped_syntax(), right.untyped_syntax());
        let equal = operator == ComparisonOperator::Equal;
        match kind {
            ComparisonKind::Integer => unreachable!("lowered above"),
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

/// The Integer Surface form of an operand of an Integer comparison: its `+`,
/// `-`, `*` and negation are Integer arithmetic, and every other construct
/// stays `Untyped`. A negated literal stays `Untyped`: lowering reads it as
/// the literal `-n`, not as a negation.
fn integer_surface_term(term: SyntaxTerm) -> SurfaceTerm {
    let binary = |op, left: Box<SyntaxTerm>, right: Box<SyntaxTerm>| SurfaceTerm::Binary {
        op,
        kind: ArithmeticKind::Integer,
        left: Box::new(integer_surface_term(*left)),
        right: Box::new(integer_surface_term(*right)),
    };
    if matches!(term, SyntaxTerm::Negate(_)) && integer_literal_spelling(&term).is_some() {
        return SurfaceTerm::Untyped(term);
    }
    match term {
        SyntaxTerm::Add(left, right) => binary(ArithmeticOperator::Add, left, right),
        SyntaxTerm::Subtract(left, right) => binary(ArithmeticOperator::Subtract, left, right),
        SyntaxTerm::Multiply(left, right) => binary(ArithmeticOperator::Multiply, left, right),
        SyntaxTerm::Negate(operand) => SurfaceTerm::Negate {
            kind: ArithmeticKind::Integer,
            operand: Box::new(integer_surface_term(*operand)),
        },
        term => SurfaceTerm::Untyped(term),
    }
}
