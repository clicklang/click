use super::*;
use crate::kernel::{bits32_constant, constant_u32};
use crate::surface::PredicateEnvironment;
use std::collections::BTreeSet;

pub(in crate::surface) fn program_expression_uses_variable(
    expression: &ProgramExpression,
    variable: &(impl binders::BinderKey + ?Sized),
) -> bool {
    match expression {
        ProgramExpression::StringLiteral(_)
        | ProgramExpression::Value(_)
        | ProgramExpression::FunctionAddress(_)
        | ProgramExpression::StepResult { .. } => false,
        ProgramExpression::Variable(name) => match (name, variable.binder_key()) {
            (
                crate::kernel::BindingName::Named(name),
                Some(binders::BinderKeyRef::Written(variable)),
            ) => name == variable,
            (
                crate::kernel::BindingName::Generated(id),
                Some(binders::BinderKeyRef::Generated(variable)),
            ) => id == variable,
            _ => false,
        },
        ProgramExpression::Cast { expression, .. } => {
            program_expression_uses_variable(expression, variable)
        }
        ProgramExpression::Negate(expression)
        | ProgramExpression::FloatNegate(expression)
        | ProgramExpression::FloatClassification { expression, .. }
        | ProgramExpression::EnumField {
            value: expression, ..
        }
        | ProgramExpression::EnumIs {
            value: expression, ..
        } => program_expression_uses_variable(expression, variable),
        ProgramExpression::EnumConstruct { fields, .. } => fields
            .iter()
            .any(|field| program_expression_uses_variable(field, variable)),
        ProgramExpression::Ternary {
            condition,
            then_branch,
            else_branch,
        } => {
            program_expression_uses_variable(condition, variable)
                || program_expression_uses_variable(then_branch, variable)
                || program_expression_uses_variable(else_branch, variable)
        }
        ProgramExpression::AddressOf(expression)
        | ProgramExpression::CheckedObjectAddress(expression)
        | ProgramExpression::Not(expression)
        | ProgramExpression::BitwiseNot(expression)
        | ProgramExpression::Load(expression)
        | ProgramExpression::TypedLoad {
            pointer: expression,
            ..
        }
        | ProgramExpression::PointerOffsetBytes {
            pointer: expression,
            ..
        }
        | ProgramExpression::Subobject {
            pointer: expression,
            ..
        } => program_expression_uses_variable(expression, variable),
        crate::kernel::binary_c_expression!(left, right) => {
            program_expression_uses_variable(left, variable)
                || program_expression_uses_variable(right, variable)
        }
    }
}

pub(in crate::surface) fn contains_old_expression(expression: &SurfaceTerm) -> bool {
    match expression {
        SurfaceTerm::IntegerContext(value) => contains_old_expression(value),

        SurfaceTerm::Proposition(proposition) => proposition_contains_old_expression(proposition),
        SurfaceTerm::Resource(subject) => resource_subject_contains_old_expression(subject),
        SurfaceTerm::RegionResult(_)
        | SurfaceTerm::RegionAllocation(_)
        | SurfaceTerm::RegionParameter { .. } => false,
        SurfaceTerm::Lambda { body, .. } => contains_old_expression(body),
        SurfaceTerm::Apply {
            function,
            arguments,
        } => contains_old_expression(function) || arguments.iter().any(contains_old_expression),

        SurfaceTerm::IntegerLiteral(_) => false,
        SurfaceTerm::CUnary { operand: inner, .. }
        | SurfaceTerm::MemoryLoad { pointer: inner, .. }
        | SurfaceTerm::Negate(inner) => contains_old_expression(inner),
        SurfaceTerm::ResourceField(_)
        | SurfaceTerm::AlgebraicVariable { .. }
        | SurfaceTerm::Binding(_) => false,
        SurfaceTerm::AlgebraicConstructor { arguments, .. } => {
            arguments.iter().any(contains_old_expression)
        }
        SurfaceTerm::AlgebraicMatch { scrutinee, arms } => {
            contains_old_expression(scrutinee)
                || arms.iter().any(|arm| contains_old_expression(&arm.body))
        }
        SurfaceTerm::SequenceLiteral(elements) => elements.iter().any(contains_old_expression),
        SurfaceTerm::SequenceConcat(left, right) => {
            contains_old_expression(left) || contains_old_expression(right)
        }
        SurfaceTerm::Old(_) => true,
        SurfaceTerm::Exact(place) => contains_old_expression(place),
        SurfaceTerm::QualifiedC { .. }
        | SurfaceTerm::ProgramExpression(_)
        | SurfaceTerm::ProgramBinding(_)
        | SurfaceTerm::ResourceWildcard => false,
        SurfaceTerm::ResourceCount(resource) => match resource.as_ref() {
            ResourceClause::Declared { arguments, .. } => {
                arguments.iter().any(contains_old_expression)
            }
            _ => false,
        },
        SurfaceTerm::Field { base, .. } => contains_old_expression(base),
        SurfaceTerm::ArrayIndex { base, .. } => contains_old_expression(base),
        SurfaceTerm::At { expression, .. } => contains_old_expression(expression),
        crate::surface::binary_contract_expression!(left, right) => {
            contains_old_expression(left) || contains_old_expression(right)
        }
        SurfaceTerm::BitwiseNot(expression) => contains_old_expression(expression),
        SurfaceTerm::If {
            condition,
            then_branch,
            else_branch,
        } => {
            proposition_contains_old_expression(condition)
                || contains_old_expression(then_branch)
                || contains_old_expression(else_branch)
        }
        SurfaceTerm::RangeFold {
            start,
            end,
            initial,
            body,
            ..
        } => {
            contains_old_expression(start)
                || contains_old_expression(end)
                || contains_old_expression(initial)
                || contains_old_expression(body)
        }
        SurfaceTerm::Let { value, body, .. } => {
            contains_old_expression(value) || contains_old_expression(body)
        }
        SurfaceTerm::MethodCall {
            receiver,
            arguments,
            ..
        } => contains_old_expression(receiver) || arguments.iter().any(contains_old_expression),
        SurfaceTerm::Call { arguments, .. } => arguments.iter().any(contains_old_expression),
    }
}

pub(in crate::surface) fn contains_resource_count(expression: &SurfaceTerm) -> bool {
    match expression {
        SurfaceTerm::IntegerContext(value) => contains_resource_count(value),

        SurfaceTerm::Proposition(proposition) => proposition_contains_resource_count(proposition),
        SurfaceTerm::Resource(_) => false,
        SurfaceTerm::RegionResult(_)
        | SurfaceTerm::RegionAllocation(_)
        | SurfaceTerm::RegionParameter { .. } => false,
        SurfaceTerm::Lambda { body, .. } => contains_resource_count(body),
        SurfaceTerm::Apply {
            function,
            arguments,
        } => contains_resource_count(function) || arguments.iter().any(contains_resource_count),

        SurfaceTerm::IntegerLiteral(_) => false,
        SurfaceTerm::CUnary { operand: inner, .. }
        | SurfaceTerm::MemoryLoad { pointer: inner, .. }
        | SurfaceTerm::Negate(inner) => contains_resource_count(inner),
        SurfaceTerm::ResourceField(_)
        | SurfaceTerm::AlgebraicVariable { .. }
        | SurfaceTerm::Binding(_) => false,
        SurfaceTerm::AlgebraicConstructor { arguments, .. } => {
            arguments.iter().any(contains_resource_count)
        }
        SurfaceTerm::AlgebraicMatch { scrutinee, arms } => {
            contains_resource_count(scrutinee)
                || arms.iter().any(|arm| contains_resource_count(&arm.body))
        }
        SurfaceTerm::SequenceLiteral(elements) => elements.iter().any(contains_resource_count),
        SurfaceTerm::SequenceConcat(left, right) => {
            contains_resource_count(left) || contains_resource_count(right)
        }
        SurfaceTerm::ResourceCount(_) => true,
        SurfaceTerm::QualifiedC { .. }
        | SurfaceTerm::ProgramExpression(_)
        | SurfaceTerm::ProgramBinding(_)
        | SurfaceTerm::ResourceWildcard => false,
        SurfaceTerm::Field { base, .. }
        | SurfaceTerm::Old(base)
        | SurfaceTerm::Exact(base)
        | SurfaceTerm::At {
            expression: base, ..
        }
        | SurfaceTerm::BitwiseNot(base) => contains_resource_count(base),
        SurfaceTerm::ArrayIndex { base, .. } => contains_resource_count(base),
        crate::surface::binary_contract_expression!(left, right) => {
            contains_resource_count(left) || contains_resource_count(right)
        }
        SurfaceTerm::If {
            condition,
            then_branch,
            else_branch,
        } => {
            proposition_contains_resource_count(condition)
                || contains_resource_count(then_branch)
                || contains_resource_count(else_branch)
        }
        SurfaceTerm::RangeFold {
            start,
            end,
            initial,
            body,
            ..
        } => {
            contains_resource_count(start)
                || contains_resource_count(end)
                || contains_resource_count(initial)
                || contains_resource_count(body)
        }
        SurfaceTerm::Let { value, body, .. } => {
            contains_resource_count(value) || contains_resource_count(body)
        }
        SurfaceTerm::MethodCall {
            receiver,
            arguments,
            ..
        } => contains_resource_count(receiver) || arguments.iter().any(contains_resource_count),
        SurfaceTerm::Call { arguments, .. } => arguments.iter().any(contains_resource_count),
    }
}

pub(in crate::surface) fn proposition_contains_resource_count(
    proposition: &SurfaceProposition,
) -> bool {
    match proposition {
        SurfaceProposition::Value(expression) => contains_resource_count(expression),
        SurfaceProposition::Comparison { left, right, .. } => {
            contains_resource_count(left) || contains_resource_count(right)
        }
        SurfaceProposition::FloatClassification { expression, .. } => {
            contains_resource_count(expression)
        }
        SurfaceProposition::Defined { expression }
        | SurfaceProposition::IsA {
            pointer: expression,
            ..
        } => contains_resource_count(expression),
        SurfaceProposition::At { proposition, .. }
        | SurfaceProposition::Not(proposition)
        | SurfaceProposition::ForAll {
            body: proposition, ..
        }
        | SurfaceProposition::Exists {
            body: proposition, ..
        } => proposition_contains_resource_count(proposition),
        SurfaceProposition::And(left, right)
        | SurfaceProposition::Or(left, right)
        | SurfaceProposition::Implies(left, right) => {
            proposition_contains_resource_count(left) || proposition_contains_resource_count(right)
        }
        SurfaceProposition::RangeAll {
            start, end, body, ..
        }
        | SurfaceProposition::RangeAny {
            start, end, body, ..
        } => {
            contains_resource_count(start)
                || contains_resource_count(end)
                || proposition_contains_resource_count(body)
        }
        SurfaceProposition::PredicateCall { arguments, .. } => {
            arguments.iter().any(contains_resource_count)
        }
        SurfaceProposition::Separate { .. }
        | SurfaceProposition::ResourceViewable { .. }
        | SurfaceProposition::Contains { .. }
        | SurfaceProposition::Loadable { .. } => false,
    }
}

/// Whether a proposition claims allocation liveness (`loadable(...)`),
/// directly or through a called predicate's body.
pub(in crate::surface) fn proposition_contains_liveness_claim(
    proposition: &SurfaceProposition,
    owned_bases: &[&ProgramExpression],
    predicate_environment: &PredicateEnvironment,
    visited_predicates: &mut BTreeSet<String>,
) -> bool {
    match proposition {
        SurfaceProposition::Value(expression) => {
            let mut calls = Vec::new();
            contract_expression_reads_memory(expression, &mut calls)
        }
        // Liveness of storage the body itself owns is stable under a borrow:
        // a live borrow over any of those bytes forbids freeing the
        // allocation. Liveness of anything else is not.
        SurfaceProposition::Loadable { segment } => {
            !owned_bases.iter().any(|base| **base == segment.base)
        }
        SurfaceProposition::ResourceViewable { resource } => match resource {
            ResourceSubject::Memory(segment) => {
                !owned_bases.iter().any(|base| **base == segment.base)
            }
            // A descriptor alone supplies no authority to keep its contents
            // live while a composite is lent out.
            _ => true,
        },
        SurfaceProposition::PredicateCall { name, .. } => {
            if !visited_predicates.insert(name.clone()) {
                return false;
            }
            predicate_environment.get(name).is_some_and(|definition| {
                proposition_contains_liveness_claim(
                    &definition.body,
                    owned_bases,
                    predicate_environment,
                    visited_predicates,
                )
            })
        }
        SurfaceProposition::At { proposition, .. }
        | SurfaceProposition::Not(proposition)
        | SurfaceProposition::ForAll {
            body: proposition, ..
        }
        | SurfaceProposition::Exists {
            body: proposition, ..
        } => proposition_contains_liveness_claim(
            proposition,
            owned_bases,
            predicate_environment,
            visited_predicates,
        ),
        SurfaceProposition::And(left, right)
        | SurfaceProposition::Or(left, right)
        | SurfaceProposition::Implies(left, right) => {
            proposition_contains_liveness_claim(
                left,
                owned_bases,
                predicate_environment,
                visited_predicates,
            ) || proposition_contains_liveness_claim(
                right,
                owned_bases,
                predicate_environment,
                visited_predicates,
            )
        }
        SurfaceProposition::RangeAll { body, .. } | SurfaceProposition::RangeAny { body, .. } => {
            proposition_contains_liveness_claim(
                body,
                owned_bases,
                predicate_environment,
                visited_predicates,
            )
        }
        SurfaceProposition::Comparison { .. }
        | SurfaceProposition::FloatClassification { .. }
        | SurfaceProposition::Separate { .. }
        | SurfaceProposition::Contains { .. }
        | SurfaceProposition::Defined { .. }
        | SurfaceProposition::IsA { .. } => false,
    }
}

pub(in crate::surface) fn collect_resource_count_families(
    proposition: &SurfaceProposition,
    families: &mut BTreeSet<String>,
) {
    fn collect_expression(expression: &SurfaceTerm, families: &mut BTreeSet<String>) {
        match expression {
            SurfaceTerm::IntegerContext(value) => collect_expression(value, families),

            SurfaceTerm::Proposition(proposition) => {
                collect_resource_count_families(proposition, families)
            }
            SurfaceTerm::Resource(_) => {}
            SurfaceTerm::RegionResult(_)
            | SurfaceTerm::RegionAllocation(_)
            | SurfaceTerm::RegionParameter { .. } => {}
            SurfaceTerm::Lambda { body, .. } => collect_expression(body, families),
            SurfaceTerm::Apply {
                function,
                arguments,
            } => {
                collect_expression(function, families);
                for argument in arguments {
                    collect_expression(argument, families);
                }
            }

            SurfaceTerm::IntegerLiteral(_) => {}
            SurfaceTerm::CUnary { operand: inner, .. }
            | SurfaceTerm::MemoryLoad { pointer: inner, .. }
            | SurfaceTerm::Negate(inner) => collect_expression(inner, families),
            SurfaceTerm::ResourceField(_)
            | SurfaceTerm::AlgebraicVariable { .. }
            | SurfaceTerm::Binding(_) => {}
            SurfaceTerm::AlgebraicConstructor { arguments, .. } => {
                for argument in arguments {
                    collect_expression(argument, families);
                }
            }
            SurfaceTerm::AlgebraicMatch { scrutinee, arms } => {
                collect_expression(scrutinee, families);
                for arm in arms {
                    collect_expression(&arm.body, families);
                }
            }
            SurfaceTerm::SequenceLiteral(elements) => {
                for element in elements {
                    collect_expression(element, families);
                }
            }
            SurfaceTerm::SequenceConcat(left, right) => {
                collect_expression(left, families);
                collect_expression(right, families);
            }
            SurfaceTerm::ResourceCount(resource) => {
                if let ResourceClause::Declared {
                    name, arguments, ..
                } = resource.as_ref()
                {
                    families.insert(name.clone());
                    for argument in arguments {
                        collect_expression(argument, families);
                    }
                }
            }
            SurfaceTerm::Field { base, .. }
            | SurfaceTerm::Old(base)
            | SurfaceTerm::Exact(base)
            | SurfaceTerm::At {
                expression: base, ..
            }
            | SurfaceTerm::BitwiseNot(base) => collect_expression(base, families),
            SurfaceTerm::ArrayIndex { base, .. } => collect_expression(base, families),
            crate::surface::binary_contract_expression!(left, right) => {
                collect_expression(left, families);
                collect_expression(right, families);
            }
            SurfaceTerm::If {
                condition,
                then_branch,
                else_branch,
            } => {
                collect_resource_count_families(condition, families);
                collect_expression(then_branch, families);
                collect_expression(else_branch, families);
            }
            SurfaceTerm::RangeFold {
                start,
                end,
                initial,
                body,
                ..
            } => {
                collect_expression(start, families);
                collect_expression(end, families);
                collect_expression(initial, families);
                collect_expression(body, families);
            }
            SurfaceTerm::Let { value, body, .. } => {
                collect_expression(value, families);
                collect_expression(body, families);
            }
            SurfaceTerm::MethodCall {
                receiver,
                arguments,
                ..
            } => {
                collect_expression(receiver, families);
                for argument in arguments {
                    collect_expression(argument, families);
                }
            }
            SurfaceTerm::Call { arguments, .. } => {
                for argument in arguments {
                    collect_expression(argument, families);
                }
            }
            SurfaceTerm::QualifiedC { .. }
            | SurfaceTerm::ProgramExpression(_)
            | SurfaceTerm::ProgramBinding(_)
            | SurfaceTerm::ResourceWildcard => {}
        }
    }

    match proposition {
        SurfaceProposition::Value(expression) => collect_expression(expression, families),
        SurfaceProposition::Comparison { left, right, .. } => {
            collect_expression(left, families);
            collect_expression(right, families);
        }
        SurfaceProposition::FloatClassification { expression, .. } => {
            collect_expression(expression, families);
        }
        SurfaceProposition::Defined { expression }
        | SurfaceProposition::IsA {
            pointer: expression,
            ..
        } => collect_expression(expression, families),
        SurfaceProposition::At { proposition, .. }
        | SurfaceProposition::Not(proposition)
        | SurfaceProposition::ForAll {
            body: proposition, ..
        }
        | SurfaceProposition::Exists {
            body: proposition, ..
        } => {
            collect_resource_count_families(proposition, families);
        }
        SurfaceProposition::And(left, right)
        | SurfaceProposition::Or(left, right)
        | SurfaceProposition::Implies(left, right) => {
            collect_resource_count_families(left, families);
            collect_resource_count_families(right, families);
        }
        SurfaceProposition::RangeAll {
            start, end, body, ..
        }
        | SurfaceProposition::RangeAny {
            start, end, body, ..
        } => {
            collect_expression(start, families);
            collect_expression(end, families);
            collect_resource_count_families(body, families);
        }
        SurfaceProposition::PredicateCall { arguments, .. } => {
            for argument in arguments {
                collect_expression(argument, families);
            }
        }
        SurfaceProposition::Separate { .. }
        | SurfaceProposition::ResourceViewable { .. }
        | SurfaceProposition::Contains { .. }
        | SurfaceProposition::Loadable { .. } => {}
    }
}

pub(in crate::surface) fn collect_called_predicates(
    proposition: &SurfaceProposition,
    names: &mut BTreeSet<String>,
) {
    match proposition {
        SurfaceProposition::Value(expression) => {
            crate::surface::proof::fixed_state_proofs::conversion_conditions::walk_written_expressions(
                expression,
                &mut |term| {
                    if let SurfaceTerm::Proposition(body) = term {
                        collect_called_predicates(body, names);
                    }
                },
            );
        }
        SurfaceProposition::PredicateCall { name, .. } => {
            names.insert(name.clone());
        }
        SurfaceProposition::At { proposition, .. }
        | SurfaceProposition::Not(proposition)
        | SurfaceProposition::ForAll {
            body: proposition, ..
        }
        | SurfaceProposition::Exists {
            body: proposition, ..
        } => {
            collect_called_predicates(proposition, names);
        }
        SurfaceProposition::And(left, right)
        | SurfaceProposition::Or(left, right)
        | SurfaceProposition::Implies(left, right) => {
            collect_called_predicates(left, names);
            collect_called_predicates(right, names);
        }
        SurfaceProposition::RangeAll { body, .. } | SurfaceProposition::RangeAny { body, .. } => {
            collect_called_predicates(body, names);
        }
        SurfaceProposition::Comparison { .. }
        | SurfaceProposition::FloatClassification { .. }
        | SurfaceProposition::Separate { .. }
        | SurfaceProposition::ResourceViewable { .. }
        | SurfaceProposition::Contains { .. }
        | SurfaceProposition::Loadable { .. }
        | SurfaceProposition::Defined { .. }
        | SurfaceProposition::IsA { .. } => {}
    }
}

fn contract_segment_contains_old_expression(segment: &ContractSegment) -> bool {
    [&segment.base, &segment.start, &segment.end]
        .into_iter()
        .any(|expression| {
            contains_old_expression(&SurfaceTerm::ProgramExpression(expression.clone()))
        })
}

fn resource_subject_contains_old_expression(resource: &ResourceSubject) -> bool {
    match resource {
        ResourceSubject::At { resource, .. } => resource_subject_contains_old_expression(resource),
        ResourceSubject::Emp => false,
        ResourceSubject::Star(left, right) => {
            resource_subject_contains_old_expression(left)
                || resource_subject_contains_old_expression(right)
        }
        ResourceSubject::Footprint(_)
        | ResourceSubject::Parameter { .. }
        | ResourceSubject::Instance { .. }
        | ResourceSubject::Captured { .. } => false,
        ResourceSubject::Memory(segment) => contract_segment_contains_old_expression(segment),
        ResourceSubject::SavedMemory { base, start, end } => [base, start]
            .into_iter()
            .chain(end.iter())
            .any(contains_old_expression),
        ResourceSubject::Declared { arguments, .. } => {
            arguments.iter().any(contains_old_expression)
        }
    }
}

pub(in crate::surface) fn proposition_contains_old_expression(
    proposition: &SurfaceProposition,
) -> bool {
    match proposition {
        SurfaceProposition::Value(expression) => contains_old_expression(expression),

        SurfaceProposition::Comparison { left, right, .. } => {
            contains_old_expression(left) || contains_old_expression(right)
        }
        SurfaceProposition::FloatClassification { expression, .. } => {
            contains_old_expression(expression)
        }
        SurfaceProposition::Separate { left, right } => {
            resource_subject_contains_old_expression(left)
                || resource_subject_contains_old_expression(right)
        }
        SurfaceProposition::ResourceViewable { resource } => {
            resource_subject_contains_old_expression(resource)
        }
        SurfaceProposition::Contains { parent, child } => {
            resource_subject_contains_old_expression(parent)
                || resource_subject_contains_old_expression(child)
        }
        SurfaceProposition::Loadable { segment } => {
            contract_segment_contains_old_expression(segment)
        }
        SurfaceProposition::Defined { expression }
        | SurfaceProposition::IsA {
            pointer: expression,
            ..
        } => contains_old_expression(expression),
        SurfaceProposition::At { proposition, .. } => {
            proposition_contains_old_expression(proposition)
        }
        SurfaceProposition::And(left, right)
        | SurfaceProposition::Or(left, right)
        | SurfaceProposition::Implies(left, right) => {
            proposition_contains_old_expression(left) || proposition_contains_old_expression(right)
        }
        SurfaceProposition::Not(body)
        | SurfaceProposition::ForAll { body, .. }
        | SurfaceProposition::Exists { body, .. } => proposition_contains_old_expression(body),
        SurfaceProposition::RangeAll {
            start, end, body, ..
        }
        | SurfaceProposition::RangeAny {
            start, end, body, ..
        } => {
            contains_old_expression(start)
                || contains_old_expression(end)
                || proposition_contains_old_expression(body)
        }
        SurfaceProposition::PredicateCall { arguments, .. } => {
            arguments.iter().any(contains_old_expression)
        }
    }
}

pub(in crate::surface) fn contains_at_expression(expression: &SurfaceTerm) -> bool {
    match expression {
        SurfaceTerm::IntegerContext(value) => contains_at_expression(value),

        SurfaceTerm::Proposition(proposition) => proposition_contains_at_expression(proposition),
        SurfaceTerm::Resource(subject) => resource_subject_contains_at_expression(subject),
        SurfaceTerm::RegionResult(_)
        | SurfaceTerm::RegionAllocation(_)
        | SurfaceTerm::RegionParameter { .. } => true,
        SurfaceTerm::Lambda { body, .. } => contains_at_expression(body),
        SurfaceTerm::Apply {
            function,
            arguments,
        } => contains_at_expression(function) || arguments.iter().any(contains_at_expression),

        SurfaceTerm::IntegerLiteral(_) => false,
        SurfaceTerm::CUnary { operand: inner, .. }
        | SurfaceTerm::MemoryLoad { pointer: inner, .. }
        | SurfaceTerm::Negate(inner) => contains_at_expression(inner),
        SurfaceTerm::ResourceField(_)
        | SurfaceTerm::AlgebraicVariable { .. }
        | SurfaceTerm::Binding(_) => false,
        SurfaceTerm::AlgebraicConstructor { arguments, .. } => {
            arguments.iter().any(contains_at_expression)
        }
        SurfaceTerm::AlgebraicMatch { scrutinee, arms } => {
            contains_at_expression(scrutinee)
                || arms.iter().any(|arm| contains_at_expression(&arm.body))
        }
        SurfaceTerm::SequenceLiteral(elements) => elements.iter().any(contains_at_expression),
        SurfaceTerm::SequenceConcat(left, right) => {
            contains_at_expression(left) || contains_at_expression(right)
        }
        SurfaceTerm::At { .. } => true,
        SurfaceTerm::QualifiedC { .. }
        | SurfaceTerm::ProgramExpression(_)
        | SurfaceTerm::ProgramBinding(_)
        | SurfaceTerm::ResourceWildcard => false,
        SurfaceTerm::ResourceCount(resource) => match resource.as_ref() {
            ResourceClause::Declared { arguments, .. } => {
                arguments.iter().any(contains_at_expression)
            }
            _ => false,
        },
        SurfaceTerm::Field { base, .. } => contains_at_expression(base),
        SurfaceTerm::ArrayIndex { base, .. } => contains_at_expression(base),
        SurfaceTerm::Old(expression)
        | SurfaceTerm::Exact(expression)
        | SurfaceTerm::BitwiseNot(expression) => contains_at_expression(expression),
        crate::surface::binary_contract_expression!(left, right) => {
            contains_at_expression(left) || contains_at_expression(right)
        }
        SurfaceTerm::If {
            condition,
            then_branch,
            else_branch,
        } => {
            proposition_contains_at_expression(condition)
                || contains_at_expression(then_branch)
                || contains_at_expression(else_branch)
        }
        SurfaceTerm::RangeFold {
            start,
            end,
            initial,
            body,
            ..
        } => {
            contains_at_expression(start)
                || contains_at_expression(end)
                || contains_at_expression(initial)
                || contains_at_expression(body)
        }
        SurfaceTerm::Let { value, body, .. } => {
            contains_at_expression(value) || contains_at_expression(body)
        }
        SurfaceTerm::MethodCall {
            receiver,
            arguments,
            ..
        } => contains_at_expression(receiver) || arguments.iter().any(contains_at_expression),
        SurfaceTerm::Call { arguments, .. } => arguments.iter().any(contains_at_expression),
    }
}

fn contract_segment_contains_at_expression(segment: &ContractSegment) -> bool {
    [&segment.base, &segment.start, &segment.end]
        .into_iter()
        .any(|expression| {
            contains_at_expression(&SurfaceTerm::ProgramExpression(expression.clone()))
        })
}

fn resource_subject_contains_at_expression(resource: &ResourceSubject) -> bool {
    match resource {
        ResourceSubject::At { .. } => true,
        ResourceSubject::Emp => false,
        ResourceSubject::Star(left, right) => {
            resource_subject_contains_at_expression(left)
                || resource_subject_contains_at_expression(right)
        }
        ResourceSubject::Footprint(_) => true,
        ResourceSubject::Parameter { .. }
        | ResourceSubject::Instance { .. }
        | ResourceSubject::Captured { .. } => false,
        ResourceSubject::Memory(segment) => contract_segment_contains_at_expression(segment),
        ResourceSubject::SavedMemory { base, start, end } => [base, start]
            .into_iter()
            .chain(end.iter())
            .any(contains_at_expression),
        ResourceSubject::Declared { arguments, .. } => arguments.iter().any(contains_at_expression),
    }
}

pub(in crate::surface) fn proposition_contains_at_expression(
    proposition: &SurfaceProposition,
) -> bool {
    match proposition {
        SurfaceProposition::Value(expression) => contains_at_expression(expression),

        SurfaceProposition::Comparison { left, right, .. } => {
            contains_at_expression(left) || contains_at_expression(right)
        }
        SurfaceProposition::FloatClassification { expression, .. } => {
            contains_at_expression(expression)
        }
        SurfaceProposition::Separate { left, right } => {
            resource_subject_contains_at_expression(left)
                || resource_subject_contains_at_expression(right)
        }
        SurfaceProposition::ResourceViewable { resource } => {
            resource_subject_contains_at_expression(resource)
        }
        SurfaceProposition::Contains { parent, child } => {
            resource_subject_contains_at_expression(parent)
                || resource_subject_contains_at_expression(child)
        }
        SurfaceProposition::Loadable { segment } => {
            contract_segment_contains_at_expression(segment)
        }
        SurfaceProposition::Defined { expression }
        | SurfaceProposition::IsA {
            pointer: expression,
            ..
        } => contains_at_expression(expression),
        SurfaceProposition::At { .. } => true,
        SurfaceProposition::And(left, right)
        | SurfaceProposition::Or(left, right)
        | SurfaceProposition::Implies(left, right) => {
            proposition_contains_at_expression(left) || proposition_contains_at_expression(right)
        }
        SurfaceProposition::Not(body)
        | SurfaceProposition::ForAll { body, .. }
        | SurfaceProposition::Exists { body, .. } => proposition_contains_at_expression(body),
        SurfaceProposition::RangeAll {
            start, end, body, ..
        }
        | SurfaceProposition::RangeAny {
            start, end, body, ..
        } => {
            contains_at_expression(start)
                || contains_at_expression(end)
                || proposition_contains_at_expression(body)
        }
        SurfaceProposition::PredicateCall { arguments, .. } => {
            arguments.iter().any(contains_at_expression)
        }
    }
}

pub(in crate::surface) fn collect_click_function_calls(
    expression: &SurfaceTerm,
    calls: &mut BTreeSet<String>,
) {
    let mut depth = 0;
    let mut current = expression;
    while let SurfaceTerm::Add(left, _) = current {
        depth += 1;
        current = left;
    }
    if depth > 128 {
        let mut pending = vec![expression];
        while let Some(expression) = pending.pop() {
            match expression {
                crate::surface::binary_contract_expression!(left, right) => {
                    pending.push(right);
                    pending.push(left);
                }
                SurfaceTerm::Negate(inner) | SurfaceTerm::BitwiseNot(inner) => pending.push(inner),
                expression => collect_click_function_calls_one(expression, calls),
            }
        }
        return;
    }
    collect_click_function_calls_one(expression, calls);
}

fn collect_click_function_calls_one(expression: &SurfaceTerm, calls: &mut BTreeSet<String>) {
    if let Ok(Some(reduced)) = lambdas::reduce_head(expression) {
        collect_click_function_calls(&reduced, calls);
        return;
    }
    match expression {
        SurfaceTerm::IntegerContext(value) => collect_click_function_calls(value, calls),

        SurfaceTerm::Proposition(proposition) => {
            collect_click_function_calls_in_proposition(proposition, calls)
        }
        SurfaceTerm::Resource(subject) => {
            collect_click_function_calls_in_resource_subject(subject, calls)
        }
        SurfaceTerm::RegionResult(_)
        | SurfaceTerm::RegionAllocation(_)
        | SurfaceTerm::RegionParameter { .. } => {}
        SurfaceTerm::Lambda { body, .. } => collect_click_function_calls(body, calls),
        SurfaceTerm::Apply {
            function,
            arguments,
        } => {
            collect_click_function_calls(function, calls);
            for argument in arguments {
                collect_click_function_calls(argument, calls);
            }
        }

        SurfaceTerm::IntegerLiteral(_) => {}
        SurfaceTerm::CUnary { operand: inner, .. }
        | SurfaceTerm::MemoryLoad { pointer: inner, .. }
        | SurfaceTerm::Negate(inner) => collect_click_function_calls(inner, calls),
        SurfaceTerm::ResourceField(_)
        | SurfaceTerm::AlgebraicVariable { .. }
        | SurfaceTerm::Binding(_) => {}
        SurfaceTerm::AlgebraicConstructor { arguments, .. } => {
            for argument in arguments {
                collect_click_function_calls(argument, calls);
            }
        }
        SurfaceTerm::AlgebraicMatch { scrutinee, arms } => {
            collect_click_function_calls(scrutinee, calls);
            for arm in arms {
                collect_click_function_calls(&arm.body, calls);
            }
        }
        SurfaceTerm::SequenceLiteral(elements) => {
            for element in elements {
                collect_click_function_calls(element, calls);
            }
        }
        SurfaceTerm::SequenceConcat(left, right) => {
            collect_click_function_calls(left, calls);
            collect_click_function_calls(right, calls);
        }
        SurfaceTerm::QualifiedC { .. }
        | SurfaceTerm::ProgramExpression(_)
        | SurfaceTerm::ProgramBinding(_)
        | SurfaceTerm::ResourceWildcard => {}
        SurfaceTerm::ResourceCount(resource) => {
            if let ResourceClause::Declared { arguments, .. } = resource.as_ref() {
                for argument in arguments {
                    collect_click_function_calls(argument, calls);
                }
            }
        }
        SurfaceTerm::Field { base, .. } => collect_click_function_calls(base, calls),
        SurfaceTerm::ArrayIndex { base, .. } => collect_click_function_calls(base, calls),
        SurfaceTerm::Old(body) | SurfaceTerm::Exact(body) => {
            collect_click_function_calls(body, calls)
        }
        SurfaceTerm::At { expression, .. } => collect_click_function_calls(expression, calls),
        crate::surface::binary_contract_expression!(left, right) => {
            collect_click_function_calls(left, calls);
            collect_click_function_calls(right, calls);
        }
        SurfaceTerm::BitwiseNot(expression) => collect_click_function_calls(expression, calls),
        SurfaceTerm::If {
            condition,
            then_branch,
            else_branch,
        } => {
            collect_click_function_calls_in_proposition(condition, calls);
            collect_click_function_calls(then_branch, calls);
            collect_click_function_calls(else_branch, calls);
        }
        SurfaceTerm::RangeFold {
            start,
            end,
            initial,
            body,
            ..
        } => {
            collect_click_function_calls(start, calls);
            collect_click_function_calls(end, calls);
            collect_click_function_calls(initial, calls);
            collect_click_function_calls(body, calls);
        }
        SurfaceTerm::Let { value, body, .. } => {
            collect_click_function_calls(value, calls);
            collect_click_function_calls(body, calls);
        }
        SurfaceTerm::MethodCall {
            receiver,
            arguments,
            ..
        } => {
            collect_click_function_calls(receiver, calls);
            for argument in arguments {
                collect_click_function_calls(argument, calls);
            }
        }
        SurfaceTerm::Call { name, arguments } => {
            calls.insert(name.clone());
            for argument in arguments {
                collect_click_function_calls(argument, calls);
            }
        }
    }
}

fn collect_click_function_calls_in_segment(
    segment: &ContractSegment,
    calls: &mut BTreeSet<String>,
) {
    for expression in [&segment.base, &segment.start, &segment.end] {
        collect_click_function_calls(&SurfaceTerm::ProgramExpression(expression.clone()), calls);
    }
}

fn collect_click_function_calls_in_resource_subject(
    resource: &ResourceSubject,
    calls: &mut BTreeSet<String>,
) {
    match resource {
        ResourceSubject::At { resource, .. } => {
            collect_click_function_calls_in_resource_subject(resource, calls)
        }
        ResourceSubject::Emp => (),
        ResourceSubject::Star(left, right) => {
            collect_click_function_calls_in_resource_subject(left, calls);
            collect_click_function_calls_in_resource_subject(right, calls);
        }
        ResourceSubject::Footprint(_)
        | ResourceSubject::Parameter { .. }
        | ResourceSubject::Instance { .. }
        | ResourceSubject::Captured { .. } => {}
        ResourceSubject::Memory(segment) => collect_click_function_calls_in_segment(segment, calls),
        ResourceSubject::SavedMemory { base, start, end } => {
            for argument in [base, start].into_iter().chain(end.iter()) {
                collect_click_function_calls(argument, calls);
            }
        }
        ResourceSubject::Declared { arguments, .. } => {
            for argument in arguments {
                collect_click_function_calls(argument, calls);
            }
        }
    }
}

pub(in crate::surface) fn collect_click_function_calls_in_proposition(
    proposition: &SurfaceProposition,
    calls: &mut BTreeSet<String>,
) {
    let mut pending = vec![proposition];
    while let Some(proposition) = pending.pop() {
        match proposition {
            SurfaceProposition::And(left, right)
            | SurfaceProposition::Or(left, right)
            | SurfaceProposition::Implies(left, right) => {
                pending.push(right);
                pending.push(left);
            }
            proposition => collect_click_function_calls_in_proposition_one(proposition, calls),
        }
    }
}

fn collect_click_function_calls_in_proposition_one(
    proposition: &SurfaceProposition,
    calls: &mut BTreeSet<String>,
) {
    match proposition {
        SurfaceProposition::Value(expression) => collect_click_function_calls(expression, calls),

        SurfaceProposition::Comparison { left, right, .. } => {
            collect_click_function_calls(left, calls);
            collect_click_function_calls(right, calls);
        }
        SurfaceProposition::FloatClassification { expression, .. } => {
            collect_click_function_calls(expression, calls);
        }
        SurfaceProposition::Separate { left, right } => {
            collect_click_function_calls_in_resource_subject(left, calls);
            collect_click_function_calls_in_resource_subject(right, calls);
        }
        SurfaceProposition::ResourceViewable { resource } => {
            collect_click_function_calls_in_resource_subject(resource, calls)
        }
        SurfaceProposition::Contains { parent, child } => {
            collect_click_function_calls_in_resource_subject(parent, calls);
            collect_click_function_calls_in_resource_subject(child, calls);
        }
        SurfaceProposition::Loadable { segment } => {
            collect_click_function_calls_in_segment(segment, calls);
        }
        SurfaceProposition::Defined { expression }
        | SurfaceProposition::IsA {
            pointer: expression,
            ..
        } => {
            collect_click_function_calls(expression, calls);
        }
        SurfaceProposition::At { proposition, .. } => {
            collect_click_function_calls_in_proposition(proposition, calls);
        }
        SurfaceProposition::And(left, right)
        | SurfaceProposition::Or(left, right)
        | SurfaceProposition::Implies(left, right) => {
            collect_click_function_calls_in_proposition(left, calls);
            collect_click_function_calls_in_proposition(right, calls);
        }
        SurfaceProposition::Not(body)
        | SurfaceProposition::ForAll { body, .. }
        | SurfaceProposition::Exists { body, .. } => {
            collect_click_function_calls_in_proposition(body, calls);
        }
        SurfaceProposition::RangeAll {
            start, end, body, ..
        }
        | SurfaceProposition::RangeAny {
            start, end, body, ..
        } => {
            collect_click_function_calls(start, calls);
            collect_click_function_calls(end, calls);
            collect_click_function_calls_in_proposition(body, calls);
        }
        SurfaceProposition::PredicateCall { arguments, .. } => {
            for argument in arguments {
                collect_click_function_calls(argument, calls);
            }
        }
    }
}

pub(super) fn validate_well_founded_click_recursion(
    definitions: &[ClickFunctionDefinition],
    function_calls: &BTreeMap<String, BTreeSet<String>>,
    algebraic_definitions: &[AlgebraicTypeDefinition],
) -> Result<(), ClickError> {
    let definitions = definitions
        .iter()
        .map(|definition| (definition.name(), definition))
        .collect::<BTreeMap<_, _>>();
    let recursive_functions = definitions
        .keys()
        .filter(|name| {
            function_calls.get(**name).is_some_and(|callees| {
                callees.iter().any(|callee| {
                    callee == **name
                        || click_function_reaches(
                            callee,
                            name,
                            function_calls,
                            &mut BTreeSet::new(),
                        )
                })
            })
        })
        .copied()
        .collect::<BTreeSet<_>>();
    let algebraic_definitions = algebraic_definitions
        .iter()
        .map(|definition| (definition.name(), definition))
        .collect::<BTreeMap<_, _>>();

    let mut measures = BTreeMap::new();
    for (name, definition) in &definitions {
        let measure = click_function_decreases_parameter(definition)?;
        if recursive_functions.contains(name) && measure.is_none() {
            return Err(ClickError::new(format!(
                "recursive pure function `{name}` requires `decreases <parameter>`"
            )));
        }
        if let Some(measure) = measure {
            measures.insert((*name).to_string(), measure);
        }
    }

    for caller in &recursive_functions {
        validate_recursive_calls_in_expression(
            caller,
            definitions[caller]
                .body()
                .expect("a recursive function has a body"),
            &BinderMap::new(),
            &BinderMap::new(),
            &definitions,
            function_calls,
            &measures,
            &algebraic_definitions,
        )?;
    }
    Ok(())
}

fn click_function_reaches(
    from: &str,
    target: &str,
    function_calls: &BTreeMap<String, BTreeSet<String>>,
    visited: &mut BTreeSet<String>,
) -> bool {
    if !visited.insert(from.to_string()) {
        return false;
    }
    function_calls.get(from).is_some_and(|callees| {
        callees.iter().any(|callee| {
            callee == target || click_function_reaches(callee, target, function_calls, visited)
        })
    })
}

#[derive(Clone, Debug)]
enum ClickRecursionMeasure {
    Int32 {
        parameter: String,
    },
    Algebraic {
        parameter: String,
        algebraic_type: AlgebraicTypeApplication,
    },
}

impl ClickRecursionMeasure {
    fn parameter(&self) -> &str {
        match self {
            Self::Int32 { parameter } | Self::Algebraic { parameter, .. } => parameter,
        }
    }
}

fn click_function_decreases_parameter(
    definition: &ClickFunctionDefinition,
) -> Result<Option<ClickRecursionMeasure>, ClickError> {
    let Some(measure) = definition.decreases() else {
        return Ok(None);
    };
    let Some(name) = contract_expression_variable(measure) else {
        return Err(ClickError::new(format!(
            "function `{}` requires `decreases` to name one int32 or algebraic datatype parameter",
            definition.name()
        )));
    };
    let Some(parameter) = definition
        .parameters()
        .iter()
        .find(|parameter| parameter.name() == name)
    else {
        return Err(ClickError::new(format!(
            "function `{}` decreases measure `{name}` is not a parameter",
            definition.name()
        )));
    };
    match parameter.click_type() {
        ClickType::Program(InterfaceType::Int32) => Ok(Some(ClickRecursionMeasure::Int32 {
            parameter: name.to_string(),
        })),
        ClickType::Algebraic(algebraic_type) => Ok(Some(ClickRecursionMeasure::Algebraic {
            parameter: name.to_string(),
            algebraic_type: algebraic_type.clone(),
        })),
        _ => Err(ClickError::new(format!(
            "function `{}` decreases measure `{name}` must be int32 or an algebraic datatype",
            definition.name()
        ))),
    }
}

fn contract_expression_variable(expression: &SurfaceTerm) -> Option<SurfaceBinder> {
    match expression {
        SurfaceTerm::Binding(name)
        | SurfaceTerm::ProgramExpression(ProgramExpression::Variable(
            crate::kernel::BindingName::Named(name),
        ))
        | SurfaceTerm::ProgramBinding(name) => Some(name.into()),
        SurfaceTerm::AlgebraicVariable { name, .. } => Some(name.clone()),
        SurfaceTerm::ProgramExpression(ProgramExpression::Variable(
            crate::kernel::BindingName::Generated(id),
        )) => Some((*id).into()),
        _ => None,
    }
}

fn contract_expression_int32_constant(expression: &SurfaceTerm) -> Option<i64> {
    let ProgramExpression::Value(ProgramValue::Int32(bits32_constant!(value))) =
        contract_expression_as_program_expression(expression)?
    else {
        return None;
    };
    Some(i64::from(constant_u32(value) as i32))
}

fn component_internal_call(
    caller: &str,
    callee: &str,
    function_calls: &BTreeMap<String, BTreeSet<String>>,
) -> bool {
    caller == callee || click_function_reaches(callee, caller, function_calls, &mut BTreeSet::new())
}

fn validate_recursive_call_edge(
    caller: &str,
    callee: &str,
    arguments: &[SurfaceTerm],
    lower_bounds: &BinderMap<i64>,
    structural_subterms: &BinderMap<ClickType>,
    definitions: &BTreeMap<&str, &ClickFunctionDefinition>,
    function_calls: &BTreeMap<String, BTreeSet<String>>,
    measures: &BTreeMap<String, ClickRecursionMeasure>,
) -> Result<(), ClickError> {
    if !component_internal_call(caller, callee, function_calls) {
        return Ok(());
    }
    let caller_measure = measures
        .get(caller)
        .expect("recursive callers have validated measures");
    let callee_measure = measures.get(callee).ok_or_else(|| {
        ClickError::new(format!(
            "recursive call `{caller}` -> `{callee}` requires `{callee}` to declare `decreases`"
        ))
    })?;
    let measure_index = definitions
        .get(callee)
        .and_then(|definition| {
            definition
                .parameters()
                .iter()
                .position(|parameter| parameter.name() == callee_measure.parameter())
        })
        .ok_or_else(|| {
            ClickError::new(format!(
                "internal error locating decreases parameter `{}` for `{callee}`",
                callee_measure.parameter()
            ))
            .with_kind(ClickErrorKind::Internal)
        })?;
    let next = arguments.get(measure_index).ok_or_else(|| {
        ClickError::new(format!(
            "recursive call `{caller}` -> `{callee}` is missing its decreases argument"
        ))
    })?;
    let valid = match (caller_measure, callee_measure) {
        (
            ClickRecursionMeasure::Int32 {
                parameter: caller_parameter,
            },
            ClickRecursionMeasure::Int32 { .. },
        ) => {
            let caller_lower = lower_bounds.get(caller_parameter).copied();
            match next {
                SurfaceTerm::Subtract(left, right)
                    if contract_expression_variable(left)
                        .is_some_and(|name| name == *caller_parameter) =>
                {
                    let step = contract_expression_int32_constant(right);
                    step.is_some_and(|step| {
                        step > 0 && caller_lower.is_some_and(|lower| lower >= step)
                    })
                }
                _ => contract_expression_int32_constant(next).is_some_and(|next| {
                    next >= 0 && caller_lower.is_some_and(|lower| lower > next)
                }),
            }
        }
        (
            ClickRecursionMeasure::Algebraic { .. },
            ClickRecursionMeasure::Algebraic {
                algebraic_type: callee_type,
                ..
            },
        ) => contract_expression_variable(next)
            .and_then(|name| structural_subterms.get(&name))
            .is_some_and(|subterm_type| subterm_type == &ClickType::Algebraic(callee_type.clone())),
        _ => false,
    };
    if !valid {
        let requirement = match caller_measure {
            ClickRecursionMeasure::Int32 { parameter } => format!(
                "a nonnegative decreases measure strictly smaller than `{parameter}` on this path"
            ),
            ClickRecursionMeasure::Algebraic { parameter, .. } => format!(
                "a recursive field structurally below `{parameter}` as its decreases argument"
            ),
        };
        return Err(ClickError::new(format!(
            "recursive call `{caller}` -> `{callee}` must pass {requirement}"
        )));
    }
    Ok(())
}

fn validate_recursive_calls_in_expression(
    caller: &str,
    expression: &SurfaceTerm,
    lower_bounds: &BinderMap<i64>,
    structural_subterms: &BinderMap<ClickType>,
    definitions: &BTreeMap<&str, &ClickFunctionDefinition>,
    function_calls: &BTreeMap<String, BTreeSet<String>>,
    measures: &BTreeMap<String, ClickRecursionMeasure>,
    algebraic_definitions: &BTreeMap<&str, &AlgebraicTypeDefinition>,
) -> Result<(), ClickError> {
    let recurse =
        |expression: &SurfaceTerm, bounds: &BinderMap<i64>, subterms: &BinderMap<ClickType>| {
            validate_recursive_calls_in_expression(
                caller,
                expression,
                bounds,
                subterms,
                definitions,
                function_calls,
                measures,
                algebraic_definitions,
            )
        };
    match expression {
        SurfaceTerm::IntegerContext(value) => recurse(value, lower_bounds, structural_subterms),

        SurfaceTerm::Proposition(proposition) => validate_recursive_calls_in_proposition(
            caller,
            proposition,
            lower_bounds,
            structural_subterms,
            definitions,
            function_calls,
            measures,
            algebraic_definitions,
        ),
        SurfaceTerm::Resource(_) => Ok(()),
        SurfaceTerm::RegionResult(_)
        | SurfaceTerm::RegionAllocation(_)
        | SurfaceTerm::RegionParameter { .. } => Ok(()),
        SurfaceTerm::Lambda { body, .. } => recurse(body, lower_bounds, structural_subterms),
        SurfaceTerm::Apply {
            function,
            arguments,
        } => {
            recurse(function, lower_bounds, structural_subterms)?;
            for argument in arguments {
                recurse(argument, lower_bounds, structural_subterms)?;
            }
            Ok(())
        }

        SurfaceTerm::IntegerLiteral(_) => Ok(()),
        SurfaceTerm::CUnary { operand: inner, .. }
        | SurfaceTerm::MemoryLoad { pointer: inner, .. }
        | SurfaceTerm::Negate(inner) => recurse(inner, lower_bounds, structural_subterms),
        SurfaceTerm::ResourceField(_)
        | SurfaceTerm::AlgebraicVariable { .. }
        | SurfaceTerm::Binding(_) => Ok(()),
        SurfaceTerm::AlgebraicConstructor { arguments, .. } => {
            for argument in arguments {
                recurse(argument, lower_bounds, structural_subterms)?;
            }
            Ok(())
        }
        SurfaceTerm::AlgebraicMatch { scrutinee, arms } => {
            recurse(scrutinee, lower_bounds, structural_subterms)?;
            // Parameter nodes retain their binder identity, whereas a match
            // or `let` binder that shadows the same spelling is a `Binding`.
            // Require that identity here so shadowing cannot turn a field of
            // an unrelated value into the root termination measure.
            let structural_scrutinee_type = match (scrutinee.as_ref(), measures.get(caller)) {
                (
                    SurfaceTerm::AlgebraicVariable {
                        name,
                        algebraic_type: actual_type,
                        ..
                    },
                    Some(ClickRecursionMeasure::Algebraic {
                        parameter,
                        algebraic_type,
                    }),
                ) if name == parameter && actual_type == algebraic_type => {
                    Some(ClickType::Algebraic(algebraic_type.clone()))
                }
                _ => contract_expression_variable(scrutinee)
                    .and_then(|name| structural_subterms.get(&name).cloned()),
            };
            for arm in arms {
                let mut arm_subterms = structural_subterms.clone();
                let mut arm_bounds = lower_bounds.clone();
                for binding in &arm.bindings {
                    arm_subterms.remove(binding);
                    arm_bounds.remove(binding);
                }
                if let Some(ClickType::Algebraic(application)) = &structural_scrutinee_type {
                    let datatype = algebraic_definitions
                        .get(application.name())
                        .expect("validated algebraic match has a declared datatype");
                    let variant = datatype
                        .variants()
                        .iter()
                        .find(|variant| variant.name() == arm.variant)
                        .expect("validated algebraic match has a declared variant");
                    for (binding, field) in arm.bindings.iter().zip(variant.fields()) {
                        let field_type = instantiate_field_type(datatype, application, field)?;
                        if matches!(field_type, ClickType::Algebraic(_)) {
                            arm_subterms.insert(binding.clone(), field_type);
                        }
                    }
                }
                recurse(&arm.body, &arm_bounds, &arm_subterms)?;
            }
            Ok(())
        }
        SurfaceTerm::SequenceLiteral(elements) => {
            for element in elements {
                recurse(element, lower_bounds, structural_subterms)?;
            }
            Ok(())
        }
        SurfaceTerm::SequenceConcat(left, right) => {
            recurse(left, lower_bounds, structural_subterms)?;
            recurse(right, lower_bounds, structural_subterms)
        }
        SurfaceTerm::QualifiedC { .. }
        | SurfaceTerm::ProgramExpression(_)
        | SurfaceTerm::ProgramBinding(_)
        | SurfaceTerm::ResourceWildcard => Ok(()),
        SurfaceTerm::ResourceCount(resource) => {
            if let ResourceClause::Declared { arguments, .. } = resource.as_ref() {
                for argument in arguments {
                    recurse(argument, lower_bounds, structural_subterms)?;
                }
            }
            Ok(())
        }
        SurfaceTerm::Field { base, .. } => recurse(base, lower_bounds, structural_subterms),
        SurfaceTerm::Old(body) | SurfaceTerm::Exact(body) | SurfaceTerm::BitwiseNot(body) => {
            recurse(body, lower_bounds, structural_subterms)
        }
        SurfaceTerm::At { expression, .. } => {
            recurse(expression, lower_bounds, structural_subterms)
        }
        crate::surface::binary_contract_expression!(left, right) => {
            recurse(left, lower_bounds, structural_subterms)?;
            recurse(right, lower_bounds, structural_subterms)
        }
        SurfaceTerm::If {
            condition,
            then_branch,
            else_branch,
        } => {
            validate_recursive_calls_in_proposition(
                caller,
                condition,
                lower_bounds,
                structural_subterms,
                definitions,
                function_calls,
                measures,
                algebraic_definitions,
            )?;
            let mut then_bounds = lower_bounds.clone();
            add_condition_lower_bounds(condition, true, &mut then_bounds);
            let mut else_bounds = lower_bounds.clone();
            add_condition_lower_bounds(condition, false, &mut else_bounds);
            recurse(then_branch, &then_bounds, structural_subterms)?;
            recurse(else_branch, &else_bounds, structural_subterms)
        }
        SurfaceTerm::RangeFold {
            start,
            end,
            initial,
            accumulator,
            item,
            body,
        } => {
            recurse(start, lower_bounds, structural_subterms)?;
            recurse(end, lower_bounds, structural_subterms)?;
            recurse(initial, lower_bounds, structural_subterms)?;
            // A fold binder that reuses the measure's spelling is a different
            // variable, so the body may not descend on it: `decreases n` with
            // a `|acc, n|` binder would otherwise accept `f(n - 1)` as a
            // descending edge while the parameter never changes.
            let mut body_bounds = lower_bounds.clone();
            let mut body_subterms = structural_subterms.clone();
            for binder in [accumulator, item] {
                body_bounds.remove(binder);
                body_subterms.remove(binder);
            }
            recurse(body, &body_bounds, &body_subterms)
        }
        SurfaceTerm::Let {
            name, value, body, ..
        } => {
            recurse(value, lower_bounds, structural_subterms)?;
            let mut body_bounds = lower_bounds.clone();
            if let Some(name) = name.written() {
                body_bounds.remove(name);
            }
            let mut body_subterms = structural_subterms.clone();
            if let Some(name) = name.written() {
                body_subterms.remove(name);
            }
            recurse(body, &body_bounds, &body_subterms)
        }
        SurfaceTerm::ArrayIndex { base, .. } => recurse(base, lower_bounds, structural_subterms),
        SurfaceTerm::MethodCall {
            receiver,
            arguments,
            ..
        } => {
            recurse(receiver, lower_bounds, structural_subterms)?;
            for argument in arguments {
                recurse(argument, lower_bounds, structural_subterms)?;
            }
            Ok(())
        }
        SurfaceTerm::Call { name, arguments } => {
            for argument in arguments {
                recurse(argument, lower_bounds, structural_subterms)?;
            }
            validate_recursive_call_edge(
                caller,
                name,
                arguments,
                lower_bounds,
                structural_subterms,
                definitions,
                function_calls,
                measures,
            )
        }
    }
}

fn validate_recursive_calls_in_proposition(
    caller: &str,
    proposition: &SurfaceProposition,
    lower_bounds: &BinderMap<i64>,
    structural_subterms: &BinderMap<ClickType>,
    definitions: &BTreeMap<&str, &ClickFunctionDefinition>,
    function_calls: &BTreeMap<String, BTreeSet<String>>,
    measures: &BTreeMap<String, ClickRecursionMeasure>,
    algebraic_definitions: &BTreeMap<&str, &AlgebraicTypeDefinition>,
) -> Result<(), ClickError> {
    let expression = |expression: &SurfaceTerm| {
        validate_recursive_calls_in_expression(
            caller,
            expression,
            lower_bounds,
            structural_subterms,
            definitions,
            function_calls,
            measures,
            algebraic_definitions,
        )
    };
    let recurse_proposition = |proposition: &SurfaceProposition| {
        validate_recursive_calls_in_proposition(
            caller,
            proposition,
            lower_bounds,
            structural_subterms,
            definitions,
            function_calls,
            measures,
            algebraic_definitions,
        )
    };
    match proposition {
        SurfaceProposition::Value(expression) => validate_recursive_calls_in_expression(
            caller,
            expression,
            lower_bounds,
            structural_subterms,
            definitions,
            function_calls,
            measures,
            algebraic_definitions,
        ),

        SurfaceProposition::Comparison { left, right, .. } => {
            expression(left)?;
            expression(right)
        }
        SurfaceProposition::FloatClassification {
            expression: value, ..
        } => expression(value),
        SurfaceProposition::And(left, right)
        | SurfaceProposition::Or(left, right)
        | SurfaceProposition::Implies(left, right) => {
            recurse_proposition(left)?;
            recurse_proposition(right)
        }
        SurfaceProposition::Not(body)
        | SurfaceProposition::ForAll { body, .. }
        | SurfaceProposition::Exists { body, .. }
        | SurfaceProposition::At {
            proposition: body, ..
        } => recurse_proposition(body),
        SurfaceProposition::RangeAll {
            start, end, body, ..
        }
        | SurfaceProposition::RangeAny {
            start, end, body, ..
        } => {
            expression(start)?;
            expression(end)?;
            recurse_proposition(body)
        }
        SurfaceProposition::PredicateCall { arguments, .. } => {
            for argument in arguments {
                expression(argument)?;
            }
            Ok(())
        }
        SurfaceProposition::Defined { expression: body }
        | SurfaceProposition::IsA { pointer: body, .. } => expression(body),
        SurfaceProposition::ResourceViewable { resource } => {
            validate_recursive_calls_in_resource_subject(
                caller,
                resource,
                lower_bounds,
                structural_subterms,
                definitions,
                function_calls,
                measures,
                algebraic_definitions,
            )
        }
        SurfaceProposition::Separate { left, right }
        | SurfaceProposition::Contains {
            parent: left,
            child: right,
        } => {
            validate_recursive_calls_in_resource_subject(
                caller,
                left,
                lower_bounds,
                structural_subterms,
                definitions,
                function_calls,
                measures,
                algebraic_definitions,
            )?;
            validate_recursive_calls_in_resource_subject(
                caller,
                right,
                lower_bounds,
                structural_subterms,
                definitions,
                function_calls,
                measures,
                algebraic_definitions,
            )
        }
        SurfaceProposition::Loadable { segment } => validate_recursive_calls_in_segment(
            caller,
            segment,
            lower_bounds,
            structural_subterms,
            definitions,
            function_calls,
            measures,
            algebraic_definitions,
        ),
    }
}

fn validate_recursive_calls_in_resource_subject(
    caller: &str,
    subject: &ResourceSubject,
    lower_bounds: &BinderMap<i64>,
    structural_subterms: &BinderMap<ClickType>,
    definitions: &BTreeMap<&str, &ClickFunctionDefinition>,
    function_calls: &BTreeMap<String, BTreeSet<String>>,
    measures: &BTreeMap<String, ClickRecursionMeasure>,
    algebraic_definitions: &BTreeMap<&str, &AlgebraicTypeDefinition>,
) -> Result<(), ClickError> {
    match subject {
        ResourceSubject::At { resource, .. } => validate_recursive_calls_in_resource_subject(
            caller,
            resource,
            lower_bounds,
            structural_subterms,
            definitions,
            function_calls,
            measures,
            algebraic_definitions,
        ),
        ResourceSubject::Emp => Ok(()),
        ResourceSubject::Star(left, right) => {
            validate_recursive_calls_in_resource_subject(
                caller,
                left,
                lower_bounds,
                structural_subterms,
                definitions,
                function_calls,
                measures,
                algebraic_definitions,
            )?;
            validate_recursive_calls_in_resource_subject(
                caller,
                right,
                lower_bounds,
                structural_subterms,
                definitions,
                function_calls,
                measures,
                algebraic_definitions,
            )
        }
        ResourceSubject::Footprint(_)
        | ResourceSubject::Parameter { .. }
        | ResourceSubject::Instance { .. }
        | ResourceSubject::Captured { .. } => Ok(()),
        ResourceSubject::Memory(segment) => validate_recursive_calls_in_segment(
            caller,
            segment,
            lower_bounds,
            structural_subterms,
            definitions,
            function_calls,
            measures,
            algebraic_definitions,
        ),
        ResourceSubject::SavedMemory { base, start, end } => {
            for argument in [base, start].into_iter().chain(end.iter()) {
                validate_recursive_calls_in_expression(
                    caller,
                    argument,
                    lower_bounds,
                    structural_subterms,
                    definitions,
                    function_calls,
                    measures,
                    algebraic_definitions,
                )?;
            }
            Ok(())
        }
        ResourceSubject::Declared { arguments, .. } => {
            for argument in arguments {
                validate_recursive_calls_in_expression(
                    caller,
                    argument,
                    lower_bounds,
                    structural_subterms,
                    definitions,
                    function_calls,
                    measures,
                    algebraic_definitions,
                )?;
            }
            Ok(())
        }
    }
}

fn validate_recursive_calls_in_segment(
    caller: &str,
    segment: &ContractSegment,
    lower_bounds: &BinderMap<i64>,
    structural_subterms: &BinderMap<ClickType>,
    definitions: &BTreeMap<&str, &ClickFunctionDefinition>,
    function_calls: &BTreeMap<String, BTreeSet<String>>,
    measures: &BTreeMap<String, ClickRecursionMeasure>,
    algebraic_definitions: &BTreeMap<&str, &AlgebraicTypeDefinition>,
) -> Result<(), ClickError> {
    let expressions = match &segment.surface {
        ContractSegmentSurface::Range { base, start, end }
        | ContractSegmentSurface::StructRange {
            base, start, end, ..
        } => vec![base, start, end],
        ContractSegmentSurface::Field { .. }
        | ContractSegmentSurface::Object(_)
        | ContractSegmentSurface::ObjectPlace { .. } => Vec::new(),
    };
    for expression in expressions {
        validate_recursive_calls_in_expression(
            caller,
            expression,
            lower_bounds,
            structural_subterms,
            definitions,
            function_calls,
            measures,
            algebraic_definitions,
        )?;
    }
    Ok(())
}

fn add_condition_lower_bounds(
    proposition: &SurfaceProposition,
    truth: bool,
    lower_bounds: &mut BinderMap<i64>,
) {
    match proposition {
        SurfaceProposition::Not(body) => add_condition_lower_bounds(body, !truth, lower_bounds),
        SurfaceProposition::And(left, right) if truth => {
            add_condition_lower_bounds(left, true, lower_bounds);
            add_condition_lower_bounds(right, true, lower_bounds);
        }
        SurfaceProposition::Or(left, right) if !truth => {
            add_condition_lower_bounds(left, false, lower_bounds);
            add_condition_lower_bounds(right, false, lower_bounds);
        }
        SurfaceProposition::Comparison {
            left,
            operator,
            right,
        } => {
            let (name, operator, constant) = if let (Some(name), Some(constant)) = (
                contract_expression_variable(left),
                contract_expression_int32_constant(right),
            ) {
                (name, *operator, constant)
            } else if let (Some(constant), Some(name)) = (
                contract_expression_int32_constant(left),
                contract_expression_variable(right),
            ) {
                let reversed = match operator {
                    ComparisonOperator::LessThan => ComparisonOperator::GreaterThan,
                    ComparisonOperator::LessEqual => ComparisonOperator::GreaterEqual,
                    ComparisonOperator::GreaterThan => ComparisonOperator::LessThan,
                    ComparisonOperator::GreaterEqual => ComparisonOperator::LessEqual,
                    operator => *operator,
                };
                (name, reversed, constant)
            } else {
                return;
            };
            let bound = match (operator, truth) {
                (ComparisonOperator::GreaterEqual, true)
                | (ComparisonOperator::LessThan, false) => Some(constant),
                (ComparisonOperator::GreaterThan, true)
                | (ComparisonOperator::LessEqual, false) => constant.checked_add(1),
                (ComparisonOperator::Equal, true) | (ComparisonOperator::NotEqual, false) => {
                    Some(constant)
                }
                _ => None,
            };
            if let Some(bound) = bound {
                let bound = lower_bounds.get(&name).copied().unwrap_or(bound).max(bound);
                lower_bounds.insert(name, bound);
            }
        }
        _ => {}
    }
}
