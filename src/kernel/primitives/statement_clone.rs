//! Clone statement trees without recursing through nested branch bodies.

use super::{CStatement, CSwitchCase};

impl Clone for CStatement {
    fn clone(&self) -> Self {
        let mut result = Self::Skip;
        let mut pending = vec![(self, &mut result)];
        while let Some((source, target)) = pending.pop() {
            crate::instrumentation::record_deterministic_work(1);
            *target = source.clone_shell();
            match (source, target) {
                (
                    Self::If {
                        then_branch,
                        else_branch,
                        ..
                    },
                    Self::If {
                        then_branch: then_target,
                        else_branch: else_target,
                        ..
                    },
                ) => {
                    pending.push((else_branch, else_target));
                    pending.push((then_branch, then_target));
                }
                (Self::ForStep { step, .. }, Self::ForStep { step: target, .. })
                | (Self::While { body: step, .. }, Self::While { body: target, .. }) => {
                    pending.push((step, target));
                }
                (
                    Self::TryCatchInt32 {
                        try_body, handler, ..
                    },
                    Self::TryCatchInt32 {
                        try_body: try_target,
                        handler: handler_target,
                        ..
                    },
                ) => {
                    pending.push((handler, handler_target));
                    pending.push((try_body, try_target));
                }
                (Self::Switch { cases, .. }, Self::Switch { cases: targets, .. }) => {
                    for (case, target) in cases.iter().zip(targets) {
                        pending.push((&case.body, &mut target.body));
                    }
                }
                _ => {}
            }
        }
        result
    }
}

impl CStatement {
    // Sequence roots are persistent. Only the directly boxed children need
    // placeholders for the visitor; all other fields retain ordinary clone
    // semantics, including source provenance, loop contracts and call data.
    fn clone_shell(&self) -> Self {
        match self {
            Self::Skip => Self::Skip,
            Self::Break => Self::Break,
            Self::Continue => Self::Continue,
            Self::Goto { target } => Self::Goto { target: *target },
            Self::ForStep {
                step: _,
                exited_locals,
                continue_after,
            } => Self::ForStep {
                step: Box::new(Self::Skip),
                exited_locals: exited_locals.clone(),
                continue_after: *continue_after,
            },
            Self::Declare {
                initializer,
                name,
                c_type,
                volatile,
                pointee_volatile,
                constant,
                pointee_constant,
                zero_fill,
                declared_class,
            } => Self::Declare {
                initializer: initializer.clone(),
                name: name.clone(),
                c_type: *c_type,
                volatile: *volatile,
                pointee_volatile: *pointee_volatile,
                constant: *constant,
                pointee_constant: *pointee_constant,
                zero_fill: zero_fill.clone(),
                declared_class: declared_class.clone(),
            },
            Self::DeclareAggregate {
                name,
                layout,
                kind,
                declared_class,
            } => Self::DeclareAggregate {
                name: name.clone(),
                layout: layout.clone(),
                kind: *kind,
                declared_class: declared_class.clone(),
            },
            Self::CopyAggregate {
                target,
                source,
                layout,
            } => Self::CopyAggregate {
                target: target.clone(),
                source: source.clone(),
                layout: layout.clone(),
            },
            Self::InitializeScalarArray {
                target,
                source,
                element_type,
                count,
                copy,
                fresh,
            } => Self::InitializeScalarArray {
                target: target.clone(),
                source: source.clone(),
                element_type: *element_type,
                count: *count,
                copy: *copy,
                fresh: *fresh,
            },
            Self::Assign {
                name,
                expression,
                source,
            } => Self::Assign {
                name: name.clone(),
                expression: expression.clone(),
                source: source.clone(),
            },
            Self::CallAssign {
                target,
                function_name,
                arguments,
            } => Self::CallAssign {
                target: target.clone(),
                function_name: function_name.clone(),
                arguments: arguments.clone(),
            },
            Self::Call {
                function_name,
                arguments,
            } => Self::Call {
                function_name: function_name.clone(),
                arguments: arguments.clone(),
            },
            Self::HeapAllocate {
                target,
                bytes,
                zeroed,
                object_type,
            } => Self::HeapAllocate {
                target: target.clone(),
                bytes: bytes.clone(),
                zeroed: *zeroed,
                object_type: object_type.clone(),
            },
            Self::HeapFree { pointer } => Self::HeapFree {
                pointer: pointer.clone(),
            },
            Self::Assert { condition, label } => Self::Assert {
                condition: condition.clone(),
                label: label.clone(),
            },
            Self::Seq(value) => Self::Seq(value.clone()),
            Self::Return(value) => Self::Return(value.clone()),
            Self::Throw(value) => Self::Throw(value.clone()),
            Self::TryCatchInt32 {
                try_body: _,
                binding,
                handler: _,
                cleanup_unwind,
            } => Self::TryCatchInt32 {
                try_body: Box::new(Self::Skip),
                binding: binding.clone(),
                handler: Box::new(Self::Skip),
                cleanup_unwind: *cleanup_unwind,
            },
            Self::Store { pointer, value } => Self::Store {
                pointer: pointer.clone(),
                value: value.clone(),
            },
            Self::EndScalarReference(value) => Self::EndScalarReference(value.clone()),
            Self::ScalarReferenceScope(value) => Self::ScalarReferenceScope(value.clone()),
            Self::TypedStore {
                pointer,
                value,
                value_type,
                access_class,
                volatile,
                pointee_constant,
                source,
            } => Self::TypedStore {
                pointer: pointer.clone(),
                value: value.clone(),
                value_type: *value_type,
                access_class: access_class.clone(),
                volatile: *volatile,
                pointee_constant: *pointee_constant,
                source: source.clone(),
            },
            Self::Update {
                target,
                operator,
                operand,
            } => Self::Update {
                target: target.clone(),
                operator: *operator,
                operand: operand.clone(),
            },
            Self::If {
                condition,
                then_branch: _,
                else_branch: _,
            } => Self::If {
                condition: condition.clone(),
                then_branch: Box::new(Self::Skip),
                else_branch: Box::new(Self::Skip),
            },
            Self::While {
                condition,
                invariant,
                invariant_checks,
                effect_checks,
                resource_specs,
                ranking_measures,
                structural_measure,
                do_while,
                backedge_target,
                natural_exit_target,
                body: _,
            } => Self::While {
                condition: condition.clone(),
                invariant: invariant.clone(),
                invariant_checks: invariant_checks.clone(),
                effect_checks: effect_checks.clone(),
                resource_specs: resource_specs.clone(),
                ranking_measures: ranking_measures.clone(),
                structural_measure: structural_measure.clone(),
                do_while: *do_while,
                backedge_target: *backedge_target,
                natural_exit_target: *natural_exit_target,
                body: Box::new(Self::Skip),
            },
            Self::Switch { expression, cases } => Self::Switch {
                expression: expression.clone(),
                cases: cases
                    .iter()
                    .map(|case| CSwitchCase {
                        value: case.value,
                        body: Box::new(Self::Skip),
                    })
                    .collect(),
            },
            Self::EndAutomaticLifetimes { names } => Self::EndAutomaticLifetimes {
                names: names.clone(),
            },
        }
    }
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/primitives/statement_clone.rs");
}
