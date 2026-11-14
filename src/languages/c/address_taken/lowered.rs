//! Addressability of imported executable bodies, including generated captures.
//! Walk the actual typed body. An opaque non-null pointer literal disables the
//! summary: unlike source address expressions, it can name arbitrary storage.

use super::AddressTakenSummary;
use crate::kernel::{
    ProgramExpression, ProgramFunction, ProgramStatement, ProgramType, ProgramValue,
};

fn declare(summary: &mut AddressTakenSummary, name: &str, ty: ProgramType) {
    if ty.is_pointer()
        || matches!(
            ty,
            ProgramType::Bool
                | ProgramType::Int8
                | ProgramType::UInt8
                | ProgramType::Int16
                | ProgramType::UInt16
                | ProgramType::Int32
                | ProgramType::UInt32
                | ProgramType::Int64
                | ProgramType::UInt64
                | ProgramType::Float32
                | ProgramType::Float64
        )
    {
        summary.scalar_declarations.insert(name.to_owned());
    } else {
        summary.taken.insert(name.to_owned());
    }
}

pub(super) fn summarize(function: &ProgramFunction, summary: &mut AddressTakenSummary) -> bool {
    for parameter in function.parameters() {
        crate::instrumentation::record_deterministic_work(1);
        if parameter.aggregate_layout().is_some() {
            summary.taken.insert(parameter.name().to_owned());
        } else {
            declare(summary, parameter.name(), parameter.c_type());
        }
    }
    let mut statements = vec![function.body()];
    let mut expressions = Vec::new();
    while let Some(statement) = statements.pop() {
        crate::instrumentation::record_deterministic_work(1);
        match statement {
            ProgramStatement::Declare {
                name,
                c_type,
                initializer,
                ..
            } => {
                declare(summary, name, *c_type);
                expressions.extend(initializer.iter().map(|expression| (expression, false)));
            }
            ProgramStatement::DeclareAggregate { name, .. } => {
                summary.taken.insert(name.clone());
            }
            ProgramStatement::Skip
            | ProgramStatement::EndScalarReference(_)
            | ProgramStatement::ScalarReferenceScope(_)
            | ProgramStatement::Break
            | ProgramStatement::Continue
            | ProgramStatement::Goto { .. }
            | ProgramStatement::EndAutomaticLifetimes { .. } => {}
            ProgramStatement::Assign { expression, .. }
            | ProgramStatement::Return(expression)
            | ProgramStatement::Throw(expression)
            | ProgramStatement::Switch { expression, .. } => {
                expressions.push((expression, false));
                if let ProgramStatement::Switch { cases, .. } = statement {
                    statements.extend(cases.iter().map(|case| case.body.as_ref()));
                }
            }
            ProgramStatement::Call { arguments, .. }
            | ProgramStatement::CallResult { arguments, .. }
            | ProgramStatement::CallAssign { arguments, .. } => {
                expressions.extend(arguments.iter().map(|argument| (argument, false)));
            }
            ProgramStatement::HeapAllocate { bytes, .. } => expressions.push((bytes, false)),
            ProgramStatement::HeapFree { pointer } => expressions.push((pointer, false)),
            ProgramStatement::Assert { condition, .. }
            | ProgramStatement::LoopTest { condition } => expressions.push((condition, false)),
            ProgramStatement::Store { pointer, value }
            | ProgramStatement::TypedStore { pointer, value, .. } => {
                expressions.extend([(pointer, false), (value, false)]);
            }
            ProgramStatement::CopyAggregate { target, source, .. }
            | ProgramStatement::InitializeScalarArray { target, source, .. }
            | ProgramStatement::Update {
                target,
                operand: source,
                ..
            } => {
                expressions.extend([(target, false), (source, false)]);
            }
            ProgramStatement::Seq(sequence) => {
                // The pair nodes beyond the first the tree held.
                crate::instrumentation::record_deterministic_work(sequence.len() - 2);
                statements.extend(sequence.iter().map(|statement| statement.as_ref()))
            }
            ProgramStatement::TryCatchInt32 {
                try_body,
                binding,
                handler,
                ..
            } => {
                declare(summary, binding, ProgramType::Int32);
                statements.extend([try_body.as_ref(), handler.as_ref()]);
            }
            ProgramStatement::If {
                condition,
                then_branch,
                else_branch,
            } => {
                expressions.push((condition, false));
                statements.extend([then_branch.as_ref(), else_branch.as_ref()]);
            }
            ProgramStatement::While {
                condition, body, ..
            } => {
                expressions.push((condition, false));
                statements.push(body);
            }
            ProgramStatement::ForStep { step, .. } => statements.push(step),
        }
    }
    while let Some((expression, addressed)) = expressions.pop() {
        crate::instrumentation::record_deterministic_work(1);
        match expression {
            ProgramExpression::Value(value) => {
                if matches!(value, ProgramValue::Pointer(pointer) if pointer.pointer() != &crate::kernel::Pointer::null())
                {
                    return false;
                }
            }
            ProgramExpression::Variable(name) => {
                if addressed {
                    summary.taken.insert(name.clone());
                }
            }
            ProgramExpression::FunctionAddress(_) | ProgramExpression::CallResult { .. } => {}
            ProgramExpression::AddressOf(value)
            | ProgramExpression::CheckedObjectAddress(value) => {
                expressions.push((value, true));
            }
            ProgramExpression::Cast {
                expression: value, ..
            }
            | ProgramExpression::FloatNegate(value)
            | ProgramExpression::FloatClassification {
                expression: value, ..
            }
            | ProgramExpression::PointerOffsetBytes { pointer: value, .. }
            | ProgramExpression::Subobject { pointer: value, .. }
            | ProgramExpression::Not(value)
            | ProgramExpression::BitwiseNot(value)
            | ProgramExpression::Load(value)
            | ProgramExpression::TypedLoad { pointer: value, .. }
            | ProgramExpression::EnumField { value, .. }
            | ProgramExpression::EnumIs { value, .. } => expressions.push((value, addressed)),
            ProgramExpression::EnumConstruct { fields, .. } => {
                expressions.extend(fields.iter().map(|field| (field, addressed)))
            }
            ProgramExpression::Conditional {
                condition,
                then_branch,
                else_branch,
            } => {
                expressions.extend([
                    (condition.as_ref(), addressed),
                    (then_branch.as_ref(), addressed),
                    (else_branch.as_ref(), addressed),
                ]);
            }
            crate::kernel::binary_c_expression!(left, right) => {
                expressions.extend([(left.as_ref(), addressed), (right.as_ref(), addressed)]);
            }
        }
    }
    true
}

#[cfg(test)]
mod tests {
    use crate::kernel::*;
    use crate::languages::c::{
        address_taken::summarize_address_taken,
        syntax::{C0Function, C0Type},
    };

    fn imported(body: ProgramStatement) -> C0Function {
        C0Function::external(C0Type::Void, "imported".into(), vec![])
            .with_prelowered_kernel_function(c_function(
                ProgramType::Void,
                "imported",
                vec![],
                body,
            ))
    }

    // Imported bodies must participate in the same whole-program name rule as
    // C bodies, and array/aggregate names already expose their storage address.
    #[test]
    fn imported_addressability_tracks_captures_escapes_and_arrays() {
        let first = imported(c_seq(
            c_declare("capture", ProgramType::Int32Pointer),
            c_seq(
                c_declare("escaped", ProgramType::Int32),
                c_declare("array", ProgramType::Int32Array(2)),
            ),
        ));
        let second = imported(c_call(
            "callee",
            vec![ProgramExpression::AddressOf(Box::new(c_variable(
                "escaped",
            )))],
        ));
        let summary = summarize_address_taken([&first, &second]);
        assert!(summary.never_taken().contains("capture"));
        assert!(!summary.never_taken().contains("escaped"));
        assert!(!summary.never_taken().contains("array"));
    }

    #[test]
    fn opaque_imported_pointer_literals_disable_the_bundle_summary() {
        let function = imported(c_seq(
            c_declare("capture", ProgramType::Int32),
            c_return(c_pointer_value(Pointer {
                block: "local:capture".into(),
                offset: PointerOffsetTerm::Constant(0),
            })),
        ));
        assert!(
            summarize_address_taken([&function])
                .never_taken()
                .is_empty()
        );
    }

    #[cfg(test)]
    mod scaling_tests {
        include!("../../../scaling_tests/languages/c/address_taken/lowered/tests.rs");
    }
}
