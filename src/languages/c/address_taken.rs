//! Which automatic objects a program can form the address of.
//!
//! One conservative syntactic pass over every parsed function body, run before
//! any verification query, so that the kernel can decide that a pointer value
//! it cannot resolve does not designate a local the program never addresses.
//! The answer is a set of declaration references, shared across a verification
//! session. C declarations in different functions or scopes have distinct IDs;
//! the legacy Named alternative remains conservative for other frontends.
//!
//! The pass is default-deny. A declaration is reported only for scalar or
//! pointer objects whose address never occurs under an address-forming node.
//! An undeclared reference or opaque runtime pointer literal contributes no
//! inaccessible-local claim.
//!
//! The two structural walks below (`child_expressions`, `child_statements`)
//! are the only exhaustive matches: a syntax form added later must be added to
//! them, and until it is, the compiler refuses to build rather than letting
//! the pass walk past it.

use std::collections::BTreeSet;

use super::syntax::{CExpression, CStatement, CSwitchCase, ImportedFunction, InterfaceType};

mod lowered;

/// What one pass learned about one bundle of parsed function bodies.
pub struct AddressTakenSummary {
    /// Every name declared as an automatic object with a scalar or pointer
    /// type, anywhere in the bundle.
    scalar_declarations: BTreeSet<crate::kernel::BindingName>,
    /// Every name the bundle can form an address of: declared with an
    /// aggregate type somewhere, so that its name converts to a pointer on
    /// use, or occurring anywhere under an address-forming node.
    taken: BTreeSet<crate::kernel::BindingName>,
}

impl AddressTakenSummary {
    /// The names no function in this bundle can form the address of.
    pub fn never_taken(&self) -> BTreeSet<crate::kernel::BindingName> {
        self.scalar_declarations
            .difference(&self.taken)
            .cloned()
            .collect()
    }

    /// The names this bundle shows to be addressable. A name absent from both
    /// sets was never declared here and is addressable by default.
    pub fn taken(&self) -> &BTreeSet<crate::kernel::BindingName> {
        &self.taken
    }
}

/// Runs the pass over every function in a parsed source bundle.
///
/// A function whose body the C frontend did not produce contributes no
/// declarations, which is the safe direction for an external declaration: it
/// has no automatic objects of this program at all. A function carrying a
/// pre-lowered kernel body from another frontend is different — it has
/// executable semantics analyzed by the typed-body walk, including generated
/// scalar captures. If that walk encounters an opaque pointer literal, the
/// whole bundle remains conservative and reports no inaccessible locals.
pub fn summarize_address_taken<'a>(
    functions: impl IntoIterator<Item = &'a ImportedFunction>,
) -> AddressTakenSummary {
    let mut summary = AddressTakenSummary {
        scalar_declarations: BTreeSet::new(),
        taken: BTreeSet::new(),
    };
    let mut unreadable_body = false;
    for function in functions {
        if let Some(lowered) = function.prelowered_kernel_function() {
            unreadable_body |= !lowered::summarize(lowered, &mut summary);
            continue;
        }
        for parameter in function.parameters() {
            declare(
                &mut summary,
                parameter.binding_name(),
                parameter.interface_type(),
            );
        }
        walk_statement(function.body(), &mut summary);
    }
    if unreadable_body {
        summary.scalar_declarations.clear();
    }
    summary
}

/// Records one automatic declaration. An aggregate or array object's name
/// converts to its address wherever it is used, so declaring one is itself a
/// way for the program to hold that address; such a name is refused rather
/// than tracked.
fn declare(
    summary: &mut AddressTakenSummary,
    name: &crate::kernel::BindingName,
    interface_type: InterfaceType,
) {
    if scalar_or_pointer(interface_type) {
        summary.scalar_declarations.insert(name.clone());
    } else {
        summary.taken.insert(name.clone());
    }
}

/// Whether an object of this type is read and written as a value rather than
/// through its address. Listed exhaustively on purpose: a type added later
/// lands in the `false` arm, which refuses the name.
fn scalar_or_pointer(interface_type: InterfaceType) -> bool {
    match interface_type {
        InterfaceType::Parameter(_) | InterfaceType::ParameterPointer(_) => false,
        InterfaceType::Int128 | InterfaceType::UInt128 => false,
        InterfaceType::Int8 | InterfaceType::Int8Pointer | InterfaceType::Int8PointerPointer => {
            true
        }
        InterfaceType::Char(_)
        | InterfaceType::Bool
        | InterfaceType::Int16
        | InterfaceType::Int32
        | InterfaceType::UInt8
        | InterfaceType::UInt16
        | InterfaceType::UInt32
        | InterfaceType::Int64(_)
        | InterfaceType::UInt64(_)
        | InterfaceType::Float32
        | InterfaceType::Float64
        | InterfaceType::VoidPointer
        | InterfaceType::VoidPointerPointer
        | InterfaceType::Pointer
        | InterfaceType::CharPointer(_)
        | InterfaceType::CharPointerPointer(_)
        | InterfaceType::Int16Pointer
        | InterfaceType::UInt16Pointer
        | InterfaceType::Int32Pointer
        | InterfaceType::UInt8Pointer
        | InterfaceType::UInt32Pointer
        | InterfaceType::Int128Pointer
        | InterfaceType::Int64Pointer(_)
        | InterfaceType::UInt128Pointer
        | InterfaceType::UInt64Pointer(_)
        | InterfaceType::Float32Pointer
        | InterfaceType::Float64Pointer
        | InterfaceType::Int16PointerPointer
        | InterfaceType::UInt16PointerPointer
        | InterfaceType::Int32PointerPointer
        | InterfaceType::UInt8PointerPointer
        | InterfaceType::UInt32PointerPointer
        | InterfaceType::Int128PointerPointer
        | InterfaceType::Int64PointerPointer(_)
        | InterfaceType::UInt128PointerPointer
        | InterfaceType::UInt64PointerPointer(_)
        | InterfaceType::Float32PointerPointer
        | InterfaceType::Float64PointerPointer
        | InterfaceType::FunctionPointer(_) => true,
        InterfaceType::Int8Array(_) => false,
        InterfaceType::PointerArray(_, _, _) => false,
        InterfaceType::Void
        | InterfaceType::CharArray(_, _)
        | InterfaceType::Int32Array(_)
        | InterfaceType::UInt8Array(_)
        | InterfaceType::Int16Array(_)
        | InterfaceType::UInt16Array(_)
        | InterfaceType::UInt32Array(_)
        | InterfaceType::Int128Array(_)
        | InterfaceType::Int64Array(_, _)
        | InterfaceType::UInt128Array(_)
        | InterfaceType::UInt64Array(_, _)
        | InterfaceType::Float32Array(_)
        | InterfaceType::Float64Array(_) => false,
    }
}

/// Walks one statement, recording declarations and address-forming nodes.
fn walk_statement(statement: &CStatement, summary: &mut AddressTakenSummary) {
    if let CStatement::Declare {
        name,
        interface_type,
        ..
    } = statement
    {
        declare(summary, name, *interface_type);
    }
    // A struct value's name is its address wherever it is used.
    if let CStatement::DeclareStructValue { name, .. } = statement {
        summary.taken.insert(name.clone().into());
    }
    let mut expressions = Vec::new();
    let mut statements = Vec::new();
    child_statements(statement, &mut expressions, &mut statements);
    for expression in expressions {
        walk_expression(expression, summary);
    }
    for statement in statements {
        walk_statement(statement, summary);
    }
}

/// Walks one expression, refusing every name under an address-forming node.
///
/// The three address-forming nodes are `&e` and the two aggregate-place nodes
/// the parser uses to carry a struct or union place through member selection.
/// Every name under one of them is refused whatever its shape, so `&x`,
/// `&a[i]`, `&s.f` and `&*p` are all caught, and so is the index in `&a[i]`.
/// The `AddressOf(Variable(_))` test in `src/kernel/termination.rs` catches
/// only the first of those.
fn walk_expression(expression: &CExpression, summary: &mut AddressTakenSummary) {
    if let CExpression::AddressOf(inner)
    | CExpression::AggregateAddress { pointer: inner, .. }
    | CExpression::UnionAddress { pointer: inner, .. } = expression
    {
        mentioned_names(inner, &mut summary.taken);
        return;
    }
    let mut expressions = Vec::new();
    let mut statements = Vec::new();
    child_expressions(expression, &mut expressions, &mut statements);
    for expression in expressions {
        walk_expression(expression, summary);
    }
    for statement in statements {
        walk_statement(statement, summary);
    }
}

/// Every name an expression mentions, at any depth and through any form,
/// including the names its embedded statements declare and read.
pub(super) fn mentioned_names(
    expression: &CExpression,
    names: &mut BTreeSet<crate::kernel::BindingName>,
) {
    match expression {
        CExpression::Variable(name)
        | CExpression::Assignment { name, .. }
        | CExpression::ScalarUpdate { name, .. } => {
            names.insert(name.clone());
        }
        _ => {}
    }
    let mut expressions = Vec::new();
    let mut statements = Vec::new();
    child_expressions(expression, &mut expressions, &mut statements);
    for expression in expressions {
        mentioned_names(expression, names);
    }
    for statement in statements {
        statement_mentioned_names(statement, names);
    }
}

/// The same for a statement, used for a statement expression under an `&`.
fn statement_mentioned_names(
    statement: &CStatement,
    names: &mut BTreeSet<crate::kernel::BindingName>,
) {
    match statement {
        CStatement::Declare { name, .. } | CStatement::DeclareStructValue { name, .. } => {
            names.insert(name.binding().clone());
        }
        CStatement::Assign { name, .. } | CStatement::HeapAllocate { target: name, .. } => {
            names.insert(name.clone());
        }
        _ => {}
    }
    let mut expressions = Vec::new();
    let mut statements = Vec::new();
    child_statements(statement, &mut expressions, &mut statements);
    for expression in expressions {
        mentioned_names(expression, names);
    }
    for statement in statements {
        statement_mentioned_names(statement, names);
    }
}

/// The immediate subexpressions and substatements of one expression.
pub(crate) fn child_expressions<'a>(
    expression: &'a CExpression,
    expressions: &mut Vec<&'a CExpression>,
    statements: &mut Vec<&'a CStatement>,
) {
    match expression {
        CExpression::ScalarUpdate { .. } => {}
        CExpression::StringLiteral(_)
        | CExpression::Void
        | CExpression::Variable(_)
        | CExpression::BuiltinConstantP { .. }
        | CExpression::StepResult { .. }
        | CExpression::FunctionAddress(_)
        | CExpression::Int32Literal(_)
        | CExpression::UInt8Literal(_)
        | CExpression::UInt32Literal(_)
        | CExpression::Int64Literal(_)
        | CExpression::UInt64Literal(_)
        | CExpression::Float32Literal(_)
        | CExpression::Float64Literal(_)
        | CExpression::SizeOfStruct { .. }
        | CExpression::SizeOfUnion { .. }
        | CExpression::SizeOfType { .. } => {}
        CExpression::Call { arguments, .. } => expressions.extend(arguments.iter()),
        CExpression::VariableArguments(arguments) => {
            expressions.extend(arguments.iter().map(|(_, argument)| argument));
        }
        CExpression::IndirectCall {
            function,
            arguments,
            ..
        } => {
            expressions.push(function);
            expressions.extend(arguments.iter());
        }
        CExpression::Assignment { value, .. } => expressions.push(value),
        CExpression::StatementExpression { body, value, .. } => {
            statements.push(body);
            expressions.push(value);
        }
        CExpression::Cast { expression, .. }
        | CExpression::FloatNegate(expression)
        | CExpression::FloatClassification { expression, .. }
        | CExpression::AddressOf(expression)
        | CExpression::PointerOffsetBytes {
            pointer: expression,
            ..
        }
        | CExpression::Subobject {
            pointer: expression,
            ..
        }
        | CExpression::Not(expression)
        | CExpression::BitwiseNot(expression)
        | CExpression::Load(expression, _)
        | CExpression::SequentialRead {
            target: expression, ..
        }
        | CExpression::AggregateAddress {
            pointer: expression,
            ..
        }
        | CExpression::Field {
            pointer: expression,
            ..
        }
        | CExpression::UnionField {
            pointer: expression,
            ..
        }
        | CExpression::UnionAddress {
            pointer: expression,
            ..
        }
        | CExpression::CheckedArrayIndex {
            index: expression, ..
        } => expressions.push(expression),
        CExpression::Ternary {
            condition,
            then_branch,
            else_branch,
        } => {
            expressions.push(condition);
            expressions.push(then_branch);
            expressions.push(else_branch);
        }
        CExpression::SequentialWrite { target, value, .. } => {
            expressions.push(target);
            expressions.push(value);
        }
        crate::languages::c::syntax::binary_c_expression!(left, right) => {
            expressions.push(left);
            expressions.push(right);
        }
    }
}

/// The immediate subexpressions and substatements of one statement.
pub(crate) fn child_statements<'a>(
    statement: &'a CStatement,
    expressions: &mut Vec<&'a CExpression>,
    statements: &mut Vec<&'a CStatement>,
) {
    match statement {
        CStatement::EndAggregateLifetimes { .. }
        | CStatement::FillArrayTail { .. }
        | CStatement::BuiltinConstantP { .. }
        | CStatement::Skip
        | CStatement::Break
        | CStatement::Continue
        | CStatement::Goto { .. }
        | CStatement::DeclareStructValue { .. } => {}
        CStatement::Label { statement, .. } => statements.push(statement),
        CStatement::Declare {
            initializer,
            zero_fill,
            ..
        } => {
            expressions.extend(
                initializer.iter().chain(
                    zero_fill
                        .iter()
                        .flat_map(|fill| fill.written_elements.iter().map(|(_, value)| value)),
                ),
            );
        }
        CStatement::Assign { expression, .. } => expressions.push(expression),
        CStatement::Call { arguments, .. } | CStatement::CallResult { arguments, .. } => {
            expressions.extend(arguments.iter());
        }
        CStatement::IndirectCall {
            function,
            arguments,
            ..
        } => {
            expressions.push(function);
            expressions.extend(arguments.iter());
        }
        CStatement::HeapAllocate { bytes, .. } => expressions.push(bytes),
        CStatement::HeapFree { pointer, .. } => expressions.push(pointer),
        CStatement::Assert { condition, .. }
        | CStatement::LoopTest { condition, .. }
        | CStatement::StepValue {
            expression: condition,
            ..
        } => expressions.push(condition),
        CStatement::Seq(first, second) => {
            statements.push(first);
            statements.push(second);
        }
        CStatement::Return(value, _) => expressions.push(value),
        CStatement::Store { pointer, value, .. } => {
            expressions.push(pointer);
            expressions.push(value);
        }
        CStatement::SequentialStore { target, value, .. }
        | CStatement::AggregateCopy {
            target,
            source: value,
            ..
        } => {
            expressions.push(target);
            expressions.push(value);
        }
        CStatement::Update {
            target, operand, ..
        } => {
            expressions.push(target);
            expressions.push(operand);
        }
        CStatement::If {
            condition,
            then_branch,
            else_branch,
            ..
        } => {
            expressions.push(condition);
            statements.push(then_branch);
            statements.push(else_branch);
        }
        CStatement::While {
            test,
            condition,
            body,
            ..
        }
        | CStatement::DoWhile {
            test,
            condition,
            body,
            ..
        } => {
            expressions.push(condition);
            statements.push(body);
            if let Some(test) = test {
                statements.push(test);
            }
        }
        CStatement::For {
            test,
            initializer,
            condition,
            step,
            body,
            ..
        } => {
            statements.push(initializer);
            expressions.push(condition);
            statements.push(step);
            statements.push(body);
            if let Some(test) = test {
                statements.push(test);
            }
        }
        CStatement::Switch {
            expression, cases, ..
        } => {
            expressions.push(expression);
            statements.extend(cases.iter().map(CSwitchCase::body));
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn summary(source: &str) -> AddressTakenSummary {
        let functions = super::super::syntax::parse_functions_for_source(source, "address.c")
            .expect("the fixture parses");
        summarize_address_taken(&functions)
    }

    #[test]
    fn a_scalar_local_whose_address_is_never_taken_is_reported() {
        let summary = summary("int32 f(void) { int32 x; int32* q; x = 5; return x; }\n");
        let never = summary.never_taken();
        assert!(
            never.iter().any(|binding| binding.source_name() == "x"),
            "{never:?}"
        );
        assert!(
            never.iter().any(|binding| binding.source_name() == "q"),
            "{never:?}"
        );
    }

    #[test]
    fn every_way_to_form_an_address_refuses_the_name() {
        let call = summary(
            "int32* echo(int32* p) { return p; }\nvoid f(void) { int32 x; int32* q; x = 5; q = echo(&x); x = 1; }\n",
        );
        assert!(
            !call
                .never_taken()
                .iter()
                .any(|binding| binding.source_name() == "x"),
            "{:?}",
            call.taken()
        );
        let indexed =
            summary("void f(void) { int32 a[4]; int32 i; int32* p; i = 0; p = &a[i]; }\n");
        assert!(
            !indexed
                .never_taken()
                .iter()
                .any(|binding| binding.source_name() == "a")
        );
        assert!(
            !indexed
                .never_taken()
                .iter()
                .any(|binding| binding.source_name() == "i")
        );
        let field = summary(
            "struct pair { int32 first; };\nvoid f(void) { struct pair s; int32* p; s.first = 1; p = &s.first; }\n",
        );
        assert!(
            !field
                .never_taken()
                .iter()
                .any(|binding| binding.source_name() == "s")
        );
    }

    /// An address does not have to come back from the call it was handed to.
    /// `stash` parks it in storage and `fetch` hands it back later, so nothing
    /// connects the pointer `v` reads through to the `&x` it wrote. The pass
    /// answers about the `&`, not about where the address went, so the name is
    /// refused all the same.
    #[test]
    fn an_address_parked_in_storage_is_still_an_address() {
        let summary = summary(
            "void stash(int32** slot, int32* p) { *slot = p; }\nint32* fetch(int32** slot) { return *slot; }\nvoid v(int32** slot) { int32 x; int32* q; x = 5; stash(slot, &x); q = fetch(slot); x = 1; }\n",
        );
        assert!(
            !summary
                .never_taken()
                .iter()
                .any(|binding| binding.source_name() == "x"),
            "the address escaped into `*slot`: {:?}",
            summary.never_taken()
        );
    }

    #[test]
    fn addressability_is_specific_to_a_declaration_in_its_function() {
        let summary = summary(
            "int32* echo(int32* p) { return p; }\nvoid taker(void) { int32 x; int32* q; q = echo(&x); }\nint32 innocent(void) { int32 x; x = 5; return x; }\n",
        );
        let never = summary.never_taken();
        assert!(never.iter().any(|binding| {
            binding
                .local_id()
                .is_some_and(|id| id.function() == "innocent" && id.spelling() == Some("x"))
        }));
        assert!(!never.iter().any(|binding| {
            binding
                .local_id()
                .is_some_and(|id| id.function() == "taker" && id.spelling() == Some("x"))
        }));
    }
}
