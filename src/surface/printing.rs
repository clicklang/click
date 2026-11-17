use super::diagnostics::{
    aligned_sugar, describe_code_region_ref, describe_contract_expression,
    describe_contract_segment, describe_program_expression, describe_program_point_selector,
    describe_resource_subject, program_point_aligned_sugar,
};
use super::*;

/// Click source that parses back. Every spelling is chosen by its caller;
/// no output depends on who else is printing.
pub(in crate::surface) fn source_click_proposition(proposition: &ClickProposition) -> String {
    print_proposition(proposition, PropositionSpelling::Source)
}

// The checker retains equality evidence internally. The Surface operation
// states its directed endpoints separately, preserving the same source type
// barriers as an equality comparison.
fn source_rewrite_arguments(equality: &ClickProposition) -> String {
    fn operands(equality: &ClickProposition, positive: bool) -> (String, String) {
        match equality {
            ClickProposition::Comparison {
                left,
                operator,
                right,
            } if (*operator == ComparisonOperator::Equal && positive)
                || (*operator == ComparisonOperator::NotEqual && !positive) =>
            {
                (
                    comparison_operand(left, right, PropositionSpelling::Source),
                    comparison_operand(right, left, PropositionSpelling::Source),
                )
            }
            ClickProposition::At {
                selector,
                proposition,
            } => {
                let (left, right) = operands(proposition, positive);
                let selector = describe_program_point_selector(selector);
                (
                    format!("at({selector}, {left})"),
                    format!("at({selector}, {right})"),
                )
            }
            ClickProposition::Not(inner) => operands(inner, !positive),
            _ => unreachable!("a checked rewrite must carry equality evidence"),
        }
    }
    let (left, right) = operands(equality, true);
    format!("{left}, {right}")
}

// Preserve retains its exact separation evidence internally. Its public
// arguments select the kept resource and the transition independently.
fn source_preserve_arguments(separation: &ClickProposition) -> String {
    fn operands(separation: &ClickProposition) -> (String, String) {
        match separation {
            ClickProposition::Separate { left, right } => {
                let (region, resource) = match (left, right) {
                    (ResourceSubject::Footprint(region), resource)
                    | (resource, ResourceSubject::Footprint(region)) => (region, resource),
                    _ => unreachable!("a checked preserve must cite a region footprint"),
                };
                (
                    describe_resource_subject(resource),
                    describe_code_region_ref(region),
                )
            }
            ClickProposition::At {
                selector,
                proposition,
            } => {
                let (resource, region) = operands(proposition);
                (
                    format!(
                        "at({}, {resource})",
                        describe_program_point_selector(selector)
                    ),
                    region,
                )
            }
            _ => unreachable!("a checked preserve must carry separation evidence"),
        }
    }
    let (resource, region) = operands(separation);
    format!("{resource}, {region}")
}

/// A proposition spelled for a refusal a person reads. It may print a term
/// as what it means, such as an unsigned order, in a form that is not Click
/// source, so it never reaches generated source.
pub(in crate::surface) fn refusal_click_proposition(proposition: &ClickProposition) -> String {
    print_proposition(proposition, PropositionSpelling::Refusal)
}

// Diagnostic quotations retain the declaration's spelling; certificate-only
// type barriers must not change messages about an authored proposition.
pub(in crate::surface) fn authored_click_proposition(proposition: &ClickProposition) -> String {
    print_proposition(proposition, PropositionSpelling::Authored)
}

#[derive(Clone, Copy, Eq, PartialEq)]
pub(super) enum PropositionSpelling {
    Source,
    Authored,
    Diagnostic,
    Refusal,
}

// Population counts are int32 values. An unobserved machine comparison
// must keep that type when reparsed: Integer specification arithmetic
// otherwise promotes a comparison containing `count(...)`.
fn comparison_operand(
    expression: &ContractExpression,
    other: &ContractExpression,
    mode: PropositionSpelling,
) -> String {
    fn typed_count_reference(expression: &ContractExpression) -> Option<String> {
        match expression {
            ContractExpression::ResourceCount(_) => Some(format!(
                "({})",
                crate::surface::diagnostics::click_cast(
                    &describe_contract_expression(expression),
                    "int32"
                )
            )),
            ContractExpression::Old(inner) => {
                Some(format!("old({})", typed_count_reference(inner)?))
            }
            ContractExpression::At {
                selector,
                expression,
            } => Some(format!(
                "at({}, {})",
                describe_program_point_selector(selector),
                typed_count_reference(expression)?,
            )),
            _ => None,
        }
    }
    if mode == PropositionSpelling::Source
        && let Some(rendered) = typed_count_reference(expression)
    {
        return rendered;
    }
    // Generated machine arithmetic must retain its type when reparsed as
    // specification syntax, including arithmetic outside a state.
    if mode == PropositionSpelling::Source
        && let Some(machine_type) = machine_arithmetic(expression, integer_comparison_type(other))
    {
        return crate::surface::diagnostics::click_cast(
            &describe_contract_expression(expression),
            machine_type,
        );
    }
    describe_contract_expression(expression)
}

/// The integer type a comparison operand fixes for the comparison: a typed
/// machine constant, or arithmetic the barrier below already types. An
/// `int32` zero is not one, since it also spells the null pointer. A
/// comparison with such an operand compares integer words, so its other
/// operand's `+` or `-` is word arithmetic, never pointer arithmetic.
fn integer_comparison_type(other: &ContractExpression) -> Option<&'static str> {
    let mut inner = other;
    while let ContractExpression::Old(next)
    | ContractExpression::At {
        expression: next, ..
    } = inner
    {
        inner = next;
    }
    match inner {
        ContractExpression::ProgramExpression(ProgramExpression::Value(value)) => match value {
            ProgramValue::UInt32(_) => Some("uint32"),
            ProgramValue::Int64(_) => Some("int64"),
            ProgramValue::UInt64(_) => Some("uint64"),
            ProgramValue::Int32(term)
                if matches!(term, crate::kernel::bits32_constant!(_))
                    && !matches!(term, crate::kernel::bits32_constant!(0)) =>
            {
                Some("int32")
            }
            _ => None,
        },
        _ => machine_arithmetic(other, None),
    }
}

/// Preserve the existing machine-arithmetic type barrier both at states
/// and in current-state comparison operands. Mathematical Integer operands
/// do not receive a machine cast. `comparison` is the integer type the
/// comparison's other operand fixes, if it fixes one: then a current-state
/// `+` or `-` is word arithmetic too, and receives the barrier, since the
/// parser reads a comparison operand that does arithmetic as an Integer.
fn machine_arithmetic(
    expression: &ContractExpression,
    comparison: Option<&'static str>,
) -> Option<&'static str> {
    let mut inner = expression;
    let mut retained_state = false;
    while let ContractExpression::Old(next)
    | ContractExpression::At {
        expression: next, ..
    } = inner
    {
        retained_state = true;
        inner = next;
    }
    // A negative literal prints with a unary minus. Specification parsing
    // reads that as Integer arithmetic, so retain its machine type explicitly.
    if matches!(inner,
        ContractExpression::ProgramExpression(ProgramExpression::Value(
            ProgramValue::Int64(crate::kernel::int64_constant!(bits))
        )) if crate::kernel::constant_i64(*bits) < 0)
    {
        return Some("int64");
    }
    // Surface addition/subtraction may be pointer arithmetic. A typed
    // literal nested inside it does not determine the result type:
    // `a + (i + 1u64)` can be a pointer. Preserve its source semantics;
    // generated C arithmetic still receives the machine barrier below.
    if !retained_state
        && comparison.is_none()
        && matches!(
            inner,
            ContractExpression::Add(..) | ContractExpression::Subtract(..)
        )
    {
        return None;
    }
    fn c_arithmetic(expression: &ProgramExpression) -> bool {
        matches!(
            expression,
            ProgramExpression::Add(..)
                | ProgramExpression::Subtract(..)
                | ProgramExpression::Multiply(..)
                | ProgramExpression::Divide(..)
                | ProgramExpression::Remainder(..)
                | ProgramExpression::ShiftLeft(..)
                | ProgramExpression::RustShiftLeft(..)
                | ProgramExpression::ShiftRight(..)
                | ProgramExpression::RustShiftRight(..)
                | ProgramExpression::BitwiseAnd(..)
                | ProgramExpression::BitwiseOr(..)
                | ProgramExpression::BitwiseXor(..)
                | ProgramExpression::BitwiseNot(..)
        )
    }
    // The operation's operands, read under the same state.
    let mut machine = false;
    let mut interface_types = Vec::new();
    let mut contract_pending = vec![inner];
    let mut c_pending = Vec::new();
    let mut top = true;
    let mut opaque = false;
    while let Some(expression) = contract_pending.pop() {
        match expression {
            ContractExpression::Add(left, right)
            | ContractExpression::Subtract(left, right)
            | ContractExpression::Multiply(left, right)
            | ContractExpression::Divide(left, right)
            | ContractExpression::Remainder(left, right)
            | ContractExpression::ShiftLeft(left, right)
            | ContractExpression::RustShiftLeft(left, right)
            | ContractExpression::ShiftRight(left, right)
            | ContractExpression::RustShiftRight(left, right)
            | ContractExpression::BitwiseAnd(left, right)
            | ContractExpression::BitwiseOr(left, right)
            | ContractExpression::BitwiseXor(left, right) => {
                contract_pending.push(left);
                contract_pending.push(right);
            }
            ContractExpression::Negate(operand) | ContractExpression::BitwiseNot(operand) => {
                contract_pending.push(operand)
            }
            ContractExpression::IntegerLiteral(_) => return None,
            ContractExpression::ProgramExpression(ProgramExpression::Value(value)) if !top => {
                machine = true;
                interface_types.push(value.clone());
            }
            ContractExpression::ProgramExpression(fragment) => {
                if top && !c_arithmetic(fragment) {
                    return None;
                }
                machine |= top;
                c_pending.push(fragment);
            }
            _ if top => return None,
            _ => opaque = true,
        }
        top = false;
    }
    // Arithmetic over C operands alone, in a comparison of integer words,
    // is word arithmetic even with no typed operand of its own.
    if !machine && (comparison.is_none() || opaque || c_pending.is_empty()) {
        return None;
    }
    while let Some(expression) = c_pending.pop() {
        match expression {
            ProgramExpression::Value(value) => interface_types.push(value.clone()),
            ProgramExpression::Add(left, right)
            | ProgramExpression::Subtract(left, right)
            | ProgramExpression::Multiply(left, right)
            | ProgramExpression::Divide(left, right)
            | ProgramExpression::Remainder(left, right)
            | ProgramExpression::ShiftLeft(left, right)
            | ProgramExpression::RustShiftLeft(left, right)
            | ProgramExpression::ShiftRight(left, right)
            | ProgramExpression::RustShiftRight(left, right)
            | ProgramExpression::BitwiseAnd(left, right)
            | ProgramExpression::BitwiseOr(left, right)
            | ProgramExpression::BitwiseXor(left, right) => {
                c_pending.push(left);
                c_pending.push(right);
            }
            ProgramExpression::BitwiseNot(operand) => c_pending.push(operand),
            _ => {}
        }
    }
    // Current-state expressions without typed operands need their type
    // retained by the producer; do not infer it from variable spellings.
    if !retained_state && interface_types.is_empty() {
        return comparison;
    }
    let mut machine_type = "int32";
    for value in interface_types {
        machine_type = match value {
            ProgramValue::Int32(_) => continue,
            ProgramValue::UInt32(_) => "uint32",
            ProgramValue::Int64(_) => "int64",
            ProgramValue::UInt64(_) => "uint64",
            _ => return None,
        };
    }
    Some(machine_type)
}

pub(super) fn print_proposition(
    proposition: &ClickProposition,
    mode: PropositionSpelling,
) -> String {
    if let Some((pointer, alignment)) = aligned_sugar(proposition) {
        return format!(
            "aligned({}, {alignment})",
            describe_program_expression(pointer)
        );
    }
    if let Some((selector, pointer, alignment)) = program_point_aligned_sugar(proposition) {
        return format!(
            "at({}, aligned({}, {alignment}))",
            describe_program_point_selector(selector),
            describe_program_expression(pointer)
        );
    }
    match proposition {
        ClickProposition::Value(expression) => describe_contract_expression(expression),
        ClickProposition::Comparison {
            left,
            operator,
            right,
        } => format!(
            "{} {operator} {}",
            comparison_operand(left, right, mode),
            comparison_operand(right, left, mode)
        ),
        ClickProposition::FloatClassification {
            expression,
            classification,
        } => format!(
            "{}({})",
            match classification {
                syntax::CFloatClassification::Finite => "isfinite",
                syntax::CFloatClassification::Infinite => "isinf",
                syntax::CFloatClassification::Zero => "iszero",
                syntax::CFloatClassification::Subnormal => "issubnormal",
                syntax::CFloatClassification::Nan => "isnan",
            },
            describe_contract_expression(expression)
        ),
        ClickProposition::Separate { left, right } => format!(
            "separate({}, {})",
            describe_resource_subject(left),
            describe_resource_subject(right)
        ),
        ClickProposition::Contains { parent, child } => format!(
            "contains({}, {})",
            describe_resource_subject(parent),
            describe_resource_subject(child)
        ),
        ClickProposition::ResourceViewable { resource } => {
            format!("viewable({})", describe_resource_subject(resource))
        }
        ClickProposition::Loadable { segment } => {
            format!("viewable({})", describe_contract_segment(segment))
        }
        ClickProposition::Defined { expression } => {
            format!("defined({})", describe_contract_expression(expression))
        }
        ClickProposition::At {
            selector,
            proposition,
        } => format!(
            "at({}, {})",
            describe_program_point_selector(selector),
            print_proposition(proposition, mode)
        ),
        // Connectives print as the sidecar writes them, with only the
        // parentheses Click's precedence needs (`docs/reference/language/
        // grammar.md`): `implies` binds loosest and to the right, then `or`,
        // `and`, and prefix `not`.
        ClickProposition::And(left, right) => format!(
            "{} and {}",
            proposition_operand(left, CONNECTIVE_AND, mode),
            proposition_operand(right, CONNECTIVE_NOT, mode)
        ),
        ClickProposition::Or(left, right) => format!(
            "{} or {}",
            proposition_operand(left, CONNECTIVE_OR, mode),
            proposition_operand(right, CONNECTIVE_AND, mode)
        ),
        ClickProposition::Not(proposition) => {
            format!(
                "not {}",
                proposition_operand(proposition, CONNECTIVE_NOT, mode)
            )
        }
        ClickProposition::Implies(left, right) => format!(
            "{} implies {}",
            proposition_operand(left, CONNECTIVE_OR, mode),
            proposition_operand(right, CONNECTIVE_IMPLIES, mode)
        ),
        ClickProposition::ForAll {
            click_type,
            name,
            body,
            ..
        } => format!(
            "forall ({name}: {}) {{ {} }}",
            validation::describe_click_type(click_type),
            print_proposition(body, mode)
        ),
        ClickProposition::Exists {
            click_type,
            name,
            body,
            ..
        } => format!(
            "exists ({name}: {}) {{ {} }}",
            validation::describe_click_type(click_type),
            print_proposition(body, mode)
        ),
        ClickProposition::RangeAll { start, end, .. }
        | ClickProposition::RangeAny { start, end, .. }
            if let Some(predicate) = lambdas::range_predicate(proposition) =>
        {
            let method = if matches!(proposition, ClickProposition::RangeAll { .. }) {
                "all"
            } else {
                "any"
            };
            format!(
                "({}..{}).{method}({})",
                describe_contract_expression(start),
                describe_contract_expression(end),
                describe_contract_expression(predicate)
            )
        }
        ClickProposition::RangeAll {
            start,
            end,
            item,
            body,
            ..
        } => {
            let body = print_proposition(body, mode);
            let (start, end) = (
                describe_contract_expression(start),
                describe_contract_expression(end),
            );
            if matches!(
                mode,
                PropositionSpelling::Source | PropositionSpelling::Authored
            ) {
                format!("({start}..{end}).all(|{item}| {{ {body} }})")
            } else {
                format!("({start}..{end}).all({item} => {body})")
            }
        }
        ClickProposition::RangeAny {
            start,
            end,
            item,
            body,
            ..
        } => {
            let body = print_proposition(body, mode);
            let (start, end) = (
                describe_contract_expression(start),
                describe_contract_expression(end),
            );
            if matches!(
                mode,
                PropositionSpelling::Source | PropositionSpelling::Authored
            ) {
                format!("({start}..{end}).any(|{item}| {{ {body} }})")
            } else {
                format!("({start}..{end}).any({item} => {body})")
            }
        }
        ClickProposition::PredicateCall { name, arguments }
            if crate::kernel::TerminationAtomKind::from_spelling(name).is_some() =>
        {
            let arguments = arguments
                .iter()
                .map(|argument| {
                    let ContractExpression::Binding(name) = argument else {
                        unreachable!("termination labels are quoted names")
                    };
                    format!("{name:?}")
                })
                .collect::<Vec<_>>()
                .join(", ");
            format!("{name}({arguments})")
        }
        ClickProposition::PredicateCall { name, arguments } => format!(
            "{name}({})",
            arguments
                .iter()
                .map(describe_contract_expression)
                .collect::<Vec<_>>()
                .join(", ")
        ),
    }
}

const CONNECTIVE_IMPLIES: u8 = 1;
const CONNECTIVE_OR: u8 = 2;
const CONNECTIVE_AND: u8 = 3;
const CONNECTIVE_NOT: u8 = 4;

/// A proposition as an operand of a connective that needs at least
/// `minimum` precedence there, parenthesized when it binds more loosely.
fn proposition_operand(
    proposition: &ClickProposition,
    minimum: u8,
    mode: PropositionSpelling,
) -> String {
    let precedence = match proposition {
        ClickProposition::Implies(..) => CONNECTIVE_IMPLIES,
        ClickProposition::Or(..) => CONNECTIVE_OR,
        ClickProposition::And(..) => CONNECTIVE_AND,
        ClickProposition::Not(..) => CONNECTIVE_NOT,
        _ => u8::MAX,
    };
    let text = print_proposition(proposition, mode);
    if precedence < minimum {
        format!("({text})")
    } else {
        text
    }
}

pub fn format_proof_tactics(tactics: &[ProofTactic]) -> Result<String, CertificateError> {
    let certificate = ProofCertificate::from_proof_tactics(tactics)?;
    Ok(format_proof_certificate(&certificate))
}

pub(super) fn format_partial_tactic_sequence(tactics: &[ProofTactic]) -> String {
    let mut output = String::new();
    write_tactics(&mut output, tactics, 0);
    output.pop();
    output
}

pub fn format_proof_certificate(certificate: &ProofCertificate) -> String {
    let mut output = String::from("by {\n");
    write_tactics(&mut output, &certificate.to_proof_tactics(), 1);
    output.push('}');
    output
}

/// A whole proof block holding `tactics`, as [`format_proof_certificate`]
/// writes a certificate's.
pub(in crate::surface) fn format_proof_block(tactics: &[ProofTactic]) -> String {
    let mut output = String::from("by {\n");
    write_tactics(&mut output, tactics, 1);
    output.push('}');
    output
}

/// The assertions of a join's `ensuring` block, one per line.
fn write_join_interface(output: &mut String, assertions: &[ProofAssertion], indent: usize) {
    let prefix = "    ".repeat(indent);
    for assertion in assertions {
        let text = match assertion {
            ProofAssertion::Fact(fact) => format!("fact {};", source_click_proposition(fact)),
            ProofAssertion::Resource(resource) => format!(
                "{} {};",
                match resource_access(resource) {
                    ResourceAccessMode::Own => "owns",
                    ResourceAccessMode::View => "views",
                },
                format_resource_target(resource)
            ),
        };
        line(output, &prefix, &text);
    }
}

fn write_tactics(output: &mut String, tactics: &[ProofTactic], indent: usize) {
    for tactic in tactics {
        write_tactic(output, tactic, indent);
    }
}

fn write_tactic(output: &mut String, tactic: &ProofTactic, indent: usize) {
    let prefix = "    ".repeat(indent);
    match tactic {
        // A synthetic tactic was never written; it prints as what it wraps.
        ProofTactic::Synthetic(inner) => write_tactic(output, inner, indent),
        ProofTactic::Mark(name) => line(output, &prefix, &format!("mark {name};")),
        ProofTactic::Sorry => line(output, &prefix, "sorry();"),
        ProofTactic::Step
        | ProofTactic::StepContract(_)
        | ProofTactic::StepBind(_)
        | ProofTactic::StepCall(_) => {
            line(output, &prefix, &format!("{};", step_head_spelling(tactic)))
        }
        ProofTactic::StepProved { step, proof } => {
            let (head, record) = if matches!(
                step.as_ref(),
                ProofTactic::FoldResource(_) | ProofTactic::UserTactic(_)
            ) {
                let mut written = String::new();
                write_tactic(&mut written, step, 0);
                let written = written.trim_end();
                // The standalone fold's own suffix is a line comment. Put
                // the proof opener before it, so the comment cannot swallow
                // `by {` or the opening brace of `requires` entries.
                match written.rsplit_once("; // record ") {
                    Some((head, record)) => (head.to_owned(), format!(" // record {record}")),
                    None => (written.trim_end_matches(';').to_owned(), String::new()),
                }
            } else {
                (step_head_spelling(step), String::new())
            };
            match proof {
                StepProof::By(body) => {
                    line(output, &prefix, &format!("{head} by {{{record}"));
                    write_tactics(output, body, indent + 1);
                    line(output, &prefix, "}");
                }
                StepProof::Requires(entries) => {
                    line(output, &prefix, &format!("{head} {{{record}"));
                    let entry_prefix = "    ".repeat(indent + 1);
                    for entry in entries {
                        output.push_str(&entry_prefix);
                        output.push_str("requires ");
                        if let Some(label) = &entry.label {
                            output.push_str(label);
                            output.push_str(": ");
                        }
                        output.push_str(&source_click_proposition(&entry.have.proposition));
                        output.push(' ');
                        write_proof(output, &entry.have.proof, indent + 1);
                        output.push('\n');
                    }
                    line(output, &prefix, "}");
                }
            }
        }
        ProofTactic::UserTactic(application) => line(
            output,
            &prefix,
            &format!("{};", application.tactic_spelling()),
        ),
        ProofTactic::UnfoldProposition(target) => line(
            output,
            &prefix,
            &format!("unfold({});", source_click_proposition(target)),
        ),
        ProofTactic::UnfoldFunction(application) => line(
            output,
            &prefix,
            &format!(
                "unfold({});",
                format_click_function_application(application)
            ),
        ),
        ProofTactic::UnfoldResource(resource @ ResourceClause::Named { binding, .. })
            if binding.child_bindings.is_some() =>
        {
            let children = binding
                .child_bindings
                .as_ref()
                .unwrap()
                .iter()
                .map(|(slot, name, _)| format!("{slot}: {name}"))
                .collect::<Vec<_>>()
                .join(", ");
            line(
                output,
                &prefix,
                &format!(
                    "let {{ {children} }} = unfold({});",
                    format_resource_call(resource)
                ),
            );
        }
        ProofTactic::UnfoldWitnesses { resource, names } => line(
            output,
            &prefix,
            &format!(
                "let {{ {} }} = unfold({});",
                names
                    .iter()
                    .map(|(slot, name)| format!("{slot}: {name}"))
                    .collect::<Vec<_>>()
                    .join(", "),
                format_resource_target(resource)
            ),
        ),
        ProofTactic::UnfoldResource(resource) => line(
            output,
            &prefix,
            &format!(
                "unfold({});",
                if matches!(resource, ResourceClause::Named { .. }) {
                    format_resource_call(resource)
                } else {
                    format_resource_target(resource)
                }
            ),
        ),
        ProofTactic::FoldResource(ResourceClause::Named { binding, resource })
            if binding.fold_fields.is_some() =>
        {
            // Hidden record fields are reconstructed from the child map by
            // the parser. Their dotted internal names are not field labels.
            let fields = binding.fold_fields.as_ref().unwrap();
            let only_hidden =
                !fields.is_empty() && fields.iter().all(|(name, _)| name.contains('.'));
            let children = binding
                .child_bindings
                .as_ref()
                .map(|children| {
                    children
                        .iter()
                        .map(|(slot, name, _)| format!("{slot}: {name}"))
                        .collect::<Vec<_>>()
                        .join(", ")
                })
                .unwrap_or_default();
            let inputs = if only_hidden {
                format!("{{ {children} }}")
            } else {
                let visible = fields
                    .iter()
                    .filter(|(name, _)| !name.contains('.'))
                    .map(|(name, value)| format!("{name}: {}", describe_contract_expression(value)))
                    .collect::<Vec<_>>()
                    .join(", ");
                format!(
                    "{{ {visible} }}{}",
                    if children.is_empty() {
                        String::new()
                    } else {
                        format!(", {{ {children} }}")
                    }
                )
            };
            let result = if binding.name.starts_with('#') {
                String::new()
            } else {
                format!("let {} = ", binding.name)
            };
            // The hidden record this fold sets has no source syntax, so it
            // is shown as a trailing comment the parser ignores, in the
            // `record { first.v: c.v }` spelling diagnostics use.
            let record = if only_hidden {
                format!(
                    " // record {{ {} }}",
                    fields
                        .iter()
                        .map(|(name, value)| format!(
                            "{name}: {}",
                            describe_contract_expression(value)
                        ))
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            } else {
                String::new()
            };
            line(
                output,
                &prefix,
                &format!(
                    "{result}fold({}, {inputs});{record}",
                    format_resource_target(resource)
                ),
            );
        }
        ProofTactic::FoldResource(resource) => line(
            output,
            &prefix,
            &format!(
                "fold({});",
                if matches!(resource, ResourceClause::Named { .. }) {
                    format_resource_call(resource)
                } else {
                    format_resource_target(resource)
                }
            ),
        ),
        ProofTactic::ConstructResource(resource) => line(
            output,
            &prefix,
            &format!("construct({});", format_resource_target(resource)),
        ),
        ProofTactic::Induct {
            parameter,
            hypothesis,
        } => line(
            output,
            &prefix,
            &format!("induct({parameter}) as {hypothesis};"),
        ),
        ProofTactic::Match(proof_match) => {
            let scrutinee = describe_contract_expression(&proof_match.scrutinee);
            if let Some(assertions) = &proof_match.ensuring {
                line(output, &prefix, &format!("match {scrutinee} ensuring {{"));
                write_join_interface(output, assertions, indent + 1);
                line(output, &prefix, "} {");
            } else {
                line(output, &prefix, &format!("match {scrutinee} {{"));
            }
            for arm in &proof_match.arms {
                let arguments = if arm.bindings.is_empty() {
                    String::new()
                } else {
                    format!("({})", arm.bindings.join(", "))
                };
                line(
                    output,
                    &format!("{prefix}    "),
                    &format!("{}::{}{arguments} => {{", arm.type_name, arm.variant),
                );
                for tactic in &arm.tactics {
                    write_tactic(output, tactic, indent + 2);
                }
                line(output, &format!("{prefix}    "), "}");
            }
            line(output, &prefix, "}");
        }
        ProofTactic::StructuralInduct {
            parameter,
            hypothesis,
            arms,
        } => {
            line(
                output,
                &prefix,
                &format!("induct({parameter}) as {hypothesis} {{"),
            );
            for arm in arms {
                let pattern = if arm.bindings.is_empty() {
                    format!("{}::{}", arm.type_name, arm.variant)
                } else {
                    format!(
                        "{}::{}({})",
                        arm.type_name,
                        arm.variant,
                        arm.bindings.join(", ")
                    )
                };
                line(
                    output,
                    &format!("{prefix}    "),
                    &format!("{pattern} => {{"),
                );
                for tactic in &arm.tactics {
                    write_tactic(output, tactic, indent + 2);
                }
                line(output, &format!("{prefix}    "), "}");
            }
            line(output, &prefix, "}");
        }
        ProofTactic::ApplyInduction {
            hypothesis,
            arguments,
        } => line(
            output,
            &prefix,
            &format!(
                "apply({hypothesis}({}));",
                describe_induction_arguments(arguments)
            ),
        ),
        ProofTactic::ApplyInductionUsing {
            hypothesis,
            arguments,
            premises,
        } => {
            line(
                output,
                &prefix,
                &format!(
                    "apply({hypothesis}({})) using {{",
                    describe_induction_arguments(arguments)
                ),
            );
            write_premise_list(output, premises, indent + 1);
            line(output, &prefix, "};");
        }
        ProofTactic::ApplyTheorem(application) => line(
            output,
            &prefix,
            &format!("apply({});", format_theorem_application(application)),
        ),
        ProofTactic::ApplyTheoremUsing {
            application,
            premises,
        } => {
            line(
                output,
                &prefix,
                &format!(
                    "apply({}) using {{",
                    format_theorem_application(application)
                ),
            );
            write_premise_list(output, premises, indent + 1);
            line(output, &prefix, "};");
        }
        ProofTactic::Have(have) => {
            output.push_str(&prefix);
            output.push_str("have ");
            output.push_str(&source_click_proposition(&have.proposition));
            output.push(' ');
            write_proof(output, &have.proof, indent);
            output.push('\n');
        }
        ProofTactic::Open(open) => {
            line(
                output,
                &prefix,
                &format!("open({}) {{", format_resource_call(&open.resource)),
            );
            write_tactics(output, &open.tactics, indent + 1);
            match &open.close_proof {
                Some(close_proof) => {
                    line(output, &prefix, "} by {");
                    write_tactics(output, close_proof, indent + 1);
                    line(output, &prefix, "}");
                }
                None => line(output, &prefix, "}"),
            }
        }
        ProofTactic::If(proof_if) => {
            output.push_str(&prefix);
            output.push_str("if ");
            output.push_str(&source_click_proposition(&proof_if.condition));
            if let Some(assertions) = &proof_if.ensuring {
                output.push_str(" ensuring {\n");
                write_join_interface(output, assertions, indent + 1);
                line(output, &prefix, "} then {");
            } else {
                output.push_str(" {\n");
            }
            write_tactics(output, &proof_if.then_tactics, indent + 1);
            line(output, &prefix, "} else {");
            write_tactics(output, &proof_if.else_tactics, indent + 1);
            line(output, &prefix, "}");
        }
        ProofTactic::Both(both) => {
            line(output, &prefix, "both {");
            write_tactics(output, &both.left_tactics, indent + 1);
            line(output, &prefix, "} and {");
            write_tactics(output, &both.right_tactics, indent + 1);
            line(output, &prefix, "}");
        }
        ProofTactic::Cases(proof_cases) => {
            line(output, &prefix, "cases {");
            let arm_prefix = "    ".repeat(indent + 1);
            for arm in proof_cases.arms() {
                line(
                    output,
                    &arm_prefix,
                    &format!("{} => {{", source_click_proposition(arm.assumption())),
                );
                write_tactics(output, arm.tactics(), indent + 2);
                line(output, &arm_prefix, "}");
            }
            line(output, &prefix, "}");
        }
        ProofTactic::Branch(proof_branch) => {
            if let Some(assertions) = &proof_branch.ensuring {
                line(output, &prefix, "branch ensuring {");
                write_join_interface(output, assertions, indent + 1);
                line(output, &prefix, "} then {");
            } else {
                line(output, &prefix, "branch {");
            }
            write_tactics(output, &proof_branch.then_tactics, indent + 1);
            line(output, &prefix, "} else {");
            write_tactics(output, &proof_branch.else_tactics, indent + 1);
            line(output, &prefix, "}");
        }
        ProofTactic::CallOutcomes(outcomes) => {
            let arm_prefix = "    ".repeat(indent + 1);
            line(output, &prefix, "outcomes {");
            line(output, &arm_prefix, "returned => {");
            write_tactics(output, &outcomes.returned_tactics, indent + 2);
            line(output, &arm_prefix, "}");
            line(output, &arm_prefix, "threw => {");
            write_tactics(output, &outcomes.threw_tactics, indent + 2);
            line(output, &arm_prefix, "}");
            line(output, &prefix, "}");
        }
        ProofTactic::Loop(loop_clause) => {
            line(
                output,
                &prefix,
                &format!(
                    "loop{}{} {{",
                    loop_clause
                        .label()
                        .map(|label| format!(" as {label}"))
                        .unwrap_or_default(),
                    if loop_clause.diverges() {
                        " diverges"
                    } else {
                        ""
                    }
                ),
            );
            let body_prefix = "    ".repeat(indent + 1);
            if let Some(decreases) = loop_clause.decreases() {
                let components = decreases
                    .components()
                    .iter()
                    .map(describe_contract_expression)
                    .collect::<Vec<_>>();
                let rendered = if components.len() == 1 {
                    components[0].clone()
                } else {
                    format!("({})", components.join(", "))
                };
                line(output, &body_prefix, &format!("decreases {rendered};"));
            }
            for resource in loop_clause.resources() {
                if matches!(resource, ResourceClause::Conditional { .. }) {
                    line(output, &body_prefix, &format_resource_target(resource));
                    continue;
                }
                let keyword = match resource_access(resource) {
                    ResourceAccessMode::Own => "owns",
                    ResourceAccessMode::View => "views",
                };
                line(
                    output,
                    &body_prefix,
                    &format!("{keyword} {};", format_resource_target(resource)),
                );
            }
            for item in loop_clause.items() {
                output.push_str(&body_prefix);
                output.push_str("invariant");
                output.push(' ');
                output.push_str(&source_click_proposition(item.proposition()));
                output.push_str(";\n");
            }
            if let Some(proof) = loop_clause.initialize_proof() {
                output.push_str(&body_prefix);
                output.push_str("initialize ");
                write_proof(output, proof, indent + 1);
                output.push('\n');
            }
            if let Some(proof) = loop_clause.preserve_proof() {
                output.push_str(&body_prefix);
                output.push_str("preserve ");
                write_proof(output, proof, indent + 1);
                output.push('\n');
            }
            line(output, &prefix, "}");
        }
        ProofTactic::ObserveSavedMemory { base, start, end } => line(
            output,
            &prefix,
            &format!(
                "observe({}[{}..{}]);",
                describe_contract_expression(base),
                describe_contract_expression(start),
                describe_contract_expression(end)
            ),
        ),
        ProofTactic::ObserveResource(resource) => line(
            output,
            &prefix,
            &format!("observe({});", format_resource_target(resource)),
        ),
        ProofTactic::Iterated(tactic) => line(
            output,
            &prefix,
            &format!("{};", describe_iterated_tactic(tactic)),
        ),
        ProofTactic::Witness(witness) => line(
            output,
            &prefix,
            &format!(
                "witness {{ {} }};",
                witness
                    .bindings()
                    .map(|(name, value)| format!("{name}: {}", describe_contract_expression(value)))
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
        ),
        ProofTactic::Choose(choice) => line(
            output,
            &prefix,
            &format!(
                "choose({} from {});",
                choice.name,
                format_fact_source(&choice.source)
            ),
        ),
        ProofTactic::LetSatisfy(binding) => {
            let bindings = binding
                .bindings
                .iter()
                .map(|(name, click_type)| {
                    format!("{name}: {}", validation::describe_click_type(click_type))
                })
                .collect::<Vec<_>>()
                .join(", ");
            let (retained_state, mut body) = match &binding.proposition {
                ClickProposition::At {
                    selector,
                    proposition,
                } => (Some(selector), proposition.as_ref()),
                proposition => (None, proposition),
            };
            for _ in &binding.bindings {
                let ClickProposition::Exists { body: inner, .. } = body else {
                    unreachable!("let-satisfy source contains its declared binders")
                };
                body = inner;
            }
            let body = if let Some(selector) = retained_state {
                format!(
                    "at({}, {})",
                    describe_program_point_selector(selector),
                    source_click_proposition(body)
                )
            } else {
                source_click_proposition(body)
            };
            line(
                output,
                &prefix,
                &format!("obtain ({bindings}) {{ {body} }}"),
            );
        }
        ProofTactic::CheckTerminationLocal(function) => line(
            output,
            &prefix,
            &format!("check_termination_local({function:?});"),
        ),
        ProofTactic::CheckTerminationComponent { function, strict } => line(
            output,
            &prefix,
            &format!(
                "check_termination_component({function:?}, {});",
                if *strict { "strict" } else { "normal" }
            ),
        ),
        ProofTactic::CheckTerminationCallbacks => {
            line(output, &prefix, "check_termination_callbacks();")
        }
        ProofTactic::ApplyFact(fact) => line(
            output,
            &prefix,
            &format!("apply({});", source_click_proposition(fact)),
        ),
        ProofTactic::ApplyFactUsing { fact, premises } => write_using_premises(
            output,
            &format!("apply({})", source_click_proposition(fact)),
            premises,
            indent,
        ),
        ProofTactic::Known => line(output, &prefix, "known();"),
        ProofTactic::Normalize => line(output, &prefix, "normalize();"),
        ProofTactic::NormalizeUsing(premises) => {
            write_using_premises(output, "normalize()", premises, indent)
        }
        ProofTactic::ArithmeticUsing(premises) => {
            write_using_premises(output, "solve()", premises, indent)
        }
        ProofTactic::Intro => line(output, &prefix, "intro();"),
        ProofTactic::IntroAs(name) => line(output, &prefix, &format!("intro() as {name};")),
        ProofTactic::IntroBinder(name) => line(output, &prefix, &format!("intro() as {name};")),
        ProofTactic::Enumerate => line(output, &prefix, "enumerate();"),
        ProofTactic::Contradiction(fact) => line(
            output,
            &prefix,
            &format!("contradiction({});", source_click_proposition(fact)),
        ),
        ProofTactic::SolveUsing(solve) => {
            write_using_premises(output, "solve()", &solve.premises, indent)
        }

        ProofTactic::CloseInvariants => line(output, &prefix, "close_invariants();"),
        ProofTactic::CloseInvariantsBy(body) => {
            line(output, &prefix, "close_invariants() by {");
            write_tactics(output, body, indent + 1);
            line(output, &prefix, "}");
        }
        ProofTactic::Preserve(separation) => line(
            output,
            &prefix,
            &format!("preserve({});", source_preserve_arguments(separation)),
        ),
        ProofTactic::Rewrite(equality) => line(
            output,
            &prefix,
            &format!("rewrite({});", source_rewrite_arguments(equality)),
        ),
        ProofTactic::Transport { source, target } => line(
            output,
            &prefix,
            &format!(
                "transport({}, {});",
                source_click_proposition(source),
                source_click_proposition(target)
            ),
        ),
        ProofTactic::TransportUsing {
            source,
            target,
            premises,
        } => {
            line(
                output,
                &prefix,
                &format!(
                    "transport({}, {}) using {{",
                    source_click_proposition(source),
                    source_click_proposition(target)
                ),
            );
            write_premise_list(output, premises, indent + 1);
            line(output, &prefix, "};");
        }
        ProofTactic::Instantiate {
            quantified,
            argument,
        } => {
            line(
                output,
                &prefix,
                &format!(
                    "instantiate({}, {});",
                    source_click_proposition(quantified),
                    describe_contract_expression(argument)
                ),
            );
        }
        ProofTactic::SmartExecute
        | ProofTactic::ExecuteUntil(_)
        | ProofTactic::Solve
        | ProofTactic::ImplicitSolve => {
            unreachable!("certificate validation rejects this tactic")
        }
    }
}

/// The Click spelling of an integer type in certificate text.
pub(in crate::surface) fn machine_integer_type_name(
    ty: crate::kernel::MachineIntegerType,
) -> &'static str {
    use crate::kernel::MachineIntegerType as Ty;
    match ty {
        Ty::Int8 => "int8",
        Ty::UInt8 => "uint8",
        Ty::Int16 => "int16",
        Ty::UInt16 => "uint16",
        Ty::Int32 => "int32",
        Ty::UInt32 => "uint32",
        Ty::Int64 => "int64",
        Ty::UInt64 => "uint64",
        Ty::Int128 => "int128",
        Ty::UInt128 => "uint128",
    }
}

/// The spelling of a `step` or `fold` form without its terminating `;`.
fn step_head_spelling(step: &ProofTactic) -> String {
    match step {
        ProofTactic::Step => "step()".to_string(),
        ProofTactic::StepContract(name) => format!("step({name})"),
        ProofTactic::StepBind(name) => format!("let {{ result: {name} }} = step()"),
        ProofTactic::StepCall(transport) => transport.to_string(),
        // A `fold` prints as it does alone, without its `;`.
        ProofTactic::FoldResource(_) => {
            let mut written = String::new();
            write_tactic(&mut written, step, 0);
            written.trim_end().trim_end_matches(';').to_string()
        }
        _ => unreachable!("a step proof wraps a `step` or `fold` form"),
    }
}

fn write_proof(output: &mut String, proof: &SourceProof, indent: usize) {
    let SourceProof::Script(tactics) = proof else {
        unreachable!("certificate validation requires an explicit proof script")
    };
    output.push_str("by {\n");
    if tactics.is_empty() {
        // A `by` block must hold a tactic. A generated proof with no step,
        // such as the `initialize` phase of a loop with no invariant, keeps
        // `known();`, the step a phase with nothing to prove is
        // checked by.
        line(output, &"    ".repeat(indent + 1), "known();");
    }
    write_tactics(output, tactics, indent + 1);
    output.push_str(&"    ".repeat(indent));
    output.push('}');
}

fn write_using_premises(
    output: &mut String,
    name: &str,
    premises: &[ClickProposition],
    indent: usize,
) {
    let prefix = "    ".repeat(indent);
    if premises.is_empty() {
        line(output, &prefix, &format!("{name} using {{}};"));
        return;
    }
    line(output, &prefix, &format!("{name} using {{"));
    write_premise_list(output, premises, indent + 1);
    line(output, &prefix, "};");
}

fn write_premise_list(output: &mut String, facts: &[ClickProposition], indent: usize) {
    let prefix = "    ".repeat(indent);
    for fact in facts {
        wrapped_line(
            output,
            &prefix,
            &format!("{};", source_click_proposition(fact)),
        );
    }
}

pub(in crate::surface) fn format_resource_call(resource: &ResourceClause) -> String {
    if let ResourceClause::Named { binding, resource } = resource {
        return if binding.name.starts_with('#') {
            format_resource_call(resource)
        } else {
            binding.name.clone()
        };
    }
    let ResourceClause::Declared {
        name,
        arguments,
        type_schema: _,
        resource_type_arguments,
        resource_arguments,
        ..
    } = resource
    else {
        unreachable!("fold, unfold, and observe use declared resources")
    };
    format!(
        "{name}({})",
        arguments
            .iter()
            .map(describe_contract_expression)
            .chain(
                resource_arguments
                    .iter()
                    .map(|reference| reference.name.clone())
            )
            .chain(resource_type_arguments.iter().map(format_resource_call))
            .collect::<Vec<_>>()
            .join(", ")
    )
}

/// One iterated-ownership tactic as it is written: `take(data[j..j + 1])`.
pub(in crate::surface) fn describe_iterated_tactic(tactic: &IteratedTactic) -> String {
    format!(
        "{}({})",
        tactic.name(),
        match tactic {
            IteratedTactic::Take(segment) | IteratedTactic::Give(segment) => {
                match segment {
                    IteratedElement::Current(segment) => describe_contract_segment(segment),
                    IteratedElement::SavedBase { base, start, end } => format!(
                        "{}[{}..{}]",
                        describe_contract_expression(base),
                        describe_contract_expression(start),
                        describe_contract_expression(end),
                    ),
                }
            }
            IteratedTactic::Gather(resource) | IteratedTactic::Scatter(resource) => {
                format_resource_target(resource)
            }
        }
    )
}

pub(in crate::surface) fn format_resource_target(resource: &ResourceClause) -> String {
    match resource {
        ResourceClause::Conditional {
            condition,
            resource,
        } => format!(
            "if {} {{ {} {}; }}",
            source_click_proposition(condition),
            if resource_access(resource) == ResourceAccessMode::Own {
                "owns"
            } else {
                "views"
            },
            format_resource_target(resource)
        ),
        ResourceClause::Named { binding, resource } => {
            if binding.name.starts_with('#') {
                format_resource_target(resource)
            } else {
                format!("{}: {}", binding.name, format_resource_target(resource))
            }
        }
        ResourceClause::Quantified { quantity, resource } => format!(
            "{} of {}",
            describe_contract_expression(quantity),
            format_resource_target(resource)
        ),
        ResourceClause::ViewMemory(segment) | ResourceClause::OwnMemory(segment) => {
            describe_contract_segment(segment)
        }
        ResourceClause::MemoryAggregate { segments, .. } => format!(
            "aggregate {{{}}}",
            segments
                .iter()
                .map(describe_contract_segment)
                .collect::<Vec<_>>()
                .join(", ")
        ),
        ResourceClause::Declared { .. } => format_resource_call(resource),
        ResourceClause::Iterated(clause) => {
            crate::surface::lowering::describe_iterated_clause(clause)
        }
    }
}

fn resource_access(resource: &ResourceClause) -> ResourceAccessMode {
    match resource {
        ResourceClause::Conditional { resource, .. } => resource_access(resource),
        ResourceClause::Named { .. } => ResourceAccessMode::Own,
        ResourceClause::Quantified { resource, .. } => resource_access(resource),
        ResourceClause::ViewMemory(_) => ResourceAccessMode::View,
        ResourceClause::OwnMemory(_) => ResourceAccessMode::Own,
        ResourceClause::MemoryAggregate { access, .. } => *access,
        ResourceClause::Declared { access, .. } => *access,
        ResourceClause::Iterated(_) => ResourceAccessMode::Own,
    }
}

/// An induction hypothesis is applied at the theorem's parameter list, so its
/// arguments print exactly like an ordinary theorem application's.
fn describe_induction_arguments(arguments: &[ContractExpression]) -> String {
    arguments
        .iter()
        .map(describe_contract_expression)
        .collect::<Vec<_>>()
        .join(", ")
}

fn format_theorem_application(application: &TheoremApplication) -> String {
    format!(
        "{}({})",
        application.name,
        application
            .arguments
            .iter()
            .map(describe_contract_expression)
            .collect::<Vec<_>>()
            .join(", ")
    )
}

fn format_click_function_application(application: &ClickFunctionApplication) -> String {
    // Each slice is one written argument, as the call is read: the parsed
    // call holds a slice parameter's pointer and length separately. The
    // application itself stays a call, which `unfold` names.
    let arguments = crate::surface::diagnostics::slice_call_arguments(
        &application.name,
        application
            .arguments
            .iter()
            .map(describe_contract_expression)
            .collect(),
    );
    format!("{}({})", application.name, arguments.join(", "))
}

fn format_fact_source(source: &ProofFactSource) -> String {
    match source {
        ProofFactSource::Requirement(index) => format!("requirement {index}"),
        ProofFactSource::Invariant(index) => format!("invariant {index}"),
    }
}

/// Wrap certificate entries and premises without splitting tokens or literals.
fn wrapped_line(output: &mut String, prefix: &str, text: &str) {
    const WIDTH: usize = 100;
    if prefix.len() + text.len() <= WIDTH {
        line(output, prefix, text);
        return;
    }
    let mut quote = None;
    let mut escaped = false;
    let mut start = 0;
    let mut words = Vec::new();
    for (offset, ch) in text.char_indices() {
        if escaped {
            escaped = false;
        } else if let Some(delimiter) = quote {
            if ch == '\\' {
                escaped = true;
            } else if ch == delimiter {
                quote = None;
            }
        } else if ch == '\'' || ch == '"' {
            quote = Some(ch);
        } else if ch.is_whitespace() {
            if start < offset {
                words.push(&text[start..offset]);
            }
            start = offset + ch.len_utf8();
        }
    }
    if start < text.len() {
        words.push(&text[start..]);
    }
    output.push_str(prefix);
    let mut column = prefix.len();
    let mut has_word = false;
    for word in words {
        if has_word && column + 1 + word.len() > WIDTH {
            output.push('\n');
            output.push_str(prefix);
            output.push_str("    ");
            column = prefix.len() + 4;
        } else if has_word {
            output.push(' ');
            column += 1;
        }
        output.push_str(word);
        column += word.len();
        has_word = true;
    }
    output.push('\n');
}

fn line(output: &mut String, prefix: &str, text: &str) {
    output.push_str(prefix);
    output.push_str(text);
    output.push('\n');
}

/// Spell canonical references with the file's import bindings. Token spans
/// ensure a path inside a literal or comment is never rewritten.
fn spell_names(symbols: &names::SymbolTable, source: &str) -> Result<String, ClickError> {
    let tokens = parser::source_tokens(source)?;
    let mut output = String::with_capacity(source.len());
    let mut copied = 0;
    let mut index = 0;
    while index < tokens.len() {
        if tokens[index].text != "click" {
            index += 1;
            continue;
        }
        let start = index;
        let mut path = String::from("click");
        while tokens
            .get(index + 1)
            .is_some_and(|token| token.text == "::")
        {
            let Some(next) = tokens.get(index + 2) else {
                break;
            };
            if !next
                .text
                .chars()
                .all(|ch| ch.is_ascii_alphanumeric() || ch == '_')
            {
                break;
            }
            path.push_str("::");
            path.push_str(&next.text);
            index += 2;
        }
        if index > start {
            output.push_str(&source[copied..tokens[start].span.start]);
            output.push_str(&symbols.spelling(&path));
            copied = tokens[index].span.end;
        }
        index += 1;
    }
    output.push_str(&source[copied..]);
    Ok(output)
}

pub(super) fn spell_source_names(context: &str, source: &str) -> String {
    names::SymbolTable::for_source(context)
        .and_then(|symbols| spell_names(&symbols, source))
        .unwrap_or_else(|_| source.to_string())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn typed_let_source_preserves_right_associated_sums() {
        let source = "theorem grouping(a:Integer,b:Integer,c:Integer) { requires (let value:Integer=a+(b+c);value)==a+(b+c); ensures true; }";
        let parsed = parser::parse(source).unwrap();
        let Requirement::Proposition(original) = &parsed.theorem_definitions()[0].requires()[0]
        else {
            panic!("expected a requirement");
        };
        let written = source_click_proposition(original);
        let reparsed = parser::parse(&format!(
            "theorem grouping(a:Integer,b:Integer,c:Integer) {{ requires {written}; ensures true; }}"
        ))
        .unwrap();
        let Requirement::Proposition(roundtrip) = &reparsed.theorem_definitions()[0].requires()[0]
        else {
            panic!("expected a requirement");
        };
        assert_eq!(original, roundtrip, "{written}");
    }

    #[test]
    fn negative_int64_source_barrier_does_not_change_diagnostic_spelling() {
        let word = |n| {
            ContractExpression::ProgramExpression(ProgramExpression::Value(ProgramValue::Int64(
                crate::kernel::MachineTerm::int64_constant(n),
            )))
        };
        let proposition = ClickProposition::Comparison {
            left: word(-9),
            operator: ComparisonOperator::LessEqual,
            right: word(100),
        };
        assert_eq!(
            source_click_proposition(&proposition),
            "-9i64 as int64 <= 100i64"
        );
        for mode in [
            PropositionSpelling::Authored,
            PropositionSpelling::Diagnostic,
            PropositionSpelling::Refusal,
        ] {
            assert_eq!(print_proposition(&proposition, mode), "-9i64 <= 100i64");
        }
    }

    #[test]
    fn population_count_comparisons_preserve_their_numeric_type_when_reparsed() {
        fn requirement(source: &str) -> ClickProposition {
            let parsed = parser::parse(source).unwrap();
            let Requirement::Proposition(proposition) = &parsed.function_blocks()[0].requires()[0]
            else {
                panic!("expected a comparison requirement");
            };
            proposition.clone()
        }
        for count in [
            "count(token())",
            "old(count(token()))",
            "at(function.entry, count(token()))",
        ] {
            let original = requirement(&format!(
                "authorized resource token() {{}} void f(int32 value) {{ requires value == {count}; ensures value == value; }}"
            ));
            let rendered = source_click_proposition(&original);
            let reparsed = requirement(&format!(
                "authorized resource token() {{}} void f(int32 value) {{ requires {rendered}; ensures value == value; }}"
            ));
            let (
                ClickProposition::Comparison { left: original, .. },
                ClickProposition::Comparison { left: reparsed, .. },
            ) = (original, reparsed)
            else {
                panic!("expected comparisons before and after printing");
            };
            assert_eq!(original, reparsed, "{rendered}");
        }
    }

    // A word's `+` or `-` compared with a typed word prints with its type
    // barrier, so it reparses as the word operation: bare, `n - 1u64 != 0u64`
    // reparses as the Integer comparison `to_integer(n) - 1 != 0`. The store
    // search spells its `size_t` index fact this way
    // (`mdtests/a_size_t_store_search_miss_names_the_word_fact.md`).
    #[test]
    fn word_arithmetic_compared_with_a_typed_word_reparses_as_the_word() {
        fn requirement(source: &str) -> ClickProposition {
            let parsed = parser::parse(source).unwrap();
            let Requirement::Proposition(proposition) = &parsed.function_blocks()[0].requires()[0]
            else {
                panic!("expected a comparison requirement");
            };
            proposition.clone()
        }
        let word = |value: u64| {
            ContractExpression::ProgramExpression(ProgramExpression::Value(ProgramValue::UInt64(
                crate::kernel::MachineTerm::uint64_constant(value),
            )))
        };
        let n = || ContractExpression::ProgramExpression(ProgramExpression::Variable("n".into()));
        for (arithmetic, spelled, bare) in [
            (
                ContractExpression::Subtract(Box::new(n()), Box::new(word(1))),
                "(n - 1u64) as uint64 != 0u64",
                "n - 1u64 != 0u64",
            ),
            (
                ContractExpression::Add(Box::new(n()), Box::new(n())),
                "(n + n) as uint64 != 0u64",
                "n + n != 0u64",
            ),
        ] {
            let synthesized = ClickProposition::Comparison {
                left: arithmetic,
                operator: ComparisonOperator::NotEqual,
                right: word(0),
            };
            let rendered = source_click_proposition(&synthesized);
            assert_eq!(rendered, spelled);
            let context =
                |text: &str| format!("void f(uint64 n) {{ requires {text}; ensures n == n; }}");
            let reparsed = requirement(&context(&rendered));
            let bare = requirement(&context(bare));
            assert!(
                !format!("{reparsed:?}").contains("to_integer"),
                "{rendered} reparsed as an Integer comparison: {reparsed:?}"
            );
            assert!(
                format!("{bare:?}").contains("to_integer"),
                "the bare spelling no longer reads as an Integer comparison: {bare:?}"
            );
            // The reparsed cast is the parser's own `as` form; it prints
            // and reparses to itself.
            let again = requirement(&context(&source_click_proposition(&reparsed)));
            assert_eq!(again, reparsed, "{rendered}");
        }
    }

    #[test]
    fn wrapping_keeps_quoted_literals_and_long_tokens_intact() {
        let literal = r#""spaces, \"quoted\" text and é stay together""#;
        let text = format!("{} == {literal} and ' ' == ' ';", "expression ".repeat(12));
        let mut output = String::new();
        wrapped_line(&mut output, "    ", &text);
        assert!(output.lines().count() > 1);
        assert!(output.contains(literal));
        assert!(output.contains("' ' == ' ';"));
        assert!(output.lines().all(|line| line.len() <= 100));
        let long_name = "identifier".repeat(20);
        output.clear();
        wrapped_line(&mut output, "", &format!("{long_name} == 0;"));
        assert!(output.contains(&long_name));
    }

    #[test]
    fn a_read_through_a_checked_object_address_spells_the_original_place() {
        let address = ProgramExpression::CheckedObjectAddress(Box::new(
            ProgramExpression::Variable("value".into()),
        ));
        let zero = ProgramExpression::Value(ProgramValue::Int32(MachineTerm::constant(0)));
        // Call substitution retains a Surface index; lowered C expressions
        // can also carry the read. Both must print the original lvalue.
        for read in [
            ContractExpression::Index(
                Box::new(ContractExpression::ProgramExpression(address.clone())),
                Box::new(ContractExpression::ProgramExpression(zero.clone())),
            ),
            ContractExpression::ProgramExpression(ProgramExpression::Index(
                Box::new(address),
                Box::new(zero),
            )),
        ] {
            let proposition = ClickProposition::Comparison {
                left: read,
                operator: ComparisonOperator::LessEqual,
                right: ContractExpression::ProgramExpression(ProgramExpression::Value(
                    ProgramValue::Int32(MachineTerm::constant(10)),
                )),
            };
            let source = source_click_proposition(&proposition);
            assert_eq!(source, "value <= 10");
            let parsed = parser::parse(&format!(
                "void f(int32 value) {{ requires {source}; ensures true; }}"
            ))
            .unwrap();
            let Requirement::Proposition(proposition) = &parsed.function_blocks()[0].requires()[0]
            else {
                panic!("expected the read comparison requirement");
            };
            assert_eq!(source_click_proposition(proposition), source);
        }
    }

    #[test]
    fn array_field_read_through_an_erased_pointer_keeps_its_element_type() {
        let read = ContractExpression::Index(
            Box::new(ContractExpression::Field {
                pointee_struct: None,
                base: Box::new(ContractExpression::ProgramExpression(
                    ProgramExpression::Variable("p".into()),
                )),
                field: "items".into(),
                lowered: ProgramExpression::TypedLoad {
                    pointer: Box::new(ProgramExpression::PointerOffsetBytes {
                        pointer: Box::new(ProgramExpression::Variable("p".into())),
                        bytes: 4,
                    }),
                    value_type: ProgramType::UInt32Array(3),
                    volatile: false,
                    pointee_constant: false,
                    access_class: None,
                    source: Default::default(),
                },
                offset_bytes: 4,
            }),
            Box::new(ContractExpression::ProgramExpression(
                ProgramExpression::Variable("index".into()),
            )),
        );
        let goal = ClickProposition::Comparison {
            left: ContractExpression::ProgramExpression(ProgramExpression::Variable(
                "result".into(),
            )),
            operator: ComparisonOperator::Equal,
            right: read,
        };
        let printed = source_click_proposition(&goal);
        let sidecar = format!(
            r#"
            verifying "read.c";
            uint32 read(uint32* p, int32 index) {{
                requires 0 <= index;
                requires index < 3;
                requires index == 1;
                views p[0..4];
                ensures {printed};
            }} by {{ step_until(function.exit); rewrite(index, 1); solve(); }}
        "#
        );
        let sources = [(
            "read.c",
            "uint32 read(uint32* p, int32 index) { return p[index + 1]; }",
        )];
        verify_c_sources(&sidecar, &sources)
            .expect("the printed read must preserve its offset, width and unsigned type");
        let false_claim = sidecar.replace("ensures result ==", "ensures result + 1u32 ==");
        assert!(verify_c_sources(&false_claim, &sources).is_err());
        assert!(verify_c_sources(&sidecar.replace("views p[0..4];", ""), &sources).is_err());
    }

    #[test]
    fn marked_conjunction_uses_parseable_click_connectives() {
        let equality = |name: &str| ClickProposition::Comparison {
            left: ContractExpression::ProgramExpression(ProgramExpression::Variable(
                (name.to_string()).into(),
            )),
            operator: ComparisonOperator::Equal,
            right: ContractExpression::ProgramExpression(ProgramExpression::Variable(
                (name.to_string()).into(),
            )),
        };
        let proposition = ClickProposition::At {
            selector: ProgramPointSelector::Mark("checkpoint".to_string()),
            proposition: Box::new(ClickProposition::And(
                Box::new(equality("left")),
                Box::new(equality("right")),
            )),
        };

        assert_eq!(
            source_click_proposition(&proposition),
            "at(checkpoint, left == left and right == right)"
        );
    }
}
