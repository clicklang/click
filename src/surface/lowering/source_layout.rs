use super::*;
use crate::surface::syntax::flatten_direct_c_statements;

type Site = std::sync::Arc<syntax::CStatementSite>;

pub(in crate::surface) fn count_loops(statement: &syntax::CStatement) -> usize {
    match statement {
        syntax::CStatement::Seq(first, second) => count_loops(first) + count_loops(second),
        syntax::CStatement::If {
            then_branch,
            else_branch,
            ..
        } => count_loops(then_branch) + count_loops(else_branch),
        syntax::CStatement::While { test, body, .. }
        | syntax::CStatement::DoWhile { test, body, .. } => {
            1 + count_loops(body) + test.as_ref().map_or(0, |test| count_loops(test))
        }
        syntax::CStatement::For {
            test,
            initializer,
            step,
            body,
            ..
        } => {
            count_loops(initializer)
                + 1
                + count_loops(body)
                + count_loops(step)
                + test.as_ref().map_or(0, |test| count_loops(test))
        }
        syntax::CStatement::Switch { cases, .. } => {
            cases.iter().map(|case| count_loops(case.body())).sum()
        }
        _ => 0,
    }
}

pub(in crate::surface) fn count_loop_regions(
    function: &crate::languages::interface::ImportedFunction,
) -> usize {
    let Some(kernel) = function.prelowered_kernel_function() else {
        return count_loops(function.body())
            + usize::from(function.natural_control_loop().is_some());
    };
    let mut pending = vec![kernel.body()];
    let mut count = 0;
    while let Some(statement) = pending.pop() {
        match statement {
            ProgramStatement::Seq(statements) => {
                pending.extend(statements.iter().map(|statement| statement.as_ref()))
            }
            ProgramStatement::If {
                then_branch,
                else_branch,
                ..
            } => pending.extend([then_branch.as_ref(), else_branch.as_ref()]),
            ProgramStatement::TryCatchInt32 {
                try_body, handler, ..
            } => pending.extend([try_body.as_ref(), handler.as_ref()]),
            ProgramStatement::UnwindCleanup { body, cleanup } => {
                pending.extend([body.as_ref(), cleanup.as_ref()])
            }
            ProgramStatement::Loop {
                test: loop_test,
                update,
                body,
                ..
            } => {
                let test = loop_test.source_region();
                count += 1;
                pending.push(body);
                if let Some(test) = test {
                    pending.push(&test.statement);
                }
                if let Some(update) = update {
                    pending.push(update);
                }
            }
            _ => {}
        }
    }
    count + usize::from(function.natural_control_loop().is_some())
}

#[derive(Clone, Default)]
pub(in crate::surface) struct SourceExecutionLayout {
    data: std::sync::Arc<SourceExecutionLayoutData>,
}

#[derive(Default)]
struct SourceExecutionLayoutData {
    /// Source parameter names, indexed once for proof output freshness checks.
    parameter_names: BTreeSet<String>,
    statements: BTreeMap<usize, SourceStatementRegion>,
    /// Static stores to named locals, indexed once in executable preorder.
    assignments: BTreeMap<String, Vec<usize>>,
    reads: Vec<usize>,
    automatic_exits: BTreeMap<usize, Vec<crate::kernel::BindingName>>,
    automatic_abrupt_exits: BTreeMap<usize, Vec<crate::kernel::BindingName>>,
    automatic_continue_exits: BTreeMap<usize, Vec<crate::kernel::BindingName>>,
    automatic_break_heads: BTreeMap<usize, usize>,
    loop_bodies: BTreeMap<usize, usize>,
    loop_updates: BTreeMap<usize, usize>,
    /// Pure decisions receive semantic regions after all written operations,
    /// preserving every existing statement number and their own footprints.
    loop_test_phases: BTreeMap<usize, (crate::kernel::LoopTestPosition, usize, usize)>,
    hidden_loop_tests: BTreeMap<usize, usize>,
    natural_loop_targets: BTreeMap<usize, crate::kernel::ControlTargetId>,
    natural_exit_targets: BTreeMap<usize, crate::kernel::ControlTargetId>,
    natural_exit_statement_indices: BTreeMap<usize, usize>,
    /// The C `if` statement indices whose regions complete when the keyed
    /// statement completes normally: the chain of enclosing branches this
    /// statement ends. Statically derived, so branch-region exits need no
    /// runtime continuation bookkeeping.
    exited_branch_regions: BTreeMap<usize, Vec<usize>>,
    /// The inverse of `exited_branch_regions`, kept while the layout is
    /// built: for each `if`, the statements whose completion completes its
    /// region. Redirecting an arm that ends in an `if` needs exactly these,
    /// and finding them by scanning every statement's list made the build
    /// quadratic in the statements of a nested branch tree.
    arm_lasts_by_exited_region: BTreeMap<usize, Vec<usize>>,
    /// Where each C statement was written, by statement index: diagnostics
    /// only, read by a refusal to name the line it refused. Statements a
    /// frontend generated with no source statement of their own are absent.
    sites: BTreeMap<usize, std::sync::Arc<syntax::CStatementSite>>,
    /// The regions of each statement as written, by its source path (see
    /// [`syntax::CStatementSite::source_path`]), in executable preorder:
    /// the statement's own regions, not its children's.
    source_statements: BTreeMap<Vec<u32>, Vec<usize>>,
    /// The function each direct-call region calls, for `.call(f, j)`.
    call_targets: BTreeMap<usize, String>,
    /// The object each call region receives as each by-value aggregate
    /// parameter, by the region and the parameter's name:
    /// `R.parameter(name)` names it.
    call_parameter_objects: BTreeMap<(usize, String), crate::kernel::BindingName>,
    /// The call region and parameter each prepared argument object is.
    prepared_parameters: BTreeMap<crate::kernel::BindingName, (usize, String)>,
    /// The layout each prepared argument object is declared with.
    prepared_layouts: BTreeMap<crate::kernel::BindingName, crate::kernel::AggregateLayout>,
    /// Every call region, including calls through a function pointer, which
    /// name no function and so have no entry in `call_targets`.
    calls: BTreeSet<usize>,
    /// The regions that are a loop's own test, `loop(i).test()`.
    loop_tests: BTreeSet<usize>,
    /// The number of each region that is a call inside an expression: its
    /// result is the state's call result of that number while its statement
    /// runs.
    call_numbers: BTreeMap<usize, u32>,
    snapshot_step_results: bool,
    aggregate_results:
        BTreeMap<usize, std::sync::Arc<BTreeMap<String, crate::kernel::AggregateField>>>,
    /// The fields of the record each pointer-valued result points at, by
    /// the region that makes the pointer.
    pointee_results:
        BTreeMap<usize, std::sync::Arc<BTreeMap<String, crate::kernel::AggregateField>>>,
    full_expression_ends: BTreeSet<usize>,
    /// The region of each step whose result its statement reads, by the
    /// step's number: a call step, or an assignment step keeping its
    /// target's prior value.
    step_regions: BTreeMap<u32, usize>,
    /// The local whose prior value each such assignment step keeps.
    prior_steps: BTreeMap<u32, crate::kernel::BindingName>,
    /// The operator each operator `if` region decides.
    operator_regions: BTreeMap<usize, crate::kernel::OperatorKind>,
    /// The local each call region assigns its result to, for
    /// `<region>.result`, and the call region of each frontend result
    /// temporary, which no other name spells.
    call_results: BTreeMap<usize, crate::kernel::BindingName>,
    /// The producing call step of a frontend temporary assigned its result.
    call_captures: BTreeMap<crate::kernel::BindingName, u32>,
    /// Source call ordinals in prelowered bodies, in executable region order.
    named_calls: Option<NamedCalls>,
    allocation_regions: BTreeSet<usize>,
    /// The source path of the statement each region belongs to: the inverse
    /// of `source_statements`, for spelling a region by its statement.
    region_paths: BTreeMap<usize, Vec<u32>>,
    /// The source path of each loop's statement as written.
    loop_paths: BTreeMap<usize, Vec<u32>>,
    /// The places a refusal names reads by, built once for the function on
    /// the first step that enters a statement scope.
    diagnostic_places:
        std::sync::OnceLock<std::sync::Arc<crate::surface::diagnostics::StatementPlaces>>,
    /// The pointee type of each local pointer and array, indexed once for
    /// every loop's re-annotation of the function rather than once per loop.
    local_pointer_element_types: std::sync::OnceLock<BTreeMap<String, crate::kernel::ProgramType>>,
    /// The function's loop regions, counted once for every loop's clause
    /// validation rather than once per loop.
    loop_region_count: std::sync::OnceLock<usize>,
}

#[derive(Debug, Default)]
struct NamedCalls {
    in_function: BTreeMap<String, Vec<usize>>,
    in_statement: BTreeMap<Vec<u32>, BTreeMap<String, Vec<usize>>>,
}

impl NamedCalls {
    fn regions(&self, path: Option<&[u32]>, callee: &str) -> &[usize] {
        crate::instrumentation::record_deterministic_work(1);
        let calls = match path {
            Some(path) => self.in_statement.get(path),
            None => Some(&self.in_function),
        };
        calls
            .and_then(|calls| calls.get(callee))
            .map_or(&[], Vec::as_slice)
    }
}

#[derive(Clone, Copy)]
pub(in crate::surface) struct SourceStatementRegion {
    pub(in crate::surface) continuation_node: usize,
    pub(in crate::surface) kind: SourceStatementKind,
}

#[derive(Clone, Copy)]
pub(in crate::surface) enum SourceStatementKind {
    Plain,
    If {
        then_statement_index: usize,
        else_statement_index: usize,
    },
    Loop {
        loop_index: usize,
    },
    /// A `try` whose body and handler the stepper descends into, so an
    /// implicit cleanup call inside either one is its own steppable
    /// statement. Only the typed C++ frontend produces `TryCatchInt32`,
    /// so C layouts never contain this kind. `after_try` is the index of
    /// the first statement after the `try`, used to resume normal control
    /// flow when the body (or handler) completes.
    Try {
        try_statement_index: usize,
        handler_statement_index: usize,
        after_try_statement_index: usize,
        try_last_statement_index: usize,
        handler_last_statement_index: usize,
    },
}

// Inspect only expressions owned by this statement, never descendant bodies.
// OldAddress-of computes an lvalue address without reading its designated cell;
// nested loads in the pointer/index expressions still count.
fn expression_reads(expression: &ProgramExpression) -> bool {
    let mut pending = vec![(expression, true)];
    while let Some((expression, value)) = pending.pop() {
        crate::instrumentation::record_deterministic_work(1);
        match expression {
            ProgramExpression::Load(_)
            | ProgramExpression::TypedLoad { .. }
            | ProgramExpression::Index(..)
                if value =>
            {
                return true;
            }
            ProgramExpression::Load(pointer) | ProgramExpression::TypedLoad { pointer, .. } => {
                pending.push((pointer, true))
            }
            ProgramExpression::AddressOf(place)
            | ProgramExpression::CheckedObjectAddress(place) => pending.push((place, false)),
            ProgramExpression::Cast { expression, .. }
            | ProgramExpression::Negate(expression)
            | ProgramExpression::FloatNegate(expression)
            | ProgramExpression::FloatClassification { expression, .. }
            | ProgramExpression::EnumField {
                value: expression, ..
            }
            | ProgramExpression::EnumIs {
                value: expression, ..
            }
            | ProgramExpression::Not(expression)
            | ProgramExpression::BitwiseNot(expression) => pending.push((expression, true)),
            ProgramExpression::EnumConstruct { fields, .. } => {
                pending.extend(fields.iter().map(|field| (field, true)))
            }
            ProgramExpression::PointerOffsetBytes { pointer, .. }
            | ProgramExpression::Subobject { pointer, .. } => pending.push((pointer, true)),
            ProgramExpression::Ternary {
                condition,
                then_branch,
                else_branch,
            } => pending.extend([
                (condition.as_ref(), true),
                (then_branch.as_ref(), true),
                (else_branch.as_ref(), true),
            ]),
            crate::kernel::binary_c_expression!(a, b) => {
                pending.extend([(a.as_ref(), true), (b.as_ref(), true)])
            }
            ProgramExpression::StringLiteral(_)
            | ProgramExpression::Value(_)
            | ProgramExpression::Variable(_)
            | ProgramExpression::FunctionAddress(_)
            | ProgramExpression::StepResult { .. } => {}
        }
    }
    false
}

fn kernel_statement_reads(statement: &ProgramStatement) -> bool {
    match statement {
        ProgramStatement::Assign { expression, .. }
        | ProgramStatement::StepValue { expression, .. }
        | ProgramStatement::Return(expression)
        | ProgramStatement::Throw(expression)
        | ProgramStatement::Assert {
            condition: expression,
            ..
        }
        | ProgramStatement::If {
            condition: expression,
            ..
        }
        | ProgramStatement::Switch { expression, .. }
        | ProgramStatement::HeapAllocate {
            bytes: expression, ..
        }
        | ProgramStatement::HeapFree {
            pointer: expression,
        } => expression_reads(expression),
        ProgramStatement::Loop { test, .. } => {
            test.source_condition().is_some_and(expression_reads)
        }
        ProgramStatement::Call { arguments, .. }
        | ProgramStatement::CallConstruct { arguments, .. }
        | ProgramStatement::CallResult { arguments, .. } => arguments.iter().any(expression_reads),
        ProgramStatement::Store { pointer, value }
        | ProgramStatement::TypedStore { pointer, value, .. } => {
            expression_reads(pointer) || expression_reads(value)
        }
        ProgramStatement::Update {
            target, operand, ..
        } => expression_reads(target) || expression_reads(operand),
        _ => false,
    }
}

fn syntax_statement_reads(statement: &syntax::CStatement) -> bool {
    use syntax::CStatement as S;
    let read =
        |expression: &syntax::CExpression| expression_reads(&expression.to_kernel_expression());
    match statement {
        S::Declare { zero_fill, .. } => zero_fill
            .iter()
            .any(|fill| fill.written_elements.iter().any(|(_, value)| read(value))),
        S::Assign { expression, .. }
        | S::Return(expression, _)
        | S::Assert {
            condition: expression,
            ..
        }
        | S::If {
            condition: expression,
            ..
        }
        | S::While {
            condition: expression,
            ..
        }
        | S::DoWhile {
            condition: expression,
            ..
        }
        | S::For {
            condition: expression,
            ..
        }
        | S::Switch { expression, .. }
        | S::HeapAllocate {
            bytes: expression, ..
        }
        | S::HeapFree {
            pointer: expression,
            ..
        } => read(expression),
        S::Call { arguments, .. } | S::CallResult { arguments, .. } => arguments.iter().any(read),
        S::Store { pointer, value, .. }
        | S::SequentialStore {
            target: pointer,
            value,
            ..
        } => read(pointer) || read(value),
        S::Update {
            target, operand, ..
        } => read(target) || read(operand),
        _ => false,
    }
}

fn record_assignment(
    layout: &mut SourceExecutionLayoutData,
    binding: &crate::kernel::BindingName,
    index: usize,
) {
    let Some(local) = binding.source_spelling() else {
        return;
    };
    crate::instrumentation::record_deterministic_work(1);
    layout
        .assignments
        .entry(local.to_owned())
        .or_default()
        .push(index);
}

type AggregateResultFields = std::sync::Arc<BTreeMap<String, crate::kernel::AggregateField>>;

/// Records the prepared argument objects among a call's arguments, each the
/// object region `index` receives as the parameter it is named for.
fn record_prepared_arguments<'a>(
    layout: &mut SourceExecutionLayoutData,
    index: usize,
    arguments: impl IntoIterator<Item = &'a crate::kernel::BindingName>,
) {
    for argument in arguments {
        let Some(parameter) = argument
            .local_id()
            .and_then(crate::kernel::LocalBindingId::call_parameter)
        else {
            continue;
        };
        layout
            .call_parameter_objects
            .insert((index, parameter.to_owned()), argument.clone());
        layout
            .prepared_parameters
            .insert(argument.clone(), (index, parameter.to_owned()));
    }
}

/// The binding a kernel call argument passes as an object, through casts.
fn kernel_argument_binding(argument: &ProgramExpression) -> Option<&crate::kernel::BindingName> {
    match argument {
        ProgramExpression::Variable(name) => Some(name),
        ProgramExpression::Cast { expression, .. } => kernel_argument_binding(expression),
        _ => None,
    }
}

fn aggregate_result_fields(layout: &crate::kernel::AggregateLayout) -> AggregateResultFields {
    std::sync::Arc::new(
        layout
            .fields()
            .iter()
            .map(|field| {
                crate::instrumentation::record_deterministic_work(1);
                (field.name().to_string(), field.clone())
            })
            .collect(),
    )
}

/// Allocate semantic decisions only after written source numbering and lexical
/// exits are complete. Each read is keyed by the selected loop/header.
fn finish_loop_phase_regions(data: &mut SourceExecutionLayoutData) {
    if data.loop_test_phases.is_empty() {
        return;
    }
    // Index the original written-source successors once. Each redirected
    // edge is removed, so nested post-tests never revisit inner edges.
    let mut successors: BTreeMap<usize, BTreeSet<usize>> = BTreeMap::new();
    let mut next = 0;
    for (index, region) in &data.statements {
        crate::instrumentation::record_deterministic_work(1);
        next = next.max(index + 1).max(region.continuation_node + 1);
        successors
            .entry(region.continuation_node)
            .or_default()
            .insert(*index);
    }
    let mut post_tests = Vec::new();
    for (loop_index, (position, region, written_end)) in &mut data.loop_test_phases {
        let body = data.loop_bodies[loop_index];
        let header = body - 1;
        let after = *written_end;
        assert_ne!(
            after,
            usize::MAX,
            "loop written extent must be completed before phase routing"
        );
        *region = next;
        if *position == crate::kernel::LoopTestPosition::AfterBody {
            post_tests.push((body, after, *region));
        }
        next += 1;
        data.statements.insert(
            *region,
            SourceStatementRegion {
                kind: SourceStatementKind::Plain,
                continuation_node: if *position == crate::kernel::LoopTestPosition::BeforeBody {
                    body
                } else {
                    header
                },
            },
        );
        data.hidden_loop_tests.insert(*region, *loop_index);
        data.loop_tests.insert(*region);
        data.full_expression_ends.insert(*region);
        if let Some(exits) = data.automatic_exits.get(&header) {
            data.automatic_abrupt_exits.insert(*region, exits.clone());
        }
        if let Some(site) = data.sites.get(&header) {
            data.sites.insert(*region, site.clone());
        }
        if let Some(path) = data.loop_paths.get(loop_index) {
            data.region_paths.insert(*region, path.clone());
            data.source_statements
                .entry(path.clone())
                .or_default()
                .push(*region);
        }
        if data.reads.binary_search(&header).is_ok() {
            data.reads.push(*region);
        }
    }
    for (body, after, test) in post_tests.into_iter().rev() {
        let Some(edges) = successors.get_mut(&after) else {
            continue;
        };
        let selected = edges.range(body..after).copied().collect::<Vec<_>>();
        for source in selected {
            crate::instrumentation::record_deterministic_work(1);
            edges.remove(&source);
            data.statements
                .get_mut(&source)
                .expect("indexed source edge")
                .continuation_node = test;
        }
    }
}

impl SourceExecutionLayout {
    pub(in crate::surface) fn is_hidden_loop_test(&self, region: usize) -> bool {
        self.data.hidden_loop_tests.contains_key(&region)
    }

    pub(in crate::surface) fn loop_test_phase_entry(&self, index: usize) -> Option<usize> {
        self.data
            .loop_test_phases
            .get(&index)
            .map(|(_, region, _)| *region)
    }

    pub(in crate::surface) fn loop_index_at_header(&self, region: usize) -> Option<usize> {
        match self.data.statements.get(&region)?.kind {
            SourceStatementKind::Loop { loop_index } => Some(loop_index),
            _ => None,
        }
    }

    pub(in crate::surface) fn loop_continuation_entry(&self, index: usize) -> Option<usize> {
        self.loop_update_entry(index)
            .or_else(|| self.loop_test_phase_entry(index))
    }

    pub(in crate::surface) fn loop_update_entry(&self, index: usize) -> Option<usize> {
        self.data.loop_updates.get(&index).copied()
    }

    pub(in crate::surface) fn for_function(
        function: &crate::languages::interface::ImportedFunction,
    ) -> Result<Self, ClickError> {
        let parameter_names = function
            .parameters()
            .iter()
            .map(|p| p.name().to_string())
            .collect();
        let imported = function;
        let Some(function) = function.prelowered_kernel_function() else {
            return Ok(Self::new_for_function(function));
        };
        let mut layout = SourceExecutionLayoutData {
            parameter_names,
            ..Default::default()
        };
        let mut next_statement_index = 0;

        fn redirect_control_successor(
            layout: &mut SourceExecutionLayoutData,
            last_statement_index: usize,
            exited_if_index: usize,
            continuation_node: usize,
        ) {
            // A statement already redirected for this `if` was redirected,
            // with everything it ends, by an earlier visit: an arm can be
            // reached again through each nested `if` it closes, and
            // revisiting it doubled the walk at every level of nesting.
            if layout
                .exited_branch_regions
                .get(&last_statement_index)
                .is_some_and(|exited| exited.contains(&exited_if_index))
            {
                return;
            }
            let Some(region) = layout.statements.get_mut(&last_statement_index) else {
                return;
            };
            region.continuation_node = continuation_node;
            let try_lasts = if let SourceStatementKind::Try {
                after_try_statement_index,
                try_last_statement_index,
                handler_last_statement_index,
                ..
            } = &mut region.kind
            {
                *after_try_statement_index = continuation_node;
                Some([*try_last_statement_index, *handler_last_statement_index])
            } else {
                None
            };
            layout
                .exited_branch_regions
                .entry(last_statement_index)
                .or_default()
                .push(exited_if_index);
            layout
                .arm_lasts_by_exited_region
                .entry(exited_if_index)
                .or_default()
                .push(last_statement_index);
            if let Some(lasts) = try_lasts {
                for last in lasts {
                    redirect_control_successor(layout, last, exited_if_index, continuation_node);
                }
            } else if let SourceStatementKind::If { .. } = region.kind {
                // In statement order, each statement once: what the scan of
                // every statement's list returned.
                let mut arm_lasts: Vec<usize> = layout
                    .arm_lasts_by_exited_region
                    .get(&last_statement_index)
                    .cloned()
                    .unwrap_or_default();
                arm_lasts.sort_unstable();
                arm_lasts.dedup();
                for arm_last in arm_lasts {
                    redirect_control_successor(
                        layout,
                        arm_last,
                        exited_if_index,
                        continuation_node,
                    );
                }
            }
        }

        fn last_non_skip(statement: &ProgramStatement) -> Option<&ProgramStatement> {
            match statement {
                ProgramStatement::Skip => None,
                ProgramStatement::Seq(statements) => statements
                    .iter()
                    .rev()
                    .find_map(|statement| last_non_skip(statement.as_ref())),
                statement => Some(statement),
            }
        }

        // A frontend can lower a conditional value to two arms that publish
        // the same result. That result belongs to the join, not either arm.
        fn terminal_value_steps(statement: &ProgramStatement) -> Option<&[u32]> {
            match last_non_skip(statement)? {
                ProgramStatement::StepValue { steps, .. } => Some(steps),
                _ => None,
            }
        }

        fn visit(
            statement: &ProgramStatement,
            next_statement_index: &mut usize,
            layout: &mut SourceExecutionLayoutData,
            aggregate_objects: &mut BTreeMap<crate::kernel::BindingName, AggregateResultFields>,
        ) -> Result<usize, ClickError> {
            if kernel_statement_reads(statement) {
                layout.reads.push(*next_statement_index);
            }
            match statement {
                ProgramStatement::Seq(statements) => {
                    let last = statements.len() - 1;
                    for statement in statements.iter().take(last) {
                        visit(statement, next_statement_index, layout, aggregate_objects)?;
                    }
                    visit(
                        statements.get(last).expect("a last statement"),
                        next_statement_index,
                        layout,
                        aggregate_objects,
                    )
                }
                ProgramStatement::If {
                    then_branch,
                    else_branch,
                    ..
                } => {
                    let statement_index = *next_statement_index;
                    *next_statement_index += 1;
                    if let (Some(yes), Some(no)) = (
                        terminal_value_steps(then_branch),
                        terminal_value_steps(else_branch),
                    ) && yes == no
                    {
                        for step in yes {
                            layout.step_regions.insert(*step, statement_index);
                            layout.call_numbers.entry(statement_index).or_insert(*step);
                        }
                    }
                    let then_statement_index = *next_statement_index;
                    let then_last =
                        visit(then_branch, next_statement_index, layout, aggregate_objects)?;
                    let else_statement_index = *next_statement_index;
                    let else_last =
                        visit(else_branch, next_statement_index, layout, aggregate_objects)?;
                    let continuation_node = *next_statement_index;
                    layout.statements.insert(
                        statement_index,
                        SourceStatementRegion {
                            continuation_node,
                            kind: SourceStatementKind::If {
                                then_statement_index,
                                else_statement_index,
                            },
                        },
                    );
                    redirect_control_successor(
                        layout,
                        then_last,
                        statement_index,
                        continuation_node,
                    );
                    redirect_control_successor(
                        layout,
                        else_last,
                        statement_index,
                        continuation_node,
                    );
                    Ok(statement_index)
                }
                ProgramStatement::Loop {
                    test: loop_test,
                    update,
                    body,
                    ..
                } => {
                    let test = loop_test.source_region();
                    let statement_index = *next_statement_index;
                    *next_statement_index += 1;
                    let loop_index = layout.loop_bodies.len();
                    layout.loop_bodies.insert(loop_index, *next_statement_index);
                    if loop_test.source_condition().is_some() {
                        layout
                            .loop_test_phases
                            .insert(loop_index, (loop_test.position, usize::MAX, usize::MAX));
                    }
                    if let Some(test) = test
                        .as_ref()
                        .filter(|test| test.position == crate::kernel::LoopTestPosition::BeforeBody)
                    {
                        visit(
                            &test.statement,
                            next_statement_index,
                            layout,
                            aggregate_objects,
                        )?;
                    }
                    visit(body, next_statement_index, layout, aggregate_objects)?;
                    if let Some(update) = update {
                        layout
                            .loop_updates
                            .insert(loop_index, *next_statement_index);
                        visit(update, next_statement_index, layout, aggregate_objects)?;
                    }
                    if let Some(test) = test
                        .as_ref()
                        .filter(|test| test.position == crate::kernel::LoopTestPosition::AfterBody)
                    {
                        layout
                            .loop_updates
                            .entry(loop_index)
                            .or_insert(*next_statement_index);
                        visit(
                            &test.statement,
                            next_statement_index,
                            layout,
                            aggregate_objects,
                        )?;
                    }
                    if let Some((_, _, end)) = layout.loop_test_phases.get_mut(&loop_index) {
                        *end = *next_statement_index;
                    }
                    layout.statements.insert(
                        statement_index,
                        SourceStatementRegion {
                            continuation_node: *next_statement_index,
                            kind: SourceStatementKind::Loop { loop_index },
                        },
                    );
                    Ok(statement_index)
                }
                ProgramStatement::Switch { .. } => Err(ClickError::new(
                    "typed-frontend source layout does not yet support switch statements",
                )),
                ProgramStatement::TryCatchInt32 { .. } | ProgramStatement::UnwindCleanup { .. } => {
                    // An unwind cleanup's exceptional path is its cleanup and
                    // then the point where the exception continues, numbered
                    // as the statements it steps.
                    let unwinding;
                    let (try_body, handler) = match statement {
                        ProgramStatement::TryCatchInt32 {
                            try_body, handler, ..
                        } => (try_body.as_ref(), handler.as_ref()),
                        ProgramStatement::UnwindCleanup { body, cleanup } => {
                            unwinding = crate::kernel::program_unwind_continuation(
                                cleanup,
                                crate::kernel::program_expression::int32_literal(0),
                            );
                            (body.as_ref(), &unwinding)
                        }
                        _ => unreachable!("matched a try or an unwind cleanup"),
                    };
                    let statement_index = *next_statement_index;
                    *next_statement_index += 1;
                    let try_statement_index = *next_statement_index;
                    let try_last =
                        visit(try_body, next_statement_index, layout, aggregate_objects)?;
                    let handler_statement_index = *next_statement_index;
                    let handler_last =
                        visit(handler, next_statement_index, layout, aggregate_objects)?;
                    let continuation_node = *next_statement_index;
                    layout.statements.insert(
                        statement_index,
                        SourceStatementRegion {
                            continuation_node,
                            kind: SourceStatementKind::Try {
                                try_statement_index,
                                handler_statement_index,
                                after_try_statement_index: continuation_node,
                                try_last_statement_index: try_last,
                                handler_last_statement_index: handler_last,
                            },
                        },
                    );
                    // Normal completion of the try body continues after the
                    // try. The handler's terminal outcomes (rethrow or return)
                    // make its continuation unreachable; keep it linked for
                    // uniformity.
                    if let Some(region) = layout.statements.get_mut(&try_last) {
                        region.continuation_node = continuation_node;
                    }
                    if let Some(region) = layout.statements.get_mut(&handler_last) {
                        region.continuation_node = continuation_node;
                    }
                    Ok(statement_index)
                }
                _ => {
                    let statement_index = *next_statement_index;
                    if let ProgramStatement::DeclareAggregate {
                        name,
                        layout: declared,
                        ..
                    } = statement
                    {
                        aggregate_objects
                            .insert(name.binding().clone(), aggregate_result_fields(declared));
                        if name
                            .binding()
                            .local_id()
                            .is_some_and(|id| id.call_parameter().is_some())
                        {
                            layout
                                .prepared_layouts
                                .insert(name.binding().clone(), declared.clone());
                        }
                        // Construction can require proofs about the destination before
                        // it has initialized fields or published the constructed value.
                        let binding = name.binding();
                        if binding
                            .local_id()
                            .is_some_and(crate::kernel::LocalBindingId::is_temporary)
                        {
                            layout.call_results.insert(statement_index, binding.clone());
                        }
                    }
                    if let ProgramStatement::CallConstruct { target, .. } = statement {
                        let fields = aggregate_objects.get(target).ok_or_else(|| {
                            ClickError::new(format!(
                                "construction result `{target}` has no declared aggregate layout"
                            ))
                        })?;
                        layout
                            .aggregate_results
                            .insert(statement_index, fields.clone());
                    }
                    if let ProgramStatement::CallResult {
                        aggregate_layout: Some(result),
                        ..
                    } = statement
                    {
                        layout
                            .aggregate_results
                            .insert(statement_index, aggregate_result_fields(&result.layout));
                    }
                    if let ProgramStatement::CallResult { call, .. }
                    | ProgramStatement::BuiltinConstantP { step: call } = statement
                    {
                        layout.call_numbers.insert(statement_index, *call);
                        layout.step_regions.insert(*call, statement_index);
                    }
                    if let ProgramStatement::StepValue {
                        steps, expression, ..
                    } = statement
                    {
                        if let ProgramExpression::Variable(name) = expression
                            && name
                                .local_id()
                                .is_some_and(crate::kernel::LocalBindingId::is_temporary)
                            && let Some(fields) = aggregate_objects.get(name)
                        {
                            layout
                                .aggregate_results
                                .insert(statement_index, fields.clone());
                        }
                        for step in steps {
                            if let std::collections::btree_map::Entry::Vacant(entry) =
                                layout.step_regions.entry(*step)
                            {
                                entry.insert(statement_index);
                                layout.call_numbers.entry(statement_index).or_insert(*step);
                            }
                        }
                    }
                    if let ProgramStatement::Call { arguments, .. }
                    | ProgramStatement::CallResult { arguments, .. }
                    | ProgramStatement::CallConstruct { arguments, .. } = statement
                    {
                        layout.calls.insert(statement_index);
                        record_prepared_arguments(
                            layout,
                            statement_index,
                            arguments.iter().filter_map(kernel_argument_binding),
                        );
                    }
                    if let ProgramStatement::Call {
                        function_name,
                        callee: None,
                        ..
                    }
                    | ProgramStatement::CallResult {
                        function_name,
                        callee: None,
                        ..
                    }
                    | ProgramStatement::CallConstruct { function_name, .. } = statement
                    {
                        layout.call_targets.insert(
                            statement_index,
                            crate::surface::call_source_spelling(function_name).to_string(),
                        );
                    }
                    if let ProgramStatement::Assign {
                        name,
                        expression:
                            ProgramExpression::StepResult {
                                step,
                                origin: crate::kernel::StepOrigin::Call(_),
                                ..
                            },
                        ..
                    } = statement
                        && name
                            .local_id()
                            .is_some_and(crate::kernel::LocalBindingId::is_temporary)
                    {
                        layout.call_captures.insert(name.clone(), *step);
                    }
                    if let ProgramStatement::Assign { name, .. } = statement
                        && name
                            .local_id()
                            .is_some_and(crate::kernel::LocalBindingId::is_return_place)
                        && name.program_type().is_some_and(|ty| {
                            ty == ProgramType::Bool
                                || ty.is_pointer()
                                || crate::kernel::MachineIntegerType::from_program_type(ty)
                                    .is_some()
                        })
                    {
                        // Record the value of the return expression at this
                        // write, even if cleanup runs before the function exits.
                        layout.call_results.insert(statement_index, name.clone());
                        layout.snapshot_step_results = true;
                    }
                    if let ProgramStatement::CallConstruct { target, .. }
                    | ProgramStatement::HeapAllocate { target, .. } = statement
                    {
                        layout.call_results.insert(statement_index, target.clone());
                    }
                    if matches!(statement, ProgramStatement::HeapAllocate { .. }) {
                        layout.allocation_regions.insert(statement_index);
                    }
                    if let ProgramStatement::Assign { name, .. }
                    | ProgramStatement::CallConstruct { target: name, .. }
                    | ProgramStatement::Update {
                        target: ProgramExpression::Variable(name),
                        ..
                    } = statement
                    {
                        record_assignment(layout, name, statement_index);
                    }
                    *next_statement_index += 1;
                    layout.statements.insert(
                        statement_index,
                        SourceStatementRegion {
                            continuation_node: *next_statement_index,
                            kind: SourceStatementKind::Plain,
                        },
                    );
                    Ok(statement_index)
                }
            }
        }
        let mut aggregate_objects = BTreeMap::new();
        for parameter in function.parameters() {
            if let Some(value) = parameter.aggregate_layout() {
                aggregate_objects.insert(
                    parameter.binding_name().clone(),
                    aggregate_result_fields(value),
                );
            }
        }
        if let Some(value) = function.return_aggregate_layout() {
            aggregate_objects.insert(
                crate::kernel::CONTRACT_RESULT,
                aggregate_result_fields(value),
            );
        }
        visit(
            function.body(),
            &mut next_statement_index,
            &mut layout,
            &mut aggregate_objects,
        )?;
        layout.snapshot_step_results |= !layout.call_numbers.is_empty();
        for (step, pointee) in imported.step_pointee_layouts() {
            crate::instrumentation::record_deterministic_work(1);
            if let Some(region) = layout.step_regions.get(step) {
                layout
                    .pointee_results
                    .insert(*region, aggregate_result_fields(pointee));
            }
        }
        // The statements as written its front end says each region comes
        // from, which name them as C's do.
        if let Some(sites) = imported.source_sites() {
            if sites.regions.len() != next_statement_index {
                return Err(ClickError::new(format!(
                    "`{}` has {next_statement_index} regions but its front end placed {} in its statements as written",
                    imported.name(),
                    sites.regions.len()
                )));
            }
            for (region, site) in sites.regions.iter().enumerate() {
                let Some(site) = site else {
                    continue;
                };
                let path = sites.paths.get(*site as usize).ok_or_else(|| {
                    ClickError::new(format!(
                        "`{}` places a region in statement {site}, which it does not have",
                        imported.name()
                    ))
                })?;
                layout
                    .source_statements
                    .entry(path.clone())
                    .or_default()
                    .push(region);
                layout.region_paths.insert(region, path.clone());
            }
            // A loop is the statement its own region comes from, the region
            // just before its body.
            let loops = layout
                .loop_bodies
                .iter()
                .filter_map(|(index, body)| {
                    let path = layout.region_paths.get(&body.checked_sub(1)?)?;
                    Some((*index, path.clone()))
                })
                .collect::<Vec<_>>();
            layout.loop_paths.extend(loops);
        }
        if !layout.call_numbers.is_empty() {
            let mut named = NamedCalls::default();
            for (region, callee) in &layout.call_targets {
                crate::instrumentation::record_deterministic_work(1);
                named
                    .in_function
                    .entry(callee.clone())
                    .or_default()
                    .push(*region);
                if let Some(path) = layout.region_paths.get(region) {
                    named
                        .in_statement
                        .entry(path.clone())
                        .or_default()
                        .entry(callee.clone())
                        .or_default()
                        .push(*region);
                }
            }
            layout.named_calls = Some(named);
        }
        // A construction return already contains the completed result in the
        // caller's destination. Retire private value parameters at its checked
        // return boundary, so preservation names the same transition as the
        // published outcome. Copy returns still need their source objects when
        // the kernel materializes the returned copy.
        let return_parameters = if function.contract_interface().aggregate_return_mode()
            == crate::kernel::AggregateReturnMode::Construction
        {
            function
                .parameters()
                .iter()
                .filter_map(|parameter| {
                    parameter
                        .aggregate_layout()
                        .map(|_| parameter.binding_name().clone())
                })
                .collect()
        } else {
            Vec::new()
        };
        collect_kernel_automatic_exits(function.body(), return_parameters, &mut layout);
        finish_loop_phase_regions(&mut layout);
        Ok(Self {
            data: std::sync::Arc::new(layout),
        })
    }

    pub(in crate::surface) fn new(statement: &syntax::CStatement) -> Self {
        Self::new_with_natural_loop(statement, None, None, None)
    }

    pub(in crate::surface) fn new_for_function(
        function: &crate::languages::interface::ImportedFunction,
    ) -> Self {
        let mut layout = match function.natural_control_loop() {
            Some((target, exit_target, _)) => {
                let exit_label = exit_target.and_then(|exit_target| {
                    function
                        .control_targets()
                        .iter()
                        .find(|(_, (target, _))| *target == exit_target)
                        .map(|(name, _)| name.clone())
                });
                Self::new_with_natural_loop(
                    function.body(),
                    Some(target),
                    exit_target,
                    exit_label.as_deref(),
                )
            }
            None => Self::new(function.body()),
        };
        std::sync::Arc::get_mut(&mut layout.data)
            .expect("new layout is unshared")
            .parameter_names = function
            .parameters()
            .iter()
            .map(|p| p.name().to_string())
            .collect();
        layout
    }

    pub(in crate::surface) fn has_parameter_name(&self, name: &str) -> bool {
        self.data.parameter_names.contains(name)
    }

    fn new_with_natural_loop(
        statement: &syntax::CStatement,
        natural_loop_target: Option<crate::kernel::ControlTargetId>,
        natural_exit_target: Option<crate::kernel::ControlTargetId>,
        natural_exit_label: Option<&str>,
    ) -> Self {
        /// Records where the statement at `index` was written and returns
        /// that site. A labeled statement is one layout statement written
        /// where its body is; a statement with no site of its own (`break`,
        /// `continue`, `goto`, an empty statement) is named by the statement
        /// enclosing it, whose step it completes.
        fn record_site(
            layout: &mut SourceExecutionLayoutData,
            index: usize,
            mut statement: &syntax::CStatement,
            enclosing: Option<&Site>,
        ) -> Option<Site> {
            while let syntax::CStatement::Label {
                statement: body, ..
            } = statement
            {
                statement = body;
            }
            if syntax_statement_reads(statement) {
                layout.reads.push(index);
            }
            // Only a statement's own site places it among the statements as
            // written; one with no site has no path of its own.
            if let Some(path) = statement
                .site()
                .and_then(syntax::CSite::get)
                .and_then(|site| site.source_path())
            {
                if matches!(statement, syntax::CStatement::EndAggregateLifetimes { .. }) {
                    layout.full_expression_ends.insert(index);
                }
                layout
                    .source_statements
                    .entry(path.to_vec())
                    .or_default()
                    .push(index);
                layout.region_paths.insert(index, path.to_vec());
            }
            if let syntax::CStatement::LoopTest { .. } = statement {
                layout.loop_tests.insert(index);
            }
            if let syntax::CStatement::CallResult {
                aggregate_layout: Some(result_layout),
                ..
            }
            | syntax::CStatement::StepValue {
                aggregate_layout: Some(result_layout),
                ..
            } = statement
            {
                let value_layout = result_layout.to_kernel_aggregate_layout();
                // The operator region owns the arm's result spelling.
                let owner = match statement {
                    syntax::CStatement::StepValue { steps, .. } => steps
                        .first()
                        .and_then(|step| layout.step_regions.get(step))
                        .copied()
                        .unwrap_or(index),
                    _ => index,
                };
                layout
                    .aggregate_results
                    .insert(owner, aggregate_result_fields(&value_layout));
            }
            if let syntax::CStatement::CallResult { call, .. }
            | syntax::CStatement::BuiltinConstantP { step: call, .. } = statement
            {
                layout.call_numbers.insert(index, *call);
                layout.step_regions.insert(*call, index);
            }
            // An operator `if` region makes its operator's value, which its
            // exit records as the region's result.
            if let syntax::CStatement::If {
                operator: Some(operator),
                ..
            } = statement
            {
                layout.operator_regions.insert(index, operator.kind);
                layout.call_numbers.insert(index, operator.step);
                layout.step_regions.insert(operator.step, index);
            }
            // A value step's region makes the value its steps name, unless
            // an operator `if` already made those steps its own.
            if let syntax::CStatement::StepValue { steps, .. } = statement {
                for step in steps {
                    if let std::collections::btree_map::Entry::Vacant(entry) =
                        layout.step_regions.entry(*step)
                    {
                        entry.insert(index);
                        layout.call_numbers.entry(index).or_insert(*step);
                    }
                }
            }
            if let syntax::CStatement::Assign {
                name,
                prior_result: Some(step),
                ..
            } = statement
            {
                layout.step_regions.insert(*step, index);
                layout.prior_steps.insert(*step, name.clone());
            }
            if let syntax::CStatement::Call { arguments, .. }
            | syntax::CStatement::CallResult { arguments, .. } = statement
            {
                layout.calls.insert(index);
                record_prepared_arguments(
                    layout,
                    index,
                    arguments.iter().filter_map(|argument| match argument {
                        syntax::CExpression::Variable(name) => Some(name),
                        _ => None,
                    }),
                );
            }
            if let syntax::CStatement::DeclareStructValue {
                name,
                layout: declared,
                ..
            } = statement
                && name
                    .binding()
                    .local_id()
                    .is_some_and(|id| id.call_parameter().is_some())
            {
                layout.prepared_layouts.insert(
                    name.binding().clone(),
                    declared.to_kernel_aggregate_layout(),
                );
            }
            if let syntax::CStatement::Call {
                function_name,
                callee: None,
                ..
            }
            | syntax::CStatement::CallResult {
                function_name,
                callee: None,
                ..
            } = statement
            {
                layout.call_targets.insert(
                    index,
                    crate::surface::call_source_spelling(function_name).to_string(),
                );
            }
            if let syntax::CStatement::HeapAllocate { target, .. } = statement {
                layout.call_results.insert(index, target.clone());
            }
            if matches!(statement, syntax::CStatement::HeapAllocate { .. }) {
                layout.allocation_regions.insert(index);
            }
            let site = statement
                .site()
                .and_then(syntax::CSite::get)
                .or(enclosing)
                .cloned()?;
            layout.sites.insert(index, site.clone());
            Some(site)
        }

        /// Visits one subtree and returns the pre-order index of its last
        /// top-level statement, so an enclosing `if` can redirect its arms'
        /// control successors past the sibling arm to its own continuation.
        /// `enclosing` is the site of the nearest enclosing statement.
        fn visit(
            statement: &syntax::CStatement,
            next_statement_index: &mut usize,
            next_loop_index: &mut usize,
            layout: &mut SourceExecutionLayoutData,
            enclosing: Option<&Site>,
        ) -> usize {
            match statement {
                // A labeled statement is laid out as its body; the natural
                // cycle layout below visits its labels' bodies itself.
                syntax::CStatement::Label {
                    statement: body, ..
                } => visit(
                    body,
                    next_statement_index,
                    next_loop_index,
                    layout,
                    enclosing,
                ),
                syntax::CStatement::Seq(first, second) => {
                    visit(
                        first,
                        next_statement_index,
                        next_loop_index,
                        layout,
                        enclosing,
                    );
                    visit(
                        second,
                        next_statement_index,
                        next_loop_index,
                        layout,
                        enclosing,
                    )
                }
                syntax::CStatement::If {
                    then_branch,
                    else_branch,
                    ..
                } => {
                    let statement_index = *next_statement_index;
                    let own = record_site(layout, statement_index, statement, enclosing);
                    *next_statement_index += 1;
                    let then_statement_index = *next_statement_index;
                    let then_last = visit(
                        then_branch,
                        next_statement_index,
                        next_loop_index,
                        layout,
                        own.as_ref(),
                    );
                    let else_statement_index = *next_statement_index;
                    let else_last = visit(
                        else_branch,
                        next_statement_index,
                        next_loop_index,
                        layout,
                        own.as_ref(),
                    );
                    let continuation_node = *next_statement_index;
                    layout.statements.insert(
                        statement_index,
                        SourceStatementRegion {
                            continuation_node,
                            kind: SourceStatementKind::If {
                                then_statement_index,
                                else_statement_index,
                            },
                        },
                    );
                    // Completing either arm's last statement completes this
                    // `if` region and continues at this `if`'s continuation,
                    // not at the next pre-order statement (the sibling arm).
                    redirect_control_successor(
                        layout,
                        then_last,
                        statement_index,
                        continuation_node,
                    );
                    redirect_control_successor(
                        layout,
                        else_last,
                        statement_index,
                        continuation_node,
                    );
                    statement_index
                }
                syntax::CStatement::While { test, body, .. }
                | syntax::CStatement::DoWhile { test, body, .. } => {
                    let statement_index = *next_statement_index;
                    let own = record_site(layout, statement_index, statement, enclosing);
                    let loop_index = *next_loop_index;
                    if let Some(path) = own.as_ref().and_then(|site| site.source_path()) {
                        layout.loop_paths.insert(loop_index, path.to_vec());
                    }
                    *next_statement_index += 1;
                    *next_loop_index += 1;
                    layout.loop_bodies.insert(loop_index, *next_statement_index);
                    let post_test = matches!(statement, syntax::CStatement::DoWhile { .. });
                    if test.is_none() {
                        layout.loop_test_phases.insert(
                            loop_index,
                            (
                                if post_test {
                                    crate::kernel::LoopTestPosition::AfterBody
                                } else {
                                    crate::kernel::LoopTestPosition::BeforeBody
                                },
                                usize::MAX,
                                usize::MAX,
                            ),
                        );
                    }
                    if !post_test && let Some(test) = test {
                        visit(
                            test,
                            next_statement_index,
                            next_loop_index,
                            layout,
                            own.as_ref(),
                        );
                    }
                    visit(
                        body,
                        next_statement_index,
                        next_loop_index,
                        layout,
                        own.as_ref(),
                    );
                    if post_test && let Some(test) = test {
                        layout
                            .loop_updates
                            .insert(loop_index, *next_statement_index);
                        visit(
                            test,
                            next_statement_index,
                            next_loop_index,
                            layout,
                            own.as_ref(),
                        );
                    }
                    if let Some((_, _, end)) = layout.loop_test_phases.get_mut(&loop_index) {
                        *end = *next_statement_index;
                    }
                    layout.statements.insert(
                        statement_index,
                        SourceStatementRegion {
                            continuation_node: *next_statement_index,
                            kind: SourceStatementKind::Loop { loop_index },
                        },
                    );
                    statement_index
                }
                syntax::CStatement::For {
                    test,
                    initializer,
                    body,
                    step,
                    ..
                } => {
                    let for_site = statement.site().and_then(syntax::CSite::get).or(enclosing);
                    visit(
                        initializer,
                        next_statement_index,
                        next_loop_index,
                        layout,
                        for_site,
                    );
                    let statement_index = *next_statement_index;
                    let own = record_site(layout, statement_index, statement, enclosing);
                    let loop_index = *next_loop_index;
                    if let Some(path) = own.as_ref().and_then(|site| site.source_path()) {
                        layout.loop_paths.insert(loop_index, path.to_vec());
                    }
                    *next_statement_index += 1;
                    *next_loop_index += 1;
                    layout.loop_bodies.insert(loop_index, *next_statement_index);
                    if test.is_none() {
                        layout.loop_test_phases.insert(
                            loop_index,
                            (
                                crate::kernel::LoopTestPosition::BeforeBody,
                                usize::MAX,
                                usize::MAX,
                            ),
                        );
                    }
                    if let Some(test) = test {
                        visit(
                            test,
                            next_statement_index,
                            next_loop_index,
                            layout,
                            own.as_ref(),
                        );
                    }
                    visit(
                        body,
                        next_statement_index,
                        next_loop_index,
                        layout,
                        own.as_ref(),
                    );
                    layout
                        .loop_updates
                        .insert(loop_index, *next_statement_index);
                    visit(
                        step,
                        next_statement_index,
                        next_loop_index,
                        layout,
                        own.as_ref(),
                    );
                    if let Some((_, _, end)) = layout.loop_test_phases.get_mut(&loop_index) {
                        *end = *next_statement_index;
                    }
                    layout.statements.insert(
                        statement_index,
                        SourceStatementRegion {
                            continuation_node: *next_statement_index,
                            kind: SourceStatementKind::Loop { loop_index },
                        },
                    );
                    statement_index
                }
                _ => {
                    let statement_index = *next_statement_index;
                    record_site(layout, statement_index, statement, enclosing);
                    if let syntax::CStatement::Assign { name, .. }
                    | syntax::CStatement::AggregateCopy {
                        target: syntax::CExpression::Variable(name),
                        ..
                    }
                    | syntax::CStatement::Update {
                        target: syntax::CExpression::Variable(name),
                        ..
                    } = statement
                    {
                        record_assignment(layout, name, statement_index);
                    }
                    *next_statement_index += 1;
                    layout.statements.insert(
                        statement_index,
                        SourceStatementRegion {
                            continuation_node: *next_statement_index,
                            kind: SourceStatementKind::Plain,
                        },
                    );
                    statement_index
                }
            }
        }

        /// Redirects the control successor of an arm's last statement to the
        /// enclosing `if`'s continuation and records the completed branch
        /// region. When that last statement is itself an `if`, its own arms'
        /// tails complete both branch regions at once, recursively.
        fn redirect_control_successor(
            layout: &mut SourceExecutionLayoutData,
            last_statement_index: usize,
            exited_if_index: usize,
            continuation_node: usize,
        ) {
            // A statement already redirected for this `if` was redirected,
            // with everything it ends, by an earlier visit: an arm can be
            // reached again through each nested `if` it closes, and
            // revisiting it doubled the walk at every level of nesting.
            if layout
                .exited_branch_regions
                .get(&last_statement_index)
                .is_some_and(|exited| exited.contains(&exited_if_index))
            {
                return;
            }
            let Some(region) = layout.statements.get_mut(&last_statement_index) else {
                return;
            };
            region.continuation_node = continuation_node;
            layout
                .exited_branch_regions
                .entry(last_statement_index)
                .or_default()
                .push(exited_if_index);
            layout
                .arm_lasts_by_exited_region
                .entry(exited_if_index)
                .or_default()
                .push(last_statement_index);
            if let SourceStatementKind::If { .. } = region.kind {
                // In statement order, each statement once: what the scan of
                // every statement's list returned.
                let mut arm_lasts: Vec<usize> = layout
                    .arm_lasts_by_exited_region
                    .get(&last_statement_index)
                    .cloned()
                    .unwrap_or_default();
                arm_lasts.sort_unstable();
                arm_lasts.dedup();
                for arm_last in arm_lasts {
                    redirect_control_successor(
                        layout,
                        arm_last,
                        exited_if_index,
                        continuation_node,
                    );
                }
            }
        }

        let mut data = SourceExecutionLayoutData::default();
        if let Some(target) = natural_loop_target {
            let mut statements = Vec::new();
            flatten_direct_c_statements(statement, &mut statements);
            let loop_index = 0;
            let statement_index = 0;
            let mut next_statement_index = 1;
            let mut next_loop_index = 1;
            data.loop_bodies.insert(loop_index, next_statement_index);
            data.natural_loop_targets.insert(loop_index, target);
            let exit_label_index = natural_exit_label.and_then(|name| {
                statements.iter().position(|statement| {
                    matches!(
                        statement,
                        syntax::CStatement::Label { name: label, .. } if label == name
                    )
                })
            });
            if let Some(syntax::CStatement::Label { statement, .. }) = statements.first() {
                visit(
                    statement,
                    &mut next_statement_index,
                    &mut next_loop_index,
                    &mut data,
                    None,
                );
            }
            let cycle_tail = exit_label_index.unwrap_or(statements.len());
            for statement in statements.iter().skip(1).take(cycle_tail.saturating_sub(1)) {
                visit(
                    statement,
                    &mut next_statement_index,
                    &mut next_loop_index,
                    &mut data,
                    None,
                );
            }
            if let (Some(exit_target), Some(exit_label_index)) =
                (natural_exit_target, exit_label_index)
            {
                data.natural_exit_targets.insert(loop_index, exit_target);
                data.natural_exit_statement_indices
                    .insert(loop_index, next_statement_index);
                let syntax::CStatement::Label { statement, .. } = statements[exit_label_index]
                else {
                    unreachable!("natural exit target points to a label");
                };
                visit(
                    statement,
                    &mut next_statement_index,
                    &mut next_loop_index,
                    &mut data,
                    None,
                );
            }
            data.statements.insert(
                statement_index,
                SourceStatementRegion {
                    continuation_node: next_statement_index,
                    kind: SourceStatementKind::Loop { loop_index },
                },
            );
        } else {
            visit(statement, &mut 0, &mut 0, &mut data, None);
        }
        collect_automatic_exits(statement, &mut data);
        finish_loop_phase_regions(&mut data);
        Self {
            data: std::sync::Arc::new(data),
        }
    }

    /// The C `if` regions that complete when this statement completes
    /// normally, innermost first.
    pub(in crate::surface) fn exited_branch_regions(&self, index: usize) -> &[usize] {
        self.data
            .exited_branch_regions
            .get(&index)
            .map_or(&[], Vec::as_slice)
    }

    pub(in crate::surface) fn automatic_continue_exits(
        &self,
        index: usize,
    ) -> &[crate::kernel::BindingName] {
        self.data
            .automatic_continue_exits
            .get(&index)
            .map(Vec::as_slice)
            .unwrap_or_else(|| self.automatic_exits(index, true))
    }

    pub(in crate::surface) fn automatic_exits(
        &self,
        index: usize,
        abrupt: bool,
    ) -> &[crate::kernel::BindingName] {
        let exits = if abrupt {
            &self.data.automatic_abrupt_exits
        } else {
            &self.data.automatic_exits
        };
        exits.get(&index).map_or(&[], Vec::as_slice)
    }

    pub(in crate::surface) fn statement(&self, index: usize) -> Option<SourceStatementRegion> {
        self.data.statements.get(&index).copied()
    }

    /// Where the C statement at `index` was written, when it records it.
    /// The places a refusal in this function names reads by, built on
    /// first use.
    pub(in crate::surface) fn diagnostic_places(
        &self,
        build: impl FnOnce() -> crate::surface::diagnostics::StatementPlaces,
    ) -> std::sync::Arc<crate::surface::diagnostics::StatementPlaces> {
        self.data
            .diagnostic_places
            .get_or_init(|| std::sync::Arc::new(build()))
            .clone()
    }

    /// The function's pointer element types, built by `build` on first use.
    pub(in crate::surface) fn local_pointer_element_types(
        &self,
        build: impl FnOnce() -> BTreeMap<String, crate::kernel::ProgramType>,
    ) -> &BTreeMap<String, crate::kernel::ProgramType> {
        self.data.local_pointer_element_types.get_or_init(build)
    }

    /// The function's loop regions, counted by `count` on first use.
    pub(in crate::surface) fn loop_region_count(&self, count: impl FnOnce() -> usize) -> usize {
        *self.data.loop_region_count.get_or_init(count)
    }

    /// The region a path through the statements as written names at `kind`.
    /// A statement path is entered at its first region, own or a child's,
    /// and exited at its compound region (an `if` or loop) when it has one,
    /// at its last own region otherwise, and at its last child's exit when
    /// it has no region of its own (a block). `.region(j)`, `.call(f, j)`,
    /// `.assignment(x, j)` and `.read(j)` name one of the statement's own
    /// regions, counted in executable order.
    /// The local holding the value produced by `region` at its exit.
    pub(in crate::surface) fn call_result_local(
        &self,
        region: usize,
    ) -> Option<&crate::kernel::BindingName> {
        self.data.call_results.get(&region)
    }

    pub(in crate::surface) fn has_call_captures(&self) -> bool {
        !self.data.call_captures.is_empty()
    }

    pub(in crate::surface) fn snapshots_step_results(&self) -> bool {
        self.data.snapshot_step_results
    }

    /// The object the call at `region` receives as its by-value aggregate
    /// parameter `name`, and that object's layout.
    pub(in crate::surface) fn call_parameter_object(
        &self,
        region: usize,
        name: &str,
    ) -> Option<(&crate::kernel::BindingName, &crate::kernel::AggregateLayout)> {
        let object = self
            .data
            .call_parameter_objects
            .get(&(region, name.to_owned()))?;
        Some((object, self.data.prepared_layouts.get(object)?))
    }

    /// The call region and parameter a prepared argument object is, with
    /// that region's source selector and the object's layout.
    pub(in crate::surface) fn prepared_parameter(
        &self,
        object: &crate::kernel::BindingName,
    ) -> Option<(
        crate::surface::CodeRegionRef,
        &str,
        &crate::kernel::AggregateLayout,
    )> {
        let (region, parameter) = self.data.prepared_parameters.get(object)?;
        let layout = self.data.prepared_layouts.get(object)?;
        let selector = self
            .call_region_source(*region)
            .unwrap_or(crate::surface::CodeRegionRef::Region(*region));
        Some((selector, parameter.as_str(), layout))
    }

    /// The source selector of the call that produced a frontend capture.
    pub(in crate::surface) fn call_capture_source(
        &self,
        binding: &crate::kernel::BindingName,
    ) -> Option<(usize, crate::surface::CodeRegionRef)> {
        crate::instrumentation::record_deterministic_work(1);
        let step = self.data.call_captures.get(binding)?;
        let region = self.step_region(*step)?;
        Some((region, self.call_region_source(region)?))
    }

    /// The source selector of direct-call region `region`:
    /// `statement(...).call(f, j)`.
    fn call_region_source(&self, region: usize) -> Option<crate::surface::CodeRegionRef> {
        use crate::surface::{CodeRegionRef, SourcePathStep};
        let callee = self.data.call_targets.get(&region)?;
        let path = self.data.region_paths.get(&region).map(Vec::as_slice);
        let calls = self.data.named_calls.as_ref()?.regions(path, callee);
        let ordinal = calls.binary_search(&region).ok()?;
        let mut steps = path
            .unwrap_or_default()
            .iter()
            .map(|index| SourcePathStep::Statement(*index as usize))
            .collect::<Vec<_>>();
        steps.push(SourcePathStep::Call(callee.clone(), ordinal));
        Some(CodeRegionRef::Path(steps))
    }

    /// The number of the call inside an expression that `region` is.
    pub(in crate::surface) fn is_aggregate_result(&self, region: usize) -> bool {
        self.data.aggregate_results.contains_key(&region)
    }

    pub(in crate::surface) fn aggregate_result_field(
        &self,
        region: usize,
        field: &str,
    ) -> Option<&crate::kernel::AggregateField> {
        crate::instrumentation::record_deterministic_work(1);
        self.data.aggregate_results.get(&region)?.get(field)
    }

    /// Field `field` of the record `region`'s pointer result points at.
    pub(in crate::surface) fn pointee_result_field(
        &self,
        region: usize,
        field: &str,
    ) -> Option<&crate::kernel::AggregateField> {
        crate::instrumentation::record_deterministic_work(1);
        self.data.pointee_results.get(&region)?.get(field)
    }

    pub(in crate::surface) fn is_pointee_result(&self, region: usize) -> bool {
        self.data.pointee_results.contains_key(&region)
    }

    pub(in crate::surface) fn call_number(&self, region: usize) -> Option<u32> {
        self.data.call_numbers.get(&region).copied()
    }

    /// A retained result’s source region. Compiler bodies without statement
    /// provenance expose their numbered regions as `region(N)`.
    /// Choose by retained provenance, rather than trying alternate spellings.
    pub(in crate::surface) fn result_code_region(
        &self,
        region: usize,
    ) -> Option<crate::surface::CodeRegionRef> {
        if self.data.region_paths.contains_key(&region) || self.data.calls.contains(&region) {
            self.source_path_spelling(region, crate::surface::ProgramPointKind::Exit)
                .map(crate::surface::CodeRegionRef::Path)
        } else {
            self.data
                .statements
                .contains_key(&region)
                .then_some(crate::surface::CodeRegionRef::Region(region))
        }
    }

    /// The region of the step numbered `step`.
    pub(in crate::surface) fn step_region(&self, step: u32) -> Option<usize> {
        self.data.step_regions.get(&step).copied()
    }

    /// The local whose prior value step `step` keeps, when it is an
    /// assignment step rather than a call.
    pub(in crate::surface) fn prior_step_local(
        &self,
        step: u32,
    ) -> Option<&crate::kernel::BindingName> {
        self.data.prior_steps.get(&step)
    }

    /// The local receiving a fresh allocation, rather than an arbitrary
    /// call result that may alias an allocation introduced elsewhere.
    pub(in crate::surface) fn allocation_result_local(
        &self,
        region: usize,
    ) -> Option<&crate::kernel::BindingName> {
        self.data
            .allocation_regions
            .contains(&region)
            .then(|| self.call_result_local(region))
            .flatten()
    }

    pub(in crate::surface) fn source_path_region(
        &self,
        steps: &[crate::surface::SourcePathStep],
        kind: crate::surface::ProgramPointKind,
    ) -> Result<usize, String> {
        use crate::surface::{ProgramPointKind, SourcePathStep};
        let data = &self.data;
        // `call(f, j)` and `call(j)` on their own count the function's
        // calls, in the order they run.
        match steps {
            [SourcePathStep::Call(function, index)] => {
                if let Some(named) = &data.named_calls {
                    let calls = named.regions(None, function);
                    return calls.get(*index).copied().ok_or_else(|| {
                        format!(
                            "this function calls `{function}` {} time(s), so it has no `call({function}, {index})`",
                            calls.len()
                        )
                    });
                }
                let calls = data
                    .calls
                    .iter()
                    .filter(|region| data.call_targets.get(region) == Some(function))
                    .collect::<Vec<_>>();
                return calls.get(*index).map(|region| **region).ok_or_else(|| {
                    format!(
                        "this function calls `{function}` {} time(s), so it has no `call({function}, {index})`",
                        calls.len()
                    )
                });
            }
            [SourcePathStep::AnyCall(index)] => {
                return data.calls.iter().nth(*index).copied().ok_or_else(|| {
                    format!(
                        "this function makes {} call(s), so it has no `call({index})`",
                        data.calls.len()
                    )
                });
            }
            _ => {}
        }
        if data.source_statements.is_empty() {
            return Err(
                "this function's source records no statements as written; name its points with `call(f, j)` or `region(N)`"
                    .into(),
            );
        }
        let mut steps = steps.iter();
        let mut path = match steps.next() {
            Some(SourcePathStep::Statement(index)) => vec![*index as u32],
            Some(SourcePathStep::Loop(index)) => data
                .loop_paths
                .get(index)
                .cloned()
                .ok_or_else(|| format!("`loop({index})` has no statement as written"))?,
            _ => return Err("a chained region starts with `statement(i)` or `loop(i)`".into()),
        };
        let describe = |path: &[u32]| {
            path.iter()
                .map(|index| format!("statement({index})"))
                .collect::<Vec<_>>()
                .join(".")
        };
        let has_statement = |path: &[u32]| {
            data.source_statements
                .range(path.to_vec()..)
                .next()
                .is_some_and(|(key, _)| key.starts_with(path))
        };
        if !has_statement(&path) {
            return Err(format!("this function has no `{}`", describe(&path)));
        }
        let own = |path: &[u32]| {
            data.source_statements
                .get(path)
                .map(Vec::as_slice)
                .unwrap_or(&[])
        };
        // The `index`th of the statement's own regions that `matches`, which
        // `what` describes for the refusal that names `step`.
        let own_occurrence = |path: &[u32],
                              index: usize,
                              matches: &dyn Fn(&usize) -> bool,
                              what: &str,
                              step: &str| {
            let regions = own(path)
                .iter()
                .filter(|region| matches(region))
                .collect::<Vec<_>>();
            regions.get(index).map(|region| **region).ok_or_else(|| {
                format!(
                    "`{}` has {} atomic region(s) of its own that {what}, so it has no `{step}`",
                    describe(path),
                    regions.len()
                )
            })
        };
        let mut remaining = steps.peekable();
        while let Some(step) = remaining.next() {
            let last = remaining.peek().is_none();
            match step {
                SourcePathStep::Statement(index) => {
                    path.push(*index as u32);
                    if !has_statement(&path) {
                        return Err(format!("this function has no `{}`", describe(&path)));
                    }
                }
                SourcePathStep::Region(index) if last => {
                    return own(&path).get(*index).copied().ok_or_else(|| {
                        format!(
                            "`{}` has {} atomic region(s) of its own, so it has no `region({index})`",
                            describe(&path),
                            own(&path).len()
                        )
                    });
                }
                SourcePathStep::Call(function, index) if last => {
                    if let Some(named) = &data.named_calls {
                        let calls = named.regions(Some(&path), function);
                        return calls.get(*index).copied().ok_or_else(|| {
                            format!(
                                "`{}` calls `{function}` {} time(s), so it has no `call({function}, {index})`",
                                describe(&path),
                                calls.len()
                            )
                        });
                    }
                    let calls = own(&path)
                        .iter()
                        .filter(|region| data.call_targets.get(region) == Some(function))
                        .collect::<Vec<_>>();
                    return calls.get(*index).map(|region| **region).ok_or_else(|| {
                        format!(
                            "`{}` calls `{function}` {} time(s), so it has no `call({function}, {index})`",
                            describe(&path),
                            calls.len()
                        )
                    });
                }
                SourcePathStep::Operator(kind, index) if last => {
                    let operators = own(&path)
                        .iter()
                        .filter(|region| data.operator_regions.get(region) == Some(kind))
                        .collect::<Vec<_>>();
                    let name = crate::surface::diagnostics::operator_step_name(*kind);
                    return operators.get(*index).map(|region| **region).ok_or_else(|| {
                        format!(
                            "`{}` has {} {} operator(s) whose operands run as steps, so it has no `{name}({index})`",
                            describe(&path),
                            operators.len(),
                            crate::surface::diagnostics::describe_operator_kind(*kind)
                        )
                    });
                }
                SourcePathStep::AnyCall(index) if last => {
                    let calls = own(&path)
                        .iter()
                        .filter(|region| data.calls.contains(region))
                        .collect::<Vec<_>>();
                    return calls.get(*index).map(|region| **region).ok_or_else(|| {
                        format!(
                            "`{}` makes {} call(s), so it has no `call({index})`",
                            describe(&path),
                            calls.len()
                        )
                    });
                }
                SourcePathStep::Test if last => {
                    return own(&path)
                        .iter()
                        .find(|region| data.loop_tests.contains(region))
                        .copied()
                        .ok_or_else(|| format!("`{}` has no loop test region", describe(&path)));
                }
                SourcePathStep::Assignment(local, index) if last => {
                    let assigns = |region: &usize| {
                        data.assignments
                            .get(local)
                            .is_some_and(|regions| regions.binary_search(region).is_ok())
                    };
                    return own_occurrence(
                        &path,
                        *index,
                        &assigns,
                        &format!("assign `{local}`"),
                        &format!("assignment({local}, {index})"),
                    );
                }
                SourcePathStep::Read(index) if last => {
                    let reads = |region: &usize| data.reads.binary_search(region).is_ok();
                    return own_occurrence(
                        &path,
                        *index,
                        &reads,
                        "read memory",
                        &format!("read({index})"),
                    );
                }
                SourcePathStep::Region(_)
                | SourcePathStep::Call(..)
                | SourcePathStep::Test
                | SourcePathStep::Assignment(..)
                | SourcePathStep::Operator(..)
                | SourcePathStep::AnyCall(_)
                | SourcePathStep::Read(_) => {
                    return Err(
                        "`region(j)`, `call(f, j)`, `test()`, `assignment(x, j)`, `read(j)`, `and(j)`, `or(j)` and `ternary(j)` end a chained region"
                            .into(),
                    );
                }
                SourcePathStep::ReadEvent(_) => {
                    return Err("`read_event(i)` selects a volatile observation's `.result`, not a statement boundary".into());
                }
                SourcePathStep::Loop(_) => {
                    return Err("`loop(i)` starts a chained region".into());
                }
            }
        }
        match kind {
            ProgramPointKind::Entry => Ok(*data
                .source_statements
                .range(path.clone()..)
                .take_while(|(key, _)| key.starts_with(&path))
                .flat_map(|(_, regions)| regions)
                .min()
                .expect("a statement that exists has a region")),
            ProgramPointKind::Exit => Ok(self.source_statement_exit(&path)),
        }
    }

    /// The path through the statements as written that names `region` at
    /// `kind`: its statement's `.entry` or `.exit` when the point is that,
    /// and otherwise the statement's call or region it is. `None` for a
    /// region with no statement as written. Each spelling is resolved back
    /// before it is returned, so it names exactly this point.
    pub(in crate::surface) fn source_path_spelling(
        &self,
        region: usize,
        kind: crate::surface::ProgramPointKind,
    ) -> Option<Vec<crate::surface::SourcePathStep>> {
        use crate::surface::SourcePathStep;
        let data = &self.data;
        // A call with no statement as written is named among the
        // function's calls.
        let Some(path) = data.region_paths.get(&region) else {
            if !data.calls.contains(&region) {
                return None;
            }
            let earlier = data.calls.range(..region);
            let steps = vec![match data.call_targets.get(&region) {
                Some(function) => SourcePathStep::Call(
                    function.clone(),
                    match &data.named_calls {
                        Some(named) => named.regions(None, function).binary_search(&region).ok()?,
                        None => earlier
                            .filter(|earlier| data.call_targets.get(earlier) == Some(function))
                            .count(),
                    },
                ),
                None => SourcePathStep::AnyCall(earlier.count()),
            }];
            return (self.source_path_region(&steps, kind) == Ok(region)).then_some(steps);
        };
        let mut steps = path
            .iter()
            .map(|index| SourcePathStep::Statement(*index as usize))
            .collect::<Vec<_>>();
        if self.source_path_region(&steps, kind) != Ok(region) {
            let own = data.source_statements.get(path)?;
            let position = own.iter().position(|own| *own == region)?;
            steps.push(match data.call_targets.get(&region) {
                None if data.loop_tests.contains(&region) => SourcePathStep::Test,
                // A call through a function pointer names no function.
                None if data.calls.contains(&region) => SourcePathStep::AnyCall(
                    own[..position]
                        .iter()
                        .filter(|earlier| data.calls.contains(earlier))
                        .count(),
                ),
                None if let Some(kind) = data.operator_regions.get(&region) => {
                    SourcePathStep::Operator(
                        *kind,
                        own[..position]
                            .iter()
                            .filter(|earlier| data.operator_regions.get(earlier) == Some(kind))
                            .count(),
                    )
                }
                Some(function) => SourcePathStep::Call(
                    function.clone(),
                    own[..position]
                        .iter()
                        .filter(|earlier| data.call_targets.get(earlier) == Some(function))
                        .count(),
                ),
                None => SourcePathStep::Region(position),
            });
        }
        (self.source_path_region(&steps, kind) == Ok(region)).then_some(steps)
    }

    fn source_statement_exit(&self, path: &[u32]) -> usize {
        let data = &self.data;
        if let Some(regions) = data.source_statements.get(path) {
            if let Some(last) = regions.last().filter(|last| {
                data.full_expression_ends.contains(last)
                    && !data.hidden_loop_tests.contains_key(last)
            }) {
                return *last;
            }
            let compound = regions.iter().find(|region| {
                data.statements
                    .get(region)
                    .is_some_and(|statement| !matches!(statement.kind, SourceStatementKind::Plain))
            });
            return *compound.unwrap_or_else(|| regions.last().expect("own regions are nonempty"));
        }
        let last_child = data
            .source_statements
            .range(path.to_vec()..)
            .take_while(|(key, _)| key.starts_with(path))
            .filter_map(|(key, _)| key.get(path.len()).copied())
            .max()
            .expect("a statement with no region of its own has children");
        let mut child = path.to_vec();
        child.push(last_child);
        self.source_statement_exit(&child)
    }

    pub(in crate::surface) fn site(
        &self,
        index: usize,
    ) -> Option<&std::sync::Arc<syntax::CStatementSite>> {
        self.data.sites.get(&index)
    }

    pub(in crate::surface) fn execution_region_entry(
        &self,
        region: CodeRegion,
    ) -> Result<usize, String> {
        match region {
            CodeRegion::Statement(index) => Ok(index),
            CodeRegion::Loop(index) => self.loop_body_entry(index)
                .and_then(|body| body.checked_sub(1))
                .filter(|head| matches!(self.statement(*head).map(|r| r.kind), Some(SourceStatementKind::Loop { loop_index }) if loop_index == index))
                .ok_or_else(|| format!("`step_until` cannot resolve loop({index})")),
            _ => Err("`step_until` expects a statement or loop region".into()),
        }
    }

    pub(in crate::surface) fn assignment_entry(
        &self,
        local: &str,
        occurrence: usize,
    ) -> Result<usize, String> {
        crate::instrumentation::record_deterministic_work(1);
        self.data
            .assignments
            .get(local)
            .and_then(|entries| entries.get(occurrence))
            .copied()
            .ok_or_else(|| format!("`step_until` cannot resolve assignment({local}, {occurrence})"))
    }

    pub(in crate::surface) fn read_entry(&self, occurrence: usize) -> Result<usize, String> {
        crate::instrumentation::record_deterministic_work(1);
        self.data
            .reads
            .get(occurrence)
            .copied()
            .ok_or_else(|| format!("`step_until` cannot resolve read({occurrence})"))
    }

    pub(in crate::surface) fn loop_body_entry(&self, loop_index: usize) -> Option<usize> {
        self.data.loop_bodies.get(&loop_index).copied()
    }

    pub(in crate::surface) fn natural_loop_target(
        &self,
        loop_index: usize,
    ) -> Option<crate::kernel::ControlTargetId> {
        self.data.natural_loop_targets.get(&loop_index).copied()
    }

    pub(in crate::surface) fn natural_exit_target(
        &self,
        loop_index: usize,
    ) -> Option<crate::kernel::ControlTargetId> {
        self.data.natural_exit_targets.get(&loop_index).copied()
    }

    pub(in crate::surface) fn natural_exit_statement_index(
        &self,
        loop_index: usize,
    ) -> Option<usize> {
        self.data
            .natural_exit_statement_indices
            .get(&loop_index)
            .copied()
    }
}

pub(in crate::surface) fn contract_segment_referenced_names(
    segment: &ContractSegment,
) -> BTreeSet<String> {
    let mut names = BTreeSet::new();
    collect_program_expression_referenced_names(&segment.base, &mut names);
    collect_program_expression_referenced_names(&segment.start, &mut names);
    collect_program_expression_referenced_names(&segment.end, &mut names);
    names
}

pub(in crate::surface) fn collect_program_expression_referenced_names(
    expression: &ProgramExpression,
    names: &mut BTreeSet<String>,
) {
    let mut bindings = BTreeSet::<crate::kernel::BindingName>::new();
    collect_program_expression_referenced_bindings(expression, &mut bindings);
    names.extend(
        bindings
            .iter()
            .filter_map(|binding| binding.metadata_name().map(str::to_owned)),
    );
}

pub(in crate::surface) fn collect_program_expression_referenced_bindings<N: ReferencedBinding>(
    expression: &ProgramExpression,
    names: &mut BTreeSet<N>,
) {
    match expression {
        ProgramExpression::Value(value) => N::captured_value(value, names),
        ProgramExpression::StringLiteral(_)
        | ProgramExpression::FunctionAddress(_)
        | ProgramExpression::StepResult { .. } => {}
        ProgramExpression::Variable(name) => {
            if let Some(name) = N::program(name) {
                names.insert(name);
            }
        }
        ProgramExpression::Cast { expression, .. }
        | ProgramExpression::Negate(expression)
        | ProgramExpression::FloatNegate(expression) => {
            collect_program_expression_referenced_bindings(expression, names);
        }
        ProgramExpression::Ternary {
            condition,
            then_branch,
            else_branch,
        } => {
            collect_program_expression_referenced_bindings(condition, names);
            collect_program_expression_referenced_bindings(then_branch, names);
            collect_program_expression_referenced_bindings(else_branch, names);
        }
        ProgramExpression::FloatClassification { expression, .. }
        | ProgramExpression::EnumField {
            value: expression, ..
        }
        | ProgramExpression::EnumIs {
            value: expression, ..
        } => {
            collect_program_expression_referenced_bindings(expression, names);
        }
        ProgramExpression::EnumConstruct { fields, .. } => {
            for field in fields {
                collect_program_expression_referenced_bindings(field, names);
            }
        }
        ProgramExpression::AddressOf(expression)
        | ProgramExpression::CheckedObjectAddress(expression)
        | ProgramExpression::Not(expression)
        | ProgramExpression::Load(expression) => {
            collect_program_expression_referenced_bindings(expression, names);
        }
        ProgramExpression::PointerOffsetBytes { pointer, .. }
        | ProgramExpression::Subobject { pointer, .. } => {
            collect_program_expression_referenced_bindings(pointer, names);
        }
        ProgramExpression::TypedLoad { pointer, .. } => {
            collect_program_expression_referenced_bindings(pointer, names);
        }
        crate::kernel::binary_c_expression!(left, right) => {
            collect_program_expression_referenced_bindings(left, names);
            collect_program_expression_referenced_bindings(right, names);
        }
        ProgramExpression::BitwiseNot(expression) => {
            collect_program_expression_referenced_bindings(expression, names);
        }
    }
}

/// Index lexical lifetime boundaries once. Normal exits are attached to every
/// terminal source node of a scope (including a whole branch executed at once).
/// Abrupt exits visit only the scopes they leave; ordinary statements do not
/// copy their enclosing declarations or scan the function.
/// Typed frontends already supply kernel statements. Track their automatic
/// scope exits with the same pre-order numbering and scope rules as C syntax.
/// Root function storage belongs to the call frame; only nested scopes expire
/// here. Walking scope spines visits declarations once per containing scope.
/// Persistent exit lists for the active lexical scope. A switch's outgoing
/// continue reads these directly instead of searching its enclosing scopes.
struct AutomaticScope {
    names: Vec<crate::kernel::BindingName>,
    all_exits: imbl::Vector<crate::kernel::BindingName>,
    continue_exits: imbl::Vector<crate::kernel::BindingName>,
    loop_head: Option<usize>,
}

impl AutomaticScope {
    fn new(
        parent: Option<&Self>,
        names: Vec<crate::kernel::BindingName>,
        loop_head: Option<usize>,
    ) -> Self {
        crate::instrumentation::record_deterministic_work(1 + names.len());
        let mut all_exits = parent
            .map(|parent| parent.all_exits.clone())
            .unwrap_or_default();
        let mut continue_exits = if loop_head.is_some() {
            imbl::Vector::new()
        } else {
            parent
                .map(|parent| parent.continue_exits.clone())
                .unwrap_or_default()
        };
        for name in names.iter().rev() {
            all_exits.push_front(name.clone());
            continue_exits.push_front(name.clone());
        }
        Self {
            names,
            all_exits,
            continue_exits,
            loop_head: loop_head.or_else(|| parent.and_then(|parent| parent.loop_head)),
        }
    }

    fn exits(scopes: &[Self], continuing: bool) -> Vec<crate::kernel::BindingName> {
        let Some(scope) = scopes.last() else {
            return Vec::new();
        };
        let names = if continuing {
            &scope.continue_exits
        } else {
            &scope.all_exits
        };
        crate::instrumentation::record_deterministic_work(names.len());
        names.iter().cloned().collect()
    }
}

fn collect_kernel_automatic_exits(
    source: &ProgramStatement,
    return_parameters: Vec<crate::kernel::BindingName>,
    layout: &mut SourceExecutionLayoutData,
) {
    fn declarations(s: &ProgramStatement, names: &mut Vec<crate::kernel::BindingName>) {
        match s {
            ProgramStatement::Declare { name, .. }
            | ProgramStatement::DeclareAggregate { name, .. } => names.push(name.binding().clone()),
            ProgramStatement::Seq(statements) => {
                for statement in statements.iter() {
                    declarations(statement, names);
                }
            }
            // An unwind cleanup does not introduce a lexical scope.
            ProgramStatement::UnwindCleanup { body, .. } => declarations(body, names),
            _ => {}
        }
    }
    fn scope(
        s: &ProgramStatement,
        index: &mut usize,
        scopes: &mut Vec<AutomaticScope>,
        loop_head: Option<usize>,
        layout: &mut SourceExecutionLayoutData,
        return_parameters: &[crate::kernel::BindingName],
    ) -> Vec<usize> {
        let mut names = Vec::new();
        declarations(s, &mut names);
        scopes.push(AutomaticScope::new(scopes.last(), names, loop_head));
        let tails = visit(s, index, scopes, layout, return_parameters);
        let names = scopes.pop().unwrap().names;
        for tail in &tails {
            layout
                .automatic_exits
                .entry(*tail)
                .or_default()
                .extend(names.iter().cloned());
        }
        tails
    }
    fn visit(
        s: &ProgramStatement,
        index: &mut usize,
        scopes: &mut Vec<AutomaticScope>,
        layout: &mut SourceExecutionLayoutData,
        return_parameters: &[crate::kernel::BindingName],
    ) -> Vec<usize> {
        if let ProgramStatement::Seq(statements) = s {
            let mut tails = Vec::new();
            for statement in statements.iter() {
                tails = visit(statement, index, scopes, layout, return_parameters);
            }
            return tails;
        }
        let head = *index;
        *index += 1;
        match s {
            ProgramStatement::If {
                then_branch,
                else_branch,
                ..
            } => {
                let mut tails = vec![head];
                tails.extend(scope(
                    then_branch,
                    index,
                    scopes,
                    None,
                    layout,
                    return_parameters,
                ));
                tails.extend(scope(
                    else_branch,
                    index,
                    scopes,
                    None,
                    layout,
                    return_parameters,
                ));
                tails
            }
            ProgramStatement::TryCatchInt32 {
                try_body, handler, ..
            } => {
                let mut tails = vec![head];
                tails.extend(scope(
                    try_body,
                    index,
                    scopes,
                    None,
                    layout,
                    return_parameters,
                ));
                tails.extend(scope(
                    handler,
                    index,
                    scopes,
                    None,
                    layout,
                    return_parameters,
                ));
                tails
            }
            // The body is in the enclosing scope; the exceptional path is
            // numbered as the layout numbers it.
            ProgramStatement::UnwindCleanup { body, cleanup } => {
                let mut tails = vec![head];
                tails.extend(visit(body, index, scopes, layout, return_parameters));
                let unwinding = crate::kernel::program_unwind_continuation(
                    cleanup,
                    crate::kernel::program_expression::int32_literal(0),
                );
                tails.extend(scope(
                    &unwinding,
                    index,
                    scopes,
                    None,
                    layout,
                    return_parameters,
                ));
                tails
            }
            ProgramStatement::Loop {
                test: loop_test,
                update,
                body,
                ..
            } => {
                let test = loop_test.source_region();
                if let Some(test) = test
                    .as_ref()
                    .filter(|test| test.position == crate::kernel::LoopTestPosition::BeforeBody)
                {
                    visit(&test.statement, index, scopes, layout, return_parameters);
                }
                scope(body, index, scopes, Some(head), layout, return_parameters);
                if let Some(update) = update {
                    visit(update, index, scopes, layout, return_parameters);
                }
                if let Some(test) = test
                    .as_ref()
                    .filter(|test| test.position == crate::kernel::LoopTestPosition::AfterBody)
                {
                    visit(&test.statement, index, scopes, layout, return_parameters);
                }
                vec![head]
            }
            ProgramStatement::Switch { .. } => {
                layout
                    .automatic_continue_exits
                    .insert(head, AutomaticScope::exits(scopes, true));
                layout
                    .automatic_abrupt_exits
                    .insert(head, AutomaticScope::exits(scopes, false));
                vec![head]
            }
            ProgramStatement::Break
            | ProgramStatement::Continue
            | ProgramStatement::Return(_)
            | ProgramStatement::Goto { .. } => {
                let loop_control =
                    matches!(s, ProgramStatement::Break | ProgramStatement::Continue);
                let mut names = AutomaticScope::exits(scopes, loop_control);
                if matches!(s, ProgramStatement::Break)
                    && let Some(head_loop) = scopes.last().and_then(|scope| scope.loop_head)
                {
                    layout.automatic_break_heads.insert(head, head_loop);
                }
                if matches!(s, ProgramStatement::Return(_)) {
                    names.extend(return_parameters.iter().cloned());
                }
                layout.automatic_abrupt_exits.insert(head, names);
                vec![head]
            }
            // Switch is refused by the typed layout before this pass. Other
            // operations occupy one native statement and introduce no scope.
            _ => vec![head],
        }
    }
    visit(source, &mut 0, &mut Vec::new(), layout, &return_parameters);
    for (at, head) in std::mem::take(&mut layout.automatic_break_heads) {
        let exited = layout
            .automatic_exits
            .get(&head)
            .cloned()
            .unwrap_or_default();
        layout
            .automatic_abrupt_exits
            .entry(at)
            .or_default()
            .extend(exited);
    }
}

fn collect_automatic_exits(source: &syntax::CStatement, layout: &mut SourceExecutionLayoutData) {
    use syntax::CStatement as S;
    fn declarations(s: &S, names: &mut Vec<crate::kernel::BindingName>) {
        match s {
            S::Declare { name, .. } | S::DeclareStructValue { name, .. } => {
                names.push(name.binding().clone())
            }
            S::Seq(a, b) => {
                declarations(a, names);
                declarations(b, names);
            }
            S::Label { statement, .. } => declarations(statement, names),
            _ => {}
        }
    }
    fn scope(
        s: &S,
        index: &mut usize,
        scopes: &mut Vec<AutomaticScope>,
        loop_head: Option<usize>,
        layout: &mut SourceExecutionLayoutData,
    ) -> Vec<usize> {
        let mut names = Vec::new();
        declarations(s, &mut names);
        scopes.push(AutomaticScope::new(scopes.last(), names, loop_head));
        let tails = visit(s, index, scopes, layout);
        let names = scopes.pop().unwrap().names;
        for tail in &tails {
            layout
                .automatic_exits
                .entry(*tail)
                .or_default()
                .extend(names.iter().cloned());
        }
        tails
    }
    fn visit(
        s: &S,
        index: &mut usize,
        scopes: &mut Vec<AutomaticScope>,
        layout: &mut SourceExecutionLayoutData,
    ) -> Vec<usize> {
        if let S::Seq(a, b) = s {
            visit(a, index, scopes, layout);
            return visit(b, index, scopes, layout);
        }
        if let S::For {
            test,
            initializer,
            body,
            step,
            ..
        } = s
        {
            visit(initializer, index, scopes, layout);
            let head = *index;
            *index += 1;
            let mut names = Vec::new();
            declarations(initializer, &mut names);
            // The initializer belongs to the for statement, not its body.
            scopes.push(AutomaticScope::new(scopes.last(), names.clone(), None));
            if let Some(test) = test {
                visit(test, index, scopes, layout);
            }
            scope(body, index, scopes, Some(head), layout);
            visit(step, index, scopes, layout);
            scopes.pop();
            layout
                .automatic_exits
                .entry(head)
                .or_default()
                .extend(names);
            return vec![head];
        }
        let head = *index;
        *index += 1;
        match s {
            S::If {
                then_branch,
                else_branch,
                ..
            } => {
                let mut tails = vec![head];
                tails.extend(scope(then_branch, index, scopes, None, layout));
                tails.extend(scope(else_branch, index, scopes, None, layout));
                tails
            }
            S::While { test, body, .. } | S::DoWhile { test, body, .. } => {
                let post_test = matches!(s, S::DoWhile { .. });
                if !post_test && let Some(test) = test {
                    visit(test, index, scopes, layout);
                }
                scope(body, index, scopes, Some(head), layout);
                if post_test && let Some(test) = test {
                    visit(test, index, scopes, layout);
                }
                vec![head]
            }
            S::Switch { .. } => {
                layout
                    .automatic_continue_exits
                    .insert(head, AutomaticScope::exits(scopes, true));
                layout
                    .automatic_abrupt_exits
                    .insert(head, AutomaticScope::exits(scopes, false));
                vec![head]
            }
            S::Break | S::Continue | S::Return(_, _) | S::Goto { .. } => {
                let loop_control = matches!(s, S::Break | S::Continue);
                let names = AutomaticScope::exits(scopes, loop_control);
                if matches!(s, S::Break)
                    && let Some(head_loop) = scopes.last().and_then(|scope| scope.loop_head)
                {
                    layout.automatic_break_heads.insert(head, head_loop);
                }
                layout.automatic_abrupt_exits.insert(head, names);
                vec![head]
            }
            // Switches are executed as a unit by the kernel, which retires
            // their own declarations. They still may end an enclosing scope.
            _ => vec![head],
        }
    }
    visit(source, &mut 0, &mut Vec::new(), layout);
    for (at, head) in std::mem::take(&mut layout.automatic_break_heads) {
        let exited = layout
            .automatic_exits
            .get(&head)
            .cloned()
            .unwrap_or_default();
        layout
            .automatic_abrupt_exits
            .entry(at)
            .or_default()
            .extend(exited);
    }
}

#[cfg(test)]
mod source_execution_layout_tests {
    use super::*;

    #[test]
    fn source_statement_exit_includes_aggregate_temporary_retirement() {
        use crate::surface::{ProgramPointKind, SourcePathStep};
        let functions = syntax::parse_functions(
            r#"
            struct box { int32 value; int32 items[1]; };
            struct box make() { struct box out = {0, {7}}; return out; }
            int32 plain() { int32* p = make().items; return 0; }
            int32 conditional(struct box input) { struct box out = 0 ? make() : input; return 0; }
            int32 choose() { switch (make().value) { case 0: break; } return 0; }
        "#,
        )
        .unwrap();
        for function in &functions[1..] {
            let layout = SourceExecutionLayout::for_function(function).unwrap();
            let exit = layout
                .source_path_region(&[SourcePathStep::Statement(0)], ProgramPointKind::Exit)
                .unwrap();
            let next = layout
                .source_path_region(&[SourcePathStep::Statement(1)], ProgramPointKind::Entry)
                .unwrap();
            assert_eq!(
                exit + 1,
                next,
                "{} exits before its lifetime boundary",
                function.name()
            );
            assert_eq!(
                layout.source_path_spelling(exit, ProgramPointKind::Exit),
                Some(vec![SourcePathStep::Statement(0)])
            );
        }
    }

    #[test]
    fn allocation_regions_are_named_for_source_and_typed_execution() {
        let function = syntax::parse_function("void f() { int32* p; p = malloc(4); }").unwrap();
        let typed = function
            .clone()
            .with_prelowered_kernel_function(function.to_kernel_function());
        let source = SourceExecutionLayout::for_function(&function).unwrap();
        let native = SourceExecutionLayout::for_function(&typed).unwrap();
        assert_eq!(source.data.allocation_regions.len(), 1);
        assert_eq!(
            source.data.allocation_regions,
            native.data.allocation_regions
        );
        assert_eq!(source.data.call_results, native.data.call_results);
    }

    #[test]
    fn retained_calls_have_distinct_assignment_points_in_typed_layouts() {
        let function =
            syntax::parse_function("int32 f() { int32 x; x=first(); x=second(); return x; }")
                .unwrap();
        let typed = function
            .clone()
            .with_prelowered_kernel_function(function.to_kernel_function());
        let source = SourceExecutionLayout::for_function(&function).unwrap();
        let native = SourceExecutionLayout::for_function(&typed).unwrap();
        assert_eq!(source.data.call_numbers.len(), 2);
        assert_eq!(native.data.call_numbers, source.data.call_numbers);
        assert_eq!(native.data.step_regions, source.data.step_regions);
        assert_eq!(native.data.call_targets, source.data.call_targets);
        for (occurrence, (region, call)) in native.data.call_numbers.iter().enumerate() {
            assert_eq!(native.step_region(*call), Some(*region));
            assert_eq!(
                native.assignment_entry("x", occurrence).unwrap(),
                region + 1
            );
        }
    }

    #[test]
    fn typed_automatic_scope_exits_match_c_for_nested_and_abrupt_paths() {
        for source in [
            "int32 f(int32 n) {int32 root; root=0; while(root<n) {int32 local; local=1; if(n==2) {int32 child; child=3; return child;} else {local=2;} root=root+1;} return root;}",
            "int32 f(int32 n) {int32 root; root=0; while(root<n) {int32 local; local=1; if(n==2) {int32 child; child=3; continue;} else {break;}} return root;}",
        ] {
            let function = syntax::parse_function(source).unwrap();
            let typed = function
                .clone()
                .with_prelowered_kernel_function(function.to_kernel_function());
            let c = SourceExecutionLayout::for_function(&function).unwrap();
            let native = SourceExecutionLayout::for_function(&typed).unwrap();
            assert!(!native.data.automatic_exits.is_empty());
            assert_eq!(native.data.automatic_exits, c.data.automatic_exits);
            assert_eq!(
                native.data.automatic_abrupt_exits,
                c.data.automatic_abrupt_exits
            );
            assert!(
                native
                    .data
                    .automatic_exits
                    .values()
                    .all(|names| !names.iter().any(|name| name.source_name() == "root"))
            );
        }
    }

    /// An `if` nested as the last statement of another's arm is reached
    /// again through every `if` it closes; each statement must still list
    /// each `if` it completes once, or the lists double with every level.
    #[test]
    fn nested_branch_exits_list_each_enclosing_if_once() {
        let depth = 16;
        let mut source = String::from("int32 f(int32 a) {int32 s; s=0;");
        for _ in 0..depth {
            source.push_str("if(a>0) {");
        }
        source.push_str("s=1;");
        for _ in 0..depth {
            source.push('}');
        }
        source.push_str("return s;}");
        let function = syntax::parse_function(&source).unwrap();
        let typed = function
            .clone()
            .with_prelowered_kernel_function(function.to_kernel_function());
        for function in [&function, &typed] {
            let layout = SourceExecutionLayout::for_function(function).unwrap();
            let lists = &layout.data.exited_branch_regions;
            for (statement, exited) in lists {
                let distinct = exited.iter().collect::<BTreeSet<_>>();
                assert_eq!(
                    distinct.len(),
                    exited.len(),
                    "statement {statement}: {exited:?}"
                );
            }
            let deepest = lists.values().map(Vec::len).max();
            assert_eq!(deepest, Some(depth));
        }
    }

    /// A statement path resolves to the regions the statement as written
    /// produced: a `for` exits at its loop region, not after its step; a
    /// block, which has no region of its own, exits at its last statement;
    /// and a label's body is the label's own statement.
    #[test]
    fn statement_paths_resolve_through_the_statements_as_written() {
        use crate::surface::{ProgramPointKind, SourcePathStep::*};
        let function = syntax::parse_function(
            "int32 f(int32 x) {int32 y = x; for (int32 i = 0; i < x; i = i + 1) { y = y + 1; } { y = y + 2; y = y + 3; } done: return y;}",
        )
        .unwrap();
        let layout = SourceExecutionLayout::for_function(&function).unwrap();
        let region =
            |steps: &[crate::surface::SourcePathStep], kind| layout.source_path_region(steps, kind);
        let (entry, exit) = (ProgramPointKind::Entry, ProgramPointKind::Exit);
        let for_loop = layout.loop_body_entry(0).unwrap() - 1;
        assert_eq!(region(&[Statement(1)], exit), Ok(for_loop));
        assert!(
            region(&[Statement(1)], entry).unwrap() < for_loop,
            "the initializer runs first"
        );
        assert_eq!(
            region(&[Statement(1), Statement(0)], entry),
            region(&[Loop(0), Statement(0)], entry)
        );
        assert_eq!(
            region(&[Statement(2)], exit),
            region(&[Statement(2), Statement(1)], exit)
        );
        assert_eq!(
            region(&[Statement(2)], entry),
            region(&[Statement(2), Statement(0)], entry)
        );
        assert!(region(&[Statement(2), Statement(2)], entry).is_err());
        assert_eq!(
            region(&[Statement(3)], entry),
            Ok(region(&[Statement(2), Statement(1)], exit).unwrap() + 1)
        );
        assert!(
            region(&[Statement(3), Statement(0)], entry).is_err(),
            "a label's body is the label's statement"
        );
        assert!(region(&[Statement(4)], entry).is_err());
        // A point is written by its statement when it is that statement's
        // entry or exit, by the statement's region otherwise, and every
        // spelling names the point it was made for.
        assert_eq!(
            layout.source_path_spelling(for_loop, exit),
            Some(vec![Statement(1)])
        );
        let return_entry = region(&[Statement(3)], entry).unwrap();
        assert_eq!(
            layout.source_path_spelling(return_entry, entry),
            Some(vec![Statement(3)])
        );
        let initializer = region(&[Statement(1)], entry).unwrap();
        assert_eq!(
            layout.source_path_spelling(initializer, exit),
            Some(vec![Statement(1), Region(0)])
        );
        for index in 0..=return_entry {
            for kind in [entry, exit] {
                if let Some(steps) = layout.source_path_spelling(index, kind) {
                    assert_eq!(region(&steps, kind), Ok(index), "{steps:?}");
                }
            }
        }
    }

    #[test]
    fn read_frontiers_index_loads_and_ignore_address_computation() {
        let function = syntax::parse_function(
            "int32 f(int32* p, int32** pp) {int32 x;int32* q; q=&*p; x=*p; q=&**pp; return *p;}",
        )
        .unwrap();
        let typed = function
            .clone()
            .with_prelowered_kernel_function(function.to_kernel_function());
        for function in [&function, &typed] {
            let layout = SourceExecutionLayout::for_function(function).unwrap();
            assert_eq!(layout.data.reads.len(), 3);
            assert!(layout.read_entry(0).unwrap() < layout.read_entry(1).unwrap());
            assert!(layout.read_entry(3).is_err());
        }
        assert!(!expression_reads(&ProgramExpression::AddressOf(Box::new(
            ProgramExpression::Variable("x".into())
        ))));
    }

    #[test]
    fn assignment_frontiers_index_static_stores_in_both_layouts() {
        let function = syntax::parse_function("int32 f(int32 n) { int32 x; x=0; if(n==0) {x=1;} else {x=2;} while(x<3) {x=3;} x+=1; x++; return x; }").unwrap();
        let kernel = function.to_kernel_function();
        let typed = function.clone().with_prelowered_kernel_function(kernel);
        for function in [&function, &typed] {
            let layout = SourceExecutionLayout::for_function(function).unwrap();
            let indices: Vec<_> = (0..6)
                .map(|n| layout.assignment_entry("x", n).unwrap())
                .collect();
            assert!(indices.windows(2).all(|pair| pair[0] < pair[1]));
            assert!(layout.assignment_entry("x", 6).is_err());
            assert!(layout.assignment_entry("absent", 0).is_err());
        }
    }

    #[test]
    fn clones_share_large_immutable_layouts() {
        let statements = (0..4096)
            .map(|index| {
                (
                    index,
                    SourceStatementRegion {
                        continuation_node: index + 1,
                        kind: SourceStatementKind::Plain,
                    },
                )
            })
            .collect();
        let layout = SourceExecutionLayout {
            data: std::sync::Arc::new(SourceExecutionLayoutData {
                parameter_names: BTreeSet::new(),
                statements,
                assignments: BTreeMap::new(),
                reads: Vec::new(),
                automatic_exits: BTreeMap::new(),
                automatic_abrupt_exits: BTreeMap::new(),
                automatic_continue_exits: BTreeMap::new(),
                automatic_break_heads: BTreeMap::new(),
                loop_bodies: BTreeMap::new(),
                loop_updates: BTreeMap::new(),
                loop_test_phases: BTreeMap::new(),
                hidden_loop_tests: BTreeMap::new(),
                natural_loop_targets: BTreeMap::new(),
                natural_exit_targets: BTreeMap::new(),
                natural_exit_statement_indices: BTreeMap::new(),
                exited_branch_regions: BTreeMap::new(),
                arm_lasts_by_exited_region: BTreeMap::new(),
                sites: BTreeMap::new(),
                source_statements: BTreeMap::new(),
                call_targets: BTreeMap::new(),
                call_parameter_objects: Default::default(),
                prepared_parameters: Default::default(),
                prepared_layouts: Default::default(),
                calls: BTreeSet::new(),
                loop_tests: BTreeSet::new(),
                call_numbers: BTreeMap::new(),
                snapshot_step_results: false,
                aggregate_results: BTreeMap::new(),
                full_expression_ends: BTreeSet::new(),
                step_regions: BTreeMap::new(),
                prior_steps: BTreeMap::new(),
                operator_regions: BTreeMap::new(),
                call_results: BTreeMap::new(),
                call_captures: BTreeMap::new(),
                pointee_results: BTreeMap::new(),
                named_calls: None,
                allocation_regions: BTreeSet::new(),
                region_paths: BTreeMap::new(),
                loop_paths: BTreeMap::new(),
                diagnostic_places: std::sync::OnceLock::new(),
                local_pointer_element_types: std::sync::OnceLock::new(),
                loop_region_count: std::sync::OnceLock::new(),
            }),
        };
        let cloned = layout.clone();

        assert!(std::sync::Arc::ptr_eq(&layout.data, &cloned.data));
        assert_eq!(cloned.data.statements.len(), 4096);
        assert_eq!(
            cloned
                .statement(4095)
                .map(|region| region.continuation_node),
            Some(4096)
        );
    }

    fn construction_result_function(
        fields: usize,
        calls: usize,
        unrelated: usize,
    ) -> crate::languages::interface::ImportedFunction {
        use crate::kernel::*;
        let layout = AggregateLayout::new(
            (fields * 8) as u32,
            8,
            (0..fields)
                .map(|i| {
                    AggregateField::new(
                        format!("nested.field_{i}"),
                        (i * 8) as u32,
                        ProgramType::UInt64,
                    )
                })
                .collect(),
        );
        let mut body = program_allocate_aggregate_destination("built", layout);
        for i in 0..unrelated {
            body = program_seq(
                body,
                program_declare(format!("other_{i}"), ProgramType::Int32),
            );
        }
        for _ in 0..calls {
            body = program_seq(body, program_call_construct("built", "factory", vec![]));
        }
        body = program_seq(
            body,
            program_return(crate::kernel::program_expression::int32_literal(0)),
        );
        syntax::parse_function("int32 source() { return 0; }")
            .unwrap()
            .with_prelowered_kernel_function(program_function(
                ProgramType::Int32,
                "source",
                vec![],
                body,
            ))
    }

    fn record_parameter_return_function(
        parameters: usize,
        construction: bool,
    ) -> crate::languages::interface::ImportedFunction {
        use crate::kernel::*;
        let record = AggregateLayout::new(
            8,
            8,
            vec![AggregateField::new("value", 0, ProgramType::UInt64)],
        );
        let arguments = (0..parameters)
            .map(|index| {
                program_parameter_with_aggregate_layout(
                    format!("arg_{index}"),
                    ProgramType::VoidPointer,
                    record.clone(),
                )
            })
            .chain([program_parameter("raw", ProgramType::Int32Pointer)])
            .collect();
        let body = program_seq(
            ProgramStatement::Goto {
                target: ControlTargetId(1),
                exited_locals: Default::default(),
            },
            program_return(crate::kernel::program_expression::variable(CONTRACT_RESULT)),
        );
        let function = program_function(ProgramType::VoidPointer, "source", arguments, body);
        let function = if construction {
            function.with_construction_return(record)
        } else {
            function.with_return_aggregate_layout(record)
        };
        syntax::parse_function("void* source() { return 0; }")
            .unwrap()
            .with_prelowered_kernel_function(function)
    }

    #[test]
    fn construction_returns_retire_record_parameters_but_copy_returns_and_gotos_do_not() {
        for construction in [false, true] {
            let function = record_parameter_return_function(2, construction);
            let layout = SourceExecutionLayout::for_function(&function).unwrap();
            assert!(
                layout.automatic_exits(0, true).is_empty(),
                "a goto stays in the function"
            );
            let retired = layout.automatic_exits(1, true);
            if construction {
                assert_eq!(retired, &["arg_0".into(), "arg_1".into()]);
            } else {
                assert!(
                    retired.is_empty(),
                    "a copied return may still read its source parameter"
                );
            }
        }
    }

    #[test]
    fn construction_call_results_keep_nested_field_names_and_share_layouts() {
        let function = construction_result_function(4, 2, 0);
        let layout = SourceExecutionLayout::for_function(&function).unwrap();
        assert!(!layout.is_aggregate_result(0));
        for region in [1, 2] {
            assert!(layout.is_aggregate_result(region));
            let field = layout
                .aggregate_result_field(region, "nested.field_3")
                .unwrap();
            assert_eq!(field.offset_bytes(), 24);
            assert_eq!(field.program_type(), crate::kernel::ProgramType::UInt64);
            assert!(
                layout
                    .aggregate_result_field(region, "nested.missing")
                    .is_none()
            );
        }
        assert!(std::sync::Arc::ptr_eq(
            &layout.data.aggregate_results[&1],
            &layout.data.aggregate_results[&2]
        ));
    }

    #[cfg(test)]
    mod scaling_tests {
        include!(
            "../../scaling_tests/surface/lowering/source_layout/source_execution_layout_tests.rs"
        );
    }
}

#[cfg(test)]
mod shared_loop_scope_scaling_tests {
    use super::*;
    include!("../../scaling_tests/surface/lowering/source_layout/shared_loop_scopes.rs");
}

#[cfg(test)]
mod loop_phase_source_tests {
    use super::*;

    #[test]
    fn pure_test_regions_follow_written_numbers_and_own_their_footprints() {
        let function =
            syntax::parse_function("int32 f(int32 n) { while (n > 0) { n = n - 1; } return n; }")
                .unwrap();
        let typed = function
            .clone()
            .with_prelowered_kernel_function(function.to_kernel_function());
        for function in [&function, &typed] {
            let layout = SourceExecutionLayout::for_function(function).unwrap();
            assert_eq!(layout.loop_body_entry(0), Some(1));
            assert!(matches!(
                layout.statement(0).unwrap().kind,
                SourceStatementKind::Loop { loop_index: 0 }
            ));
            assert!(matches!(
                layout.statement(2).unwrap().kind,
                SourceStatementKind::Plain
            ));
            let test = layout.loop_test_phase_entry(0).unwrap();
            assert!(
                test > 3,
                "the test must not overwrite source statements or their end boundary"
            );
            assert!(layout.is_hidden_loop_test(test));
            if function.prelowered_kernel_function().is_none() {
                use crate::surface::{ProgramPointKind, SourcePathStep};
                assert_eq!(
                    layout.source_path_region(&[SourcePathStep::Loop(0)], ProgramPointKind::Exit),
                    Ok(0),
                );
                assert_eq!(
                    layout.source_path_region(
                        &[SourcePathStep::Loop(0), SourcePathStep::Test],
                        ProgramPointKind::Exit,
                    ),
                    Ok(test),
                );
            }
            assert_eq!(layout.statement(test).unwrap().continuation_node, 1);
            assert_ne!(
                test, 0,
                "test effects must not be labelled as whole-loop effects"
            );
        }
    }
    #[test]
    fn nested_post_test_successors_reach_the_innermost_pending_phase() {
        let function = syntax::parse_function(
            "int32 f(int32 n) { do { do { n = 0; } while(n > 0); } while(n > 0); return n; }",
        )
        .unwrap();
        let typed = function
            .clone()
            .with_prelowered_kernel_function(function.to_kernel_function());
        for function in [&function, &typed] {
            let layout = SourceExecutionLayout::for_function(function).unwrap();
            let outer = layout.loop_test_phase_entry(0).unwrap();
            let inner = layout.loop_test_phase_entry(1).unwrap();
            assert_eq!(layout.statement(2).unwrap().continuation_node, inner);
            assert_eq!(layout.statement(1).unwrap().continuation_node, outer);
            assert_eq!(layout.statement(0).unwrap().continuation_node, 3);
            assert_eq!(layout.statement(inner).unwrap().continuation_node, 1);
            assert_eq!(layout.statement(outer).unwrap().continuation_node, 0);
        }
    }
    #[test]
    fn a_post_test_routes_its_body_without_redirecting_a_sibling_branch() {
        let function = syntax::parse_function("int32 f(int32 n) { if(n > 0) { do { n = 0; } while(n > 0); } else { n = 1; } return n; }").unwrap();
        let typed = function
            .clone()
            .with_prelowered_kernel_function(function.to_kernel_function());
        for function in [&function, &typed] {
            let layout = SourceExecutionLayout::for_function(function).unwrap();
            let test = layout.loop_test_phase_entry(0).unwrap();
            assert_eq!(layout.statement(2).unwrap().continuation_node, test);
            assert_eq!(layout.statement(1).unwrap().continuation_node, 4);
            assert_eq!(layout.statement(3).unwrap().continuation_node, 4);
        }
    }
}
