//! Compiler drop CFGs emit shared joins and supported natural while loops once.
//! The MIR is drop-elaborated: rustc has already decided every move and drop,
//! so a move copies the fields and a drop runs the destructor, with no state
//! of the lowering's own recording which values are live.
use super::*;
mod flow;
use crate::languages::rust::names::RustDestructor;
use crate::languages::rust::schema::{Destructor, MirBody, MirStatement as S, MirTerminator as T};

/// A lowered statement and the source statement each of its regions comes
/// from (`Function::sites`), in the order the source layout numbers its
/// regions: a statement before the statements it contains. A region the
/// lowering adds with no source statement of its own has none.
#[derive(Clone)]
pub(super) struct Sited {
    pub(super) statement: ProgramStatement,
    pub(super) sites: Vec<Option<u32>>,
    /// The call region of each MIR block participating in an object binding.
    pub(super) binding_calls: Vec<(usize, usize)>,
}

impl Sited {
    /// `statement`, every region of which comes from `site`.
    fn at(site: Option<u32>, statement: ProgramStatement) -> Self {
        let sites = vec![site; region_count(&statement)];
        Self {
            statement,
            sites,
            binding_calls: Vec::new(),
        }
    }

    fn unsited(statement: ProgramStatement) -> Self {
        Self::at(None, statement)
    }

    /// `self`, then `next`: `program_seq(self, next)`.
    fn then(mut self, next: Sited) -> Self {
        let offset = self.sites.len();
        self.binding_calls
            .extend(offset_calls(next.binding_calls, offset));
        self.sites.extend(next.sites);
        Self {
            statement: program_seq(self.statement, next.statement),
            sites: self.sites,
            binding_calls: self.binding_calls,
        }
    }

    /// `program_if(condition, then, otherwise)`, whose test comes from `site`.
    fn branch(
        site: Option<u32>,
        condition: ProgramExpression,
        then: Sited,
        otherwise: Sited,
    ) -> Self {
        let mut sites = vec![site];
        let binding_calls = offset_calls(then.binding_calls, 1)
            .chain(offset_calls(otherwise.binding_calls, 1 + then.sites.len()))
            .collect();
        sites.extend(then.sites);
        sites.extend(otherwise.sites);
        Self {
            statement: program_if(condition, then.statement, otherwise.statement),
            sites,
            binding_calls,
        }
    }

    /// `program_while(condition, [], body)`, a loop that comes from `site`.
    fn looping(site: Option<u32>, condition: ProgramExpression, body: Sited) -> Self {
        let mut sites = vec![site];
        sites.extend(body.sites);
        Self {
            statement: program_while(condition, Vec::new(), body.statement),
            sites,
            binding_calls: offset_calls(body.binding_calls, 1).collect(),
        }
    }
}

fn offset_calls(calls: Vec<(usize, usize)>, offset: usize) -> impl Iterator<Item = (usize, usize)> {
    calls
        .into_iter()
        .map(move |(block, region)| (block, region + offset))
}

/// How many regions the source layout numbers in `statement`: one for each
/// `if`, loop and `try` and each statement that is none of these or a
/// sequence, which numbers its statements' regions in order.
pub(super) fn region_count(statement: &ProgramStatement) -> usize {
    match statement {
        ProgramStatement::Seq(statements) => statements.iter().map(|s| region_count(s)).sum(),
        ProgramStatement::If {
            then_branch,
            else_branch,
            ..
        } => 1 + region_count(then_branch) + region_count(else_branch),
        ProgramStatement::Loop {
            test: loop_test,
            update,
            body,
            ..
        } => {
            let test = loop_test.source_region();
            1 + region_count(body)
                + test
                    .as_ref()
                    .map_or(0, |test| region_count(&test.statement))
                + update.as_ref().map_or(0, |update| region_count(update))
        }
        ProgramStatement::TryCatchInt32 {
            try_body, handler, ..
        } => 1 + region_count(try_body) + region_count(handler),
        // Its cleanup, then the point where the exception continues.
        ProgramStatement::UnwindCleanup { body, cleanup } => {
            1 + region_count(body) + region_count(cleanup) + 1
        }
        _ => 1,
    }
}

pub(super) fn lower(
    cx: &mut Context<'_>,
    f: &Function,
    mir: &MirBody,
    owner: &LocalFunctionId,
) -> Result<Sited, String> {
    if mir.blocks.is_empty() {
        return Err("MIR body has no entry block".into());
    }
    let flow = flow::Flow::analyze(f, mir)?;
    // Loop reconstruction can evaluate its test before the header statements.
    // Ordinary branches run immediately after their block's statements.
    let loop_tests = flow.loops.values().map(|loop_| loop_.test).collect();
    let local_types: BTreeMap<_, _> = f
        .parameters
        .iter()
        .chain(&mir.locals)
        .map(|local| (&local.name, &local.value_type))
        .collect();
    for (name, last_use) in super::super::charon::scalar_expression_operands(mir, &loop_tests) {
        cx.scalar_operands
            .insert(name, (cx.result_step(), last_use));
    }
    // Index storage starts once. Locals without a compiler storage event
    // retain their function-entry backing (including return-place arrays).
    let storage_starts: BTreeSet<&MirLocalId> = mir
        .blocks
        .iter()
        .flat_map(|block| &block.statements)
        .filter_map(|statement| match statement {
            S::BeginStorage { local } => Some(local),
            _ => None,
        })
        .collect();
    // The locals the body borrows, `_5 = &mut o`.
    // The locals a borrow names: a borrow is a statement's value, or a call's
    // argument, `f(&mut x)`.
    let borrowed: BTreeSet<&MirLocalId> = mir
        .blocks
        .iter()
        .flat_map(|block| {
            let arguments = match &block.terminator {
                T::Call { arguments, .. } => arguments.as_slice(),
                _ => &[],
            };
            block
                .statements
                .iter()
                .filter_map(|statement| match statement {
                    S::Assign { value, .. } => Some(value),
                    _ => None,
                })
                .chain(arguments)
        })
        .filter_map(|value| match value {
            E::Borrow { place, .. } => match place.as_ref() {
                E::Local { name } => Some(name),
                _ => None,
            },
            _ => None,
        })
        .collect();
    let drop_operands = super::super::charon::moved_drop_operands(mir);
    for (&local, &site) in &drop_operands {
        cx.bindings.insert(
            local.to_owned(),
            LocalBindingId::prepared_argument(owner.clone(), site).into(),
        );
    }
    let mut records = BTreeMap::new();
    let mut declarations = program_skip();
    // The declarations of the locals `Context::bindings` spells, which run
    // where their storage starts.
    let mut scoped = BTreeMap::new();
    let owned_parameter_count = f
        .parameters
        .iter()
        .filter(|p| matches!(p.value_type, Type::Record { .. }))
        .count();
    for (index, local) in f
        .parameters
        .iter()
        .filter(|p| matches!(p.value_type, Type::Record { .. }))
        .chain(mir.locals.iter())
        .enumerate()
    {
        let parameter = index < owned_parameter_count;
        if cx.scalar_operands.contains_key(&local.name) {
            continue;
        }
        if let Type::SharedArrayIterator { element } | Type::SharedArrayOption { element } =
            &local.value_type
        {
            declarations = program_seq(
                declarations,
                cx.shared_array_storage(
                    &local.name,
                    element,
                    matches!(local.value_type, Type::SharedArrayOption { .. }),
                    owner,
                    u32::try_from(index - owned_parameter_count)
                        .map_err(|_| "MIR local index exceeds u32")?,
                )?,
            );
            continue;
        }
        if let Type::EnumerateIterator { element } | Type::EnumerateOption { element } =
            &local.value_type
        {
            let ordinal = u32::try_from(index - owned_parameter_count)
                .map_err(|_| "MIR local index exceeds u32")?;
            declarations = program_seq(
                declarations,
                cx.enumerate_storage(
                    &local.name,
                    element,
                    matches!(local.value_type, Type::EnumerateOption { .. }),
                    owner,
                    ordinal,
                )?,
            );
            continue;
        }
        if let Type::Range { element, inclusive } = &local.value_type {
            declarations = program_seq(
                declarations,
                cx.range_storage(
                    &local.name,
                    element,
                    *inclusive,
                    owner,
                    u32::try_from(index - owned_parameter_count)
                        .map_err(|_| "MIR local index exceeds u32")?,
                )?,
            );
            continue;
        }
        if matches!(local.value_type, Type::ChunkIterator | Type::ChunkOption) {
            declarations = program_seq(
                declarations,
                cx.chunk_storage(
                    &local.name,
                    local.value_type == Type::ChunkOption,
                    owner,
                    u32::try_from(index - owned_parameter_count)
                        .map_err(|_| "MIR local index exceeds u32")?,
                )?,
            );
            continue;
        }
        if !parameter && !cx.locals.insert(local.name.clone()) {
            return Err("duplicate MIR local identity".into());
        }
        if let Type::Reference { mutable, .. } = &local.value_type {
            cx.references.insert(local.name.clone(), !mutable);
        }
        let statement = match &local.value_type {
            Type::Unit => program_skip(),
            Type::Reference { .. } if iterator_reference(&local.value_type) => program_skip(),
            _ if local.name.source_name().is_none() && !cx.bindings.contains_key(&local.name) => {
                return Err(format!(
                    "{}:{}:{}: unsupported Rust construct: an unnamed compiler local requires storage with no supported identity",
                    cx.source, local.span.line, local.span.column
                ));
            }
            Type::Record { name } => {
                cx.owned_locals.insert(local.name.clone());
                records.insert(&local.name, name.as_str());
                if parameter {
                    continue;
                }
                // Construction grants authority over fresh stack bytes;
                // source reads cannot observe the kernel's fresh placeholders,
                // since rustc reads no field before it is written.
                if !drop_operands.contains_key(&local.name)
                    && storage_starts.contains(&local.name)
                    && check_copyable(cx, name).is_ok()
                {
                    program_skip()
                } else {
                    program_begin_aggregate_construction(
                        cx.binding(&local.name)?,
                        cx.layouts
                            .get(name.as_str())
                            .ok_or("missing owned record layout")?
                            .to_kernel_aggregate_layout(),
                    )
                }
            }
            Type::ScalarSlice { element, mutable } => {
                let element_type = scalar_type(element)?.to_kernel_type();
                let pointer_type = scalar_type(&Type::Reference {
                    mutable: *mutable,
                    pointee: element.clone(),
                })?
                .to_kernel_type();
                let length = cx.declare_slice_length(&local.name)?;
                cx.shared_scalar_slices
                    .insert(local.name.clone(), (length.clone(), element_type));
                program_seq(
                    program_declare_with_all_qualifiers(
                        cx.binding(&local.name)?,
                        pointer_type,
                        false,
                        false,
                        false,
                        !mutable,
                    ),
                    program_declare(length, ProgramType::UInt64),
                )
            }
            Type::ByteSlice { mutable } => {
                let length = cx.declare_slice_length(&local.name)?;
                cx.slices
                    .insert(local.name.clone(), (length.clone(), !mutable));
                program_seq(
                    program_declare_with_all_qualifiers(
                        cx.binding(&local.name)?,
                        ProgramType::UInt8Pointer,
                        false,
                        false,
                        false,
                        !mutable,
                    ),
                    program_declare(length, ProgramType::UInt64),
                )
            }
            Type::Reference { mutable, pointee }
                if matches!(pointee.as_ref(), Type::Array { .. }) =>
            {
                let Type::Array { element, length } = pointee.as_ref() else {
                    unreachable!()
                };
                let element = scalar_type(element)?.to_kernel_type();
                cx.arrays
                    .insert(local.name.clone(), (*length, element, !mutable));
                program_declare_with_all_qualifiers(
                    cx.binding(&local.name)?,
                    scalar_type(&local.value_type)?.to_kernel_type(),
                    false,
                    false,
                    false,
                    !mutable,
                )
            }
            Type::Array { element, length } => {
                let element = scalar_type(element)?.to_kernel_type();
                if !matches!(
                    element,
                    ProgramType::Int32 | ProgramType::UInt8 | ProgramType::UInt32
                ) || *length > i32::MAX as u64 / u64::from(element.byte_width())
                {
                    return Err(
                        "compact arrays require i32/u8/u32 elements and signed-word storage".into(),
                    );
                }
                cx.local_arrays.insert(local.name.clone());
                cx.arrays
                    .insert(local.name.clone(), (*length, element, false));
                if storage_starts.contains(&local.name) {
                    program_skip()
                } else {
                    program_begin_aggregate_construction(
                        cx.binding(&local.name)?,
                        AggregateLayout::new(
                            *length as u32 * element.byte_width(),
                            element.byte_width(),
                            vec![],
                        ),
                    )
                }
            }
            Type::Reference { mutable, .. } => program_declare_with_all_qualifiers(
                cx.binding(&local.name)?,
                scalar_type(&local.value_type)?.to_kernel_type(),
                false,
                false,
                false,
                !mutable,
            ),
            // A borrowed enum or type-parameter local keeps its value in its
            // object's memory, where a write through the borrow lands.
            t @ (Type::Enum { .. } | Type::Parameter { .. } | Type::Vec { .. })
                if borrowed.contains(&local.name) =>
            {
                let value_type = scalar_type(t)?.to_kernel_type();
                cx.memory_values.insert(local.name.clone(), value_type);
                program_begin_aggregate_construction(
                    cx.binding(&local.name)?,
                    AggregateLayout::holding_value(value_type),
                )
            }
            t => {
                // An integer or `bool` local is a stack object `&mut` can
                // borrow by its address. An enum's or a type parameter's
                // value lives in its local's binding, with no bytes a
                // callee could write through a borrow, so neither is
                // borrowed.
                if t.is_scalar() {
                    cx.addressable_locals.insert(local.name.clone());
                }
                program_declare(cx.binding(&local.name)?, scalar_type(t)?.to_kernel_type())
            }
        };
        if cx.bindings.contains_key(&local.name)
            && (drop_operands.contains_key(&local.name)
                || !matches!(local.value_type, Type::Record { .. } | Type::Array { .. }))
            && storage_starts.contains(&local.name)
        {
            scoped.insert(local.name.clone(), statement);
        } else {
            declarations = program_seq(declarations, statement);
        }
    }
    let mut escape_flags = BTreeMap::new();
    for (header, loop_) in &flow.loops {
        if loop_.escapes.is_empty() {
            continue;
        }
        let ordinal = u32::try_from(*header).map_err(|_| "MIR loop header index exceeds u32")?;
        let flag = BindingName::from(LocalBindingId::loop_escape(owner.clone(), ordinal));
        declarations = program_seq(
            declarations,
            program_declare(flag.clone(), ProgramType::Int32),
        );
        escape_flags.insert(*header, flag);
    }
    let binding_blocks = mir
        .object_bindings
        .iter()
        .flat_map(|binding| [binding.call, binding.acquire, binding.release])
        .collect::<BTreeSet<_>>();
    let mut nodes = vec![None; mir.blocks.len()];
    let check = |local: &MirLocalId, record: &str| -> Result<(), String> {
        if records.get(local).copied() != Some(record) {
            return Err("owned MIR place disagrees with record type".into());
        }
        Ok(())
    };
    for &block in &flow.order {
        let terminator = &mir.blocks[block].terminator;
        cx.mir_point = matches!(
            terminator,
            T::ReturnValue { .. }
                | T::BoxFree { .. }
                | T::Call {
                    function: MirCallee::Direct(_) | MirCallee::Binding { .. },
                    ..
                }
        )
        .then_some(super::super::borrow_frontiers::MirPoint {
            block,
            statement: mir.blocks[block].statements.len(),
        });
        cx.mir_nodes.clear();
        let mut binding_call = None;
        let terminal = match terminator {
            T::Goto { .. } | T::If { .. } | T::Switch { .. } => program_skip(),
            T::Return => {
                if f.return_type == Type::Unit {
                    program_return(program_void_value())
                } else {
                    if let Type::Record { name } = &f.return_type {
                        check(&mir.return_place, name)?;
                    }
                    program_return(crate::kernel::program_expression::variable(
                        cx.binding(&mir.return_place)?,
                    ))
                }
            }
            // The value MIR wrote to its return place, returned as written.
            T::ReturnValue { value } => {
                let (checks, value) = cx.prepared_expr(value)?;
                let return_type = scalar_type(&f.return_type)?.to_kernel_type();
                program_seq(
                    checks,
                    program_return(crate::kernel::program_expression::cast(value, return_type)),
                )
            }
            T::Unreachable => program_assert(crate::kernel::program_expression::int32_literal(0)),
            T::Panic { message } => program_labeled_assert(
                crate::kernel::program_expression::int32_literal(0),
                format!("Rust panic `{message}`"),
            ),
            // A non-null box's record is dropped through its glue before the
            // library's `Box::drop`, `if (box) { glue(box); drop(box); }`.
            T::BoxFree {
                local,
                record,
                drop_contents,
                optional,
                ..
            } => {
                // The library's `Box::drop<R>` frees the allocation, after
                // the record's glue; a `None` box, null, drops nothing.
                let boxed = cx.expr(&E::Local {
                    name: local.clone(),
                })?;
                let free = program_call(
                    super::super::standard_library::box_function(
                        super::super::standard_library::BOX_DROP,
                        record,
                    ),
                    vec![boxed.clone()],
                );
                let drop = if *drop_contents {
                    let destructor = RustDestructor {
                        record: record.clone(),
                    }
                    .contract_name();
                    if !cx.functions.contains_key(destructor.as_str()) {
                        return Err(
                            "box contents' destructor missing from prepared Rust input".into()
                        );
                    }
                    program_seq(
                        program_call(destructor, vec![observe_operand(boxed.clone())]),
                        free,
                    )
                } else {
                    free
                };
                if *optional {
                    // The free ends the capture on the non-null path.
                    // A null box must end it without invoking drop.
                    let none = if matches!(&boxed, ProgramExpression::StepResult { ends: true, .. })
                    {
                        typed_value_step(
                            Vec::new(),
                            boxed.clone(),
                            ProgramType::Int32Pointer,
                            false,
                        )
                    } else {
                        program_skip()
                    };
                    crate::kernel::program_if(observe_operand(boxed), drop, none)
                } else {
                    drop
                }
            }
            T::Drop { local, record, .. } => {
                check(local, record)?;
                let r = cx.records.get(record.as_str()).ok_or("unknown drop type")?;

                if let Some(destructor) = &r.destructor {
                    let name = match destructor {
                        Destructor::Implicit => RustDestructor {
                            record: record.clone(),
                        }
                        .contract_name(),
                        Destructor::Explicit(name) => name.clone(),
                    };
                    if !cx.functions.contains_key(name.as_str()) {
                        return Err("destructor body missing from prepared Rust input".into());
                    }
                    program_call(
                        name,
                        vec![crate::kernel::program_expression::cast(
                            crate::kernel::program_expression::variable(cx.binding(local)?),
                            ProgramType::Int32Pointer,
                        )],
                    )
                } else {
                    program_skip()
                }
            }
            T::Call {
                function: MirCallee::Binding { binding },
                arguments,
                ..
            } => {
                use crate::kernel::{ReferenceBindingContract, ReferenceBindingOperation};
                let object = Type::Reference {
                    mutable: false,
                    pointee: Box::new(Type::Record {
                        name: binding.conversion.record.clone(),
                    }),
                };
                let (prefix, arguments) = cx.typed_arguments(vec![object], arguments)?;
                // Keep the same region boundaries as other direct MIR calls.
                let prefix = program_seq(prefix, program_skip());
                binding_call = Some((block, region_count(&prefix)));
                program_seq(
                    prefix,
                    ProgramStatement::Call {
                        function_name: String::new(),
                        arguments,
                        callee: None,
                        dispatch: crate::kernel::CallDispatch::Direct,
                        reference_binding: Some(std::sync::Arc::new(ReferenceBindingOperation {
                            contract: ReferenceBindingContract::Rust(binding.clone()),
                            source: None,
                        })),
                    },
                )
            }
            T::Call {
                function: MirCallee::Pointer { local },
                arguments,
                destination,
                result: result_step,
                owned_arguments,
                ..
            } => {
                // The pointer's own type gives the arguments and result.
                let Some(Type::FnPointer { parameters, result }) = local_types.get(local).copied()
                else {
                    return Err("Rust pointer call target is not a function-pointer local".into());
                };
                if !owned_arguments.is_empty() {
                    return Err("Rust pointer call carries owned-argument metadata".into());
                }
                let function = local
                    .source_name()
                    .ok_or("unsupported Rust construct: unnamed function pointer call")?;
                let (prefix, arguments_values) =
                    cx.typed_arguments(parameters.clone(), arguments)?;
                let call = if **result == Type::Unit {
                    program_call(function, arguments_values)
                } else if let Some(step) = result_step {
                    crate::kernel::program_call_value(*step, function, arguments_values).0
                } else {
                    let destination = destination
                        .as_ref()
                        .ok_or("missing Rust pointer call destination")?;
                    cx.call_then_assign(destination, function, arguments_values)?
                };
                program_seq(prefix, call)
            }
            T::Call {
                function: MirCallee::Direct(function),
                arguments,
                owned_arguments,
                destination,
                result,
                ..
            } => {
                let callee = cx
                    .functions
                    .get(function.as_str())
                    .ok_or("missing MIR call definition")?;
                let (prefix, mut arguments_values) = cx.prepared_arguments(function, arguments)?;
                let mut indices = BTreeSet::new();
                let mut moved_results = Vec::new();
                let mut previous_index = None;
                let mut aggregate_steps = Vec::new();
                for argument in owned_arguments {
                    if previous_index.is_some_and(|previous| previous >= argument.index)
                        || !indices.insert(argument.index)
                        || callee.parameters.get(argument.index).map(|p| &p.value_type)
                            != Some(&Type::Record {
                                name: argument.record.clone(),
                            })
                    {
                        return Err("owned call metadata disagrees with callee and operands".into());
                    }
                    previous_index = Some(argument.index);
                    match (arguments.get(argument.index), &argument.local) {
                        (Some(E::Local { name }), Some(local)) if name == local => {
                            check(local, &argument.record)?;
                            if !argument.moved {
                                check_copyable(cx, &argument.record)?;
                            }
                            // A drop operand is already the call's prepared
                            // object; any other local is copied into one.
                            if !cx
                                .binding(local)?
                                .local_id()
                                .is_some_and(LocalBindingId::is_prepared_argument)
                            {
                                moved_results.push((argument.index, argument.record.clone()));
                            }
                        }
                        (
                            Some(E::CallResult {
                                call,
                                function: MirCallee::Direct(function),
                                keeps: false,
                            }),
                            None,
                        ) if argument.moved
                            && cx
                                .functions
                                .get(function.as_str())
                                .map(|producer| &producer.return_type)
                                == Some(&Type::Record {
                                    name: argument.record.clone(),
                                }) =>
                        {
                            aggregate_steps.push(*call);
                            moved_results.push((argument.index, argument.record.clone()));
                        }
                        _ => return Err("owned call metadata disagrees with operand".into()),
                    }
                }
                if callee.parameters.iter().enumerate().any(|(index, p)| {
                    matches!(p.value_type, Type::Record { .. }) && !indices.contains(&index)
                }) {
                    return Err("owned call operand lacks transfer metadata".into());
                }
                // A by-value record argument that is not already the call's
                // prepared object (a call result, or a local other than a drop
                // operand) is copied into one, a region of its own before the
                // call, so the call receives the initialized object, as Rust
                // moves or copies it.
                let mut binding = program_skip();
                let mut prepared = Vec::new();
                for (index, record) in moved_results {
                    let layout = cx
                        .layouts
                        .get(record.as_str())
                        .ok_or("missing moved record layout")?
                        .to_kernel_aggregate_layout();
                    // Prepared objects made here are numbered from the top of
                    // the ordinal range, by block and argument, apart from the
                    // drop operands numbered by their MIR sites.
                    let ordinal = u32::try_from(block)
                        .ok()
                        .and_then(|block| block.checked_mul(64))
                        .and_then(|base| base.checked_add(u32::try_from(index).ok()?))
                        .filter(|_| index < 64)
                        .map(|key| u32::MAX - key)
                        .ok_or("too many Rust call blocks or arguments")?;
                    let id = match &callee.parameters[index].name {
                        MirLocalId::Source(parameter) => {
                            LocalBindingId::prepared_argument_for(owner.clone(), ordinal, parameter)
                        }
                        _ => LocalBindingId::prepared_argument(owner.clone(), ordinal),
                    };
                    id.initialize_struct_name(&record);
                    let object = BindingName::from(id);
                    binding = program_seq(
                        binding,
                        program_seq(
                            crate::kernel::program_allocate_aggregate_destination(
                                object.clone(),
                                layout.clone(),
                            ),
                            crate::kernel::program_copy_aggregate(
                                crate::kernel::program_expression::variable(object.clone()),
                                arguments_values[index].clone(),
                                layout,
                            ),
                        ),
                    );
                    arguments_values[index] = crate::kernel::program_expression::cast(
                        crate::kernel::program_expression::variable(object.clone()),
                        ProgramType::UInt8Pointer,
                    );
                    prepared.push(object);
                }
                let prefix = program_seq(prefix, binding);
                if binding_blocks.contains(&block) {
                    binding_call = Some((block, region_count(&prefix)));
                }
                let call = if let Some(step) = result {
                    // A call step: its successor reads the result as the
                    // value of the expression that holds the call.
                    let aggregate_layout = if let Type::Record { name } = &callee.return_type {
                        check_copyable(cx, name)?;
                        Some(
                            cx.layouts
                                .get(name.as_str())
                                .ok_or("missing returned record layout")?
                                .to_kernel_aggregate_layout(),
                        )
                    } else {
                        None
                    };
                    ProgramStatement::CallResult {
                        aggregate_layout: aggregate_layout.clone().map(|layout| {
                            crate::kernel::AggregateResultLayout {
                                layout,
                                declared_class: None,
                            }
                        }),
                        call: *step,
                        function_name: function.clone(),
                        arguments: arguments_values,
                        result_type: scalar_type(&callee.return_type)
                            .ok()
                            .map(|scalar| scalar.to_kernel_type()),
                        result_aggregate_layout: aggregate_layout,
                        result_pointee_constant: false,
                        dispatch: crate::kernel::CallDispatch::Direct,
                        callee: None,
                    }
                } else if callee.return_type == Type::Unit
                    || (destination.is_none() && callee.return_type.is_scalar())
                {
                    program_call(function, arguments_values)
                } else if let Some(destination) = destination {
                    if let Type::Record { name } = &callee.return_type {
                        check(destination, name)?;
                        let layout = cx
                            .layouts
                            .get(name.as_str())
                            .ok_or("missing returned record layout")?
                            .to_kernel_aggregate_layout();
                        let (call, result) = cx.call_value(function, arguments_values);
                        let copy = crate::kernel::program_copy_aggregate(
                            crate::kernel::program_expression::variable(cx.binding(destination)?),
                            result,
                            layout,
                        );
                        program_seq(call, copy)
                    } else if let Some(&value_type) = cx.memory_values.get(destination) {
                        let (call, result) = cx.call_value(function, arguments_values);
                        let address = cx.address(&E::Local {
                            name: destination.clone(),
                        })?;
                        program_seq(call, program_typed_store(address, result, value_type))
                    } else {
                        cx.call_then_assign(destination, function, arguments_values)?
                    }
                } else {
                    return Err("missing Rust call destination for a non-scalar result".into());
                };
                let call = if aggregate_steps.is_empty() && prepared.is_empty() {
                    call
                } else {
                    program_seq(
                        call,
                        ProgramStatement::EndAutomaticLifetimes {
                            names: prepared,
                            steps: aggregate_steps,
                        },
                    )
                };
                program_seq(prefix, call)
            }
        };
        cx.mir_point = None;
        // The source statement the block's statements come from, as its
        // `Site` statements name it.
        let mut site = None;
        let mut statements = Sited::unsited(program_skip());
        for (statement_index, s) in mir.blocks[block].statements.iter().enumerate() {
            cx.mir_point = Some(super::super::borrow_frontiers::MirPoint {
                block,
                statement: statement_index,
            });
            cx.mir_nodes = if cx.import_identity.is_some() {
                super::super::borrow_frontiers::mir_expression_nodes(s)
            } else {
                BTreeMap::new()
            };
            let statement = match s {
                S::Site { site: next } => {
                    site = Some(*next);
                    continue;
                }
                S::Assert { condition, message } => {
                    let (checks, condition) = cx.prepared_expr(condition)?;
                    program_seq(
                        checks,
                        program_labeled_assert(
                            branch_condition(condition),
                            format!("Rust panic `{message}`"),
                        ),
                    )
                }
                S::SliceSplit {
                    slice,
                    midpoint,
                    left,
                    right,
                } => {
                    let slot = |name: &MirLocalId| super::super::schema::Place {
                        name: name.clone(),
                        value_type: Type::ByteSlice { mutable: false },
                        span: super::super::schema::Span { line: 0, column: 0 },
                    };
                    cx.slice_split_slots(slice, midpoint, &slot(left), &slot(right), false)?
                }
                S::SharedArrayInitialize { target, source } => {
                    cx.shared_array_initialize(target, source)?
                }
                S::SharedArrayMove { target, source } => cx.shared_array_move(target, source)?,
                S::SharedArrayNext {
                    iterator,
                    option,
                    payload,
                    taken,
                } => {
                    let payload = payload
                        .as_ref()
                        .map(|name| {
                            local_types
                                .get(name)
                                .map(|ty| (name, *ty))
                                .ok_or("unknown Rust slice iterator payload")
                        })
                        .transpose()?;
                    cx.shared_array_next(iterator, option.as_ref(), payload, *taken)?
                }
                S::ChunkInitialize {
                    target,
                    slice,
                    size,
                } => cx.chunk_initialize_mir(target, slice, size)?,
                S::ChunkMove { target, source } => cx.chunk_move(target, source)?,
                S::EnumerateInitialize { target, source } => {
                    cx.enumerate_initialize(target, source)?
                }
                S::EnumerateMove { target, source } => cx.enumerate_move(target, source)?,
                S::EnumerateNext {
                    iterator,
                    option,
                    index,
                    element,
                    taken,
                } => {
                    let element = element
                        .as_ref()
                        .map(|name| {
                            local_types
                                .get(name)
                                .map(|ty| (name, *ty))
                                .ok_or("unknown Rust enumerate iterator payload")
                        })
                        .transpose()?;
                    cx.enumerate_next(iterator, option.as_ref(), index.as_ref(), element, *taken)?
                }
                S::RangeInitialize { target, start, end } => {
                    cx.range_initialize(target, start, end)?
                }
                S::RangeMove { target, source } => cx.range_move(target, source)?,
                S::RangeNext {
                    iterator,
                    option,
                    option_type,
                    payload,
                    taken,
                } => cx.range_next(
                    iterator,
                    option.as_ref(),
                    option_type,
                    payload.as_ref(),
                    *taken,
                )?,
                S::ChunkNext {
                    iterator,
                    option,
                    payload,
                    taken,
                } => cx.chunk_next(iterator, option.as_ref(), payload.as_ref(), *taken)?,
                S::Assign {
                    target: E::Local { name },
                    value,
                } if cx.scalar_operands.contains_key(name) => {
                    let (prefix, value) = cx.prepared_expr(value)?;
                    let ty = scalar_type(local_types[name])?.to_kernel_type();
                    let step = cx.scalar_operands[name].0;
                    program_seq(prefix, typed_value_step(vec![step], value, ty, false))
                }
                S::Assign {
                    target: E::Local { name },
                    value,
                } if cx.local_arrays.contains(name) => {
                    let (length, element, _) = cx.arrays[name];
                    let pointer = cx.array_pointer(name)?;
                    match value {
                        E::Array { .. } => cx.assign_array(pointer, element, length, value)?,
                        E::Repeat {
                            value,
                            length: count,
                        } if *count == length => {
                            let (checks, value) = cx.prepared_expr(value)?;
                            program_seq(
                                checks,
                                program_initialize_scalar_array(
                                    pointer,
                                    value,
                                    element,
                                    length as u32,
                                    false,
                                ),
                            )
                        }
                        E::Repeat { .. } => {
                            return Err("array repeat length disagrees with destination".into());
                        }
                        value => {
                            let (source, count, source_element) = cx.indexed_parts(value)?;
                            if count != crate::kernel::program_expression::uint64_literal(length)
                                || source_element != element
                            {
                                return Err("array copy type disagrees with destination".into());
                            }
                            program_write_scalar_array_region(
                                pointer,
                                source,
                                element,
                                length as u32,
                                true,
                            )
                        }
                    }
                }
                // Form a callable carrying the values captured here.
                S::Assign {
                    target: E::Local { name },
                    value:
                        E::ClosureInstance {
                            function,
                            site,
                            captures,
                            value_type,
                        },
                } => {
                    let (checks, value) =
                        cx.prepared_closure(function, site, captures, value_type)?;
                    program_seq(checks, program_assign(cx.binding(name)?, value))
                }
                S::Assign {
                    target: E::Local { name },
                    value,
                } if !records.contains_key(name) => cx.assign(name, value)?,
                S::Assign { target, value } => {
                    if let E::Deref {
                        value_type: Type::Array { element, length },
                        ..
                    } = target
                    {
                        let address = cx.address(target)?;
                        let element = scalar_type(element)?.to_kernel_type();
                        cx.assign_array_region(address, element, *length, value)?
                    } else if let E::Field { record, field, .. } = target
                        && let Some((element, length)) = cx
                            .fields
                            .get(&(record.as_str(), field.as_str()))
                            .and_then(|(_, ty)| array_field_parts(*ty))
                    {
                        let address = cx.address(target)?;
                        cx.assign_array_region(address, element, u64::from(length), value)?
                    } else {
                        let (mut checks, mut value) = cx.prepared_expr(value)?;
                        if matches!(target, E::Index { .. }) {
                            let value_type = indexed_element_type(cx.place_type(target)?)
                                .ok_or("unsupported Rust indexed assignment type")?;
                            let (capture, result) = cx.capture_operand(value, &value_type)?;
                            checks = program_seq(checks, capture);
                            value = result;
                        }
                        let (target_checks, address) = cx.prepared_address(target)?;
                        let value_type = cx.place_type(target)?;
                        program_seq(
                            program_seq(checks, target_checks),
                            cx.source_store(target, address, value, value_type),
                        )
                    }
                }
                S::Initialize {
                    target,
                    record,
                    fields,
                } => {
                    check(target, record)?;
                    write_fields(
                        cx,
                        crate::kernel::program_expression::variable(cx.binding(target)?),
                        record,
                        fields,
                    )?
                }
                S::Move {
                    target,
                    source,
                    record,
                }
                | S::Copy {
                    target,
                    source,
                    record,
                } => {
                    let moving = matches!(s, S::Move { .. });
                    if !moving {
                        check_copyable(cx, record)?;
                    }
                    if target == source {
                        return Err("self move is invalid".into());
                    }
                    check(source, record)?;
                    check(target, record)?;
                    let mut copy = program_skip();
                    let record_fields = cx
                        .records
                        .get(record.as_str())
                        .ok_or("missing moved record")?
                        .fields
                        .clone();
                    for field in &record_fields {
                        // The layout's offset: a symbolic layout's is a term.
                        let offset = cx.field_offset(record, &field.name)?;
                        let source_address =
                            crate::kernel::program_expression::pointer_offset_bytes(
                                crate::kernel::program_expression::variable(cx.binding(source)?),
                                offset,
                            );
                        let target_address =
                            crate::kernel::program_expression::pointer_offset_bytes(
                                crate::kernel::program_expression::variable(cx.binding(target)?),
                                offset,
                            );
                        let write = if let Type::Array { element, length } = &field.value_type {
                            program_write_scalar_array_region(
                                target_address,
                                source_address,
                                scalar_type(element)?.to_kernel_type(),
                                arrays::array_length(
                                    scalar_type(element)?.to_kernel_type(),
                                    *length,
                                )?,
                                true,
                            )
                        } else {
                            let read = E::Field {
                                base: Box::new(E::Local {
                                    name: source.clone(),
                                }),
                                record: record.clone(),
                                field: field.name.clone(),
                            };
                            program_typed_store(
                                target_address,
                                cx.expr(&read)?,
                                scalar_type(&field.value_type)?.to_kernel_type(),
                            )
                        };
                        copy = program_seq(copy, write);
                    }
                    copy
                }
                // Declare lexically scoped storage at its start. Record the
                // source declaration only when there is a written binding.
                S::BeginStorage { local } if scoped.contains_key(local) => {
                    if let Some(site) = site
                        && !drop_operands.contains_key(local)
                    {
                        cx.declaration_sites.push((cx.binding(local)?, site));
                    }
                    scoped[local].clone()
                }
                S::EndStorage { local }
                    if scoped.contains_key(local) || mir.compound_literals.contains_key(local) =>
                {
                    program_end_automatic_lifetimes(vec![cx.binding(local)?])
                }
                // Any other repeated name's storage start, as an iterator's
                // whose fields are its own locals, runs nothing.
                S::BeginStorage { local }
                    if cx.bindings.contains_key(local)
                        && !records.contains_key(local)
                        && !cx.local_arrays.contains(local) =>
                {
                    program_skip()
                }
                S::BeginStorage { local } if cx.local_arrays.contains(local) => {
                    let (length, element, _) = cx.arrays[local];
                    // Mint checked fresh automatic storage at the compiler's
                    // lifetime start, including each symbolic loop iteration.
                    // Re-entry retires the old object and checks live borrows.
                    program_begin_aggregate_construction(
                        cx.binding(local)?,
                        AggregateLayout::new(
                            arrays::array_length(element, length)? * element.byte_width(),
                            element.byte_width(),
                            vec![],
                        ),
                    )
                }
                S::BeginStorage { local } => {
                    let record = records.get(local).ok_or("unknown record storage start")?;
                    // Plain values carry no destructor or borrowed authority,
                    // so StorageLive starts a fresh lifetime, also in each
                    // pass of a loop. Drop/reference-bearing records keep the
                    // storage they were declared with.
                    if check_copyable(cx, record).is_ok() {
                        program_begin_aggregate_construction(
                            cx.binding(local)?,
                            cx.layouts
                                .get(*record)
                                .ok_or("missing record storage layout")?
                                .to_kernel_aggregate_layout(),
                        )
                    } else {
                        program_skip()
                    }
                }
                S::EndStorage { .. } => program_skip(),
            };
            statements = statements.then(Sited::at(site, statement));
        }
        let mut terminal = Sited::at(mir.blocks[block].terminator_site, terminal);
        terminal.binding_calls.extend(binding_call);
        // Each block keeps its leading unsited step, so proofs' region
        // numbers stay where they were when it held borrow endings.
        nodes[block] = Some(Sited::unsited(program_skip()).then(statements.then(terminal)));
    }
    let mut emitted = vec![false; mir.blocks.len()];
    let structured = region(
        cx,
        mir,
        &nodes,
        &flow,
        &escape_flags,
        &mut emitted,
        0..mir.blocks.len(),
        None,
    )?;
    Ok(Sited::unsited(declarations).then(structured))
}

/// Writes a record's field values, in order, at the record object `base`:
/// each scalar field by a typed store, each array field from the array
/// value itself, `[v; n]` or `[a, b]`, or from the array it copies.
fn write_fields(
    cx: &mut Context<'_>,
    base: ProgramExpression,
    record: &str,
    fields: &[E],
) -> Result<ProgramStatement, String> {
    let record_fields = cx
        .records
        .get(record)
        .ok_or("unknown constructor record")?
        .fields
        .clone();
    if fields.len() != record_fields.len() {
        return Err("partial record initialization".into());
    }
    let mut initialize = program_skip();
    for (value, field) in fields.iter().zip(&record_fields) {
        let address = crate::kernel::program_expression::pointer_offset_bytes(
            base.clone(),
            cx.field_offset(record, &field.name)?,
        );
        let write = if let Type::Array { element, length } = &field.value_type {
            cx.assign_array_region(
                address,
                scalar_type(element)?.to_kernel_type(),
                *length,
                value,
            )?
        } else {
            let (prefix, value) = cx.prepared_expr(value)?;
            program_seq(
                prefix,
                program_typed_store(
                    address,
                    value,
                    scalar_type(&field.value_type)?.to_kernel_type(),
                ),
            )
        };
        initialize = program_seq(initialize, write);
    }
    Ok(initialize)
}

fn successors(t: &T, exit: usize) -> Vec<usize> {
    match t {
        T::Goto { target }
        | T::Drop { target, .. }
        | T::Call { target, .. }
        | T::BoxFree { target, .. } => vec![*target],
        T::If {
            then_target,
            else_target,
            ..
        } => vec![*then_target, *else_target],
        T::Switch {
            cases, otherwise, ..
        } => cases
            .iter()
            .map(|case| case.target)
            .chain(*otherwise)
            .collect(),
        _ => vec![exit],
    }
}
// A reverse topological pass builds the postdominator tree. Binary lifting
// keeps each merge logarithmic; no path enumeration or graph-wide set clones.
fn iterator_reference(ty: &Type) -> bool {
    match ty {
        Type::Reference { pointee, .. } => {
            matches!(
                pointee.as_ref(),
                Type::ChunkIterator
                    | Type::SharedArrayIterator { .. }
                    | Type::EnumerateIterator { .. }
                    | Type::Range { .. }
            ) || iterator_reference(pointee)
        }
        _ => false,
    }
}

#[cfg(test)]
fn postdominators(mir: &MirBody, order: &[usize]) -> Vec<usize> {
    let graph = mir
        .blocks
        .iter()
        .map(|b| successors(&b.terminator, mir.blocks.len()))
        .collect::<Vec<_>>();
    graph_postdominators(&graph, order)
}
fn graph_postdominators(graph: &[Vec<usize>], order: &[usize]) -> Vec<usize> {
    let exit = graph.len();
    let levels = (usize::BITS - (exit + 1).leading_zeros()) as usize;
    let mut ancestors = vec![vec![exit; levels]; exit + 1];
    let mut depths = vec![0usize; exit + 1];
    let mut joins = vec![exit; exit];
    for &block in order {
        let targets = &graph[block];
        let mut a = targets[0];
        for &b in &targets[1..] {
            let mut b = b;
            if depths[a] < depths[b] {
                std::mem::swap(&mut a, &mut b);
            }
            let mut difference = depths[a] - depths[b];
            while difference != 0 {
                let bit = difference.trailing_zeros() as usize;
                a = ancestors[a][bit];
                difference &= difference - 1;
            }
            if a != b {
                for bit in (0..levels).rev() {
                    if ancestors[a][bit] != ancestors[b][bit] {
                        a = ancestors[a][bit];
                        b = ancestors[b][bit];
                    }
                }
                a = ancestors[a][0];
            }
        }
        joins[block] = a;
        depths[block] = depths[a] + 1;
        ancestors[block][0] = a;
        for bit in 1..levels {
            ancestors[block][bit] = ancestors[ancestors[block][bit - 1]][bit - 1];
        }
    }
    joins
}
/// How a loop body leaves its loop: by `break` at the loop's exit, or by a
/// labeled `break` or `continue` to an enclosing loop, which sets the loop's
/// flag to that escape's code before the `break`.
struct LoopExits<'a> {
    header: usize,
    exit: usize,
    escapes: &'a [usize],
    flag: Option<&'a BindingName>,
}

impl LoopExits<'_> {
    fn leave(&self, block: usize) -> Option<ProgramStatement> {
        if block == self.exit {
            return Some(program_break());
        }
        let index = self.escapes.iter().position(|end| *end == block)?;
        Some(program_seq(
            program_assign(self.flag?, escape_code(index)),
            program_break(),
        ))
    }
}

/// The iterator the loop headed at `header` advances: the first `next` of a
/// supported iterator in its header blocks, then in its body.
fn loop_iterator(
    cx: &Context<'_>,
    mir: &MirBody,
    header: usize,
    loop_: &flow::While,
) -> Option<crate::languages::interface::RustLoopIterator> {
    use crate::languages::c::syntax::{RustIteratorKind as K, RustLoopIterator};
    let body = if loop_.body <= header {
        loop_.body..header
    } else {
        loop_.body..loop_.exit.max(loop_.body)
    };
    // A crate's own iterator: the header calls its `next(&mut iter)` and
    // tests the `Option` that call returns.
    if let T::If {
        condition: E::VariantIs { value, .. },
        ..
    } = &mir.blocks[loop_.test].terminator
    {
        // The call whose result the test reads: by its destination, or by
        // its step when its result is the test's own.
        let reads = |terminator: &T| match (value.as_ref(), terminator) {
            (
                E::Local { name },
                T::Call {
                    destination: Some(destination),
                    ..
                },
            ) => destination == name,
            (E::CallResult { call, .. }, T::Call { result, .. }) => *result == Some(*call),
            _ => false,
        };
        let user = std::iter::once(header)
            .chain(loop_.headers.iter().copied())
            .filter_map(|block| mir.blocks.get(block))
            .find_map(|block| match &block.terminator {
                terminator @ T::Call { arguments, .. } if reads(terminator) => {
                    match arguments.as_slice() {
                        [E::Borrow { place, .. }] => match place.as_ref() {
                            E::Local { name } => Some(name.clone()),
                            _ => None,
                        },
                        _ => None,
                    }
                }
                _ => None,
            });
        if user.is_some() {
            return Some(RustLoopIterator {
                chunk_fields: None,
                slice_fields: None,
                kind: K::User,
                count_binding: None,
                range_bounds: None,
            });
        }
    }
    std::iter::once(header)
        .chain(loop_.headers.iter().copied())
        .chain(std::iter::once(loop_.test))
        .chain(body)
        .filter_map(|block| mir.blocks.get(block))
        .flat_map(|block| &block.statements)
        .find_map(|statement| {
            let (local, kind) = match statement {
                S::SharedArrayNext { iterator, .. } => (iterator, K::Slice),
                S::EnumerateNext { iterator, .. } => (iterator, K::Enumerate),
                S::ChunkNext { iterator, .. } => (iterator, K::Chunks),
                S::RangeNext { iterator, .. } => {
                    let inclusive = cx.ranges.get(iterator)?.inclusive;
                    (
                        iterator,
                        if inclusive {
                            K::RangeInclusive
                        } else {
                            K::Range
                        },
                    )
                }
                _ => return None,
            };
            Some(RustLoopIterator {
                chunk_fields: cx.mir_chunk_iterators.get(local).cloned(),
                slice_fields: cx
                    .shared_array_iterators
                    .get(local)
                    .map(|iter| iter.fields.clone()),
                kind,
                range_bounds: cx.ranges.get(local).map(|range| range.bounds.clone()),
                count_binding: if kind == K::Enumerate {
                    cx.enumerate_fields.get(local).cloned()
                } else {
                    None
                },
            })
        })
}

fn escape_code(index: usize) -> ProgramExpression {
    crate::kernel::program_expression::int32_literal(index as u32 + 1)
}

#[allow(clippy::too_many_arguments)]
fn region(
    cx: &mut Context<'_>,
    mir: &MirBody,
    nodes: &[Option<Sited>],
    flow: &flow::Flow,
    escape_flags: &BTreeMap<usize, BindingName>,
    emitted: &mut [bool],
    bounds: std::ops::Range<usize>,
    exits: Option<&LoopExits<'_>>,
) -> Result<Sited, String> {
    let mut block = bounds.start;
    let stop = bounds.end;
    let mut result = Sited::unsited(program_skip());
    while block != stop && block != mir.blocks.len() {
        // The enclosing loop's exit, reached from its body, is a `break`,
        // and so is a labeled escape, after setting the loop's flag.
        if let Some(leave) = exits.and_then(|exits| exits.leave(block)) {
            result = result.then(Sited::unsited(leave));
            break;
        }
        if std::mem::replace(&mut emitted[block], true) && !flow.exit_tails[block] {
            return Err("unstructured shared MIR region outside move/drop slice".into());
        }
        if let Some(loop_) = flow.loops.get(&block) {
            let T::If { condition, .. } = &mir.blocks[loop_.test].terminator else {
                return Err("natural while header is not conditional".into());
            };
            // The loop statement, as written: the source of its test.
            let loop_site = mir.blocks[loop_.test].terminator_site;
            let inner = LoopExits {
                header: block,
                exit: loop_.exit,
                escapes: &loop_.escapes,
                flag: escape_flags.get(&block),
            };
            // The loop's index is its place in preorder, the order its
            // `while` takes in the lowered body; its iterator is the one the
            // first `next` from its header on advances.
            let iterator = loop_iterator(cx, mir, block, loop_);
            cx.loop_iterators.push(iterator);
            let body = region(
                cx,
                mir,
                nodes,
                flow,
                escape_flags,
                emitted,
                loop_.body..block,
                loop_.breaks.then_some(&inner),
            )?;
            // A header that calls runs before its test each pass, so the test
            // reads what the header left; otherwise the test is read through
            // the header's scalar copies.
            let condition = if loop_.header_calls {
                condition.clone()
            } else {
                flow::header_condition(
                    mir,
                    &loop_.headers,
                    condition,
                    &flow.scalar_names,
                    &flow.metadata_names,
                )?
            };
            let condition = if loop_.body_on_true {
                condition
            } else {
                flow::negate_condition(condition)
            };
            let condition = cx.condition(&condition)?;
            let mut header = nodes[block].as_ref().ok_or("missing loop header")?.clone();
            for part in loop_.headers.iter().skip(1) {
                if std::mem::replace(&mut emitted[*part], true) {
                    return Err("shared MIR while-header continuation".into());
                }
                header = header.then(
                    nodes[*part]
                        .as_ref()
                        .ok_or("missing loop header continuation")?
                        .clone(),
                );
            }
            // The pure condition denotes the value after the header's scalar
            // assignments. Keep those assignments before each taken body and
            // once on the final false test, without an artificial break exit.
            // A body that breaks leaves without running them again, so its
            // test exits by `break` too, right after them, as the MIR does.
            let lowered = if loop_.breaks {
                let exit = region(
                    cx,
                    mir,
                    nodes,
                    flow,
                    escape_flags,
                    emitted,
                    loop_.after..mir.blocks.len(),
                    Some(&inner),
                )?;
                Sited::looping(
                    loop_site,
                    crate::kernel::program_expression::int32_literal(1),
                    header.then(
                        Sited::branch(loop_site, condition, Sited::unsited(program_skip()), exit)
                            .then(body),
                    ),
                )
            } else if loop_.header_calls {
                // The test reads what the header's call returned, so the
                // header runs at the top of each pass and its test leaves.
                Sited::looping(
                    loop_site,
                    crate::kernel::program_expression::int32_literal(1),
                    header.then(
                        Sited::branch(
                            loop_site,
                            condition,
                            Sited::unsited(program_skip()),
                            Sited::unsited(program_break()),
                        )
                        .then(body),
                    ),
                )
            } else {
                Sited::looping(loop_site, condition, header.clone().then(body)).then(header)
            };
            // A labeled `break` or `continue` leaves this loop with its flag
            // naming the escape; the enclosing body then resumes there.
            let mut lowered = lowered;
            if let Some(flag) = inner.flag {
                lowered = Sited::unsited(program_assign(
                    flag,
                    crate::kernel::program_expression::int32_literal(0),
                ))
                .then(lowered);
                for (index, end) in loop_.escapes.iter().enumerate() {
                    let resume = match exits {
                        Some(outer) if *end == outer.header => program_continue(),
                        Some(outer) => outer
                            .leave(*end)
                            .ok_or("Rust labeled break leaves more than one enclosing loop")?,
                        None => return Err("Rust labeled break outside an enclosing loop".into()),
                    };
                    lowered = lowered.then(Sited::unsited(program_if(
                        crate::kernel::program_expression::equal(
                            crate::kernel::program_expression::variable(flag),
                            escape_code(index),
                        ),
                        resume,
                        program_skip(),
                    )));
                }
            }
            result = result.then(lowered);
            block = loop_.exit;
            continue;
        }
        result = result.then(nodes[block].as_ref().ok_or("missing MIR block")?.clone());
        // The statement as written that branches here.
        let site = mir.blocks[block].terminator_site;
        match &mir.blocks[block].terminator {
            T::If {
                condition,
                then_target,
                else_target,
            } => {
                let join = if flow.joins[block] == mir.blocks.len() {
                    stop
                } else {
                    flow.joins[block]
                };
                let yes = region(
                    cx,
                    mir,
                    nodes,
                    flow,
                    escape_flags,
                    emitted,
                    *then_target..join,
                    exits,
                )?;
                let mut no = region(
                    cx,
                    mir,
                    nodes,
                    flow,
                    escape_flags,
                    emitted,
                    *else_target..join,
                    exits,
                )?;
                // The unwrapped payload ends the retained box on the Some
                // arm. On the None arm it can end immediately after the test.
                if let Some(name) = super::super::charon::tested_option_box_local(condition)
                    && cx
                        .scalar_operands
                        .get(name)
                        .is_some_and(|(_, last)| last.block == *then_target)
                {
                    let mut operand = cx.expr(&E::Local { name: name.clone() })?;
                    if let ProgramExpression::StepResult { ends, .. } = &mut operand {
                        *ends = true;
                    }
                    no = Sited::unsited(typed_value_step(
                        Vec::new(),
                        operand,
                        ProgramType::Int32Pointer,
                        false,
                    ))
                    .then(no);
                }
                cx.mir_point = Some(super::super::borrow_frontiers::MirPoint {
                    block,
                    statement: mir.blocks[block].statements.len(),
                });
                let condition = cx.condition(condition)?;
                cx.mir_point = None;
                result = result.then(Sited::branch(site, condition, yes, no));
                block = join;
            }
            T::Switch {
                scrutinee,
                cases,
                otherwise,
            } => {
                let join = if flow.joins[block] == mir.blocks.len() {
                    stop
                } else {
                    flow.joins[block]
                };
                result = result.then(switch(
                    cx,
                    mir,
                    nodes,
                    flow,
                    escape_flags,
                    emitted,
                    scrutinee,
                    cases,
                    *otherwise,
                    join,
                    exits,
                    site,
                )?);
                block = join;
            }
            T::Goto { target }
            | T::Drop { target, .. }
            | T::Call { target, .. }
            | T::BoxFree { target, .. } => block = *target,
            _ => break,
        }
    }
    Ok(result)
}

/// A `match`: each distinct target's region once, entered by every label
/// that leads to it. An enum's labels are its variants, which the kernel's
/// `switch` matches; an integer's are values, tested in an `if` chain whose
/// last arm is the otherwise target, or the last target when there is none.
#[allow(clippy::too_many_arguments)]
fn switch(
    cx: &mut Context<'_>,
    mir: &MirBody,
    nodes: &[Option<Sited>],
    flow: &flow::Flow,
    escape_flags: &BTreeMap<usize, BindingName>,
    emitted: &mut [bool],
    scrutinee: &E,
    cases: &[crate::languages::rust::schema::SwitchCase],
    otherwise: Option<usize>,
    join: usize,
    exits: Option<&LoopExits<'_>>,
    site: Option<u32>,
) -> Result<Sited, String> {
    use crate::languages::rust::schema::SwitchLabel;
    let mut groups: Vec<(usize, Vec<&SwitchLabel>)> = Vec::new();
    for case in cases {
        match groups.iter_mut().find(|(target, _)| *target == case.target) {
            Some((_, labels)) => labels.push(&case.label),
            None => groups.push((case.target, vec![&case.label])),
        }
    }
    if let Some(otherwise) = otherwise
        && !groups.iter().any(|(target, _)| *target == otherwise)
    {
        groups.push((otherwise, Vec::new()));
    }
    let mut bodies = Vec::with_capacity(groups.len());
    for (target, _) in &groups {
        bodies.push(region(
            cx,
            mir,
            nodes,
            flow,
            escape_flags,
            emitted,
            *target..join,
            exits,
        )?);
    }
    let capture_type = match scrutinee {
        E::EnumField {
            name,
            variant,
            index,
            ..
        } => super::nested_enum_field_type(name, variant, *index)?
            .map(|ty| (ty.to_kernel_type(), "Rust enum field")),
        E::Deref {
            value_type: value_type @ Type::Enum { .. },
            ..
        } => Some((
            scalar_type(value_type)?.to_kernel_type(),
            "Rust match operand",
        )),
        _ => None,
    };
    if groups.len() == 1 {
        let body = bodies.pop().expect("one match arm");
        return Ok(if let Some((value_type, _)) = capture_type {
            let value = cx.expr(scrutinee)?;
            Sited::at(site, typed_value_step(Vec::new(), value, value_type, false)).then(body)
        } else {
            body
        });
    }
    // Read the match operand once so the proof can split on that value.
    // Only the last test can end it on both edges.
    let capture = if let Some((value_type, origin)) = capture_type {
        let step = cx.result_step();
        let value = cx.expr(scrutinee)?;
        Some((
            Sited::at(site, typed_value_step(vec![step], value, value_type, false)),
            ProgramExpression::StepResult {
                step,
                origin: StepOrigin::Value(origin),
                ends: true,
            },
            value_type,
        ))
    } else {
        None
    };
    let mut has_later_test = false;
    let mut chain = None;
    for ((target, labels), body) in groups.iter().zip(bodies).rev() {
        let Some(rest) = chain else {
            chain = Some(body);
            continue;
        };
        if otherwise == Some(*target) {
            return Err("a Rust match's otherwise arm must come last".into());
        }
        let (value, body) = match &capture {
            Some((_, value, ty)) if has_later_test => {
                // The false edge still needs the projection. End it before
                // entering this arm, which can return or start another loop.
                let end = typed_value_step(Vec::new(), value.clone(), *ty, false);
                (
                    observe_operand(value.clone()),
                    Sited::unsited(end).then(body),
                )
            }
            Some((_, value, _)) => (value.clone(), body),
            None => (cx.expr(scrutinee)?, body),
        };
        let mut condition = None;
        for label in labels {
            // An enum arm tests its variant; the `if` it becomes steps and
            // splits as any other.
            let test = match label {
                SwitchLabel::Value { value: label_value } => {
                    crate::kernel::program_expression::equal(value.clone(), cx.expr(label_value)?)
                }
                SwitchLabel::Variant { name } => ProgramExpression::EnumIs {
                    value: Box::new(value.clone()),
                    variant: name.clone(),
                },
            };
            condition = Some(match condition {
                Some(earlier) => crate::kernel::program_expression::or(earlier, test),
                None => test,
            });
        }
        chain = Some(Sited::branch(
            site,
            condition.ok_or("Rust match arm without a label")?,
            body,
            rest,
        ));
        has_later_test = true;
    }
    let chain = chain.ok_or_else(|| "Rust match without arms".to_string())?;
    Ok(match capture {
        Some((capture, _, _)) => capture.then(chain),
        None => chain,
    })
}

fn check_copyable(cx: &Context<'_>, name: &str) -> Result<(), String> {
    let record = cx.records.get(name).ok_or("unknown copied record")?;
    if record.destructor.is_some() || record.fields.iter().any(|field| {
        !field.value_type.is_scalar()
            && !matches!(&field.value_type, Type::Array { element, .. } if matches!(element.as_ref(), Type::I32 | Type::U8 | Type::U32))
    }) {
        return Err("record copies require plain scalar/array fields and no Drop".into());
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn owned_lowering_does_not_duplicate_unrelated_context() {
        use crate::languages::rust::schema::{Field, Place, Span};
        fn count(s: &ProgramStatement) -> usize {
            match s {
                ProgramStatement::Seq(statements) => {
                    statements.len() - 1
                        + statements
                            .iter()
                            .map(|statement| count(statement))
                            .sum::<usize>()
                }
                ProgramStatement::If {
                    then_branch,
                    else_branch,
                    ..
                } => 1 + count(then_branch) + count(else_branch),
                _ => 1,
            }
        }
        let span = Span { line: 1, column: 1 };
        let record = Record {
            name: "Live".into(),
            size: 4,
            alignment: 4,
            fields: vec![Field {
                name: "x".into(),
                offset: 0,
                value_type: Type::I32,
            }],
            destructor: None,
            symbolic: false,
        };
        let owned = Function {
            sites: Vec::new(),
            name: "owned".into(),
            return_type: Type::Unit,
            parameters: vec![],
            body: vec![],
            external: false,
            captures: 0,
            implements: None,
            instance_of: None,
            core_method: None,
            span: span.clone(),
            mir: Some(MirBody {
                object_bindings: Vec::new(),
                return_place: "__rust_mir_0".into(),
                spellings: Default::default(),
                unnamed_locals: Default::default(),
                compound_literals: Default::default(),
                borrowed_scalars: Default::default(),
                locals: vec![Place {
                    name: "value".into(),
                    value_type: Type::Record {
                        name: "Live".into(),
                    },
                    span: span.clone(),
                }],
                blocks: vec![crate::languages::rust::schema::MirBlock {
                    terminator_site: None,
                    statements: vec![S::Initialize {
                        target: "value".into(),
                        record: "Live".into(),
                        fields: vec![E::Integer { value: 3 }],
                    }],
                    terminator: T::Return,
                }],
            }),
        };
        let mut baseline = None;
        for size in [8, 32, 128] {
            let mut export = RustExport {
                schema: 2,
                compiler_commit: String::new(),
                target: String::new(),
                edition: "2024".into(),
                overflow_checks: true,
                panic: "abort".into(),
                mir_opt_level: 0,
                logical_source: "scale.rs".into(),
                records: vec![record.clone()],
                enums: vec![],
                functions: vec![owned.clone()],
            };
            for i in 0..size {
                let mut unrelated = record.clone();
                unrelated.name = format!("Unrelated{i}");
                export.records.push(unrelated);
                export.functions.push(Function {
                    sites: Vec::new(),
                    name: format!("unrelated{i}"),
                    return_type: Type::I32,
                    parameters: vec![],
                    body: vec![super::super::S::Return {
                        value: Some(E::Integer { value: 0 }),
                    }],
                    mir: None,
                    external: false,
                    captures: 0,
                    implements: None,
                    instance_of: None,
                    core_method: None,
                    span: span.clone(),
                });
            }
            let (lowered, _) = super::super::lower(&export).unwrap();
            assert_eq!(lowered.len(), size + 1);
            let operations = count(lowered[0].to_kernel_function().body());
            assert_eq!(*baseline.get_or_insert(operations), operations);
        }
    }
    #[test]
    fn diamond_cleanup_joins_emit_each_block_once_at_multiple_sizes() {
        for count in [8, 32, 128] {
            let mut blocks = Vec::new();
            for i in 0..count {
                let start = i * 3;
                blocks.push(crate::languages::rust::schema::MirBlock {
                    terminator_site: None,
                    statements: vec![],
                    terminator: T::If {
                        condition: E::Boolean { value: true },
                        then_target: start + 1,
                        else_target: start + 2,
                    },
                });
                for _ in 0..2 {
                    blocks.push(crate::languages::rust::schema::MirBlock {
                        terminator_site: None,
                        statements: vec![],
                        terminator: T::Goto { target: start + 3 },
                    });
                }
            }
            blocks.push(crate::languages::rust::schema::MirBlock {
                terminator_site: None,
                statements: vec![],
                terminator: T::Return,
            });
            let mir = MirBody {
                object_bindings: Vec::new(),
                return_place: "__rust_mir_0".into(),
                spellings: Default::default(),
                unnamed_locals: Default::default(),
                compound_literals: Default::default(),
                borrowed_scalars: Default::default(),
                locals: vec![],
                blocks,
            };
            let order = (0..mir.blocks.len()).rev().collect::<Vec<_>>();
            let joins = postdominators(&mir, &order);
            for i in 0..count {
                assert_eq!(joins[i * 3], i * 3 + 3);
            }
            let fields = BTreeMap::new();
            let layouts = BTreeMap::new();
            let records = BTreeMap::new();
            let functions = BTreeMap::new();
            let mut cx = Context {
                scalar_operands: BTreeMap::new(),
                bindings: BTreeMap::new(),
                declaration_sites: Vec::new(),
                references: BTreeMap::new(),
                shared_array_iterators: BTreeMap::new(),
                ranges: BTreeMap::new(),
                enumerate_fields: BTreeMap::new(),
                shared_array_options: BTreeMap::new(),
                shared_scalar_slices: BTreeMap::new(),
                mir_chunk_iterators: BTreeMap::new(),
                chunk_options: BTreeMap::new(),
                local_arrays: BTreeSet::new(),
                arrays: BTreeMap::new(),
                owned_locals: BTreeSet::new(),
                addressable_locals: BTreeSet::new(),
                memory_values: BTreeMap::new(),
                slices: BTreeMap::new(),
                source: "scale.rs",
                function: "scale",
                fields: &fields,
                next_load: 0,
                import_identity: None,
                mir_point: None,
                mir_nodes: BTreeMap::new(),
                slice_local_owner: LocalFunctionId::new(None, "test".into()),
                next_slice_local: 0,
                next_result_step: std::cell::Cell::new(0),
                step_pointee_layouts: std::cell::RefCell::new(BTreeMap::new()),
                loop_iterators: Vec::new(),
                locals: BTreeSet::new(),
                return_type: InterfaceType::Void,
                layouts: &layouts,
                records: &records,
                functions: &functions,
            };
            let nodes = (0..mir.blocks.len())
                .map(|i| {
                    Some(Sited::unsited(program_assert(
                        crate::kernel::program_expression::int32_literal(i as u32),
                    )))
                })
                .collect::<Vec<_>>();
            let mut emitted = vec![false; mir.blocks.len()];
            let structured = region(
                &mut cx,
                &mir,
                &nodes,
                &flow::Flow {
                    order,
                    joins,
                    exit_tails: vec![false; mir.blocks.len()],
                    loops: BTreeMap::new(),
                    scalar_names: BTreeSet::new(),
                    metadata_names: BTreeSet::new(),
                },
                &BTreeMap::new(),
                &mut emitted,
                0..mir.blocks.len(),
                None,
            )
            .unwrap();
            assert!(emitted.iter().all(|b| *b));
            fn assertions(s: &ProgramStatement) -> usize {
                match s {
                    ProgramStatement::Seq(statements) => statements
                        .iter()
                        .map(|statement| assertions(statement))
                        .sum(),
                    ProgramStatement::If {
                        then_branch,
                        else_branch,
                        ..
                    } => assertions(then_branch) + assertions(else_branch),
                    ProgramStatement::Assert { .. } => 1,
                    _ => 0,
                }
            }
            assert_eq!(assertions(&structured.statement), count * 3 + 1);
        }
    }
}
