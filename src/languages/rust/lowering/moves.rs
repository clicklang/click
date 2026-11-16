//! Compiler drop CFGs emit shared joins and supported natural while loops once. Checked live flags consume
//! a whole value on move/drop and reject duplicate cleanup even when scalar
//! field bits remain in old storage.
use super::*;
mod flow;
use crate::languages::rust::schema::{MirBody, MirStatement as S, MirTerminator as T};

/// A lowered statement and the source statement each of its regions comes
/// from (`Function::sites`), in the order the source layout numbers its
/// regions: a statement before the statements it contains. A region the
/// lowering adds with no source statement of its own has none.
#[derive(Clone)]
pub(super) struct Sited {
    pub(super) statement: ProgramStatement,
    pub(super) sites: Vec<Option<u32>>,
}

impl Sited {
    /// `statement`, every region of which comes from `site`.
    fn at(site: Option<u32>, statement: ProgramStatement) -> Self {
        let sites = vec![site; region_count(&statement)];
        Self { statement, sites }
    }

    fn unsited(statement: ProgramStatement) -> Self {
        Self::at(None, statement)
    }

    /// `self`, then `next`: `program_seq(self, next)`.
    fn then(mut self, next: Sited) -> Self {
        self.sites.extend(next.sites);
        Self {
            statement: program_seq(self.statement, next.statement),
            sites: self.sites,
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
        sites.extend(then.sites);
        sites.extend(otherwise.sites);
        Self {
            statement: program_if(condition, then.statement, otherwise.statement),
            sites,
        }
    }

    /// `program_while(condition, [], body)`, a loop that comes from `site`.
    fn looping(site: Option<u32>, condition: ProgramExpression, body: Sited) -> Self {
        let mut sites = vec![site];
        sites.extend(body.sites);
        Self {
            statement: program_while(condition, Vec::new(), body.statement),
            sites,
        }
    }
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
        ProgramStatement::Loop { body, .. } => 1 + region_count(body),
        ProgramStatement::TryCatchInt32 {
            try_body, handler, ..
        } => 1 + region_count(try_body) + region_count(handler),
        _ => 1,
    }
}

pub(super) fn lower(cx: &mut Context<'_>, f: &Function, mir: &MirBody) -> Result<Sited, String> {
    // Index storage starts once. Locals without a compiler storage event
    // retain their function-entry backing (including return-place arrays).
    let storage_starts: BTreeSet<&str> = mir
        .blocks
        .iter()
        .flat_map(|block| &block.statements)
        .filter_map(|statement| match statement {
            S::BeginStorage { local } => Some(local.as_str()),
            _ => None,
        })
        .collect();
    // The locals the body borrows, `_5 = &mut o`.
    // The locals a borrow names: a borrow is a statement's value, or a call's
    // argument, `f(&mut x)`.
    let borrowed: BTreeSet<&str> = mir
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
                E::Local { name } => Some(name.as_str()),
                _ => None,
            },
            _ => None,
        })
        .collect();
    let mut records = BTreeMap::new();
    let mut live = BTreeMap::new();
    let mut declarations = program_skip();
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
        if let Type::SharedArrayIterator { element } | Type::SharedArrayOption { element } =
            &local.value_type
        {
            declarations = program_seq(
                declarations,
                cx.shared_array_storage(
                    &local.name,
                    element,
                    matches!(local.value_type, Type::SharedArrayOption { .. }),
                )?,
            );
            continue;
        }
        if let Type::EnumerateIterator { element } | Type::EnumerateOption { element } =
            &local.value_type
        {
            declarations = program_seq(
                declarations,
                cx.enumerate_storage(
                    &local.name,
                    element,
                    matches!(local.value_type, Type::EnumerateOption { .. }),
                )?,
            );
            continue;
        }
        if let Type::Range { element, inclusive } = &local.value_type {
            declarations = program_seq(
                declarations,
                cx.range_storage(&local.name, element, *inclusive)?,
            );
            continue;
        }
        if matches!(local.value_type, Type::ChunkIterator | Type::ChunkOption) {
            declarations = program_seq(
                declarations,
                cx.chunk_storage(&local.name, local.value_type == Type::ChunkOption)?,
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
            Type::Record { name } => {
                cx.owned_locals.insert(local.name.clone());
                let flag = format!("__rust_owned_live_{index}");
                if !cx.locals.insert(flag.clone()) {
                    return Err("MIR live flag collides with a source name".into());
                }
                records.insert(local.name.as_str(), name.as_str());
                live.insert(local.name.as_str(), flag.clone());
                // Construction grants authority over fresh stack bytes. The
                // live flag stays false until every typed field is overwritten;
                // source reads cannot observe the kernel's fresh placeholders.
                if parameter {
                    declarations = program_seq(
                        declarations,
                        program_seq(
                            program_declare(flag.clone(), ProgramType::Int32),
                            program_assign(
                                flag,
                                crate::kernel::program_expression::int32_literal(1),
                            ),
                        ),
                    );
                    continue;
                }
                program_seq(
                    program_declare(flag.clone(), ProgramType::Int32),
                    program_seq(
                        program_assign(flag, crate::kernel::program_expression::int32_literal(0)),
                        if storage_starts.contains(local.name.as_str())
                            && check_copyable(cx, name).is_ok()
                        {
                            program_skip()
                        } else {
                            program_begin_aggregate_construction(
                                local.name.clone(),
                                cx.layouts
                                    .get(name.as_str())
                                    .ok_or("missing owned record layout")?
                                    .to_kernel_aggregate_layout(),
                            )
                        },
                    ),
                )
            }
            Type::ScalarSlice { element, mutable } => {
                let element_type = scalar_type(element)?.to_kernel_type();
                let pointer_type = scalar_type(&Type::Reference {
                    mutable: *mutable,
                    pointee: element.clone(),
                })?
                .to_kernel_type();
                let length = format!("{}_len", local.name);
                if !cx.locals.insert(length.clone()) {
                    return Err("MIR scalar slice length collision".into());
                }
                cx.shared_scalar_slices
                    .insert(local.name.clone(), (length.clone(), element_type));
                program_seq(
                    program_declare_with_all_qualifiers(
                        &local.name,
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
                let length = format!("{}_len", local.name);
                if !cx.locals.insert(length.clone()) {
                    return Err("MIR slice local length collision".into());
                }
                cx.slices
                    .insert(local.name.clone(), (length.clone(), !mutable));
                program_seq(
                    program_declare_with_all_qualifiers(
                        &local.name,
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
                    &local.name,
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
                if storage_starts.contains(local.name.as_str()) {
                    program_skip()
                } else {
                    program_begin_aggregate_construction(
                        local.name.clone(),
                        AggregateLayout::new(
                            *length as u32 * element.byte_width(),
                            element.byte_width(),
                            vec![],
                        ),
                    )
                }
            }
            Type::Reference { mutable, .. } => program_declare_with_all_qualifiers(
                local.name.clone(),
                scalar_type(&local.value_type)?.to_kernel_type(),
                false,
                false,
                false,
                !mutable,
            ),
            // A borrowed enum or type-parameter local keeps its value in its
            // object's memory, where a write through the borrow lands.
            t @ (Type::Enum { .. } | Type::Parameter { .. } | Type::Vec { .. })
                if borrowed.contains(local.name.as_str()) =>
            {
                let value_type = scalar_type(t)?.to_kernel_type();
                cx.memory_values.insert(local.name.clone(), value_type);
                program_begin_aggregate_construction(
                    local.name.clone(),
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
                program_declare(local.name.clone(), scalar_type(t)?.to_kernel_type())
            }
        };
        declarations = program_seq(declarations, statement);
    }
    if mir.blocks.is_empty() {
        return Err("MIR body has no entry block".into());
    }
    let flow = flow::Flow::analyze(f, mir)?;
    for (header, loop_) in &flow.loops {
        if loop_.escapes.is_empty() {
            continue;
        }
        let flag = escape_flag(*header);
        if !cx.locals.insert(flag.clone()) {
            return Err("MIR loop escape flag collides with a source name".into());
        }
        declarations = program_seq(declarations, program_declare(flag, ProgramType::Int32));
    }
    let leases = super::scalar_leases::prepare(
        f,
        cx.import_identity.as_deref(),
        flow.loops.is_empty().then_some(flow.joins.as_slice()),
    );
    let mut nodes = vec![None; mir.blocks.len()];
    let check = |local: &str, record: &str| -> Result<&str, String> {
        if records.get(local).copied() != Some(record) {
            return Err("owned MIR place disagrees with record type".into());
        }
        live.get(local)
            .map(String::as_str)
            .ok_or("unknown owned MIR place".into())
    };
    let assertion = |flag: &str, is_live: bool| {
        program_assert(crate::kernel::program_expression::equal(
            crate::kernel::program_expression::variable(flag),
            crate::kernel::program_expression::int32_literal(u32::from(is_live)),
        ))
    };
    for &block in &flow.order {
        cx.mir_point = None;
        cx.mir_nodes.clear();
        let terminal = match &mir.blocks[block].terminator {
            T::Goto { .. } => program_skip(),
            T::If { condition, .. } => accesses(&[condition], &live),
            T::Switch { scrutinee, .. } => accesses(&[scrutinee], &live),
            T::Return => {
                let mut end = if f.return_type == Type::Unit {
                    program_return(program_void_value())
                } else if let Type::Record { name } = &f.return_type {
                    let flag = check("__rust_mir_0", name)?;
                    program_seq(
                        assertion(flag, true),
                        program_seq(
                            program_assign(
                                flag,
                                crate::kernel::program_expression::int32_literal(0),
                            ),
                            program_return(crate::kernel::program_expression::variable(
                                "__rust_mir_0",
                            )),
                        ),
                    )
                } else {
                    program_return(crate::kernel::program_expression::variable("__rust_mir_0"))
                };
                // Plain values without a destructor can die at Return; any
                // destructor-bearing value must already have been consumed.
                for (local, record) in &records {
                    if *local == "__rust_mir_0"
                        && matches!(&f.return_type, Type::Record { name } if name == record)
                    {
                        // The return sequence itself consumes this slot;
                        // its destructor belongs to the receiving caller.
                        continue;
                    }
                    if cx
                        .records
                        .get(record)
                        .ok_or("missing record")?
                        .destructor
                        .is_some()
                    {
                        end = program_seq(assertion(&live[*local], false), end);
                    }
                }
                end
            }
            T::Unreachable => program_assert(crate::kernel::program_expression::int32_literal(0)),
            T::Panic { message } => program_labeled_assert(
                crate::kernel::program_expression::int32_literal(0),
                format!("Rust panic `{message}`"),
            ),
            // The allocation comes first; a failed one aborts, so the
            // record moves into a live block, and the box is its address.
            T::BoxNew {
                source,
                record,
                destination,
                ..
            } => {
                let flag = check(source, record)?;
                let layout = cx
                    .layouts
                    .get(record.as_str())
                    .ok_or("missing boxed record layout")?;
                let class = layout.class().map(|class| {
                    (
                        crate::kernel::effective_type::CAccessClass::Struct(class.clone()),
                        layout.size_bytes(),
                        layout.alignment_bytes(),
                    )
                });
                program_seq(
                    assertion(flag, true),
                    program_seq(
                        ProgramStatement::HeapAllocate {
                            target: (destination.clone()).into(),
                            bytes: crate::kernel::program_expression::int32_literal(
                                layout.size_bytes(),
                            ),
                            zeroed: false,
                            object_type: class,
                            ends_program_on_failure: true,
                        },
                        program_seq(
                            crate::kernel::program_copy_aggregate(
                                crate::kernel::program_expression::variable(destination),
                                crate::kernel::program_expression::cast(
                                    crate::kernel::program_expression::variable(source),
                                    ProgramType::Int32Pointer,
                                ),
                                layout.to_kernel_aggregate_layout(),
                            ),
                            program_assign(
                                flag,
                                crate::kernel::program_expression::int32_literal(0),
                            ),
                        ),
                    ),
                )
            }
            // A non-null box's record is dropped through its glue before
            // the free, `if (box) glue(box); free(box);`; freeing null has no
            // effect.
            T::BoxFree { local, glue, .. } => {
                let free = crate::kernel::program_heap_free(
                    crate::kernel::program_expression::variable(local),
                );
                match glue {
                    Some(glue) => program_seq(
                        crate::kernel::program_if(
                            crate::kernel::program_expression::variable(local),
                            program_call(
                                glue,
                                vec![crate::kernel::program_expression::variable(local)],
                            ),
                            program_skip(),
                        ),
                        free,
                    ),
                    None => free,
                }
            }
            T::Drop { local, record, .. } => {
                let flag = check(local, record)?;
                let r = cx.records.get(record.as_str()).ok_or("unknown drop type")?;
                let cleanup = match &r.destructor {
                    Some(dtor) if cx.functions.contains_key(dtor.as_str()) => program_call(
                        dtor,
                        vec![crate::kernel::program_expression::cast(
                            crate::kernel::program_expression::variable(local),
                            ProgramType::Int32Pointer,
                        )],
                    ),
                    Some(_) => {
                        return Err("destructor body missing from prepared Rust input".into());
                    }
                    None => program_skip(),
                };
                program_seq(
                    assertion(flag, true),
                    program_seq(
                        cleanup,
                        program_assign(flag, crate::kernel::program_expression::int32_literal(0)),
                    ),
                )
            }
            T::Call {
                function,
                arguments,
                destination,
                through_pointer: true,
                owned_arguments,
                ..
            } => {
                // The pointer's own type gives the arguments and result.
                let Some(Type::FnPointer { parameters, result }) = mir
                    .locals
                    .iter()
                    .find(|local| &local.name == function)
                    .map(|local| &local.value_type)
                else {
                    return Err("Rust pointer call target is not a function-pointer local".into());
                };
                if !owned_arguments.is_empty() {
                    return Err("Rust pointer call carries owned-argument metadata".into());
                }
                let (prefix, arguments_values) =
                    cx.typed_arguments(parameters.clone(), arguments)?;
                let call = if **result == Type::Unit {
                    program_call(function, arguments_values)
                } else {
                    cx.call_then_assign(destination, function, arguments_values)
                };
                program_seq(
                    accesses(&arguments.iter().collect::<Vec<_>>(), &live),
                    program_seq(prefix, call),
                )
            }
            T::Call {
                function,
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
                let (prefix, arguments_values) = cx.prepared_arguments(function, arguments)?;
                let mut transfer = program_skip();
                let mut indices = BTreeSet::new();
                let mut previous_index = None;
                for argument in owned_arguments {
                    if previous_index.is_some_and(|previous| previous >= argument.index)
                        || !indices.insert(argument.index)
                        || !matches!(arguments.get(argument.index), Some(E::Local { name }) if name == &argument.local)
                        || callee.parameters.get(argument.index).map(|p| &p.value_type)
                            != Some(&Type::Record {
                                name: argument.record.clone(),
                            })
                    {
                        return Err("owned call metadata disagrees with callee and operands".into());
                    }
                    previous_index = Some(argument.index);
                    let flag = check(&argument.local, &argument.record)?;
                    if !argument.moved {
                        check_copyable(cx, &argument.record)?;
                    }
                    transfer = program_seq(transfer, assertion(flag, true));
                    if argument.moved {
                        transfer = program_seq(
                            transfer,
                            program_assign(
                                flag,
                                crate::kernel::program_expression::int32_literal(0),
                            ),
                        );
                    }
                }
                if callee.parameters.iter().enumerate().any(|(index, p)| {
                    matches!(p.value_type, Type::Record { .. }) && !indices.contains(&index)
                }) {
                    return Err("owned call operand lacks transfer metadata".into());
                }
                let call = if let Some(step) = result {
                    // A call step: its successor reads the result as the
                    // value of the expression that holds the call.
                    ProgramStatement::CallResult {
                        aggregate_layout: None,
                        call: *step,
                        function_name: function.clone(),
                        arguments: arguments_values,
                        result_type: scalar_type(&callee.return_type)
                            .ok()
                            .map(|scalar| scalar.to_kernel_type()),
                        result_aggregate_layout: None,
                        result_pointee_constant: false,
                        callee: None,
                    }
                } else if let Type::Record { name } = &callee.return_type {
                    let flag = check(destination, name)?;
                    let layout = cx
                        .layouts
                        .get(name.as_str())
                        .ok_or("missing returned record layout")?
                        .to_kernel_aggregate_layout();
                    let (call, result) = cx.call_value(function, arguments_values);
                    let copy = crate::kernel::program_copy_aggregate(
                        crate::kernel::program_expression::variable(destination),
                        result,
                        layout,
                    );
                    program_seq(
                        assertion(flag, false),
                        program_seq(
                            program_seq(call, copy),
                            program_assign(
                                flag,
                                crate::kernel::program_expression::int32_literal(1),
                            ),
                        ),
                    )
                } else if callee.return_type == Type::Unit {
                    program_call(function, arguments_values)
                } else if let Some(&value_type) = cx.memory_values.get(destination.as_str()) {
                    // A memory-backed local, a borrowed enum or `Vec`,
                    // receives the result through a temporary stored to its
                    // object.
                    let temporary = cx.fresh_temporary()?;
                    let address = cx.address(&E::Local {
                        name: destination.clone(),
                    })?;
                    program_seq(
                        program_seq(
                            program_declare(&temporary, value_type),
                            cx.call_then_assign(&temporary, function, arguments_values),
                        ),
                        program_typed_store(
                            address,
                            crate::kernel::program_expression::variable(&temporary),
                            value_type,
                        ),
                    )
                } else {
                    cx.call_then_assign(destination, function, arguments_values)
                };
                program_seq(
                    accesses(&arguments.iter().collect::<Vec<_>>(), &live),
                    program_seq(prefix, program_seq(transfer, call)),
                )
            }
        };
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
            let mut statement = match s {
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
                    let slot = |name: &String| super::super::schema::Place {
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
                S::SharedArrayNext { iterator, option } => {
                    cx.shared_array_next(iterator, option)?
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
                S::EnumerateNext { iterator, option } => cx.enumerate_next(iterator, option)?,
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
                    option.as_deref(),
                    option_type,
                    payload.as_deref(),
                    *taken,
                )?,
                S::ChunkNext { iterator, option } => cx.chunk_next(iterator, option)?,
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
                // A new closure instance is the value its instance function
                // returns for the captured values.
                S::Assign {
                    target: E::Local { name },
                    value:
                        E::ClosureInstance {
                            function,
                            captures,
                            value_type,
                        },
                } => {
                    let closure = cx
                        .functions
                        .get(function.as_str())
                        .ok_or("Rust closure instance of an unknown closure")?;
                    let Type::FnPointer { parameters, result } = value_type else {
                        return Err("Rust closure instance requires a callable type".into());
                    };
                    if closure.captures != captures.len()
                        || closure.return_type != **result
                        || closure.parameters.len() != closure.captures + parameters.len()
                        || closure.parameters[closure.captures..]
                            .iter()
                            .zip(parameters)
                            .any(|(parameter, expected)| parameter.value_type != *expected)
                    {
                        return Err(format!(
                            "Rust closure instance of `{function}` does not have the closure's type"
                        ));
                    }
                    let mut checks = program_skip();
                    let mut values = Vec::new();
                    for capture in captures {
                        let (capture_checks, value) = cx.prepared_expr(capture)?;
                        checks = program_seq(checks, capture_checks);
                        values.push(value);
                    }
                    program_seq(
                        checks,
                        cx.call_then_assign(
                            name,
                            crate::languages::rust::names::closure_instance_name(function),
                            values,
                        ),
                    )
                }
                S::Assign {
                    target: E::Local { name },
                    value,
                } if !records.contains_key(name.as_str()) => cx.assign(name, value)?,
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
                            let (capture, name) = cx.capture_operand(value, &value_type)?;
                            checks = program_seq(checks, capture);
                            value = crate::kernel::program_expression::variable(name);
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
                    let flag = check(target, record)?;
                    let r = cx
                        .records
                        .get(record.as_str())
                        .ok_or("unknown constructor record")?;
                    if fields.len() != r.fields.len() {
                        return Err("partial record initialization".into());
                    }
                    let mut initialize = assertion(flag, false);
                    let record_fields = r.fields.clone();
                    for (value, field) in fields.iter().zip(&record_fields) {
                        let address = crate::kernel::program_expression::pointer_offset_bytes(
                            crate::kernel::program_expression::variable(target),
                            field.offset,
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
                    program_seq(
                        initialize,
                        program_assign(flag, crate::kernel::program_expression::int32_literal(1)),
                    )
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
                    let source_flag = check(source, record)?;
                    let target_flag = check(target, record)?;
                    let mut copy =
                        program_seq(assertion(source_flag, true), assertion(target_flag, false));
                    let record_fields = cx
                        .records
                        .get(record.as_str())
                        .ok_or("missing moved record")?
                        .fields
                        .clone();
                    for field in &record_fields {
                        let source_address =
                            crate::kernel::program_expression::pointer_offset_bytes(
                                crate::kernel::program_expression::variable(source),
                                field.offset,
                            );
                        let target_address =
                            crate::kernel::program_expression::pointer_offset_bytes(
                                crate::kernel::program_expression::variable(target),
                                field.offset,
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
                    program_seq(
                        copy,
                        program_seq(
                            if moving {
                                program_assign(
                                    source_flag,
                                    crate::kernel::program_expression::int32_literal(0),
                                )
                            } else {
                                program_skip()
                            },
                            program_assign(
                                target_flag,
                                crate::kernel::program_expression::int32_literal(1),
                            ),
                        ),
                    )
                }
                S::BeginStorage { local } if cx.local_arrays.contains(local) => {
                    let (length, element, _) = cx.arrays[local];
                    // Mint checked fresh automatic storage at the compiler's
                    // lifetime start, including each symbolic loop iteration.
                    // Re-entry retires the old object and checks live loans.
                    program_begin_aggregate_construction(
                        local.clone(),
                        AggregateLayout::new(
                            arrays::array_length(element, length)? * element.byte_width(),
                            element.byte_width(),
                            vec![],
                        ),
                    )
                }
                S::BeginStorage { local } => {
                    let record = records
                        .get(local.as_str())
                        .ok_or("unknown record storage start")?;
                    let flag = check(local, record)?;
                    // Plain values carry no destructor or borrowed authority.
                    // StorageLive starts a fresh lifetime even when a loop
                    // summary has abstracted the previous lifetime's flag.
                    // Drop/reference-bearing records retain their checked
                    // move/drop protocol; starting storage cannot erase it.
                    if check_copyable(cx, record).is_ok() {
                        program_seq(
                            program_begin_aggregate_construction(
                                local.clone(),
                                cx.layouts
                                    .get(*record)
                                    .ok_or("missing record storage layout")?
                                    .to_kernel_aggregate_layout(),
                            ),
                            program_assign(
                                flag,
                                crate::kernel::program_expression::int32_literal(0),
                            ),
                        )
                    } else {
                        program_skip()
                    }
                }
                S::EndStorage { local } => match records.get(local.as_str()) {
                    Some(record) => {
                        let flag = check(local, record)?;
                        if cx
                            .records
                            .get(record)
                            .ok_or("missing record")?
                            .destructor
                            .is_some()
                        {
                            assertion(flag, false)
                        } else {
                            program_assign(
                                flag,
                                crate::kernel::program_expression::int32_literal(0),
                            )
                        }
                    }
                    None => program_skip(),
                },
            };
            let inputs: Vec<&E> = match s {
                S::SliceSplit {
                    slice, midpoint, ..
                } => vec![slice, midpoint],
                S::SharedArrayInitialize { source, .. } => vec![source],
                S::Assert { condition, .. } => vec![condition],
                S::RangeInitialize { start, end, .. } => vec![start, end],
                S::Assign { target, value } => vec![target, value],
                S::Initialize { fields, .. } => fields.iter().collect(),
                _ => Vec::new(),
            };
            if let Some(forest) = &leases {
                super::scalar_leases::decorate(
                    forest,
                    super::super::borrow_frontiers::MirPoint {
                        block,
                        statement: statement_index,
                    },
                    &mut statement,
                )?;
            }
            statements = statements.then(Sited::at(
                site,
                program_seq(accesses(&inputs, &live), statement),
            ));
        }
        let prefix = leases.as_ref().map_or_else(program_skip, |forest| {
            super::scalar_leases::endings(
                forest,
                super::super::borrow_frontiers::MirPoint {
                    block,
                    statement: 0,
                },
            )
        });
        let terminal = Sited::at(mir.blocks[block].terminator_site, terminal);
        nodes[block] = Some(Sited::unsited(prefix).then(statements.then(terminal)));
    }
    let mut emitted = vec![false; mir.blocks.len()];
    let structured = region(
        cx,
        mir,
        &nodes,
        &flow,
        &mut emitted,
        0..mir.blocks.len(),
        leases.as_ref(),
        None,
    )?;
    Ok(Sited::unsited(declarations).then(structured))
}

fn successors(t: &T, exit: usize) -> Vec<usize> {
    match t {
        T::Goto { target }
        | T::Drop { target, .. }
        | T::Call { target, .. }
        | T::BoxNew { target, .. }
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
    flag: String,
}

impl LoopExits<'_> {
    fn leave(&self, block: usize) -> Option<ProgramStatement> {
        if block == self.exit {
            return Some(program_break());
        }
        let index = self.escapes.iter().position(|end| *end == block)?;
        Some(program_seq(
            program_assign(&self.flag, escape_code(index)),
            program_break(),
        ))
    }
}

/// The local recording which labeled escape left the loop headed at
/// `header`; zero while none has.
fn escape_flag(header: usize) -> String {
    format!("__rust_loop_escape_{header}")
}

/// The iterator the loop headed at `header` advances: the first `next` of a
/// supported iterator in its header blocks, then in its body.
fn loop_iterator(
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
            (E::Local { name }, T::Call { destination, .. }) => destination == name,
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
        if let Some(local) = user {
            return Some(RustLoopIterator {
                local,
                kind: K::User,
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
                    let inclusive = mir.locals.iter().any(|local| {
                        local.name == *iterator
                            && matches!(
                                local.value_type,
                                Type::Range {
                                    inclusive: true,
                                    ..
                                }
                            )
                    });
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
                local: local.clone(),
                kind,
            })
        })
}

fn escape_code(index: usize) -> ProgramExpression {
    crate::kernel::program_expression::int32_literal(index as u32 + 1)
}

fn region(
    cx: &mut Context<'_>,
    mir: &MirBody,
    nodes: &[Option<Sited>],
    flow: &flow::Flow,
    emitted: &mut [bool],
    bounds: std::ops::Range<usize>,
    leases: Option<&super::scalar_leases::Prepared>,
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
                flag: escape_flag(block),
            };
            // The loop's index is its place in preorder, the order its
            // `while` takes in the lowered body; its iterator is the one the
            // first `next` from its header on advances.
            let ordinal = cx.loop_iterators.len();
            cx.loop_iterators.push(None);
            cx.loop_iterators[ordinal] = loop_iterator(mir, block, loop_);
            let body = region(
                cx,
                mir,
                nodes,
                flow,
                emitted,
                loop_.body..block,
                leases,
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
                    emitted,
                    loop_.after..mir.blocks.len(),
                    leases,
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
            if !loop_.escapes.is_empty() {
                lowered = Sited::unsited(program_assign(
                    &inner.flag,
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
                            crate::kernel::program_expression::variable(&inner.flag),
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
                    emitted,
                    *then_target..join,
                    leases,
                    exits,
                )?;
                let no = region(
                    cx,
                    mir,
                    nodes,
                    flow,
                    emitted,
                    *else_target..join,
                    leases,
                    exits,
                )?;
                let branch =
                    if let Some(scope) = leases.and_then(|leases| leases.scopes.get(&block)) {
                        Sited::unsited(scope.operation(false)).then(Sited::branch(
                            site,
                            cx.condition(condition)?,
                            yes.then(Sited::unsited(scope.operation(true))),
                            no.then(Sited::unsited(scope.operation(true))),
                        ))
                    } else {
                        Sited::branch(site, cx.condition(condition)?, yes, no)
                    };
                result = result.then(branch);
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
                    cx, mir, nodes, flow, emitted, scrutinee, cases, *otherwise, join, leases,
                    exits, site,
                )?);
                block = join;
            }
            T::Goto { target }
            | T::Drop { target, .. }
            | T::Call { target, .. }
            | T::BoxNew { target, .. }
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
    emitted: &mut [bool],
    scrutinee: &E,
    cases: &[crate::languages::rust::schema::SwitchCase],
    otherwise: Option<usize>,
    join: usize,
    leases: Option<&super::scalar_leases::Prepared>,
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
            emitted,
            *target..join,
            leases,
            exits,
        )?);
    }
    // A match on an enum field of an enum, `Err(ParseError::Empty)`, tests a
    // local bound to that field, so the test splits as one on any enum local.
    let mut bound_field = None;
    let bound_local;
    let scrutinee = if let E::EnumField {
        name,
        variant,
        index,
        ..
    } = scrutinee
        && let Some(field_enum) = super::nested_enum_field_type(name, variant, *index)?
    {
        let local = cx.fresh_temporary()?;
        bound_field = Some(Sited::at(
            site,
            program_seq(
                program_declare_with_all_qualifiers(
                    &local,
                    field_enum.to_kernel_type(),
                    false,
                    false,
                    false,
                    false,
                ),
                program_assign(&local, cx.expr(scrutinee)?),
            ),
        ));
        bound_local = E::Local { name: local };
        &bound_local
    } else {
        scrutinee
    };
    let mut chain = None;
    for ((target, labels), body) in groups.iter().zip(bodies).rev() {
        let Some(rest) = chain else {
            chain = Some(body);
            continue;
        };
        if otherwise == Some(*target) {
            return Err("a Rust match's otherwise arm must come last".into());
        }
        let mut condition = None;
        for label in labels {
            // An enum arm tests its variant; the `if` it becomes steps and
            // splits as any other.
            let test = match label {
                SwitchLabel::Value { value } => {
                    crate::kernel::program_expression::equal(cx.expr(scrutinee)?, cx.expr(value)?)
                }
                SwitchLabel::Variant { name } => ProgramExpression::EnumIs {
                    value: Box::new(cx.expr(scrutinee)?),
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
    }
    let chain = chain.ok_or_else(|| "Rust match without arms".to_string())?;
    Ok(match bound_field {
        Some(bound) => bound.then(chain),
        None => chain,
    })
}

fn accesses(expressions: &[&E], live: &BTreeMap<&str, String>) -> ProgramStatement {
    let mut roots = BTreeSet::new();
    let mut pending = expressions.to_vec();
    while let Some(expression) = pending.pop() {
        match expression {
            E::Local { name } => {
                if let Some(flag) = live.get(name.as_str()) {
                    roots.insert(flag.as_str());
                }
            }
            E::Binary { left, right, .. } => {
                pending.push(left);
                pending.push(right);
            }
            E::Index { slice, index } => {
                pending.push(slice);
                pending.push(index);
            }
            E::Array { elements } => pending.extend(elements),
            E::Repeat { value, .. } => pending.push(value),
            E::Not { value }
            | E::BitwiseNot { value, .. }
            | E::Cast { value, .. }
            | E::IntegerFrom { value, .. } => pending.push(value),
            E::Borrow { place, .. } => pending.push(place),
            E::SliceLength { slice } => pending.push(slice),
            E::ArrayToSlice { array, .. } => pending.push(array),
            E::Deref { reference, .. } => pending.push(reference),
            E::Field { base, .. } => pending.push(base),
            E::Call { arguments, .. } => pending.extend(arguments),
            _ => {}
        }
    }
    roots.into_iter().fold(program_skip(), |s, flag| {
        program_seq(
            s,
            program_assert(crate::kernel::program_expression::equal(
                crate::kernel::program_expression::variable(flag),
                crate::kernel::program_expression::int32_literal(1),
            )),
        )
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
                references: BTreeMap::new(),
                shared_array_iterators: BTreeMap::new(),
                ranges: BTreeMap::new(),
                enumerated: BTreeSet::new(),
                shared_array_options: BTreeMap::new(),
                shared_scalar_slices: BTreeMap::new(),
                mir_chunk_iterators: BTreeSet::new(),
                chunk_options: BTreeSet::new(),
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
                next_temporary: 0,
                next_call_result: std::cell::Cell::new(0),
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
                &mut emitted,
                0..mir.blocks.len(),
                None,
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
