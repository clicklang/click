//! Scalar shared iteration: the iterator holds the slice it was built from,
//! `base` and `length`, set once, and how many elements remain. Each `next`
//! yields `base + (length - remaining)`, so where the iterator stands in its
//! slice follows from `remaining` alone: a proof reads `iter.len()`.
use super::*;
/// The cursor's pointer type, as a Rust reference to the element lowers.
fn pointer_type(element: &Type) -> Result<ProgramType, String> {
    if !element.is_integer() {
        return Err("shared array iterator requires an integer element".into());
    }
    Ok(scalar_type(&Type::Reference {
        mutable: false,
        pointee: Box::new(element.clone()),
    })?
    .to_kernel_type())
}
/// The element a slice iterator yields next: `base + (length - remaining)`.
pub(super) fn shared_array_position(iterator: &str) -> ProgramExpression {
    crate::kernel::program_expression::add(
        crate::kernel::program_expression::variable(format!("{iterator}_base")),
        crate::kernel::program_expression::subtract(
            crate::kernel::program_expression::variable(format!("{iterator}_length")),
            crate::kernel::program_expression::variable(format!("{iterator}_remaining")),
        ),
    )
}

/// Assigns `target` the result of the slice iterator operation
/// `operation`, at element type `element`, on `arguments`: one of the Rust
/// calls `<[T]>::iter` and `Iterator::next`.
fn slice_iter_call(
    target: String,
    operation: &str,
    element: &Type,
    arguments: Vec<ProgramExpression>,
) -> Result<ProgramStatement, String> {
    let element = element
        .scalar_name()
        .ok_or("shared array iterator requires an integer element")?;
    Ok(program_call_assign(
        target,
        super::super::standard_library::slice_iter_function(operation, element),
        arguments,
    ))
}

impl Context<'_> {
    /// Storage of a slice iterator that is one value of the library's
    /// `SliceIter`. `next` borrows it mutably, so its value lives in its
    /// object's memory, as a borrowed `Vec`'s does.
    pub(super) fn library_slice_iterator_storage(
        &mut self,
        name: &str,
        element: &Type,
    ) -> Result<ProgramStatement, String> {
        pointer_type(element)?;
        if !self.locals.insert(name.into()) {
            return Err("shared iterator state identity collision".into());
        }
        self.library_slice_iterators
            .insert(name.into(), element.clone());
        let value_type = ProgramType::Parameter(super::slice_iter_type(element)?);
        // Only the iterator a `next(&mut it)` borrows lives in memory; one
        // that is only built and moved holds its value.
        if !self.library_next_options.contains_key(name) {
            return Ok(program_declare(name, value_type));
        }
        self.memory_values.insert(name.into(), value_type);
        Ok(program_begin_aggregate_construction(
            name.to_string(),
            AggregateLayout::holding_value(value_type),
        ))
    }
    /// Storage of the `Option<&T>` a library slice iterator's `next()`
    /// returns: a value of the library's `Option` at the reference.
    pub(super) fn library_slice_option_storage(
        &mut self,
        name: &str,
        element: &Type,
    ) -> Result<ProgramStatement, String> {
        let spelling = element
            .scalar_name()
            .ok_or("shared array iterator requires an integer element")?;
        if !self.locals.insert(name.into()) {
            return Err("shared iterator state identity collision".into());
        }
        self.library_slice_options
            .insert(name.into(), element.clone());
        let option = super::super::standard_library::option_reference_name(spelling);
        Ok(program_declare(
            name,
            ProgramType::Parameter(EnumTypes::get(&option)?),
        ))
    }
    /// The `next(&mut it)` call a test of the library iterator `iterator`
    /// makes, assigning the `Option` it returns. The importer places the
    /// call ahead of the test that reads its `Option`, as the compiler's
    /// `match` on `next()` does.
    pub(super) fn library_slice_next_call(&mut self, iterator: &str) -> Option<ProgramStatement> {
        let element = self.library_slice_iterators.get(iterator)?.clone();
        let option = self.library_next_options.get(iterator)?.clone();
        let address = self
            .address(&E::Local {
                name: iterator.to_string(),
            })
            .ok()?;
        slice_iter_call(option, "next", &element, vec![address]).ok()
    }
    /// Stores the iterator value `assign` computes into a temporary into the
    /// memory-backed library iterator `target`.
    fn store_library_iterator(
        &mut self,
        target: &str,
        assign: impl FnOnce(String) -> Result<ProgramStatement, String>,
    ) -> Result<ProgramStatement, String> {
        let Some(&value_type) = self.memory_values.get(target) else {
            return assign(target.to_string());
        };
        let temporary = self.fresh_temporary()?;
        let address = self.address(&E::Local {
            name: target.to_string(),
        })?;
        Ok(program_seq(
            program_seq(
                program_declare(&temporary, value_type),
                assign(temporary.clone())?,
            ),
            program_typed_store(
                address,
                crate::kernel::program_expression::variable(&temporary),
                value_type,
            ),
        ))
    }
    pub(super) fn shared_array_storage(
        &mut self,
        name: &str,
        element: &Type,
        option: bool,
    ) -> Result<ProgramStatement, String> {
        let pointer = pointer_type(element)?;
        let element = scalar_type(element)?.to_kernel_type();
        if !self.locals.insert(name.into()) {
            return Err("shared iterator state identity collision".into());
        }
        let fields = if option {
            self.shared_array_options.insert(name.into(), element);
            vec![
                ("some", ProgramType::Int32, false),
                ("pointer", pointer, true),
            ]
        } else {
            self.shared_array_iterators.insert(name.into(), element);
            vec![
                ("base", pointer, true),
                // The lengths are `usize`s.
                ("length", ProgramType::UInt64, false),
                ("remaining", ProgramType::UInt64, false),
                ("live", ProgramType::Int32, false),
            ]
        };
        let mut result = program_skip();
        for (suffix, ty, constant) in fields {
            let field = format!("{name}_{suffix}");
            if !self.locals.insert(field.clone()) {
                return Err("shared iterator metadata identity collision".into());
            }
            result = program_seq(
                result,
                program_declare_with_all_qualifiers(
                    field.clone(),
                    ty,
                    false,
                    false,
                    false,
                    constant,
                ),
            );
            if suffix == "live" || suffix == "some" {
                result = program_seq(
                    result,
                    program_assign(field, crate::kernel::program_expression::int32_literal(0)),
                );
            }
        }
        Ok(result)
    }
    pub(super) fn shared_array_initialize(
        &mut self,
        target: &str,
        source: &E,
    ) -> Result<ProgramStatement, String> {
        let library = self.library_slice_iterators.get(target).cloned();
        let expected = match &library {
            Some(element) => scalar_type(element)?.to_kernel_type(),
            None => *self
                .shared_array_iterators
                .get(target)
                .ok_or("unknown shared iterator")?,
        };
        let (pointer, length, element) = self.indexed_parts(source)?;
        if element != expected {
            return Err("shared array iterator source element mismatch".into());
        }
        let (p_capture, p) = self.capture_operand(
            pointer,
            &Type::Reference {
                mutable: false,
                pointee: Box::new(
                    indexed_element_type(element)
                        .ok_or("shared array iterator requires an integer element")?,
                ),
            },
        )?;
        let (l_capture, l) = self.capture_operand(length, &Type::Usize)?;
        if let Some(element) = library {
            let call = |temporary: String| {
                slice_iter_call(
                    temporary,
                    "iter",
                    &element,
                    vec![
                        crate::kernel::program_expression::variable(&p),
                        crate::kernel::program_expression::variable(&l),
                    ],
                )
            };
            return Ok(program_seq(
                program_seq(p_capture, l_capture),
                self.store_library_iterator(target, call)?,
            ));
        }
        let begin = |length: ProgramExpression| {
            program_seq(
                program_assign(
                    format!("{target}_base"),
                    crate::kernel::program_expression::variable(&p),
                ),
                program_seq(
                    program_assign(format!("{target}_length"), length.clone()),
                    program_seq(
                        program_assign(format!("{target}_remaining"), length),
                        program_assign(
                            format!("{target}_live"),
                            crate::kernel::program_expression::int32_literal(1),
                        ),
                    ),
                ),
            )
        };
        // A held range states its own extent limit, so the count is the
        // length as it is and nothing is asserted about it.
        Ok(program_seq(
            program_assert(crate::kernel::program_expression::equal(
                crate::kernel::program_expression::variable(format!("{target}_live")),
                crate::kernel::program_expression::int32_literal(0),
            )),
            program_seq(
                p_capture,
                program_seq(
                    l_capture,
                    begin(crate::kernel::program_expression::variable(&l)),
                ),
            ),
        ))
    }
    pub(super) fn shared_array_live(&self, iterator: &str) -> Result<ProgramStatement, String> {
        if !self.shared_array_iterators.contains_key(iterator) {
            return Err("unknown shared iterator".into());
        }
        Ok(program_assert(crate::kernel::program_expression::equal(
            crate::kernel::program_expression::variable(format!("{iterator}_live")),
            crate::kernel::program_expression::int32_literal(1),
        )))
    }
    pub(super) fn shared_array_has_next(
        &self,
        iterator: &str,
    ) -> Result<ProgramExpression, String> {
        if self.library_slice_iterators.contains_key(iterator) {
            let option = self
                .library_next_options
                .get(iterator)
                .ok_or("library slice iterator test without its next() call")?;
            return Ok(ProgramExpression::EnumIs {
                value: Box::new(crate::kernel::program_expression::variable(option)),
                variant: "Some".into(),
            });
        }
        if !self.shared_array_iterators.contains_key(iterator) {
            return Err("unknown shared iterator".into());
        }
        Ok(crate::kernel::program_expression::less_than(
            crate::kernel::program_expression::uint64_literal(0),
            crate::kernel::program_expression::variable(format!("{iterator}_remaining")),
        ))
    }
    pub(super) fn shared_array_move(
        &mut self,
        target: &str,
        source: &str,
    ) -> Result<ProgramStatement, String> {
        if let (Some(to), Some(from)) = (
            self.library_slice_iterators.get(target),
            self.library_slice_iterators.get(source),
        ) {
            if target == source || to != from {
                return Err("invalid shared iterator move".into());
            }
            let value = self.expr(&E::Local {
                name: source.to_string(),
            })?;
            let Some(&value_type) = self.memory_values.get(target) else {
                return Ok(program_assign(target, value));
            };
            let address = self.address(&E::Local {
                name: target.to_string(),
            })?;
            return Ok(program_typed_store(address, value, value_type));
        }
        if self.library_slice_iterators.contains_key(source) {
            return Err(
                "enumerate over a slice iterator imported as a library value is not supported yet"
                    .into(),
            );
        }
        if target == source
            || !self.shared_array_iterators.contains_key(target)
            || self.shared_array_iterators.get(target) != self.shared_array_iterators.get(source)
        {
            return Err("invalid shared iterator move".into());
        }
        let mut result = program_seq(
            self.shared_array_live(source)?,
            program_assert(crate::kernel::program_expression::equal(
                crate::kernel::program_expression::variable(format!("{target}_live")),
                crate::kernel::program_expression::int32_literal(0),
            )),
        );
        for suffix in ["base", "length", "remaining"] {
            result = program_seq(
                result,
                program_assign(
                    format!("{target}_{suffix}"),
                    crate::kernel::program_expression::variable(format!("{source}_{suffix}")),
                ),
            );
        }
        Ok(program_seq(
            result,
            program_seq(
                program_assign(
                    format!("{source}_live"),
                    crate::kernel::program_expression::int32_literal(0),
                ),
                program_assign(
                    format!("{target}_live"),
                    crate::kernel::program_expression::int32_literal(1),
                ),
            ),
        ))
    }
    pub(super) fn shared_array_next(
        &self,
        iterator: &str,
        option: &str,
    ) -> Result<ProgramStatement, String> {
        self.shared_array_next_with(iterator, option, program_skip())
    }
    /// [`Self::shared_array_next`], also running `yielded` when it yields,
    /// before the iterator advances.
    pub(super) fn shared_array_next_with(
        &self,
        iterator: &str,
        option: &str,
        yielded: ProgramStatement,
    ) -> Result<ProgramStatement, String> {
        if self.library_slice_iterators.contains_key(iterator) {
            // `next(&mut it)` ran ahead of the test that reads its `Option`
            // (`library_slice_next_call`); this edge only continues.
            if self.library_next_options.get(iterator).map(String::as_str) != Some(option) {
                return Err("shared iterator Option element mismatch".into());
            }
            return Ok(yielded);
        }
        if !self.shared_array_iterators.contains_key(iterator)
            || self.shared_array_iterators.get(iterator) != self.shared_array_options.get(option)
        {
            return Err("shared iterator Option element mismatch".into());
        }
        let remaining = format!("{iterator}_remaining");
        let some = program_seq(
            program_assign(
                format!("{option}_some"),
                crate::kernel::program_expression::int32_literal(1),
            ),
            program_seq(
                program_assign(format!("{option}_pointer"), shared_array_position(iterator)),
                program_seq(
                    yielded,
                    program_assign(
                        &remaining,
                        crate::kernel::program_expression::subtract(
                            crate::kernel::program_expression::variable(&remaining),
                            crate::kernel::program_expression::uint64_literal(1),
                        ),
                    ),
                ),
            ),
        );
        Ok(program_seq(
            self.shared_array_live(iterator)?,
            program_if(
                self.shared_array_has_next(iterator)?,
                some,
                program_assign(
                    format!("{option}_some"),
                    crate::kernel::program_expression::int32_literal(0),
                ),
            ),
        ))
    }
}
