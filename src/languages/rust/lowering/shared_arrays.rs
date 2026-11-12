//! Scalar shared iteration: the iterator holds the slice it was built from,
//! `base` and `length`, set once, and how many elements remain. Each `next`
//! yields `base + (length - remaining)`, so where the iterator stands in its
//! slice follows from `remaining` alone: a proof reads `iter.len()`.
use super::*;
/// The cursor's pointer type, as a Rust reference to the element lowers.
fn pointer_type(element: &Type) -> Result<CType, String> {
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
pub(super) fn shared_array_position(iterator: &str) -> CExpression {
    c_add(
        c_variable(format!("{iterator}_base")),
        c_subtract(
            c_variable(format!("{iterator}_length")),
            c_variable(format!("{iterator}_remaining")),
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
    arguments: Vec<CExpression>,
) -> Result<CStatement, String> {
    let element = element
        .scalar_name()
        .ok_or("shared array iterator requires an integer element")?;
    Ok(c_call_assign(
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
    ) -> Result<CStatement, String> {
        pointer_type(element)?;
        if !self.locals.insert(name.into()) {
            return Err("shared iterator state identity collision".into());
        }
        self.library_slice_iterators
            .insert(name.into(), element.clone());
        let value_type = CType::Parameter(super::slice_iter_type(element)?);
        // Only the iterator a `next(&mut it)` borrows lives in memory; one
        // that is only built and moved holds its value.
        if !self.library_next_options.contains_key(name) {
            return Ok(c_declare(name, value_type));
        }
        self.memory_values.insert(name.into(), value_type);
        Ok(c_begin_aggregate_construction(
            name.to_string(),
            CAggregateLayout::holding_value(value_type),
        ))
    }
    /// Storage of the `Option<&T>` a library slice iterator's `next()`
    /// returns: a value of the library's `Option` at the reference.
    pub(super) fn library_slice_option_storage(
        &mut self,
        name: &str,
        element: &Type,
    ) -> Result<CStatement, String> {
        let spelling = element
            .scalar_name()
            .ok_or("shared array iterator requires an integer element")?;
        if !self.locals.insert(name.into()) {
            return Err("shared iterator state identity collision".into());
        }
        self.library_slice_options
            .insert(name.into(), element.clone());
        let option = super::super::standard_library::option_reference_name(spelling);
        Ok(c_declare(name, CType::Parameter(EnumTypes::get(&option)?)))
    }
    /// The `next(&mut it)` call a test of the library iterator `iterator`
    /// makes, assigning the `Option` it returns. The importer places the
    /// call ahead of the test that reads its `Option`, as the compiler's
    /// `match` on `next()` does.
    pub(super) fn library_slice_next_call(&mut self, iterator: &str) -> Option<CStatement> {
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
        assign: impl FnOnce(String) -> Result<CStatement, String>,
    ) -> Result<CStatement, String> {
        let Some(&value_type) = self.memory_values.get(target) else {
            return assign(target.to_string());
        };
        let temporary = self.fresh_temporary()?;
        let address = self.address(&E::Local {
            name: target.to_string(),
        })?;
        Ok(c_seq(
            c_seq(
                c_declare(&temporary, value_type),
                assign(temporary.clone())?,
            ),
            c_typed_store(address, c_variable(&temporary), value_type),
        ))
    }
    pub(super) fn shared_array_storage(
        &mut self,
        name: &str,
        element: &Type,
        option: bool,
    ) -> Result<CStatement, String> {
        let pointer = pointer_type(element)?;
        let element = scalar_type(element)?.to_kernel_type();
        if !self.locals.insert(name.into()) {
            return Err("shared iterator state identity collision".into());
        }
        let fields = if option {
            self.shared_array_options.insert(name.into(), element);
            vec![("some", CType::Int32, false), ("pointer", pointer, true)]
        } else {
            self.shared_array_iterators.insert(name.into(), element);
            vec![
                ("base", pointer, true),
                // The lengths are `usize`s.
                ("length", CType::UInt64, false),
                ("remaining", CType::UInt64, false),
                ("live", CType::Int32, false),
            ]
        };
        let mut result = c_skip();
        for (suffix, ty, constant) in fields {
            let field = format!("{name}_{suffix}");
            if !self.locals.insert(field.clone()) {
                return Err("shared iterator metadata identity collision".into());
            }
            result = c_seq(
                result,
                c_declare_with_all_qualifiers(field.clone(), ty, false, false, false, constant),
            );
            if suffix == "live" || suffix == "some" {
                result = c_seq(result, c_assign(field, c_int32_literal(0)));
            }
        }
        Ok(result)
    }
    pub(super) fn shared_array_initialize(
        &mut self,
        target: &str,
        source: &E,
    ) -> Result<CStatement, String> {
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
                    vec![c_variable(&p), c_variable(&l)],
                )
            };
            return Ok(c_seq(
                c_seq(p_capture, l_capture),
                self.store_library_iterator(target, call)?,
            ));
        }
        let begin = |length: CExpression| {
            c_seq(
                c_assign(format!("{target}_base"), c_variable(&p)),
                c_seq(
                    c_assign(format!("{target}_length"), length.clone()),
                    c_seq(
                        c_assign(format!("{target}_remaining"), length),
                        c_assign(format!("{target}_live"), c_int32_literal(1)),
                    ),
                ),
            )
        };
        // A held range states its own extent limit, so the count is the
        // length as it is and nothing is asserted about it.
        Ok(c_seq(
            c_assert(c_equal(
                c_variable(format!("{target}_live")),
                c_int32_literal(0),
            )),
            c_seq(p_capture, c_seq(l_capture, begin(c_variable(&l)))),
        ))
    }
    pub(super) fn shared_array_live(&self, iterator: &str) -> Result<CStatement, String> {
        if !self.shared_array_iterators.contains_key(iterator) {
            return Err("unknown shared iterator".into());
        }
        Ok(c_assert(c_equal(
            c_variable(format!("{iterator}_live")),
            c_int32_literal(1),
        )))
    }
    pub(super) fn shared_array_has_next(&self, iterator: &str) -> Result<CExpression, String> {
        if self.library_slice_iterators.contains_key(iterator) {
            let option = self
                .library_next_options
                .get(iterator)
                .ok_or("library slice iterator test without its next() call")?;
            return Ok(CExpression::EnumIs {
                value: Box::new(c_variable(option)),
                variant: "Some".into(),
            });
        }
        if !self.shared_array_iterators.contains_key(iterator) {
            return Err("unknown shared iterator".into());
        }
        Ok(c_less_than(
            c_uint64_literal(0),
            c_variable(format!("{iterator}_remaining")),
        ))
    }
    pub(super) fn shared_array_move(
        &mut self,
        target: &str,
        source: &str,
    ) -> Result<CStatement, String> {
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
                return Ok(c_assign(target, value));
            };
            let address = self.address(&E::Local {
                name: target.to_string(),
            })?;
            return Ok(c_typed_store(address, value, value_type));
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
        let mut result = c_seq(
            self.shared_array_live(source)?,
            c_assert(c_equal(
                c_variable(format!("{target}_live")),
                c_int32_literal(0),
            )),
        );
        for suffix in ["base", "length", "remaining"] {
            result = c_seq(
                result,
                c_assign(
                    format!("{target}_{suffix}"),
                    c_variable(format!("{source}_{suffix}")),
                ),
            );
        }
        Ok(c_seq(
            result,
            c_seq(
                c_assign(format!("{source}_live"), c_int32_literal(0)),
                c_assign(format!("{target}_live"), c_int32_literal(1)),
            ),
        ))
    }
    pub(super) fn shared_array_next(
        &self,
        iterator: &str,
        option: &str,
    ) -> Result<CStatement, String> {
        self.shared_array_next_with(iterator, option, c_skip())
    }
    /// [`Self::shared_array_next`], also running `yielded` when it yields,
    /// before the iterator advances.
    pub(super) fn shared_array_next_with(
        &self,
        iterator: &str,
        option: &str,
        yielded: CStatement,
    ) -> Result<CStatement, String> {
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
        let some = c_seq(
            c_assign(format!("{option}_some"), c_int32_literal(1)),
            c_seq(
                c_assign(format!("{option}_pointer"), shared_array_position(iterator)),
                c_seq(
                    yielded,
                    c_assign(
                        &remaining,
                        c_subtract(c_variable(&remaining), c_uint64_literal(1)),
                    ),
                ),
            ),
        );
        Ok(c_seq(
            self.shared_array_live(iterator)?,
            c_if(
                self.shared_array_has_next(iterator)?,
                some,
                c_assign(format!("{option}_some"), c_int32_literal(0)),
            ),
        ))
    }
}
