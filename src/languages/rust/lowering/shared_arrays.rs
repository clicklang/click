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

/// Assigns `target` the result of the library slice iterator operation
/// `operation`, at element type `element`, on `arguments`.
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
    /// `SliceIter`. A terminator's condition is an expression, so the number
    /// of elements left is read into a local of its own.
    pub(super) fn library_slice_iterator_storage(
        &mut self,
        name: &str,
        element: &Type,
    ) -> Result<CStatement, String> {
        pointer_type(element)?;
        let left = format!("{name}_left");
        if !self.locals.insert(name.into()) || !self.locals.insert(left.clone()) {
            return Err("shared iterator state identity collision".into());
        }
        self.library_slice_iterators
            .insert(name.into(), element.clone());
        Ok(c_seq(
            c_declare(name, CType::Parameter(super::slice_iter_type(element)?)),
            c_declare(left, CType::UInt64),
        ))
    }
    /// Reads how many elements the library iterator will still yield into
    /// its `_left` local, when `iterator` is one. Each test of it reads it
    /// afresh first, and the `next()` the test leads to uses that read.
    pub(super) fn library_slice_read_left(&self, iterator: &str) -> Option<CStatement> {
        let element = self.library_slice_iterators.get(iterator)?;
        slice_iter_call(
            format!("{iterator}_left"),
            "len",
            element,
            vec![c_variable(iterator)],
        )
        .ok()
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
            return Ok(c_seq(
                c_seq(p_capture, l_capture),
                slice_iter_call(
                    target.to_string(),
                    "new",
                    &element,
                    vec![c_variable(&p), c_variable(&l)],
                )?,
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
            return Ok(c_less_than(
                c_uint64_literal(0),
                c_variable(format!("{iterator}_left")),
            ));
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
        &self,
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
            return Ok(c_assign(target, c_variable(source)));
        }
        // An enumerated iterator keeps the hidden-state model; one built
        // from a library iterator starts from what that iterator has left.
        if let Some(element) = self.library_slice_iterators.get(source) {
            if !self.shared_array_iterators.contains_key(target) {
                return Err("invalid shared iterator move".into());
            }
            let value = || vec![c_variable(source)];
            return Ok(c_seq(
                c_assert(c_equal(
                    c_variable(format!("{target}_live")),
                    c_int32_literal(0),
                )),
                c_seq(
                    slice_iter_call(format!("{target}_base"), "as_ptr", element, value())?,
                    c_seq(
                        slice_iter_call(format!("{target}_length"), "len", element, value())?,
                        c_seq(
                            c_assign(
                                format!("{target}_remaining"),
                                c_variable(format!("{target}_length")),
                            ),
                            c_assign(format!("{target}_live"), c_int32_literal(1)),
                        ),
                    ),
                ),
            ));
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
        if let Some(element) = self.library_slice_iterators.get(iterator) {
            if self.shared_array_options.get(option)
                != Some(&scalar_type(element)?.to_kernel_type())
            {
                return Err("shared iterator Option element mismatch".into());
            }
            let value = || vec![c_variable(iterator)];
            // `next()`: the first element still to come, then the iterator
            // after it. The test that led here read `_left` from this
            // iterator.
            let some = c_seq(
                c_assign(format!("{option}_some"), c_int32_literal(1)),
                c_seq(
                    slice_iter_call(format!("{option}_pointer"), "as_ptr", element, value())?,
                    c_seq(
                        yielded,
                        slice_iter_call(iterator.to_string(), "after_next", element, value())?,
                    ),
                ),
            );
            return Ok(c_if(
                self.shared_array_has_next(iterator)?,
                some,
                c_assign(format!("{option}_some"), c_int32_literal(0)),
            ));
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
