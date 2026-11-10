//! Shared `ChunksExact` state. The tail is fixed at construction; consuming
//! chunks advances only the cursor and remaining complete-byte range.
use super::*;

/// Whether a whole chunk of `size` bytes is left in `remaining`. Both are
/// `usize` byte counts.
fn chunk_has_whole(remaining: CExpression, size: CExpression) -> CExpression {
    c_and(
        c_less_than(c_uint64_literal(0), remaining.clone()),
        c_less_equal(size, remaining),
    )
}

impl Context<'_> {
    pub(super) fn chunk_declare(
        &mut self,
        iterator: &str,
        slice: &E,
        size: &E,
    ) -> Result<CStatement, String> {
        if !matches!(slice, E::ChunkRemainder { .. })
            && !matches!(slice, E::Local { name } if self.slices.get(name).is_some_and(|(_, shared)| *shared))
        {
            return Err("chunks_exact requires a shared byte-slice local".into());
        }
        let (pointer, length) = self.slice_parts(slice)?;
        let (pointer_capture, pointer_name) = self.capture_operand(
            pointer,
            &Type::Reference {
                mutable: false,
                pointee: Box::new(Type::U8),
            },
        )?;
        let (length_capture, length_name) = self.capture_operand(length, &Type::Usize)?;
        let (size_prefix, size_value) = self.prepared_expr(size)?;
        let cursor = format!("{iterator}_cursor");
        let remaining = format!("{iterator}_remaining");
        let size_name = format!("{iterator}_size");
        let tail = format!("{iterator}_tail");
        let tail_len = format!("{iterator}_tail_len");
        if !self.chunk_iterators.insert(iterator.into()) {
            return Err("duplicate Rust chunk iterator".into());
        }
        for name in [iterator, &cursor, &remaining, &size_name, &tail, &tail_len] {
            if !self.locals.insert(name.into()) {
                return Err("Rust chunk iterator state identity collision".into());
            }
        }
        let mut result = c_seq(pointer_capture, c_seq(length_capture, size_prefix));
        for (name, value_type, constant) in [
            (&cursor, CType::UInt8Pointer, true),
            (&remaining, CType::UInt64, false),
            (&size_name, CType::UInt64, false),
            (&tail, CType::UInt8Pointer, true),
            (&tail_len, CType::UInt64, false),
        ] {
            result = c_seq(
                result,
                c_declare_with_all_qualifiers(name, value_type, false, false, false, constant),
            );
        }
        self.chunk_initialize_values(result, iterator, size_value, &pointer_name, &length_name)
    }

    fn chunk_initialize_values(
        &self,
        mut result: CStatement,
        iterator: &str,
        size_value: CExpression,
        pointer_name: &str,
        length_name: &str,
    ) -> Result<CStatement, String> {
        let cursor = format!("{iterator}_cursor");
        let remaining = format!("{iterator}_remaining");
        let size_name = format!("{iterator}_size");
        let tail = format!("{iterator}_tail");
        let tail_len = format!("{iterator}_tail_len");
        result = c_seq(result, c_assign(&size_name, size_value));
        result = c_seq(
            result,
            c_labeled_assert(
                c_not(c_equal(c_variable(&size_name), c_uint64_literal(0))),
                "Rust chunks_exact zero size panic check",
            ),
        );
        result = c_seq(
            result,
            c_assign(
                &tail_len,
                c_remainder(c_variable(length_name), c_variable(&size_name)),
            ),
        );
        // Both lengths are bounded by the original length. Preserve full-width
        // chunk sizes: a size larger than the input yields only a remainder.
        result = c_seq(
            result,
            c_assign(
                &remaining,
                c_subtract(c_variable(length_name), c_variable(&tail_len)),
            ),
        );
        result = c_seq(result, c_assign(&cursor, c_variable(pointer_name)));
        result = c_seq(
            result,
            c_assign(
                &tail,
                c_add(c_variable(pointer_name), c_variable(&remaining)),
            ),
        );
        Ok(result)
    }

    pub(super) fn chunk_for(
        &mut self,
        iterator: &str,
        binding: &super::super::schema::Place,
        body: &[S],
    ) -> Result<CStatement, String> {
        if !self.chunk_iterators.contains(iterator)
            || binding.value_type != (Type::ByteSlice { mutable: false })
        {
            return Err(
                "Rust chunk loop requires a ChunksExact iterator yielding shared byte slices"
                    .into(),
            );
        }
        let cursor = format!("{iterator}_cursor");
        let remaining = format!("{iterator}_remaining");
        let size = format!("{iterator}_size");
        let length = format!("{}_len", binding.name);
        for name in [&binding.name, &length] {
            if !self.locals.insert(name.clone()) {
                return Err("Rust chunk binding identity collision".into());
            }
        }
        self.slices
            .insert(binding.name.clone(), (length.clone(), true));
        let mut next = c_declare_with_all_qualifiers(
            &binding.name,
            CType::UInt8Pointer,
            false,
            false,
            false,
            true,
        );
        next = c_seq(next, c_declare(&length, CType::UInt64));
        next = c_seq(next, c_assign(&binding.name, c_variable(&cursor)));
        next = c_seq(next, c_assign(&length, c_variable(&size)));
        let step = c_variable(&size);
        next = c_seq(
            next,
            c_assign(&cursor, c_add(c_variable(&cursor), step.clone())),
        );
        next = c_seq(
            next,
            c_assign(&remaining, c_subtract(c_variable(&remaining), step)),
        );
        let source_body = self.body(body)?;
        Ok(c_while(
            chunk_has_whole(c_variable(&remaining), c_variable(&size)),
            Vec::new(),
            c_seq(next, source_body),
        ))
    }
}

impl Context<'_> {
    pub(super) fn chunk_storage(&mut self, name: &str, option: bool) -> Result<CStatement, String> {
        if !self.locals.insert(name.into()) {
            return Err("chunk state identity collision".into());
        }
        let fields = if option {
            self.chunk_options.insert(name.into());
            vec![
                ("some", CType::Int32, false),
                ("pointer", CType::UInt8Pointer, true),
                ("len", CType::UInt64, false),
            ]
        } else if library_iterators() {
            // One value of the library's `ChunksExact<uint8>`. A slice is
            // still a pointer and a length here, so the fixed remainder is
            // read once into two locals, and a terminator's condition is an
            // expression, so the number of chunks left is read into one.
            self.chunk_iterators.insert(name.into());
            self.mir_chunk_iterators.insert(name.into());
            let mut result = c_declare(name, CType::Parameter(super::chunks_exact_type()));
            for (suffix, ty, constant) in [
                ("left", CType::UInt64, false),
                ("tail", CType::UInt8Pointer, true),
                ("tail_len", CType::UInt64, false),
            ] {
                let field = format!("{name}_{suffix}");
                if !self.locals.insert(field.clone()) {
                    return Err("chunk metadata identity collision".into());
                }
                result = c_seq(
                    result,
                    c_declare_with_all_qualifiers(field, ty, false, false, false, constant),
                );
            }
            return Ok(result);
        } else {
            self.chunk_iterators.insert(name.into());
            self.mir_chunk_iterators.insert(name.into());
            vec![
                ("cursor", CType::UInt8Pointer, true),
                ("remaining", CType::UInt64, false),
                ("size", CType::UInt64, false),
                ("tail", CType::UInt8Pointer, true),
                ("tail_len", CType::UInt64, false),
                ("live", CType::Int32, false),
            ]
        };
        let mut result = c_skip();
        for (suffix, ty, constant) in fields {
            let field = format!("{name}_{suffix}");
            if !self.locals.insert(field.clone()) {
                return Err("chunk metadata identity collision".into());
            }
            result = c_seq(
                result,
                c_declare_with_all_qualifiers(field, ty, false, false, false, constant),
            );
        }
        Ok(c_seq(
            result,
            c_assign(
                format!("{name}_{}", if option { "some" } else { "live" }),
                c_int32_literal(0),
            ),
        ))
    }
    fn chunk_live(&self, iterator: &str) -> Result<CStatement, String> {
        if !self.mir_chunk_iterators.contains(iterator) {
            return Err("unknown MIR chunk iterator".into());
        }
        // The library model keeps no liveness flag: the compiler has
        // already checked each use is of a live iterator.
        if library_iterators() {
            return Ok(c_skip());
        }
        Ok(c_assert(c_equal(
            c_variable(format!("{iterator}_live")),
            c_int32_literal(1),
        )))
    }
    pub(super) fn chunk_initialize_mir(
        &mut self,
        iterator: &str,
        slice: &E,
        size: &E,
    ) -> Result<CStatement, String> {
        if !matches!(slice, E::Local { name } if self.slices.get(name).is_some_and(|(_, shared)| *shared))
        {
            return Err("chunks_exact requires a shared byte-slice local".into());
        }
        if !self.mir_chunk_iterators.contains(iterator) {
            return Err("unknown MIR chunk iterator".into());
        }
        let (pointer, length) = self.slice_parts(slice)?;
        let (p_capture, p) = self.capture_operand(
            pointer,
            &Type::Reference {
                mutable: false,
                pointee: Box::new(Type::U8),
            },
        )?;
        let (l_capture, l) = self.capture_operand(length, &Type::Usize)?;
        let (size_prefix, size) = self.prepared_expr(size)?;
        if library_iterators() {
            let call = |target: String, operation: &str, arguments| {
                c_call_assign(
                    target,
                    super::super::standard_library::chunks_exact_function(operation),
                    arguments,
                )
            };
            let value = || vec![c_variable(iterator)];
            return Ok(c_seq(
                c_seq(p_capture, c_seq(l_capture, size_prefix)),
                c_seq(
                    call(
                        iterator.to_string(),
                        "new",
                        vec![c_variable(&p), c_variable(&l), size],
                    ),
                    c_seq(
                        call(format!("{iterator}_tail"), "remainder_ptr", value()),
                        call(format!("{iterator}_tail_len"), "remainder_len", value()),
                    ),
                ),
            ));
        }
        let prefix = c_seq(
            c_assert(c_equal(
                c_variable(format!("{iterator}_live")),
                c_int32_literal(0),
            )),
            c_seq(p_capture, c_seq(l_capture, size_prefix)),
        );
        let values = self.chunk_initialize_values(prefix, iterator, size, &p, &l)?;
        Ok(c_seq(
            values,
            c_assign(format!("{iterator}_live"), c_int32_literal(1)),
        ))
    }
    pub(super) fn chunk_move(&self, target: &str, source: &str) -> Result<CStatement, String> {
        if target == source || !self.mir_chunk_iterators.contains(target) {
            return Err("invalid chunk move destination".into());
        }
        if library_iterators() {
            let mut result = c_assign(target, c_variable(source));
            for suffix in ["tail", "tail_len"] {
                result = c_seq(
                    result,
                    c_assign(
                        format!("{target}_{suffix}"),
                        c_variable(format!("{source}_{suffix}")),
                    ),
                );
            }
            return Ok(result);
        }
        let mut result = c_seq(
            self.chunk_live(source)?,
            c_assert(c_equal(
                c_variable(format!("{target}_live")),
                c_int32_literal(0),
            )),
        );
        for suffix in ["cursor", "remaining", "size", "tail", "tail_len"] {
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
    pub(super) fn chunk_has_next(&self, iterator: &str) -> Result<CExpression, String> {
        if !self.mir_chunk_iterators.contains(iterator) {
            return Err("unknown MIR chunk iterator".into());
        }
        if library_iterators() {
            return Ok(c_less_than(
                c_uint64_literal(0),
                c_variable(format!("{iterator}_left")),
            ));
        }
        let remaining = c_variable(format!("{iterator}_remaining"));
        let size = c_variable(format!("{iterator}_size"));
        Ok(chunk_has_whole(remaining, size))
    }
    /// Reads how many chunks the library iterator will still yield into its
    /// `_left` local. Each test of it reads it afresh first, and the
    /// `next()` the test leads to uses that read, so no loop has to carry
    /// the local's meaning across its head.
    pub(super) fn chunk_read_left(&self, iterator: &str) -> CStatement {
        c_call_assign(
            format!("{iterator}_left"),
            super::super::standard_library::chunks_exact_function("len"),
            vec![c_variable(iterator)],
        )
    }
    pub(super) fn chunk_next(&self, iterator: &str, option: &str) -> Result<CStatement, String> {
        if !self.chunk_options.contains(option) {
            return Err("unknown chunk Option".into());
        }
        if library_iterators() {
            let call = |target: String, operation: &str, arguments| {
                c_call_assign(
                    target,
                    super::super::standard_library::chunks_exact_function(operation),
                    arguments,
                )
            };
            let value = || vec![c_variable(iterator)];
            // `next()`: the first chunk still to come, then the iterator
            // after it.
            let some = c_seq(
                c_assign(format!("{option}_some"), c_int32_literal(1)),
                c_seq(
                    call(format!("{option}_pointer"), "item_ptr", value()),
                    c_seq(
                        call(format!("{option}_len"), "item_len", value()),
                        call(iterator.to_string(), "after_next", value()),
                    ),
                ),
            );
            // The test that led here read `_left` from this iterator.
            return Ok(c_if(
                self.chunk_has_next(iterator)?,
                some,
                c_assign(format!("{option}_some"), c_int32_literal(0)),
            ));
        }
        let cursor = format!("{iterator}_cursor");
        let remaining = format!("{iterator}_remaining");
        let size = c_variable(format!("{iterator}_size"));
        let step = size.clone();
        let some = c_seq(
            c_assign(format!("{option}_some"), c_int32_literal(1)),
            c_seq(
                c_assign(format!("{option}_pointer"), c_variable(&cursor)),
                c_seq(
                    c_assign(format!("{option}_len"), size),
                    c_seq(
                        c_assign(&cursor, c_add(c_variable(&cursor), step.clone())),
                        c_assign(&remaining, c_subtract(c_variable(&remaining), step)),
                    ),
                ),
            ),
        );
        Ok(c_seq(
            self.chunk_live(iterator)?,
            c_if(
                self.chunk_has_next(iterator)?,
                some,
                c_assign(format!("{option}_some"), c_int32_literal(0)),
            ),
        ))
    }
    pub(super) fn chunk_slice_checks(&self, value: &E) -> Result<CStatement, String> {
        match value {
            E::ChunkOptionSlice { option } if self.chunk_options.contains(option) => Ok(c_assert(
                c_equal(c_variable(format!("{option}_some")), c_int32_literal(1)),
            )),
            E::ChunkRemainder { iterator } if self.mir_chunk_iterators.contains(iterator) => {
                self.chunk_live(iterator)
            }
            _ => Ok(c_skip()),
        }
    }
}
