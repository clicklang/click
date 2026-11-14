//! A `ChunksExact<u8>` is one value of the library's `ChunksExact<uint8>`;
//! each operation is a call of its library contract.
use super::*;

impl Context<'_> {
    pub(super) fn chunk_storage(
        &mut self,
        name: &str,
        option: bool,
    ) -> Result<ProgramStatement, String> {
        if !self.locals.insert(name.into()) {
            return Err("chunk state identity collision".into());
        }
        if super::library_iterators() {
            return self.library_chunk_storage(name, option);
        }
        let mut result = if option {
            self.chunk_options.insert(name.into());
            c_skip()
        } else {
            // One value of the library's `ChunksExact<uint8>`. A slice is
            // still a pointer and a length here, so the fixed remainder is
            // read once into two locals, and a terminator's condition is an
            // expression, so the number of chunks left is read into one.
            self.mir_chunk_iterators.insert(name.into());
            c_declare(name, ProgramType::Parameter(super::chunks_exact_type()))
        };
        let fields = if option {
            [
                ("some", ProgramType::Int32, false),
                ("pointer", ProgramType::UInt8Pointer, true),
                ("len", ProgramType::UInt64, false),
            ]
        } else {
            [
                ("left", ProgramType::UInt64, false),
                ("tail", ProgramType::UInt8Pointer, true),
                ("tail_len", ProgramType::UInt64, false),
            ]
        };
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
        if option {
            result = c_seq(result, c_assign(format!("{name}_some"), c_int32_literal(0)));
        }
        Ok(result)
    }
    /// Storage of a `chunks_exact` iterator imported through Rust's
    /// interface: one value of the library's `ChunksExact<uint8>`, which
    /// `next(&mut it)` borrows, so it lives in memory. The `Option<&[u8]>`
    /// `next` returns is a value of the library's `Option`; the chunk it
    /// holds is still a pointer and a length to the body, read once into two
    /// locals, as the remainder is.
    fn library_chunk_storage(
        &mut self,
        name: &str,
        option: bool,
    ) -> Result<ProgramStatement, String> {
        let mut result = if option {
            self.chunk_options.insert(name.into());
            let option_type =
                EnumTypes::get(&super::super::standard_library::option_byte_slice_name())?;
            c_declare(name, ProgramType::Parameter(option_type))
        } else {
            self.mir_chunk_iterators.insert(name.into());
            let value_type = ProgramType::Parameter(super::chunks_exact_type());
            // Only an iterator a call borrows lives in memory: the one
            // `next(&mut it)` advances, and the one `remainder(&it)` reads
            // where it is built. One that is only moved holds its value.
            if self.library_next_options.contains_key(name)
                || self.library_chunk_built.contains(name)
            {
                self.memory_values.insert(name.into(), value_type);
                c_begin_aggregate_construction(
                    name.to_string(),
                    CAggregateLayout::holding_value(value_type),
                )
            } else {
                c_declare(name, value_type)
            }
        };
        let fields = if option {
            [
                ("pointer", ProgramType::UInt8Pointer, true),
                ("len", ProgramType::UInt64, false),
            ]
        } else {
            [
                ("tail", ProgramType::UInt8Pointer, true),
                ("tail_len", ProgramType::UInt64, false),
            ]
        };
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
        Ok(result)
    }
    /// Reads the library `Slice<u8>` value `slice` into the pointer and
    /// length locals `pointer` and `length`, through Rust's own
    /// `<[u8]>::as_ptr` and `<[u8]>::len`.
    fn split_slice_value(
        slice: ProgramExpression,
        pointer: String,
        length: String,
    ) -> ProgramStatement {
        let call = |target, operation| {
            c_call_assign(
                target,
                super::super::standard_library::byte_slice_function(operation),
                vec![slice.clone()],
            )
        };
        c_seq(call(pointer, "as_ptr"), call(length, "len"))
    }
    /// The `next(&mut it)` call a test of the library `chunks_exact`
    /// iterator `iterator` makes, assigning the `Option<&[u8]>` it returns.
    pub(super) fn library_chunk_next_call(
        &mut self,
        iterator: &str,
    ) -> Result<ProgramStatement, String> {
        let option = self
            .library_next_options
            .get(iterator)
            .ok_or("library chunk iterator test without its next() call")?
            .clone();
        let address = self.address(&E::Local {
            name: iterator.to_string(),
        })?;
        Ok(chunk_call(option, "next", vec![address]))
    }
    pub(super) fn chunk_initialize_mir(
        &mut self,
        iterator: &str,
        slice: &E,
        size: &E,
    ) -> Result<ProgramStatement, String> {
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
        if super::library_iterators() {
            let value_type = ProgramType::Parameter(super::chunks_exact_type());
            let built = self.fresh_temporary()?;
            let remainder = self.fresh_temporary()?;
            let address = self.address(&E::Local {
                name: iterator.to_string(),
            })?;
            let slice_type = ProgramType::Parameter(EnumTypes::get(
                &super::super::standard_library::byte_slice_value_name(),
            )?);
            return Ok(c_seq(
                c_seq(p_capture, c_seq(l_capture, size_prefix)),
                c_seq(
                    c_seq(
                        c_declare(&built, value_type),
                        chunk_call(
                            built.clone(),
                            "new",
                            vec![c_variable(&p), c_variable(&l), size],
                        ),
                    ),
                    c_seq(
                        c_typed_store(address.clone(), c_variable(&built), value_type),
                        c_seq(
                            c_seq(
                                c_declare(&remainder, slice_type),
                                chunk_call(remainder.clone(), "remainder", vec![address]),
                            ),
                            Self::split_slice_value(
                                c_variable(&remainder),
                                format!("{iterator}_tail"),
                                format!("{iterator}_tail_len"),
                            ),
                        ),
                    ),
                ),
            ));
        }
        let value = || vec![c_variable(iterator)];
        Ok(c_seq(
            c_seq(p_capture, c_seq(l_capture, size_prefix)),
            c_seq(
                chunk_call(
                    iterator.to_string(),
                    "new",
                    vec![c_variable(&p), c_variable(&l), size],
                ),
                c_seq(
                    chunk_call(format!("{iterator}_tail"), "remainder_ptr", value()),
                    chunk_call(format!("{iterator}_tail_len"), "remainder_len", value()),
                ),
            ),
        ))
    }
    pub(super) fn chunk_move(
        &mut self,
        target: &str,
        source: &str,
    ) -> Result<ProgramStatement, String> {
        if target == source || !self.mir_chunk_iterators.contains(target) {
            return Err("invalid chunk move destination".into());
        }
        // A memory-backed iterator is read and written through its object.
        let value = self.expr(&E::Local {
            name: source.to_string(),
        })?;
        let mut result = if let Some(&value_type) = self.memory_values.get(target) {
            let address = self.address(&E::Local {
                name: target.to_string(),
            })?;
            c_typed_store(address, value, value_type)
        } else {
            c_assign(target, value)
        };
        for suffix in ["tail", "tail_len"] {
            result = c_seq(
                result,
                c_assign(
                    format!("{target}_{suffix}"),
                    c_variable(format!("{source}_{suffix}")),
                ),
            );
        }
        Ok(result)
    }
    pub(super) fn chunk_has_next(&self, iterator: &str) -> Result<ProgramExpression, String> {
        if !self.mir_chunk_iterators.contains(iterator) {
            return Err("unknown MIR chunk iterator".into());
        }
        if super::library_iterators() {
            let option = self
                .library_next_options
                .get(iterator)
                .ok_or("library chunk iterator test without its next() call")?;
            return Ok(ProgramExpression::EnumIs {
                value: Box::new(c_variable(option)),
                variant: "Some".into(),
            });
        }
        Ok(c_less_than(
            c_uint64_literal(0),
            c_variable(format!("{iterator}_left")),
        ))
    }
    /// Reads how many chunks the library iterator will still yield into its
    /// `_left` local. Each test of it reads it afresh first, and the
    /// `next()` the test leads to uses that read, so no loop has to carry
    /// the local's meaning across its head.
    pub(super) fn chunk_read_left(&self, iterator: &str) -> ProgramStatement {
        chunk_call(
            format!("{iterator}_left"),
            "len",
            vec![c_variable(iterator)],
        )
    }
    pub(super) fn chunk_next(
        &self,
        iterator: &str,
        option: &str,
    ) -> Result<ProgramStatement, String> {
        if !self.chunk_options.contains(option) {
            return Err("unknown chunk Option".into());
        }
        if super::library_iterators() {
            // The call is made at the test; on the edge it leads to, the
            // chunk the `Some` holds is read into the chunk's locals.
            let chunk = ProgramExpression::EnumField {
                value: Box::new(c_variable(option)),
                variant: "Some".into(),
                index: 0,
            };
            return Ok(c_if(
                ProgramExpression::EnumIs {
                    value: Box::new(c_variable(option)),
                    variant: "Some".into(),
                },
                Self::split_slice_value(
                    chunk,
                    format!("{option}_pointer"),
                    format!("{option}_len"),
                ),
                c_skip(),
            ));
        }
        let value = || vec![c_variable(iterator)];
        // `next()`: the first chunk still to come, then the iterator after
        // it.
        let some = c_seq(
            c_assign(format!("{option}_some"), c_int32_literal(1)),
            c_seq(
                chunk_call(format!("{option}_pointer"), "item_ptr", value()),
                c_seq(
                    chunk_call(format!("{option}_len"), "item_len", value()),
                    chunk_call(iterator.to_string(), "after_next", value()),
                ),
            ),
        );
        // The test that led here read `_left` from this iterator.
        Ok(c_if(
            self.chunk_has_next(iterator)?,
            some,
            c_assign(format!("{option}_some"), c_int32_literal(0)),
        ))
    }
    pub(super) fn chunk_slice_checks(&self, value: &E) -> Result<ProgramStatement, String> {
        match value {
            E::ChunkOptionSlice { .. } if super::library_iterators() => Ok(c_skip()),
            E::ChunkOptionSlice { option } if self.chunk_options.contains(option) => Ok(c_assert(
                c_equal(c_variable(format!("{option}_some")), c_int32_literal(1)),
            )),
            _ => Ok(c_skip()),
        }
    }
}

/// Assigns `target` the result of the library `ChunksExact` operation
/// `operation` on `arguments`.
fn chunk_call(
    target: String,
    operation: &str,
    arguments: Vec<ProgramExpression>,
) -> ProgramStatement {
    c_call_assign(
        target,
        super::super::standard_library::chunks_exact_function(operation),
        arguments,
    )
}
