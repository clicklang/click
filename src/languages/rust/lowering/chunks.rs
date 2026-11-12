//! A `ChunksExact<u8>` is one value of the library's `ChunksExact<uint8>`;
//! each operation is a call of its library contract.
use super::*;

impl Context<'_> {
    pub(super) fn chunk_storage(&mut self, name: &str, option: bool) -> Result<CStatement, String> {
        if !self.locals.insert(name.into()) {
            return Err("chunk state identity collision".into());
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
            c_declare(name, CType::Parameter(super::chunks_exact_type()))
        };
        let fields = if option {
            [
                ("some", CType::Int32, false),
                ("pointer", CType::UInt8Pointer, true),
                ("len", CType::UInt64, false),
            ]
        } else {
            [
                ("left", CType::UInt64, false),
                ("tail", CType::UInt8Pointer, true),
                ("tail_len", CType::UInt64, false),
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
    pub(super) fn chunk_move(&self, target: &str, source: &str) -> Result<CStatement, String> {
        if target == source || !self.mir_chunk_iterators.contains(target) {
            return Err("invalid chunk move destination".into());
        }
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
        Ok(result)
    }
    pub(super) fn chunk_has_next(&self, iterator: &str) -> Result<CExpression, String> {
        if !self.mir_chunk_iterators.contains(iterator) {
            return Err("unknown MIR chunk iterator".into());
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
    pub(super) fn chunk_read_left(&self, iterator: &str) -> CStatement {
        chunk_call(
            format!("{iterator}_left"),
            "len",
            vec![c_variable(iterator)],
        )
    }
    pub(super) fn chunk_next(&self, iterator: &str, option: &str) -> Result<CStatement, String> {
        if !self.chunk_options.contains(option) {
            return Err("unknown chunk Option".into());
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
    pub(super) fn chunk_slice_checks(&self, value: &E) -> Result<CStatement, String> {
        match value {
            E::ChunkOptionSlice { option } if self.chunk_options.contains(option) => Ok(c_assert(
                c_equal(c_variable(format!("{option}_some")), c_int32_literal(1)),
            )),
            _ => Ok(c_skip()),
        }
    }
}

/// Assigns `target` the result of the library `ChunksExact` operation
/// `operation` on `arguments`.
fn chunk_call(target: String, operation: &str, arguments: Vec<CExpression>) -> CStatement {
    c_call_assign(
        target,
        super::super::standard_library::chunks_exact_function(operation),
        arguments,
    )
}
