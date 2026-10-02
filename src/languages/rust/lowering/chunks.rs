//! Shared `ChunksExact` state. The tail is fixed at construction; consuming
//! chunks advances only the cursor and remaining complete-byte range.
use super::*;

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
            (&remaining, CType::Int32, false),
            (&size_name, CType::UInt64, false),
            (&tail, CType::UInt8Pointer, true),
            (&tail_len, CType::UInt64, false),
        ] {
            result = c_seq(
                result,
                c_declare_with_all_qualifiers(name, value_type, false, false, false, constant),
            );
        }
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
            c_labeled_assert(
                c_less_equal(c_variable(&length_name), c_uint64_literal(i32::MAX as u64)),
                "Rust chunk iterator memory-model length bound",
            ),
        );
        result = c_seq(
            result,
            c_assign(
                &tail_len,
                c_remainder(c_variable(&length_name), c_variable(&size_name)),
            ),
        );
        // Both lengths are bounded by the original length. Preserve full-width
        // chunk sizes: a size larger than the input yields only a remainder.
        result = c_seq(
            result,
            c_assign(
                &remaining,
                c_cast(
                    c_cast(
                        c_subtract(c_variable(&length_name), c_variable(&tail_len)),
                        CType::UInt32,
                    ),
                    CType::Int32,
                ),
            ),
        );
        result = c_seq(result, c_assign(&cursor, c_variable(&pointer_name)));
        result = c_seq(
            result,
            c_assign(
                &tail,
                c_add(c_variable(&pointer_name), c_variable(&remaining)),
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
        // The successful next guard bounds the size before pointer narrowing.
        next = c_seq(
            next,
            c_labeled_assert(
                c_less_equal(c_variable(&size), c_uint64_literal(i32::MAX as u64)),
                "Rust chunk iterator memory-model offset bound",
            ),
        );
        let step = c_cast(c_cast(c_variable(&size), CType::UInt32), CType::Int32);
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
            c_and(
                c_less_than(c_int32_literal(0), c_variable(&remaining)),
                c_and(
                    c_less_equal(c_variable(&size), c_uint64_literal(i32::MAX as u64)),
                    c_less_equal(
                        c_cast(c_cast(c_variable(&size), CType::UInt32), CType::Int32),
                        c_variable(&remaining),
                    ),
                ),
            ),
            Vec::new(),
            c_seq(next, source_body),
        ))
    }
}
