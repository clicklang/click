//! A `ChunksExact<'_, u8>` is held as its own fields, as `core` declares
//! them: `v`, the chunks still to come, `rem`, the elements they leave over,
//! and `chunk_size`. Each slice holds a pointer and a length. A proof reads
//! these fields as `iter.v`, `iter.v.len()`, `iter.rem`, `iter.rem.len()`
//! and `iter.chunk_size`.
use super::*;
use crate::kernel::program_expression::variable;
use crate::languages::interface::ChunkIteratorFields;

impl ChunkIteratorFields {
    fn bindings(&self) -> [&BindingName; 5] {
        [
            &self.remaining,
            &self.remaining_length,
            &self.remainder,
            &self.remainder_length,
            &self.size,
        ]
    }

    fn advance(&self) -> ProgramStatement {
        use crate::kernel::program_expression::{add, subtract};
        program_seq(
            program_assign(
                self.remaining.clone(),
                add(variable(&self.remaining), variable(&self.size)),
            ),
            program_assign(
                self.remaining_length.clone(),
                subtract(variable(&self.remaining_length), variable(&self.size)),
            ),
        )
    }

    fn has_next(&self) -> ProgramExpression {
        crate::kernel::program_expression::less_equal(
            variable(&self.size),
            variable(&self.remaining_length),
        )
    }
}

/// The locals of the `Option<&[u8]>` a chunk iterator's `next` returns:
/// whether it is `Some`, and the chunk it holds.
const CHUNK_OPTION_FIELDS: [(&str, ProgramType, bool); 3] = [
    ("some", ProgramType::Int32, false),
    ("pointer", ProgramType::UInt8Pointer, true),
    ("len", ProgramType::UInt64, false),
];

impl Context<'_> {
    pub(super) fn chunk_iterator(&self, name: &str) -> Result<&ChunkIteratorFields, String> {
        self.mir_chunk_iterators
            .get(name)
            .ok_or_else(|| "unknown Rust chunk iterator".into())
    }

    pub(super) fn chunk_storage(
        &mut self,
        name: &str,
        option: bool,
        owner: &LocalFunctionId,
        ordinal: u32,
    ) -> Result<ProgramStatement, String> {
        if !self.locals.insert(name.into()) {
            return Err("chunk state identity collision".into());
        }
        if !option {
            let [
                remaining,
                remaining_length,
                remainder,
                remainder_length,
                size,
            ] = LocalBindingId::chunk_iterator_fields(owner.clone(), ordinal)
                .map(BindingName::from);
            let fields = ChunkIteratorFields {
                remaining,
                remaining_length,
                remainder,
                remainder_length,
                size,
            };
            let mut result = program_skip();
            for binding in fields.bindings() {
                let ty = binding.program_type().expect("chunk field type");
                result = program_seq(
                    result,
                    program_declare_with_all_qualifiers(
                        binding.clone(),
                        ty,
                        false,
                        false,
                        false,
                        ty.is_pointer(),
                    ),
                );
            }
            self.mir_chunk_iterators.insert(name.into(), fields);
            return Ok(result);
        }

        self.chunk_options.insert(name.into());
        let mut result = program_skip();
        for (suffix, ty, constant) in CHUNK_OPTION_FIELDS {
            let field = format!("{name}_{suffix}");
            if !self.locals.insert(field.clone()) {
                return Err("chunk field identity collision".into());
            }
            result = program_seq(
                result,
                program_declare_with_all_qualifiers(
                    self.binding(&field),
                    ty,
                    false,
                    false,
                    false,
                    constant,
                ),
            );
        }
        Ok(program_seq(
            result,
            program_assign(
                self.binding(&format!("{name}_some")),
                crate::kernel::program_expression::int32_literal(0),
            ),
        ))
    }

    /// `slice.chunks_exact(size)`, as `core` builds it: it panics on a zero
    /// size, then `v` is the first `len - len % size` elements and `rem` the
    /// rest.
    pub(super) fn chunk_initialize_mir(
        &mut self,
        iterator: &str,
        slice: &E,
        size: &E,
    ) -> Result<ProgramStatement, String> {
        if !self.shared_byte_slice(slice) {
            return Err("chunks_exact requires a shared byte-slice local".into());
        }
        let fields = self.chunk_iterator(iterator)?.clone();
        // The slice is a local, so its parts are its own locals, read
        // before anything here writes.
        let (pointer, length) = self.slice_parts(slice)?;
        let (size_prefix, size) = self.prepared_expr(size)?;
        use crate::kernel::program_expression::{
            add, not_equal, remainder, subtract, uint64_literal,
        };
        let mut result = size_prefix;
        for statement in [
            program_assign(fields.size.clone(), size),
            program_labeled_assert(
                not_equal(variable(&fields.size), uint64_literal(0)),
                "Rust chunks_exact panic check",
            ),
            program_assign(
                fields.remainder_length.clone(),
                remainder(length.clone(), variable(&fields.size)),
            ),
            program_assign(fields.remaining.clone(), pointer.clone()),
            program_assign(
                fields.remaining_length.clone(),
                subtract(length, variable(&fields.remainder_length)),
            ),
            program_assign(
                fields.remainder.clone(),
                add(pointer, variable(&fields.remaining_length)),
            ),
        ] {
            result = program_seq(result, statement);
        }
        Ok(result)
    }

    pub(super) fn chunk_move(
        &mut self,
        target: &str,
        source: &str,
    ) -> Result<ProgramStatement, String> {
        let target_fields = self.mir_chunk_iterators.get(target);
        let source_fields = self.mir_chunk_iterators.get(source);
        if let (Some(destination), Some(origin)) = (target_fields, source_fields)
            && target != source
        {
            let mut result = program_skip();
            for (target, source) in destination.bindings().into_iter().zip(origin.bindings()) {
                result = program_seq(result, program_assign(target.clone(), variable(source)));
            }
            return Ok(result);
        }
        Err("invalid chunk move".into())
    }

    /// Whether the remaining slice contains a full chunk.
    pub(super) fn chunk_has_next(&self, iterator: &str) -> Result<ProgramExpression, String> {
        Ok(self.chunk_iterator(iterator)?.has_next())
    }

    /// `next()`, as `core` runs it: `v.split_at(chunk_size)`, keeping the
    /// back as `v` and returning the front.
    /// `next` of a chunk iterator: the `Option` built in `option`, or, once
    /// the loop reads only its chunk, the chunk assigned to the slice local
    /// `payload`. When the `for` header's test decided whether it yields
    /// (`taken`), only that arm runs; the arm that does not yield is nothing.
    pub(super) fn chunk_next(
        &mut self,
        iterator: &str,
        option: Option<&str>,
        payload: Option<&str>,
        taken: Option<bool>,
    ) -> Result<ProgramStatement, String> {
        use crate::kernel::program_expression::int32_literal;
        let Some(option) = option else {
            let fields = self.chunk_iterator(iterator)?;
            if taken == Some(false) {
                return Ok(program_skip());
            }
            let mut some = program_skip();
            if let Some(payload) = payload {
                let Some((length, constant)) = self.slices.get(payload).cloned() else {
                    return Err("chunk payload requires a byte-slice local".into());
                };
                some = program_seq(
                    program_assign(
                        self.binding(payload),
                        reference_view(
                            variable(&fields.remaining),
                            ProgramType::UInt8Pointer,
                            false,
                            constant,
                        ),
                    ),
                    program_assign(self.binding(&length), variable(&fields.size)),
                );
            }
            let some = program_seq(some, fields.advance());
            return Ok(match taken {
                Some(_) => some,
                None => program_if(fields.has_next(), some, program_skip()),
            });
        };
        if !self.chunk_options.contains(option) {
            return Err("unknown chunk Option".into());
        }
        let fields = self.chunk_iterator(iterator)?;
        let mut some = program_assign(self.binding(&format!("{option}_some")), int32_literal(1));
        for statement in [
            program_assign(
                self.binding(&format!("{option}_pointer")),
                variable(&fields.remaining),
            ),
            program_assign(
                self.binding(&format!("{option}_len")),
                variable(&fields.size),
            ),
            fields.advance(),
        ] {
            some = program_seq(some, statement);
        }
        Ok(program_if(
            fields.has_next(),
            some,
            program_assign(self.binding(&format!("{option}_some")), int32_literal(0)),
        ))
    }

    pub(super) fn chunk_slice_checks(&self, value: &E) -> Result<ProgramStatement, String> {
        match value {
            E::ChunkOptionSlice { option } if self.chunk_options.contains(option) => {
                Ok(program_assert(crate::kernel::program_expression::equal(
                    crate::kernel::program_expression::variable(
                        self.binding(&format!("{option}_some")),
                    ),
                    crate::kernel::program_expression::int32_literal(1),
                )))
            }
            _ => Ok(program_skip()),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::languages::rust::schema::Place;

    #[test]
    fn chunk_iterator_fields_are_distinct_from_source_locals() {
        let mut export = crate::languages::rust::charon::decode(
            include_bytes!("../../../../design/charon-trial/chunks/.click/chunks/chunks.rs.ullbc"),
            "chunks.rs",
            include_bytes!("../../../../design/charon-trial/chunks/chunks.rs"),
        )
        .unwrap();
        let function = export
            .functions
            .iter_mut()
            .find(|f| f.name == "walk")
            .unwrap();
        let mir = function.mir.as_mut().unwrap();
        let iterator = mir
            .locals
            .iter()
            .find(|local| local.value_type == Type::ChunkIterator)
            .unwrap();
        let colliding = ["v", "v_len", "rem", "rem_len", "chunk_size"].map(|field| Place {
            name: format!("{}_{field}", iterator.name),
            value_type: Type::Usize,
            span: iterator.span.clone(),
        });
        mir.locals.extend(colliding);
        super::super::lower(&export).unwrap();
    }
}
