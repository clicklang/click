//! A `ChunksExact<'_, u8>` is held as its own fields, as `core` declares
//! them: `v`, the chunks still to come, `rem`, the elements they leave over,
//! and `chunk_size`. A slice field is a pointer and a length, so the fields
//! are the five locals `<it>_v`, `<it>_v_len`, `<it>_rem`, `<it>_rem_len`
//! and `<it>_chunk_size`, and `chunks_exact`, `next` and `remainder` run
//! `core`'s own code over them. A proof reads them as `iter.v`,
//! `iter.v.len()`, `iter.rem`, `iter.rem.len()` and `iter.chunk_size`.
use super::*;

/// The locals of a chunk iterator's fields, by suffix, with their types and
/// whether each is a pointer to constant bytes.
const CHUNK_FIELDS: [(&str, ProgramType, bool); 5] = [
    ("v", ProgramType::UInt8Pointer, true),
    ("v_len", ProgramType::UInt64, false),
    ("rem", ProgramType::UInt8Pointer, true),
    ("rem_len", ProgramType::UInt64, false),
    ("chunk_size", ProgramType::UInt64, false),
];

/// The locals of the `Option<&[u8]>` a chunk iterator's `next` returns:
/// whether it is `Some`, and the chunk it holds.
const CHUNK_OPTION_FIELDS: [(&str, ProgramType, bool); 3] = [
    ("some", ProgramType::Int32, false),
    ("pointer", ProgramType::UInt8Pointer, true),
    ("len", ProgramType::UInt64, false),
];

impl Context<'_> {
    pub(super) fn chunk_storage(
        &mut self,
        name: &str,
        option: bool,
    ) -> Result<ProgramStatement, String> {
        if !self.locals.insert(name.into()) {
            return Err("chunk state identity collision".into());
        }
        let fields: &[(&str, ProgramType, bool)] = if option {
            self.chunk_options.insert(name.into());
            &CHUNK_OPTION_FIELDS
        } else {
            self.mir_chunk_iterators.insert(name.into());
            &CHUNK_FIELDS
        };
        let mut result = program_skip();
        for (suffix, ty, constant) in fields {
            let field = format!("{name}_{suffix}");
            if !self.locals.insert(field.clone()) {
                return Err("chunk field identity collision".into());
            }
            result = program_seq(
                result,
                program_declare_with_all_qualifiers(
                    self.binding(&field),
                    *ty,
                    false,
                    false,
                    false,
                    *constant,
                ),
            );
        }
        if option {
            result = program_seq(
                result,
                program_assign(
                    self.binding(&format!("{name}_some")),
                    crate::kernel::program_expression::int32_literal(0),
                ),
            );
        }
        Ok(result)
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
        if !self.mir_chunk_iterators.contains(iterator) {
            return Err("unknown MIR chunk iterator".into());
        }
        // The slice is a local, so its parts are its own locals, read
        // before anything here writes.
        let (pointer, length) = self.slice_parts(slice)?;
        let (size_prefix, size) = self.prepared_expr(size)?;
        use crate::kernel::program_expression::{
            add, not_equal, remainder, subtract, uint64_literal, variable,
        };
        let field = |suffix: &str| format!("{iterator}_{suffix}");
        let mut result = size_prefix;
        for statement in [
            program_assign(self.binding(&field("chunk_size")), size),
            program_labeled_assert(
                not_equal(
                    variable(self.binding(&field("chunk_size"))),
                    uint64_literal(0),
                ),
                "Rust chunks_exact panic check",
            ),
            program_assign(
                self.binding(&field("rem_len")),
                remainder(length.clone(), variable(self.binding(&field("chunk_size")))),
            ),
            program_assign(self.binding(&field("v")), pointer.clone()),
            program_assign(
                self.binding(&field("v_len")),
                subtract(length, variable(self.binding(&field("rem_len")))),
            ),
            program_assign(
                self.binding(&field("rem")),
                add(pointer, variable(self.binding(&field("v_len")))),
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
        if target == source
            || !self.mir_chunk_iterators.contains(target)
            || !self.mir_chunk_iterators.contains(source)
        {
            return Err("invalid chunk move".into());
        }
        let mut result = program_skip();
        for (suffix, _, _) in CHUNK_FIELDS {
            result = program_seq(
                result,
                program_assign(
                    self.binding(&format!("{target}_{suffix}")),
                    crate::kernel::program_expression::variable(
                        self.binding(&format!("{source}_{suffix}")),
                    ),
                ),
            );
        }
        Ok(result)
    }

    /// Whether `next` yields a chunk: `core` returns `None` when
    /// `v.len() < chunk_size`.
    pub(super) fn chunk_has_next(&self, iterator: &str) -> Result<ProgramExpression, String> {
        if !self.mir_chunk_iterators.contains(iterator) {
            return Err("unknown MIR chunk iterator".into());
        }
        Ok(crate::kernel::program_expression::less_equal(
            crate::kernel::program_expression::variable(
                self.binding(&format!("{iterator}_chunk_size")),
            ),
            crate::kernel::program_expression::variable(self.binding(&format!("{iterator}_v_len"))),
        ))
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
        use crate::kernel::program_expression::{add, int32_literal, subtract, variable};
        let field = |suffix: &str| format!("{iterator}_{suffix}");
        let Some(option) = option else {
            if !self.mir_chunk_iterators.contains(iterator) {
                return Err("unknown MIR chunk iterator".into());
            }
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
                            variable(self.binding(&field("v"))),
                            ProgramType::UInt8Pointer,
                            false,
                            constant,
                        ),
                    ),
                    program_assign(
                        self.binding(&length),
                        variable(self.binding(&field("chunk_size"))),
                    ),
                );
            }
            for statement in [
                program_assign(
                    self.binding(&field("v")),
                    add(
                        variable(self.binding(&field("v"))),
                        variable(self.binding(&field("chunk_size"))),
                    ),
                ),
                program_assign(
                    self.binding(&field("v_len")),
                    subtract(
                        variable(self.binding(&field("v_len"))),
                        variable(self.binding(&field("chunk_size"))),
                    ),
                ),
            ] {
                some = program_seq(some, statement);
            }
            return Ok(match taken {
                Some(_) => some,
                None => program_if(self.chunk_has_next(iterator)?, some, program_skip()),
            });
        };
        if !self.chunk_options.contains(option) {
            return Err("unknown chunk Option".into());
        }
        let mut some = program_assign(self.binding(&format!("{option}_some")), int32_literal(1));
        for statement in [
            program_assign(
                self.binding(&format!("{option}_pointer")),
                variable(self.binding(&field("v"))),
            ),
            program_assign(
                self.binding(&format!("{option}_len")),
                variable(self.binding(&field("chunk_size"))),
            ),
            program_assign(
                self.binding(&field("v")),
                add(
                    variable(self.binding(&field("v"))),
                    variable(self.binding(&field("chunk_size"))),
                ),
            ),
            program_assign(
                self.binding(&field("v_len")),
                subtract(
                    variable(self.binding(&field("v_len"))),
                    variable(self.binding(&field("chunk_size"))),
                ),
            ),
        ] {
            some = program_seq(some, statement);
        }
        Ok(program_if(
            self.chunk_has_next(iterator)?,
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
