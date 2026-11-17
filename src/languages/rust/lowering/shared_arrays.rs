//! A shared slice iterator, `core::slice::Iter<'_, T>`, is held as the slice
//! it still covers, what `iter.as_slice()` returns: its data `<it>_ptr` and
//! its length `<it>_len`, which is `iter.len()`. `core`'s iterator holds
//! the same slice as a start and an end pointer. `next` yields the element
//! at `ptr` and moves the slice on by one, as `core`'s does.
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

/// The fields of a slice iterator, by suffix, after the slice it covers.
pub(super) const SLICE_ITERATOR_FIELDS: [&str; 2] = ["ptr", "len"];

impl Context<'_> {
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
            // The length is a `usize`.
            vec![("ptr", pointer, true), ("len", ProgramType::UInt64, false)]
        };
        let mut result = program_skip();
        for (suffix, ty, constant) in fields {
            let field = format!("{name}_{suffix}");
            if !self.locals.insert(field.clone()) {
                return Err("shared iterator field identity collision".into());
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
            if suffix == "some" {
                result = program_seq(
                    result,
                    program_assign(field, crate::kernel::program_expression::int32_literal(0)),
                );
            }
        }
        Ok(result)
    }

    /// `source.iter()`: the iterator covers the whole slice.
    pub(super) fn shared_array_initialize(
        &mut self,
        target: &str,
        source: &E,
    ) -> Result<ProgramStatement, String> {
        let expected = *self
            .shared_array_iterators
            .get(target)
            .ok_or("unknown shared iterator")?;
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
        Ok(program_seq(
            program_seq(p_capture, l_capture),
            program_seq(
                program_assign(format!("{target}_ptr"), p),
                program_assign(format!("{target}_len"), l),
            ),
        ))
    }

    /// Whether `next` yields: the slice it covers is not empty.
    pub(super) fn shared_array_has_next(
        &self,
        iterator: &str,
    ) -> Result<ProgramExpression, String> {
        if !self.shared_array_iterators.contains_key(iterator) {
            return Err("unknown shared iterator".into());
        }
        Ok(crate::kernel::program_expression::less_than(
            crate::kernel::program_expression::uint64_literal(0),
            crate::kernel::program_expression::variable(format!("{iterator}_len")),
        ))
    }

    pub(super) fn shared_array_move(
        &mut self,
        target: &str,
        source: &str,
    ) -> Result<ProgramStatement, String> {
        if target == source
            || !self.shared_array_iterators.contains_key(target)
            || self.shared_array_iterators.get(target) != self.shared_array_iterators.get(source)
        {
            return Err("invalid shared iterator move".into());
        }
        let mut result = program_skip();
        for suffix in SLICE_ITERATOR_FIELDS {
            result = program_seq(
                result,
                program_assign(
                    format!("{target}_{suffix}"),
                    crate::kernel::program_expression::variable(format!("{source}_{suffix}")),
                ),
            );
        }
        Ok(result)
    }

    pub(super) fn shared_array_next(
        &self,
        iterator: &str,
        option: &str,
    ) -> Result<ProgramStatement, String> {
        self.shared_array_next_with(iterator, option, program_skip())
    }

    /// [`Self::shared_array_next`], also running `yielded` when it yields,
    /// before the iterator moves on.
    pub(super) fn shared_array_next_with(
        &self,
        iterator: &str,
        option: &str,
        yielded: ProgramStatement,
    ) -> Result<ProgramStatement, String> {
        if !self.shared_array_iterators.contains_key(iterator)
            || self.shared_array_iterators.get(iterator) != self.shared_array_options.get(option)
        {
            return Err("shared iterator Option element mismatch".into());
        }
        use crate::kernel::program_expression::{
            add, int32_literal, subtract, uint64_literal, variable,
        };
        let field = |suffix: &str| format!("{iterator}_{suffix}");
        let mut some = program_assign(format!("{option}_some"), int32_literal(1));
        for statement in [
            program_assign(format!("{option}_pointer"), variable(field("ptr"))),
            yielded,
            program_assign(field("ptr"), add(variable(field("ptr")), uint64_literal(1))),
            program_assign(
                field("len"),
                subtract(variable(field("len")), uint64_literal(1)),
            ),
        ] {
            some = program_seq(some, statement);
        }
        Ok(program_if(
            self.shared_array_has_next(iterator)?,
            some,
            program_assign(format!("{option}_some"), int32_literal(0)),
        ))
    }
}
