//! A shared slice iterator, `core::slice::Iter<'_, T>`, is held as the slice
//! it still covers, what `iter.as_slice()` returns, and its length as read
//! by `iter.len()`. `core`'s iterator holds
//! the same slice as a start and an end pointer. `next` yields the element
//! at the cursor and moves the slice on by one, as `core`'s does.
use super::*;
use crate::languages::interface::SliceIteratorFields;
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

pub(super) struct SliceIteratorStorage {
    element: ProgramType,
    pub(super) fields: SliceIteratorFields,
}

/// Move the iterator on by one element.
pub(super) fn advance(fields: &SliceIteratorFields) -> ProgramStatement {
    use crate::kernel::program_expression::{add, subtract, uint64_literal, variable};
    program_seq(
        program_assign(
            fields.pointer.clone(),
            add(variable(fields.pointer.clone()), uint64_literal(1)),
        ),
        program_assign(
            fields.length.clone(),
            subtract(variable(fields.length.clone()), uint64_literal(1)),
        ),
    )
}

impl Context<'_> {
    /// `name = value` for a local `next` binds, as `assign` assigns a local:
    /// stored to its object when it is memory-backed.
    pub(super) fn bind_local(
        &mut self,
        name: &str,
        value: ProgramExpression,
    ) -> Result<ProgramStatement, String> {
        if !self.locals.contains(name) {
            return Err(format!("unknown Rust local `{name}`"));
        }
        Ok(match self.memory_values.get(name).copied() {
            Some(value_type) => program_typed_store(
                self.address(&E::Local { name: name.into() })?,
                value,
                value_type,
            ),
            None => program_assign(self.binding(name), value),
        })
    }

    pub(super) fn shared_array_iterator(
        &self,
        name: &str,
    ) -> Result<&SliceIteratorStorage, String> {
        self.shared_array_iterators
            .get(name)
            .ok_or_else(|| "unknown shared iterator".into())
    }

    pub(super) fn shared_array_storage(
        &mut self,
        name: &str,
        element: &Type,
        option: bool,
        owner: &LocalFunctionId,
        ordinal: u32,
    ) -> Result<ProgramStatement, String> {
        let pointer_type = pointer_type(element)?;
        let element = scalar_type(element)?.to_kernel_type();
        if !self.locals.insert(name.into()) {
            return Err("shared iterator state identity collision".into());
        }
        if !option {
            let [pointer, length] =
                LocalBindingId::slice_iterator_fields(owner.clone(), ordinal, pointer_type)
                    .map(BindingName::from);
            self.shared_array_iterators.insert(
                name.into(),
                SliceIteratorStorage {
                    element,
                    fields: SliceIteratorFields {
                        pointer: pointer.clone(),
                        length: length.clone(),
                    },
                },
            );
            return Ok(program_seq(
                program_declare_with_all_qualifiers(
                    pointer,
                    pointer_type,
                    false,
                    false,
                    false,
                    true,
                ),
                program_declare(length, ProgramType::UInt64),
            ));
        }

        self.shared_array_options.insert(name.into(), element);
        let fields = [
            ("some", ProgramType::Int32, false),
            ("pointer", pointer_type, true),
        ];
        let mut result = program_skip();
        for (suffix, ty, constant) in fields {
            let field = format!("{name}_{suffix}");
            if !self.locals.insert(field.clone()) {
                return Err("shared iterator field identity collision".into());
            }
            result = program_seq(
                result,
                program_declare_with_all_qualifiers(
                    self.binding(&field.clone()),
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
                    program_assign(
                        self.binding(&field),
                        crate::kernel::program_expression::int32_literal(0),
                    ),
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
        let state = self.shared_array_iterator(target)?;
        let expected = state.element;
        let fields = state.fields.clone();
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
                program_assign(fields.pointer, p),
                program_assign(fields.length, l),
            ),
        ))
    }

    /// Whether `next` yields: the slice it covers is not empty.
    pub(super) fn shared_array_has_next(
        &self,
        iterator: &str,
    ) -> Result<ProgramExpression, String> {
        let length = self.shared_array_iterator(iterator)?.fields.length.clone();
        Ok(crate::kernel::program_expression::less_than(
            crate::kernel::program_expression::uint64_literal(0),
            crate::kernel::program_expression::variable(length),
        ))
    }

    pub(super) fn shared_array_move(
        &mut self,
        target: &str,
        source: &str,
    ) -> Result<ProgramStatement, String> {
        use crate::kernel::program_expression::variable;
        let target_fields = self.shared_array_iterators.get(target);
        let source_fields = self.shared_array_iterators.get(source);
        if let (Some(destination), Some(origin)) = (target_fields, source_fields)
            && target != source
            && destination.element == origin.element
        {
            return Ok(program_seq(
                program_assign(
                    destination.fields.pointer.clone(),
                    variable(origin.fields.pointer.clone()),
                ),
                program_assign(
                    destination.fields.length.clone(),
                    variable(origin.fields.length.clone()),
                ),
            ));
        }
        Err("invalid shared iterator move".into())
    }

    /// `next` of a slice iterator: the `Option` built in `option`, or, once
    /// the loop reads only its element, the element's reference assigned to
    /// `payload`. When the `for` header's test decided whether it yields
    /// (`taken`), only that arm runs; the arm that does not yield is nothing.
    pub(super) fn shared_array_next(
        &mut self,
        iterator: &str,
        option: Option<&str>,
        payload: Option<&str>,
        taken: Option<bool>,
    ) -> Result<ProgramStatement, String> {
        match (option, payload) {
            (Some(option), None) => self.shared_array_next_with(iterator, option, program_skip()),
            (None, Some(payload)) => {
                let fields = self.shared_array_iterator(iterator)?.fields.clone();
                if taken == Some(false) {
                    return Ok(program_skip());
                }
                use crate::kernel::program_expression::variable;
                let bind = self.bind_local(payload, variable(fields.pointer.clone()))?;
                let some = program_seq(bind, advance(&fields));
                Ok(match taken {
                    Some(_) => some,
                    None => program_if(self.shared_array_has_next(iterator)?, some, program_skip()),
                })
            }
            // When nothing reads the result, only a yielding arm moves on.
            (None, None) if taken.is_some() => {
                let fields = &self.shared_array_iterator(iterator)?.fields;
                Ok(if taken == Some(true) {
                    advance(fields)
                } else {
                    program_skip()
                })
            }
            _ => Err("Rust slice next binds neither its Option nor its element".into()),
        }
    }

    /// [`Self::shared_array_next`], also running `yielded` when it yields,
    /// before the iterator moves on.
    pub(super) fn shared_array_next_with(
        &self,
        iterator: &str,
        option: &str,
        yielded: ProgramStatement,
    ) -> Result<ProgramStatement, String> {
        let Some(state) = self
            .shared_array_iterators
            .get(iterator)
            .filter(|state| self.shared_array_options.get(option) == Some(&state.element))
        else {
            return Err("shared iterator Option element mismatch".into());
        };
        use crate::kernel::program_expression::{int32_literal, variable};
        let mut some = program_assign(self.binding(&format!("{option}_some")), int32_literal(1));
        for statement in [
            program_assign(
                self.binding(&format!("{option}_pointer")),
                variable(state.fields.pointer.clone()),
            ),
            yielded,
            advance(&state.fields),
        ] {
            some = program_seq(some, statement);
        }
        Ok(program_if(
            self.shared_array_has_next(iterator)?,
            some,
            program_assign(self.binding(&format!("{option}_some")), int32_literal(0)),
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::languages::rust::schema::Place;

    #[test]
    fn slice_iterator_fields_are_distinct_from_source_locals() {
        let mut export = crate::languages::rust::charon::decode(
            include_bytes!("../../../../design/charon-trial/slice-iter/.click/sum/sum.rs.ullbc"),
            "sum.rs",
            include_bytes!("../../../../design/charon-trial/slice-iter/sum.rs"),
        )
        .unwrap();
        let function = export
            .functions
            .iter_mut()
            .find(|f| f.name == "sum")
            .unwrap();
        let mir = function.mir.as_mut().unwrap();
        let iterator = mir
            .locals
            .iter()
            .find(|local| matches!(local.value_type, Type::SharedArrayIterator { .. }))
            .unwrap();
        let colliding = ["ptr", "len"].map(|field| Place {
            name: format!("{}_{field}", iterator.name),
            value_type: Type::Usize,
            span: iterator.span.clone(),
        });
        mir.locals.extend(colliding);
        super::super::lower(&export).unwrap();
    }
}
