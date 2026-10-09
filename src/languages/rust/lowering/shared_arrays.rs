//! Scalar shared iteration retains cursor/remaining state and a typed Option.
use super::*;
fn pointer_type(element: CType) -> Result<CType, String> {
    match element {
        CType::Int32 => Ok(CType::Int32Pointer),
        CType::UInt8 => Ok(CType::UInt8Pointer),
        CType::UInt32 => Ok(CType::UInt32Pointer),
        _ => Err("shared array iterator requires i32, u8 or u32".into()),
    }
}
impl Context<'_> {
    pub(super) fn shared_array_storage(
        &mut self,
        name: &str,
        element: &Type,
        option: bool,
    ) -> Result<CStatement, String> {
        let element = scalar_type(element)?.to_kernel_type();
        let pointer = pointer_type(element)?;
        if !self.locals.insert(name.into()) {
            return Err("shared iterator state identity collision".into());
        }
        let fields = if option {
            self.shared_array_options.insert(name.into(), element);
            vec![("some", CType::Int32, false), ("pointer", pointer, true)]
        } else {
            self.shared_array_iterators.insert(name.into(), element);
            vec![
                ("cursor", pointer, true),
                // The remaining count is a `usize`.
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
                pointee: Box::new(match element {
                    CType::UInt8 => Type::U8,
                    CType::Int32 => Type::I32,
                    _ => Type::U32,
                }),
            },
        )?;
        let (l_capture, l) = self.capture_operand(length, &Type::Usize)?;
        let begin = |remaining: CExpression| {
            c_seq(
                c_assign(format!("{target}_cursor"), c_variable(&p)),
                c_seq(
                    c_assign(format!("{target}_remaining"), remaining),
                    c_assign(format!("{target}_live"), c_int32_literal(1)),
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
        for suffix in ["cursor", "remaining"] {
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
        if !self.shared_array_iterators.contains_key(iterator)
            || self.shared_array_iterators.get(iterator) != self.shared_array_options.get(option)
        {
            return Err("shared iterator Option element mismatch".into());
        }
        let cursor = format!("{iterator}_cursor");
        let remaining = format!("{iterator}_remaining");
        let some = c_seq(
            c_assign(format!("{option}_some"), c_int32_literal(1)),
            c_seq(
                c_assign(format!("{option}_pointer"), c_variable(&cursor)),
                c_seq(
                    c_assign(&cursor, c_add(c_variable(&cursor), c_int32_literal(1))),
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
