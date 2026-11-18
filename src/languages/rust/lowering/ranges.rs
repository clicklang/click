//! An integer range is held as its two bounds. A half-open range yields
//! while its start is below its end. An inclusive range also yields at
//! equality, then takes the empty representation `1..=0`.
use super::*;

/// The constant `1` of integer type `element`, as the importer spells it.
fn one(element: &Type) -> Result<E, String> {
    Ok(match element {
        Type::I32 => E::Integer { value: 1 },
        Type::Usize => E::UsizeInteger { value: 1 },
        Type::U8 | Type::U16 | Type::U32 | Type::U64 => E::UnsignedInteger {
            value: 1,
            value_type: element.clone(),
        },
        Type::I8 | Type::I16 | Type::I64 | Type::Isize => E::SignedInteger {
            value: 1,
            value_type: element.clone(),
        },
        _ => return Err("a Rust range requires an integer element".into()),
    })
}

pub(super) struct RangeStorage {
    element: Type,
    pub(super) inclusive: bool,
    pub(super) bounds: [BindingName; 2],
}

impl Context<'_> {
    pub(super) fn range_storage(
        &mut self,
        name: &str,
        element: &Type,
        inclusive: bool,
        owner: &LocalFunctionId,
        ordinal: u32,
    ) -> Result<ProgramStatement, String> {
        if !element.is_integer() {
            return Err("a Rust range requires an integer element".into());
        }
        let ty = scalar_type(element)?.to_kernel_type();
        let [start, end] =
            LocalBindingId::range_bounds(owner.clone(), ordinal, ty).map(BindingName::from);
        let storage = RangeStorage {
            element: element.clone(),
            inclusive,
            bounds: [start.clone(), end.clone()],
        };
        if self.ranges.insert(name.into(), storage).is_some() {
            return Err("range state identity collision".into());
        }
        Ok(program_seq(
            program_declare(start, ty),
            program_declare(end, ty),
        ))
    }

    fn range(&self, name: &str) -> Result<&RangeStorage, String> {
        self.ranges
            .get(name)
            .ok_or_else(|| "unknown Rust range".into())
    }

    pub(super) fn range_initialize(
        &mut self,
        target: &str,
        start: &E,
        end: &E,
    ) -> Result<ProgramStatement, String> {
        let [start_binding, end_binding] = self.range(target)?.bounds.clone();
        let (start_checks, start) = self.prepared_expr(start)?;
        let (end_checks, end) = self.prepared_expr(end)?;
        Ok(program_seq(
            program_seq(start_checks, program_assign(start_binding, start)),
            program_seq(end_checks, program_assign(end_binding, end)),
        ))
    }

    pub(super) fn range_move(
        &self,
        target: &str,
        source: &str,
    ) -> Result<ProgramStatement, String> {
        use crate::kernel::program_expression::variable;
        let (destination, origin) = (self.range(target)?, self.range(source)?);
        if target == source
            || destination.element != origin.element
            || destination.inclusive != origin.inclusive
        {
            return Err("invalid Rust range move".into());
        }
        let [start, end] = destination.bounds.clone();
        let [source_start, source_end] = origin.bounds.clone().map(variable);
        Ok(program_seq(
            program_assign(start, source_start),
            program_assign(end, source_end),
        ))
    }

    pub(super) fn range_has_next(&self, iterator: &str) -> Result<ProgramExpression, String> {
        use crate::kernel::program_expression as e;
        let range = self.range(iterator)?;
        let [start, end] = range.bounds.clone().map(e::variable);
        Ok(if range.inclusive {
            e::less_equal(start, end)
        } else {
            e::less_than(start, end)
        })
    }

    pub(super) fn range_next(
        &mut self,
        iterator: &str,
        option: Option<&str>,
        option_type: &str,
        payload: Option<&str>,
        taken: Option<bool>,
    ) -> Result<ProgramStatement, String> {
        use crate::kernel::program_expression as e;
        let range = self.range(iterator)?;
        let element = range.element.clone();
        let inclusive = range.inclusive;
        let [start, end] = range.bounds.clone();
        let start_value = e::variable(start.clone());
        let unit = self.expr(&one(&element)?)?;
        // `start + 1` cannot overflow below `end`. Retain the ordinary
        // Rust arithmetic checks for this advance.
        let (_, start_operand, _) = self.read_operand(start_value.clone(), &element, true)?;
        let (_, unit_operand, _) = self.read_operand(unit.clone(), &element, true)?;
        let checks = binary_checks("add", &element, &element, &start_operand, &unit_operand)?;
        let next = binary_value("add", &element, &element, start_value.clone(), unit)?;
        let advance = program_seq(checks, program_assign(start.clone(), next));
        // Rust leaves the bounds unspecified after exhaustion. Both 0 and
        // 1 fit every supported element type, so use the same empty bounds
        // at every endpoint, including the integer type's minimum and maximum.
        let advance = if inclusive {
            let exhausted = program_seq(
                program_assign(start, e::int32_literal(1)),
                program_assign(end.clone(), e::int32_literal(0)),
            );
            program_if(
                e::less_than(start_value.clone(), e::variable(end)),
                advance,
                exhausted,
            )
        } else {
            advance
        };
        let none = match option {
            Some(option) => self.bind_local(option, enum_construct(option_type, "None", [])?)?,
            None => program_skip(),
        };
        if taken == Some(false) {
            return Ok(none);
        }
        // The yielded value is the loop variable's, when the loop reads only
        // that; otherwise the `Option` holds it.
        let yielded = match (payload, option) {
            (Some(payload), _) => self.bind_local(payload, start_value)?,
            (None, Some(option)) => self.bind_local(
                option,
                enum_construct(option_type, "Some", [Ok(start_value)])?,
            )?,
            (None, None) => {
                return Err("Rust range next binds neither its Option nor its value".into());
            }
        };
        let some = program_seq(yielded, advance);
        Ok(match taken {
            Some(_) => some,
            None => program_if(self.range_has_next(iterator)?, some, none),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::languages::rust::schema::Place;

    #[test]
    fn range_bounds_are_distinct_from_source_locals() {
        let mut export = crate::languages::rust::charon::decode(
            include_bytes!("../../../../design/charon-trial/ranges/.click/ranges/ranges.rs.ullbc"),
            "ranges.rs",
            include_bytes!("../../../../design/charon-trial/ranges/ranges.rs"),
        )
        .unwrap();
        let function = export
            .functions
            .iter_mut()
            .find(|f| f.name == "count_to")
            .unwrap();
        let mir = function.mir.as_mut().unwrap();
        let range = mir
            .locals
            .iter()
            .find(|local| matches!(local.value_type, Type::Range { .. }))
            .unwrap();
        let colliding = ["start", "end"].map(|field| Place {
            name: format!("{}_{field}", range.name),
            value_type: Type::U32,
            span: range.span.clone(),
        });
        mir.locals.extend(colliding);
        super::super::lower(&export).unwrap();
    }
}
