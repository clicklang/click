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

impl Context<'_> {
    pub(super) fn range_storage(
        &mut self,
        name: &str,
        element: &Type,
        inclusive: bool,
    ) -> Result<ProgramStatement, String> {
        if !element.is_integer() {
            return Err("a Rust range requires an integer element".into());
        }
        if self
            .ranges
            .insert(name.into(), (element.clone(), inclusive))
            .is_some()
        {
            return Err("range state identity collision".into());
        }
        let interface_type = scalar_type(element)?.to_kernel_type();
        let mut result = program_skip();
        for bound in ["start", "end"] {
            let local = format!("{name}_{bound}");
            if !self.locals.insert(local.clone()) {
                return Err("range bound identity collision".into());
            }
            result = program_seq(
                result,
                program_declare(self.binding(&local), interface_type),
            );
        }
        Ok(result)
    }

    fn range_element(&self, range: &str) -> Result<Type, String> {
        self.ranges
            .get(range)
            .map(|(element, _)| element.clone())
            .ok_or_else(|| "unknown Rust range".into())
    }

    fn inclusive(&self, range: &str) -> Result<bool, String> {
        self.ranges
            .get(range)
            .map(|(_, inclusive)| *inclusive)
            .ok_or_else(|| "unknown Rust range".into())
    }

    pub(super) fn range_initialize(
        &mut self,
        target: &str,
        start: &E,
        end: &E,
    ) -> Result<ProgramStatement, String> {
        self.range_element(target)?;
        Ok(program_seq(
            self.assign(&format!("{target}_start"), start)?,
            self.assign(&format!("{target}_end"), end)?,
        ))
    }

    pub(super) fn range_move(
        &self,
        target: &str,
        source: &str,
    ) -> Result<ProgramStatement, String> {
        if target == source
            || self.range_element(target)? != self.range_element(source)?
            || self.inclusive(target)? != self.inclusive(source)?
        {
            return Err("invalid Rust range move".into());
        }
        Ok(program_seq(
            program_assign(
                self.binding(&format!("{target}_start")),
                crate::kernel::program_expression::variable(
                    self.binding(&format!("{source}_start")),
                ),
            ),
            program_assign(
                self.binding(&format!("{target}_end")),
                crate::kernel::program_expression::variable(self.binding(&format!("{source}_end"))),
            ),
        ))
    }

    pub(super) fn range_has_next(&self, iterator: &str) -> Result<ProgramExpression, String> {
        self.range_element(iterator)?;
        let start =
            crate::kernel::program_expression::variable(self.binding(&format!("{iterator}_start")));
        let end =
            crate::kernel::program_expression::variable(self.binding(&format!("{iterator}_end")));
        Ok(if self.inclusive(iterator)? {
            crate::kernel::program_expression::less_equal(start, end)
        } else {
            crate::kernel::program_expression::less_than(start, end)
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
        let element = self.range_element(iterator)?;
        let start = format!("{iterator}_start");
        let local = |name: &str| E::Local { name: name.into() };
        let construct = |variant: &str, fields| E::EnumConstruct {
            name: option_type.into(),
            variant: variant.into(),
            fields,
        };
        // `start + 1` cannot overflow below `end`; its panic check is
        // decided by the guard, and an inclusive range's by `start < end`.
        let advance = self.assign(
            &start,
            &E::Binary {
                operator: "add".into(),
                left_type: element.clone(),
                right_type: element.clone(),
                left: Box::new(local(&start)),
                right: Box::new(one(&element)?),
            },
        )?;
        // Rust leaves the bounds unspecified after exhaustion. Both 0 and
        // 1 fit every supported element type, so use the same empty bounds
        // at every endpoint, including the integer type's minimum and maximum.
        let advance = if self.inclusive(iterator)? {
            use crate::kernel::program_expression as e;
            let end = format!("{iterator}_end");
            let exhausted = program_seq(
                program_assign(self.binding(&start), e::int32_literal(1)),
                program_assign(self.binding(&end), e::int32_literal(0)),
            );
            program_if(
                e::less_than(e::variable(&start), e::variable(&end)),
                advance,
                exhausted,
            )
        } else {
            advance
        };
        let none = match option {
            Some(option) => self.assign(option, &construct("None", vec![]))?,
            None => program_skip(),
        };
        if taken == Some(false) {
            return Ok(none);
        }
        // The yielded value is the loop variable's, when the loop reads only
        // that; otherwise the `Option` holds it.
        let yielded = match (payload, option) {
            (Some(payload), _) => self.assign(payload, &local(&start))?,
            (None, Some(option)) => self.assign(option, &construct("Some", vec![local(&start)]))?,
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
