//! An integer range is held as its two bounds, `{name}_start` and
//! `{name}_end`; `next` yields `Some(start)` and advances `start` while
//! `start < end`. An inclusive range also holds `{name}_done`, set once it
//! yields `end`: it yields while `!done && start <= end`, and `next` at
//! `start == end` sets `done` instead of advancing past `end`.
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
        let c_type = scalar_type(element)?.to_kernel_type();
        let mut result = program_skip();
        for bound in ["start", "end"] {
            let local = format!("{name}_{bound}");
            if !self.locals.insert(local.clone()) {
                return Err("range bound identity collision".into());
            }
            result = program_seq(result, program_declare(local, c_type));
        }
        if inclusive {
            let done = format!("{name}_done");
            if !self.locals.insert(done.clone()) {
                return Err("range bound identity collision".into());
            }
            result = program_seq(result, program_declare(done, ProgramType::Int32));
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
        let bounds = program_seq(
            self.assign(&format!("{target}_start"), start)?,
            self.assign(&format!("{target}_end"), end)?,
        );
        Ok(if self.inclusive(target)? {
            program_seq(
                bounds,
                program_assign(
                    format!("{target}_done"),
                    crate::kernel::program_expression::int32_literal(0),
                ),
            )
        } else {
            bounds
        })
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
        let bounds = program_seq(
            program_assign(
                format!("{target}_start"),
                crate::kernel::program_expression::variable(format!("{source}_start")),
            ),
            program_assign(
                format!("{target}_end"),
                crate::kernel::program_expression::variable(format!("{source}_end")),
            ),
        );
        Ok(if self.inclusive(target)? {
            program_seq(
                bounds,
                program_assign(
                    format!("{target}_done"),
                    crate::kernel::program_expression::variable(format!("{source}_done")),
                ),
            )
        } else {
            bounds
        })
    }

    pub(super) fn range_has_next(&self, iterator: &str) -> Result<ProgramExpression, String> {
        self.range_element(iterator)?;
        let start = crate::kernel::program_expression::variable(format!("{iterator}_start"));
        let end = crate::kernel::program_expression::variable(format!("{iterator}_end"));
        Ok(if self.inclusive(iterator)? {
            crate::kernel::program_expression::and(
                crate::kernel::program_expression::equal(
                    crate::kernel::program_expression::variable(format!("{iterator}_done")),
                    crate::kernel::program_expression::int32_literal(0),
                ),
                crate::kernel::program_expression::less_equal(start, end),
            )
        } else {
            crate::kernel::program_expression::less_than(start, end)
        })
    }

    pub(super) fn range_next(
        &mut self,
        iterator: &str,
        option: &str,
        option_type: &str,
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
        // An inclusive range at `start == end` yields `end` and is done; its
        // `start` is not advanced past `end`.
        let advance = if self.inclusive(iterator)? {
            program_if(
                crate::kernel::program_expression::less_than(
                    crate::kernel::program_expression::variable(&start),
                    crate::kernel::program_expression::variable(format!("{iterator}_end")),
                ),
                advance,
                program_assign(
                    format!("{iterator}_done"),
                    crate::kernel::program_expression::int32_literal(1),
                ),
            )
        } else {
            advance
        };
        let some = program_seq(
            self.assign(option, &construct("Some", vec![local(&start)]))?,
            advance,
        );
        let none = self.assign(option, &construct("None", vec![]))?;
        Ok(match taken {
            Some(true) => some,
            Some(false) => none,
            None => program_if(self.range_has_next(iterator)?, some, none),
        })
    }
}
