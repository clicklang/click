//! An integer range is held as its two bounds, `{name}_start` and
//! `{name}_end`; `next` yields `Some(start)` and advances `start` while
//! `start < end`.
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
    ) -> Result<CStatement, String> {
        if !element.is_integer() {
            return Err("a Rust range requires an integer element".into());
        }
        if self.ranges.insert(name.into(), element.clone()).is_some() {
            return Err("range state identity collision".into());
        }
        let c_type = scalar_type(element)?.to_kernel_type();
        let mut result = c_skip();
        for bound in ["start", "end"] {
            let local = format!("{name}_{bound}");
            if !self.locals.insert(local.clone()) {
                return Err("range bound identity collision".into());
            }
            result = c_seq(result, c_declare(local, c_type));
        }
        Ok(result)
    }

    fn range_element(&self, range: &str) -> Result<Type, String> {
        self.ranges
            .get(range)
            .cloned()
            .ok_or_else(|| "unknown Rust range".into())
    }

    pub(super) fn range_initialize(
        &mut self,
        target: &str,
        start: &E,
        end: &E,
    ) -> Result<CStatement, String> {
        self.range_element(target)?;
        Ok(c_seq(
            self.assign(&format!("{target}_start"), start)?,
            self.assign(&format!("{target}_end"), end)?,
        ))
    }

    pub(super) fn range_move(&self, target: &str, source: &str) -> Result<CStatement, String> {
        if target == source || self.range_element(target)? != self.range_element(source)? {
            return Err("invalid Rust range move".into());
        }
        Ok(c_seq(
            c_assign(
                format!("{target}_start"),
                c_variable(format!("{source}_start")),
            ),
            c_assign(format!("{target}_end"), c_variable(format!("{source}_end"))),
        ))
    }

    pub(super) fn range_has_next(&self, iterator: &str) -> Result<CExpression, String> {
        self.range_element(iterator)?;
        Ok(c_less_than(
            c_variable(format!("{iterator}_start")),
            c_variable(format!("{iterator}_end")),
        ))
    }

    pub(super) fn range_next(
        &mut self,
        iterator: &str,
        option: &str,
        option_type: &str,
    ) -> Result<CStatement, String> {
        let element = self.range_element(iterator)?;
        let start = format!("{iterator}_start");
        let local = |name: &str| E::Local { name: name.into() };
        let construct = |variant: &str, fields| E::EnumConstruct {
            name: option_type.into(),
            variant: variant.into(),
            fields,
        };
        // `start + 1` cannot overflow below `end`; its panic check is
        // decided by the guard.
        let advance = E::Binary {
            operator: "add".into(),
            left_type: element.clone(),
            right_type: element.clone(),
            left: Box::new(local(&start)),
            right: Box::new(one(&element)?),
        };
        let some = c_seq(
            self.assign(option, &construct("Some", vec![local(&start)]))?,
            self.assign(&start, &advance)?,
        );
        let none = self.assign(option, &construct("None", vec![]))?;
        Ok(c_if(self.range_has_next(iterator)?, some, none))
    }
}
