//! An enumerated slice iterator is the slice iterator's cursor, remaining
//! length and live flag with `{name}_count`, the values it has yielded; its
//! `Option` holds the yielded element's address and `{name}_index`.
use super::*;

impl Context<'_> {
    pub(super) fn enumerate_storage(
        &mut self,
        name: &str,
        element: &Type,
        option: bool,
    ) -> Result<CStatement, String> {
        let storage = self.shared_array_storage(name, element, option)?;
        let field = format!("{name}_{}", if option { "index" } else { "count" });
        if !self.locals.insert(field.clone()) || !self.enumerated.insert(name.into()) {
            return Err("enumerated iterator identity collision".into());
        }
        Ok(c_seq(storage, c_declare(field, CType::UInt64)))
    }

    fn enumerated_iterator(&self, name: &str) -> Result<(), String> {
        if self.enumerated.contains(name) && self.shared_array_iterators.contains_key(name) {
            Ok(())
        } else {
            Err("unknown enumerated iterator".into())
        }
    }

    /// `target = source.enumerate()`: the slice iterator's state, with no
    /// value yielded yet.
    pub(super) fn enumerate_initialize(
        &self,
        target: &str,
        source: &str,
    ) -> Result<CStatement, String> {
        self.enumerated_iterator(target)?;
        if self.enumerated.contains(source) {
            return Err("enumerate requires a slice iterator".into());
        }
        Ok(c_seq(
            self.shared_array_move(target, source)?,
            c_assign(format!("{target}_count"), c_uint64_literal(0)),
        ))
    }

    pub(super) fn enumerate_move(&self, target: &str, source: &str) -> Result<CStatement, String> {
        self.enumerated_iterator(target)?;
        self.enumerated_iterator(source)?;
        Ok(c_seq(
            self.shared_array_move(target, source)?,
            c_assign(
                format!("{target}_count"),
                c_variable(format!("{source}_count")),
            ),
        ))
    }

    /// The slice iterator's `next`, which also records the yielded value's
    /// index and counts it.
    pub(super) fn enumerate_next(
        &self,
        iterator: &str,
        option: &str,
    ) -> Result<CStatement, String> {
        self.enumerated_iterator(iterator)?;
        if !self.enumerated.contains(option) || !self.shared_array_options.contains_key(option) {
            return Err("unknown enumerated iterator Option".into());
        }
        let count = format!("{iterator}_count");
        let yielded = c_seq(
            c_assign(format!("{option}_index"), c_variable(&count)),
            c_assign(&count, c_add(c_variable(&count), c_uint64_literal(1))),
        );
        self.shared_array_next_with(iterator, option, yielded)
    }

    /// The index an enumerated iterator's `Some` holds.
    pub(super) fn enumerate_option_index(
        &self,
        option: &str,
    ) -> Result<(CStatement, CExpression), String> {
        if !self.enumerated.contains(option) || !self.shared_array_options.contains_key(option) {
            return Err("unknown enumerated iterator Option".into());
        }
        Ok((
            c_assert(c_equal(
                c_variable(format!("{option}_some")),
                c_int32_literal(1),
            )),
            c_variable(format!("{option}_index")),
        ))
    }
}
