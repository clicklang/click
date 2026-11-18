//! An enumerated slice iterator is `core`'s `Enumerate { iter, count }`:
//! the slice iterator's fields and `<it>_count`, how many elements it has
//! yielded. Its `next` yields the slice iterator's element with the index
//! `count`, then counts it. Its `Option` holds the yielded element's address
//! and `<option>_index`.
use super::*;

impl Context<'_> {
    pub(super) fn enumerate_storage(
        &mut self,
        name: &str,
        element: &Type,
        option: bool,
    ) -> Result<ProgramStatement, String> {
        let storage = self.shared_array_storage(name, element, option)?;
        if !self.enumerated.insert(name.into()) {
            return Err("enumerated iterator identity collision".into());
        }
        let field = format!("{name}_{}", if option { "index" } else { "count" });
        if !self.locals.insert(field.clone()) {
            return Err("enumerated iterator identity collision".into());
        }
        Ok(program_seq(
            storage,
            program_declare(field, ProgramType::UInt64),
        ))
    }

    fn enumerated_iterator(&self, name: &str) -> Result<(), String> {
        if self.enumerated.contains(name) && self.shared_array_iterators.contains_key(name) {
            Ok(())
        } else {
            Err("unknown enumerated iterator".into())
        }
    }

    /// `target = source.enumerate()`: the slice iterator, which has yielded
    /// nothing yet as an enumeration.
    pub(super) fn enumerate_initialize(
        &mut self,
        target: &str,
        source: &str,
    ) -> Result<ProgramStatement, String> {
        self.enumerated_iterator(target)?;
        if self.enumerated.contains(source) {
            return Err("enumerate requires a slice iterator".into());
        }
        Ok(program_seq(
            self.shared_array_move(target, source)?,
            program_assign(
                format!("{target}_count"),
                crate::kernel::program_expression::uint64_literal(0),
            ),
        ))
    }

    pub(super) fn enumerate_move(
        &mut self,
        target: &str,
        source: &str,
    ) -> Result<ProgramStatement, String> {
        self.enumerated_iterator(target)?;
        self.enumerated_iterator(source)?;
        Ok(program_seq(
            self.shared_array_move(target, source)?,
            program_assign(
                format!("{target}_count"),
                crate::kernel::program_expression::variable(format!("{source}_count")),
            ),
        ))
    }

    /// The slice iterator's `next`, which also yields the index `count` and
    /// counts the element.
    /// `next` of an enumerated slice iterator: the `Option` built in
    /// `option`, or, once the loop reads only what it yields, the index
    /// assigned to `index` and the element's reference to `element`. When the
    /// `for` header's test decided whether it yields (`taken`), only that arm
    /// runs; the arm that does not yield is nothing.
    pub(super) fn enumerate_next(
        &mut self,
        iterator: &str,
        option: Option<&str>,
        index: Option<&str>,
        element: Option<&str>,
        taken: Option<bool>,
    ) -> Result<ProgramStatement, String> {
        self.enumerated_iterator(iterator)?;
        use crate::kernel::program_expression::{add, uint64_literal, variable};
        let count = format!("{iterator}_count");
        let Some(option) = option else {
            if taken == Some(false) {
                return Ok(program_skip());
            }
            let mut some = program_skip();
            if let Some(index) = index {
                some = program_seq(some, self.bind_local(index, variable(&count))?);
            }
            some = program_seq(
                some,
                program_assign(&count, add(variable(&count), uint64_literal(1))),
            );
            if let Some(element) = element {
                some = program_seq(
                    some,
                    self.bind_local(element, variable(format!("{iterator}_ptr")))?,
                );
            }
            some = program_seq(some, self.shared_array_advance(iterator));
            return Ok(match taken {
                Some(_) => some,
                None => program_if(self.shared_array_has_next(iterator)?, some, program_skip()),
            });
        };
        if !self.enumerated.contains(option) || !self.shared_array_options.contains_key(option) {
            return Err("unknown enumerated iterator Option".into());
        }
        let yielded = program_seq(
            program_assign(format!("{option}_index"), variable(&count)),
            program_assign(&count, add(variable(&count), uint64_literal(1))),
        );
        self.shared_array_next_with(iterator, option, yielded)
    }

    /// The index an enumerated iterator's `Some` holds.
    pub(super) fn enumerate_option_index(
        &self,
        option: &str,
    ) -> Result<(ProgramStatement, ProgramExpression), String> {
        if !self.enumerated.contains(option) || !self.shared_array_options.contains_key(option) {
            return Err("unknown enumerated iterator Option".into());
        }
        Ok((
            program_assert(crate::kernel::program_expression::equal(
                crate::kernel::program_expression::variable(format!("{option}_some")),
                crate::kernel::program_expression::int32_literal(1),
            )),
            crate::kernel::program_expression::variable(format!("{option}_index")),
        ))
    }
}
