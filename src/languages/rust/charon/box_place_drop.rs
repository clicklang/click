//! The drop of a box held in a place other than a local, rewritten to a
//! drop of a local.
//!
//! Assigning a struct's box field, `self.slot = v`, first drops the field's
//! old value in place. Dropping a box in place is dropping it after moving
//! it out: `drop P` is `tmp = move P; drop tmp`, which frees the allocation
//! once (a moved-out `None` is null, whose free has no effect). The place is
//! then overwritten, so nothing reads the moved-out value.
use super::*;

impl Adapter<'_> {
    /// `body` with each drop of a box or an option of one in a projected
    /// place moved through a fresh local, or `None` when it has none.
    pub(super) fn box_place_drop_body(&self, body: &u::ExprBody) -> Option<u::ExprBody> {
        let projected = |terminator: &u::Terminator| {
            matches!(&terminator.kind, u::TerminatorKind::Drop { place, .. }
                if place.as_local().is_none()
                    && matches!(self.ty(&place.ty), Ok(Type::Box { .. } | Type::OptionBox { .. })))
        };
        if !body.body.iter().any(|block| projected(&block.terminator)) {
            return None;
        }
        let mut body = body.clone();
        for block in body.body.iter_mut() {
            if !projected(&block.terminator) {
                continue;
            }
            let u::TerminatorKind::Drop { place, .. } = &mut block.terminator.kind else {
                unreachable!()
            };
            let local = a::LocalId::from_usize(body.locals.locals.len());
            body.locals.locals.push(a::Local {
                index: local,
                name: None,
                span: block.terminator.span,
                ty: place.ty.clone(),
                drop_flag_for: None,
            });
            let moved = std::mem::replace(place, a::Place::new(local, place.ty.clone()));
            block.statements.push(u::Statement::new(
                block.terminator.span,
                u::StatementKind::Assign(
                    a::Place::new(local, moved.ty.clone()),
                    a::Rvalue::Use(a::Operand::Move(moved), a::WithRetag::No),
                ),
            ));
        }
        Some(body)
    }
}
