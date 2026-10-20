//! A `match` on an enum behind a reference, `match *r`, tests a copy.
//!
//! The compiler reads the discriminant of `*r` in place. Copying the
//! referent into a fresh local at that read, `m = copy *r;
//! d = @discriminant(m)`, makes the `match` one on a local, which steps and
//! splits like any other. Nothing runs between the copy and the switch on
//! `d`, so `m` holds the value `*r` holds there; the arms still read their
//! fields through `*r`.
use super::*;

impl Adapter<'_> {
    /// Whether `ty` is a crate enum or an `Option` that a `match` splits.
    fn matched_enum(&self, ty: &a::Ty) -> bool {
        matches!(ty.kind(), a::TyKind::Adt(r) if self.enums.contains_key(&r.id))
            || self.option_payload(ty).is_some()
    }

    /// `body` with each discriminant read of a referent rewritten to read a
    /// copy, or `None` when it has none.
    pub(super) fn referent_match_body(&self, body: &u::ExprBody) -> Option<u::ExprBody> {
        let referent = |place: &a::Place| {
            matches!(&place.kind, a::PlaceKind::Projection(base, a::ProjectionElem::Deref)
                if base.as_local().is_some() && matches!(base.ty.kind(), a::TyKind::Ref(..)))
                && self.matched_enum(&place.ty)
        };
        let reads = |statement: &u::Statement| {
            matches!(&statement.kind,
                u::StatementKind::Assign(target, a::Rvalue::Discriminant(place))
                    if target.as_local().is_some() && referent(place))
        };
        if !body
            .body
            .iter()
            .any(|block| block.statements.iter().any(reads))
        {
            return None;
        }
        let mut body = body.clone();
        for block in body.body.iter_mut() {
            let mut statements = Vec::with_capacity(block.statements.len());
            for statement in std::mem::take(&mut block.statements) {
                if !reads(&statement) {
                    statements.push(statement);
                    continue;
                }
                let u::StatementKind::Assign(target, a::Rvalue::Discriminant(place)) =
                    statement.kind
                else {
                    unreachable!()
                };
                let copy = a::LocalId::from_usize(body.locals.locals.len());
                body.locals.locals.push(a::Local {
                    index: copy,
                    name: None,
                    span: statement.span,
                    ty: place.ty.clone(),
                    drop_flag_for: None,
                });
                let local = a::Place::new(copy, place.ty.clone());
                statements.push(u::Statement::new(
                    statement.span,
                    u::StatementKind::Assign(
                        local.clone(),
                        a::Rvalue::Use(a::Operand::Copy(place), a::WithRetag::No),
                    ),
                ));
                statements.push(u::Statement::new(
                    statement.span,
                    u::StatementKind::Assign(target, a::Rvalue::Discriminant(local)),
                ));
            }
            block.statements = statements;
        }
        Some(body)
    }
}
