//! Shared iterator reference origins, typed Option dispatch and checked CFG splitting.
use super::*;
mod borrowing;
pub(super) use borrowing::BorrowedProtocolCall;
pub(super) fn path(name: &a::Name, expected: &[&str]) -> bool {
    name.name.len() == expected.len()
        && name.name.iter().zip(expected).all(|(part, expected)| matches!(part, a::PathElem::Ident(actual, d) if actual == expected && *d == a::Disambiguator::ZERO))
}
pub(super) fn variable(ty: &a::Ty) -> bool {
    matches!(ty.kind(), a::TyKind::TypeVar(a::DeBruijnVar::Bound(depth, id)) if depth.index == 0 && id.index() == 0)
}
impl Adapter<'_> {
    fn protocol_reference(&self, ty: &a::Ty) -> Option<bool> {
        match ty.kind() {
            a::TyKind::Ref(_, p, kind)
                if self.protocol_type(p) || self.protocol_reference(p).is_some() =>
            {
                Some(*kind == a::RefKind::Mut)
            }
            _ => None,
        }
    }
    fn protocol_type(&self, ty: &a::Ty) -> bool {
        self.chunk_type(ty) || self.shared_iterator_element(ty, false).is_some()
    }
    fn protocol_option(&self, ty: &a::Ty) -> bool {
        self.chunk_option_type(ty) || self.shared_option_element(ty, false).is_some()
    }
}
pub(super) fn bindings(
    adapter: &Adapter<'_>,
    body: &u::ExprBody,
) -> Result<
    (
        BTreeMap<a::LocalId, a::LocalId>,
        BTreeMap<a::LocalId, a::LocalId>,
    ),
    String,
> {
    let mut references = BTreeMap::new();
    let mut discriminants = BTreeMap::new();
    for statement in body.body.iter().flat_map(|block| &block.statements) {
        let u::StatementKind::Assign(target, value) = &statement.kind else {
            continue;
        };
        if let Some(mutable) = adapter.protocol_reference(&target.ty) {
            let a::PlaceKind::Local(target) = target.kind else {
                return Err(unsupported("partial iterator reference"));
            };
            let source = match value {
                a::Rvalue::Ref {
                    place,
                    kind,
                    ptr_metadata,
                } => {
                    let a::TyKind::Ref(_, pointee, _) = body.locals.locals[target].ty.kind() else {
                        unreachable!()
                    };
                    if adapter.ty(pointee)? != adapter.ty(&place.ty)? {
                        return Err(unsupported("iterator reference pointee type"));
                    }
                    if !ptr_metadata.ty().is_unit()
                        || !matches!(
                            kind,
                            a::BorrowKind::Shared | a::BorrowKind::Mut | a::BorrowKind::TwoPhaseMut
                        )
                        || mutable
                            != matches!(kind, a::BorrowKind::Mut | a::BorrowKind::TwoPhaseMut)
                    {
                        return Err(unsupported("iterator reference mutability/metadata"));
                    }
                    match &place.kind {
                        a::PlaceKind::Local(id)
                            if adapter.protocol_type(&place.ty)
                                || adapter.protocol_reference(&place.ty).is_some() =>
                        {
                            *id
                        }
                        a::PlaceKind::Projection(base, a::ProjectionElem::Deref)
                            if (adapter.protocol_type(&place.ty)
                                || adapter.protocol_reference(&place.ty).is_some())
                                && adapter
                                    .protocol_reference(&base.ty)
                                    .is_some_and(|source| !mutable || source) =>
                        {
                            local(base)?
                        }
                        _ => return Err(unsupported("iterator reference origin")),
                    }
                }
                a::Rvalue::Use(operand @ (a::Operand::Move(_) | a::Operand::Copy(_)), _)
                    if (!mutable || matches!(operand, a::Operand::Move(_)))
                        && adapter.protocol_reference(operand.ty()) == Some(mutable)
                        && adapter.ty(operand.ty())?
                            == adapter.ty(&body.locals.locals[target].ty)? =>
                {
                    local(operand_place(operand)?)?
                }
                _ => return Err(unsupported("iterator reference assignment")),
            };
            if references.insert(target, source).is_some() {
                return Err(unsupported("reassigned iterator reference"));
            }
        }
        if let a::Rvalue::Discriminant(option) = value
            && adapter.protocol_option(&option.ty)
        {
            if !matches!(
                target.ty.kind(),
                a::TyKind::Scalar(a::ScalarTy::Integer(a::IntegerTy::Signed(a::IntTy::Isize)))
            ) {
                return Err(unsupported("iterator option discriminant type"));
            }
            if discriminants
                .insert(local(target)?, local(option)?)
                .is_some()
            {
                return Err(unsupported("reassigned iterator discriminant"));
            }
        }
    }
    for block in &body.body {
        if let Some(BorrowedProtocolCall::Into { target, source }) =
            adapter.borrowed_protocol_call(&block.terminator)?
            && references.insert(target, source).is_some()
        {
            return Err(unsupported("reassigned iterator reference"));
        }
    }
    // Resolve each alias path once. Subsequent method calls use its root
    // directly, including long source reborrow chains.
    let mut roots = BTreeMap::new();
    for &start in references.keys() {
        let mut current = start;
        let mut pending = Vec::new();
        let mut seen = BTreeSet::new();
        while let Some(&next) = references.get(&current) {
            if let Some(&root) = roots.get(&current) {
                current = root;
                break;
            }
            if !seen.insert(current) {
                return Err(unsupported("cyclic iterator reference"));
            }
            pending.push(current);
            current = next;
        }
        for reference in pending {
            roots.insert(reference, current);
        }
    }
    Ok((roots, discriminants))
}
pub(super) fn local(place: &a::Place) -> Result<a::LocalId, String> {
    match place.kind {
        a::PlaceKind::Local(id) => Ok(id),
        _ => Err(unsupported("iterator protocol requires complete locals")),
    }
}
pub(super) fn operand_place(op: &a::Operand) -> Result<&a::Place, String> {
    match op {
        a::Operand::Copy(p) | a::Operand::Move(p) => Ok(p),
        _ => Err(unsupported("iterator protocol operand")),
    }
}
impl BodyAdapter<'_, '_> {
    pub(super) fn iterator_root(&self, place: &a::Place) -> Result<String, String> {
        let mut id = local(place)?;
        let mut seen = BTreeSet::new();
        while let Some(source) = self.iterator_refs.get(&id) {
            if !seen.insert(id) {
                return Err(unsupported("cyclic iterator reference"));
            }
            id = *source;
        }
        let entry = self
            .body
            .locals
            .locals
            .get(id)
            .ok_or_else(|| unsupported("iterator reference root"))?;
        if !self.adapter.protocol_type(&entry.ty) {
            return Err(unsupported("iterator reference root type"));
        }
        self.local(id)
    }
    fn protocol_option_tag(&self, option: &a::Place) -> Result<E, String> {
        let name = self.local(local(option)?)?;
        Ok(
            if self
                .adapter
                .shared_option_element(&option.ty, false)
                .is_some()
            {
                E::SharedArrayOptionTag { option: name }
            } else {
                E::ChunkOptionTag { option: name }
            },
        )
    }
    pub(super) fn iterator_statement(
        &self,
        statement: &u::Statement,
    ) -> Result<Option<Option<S>>, String> {
        match &statement.kind {
            u::StatementKind::Assign(target, _)
                if self.adapter.protocol_reference(&target.ty).is_some() =>
            {
                Ok(Some(None))
            }
            u::StatementKind::Assign(target, a::Rvalue::Discriminant(option))
                if self.adapter.protocol_option(&option.ty) =>
            {
                Ok(Some(Some(S::Assign {
                    target: self.place(target)?,
                    value: self.protocol_option_tag(option)?,
                })))
            }
            u::StatementKind::Assign(target, value) if self.adapter.protocol_type(&target.ty) => {
                let a::Rvalue::Use(a::Operand::Move(source), _) = value else {
                    return Err(unsupported("iterator requires a complete move"));
                };
                if !self.adapter.protocol_type(&source.ty) {
                    return Err(unsupported("iterator move type"));
                }
                if self.adapter.ty(&source.ty)? != self.adapter.ty(&target.ty)? {
                    return Err(unsupported("iterator move element type"));
                }
                let target_name = self.local(local(target)?)?;
                let source_name = self.local(local(source)?)?;
                Ok(Some(Some(
                    if self
                        .adapter
                        .shared_iterator_element(&target.ty, false)
                        .is_some()
                    {
                        S::SharedArrayMove {
                            target: target_name,
                            source: source_name,
                        }
                    } else {
                        S::ChunkMove {
                            target: target_name,
                            source: source_name,
                        }
                    },
                )))
            }
            u::StatementKind::StorageDead(id) if self.iterator_refs.contains_key(id) => {
                Ok(Some(None))
            }
            _ => Ok(None),
        }
    }
    pub(super) fn iterator_projection(&self, place: &a::Place) -> Result<Option<E>, String> {
        if let a::PlaceKind::Projection(base, a::ProjectionElem::Field(Some(variant), field)) =
            &place.kind
            && self.adapter.protocol_option(&base.ty)
        {
            let shared_element = self.adapter.shared_option_element(&base.ty, false);
            let valid_payload = if let Some(element) = shared_element {
                matches!(place.ty.kind(), a::TyKind::Ref(_, p, a::RefKind::Shared) if p == element)
            } else {
                matches!(place.ty.kind(), a::TyKind::Ref(_, p, a::RefKind::Shared) if byte_slice(p))
            };
            if variant.index() != 1 || field.index() != 0 || !valid_payload {
                return Err(unsupported("iterator Option projection"));
            }
            let option = self.local(local(base)?)?;
            return Ok(Some(if shared_element.is_some() {
                E::SharedArrayOptionElement { option }
            } else {
                E::ChunkOptionSlice { option }
            }));
        }
        Ok(None)
    }
    pub(super) fn iterator_switch(&self, t: &u::Terminator) -> Result<Option<T>, String> {
        let u::TerminatorKind::Switch { data, branches } = &t.kind else {
            return Ok(None);
        };
        let a::SwitchScrutinee::Value(value) = &data.scrutinee else {
            return Ok(None);
        };
        let place = operand_place(value)?;
        let a::PlaceKind::Local(id) = place.kind else {
            return Ok(None);
        };
        let Some(option) = self.iterator_discriminants.get(&id) else {
            return Ok(None);
        };
        let mut targets = [None, None];
        for (constant, branch) in &data.branches {
            let a::ConstantExprKind::Integer(a::IntegerValue::Signed(a::IntTy::Isize, tag)) =
                constant.kind()
            else {
                return Err(unsupported("iterator discriminant branch type"));
            };
            let tag =
                usize::try_from(*tag).map_err(|_| unsupported("iterator discriminant branch"))?;
            if tag > 1
                || targets[tag]
                    .replace(
                        branches
                            .get(*branch)
                            .ok_or_else(|| unsupported("iterator Option branch target"))?
                            .index(),
                    )
                    .is_some()
            {
                return Err(unsupported("iterator discriminant branch"));
            }
        }
        if data.branches.len() != 2
            || !data
                .fallback
                .and_then(|fallback| branches.get(fallback))
                .and_then(|target| self.body.body.get(*target))
                .is_some_and(|block| {
                    matches!(block.terminator.kind, u::TerminatorKind::UndefinedBehavior)
                })
        {
            return Err(unsupported("iterator Option dispatch"));
        }
        Ok(Some(T::If {
            condition: if self
                .adapter
                .shared_option_element(&self.body.locals.locals[*option].ty, false)
                .is_some()
            {
                E::SharedArrayOptionTag {
                    option: self.local(*option)?,
                }
            } else {
                E::ChunkOptionTag {
                    option: self.local(*option)?,
                }
            },
            then_target: targets[1].ok_or_else(|| unsupported("missing Some branch"))?,
            else_target: targets[0].ok_or_else(|| unsupported("missing None branch"))?,
        }))
    }
}
/// Split the assessed next+Option dispatch into a pure state guard and two
/// edge-local transitions. Both taken and final false calls still execute
/// `next` exactly once. This exposes the natural loop to the shared CFG pass.
pub(super) fn split_next_branches(blocks: &mut Vec<out::MirBlock>) -> Result<(), String> {
    let original_len = blocks.len();
    let mut predecessors = vec![Vec::new(); original_len];
    for (index, block) in blocks.iter().enumerate() {
        crate::instrumentation::record_deterministic_work(1);
        let targets = match block.terminator {
            T::Goto { target } | T::Call { target, .. } | T::Drop { target, .. } => vec![target],
            T::If {
                then_target,
                else_target,
                ..
            } => vec![then_target, else_target],
            _ => Vec::new(),
        };
        for target in targets {
            crate::instrumentation::record_deterministic_work(1);
            predecessors
                .get_mut(target)
                .ok_or_else(|| unsupported("iterator CFG successor"))?
                .push(index);
        }
    }
    for header in 0..original_len {
        crate::instrumentation::record_deterministic_work(1);
        let Some(next) = blocks[header].statements.last().cloned() else {
            continue;
        };
        let (iterator, option, shared) = match &next {
            S::ChunkNext { iterator, option } => (iterator.clone(), option.clone(), false),
            S::SharedArrayNext { iterator, option } => (iterator.clone(), option.clone(), true),
            _ => continue,
        };
        let T::Goto { target: dispatch } = blocks[header].terminator else {
            return Err(unsupported("iterator next continuation"));
        };
        let T::If {
            condition: tag,
            then_target,
            else_target,
        } = &blocks[dispatch].terminator
        else {
            return Err(unsupported("iterator next requires typed Option dispatch"));
        };
        let dispatched = match tag {
            E::ChunkOptionTag { option } if !shared => option,
            E::SharedArrayOptionTag { option } if shared => option,
            _ => return Err(unsupported("iterator Option kind")),
        };
        if dispatched != &option || !blocks[dispatch].statements.iter().all(|s| matches!(s, S::Assign { target: E::Local { .. }, value: E::ChunkOptionTag { option: value } | E::SharedArrayOptionTag { option: value } } if value == &option)) { return Err(unsupported("iterator next dispatch effects")) }
        // Reject external entry into the dispatch; it must denote this call.
        if predecessors[dispatch].as_slice() != [header] {
            return Err(unsupported("shared iterator next dispatch"));
        }
        let targets = [*then_target, *else_target];
        let first = blocks.len();
        for target in targets {
            blocks.push(out::MirBlock {
                statements: vec![next.clone()],
                terminator: T::Goto { target },
            });
        }
        blocks[header].statements.pop();
        blocks[header].terminator = T::If {
            condition: if shared {
                E::SharedArrayHasNext { iterator }
            } else {
                E::ChunkHasNext { iterator }
            },
            then_target: first,
            else_target: first + 1,
        };
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    fn protocol() -> Vec<out::MirBlock> {
        vec![
            out::MirBlock {
                statements: vec![S::ChunkNext {
                    iterator: "iter".into(),
                    option: "option".into(),
                }],
                terminator: T::Goto { target: 1 },
            },
            out::MirBlock {
                statements: vec![],
                terminator: T::If {
                    condition: E::ChunkOptionTag {
                        option: "option".into(),
                    },
                    then_target: 2,
                    else_target: 3,
                },
            },
            out::MirBlock {
                statements: vec![],
                terminator: T::Goto { target: 0 },
            },
            out::MirBlock {
                statements: vec![],
                terminator: T::Return,
            },
        ]
    }
    #[test]
    fn next_dispatch_retains_both_transitions_and_rejects_extra_effects_or_entries() {
        let mut blocks = protocol();
        split_next_branches(&mut blocks).unwrap();
        assert_eq!(blocks.len(), 6);
        assert!(blocks[0].statements.is_empty());
        for index in [4, 5] {
            assert!(matches!(
                blocks[index].statements.as_slice(),
                [S::ChunkNext { .. }]
            ));
        }
        for shared in [false, true] {
            let mut blocks = protocol();
            if shared {
                blocks[2].terminator = T::Goto { target: 1 };
            } else {
                blocks[1].statements.push(S::ChunkMove {
                    source: "iter".into(),
                    target: "other".into(),
                });
            }
            assert!(split_next_branches(&mut blocks).is_err());
        }
    }
    #[test]
    fn next_dispatch_output_scales_with_protocol_count() {
        for (shared, count) in [false, true]
            .into_iter()
            .flat_map(|shared| [8, 128, 1024].map(|count| (shared, count)))
        {
            let mut blocks = Vec::new();
            for index in 0..count {
                let offset = index * 4;
                let mut added = protocol();
                if shared {
                    added[0].statements = vec![S::SharedArrayNext {
                        iterator: "iter".into(),
                        option: "option".into(),
                    }];
                    if let T::If { condition, .. } = &mut added[1].terminator {
                        *condition = E::SharedArrayOptionTag {
                            option: "option".into(),
                        };
                    }
                }
                for block in &mut added {
                    match &mut block.terminator {
                        T::Goto { target } => *target += offset,
                        T::If {
                            then_target,
                            else_target,
                            ..
                        } => {
                            *then_target += offset;
                            *else_target += offset;
                        }
                        _ => (),
                    }
                }
                blocks.extend(added);
            }
            let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                split_next_branches(&mut blocks)
            });
            result.unwrap();
            assert_eq!(work, count * 12);
            assert_eq!(blocks.len(), count * 6);
            assert_eq!(blocks.iter().flat_map(|b| &b.statements).count(), count * 2);
        }
    }
}
