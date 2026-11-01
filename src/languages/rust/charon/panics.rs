//! Rust panics, `assert!(c)`, `panic!("...")` or `unreachable!()`: a block
//! that can only reach a call of `core::panicking` is never executed, which
//! the verifier proves. Each such block becomes one `Panic` obligation named
//! by the panic's message, and the statements that build the message are
//! dropped with it: a block shown unreachable has no effect to model.
use super::*;

/// The `core::panicking` or `std::panicking` function `callee` is, when it
/// is one: a function of the standard library that never returns.
fn panicking(callee: &a::FunDecl) -> bool {
    !callee.item_meta.is_local
        && matches!(callee.signature.output.kind(), a::TyKind::Never)
        && matches!(callee.item_meta.name.name.as_slice(), [
            a::PathElem::Ident(krate, _),
            a::PathElem::Ident(module, _),
            ..
        ] if matches!(krate.as_str(), "core" | "std") && module == "panicking")
}

/// The string constant `operand` is, `"..."` or `&"..."`.
fn string(constant: &a::ConstantExpr) -> Option<&str> {
    match constant.kind() {
        a::ConstantExprKind::Str(text) => Some(text.as_str()),
        a::ConstantExprKind::Ref(inner, _) => string(inner),
        _ => None,
    }
}

fn operand_string(operand: &a::Operand) -> Option<&str> {
    match operand {
        a::Operand::Const(constant) => string(constant),
        _ => None,
    }
}

/// A body whose panicking blocks are emptied, with each one's message.
pub(super) struct PanicBody {
    pub(super) body: u::ExprBody,
    pub(super) messages: BTreeMap<u::BlockId, String>,
    /// The locals only the emptied blocks mentioned, which the function no
    /// longer declares.
    pub(super) pruned: BTreeSet<a::LocalId>,
}

impl Adapter<'_> {
    fn panic_call<'b>(&self, block: &'b u::BlockData) -> Option<&'b a::Call> {
        let u::TerminatorKind::Call { call, .. } = &block.terminator.kind else {
            return None;
        };
        let a::FnOperand::Regular(pointer) = &call.func else {
            return None;
        };
        let callee = self.krate.fun_decls.get(self.resolve(pointer).ok()?)?;
        panicking(callee).then_some(call)
    }

    /// The local holding the message of the `Option::expect` call `block`
    /// ends with.
    fn expect_message(&self, block: &u::BlockData) -> Option<a::LocalId> {
        let u::TerminatorKind::Call { call, .. } = &block.terminator.kind else {
            return None;
        };
        let a::FnOperand::Regular(pointer) = &call.func else {
            return None;
        };
        let callee = self.krate.fun_decls.get(self.resolve(pointer).ok()?)?;
        if callee.item_meta.is_local
            || callee.item_meta.diagnostic_item.as_deref() != Some("option_expect")
        {
            return None;
        }
        match call.args.as_slice() {
            [_, a::Operand::Move(message) | a::Operand::Copy(message)] => message.as_local(),
            _ => None,
        }
    }

    /// `body` with each block that can only reach a panic emptied and each
    /// `expect` message unbuilt, or `None` when neither occurs.
    pub(super) fn panic_body(&self, body: &u::ExprBody) -> Option<PanicBody> {
        let blocks = &body.body;
        let mut panics: BTreeSet<u::BlockId> = blocks
            .iter_enumerated()
            .filter(|(_, block)| self.panic_call(block).is_some())
            .map(|(id, _)| id)
            .collect();
        // `o.expect("...")`'s message serves its panic alone: the statements
        // that build it are dropped with the panic.
        let mut messages_built: BTreeMap<u::BlockId, BTreeSet<usize>> = BTreeMap::new();
        let mut message_locals = BTreeSet::new();
        for (id, block) in blocks.iter_enumerated() {
            let Some(message) = self.expect_message(block) else {
                continue;
            };
            let mut locals = BTreeSet::from([message]);
            let mut built = BTreeSet::new();
            for (index, statement) in block.statements.iter().enumerate().rev() {
                if let u::StatementKind::Assign(place, value) = &statement.kind
                    && place
                        .as_local()
                        .is_some_and(|local| locals.contains(&local))
                {
                    built.insert(index);
                    value.dyn_visit(|local: &a::LocalId| {
                        locals.insert(*local);
                    });
                }
            }
            message_locals.extend(locals);
            messages_built.insert(id, built);
        }
        if panics.is_empty() && messages_built.is_empty() {
            return None;
        }
        // A block panics when every way it continues, other than unwinding,
        // panics.
        loop {
            let before = panics.len();
            for (id, block) in blocks.iter_enumerated() {
                if panics.contains(&id) {
                    continue;
                }
                let successors: Vec<u::BlockId> = match &block.terminator.kind {
                    u::TerminatorKind::Goto { target }
                    | u::TerminatorKind::Call { target, .. }
                    | u::TerminatorKind::Drop { target, .. }
                    | u::TerminatorKind::Assert { target, .. } => vec![*target],
                    u::TerminatorKind::Switch { branches, .. } => {
                        branches.iter().copied().collect()
                    }
                    _ => Vec::new(),
                };
                if !successors.is_empty() && successors.iter().all(|s| panics.contains(s)) {
                    panics.insert(id);
                }
            }
            if panics.len() == before {
                break;
            }
        }
        let messages = panics
            .iter()
            .map(|id| (*id, self.panic_message(body, &panics, *id)))
            .collect();
        let mentioned =
            |id: u::BlockId, block: &u::BlockData, locals: &mut BTreeSet<a::LocalId>| {
                let built = messages_built.get(&id);
                for (index, statement) in block.statements.iter().enumerate() {
                    if !matches!(
                        statement.kind,
                        u::StatementKind::StorageLive(_) | u::StatementKind::StorageDead(_)
                    ) && !built.is_some_and(|built| built.contains(&index))
                    {
                        statement.dyn_visit(|local: &a::LocalId| {
                            locals.insert(*local);
                        });
                    }
                }
                match &block.terminator.kind {
                    // The message argument of `expect` is not passed on.
                    u::TerminatorKind::Call { call, .. } if built.is_some() => {
                        call.dest.dyn_visit(|local: &a::LocalId| {
                            locals.insert(*local);
                        });
                        call.args[0].dyn_visit(|local: &a::LocalId| {
                            locals.insert(*local);
                        });
                    }
                    _ => block.terminator.dyn_visit(|local: &a::LocalId| {
                        locals.insert(*local);
                    }),
                }
            };
        let mut inside = message_locals.clone();
        let mut outside = BTreeSet::new();
        for (id, block) in blocks.iter_enumerated() {
            if panics.contains(&id) {
                mentioned(id, block, &mut inside);
            } else {
                mentioned(id, block, &mut outside);
            }
        }
        // A message another statement reads is kept, and refused there.
        if !message_locals.is_disjoint(&outside) {
            return None;
        }
        let parameters = body.locals.arg_count;
        let pruned: BTreeSet<a::LocalId> = inside
            .difference(&outside)
            .filter(|local| local.index() > parameters)
            .copied()
            .collect();
        let mut rewritten = body.clone();
        for (id, block) in rewritten.body.iter_mut_enumerated() {
            if panics.contains(&id) {
                block.statements.clear();
                block.terminator.kind = u::TerminatorKind::UndefinedBehavior;
            } else {
                if let Some(built) = messages_built.get(&id) {
                    let mut index = 0;
                    block.statements.retain(|_| {
                        index += 1;
                        !built.contains(&(index - 1))
                    });
                }
                block.statements.retain(|statement| {
                    !matches!(statement.kind,
                        u::StatementKind::StorageLive(local) | u::StatementKind::StorageDead(local)
                            if pruned.contains(&local))
                });
            }
        }
        Some(PanicBody {
            body: rewritten,
            messages,
            pruned,
        })
    }

    /// The message of the panic block `id` reaches: the string the panic
    /// function is called with, or that a constant `format_args!` holds.
    fn panic_message(
        &self,
        body: &u::ExprBody,
        panics: &BTreeSet<u::BlockId>,
        id: u::BlockId,
    ) -> String {
        let mut current = id;
        let mut seen = BTreeSet::new();
        while seen.insert(current) {
            let block = &body.body[current];
            if let Some(call) = self.panic_call(block) {
                let argument = call.args.first();
                if let Some(text) = argument.and_then(operand_string) {
                    return text.to_string();
                }
                // `panic_fmt(Arguments::from_str("..."))`.
                if let Some(a::Operand::Move(place) | a::Operand::Copy(place)) = argument
                    && let Some(local) = place.as_local()
                    && let Some(text) = panics.iter().find_map(|other| {
                        let u::TerminatorKind::Call { call, .. } =
                            &body.body[*other].terminator.kind
                        else {
                            return None;
                        };
                        (call.dest.as_local() == Some(local))
                            .then(|| call.args.first().and_then(operand_string))
                            .flatten()
                    })
                {
                    return text.to_string();
                }
                return "formatted message".into();
            }
            match &block.terminator.kind {
                u::TerminatorKind::Goto { target }
                | u::TerminatorKind::Call { target, .. }
                | u::TerminatorKind::Drop { target, .. }
                | u::TerminatorKind::Assert { target, .. } => current = *target,
                _ => break,
            }
        }
        "panic".into()
    }
}

/// A branch whose one side panics, `if c { ... } else { panic }`, is the
/// assertion `c`: a refusal names the condition, not the unreachable block.
pub(super) fn assert_branches(blocks: &mut [out::MirBlock]) {
    for index in 0..blocks.len() {
        let T::If {
            condition,
            then_target,
            else_target,
        } = &blocks[index].terminator
        else {
            continue;
        };
        let message = |target: usize| match &blocks[target].terminator {
            T::Panic { message } if blocks[target].statements.is_empty() => Some(message.clone()),
            _ => None,
        };
        let (condition, message, target) = match (message(*then_target), message(*else_target)) {
            (None, Some(message)) => (condition.clone(), message, *then_target),
            (Some(message), None) => (
                E::Not {
                    value: Box::new(condition.clone()),
                },
                message,
                *else_target,
            ),
            _ => continue,
        };
        blocks[index]
            .statements
            .push(S::Assert { condition, message });
        blocks[index].terminator = T::Goto { target };
    }
}
