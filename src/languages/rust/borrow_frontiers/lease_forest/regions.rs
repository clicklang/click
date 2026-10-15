//! Project supported acyclic regions once. Arm accesses share the outermost
//! common continuation; no birth, alias mutation or end is issued in an arm.
use super::*;
use crate::languages::rust::schema::MirBody;

#[derive(Clone, Copy)]
pub(super) enum Operation<'a> {
    Statement(&'a S),
    Condition(&'a E),
}
pub(super) struct Event<'a> {
    pub source: MirPoint,
    pub frontier: MirPoint,
    pub in_arm: bool,
    pub operation: Operation<'a>,
}

pub(super) fn project<'a>(mir: &'a MirBody, joins: &[usize]) -> Option<Vec<Event<'a>>> {
    let exit = mir.blocks.len();
    if exit == 0 || joins.len() != exit {
        return None;
    }
    let mut events = vec![];
    let mut seen = vec![false; exit];
    let mut pending = vec![(0, exit, None)];
    while let Some((block, stop, arm_join)) = pending.pop() {
        crate::instrumentation::record_deterministic_work(1);
        if block == stop {
            continue;
        }
        if block >= exit || std::mem::replace(&mut seen[block], true) {
            return None;
        }
        let selected = &mir.blocks[block];
        for (statement, operation) in selected.statements.iter().enumerate() {
            events.push(Event {
                source: MirPoint { block, statement },
                frontier: arm_join.map_or(
                    MirPoint {
                        block,
                        statement: statement + 1,
                    },
                    |block| MirPoint {
                        block,
                        statement: 0,
                    },
                ),
                in_arm: arm_join.is_some(),
                operation: Operation::Statement(operation),
            });
        }
        match &selected.terminator {
            T::Goto { target } => pending.push((*target, stop, arm_join)),
            T::If {
                condition,
                then_target,
                else_target,
            } => {
                let join = joins[block];
                // An early return has no actual common continuation. Its
                // branch-specific authority transition remains unsupported.
                if join >= exit || join == block {
                    return None;
                }
                events.push(Event {
                    source: MirPoint {
                        block,
                        statement: selected.statements.len(),
                    },
                    frontier: MirPoint {
                        block: arm_join.unwrap_or(join),
                        statement: 0,
                    },
                    in_arm: arm_join.is_some(),
                    operation: Operation::Condition(condition),
                });
                pending.push((join, stop, arm_join));
                pending.push((*else_target, join, Some(arm_join.unwrap_or(join))));
                pending.push((*then_target, join, Some(arm_join.unwrap_or(join))));
            }
            T::Return if arm_join.is_none() && stop == exit => {}
            _ => return None,
        }
    }
    Some(events)
}
