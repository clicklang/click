//! One structured region projection. Lexical arm paths delimit non-escaping
//! reference definitions; ancestor jumps locate a use's common continuation.
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
    pub path: usize,
    pub operation: Operation<'a>,
}
struct Path {
    parent: usize,
    depth: usize,
    up: Vec<usize>,
    fork: Option<usize>,
    join: MirPoint,
}
pub(super) struct Projection<'a> {
    pub events: Vec<Event<'a>>,
    paths: Vec<Path>,
}
impl Projection<'_> {
    fn arm(&mut self, parent: usize, fork: usize, join: usize) -> usize {
        let depth = self.paths[parent].depth + 1;
        let mut up = vec![parent];
        for bit in 1..usize::BITS as usize {
            if (1usize << bit) > depth {
                break;
            }
            up.push(
                self.paths[up[bit - 1]]
                    .up
                    .get(bit - 1)
                    .copied()
                    .unwrap_or(0),
            );
        }
        let index = self.paths.len();
        self.paths.push(Path {
            parent,
            depth,
            up,
            fork: Some(fork),
            join: MirPoint {
                block: join,
                statement: 0,
            },
        });
        index
    }
    pub fn scope(&self, path: usize) -> Option<(usize, usize)> {
        let path = &self.paths[path];
        Some((path.fork?, path.join.block))
    }
    pub fn frontier(&self, birth: usize, event: &Event<'_>) -> Option<MirPoint> {
        if birth == event.path {
            return Some(event.frontier);
        }
        let depth = self.paths[birth].depth;
        if depth >= self.paths[event.path].depth {
            return None;
        }
        let mut child = event.path;
        let mut difference = self.paths[child].depth - depth - 1;
        while difference != 0 {
            crate::instrumentation::record_deterministic_work(1);
            let bit = difference.trailing_zeros() as usize;
            child = self.paths[child].up[bit];
            difference &= difference - 1;
        }
        (self.paths[child].parent == birth).then_some(self.paths[child].join)
    }
}
pub(super) fn project<'a>(mir: &'a MirBody, joins: &[usize]) -> Option<Projection<'a>> {
    let exit = mir.blocks.len();
    if exit == 0 || joins.len() != exit {
        return None;
    }
    let mut result = Projection {
        events: vec![],
        paths: vec![Path {
            parent: 0,
            depth: 0,
            up: vec![0],
            fork: None,
            join: MirPoint {
                block: exit,
                statement: 0,
            },
        }],
    };
    let mut seen = vec![false; exit];
    let mut pending = vec![(0, exit, 0)];
    while let Some((block, stop, path)) = pending.pop() {
        crate::instrumentation::record_deterministic_work(1);
        if block == stop {
            continue;
        }
        if block >= exit || std::mem::replace(&mut seen[block], true) {
            return None;
        }
        let selected = &mir.blocks[block];
        for (statement, operation) in selected.statements.iter().enumerate() {
            result.events.push(Event {
                source: MirPoint { block, statement },
                frontier: MirPoint {
                    block,
                    statement: statement + 1,
                },
                path,
                operation: Operation::Statement(operation),
            });
        }
        match &selected.terminator {
            T::Goto { target } => pending.push((*target, stop, path)),
            T::If {
                condition,
                then_target,
                else_target,
            } => {
                let join = joins[block];
                if join >= exit || join == block {
                    return None;
                }
                result.events.push(Event {
                    source: MirPoint {
                        block,
                        statement: selected.statements.len(),
                    },
                    frontier: MirPoint {
                        block: join,
                        statement: 0,
                    },
                    path,
                    operation: Operation::Condition(condition),
                });
                let yes = result.arm(path, block, join);
                let no = result.arm(path, block, join);
                pending.push((join, stop, path));
                pending.push((*else_target, join, no));
                pending.push((*then_target, join, yes));
            }
            T::Return if path == 0 && stop == exit => {}
            _ => return None,
        }
    }
    Some(result)
}
