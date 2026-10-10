//! Persistent admitted equality inputs, distinct from query registrations.
//!
//! A derived resource index may fork its own graph checkpoint and apply only
//! later admitted inputs. It never imports a sibling's query-local node IDs or
//! class unions, and never scans the proof context to recover those inputs.
use super::*;
use std::sync::Arc;

#[derive(Clone)]
pub(super) enum Input {
    Pointer(Pointer, Pointer),
    Offset(PointerOffsetTerm, PointerOffsetTerm),
    Int32(Bitvector32Term, Bitvector32Term),
    UInt64(Bitvector32Term, Bitvector32Term),
    CheckedRead(Pointer, Pointer),
}

pub(super) struct History {
    depth: usize,
    input: Input,
    parent: Option<Arc<History>>,
}

impl Drop for History {
    fn drop(&mut self) {
        let mut parent = self.parent.take();
        while let Some(node) = parent {
            let Ok(mut node) = Arc::try_unwrap(node) else {
                break;
            };
            parent = node.parent.take();
        }
    }
}

// Each cached view owns the graph's origin and input-history Arcs, so neither
// pointer can be reused while its key is retained. These are checkpoint tokens,
// never numeric term or address-class IDs.
#[derive(Clone, Copy, Eq, PartialEq, Ord, PartialOrd)]
pub(in crate::kernel) struct InputKey {
    origin: usize,
    input: usize,
}
impl InputKey {
    pub(in crate::kernel) fn root(self) -> Self {
        Self { input: 0, ..self }
    }
}

pub(in crate::kernel) struct Checkpoints {
    origin: Arc<()>,
    cursor: Option<Arc<History>>,
    finished: bool,
}

fn key(origin: &Arc<()>, history: &Option<Arc<History>>) -> InputKey {
    InputKey {
        origin: Arc::as_ptr(origin) as usize,
        input: history
            .as_ref()
            .map_or(0, |node| Arc::as_ptr(node) as usize),
    }
}

impl Iterator for Checkpoints {
    type Item = InputKey;
    fn next(&mut self) -> Option<Self::Item> {
        if self.finished {
            return None;
        }
        let result = key(&self.origin, &self.cursor);
        self.cursor = match &self.cursor {
            Some(node) => {
                crate::instrumentation::record_deterministic_work(1);
                node.parent.clone()
            }
            None => {
                self.finished = true;
                None
            }
        };
        Some(result)
    }
}

impl EqualityGraphState {
    pub(super) fn remember_input(&mut self, input: Input) {
        self.input_history = Some(Arc::new(History {
            depth: self.input_history.as_ref().map_or(1, |node| node.depth + 1),
            input,
            parent: self.input_history.clone(),
        }));
    }
}

impl EqualityGraph {
    /// Prepare a resource index at this lineage's initial input boundary.
    /// Only unconditional term metadata is shared. No proof context is changed
    /// or weakened: later inputs are applied into forks of this checkpoint.
    pub(in crate::kernel) fn input_root(&self) -> Self {
        let origin = self
            .state
            .lock()
            .expect("equality graph")
            .merge_origin
            .clone();
        Self {
            state: std::sync::Mutex::new(EqualityGraphState {
                merge_origin: origin,
                ..EqualityGraphState::default()
            }),
            logical_reads: self.logical_reads.clone(),
        }
    }

    pub(in crate::kernel) fn input_key(&self) -> InputKey {
        let state = self.state.lock().expect("equality graph");
        key(&state.merge_origin, &state.input_history)
    }

    pub(in crate::kernel) fn input_checkpoints(&self) -> Checkpoints {
        let state = self.state.lock().expect("equality graph");
        Checkpoints {
            origin: state.merge_origin.clone(),
            cursor: state.input_history.clone(),
            finished: false,
        }
    }

    /// Advance this private checkpoint by precisely the source's admitted
    /// equality delta. Registration-only unions are reconstructed locally.
    /// A sibling or weaker input is rejected before mutating the checkpoint.
    pub(in crate::kernel) fn append_inputs_from(&mut self, source: &Self) -> bool {
        let (origin, history) = {
            let state = source.state.lock().expect("equality graph");
            (state.merge_origin.clone(), state.input_history.clone())
        };
        let previous = {
            let state = self.state.get_mut().expect("equality graph");
            if !Arc::ptr_eq(&origin, &state.merge_origin) {
                return false;
            }
            state.input_history.clone()
        };
        let previous_depth = previous.as_ref().map_or(0, |node| node.depth);
        let mut cursor = history.clone();
        let mut pending = Vec::new();
        while !match (&cursor, &previous) {
            (None, None) => true,
            (Some(current), Some(previous)) => Arc::ptr_eq(current, previous),
            _ => false,
        } {
            let Some(node) = cursor else { return false };
            if node.depth <= previous_depth {
                return false;
            }
            crate::instrumentation::record_deterministic_work(1);
            pending.push(node.clone());
            cursor = node.parent.clone();
        }
        for node in pending.into_iter().rev() {
            match &node.input {
                Input::Pointer(left, right) => {
                    self.add_equality(left, right);
                }
                Input::Offset(left, right) => {
                    self.add_offset_equality(left, right);
                }
                Input::UInt64(left, right) => {
                    self.add_uint64_equality(left, right);
                }
                Input::Int32(left, right) => {
                    self.add_int32_equality(left, right);
                }
                Input::CheckedRead(left, right) => self.add_checked_read_equality(left, right),
            }
        }
        // Retain the actual branch's input identity rather than the temporary
        // admission records made while applying into this derived graph.
        self.state.get_mut().expect("equality graph").input_history = history;
        true
    }
}
