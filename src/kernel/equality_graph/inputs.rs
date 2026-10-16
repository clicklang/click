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
    Algebraic(AlgebraicTerm, AlgebraicTerm),
    UInt64(Bitvector32Term, Bitvector32Term),
    Integer(
        crate::kernel::SharedIntegerTerm,
        crate::kernel::SharedIntegerTerm,
    ),
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
            admitted: Default::default(),
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
                Input::Integer(left, right) => {
                    self.add_integer_equality(left, right);
                }
                Input::Algebraic(left, right) => {
                    self.add_algebraic_equality(left, right);
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

/// An immutable diagnostic checkpoint. Retaining the tail before a step also
/// handles queries that add checked evidence through a shared context.
pub(crate) struct ReadEqualityCheckpoint {
    origin: Arc<()>,
    history: Option<Arc<History>>,
}

pub(crate) struct ReadEqualityDelta {
    pub(crate) context_changed: bool,
    pub(crate) equalities: Vec<crate::kernel::Proposition>,
}

fn is_scalar_read(term: &Bitvector32Term) -> bool {
    match term {
        Bitvector32Term::MemoryLoad(..) => true,
        Bitvector32Term::Variable(variable) => {
            crate::kernel::registered_load_term_for_variable(variable).is_some()
        }
        _ => false,
    }
}

fn is_read_offset(offset: &PointerOffsetTerm) -> bool {
    let mut pending = vec![offset];
    while let Some(offset) = pending.pop() {
        match offset {
            PointerOffsetTerm::Add(left, right) => {
                pending.push(left);
                pending.push(right);
            }
            PointerOffsetTerm::Int32Scaled { value, .. }
            | PointerOffsetTerm::Int64Scaled { value, .. }
                if is_scalar_read(value) =>
            {
                return true;
            }
            _ => {}
        }
    }
    false
}

impl EqualityGraph {
    pub(in crate::kernel) fn read_equality_checkpoint(&self) -> ReadEqualityCheckpoint {
        let state = self.state.lock().expect("equality graph");
        ReadEqualityCheckpoint {
            origin: state.merge_origin.clone(),
            history: state.input_history.clone(),
        }
    }

    /// Inspect admission inputs only, without asking an equality query.
    /// Shared ancestry stops the walk before unrelated earlier history. For
    /// a rebuilt graph, its inputs were admitted anew in the selected step.
    pub(in crate::kernel) fn read_equalities_since(
        &self,
        checkpoint: &ReadEqualityCheckpoint,
    ) -> ReadEqualityDelta {
        let (origin, mut current) = {
            let state = self.state.lock().expect("equality graph");
            (state.merge_origin.clone(), state.input_history.clone())
        };
        let same_origin = Arc::ptr_eq(&origin, &checkpoint.origin);
        let mut previous = same_origin.then(|| checkpoint.history.clone()).flatten();
        let mut context_changed = !same_origin;
        let mut equalities = Vec::new();
        let reads = self.logical_reads.lock().expect("logical pointer reads");
        let is_read = |pointer: &Pointer| {
            pointer.as_loaded_value().is_some()
                || reads.definitions.contains_key(pointer)
                || is_read_offset(&pointer.offset)
                || matches!(&pointer.block, PointerBlock::FunctionSymbolic(variable)
                    if pointer.offset == PointerOffsetTerm::Constant(0)
                    && crate::kernel::registered_load_term_for_variable(variable).is_some())
        };
        let depth = |node: &Option<Arc<History>>| node.as_ref().map_or(0, |node| node.depth);
        while !match (&current, &previous) {
            (None, None) => true,
            (Some(current), Some(previous)) => Arc::ptr_eq(current, previous),
            _ => false,
        } {
            crate::instrumentation::record_deterministic_work(1);
            if depth(&previous) > depth(&current) {
                context_changed = true;
                previous = previous.as_ref().and_then(|node| node.parent.clone());
                continue;
            }
            if depth(&current) == depth(&previous) {
                context_changed = true;
                previous = previous.as_ref().and_then(|node| node.parent.clone());
            }
            let Some(node) = current else { break };
            let pair = match &node.input {
                Input::CheckedRead(left, right) => Some((left, right)),
                Input::Pointer(left, right) if is_read(left) || is_read(right) => {
                    Some((left, right))
                }
                _ => None,
            };
            if let Some((left, right)) = pair {
                equalities.push(crate::kernel::Proposition::ConditionIs(
                    crate::kernel::ConditionTerm::pointer_equal(left.clone(), right.clone()),
                    true,
                ));
            }
            let scalar_condition = match &node.input {
                Input::Int32(left, right) if is_scalar_read(left) || is_scalar_read(right) => {
                    Some(ConditionTerm::Bitvector32Equal(
                        Box::new(left.clone()),
                        Box::new(right.clone()),
                    ))
                }
                Input::UInt64(left, right) if is_scalar_read(left) || is_scalar_read(right) => {
                    Some(ConditionTerm::Bitvector64Equal(
                        Box::new(left.clone()),
                        Box::new(right.clone()),
                    ))
                }
                Input::Offset(left, right) if is_read_offset(left) || is_read_offset(right) => {
                    Some(ConditionTerm::PointerOffsetEqual(
                        Box::new(left.clone()),
                        Box::new(right.clone()),
                    ))
                }
                _ => None,
            };
            if let Some(condition) = scalar_condition {
                equalities.push(crate::kernel::Proposition::ConditionIs(condition, true));
            }
            current = node.parent.clone();
        }
        equalities.reverse();
        ReadEqualityDelta {
            context_changed,
            equalities,
        }
    }
}

#[cfg(test)]
mod read_trace_tests {
    use super::*;
    use crate::kernel::{ConditionTerm, Proposition};

    fn pointer(id: u64) -> Pointer {
        Pointer::symbolic(Variable(id))
    }
    fn equality(left: Pointer, right: Pointer) -> Proposition {
        Proposition::ConditionIs(ConditionTerm::pointer_equal(left, right), true)
    }

    #[test]
    fn admitted_read_trace_excludes_query_registration_and_sibling_inputs() {
        let graph = EqualityGraph::default();
        let checkpoint = graph.read_equality_checkpoint();
        assert!(!graph.are_equal(&pointer(300_000), &pointer(300_001)));
        assert!(
            graph
                .read_equalities_since(&checkpoint)
                .equalities
                .is_empty()
        );
        let sibling = graph.clone();
        graph.add_checked_read_equality(&pointer(300_002), &pointer(300_003));
        let admitted = graph.read_equalities_since(&checkpoint);
        assert!(!admitted.context_changed);
        assert_eq!(
            admitted.equalities,
            vec![equality(pointer(300_002), pointer(300_003))]
        );
        assert!(
            sibling
                .read_equalities_since(&checkpoint)
                .equalities
                .is_empty()
        );
        let after = graph.read_equality_checkpoint();
        let restored = sibling.read_equalities_since(&after);
        assert!(restored.context_changed);
        assert!(restored.equalities.is_empty());
        sibling.add_checked_read_equality(&pointer(300_006), &pointer(300_007));
        let sibling_delta = sibling.read_equalities_since(&after);
        assert!(sibling_delta.context_changed);
        assert_eq!(
            sibling_delta.equalities,
            vec![equality(pointer(300_006), pointer(300_007))]
        );
        let rebuilt = EqualityGraph::default();
        rebuilt.add_checked_read_equality(&pointer(300_004), &pointer(300_005));
        let delta = rebuilt.read_equalities_since(&after);
        assert!(delta.context_changed);
        assert_eq!(
            delta.equalities,
            vec![equality(pointer(300_004), pointer(300_005))]
        );
    }

    #[test]
    fn admitted_read_trace_includes_ordinary_read_value_equalities() {
        let mut graph = EqualityGraph::default();
        let memory = crate::kernel::intern_c_memory(CMemory::new());
        let read = Pointer::loaded_value(&memory, &pointer(303_000));
        let checkpoint = graph.read_equality_checkpoint();
        graph.add_equality(&read, &pointer(303_001));
        graph.add_equality(&pointer(303_002), &pointer(303_003));
        assert_eq!(
            graph.read_equalities_since(&checkpoint).equalities,
            vec![equality(read, pointer(303_001))]
        );
    }

    #[test]
    fn admitted_read_trace_includes_read_values_carried_as_offsets() {
        let mut graph = EqualityGraph::default();
        let memory = crate::kernel::intern_c_memory(CMemory::new());
        let load =
            Bitvector32Term::MemoryLoad(memory, Box::new(pointer(304_000)), LoadKind::Bits32);
        let (variable, _) = crate::kernel::load_variable_for_term(&load).unwrap();
        let read = PointerOffsetTerm::Int32Scaled {
            value: Box::new(Bitvector32Term::Variable(variable)),
            byte_width: 4,
        };
        let target = PointerOffsetTerm::Constant(8);
        let checkpoint = graph.read_equality_checkpoint();
        graph.add_offset_equality(&read, &target);
        assert_eq!(
            graph.read_equalities_since(&checkpoint).equalities,
            vec![Proposition::ConditionIs(
                ConditionTerm::PointerOffsetEqual(Box::new(read), Box::new(target)),
                true
            )]
        );
    }

    #[cfg(test)]
    mod scaling_tests {
        include!("../../scaling_tests/kernel/equality_graph/inputs/read_trace_tests.rs");
    }
}
