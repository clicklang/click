//! Definitions for report-local labels, never additional proof evidence.
use super::*;
use crate::kernel::{CMemoryDerivation, CValue, PointerBlock};

const MAX_ROUNDS: usize = 96;
const MAX_LEGEND_BYTES: usize = 12 * 1024;

fn short(text: &str) -> String {
    let mut end = text.len().min(300);
    while !text.is_char_boundary(end) {
        end -= 1;
    }
    if end < text.len() {
        format!("{}…", &text[..end])
    } else {
        text.into()
    }
}

impl SnapshotLabels {
    pub(crate) fn immutable_pointer_name(&mut self, pointer: &Pointer, name: &str) {
        if self.pointer_sources.len() < 128 {
            self.pointer_sources
                .entry(pointer.clone())
                .or_insert_with(|| short(name));
        }
    }

    // Anonymous identities remain distinct without presenting a mutable C local
    // as though it named this value at every program point.
    fn legend_symbol(&mut self, variable: Variable) -> String {
        let next = self.anonymous_names.len();
        self.anonymous_names
            .entry(variable)
            .or_insert_with(|| format!("symbol {}", alphabetic_label(next)))
            .clone()
    }

    fn legend_bits(&mut self, value: &Bitvector32Term) -> String {
        match value {
            Bitvector32Term::Constant(value) => value.to_string(),
            Bitvector32Term::Int64Constant(value) => value.to_string(),
            Bitvector32Term::UInt64Constant(value) => value.to_string(),
            Bitvector32Term::Variable(variable) => {
                if let Some((memory, address)) =
                    crate::kernel::registered_load_for_variable(variable)
                {
                    return format!(
                        "read({}, address {})",
                        self.snapshot_name(memory.memory()),
                        self.pointer_value_name(&address)
                    );
                }
                format!(
                    "<{}; source binding unavailable>",
                    self.legend_symbol(*variable)
                )
            }
            Bitvector32Term::MemoryLoad(memory, address, kind) => format!(
                "{}-byte read({}, address {})",
                kind.byte_width(),
                self.snapshot_name(memory.memory()),
                self.pointer_value_name(address)
            ),
            _ => "<scalar construction not available in this legend>".into(),
        }
    }

    fn legend_offset(&mut self, offset: &PointerOffsetTerm, depth: usize) -> String {
        if depth == 0 {
            return "<offset depth limit>".into();
        }
        match offset {
            PointerOffsetTerm::Constant(bytes) => format!("{bytes} bytes"),
            PointerOffsetTerm::Variable(variable) => {
                format!(
                    "({}) bytes",
                    self.legend_bits(&Bitvector32Term::Variable(*variable))
                )
            }
            PointerOffsetTerm::Add(left, right) => format!(
                "({} + {})",
                self.legend_offset(left, depth - 1),
                self.legend_offset(right, depth - 1)
            ),
            PointerOffsetTerm::Int32Scaled { value, byte_width } => {
                format!("int32({}) * {byte_width} bytes", self.legend_bits(value))
            }
            PointerOffsetTerm::Int64Scaled {
                value,
                byte_width,
                unsigned,
            } => {
                let kind = if *unsigned { "uint64" } else { "int64" };
                format!("{kind}({}) * {byte_width} bytes", self.legend_bits(value))
            }
        }
    }

    fn legend_pointer(&mut self, pointer: &Pointer) -> String {
        if let Some(name) = self.pointer_sources.get(pointer) {
            return name.clone();
        }
        if pointer == &Pointer::null() {
            return "null pointer (0)".into();
        }
        if let Some(read) = pointer.as_loaded_value() {
            let snapshot = self.snapshot_name(read.defining_memory.memory());
            let address = self.pointer_value_name(&read.defining_address);
            let displacement = self.legend_offset(&read.displacement, 4);
            return format!("pointer read at {snapshot}, address {address}, plus {displacement}");
        }
        if let Some(Bitvector32Term::MemoryLoad(memory, address, _)) =
            crate::kernel::logical_pointer_read_term(pointer)
        {
            return format!(
                "pointer read at {}, address {}",
                self.snapshot_name(memory.memory()),
                self.pointer_value_name(&address)
            );
        }
        let base = Pointer {
            block: pointer.block.clone(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let base_name = if let Some(name) = self.pointer_sources.get(&base) {
            name.clone()
        } else {
            match &pointer.block {
                PointerBlock::Concrete(name) => format!("object `{}`", short(name)),
                PointerBlock::Symbolic(variable) | PointerBlock::ExternalObject(variable) => {
                    format!(
                        "<{}; source binding unavailable>",
                        self.legend_symbol(*variable)
                    )
                }
                PointerBlock::ExternalArgument => "external argument address base".into(),
                PointerBlock::Heap(_) => "<heap allocation; source origin unavailable>".into(),
                PointerBlock::Function(name) => format!("function `{}`", short(name)),
                _ => "<pointer base; source origin unavailable>".into(),
            }
        };
        format!("{base_name} + {}", self.legend_offset(&pointer.offset, 4))
    }

    fn legend_snapshot(&mut self, memory: &CMemory) -> String {
        let point = self
            .source_memories
            .iter()
            .find(|(known, point, _)| {
                point != "current" && (known.same_storage_roots(memory) || known == memory)
            })
            .map(|(_, point, _)| format!("recorded at {}; ", short(point)))
            .unwrap_or_default();
        let shared = crate::kernel::intern_c_memory_ref(memory);
        let Some(edge) = shared.derivation() else {
            return format!("{point}memory construction provenance unavailable");
        };
        let base = self.snapshot_name(edge.base().memory());
        let operation = match edge.as_ref() {
            CMemoryDerivation::Store { pointer, value, .. } => {
                let address = self.pointer_value_name(pointer);
                let value = match value {
                    CValue::Pointer(value) => self.pointer_value_name(value.pointer()),
                    CValue::Int32(bits)
                    | CValue::UInt32(bits)
                    | CValue::Int64(bits)
                    | CValue::UInt64(bits) => self.legend_bits(bits),
                    _ => "<stored value presentation unavailable>".into(),
                };
                format!("store {value} at address {address}")
            }
            CMemoryDerivation::CellsForgotten { .. } => {
                "cached cells forgotten (not a program write)".into()
            }
            CMemoryDerivation::CallHavoc { .. } => {
                "call effect: permitted memory may change".into()
            }
            CMemoryDerivation::LoopHavoc { .. } => {
                "loop effect: permitted memory may change".into()
            }
            other => format!("{} memory transition", other.kind_name()),
        };
        format!("{point}{operation}, based on {base}")
    }

    /// Expand references breadth-first under fixed entry/byte limits. Number
    /// order, rather than hash-map order, makes reports deterministic.
    pub(crate) fn trace_legend(&mut self) -> String {
        if self.pointer_values.is_empty() && self.memories.is_empty() {
            return String::new();
        }
        let mut output =
            String::from("\n\n  label definitions (recorded constructions, not additional facts):");
        if self.memories.len() > MAX_SNAPSHOT_LABELS {
            output.push_str("\n    Beyond the first 32 snapshots, labels reuse retained identities only; separately constructed equal memories may have different labels.");
        }
        let (mut pointer_index, mut memory_index) = (1, 0);
        for _ in 0..MAX_ROUNDS {
            let mut added = false;
            if let Some(pointer) = self
                .pointer_values
                .iter()
                .find_map(|(pointer, index)| (*index == pointer_index).then(|| pointer.clone()))
            {
                let definition = self.legend_pointer(&pointer);
                output.push_str(&format!(
                    "\n    value#{pointer_index} = {}",
                    short(&definition)
                ));
                pointer_index += 1;
                added = true;
            }
            if let Some(memory) = self.memories.get(memory_index).cloned() {
                let definition = self.legend_snapshot(&memory);
                output.push_str(&format!(
                    "\n    snapshot#{} = {}",
                    memory_index + 1,
                    short(&definition)
                ));
                memory_index += 1;
                added = true;
            }
            if output.len() + 700 > MAX_LEGEND_BYTES || !added {
                break;
            }
        }
        if pointer_index <= self.pointer_values.len() || memory_index < self.memories.len() {
            output.push_str("\n    … additional label definitions omitted (legend limit)");
        }
        output
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn legend_defines_loaded_address_and_displacement_recursively() {
        let memory = crate::kernel::intern_c_memory(CMemory::new());
        let base = Pointer::symbolic(Variable(986_401));
        let mut loaded = Pointer::loaded_value(&memory, &base);
        loaded.offset = PointerOffsetTerm::Constant(16);
        let mut labels = SnapshotLabels::default();
        labels.immutable_pointer_name(&base, "zid");
        assert_eq!(labels.pointer_value_name(&loaded), "value#1");
        let text = labels.trace_legend();
        assert!(
            text.contains("value#1 = pointer read at snapshot#1, address value#2, plus 16 bytes"),
            "{text}"
        );
        assert!(text.contains("value#2 = zid"), "{text}");
        assert!(
            text.contains("snapshot#1 = memory construction provenance unavailable"),
            "{text}"
        );
        assert_eq!(text, labels.trace_legend());
    }

    #[test]
    fn legend_shows_recorded_store_and_its_base() {
        let address = Pointer::symbolic(Variable(986_402));
        let memory =
            CMemory::new().store(address.clone(), CValue::Int32(Bitvector32Term::Constant(7)));
        let mut labels = SnapshotLabels::default();
        labels.immutable_pointer_name(&address, "p");
        labels.snapshot_name(&memory);
        let text = labels.trace_legend();
        assert!(
            text.contains("store 7 at address value#1, based on snapshot#2"),
            "{text}"
        );
        assert!(text.contains("value#1 = p"), "{text}");
    }

    #[test]
    fn legend_names_only_matching_recorded_memories() {
        let memory = CMemory::new().with_block("legend_recorded", 8);
        let mut labels = SnapshotLabels::default();
        let naming = std::rc::Rc::new((Vec::new(), Vec::new()));
        labels
            .source_memories
            .push((CMemory::new(), "unrelated_point".into(), naming.clone()));
        labels
            .source_memories
            .push((memory.clone(), "before_rotation".into(), naming));
        labels.snapshot_name(&memory);
        let text = labels.trace_legend();
        assert!(
            text.contains("snapshot#1 = recorded at before_rotation;"),
            "{text}"
        );
        assert!(
            !text.contains("snapshot#1 = recorded at unrelated_point;"),
            "{text}"
        );
    }

    #[test]
    fn legend_does_not_collapse_unknown_bases_or_use_mutable_names() {
        let mut labels = SnapshotLabels::default();
        for id in [986_403, 986_404] {
            labels.source_name(Variable(id), "sibling".into());
            labels.pointer_value_name(&Pointer::symbolic(Variable(id)));
        }
        let text = labels.trace_legend();
        assert!(text.contains("symbol A"), "{text}");
        assert!(text.contains("symbol B"), "{text}");
        assert!(!text.contains("sibling"), "{text}");
    }

    #[test]
    fn legend_bounds_recursive_output_and_preserves_failure_tail() {
        let mut labels = SnapshotLabels::default();
        for id in 0..128 {
            let pointer = Pointer::symbolic(Variable(987_000 + id));
            labels.immutable_pointer_name(&pointer, &"é".repeat(200));
            labels.pointer_value_name(&pointer);
        }
        let legend = labels.trace_legend();
        assert!(legend.len() <= MAX_LEGEND_BYTES);
        assert!(legend.contains("additional label definitions omitted"));
        let mut trace = "é".repeat(32 * 1024);
        trace.push_str("failure comparison retained");
        crate::surface::proof_trace::append_legend(&mut trace, &mut labels);
        assert!(trace.len() <= 64 * 1024);
        assert!(trace.contains("failure comparison retained"));
        assert!(trace.contains("earlier trace text omitted"));
    }
}
