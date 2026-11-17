// Scaling tests of `src/kernel/proof/arithmetic_special.rs` (module `tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;
use crate::kernel::CompareRelation;
use crate::kernel::MachineBinaryOp;
use crate::kernel::MachineIntegerType;
use crate::kernel::binary_node;
use crate::kernel::{MachineCastSpelling, MachineTerm};

#[test]
fn cast_identity_reads_interned_integer_operands_without_walking_their_dags() {
    use crate::kernel::{IntegerTerm, MachineIntegerType, Variable};
    let mut samples = Vec::new();
    for size in [8, 32, 128, 512] {
        let _session = crate::kernel::VerificationSession::enter();
        let mut value = IntegerTerm::Variable(Variable(892_000));
        for index in 0..size {
            value = IntegerTerm::add(value, IntegerTerm::Variable(Variable(893_000 + index)));
        }
        let cast = MachineTerm::IntegerToMachine {
            value: value.into(),
            destination: MachineIntegerType::Int64,
        };
        let duplicate = cast.clone();
        let (equal, work) = crate::instrumentation::measure_deterministic_work(|| {
            bitvector_equal(&cast, &duplicate)
        });
        assert!(equal);
        assert!(work <= 16, "{size}: {work}");
        samples.push(work);
    }
    assert!(
        samples.windows(2).all(|pair| pair[0] == pair[1]),
        "{samples:?}"
    );
}

#[test]
fn unsigned_widening_identity_work_scales_with_operand_payload() {
    let mut samples = Vec::new();
    for size in [4, 16, 64, 96] {
        let mut value = MachineTerm::Variable(crate::kernel::Variable(994_111));
        for _ in 0..size {
            value = binary_node!(
                Int32,
                Add,
                Box::new(value),
                Box::new(MachineTerm::constant(0))
            );
        }
        let widened = MachineTerm::legacy_cast(MachineCastSpelling::UInt64From32, Box::new(value));
        let (same, work) = crate::instrumentation::measure_deterministic_work(|| {
            bitvector_equal(&widened, &widened)
        });
        assert!(same);
        assert!(work <= size * 8 + 8, "{size}: {work}");
        samples.push((size, work));
    }
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1 * pair[1].0.div_ceil(pair[0].0),
            "{samples:?}"
        );
    }
}

#[test]
fn arithmetic_read_atoms_keep_state_identity_without_scanning_storage() {
    use crate::kernel::{LoadKind, ProgramValue, SymbolicMemory, Variable, intern_memory};
    let mut samples = Vec::new();
    for size in [8, 64, 512] {
        let _session = crate::kernel::VerificationSession::enter();
        let address = Pointer::symbolic(Variable(894_000));
        let mut memory = SymbolicMemory::new();
        for index in 0..size {
            memory = memory.store(
                Pointer::symbolic(Variable(895_000 + index)),
                ProgramValue::Int32(MachineTerm::constant(7)),
            );
        }
        let memory = intern_memory(memory);
        let read = MachineTerm::MemoryLoad(
            crate::kernel::ProgramPoint::at(&memory),
            Box::new(address.clone()),
            LoadKind::Bits64,
        );
        let duplicate = read.clone();
        let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
            assert!(charge_bitvector(&read));
            assert!(bitvector_equal(&read, &duplicate));
            assert_eq!(bounded_term_hash(&read), bounded_term_hash(&duplicate));
            assert!(bounded_term_hash(&read).is_some());
        });
        let changed = intern_memory(memory.memory().clone().store(
            address.clone(),
            ProgramValue::UInt64(MachineTerm::uint64_constant(9)),
        ));
        let different = MachineTerm::MemoryLoad(
            crate::kernel::ProgramPoint::at(&changed),
            Box::new(address.clone()),
            LoadKind::Bits64,
        );
        assert!(!bitvector_equal(&read, &different));
        assert!(!bitvector_equal(
            &read,
            &MachineTerm::MemoryLoad(
                crate::kernel::ProgramPoint::at(&memory),
                Box::new(address),
                LoadKind::Int32
            )
        ));
        samples.push(work);
    }
    assert!(
        samples.windows(2).all(|pair| pair[0] == pair[1]),
        "{samples:?}"
    );
}

#[test]
fn shared_tagged_word_certificates_preserve_bounds_without_exports() {
    use crate::kernel::{KernelTerm, KernelTermExport, MachineOperandView as View};
    let mut previous = None;
    for size in [8, 32, 96] {
        let _session = crate::kernel::VerificationSession::enter();
        let format = MachineIntegerType::UInt64;
        let address = MachineTerm::PointerAddress(
            Box::new(pointer(PointerOffsetTerm::Constant(0))),
            crate::kernel::AddressObjectClass::NONE,
        );
        let mut root = KernelTerm::retained_machine_operand(format, View::Legacy(&address));
        let one = KernelTerm::retained_machine_operand(
            format,
            View::Legacy(&MachineTerm::uint64_constant(1)),
        );
        for _ in 0..size {
            root = KernelTerm::machine_binary_shared(
                format,
                MachineBinaryOp::Add,
                [root, one.clone()],
            );
        }
        let condition = crate::kernel::machine_integer::comparison::condition_for_operand_views(
            format,
            CompareRelation::Equal,
            [View::Shared(&root), View::Shared(&root)],
        );
        let goal = Proposition::ConditionIs(condition.clone(), true);
        let exports = KernelTermExport::machine_export_count();
        let (valid, work) = crate::instrumentation::measure_deterministic_work(|| {
            pointer_word_from_alignment(&[], &goal)
        });
        assert!(valid, "size={size}");
        assert!(!pointer_word_from_alignment(
            &[],
            &Proposition::ConditionIs(condition, false)
        ));
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        if let Some(previous) = previous {
            assert!(
                work <= previous * 5,
                "size={size}, work={work}, previous={previous}"
            );
        }
        previous = Some(work);
    }
}
