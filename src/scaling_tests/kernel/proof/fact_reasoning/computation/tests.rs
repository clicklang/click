// Goal-local computational refusal must not traverse the selected snapshots.
use super::*;

#[test]
fn computation_refusal_is_independent_of_memory_history() {
    let mut costs = Vec::new();
    for size in [4, 16, 64, 256] {
        let _session = VerificationSession::enter();
        let pointer = Pointer {
            block: PointerBlock::Concrete("computation-read".into()),
            offset: PointerOffsetTerm::Constant(0),
        };
        let other = Pointer {
            block: PointerBlock::Concrete("computation-write".into()),
            offset: PointerOffsetTerm::Constant(0),
        };
        let before = crate::kernel::intern_memory(
            Memory::new()
                .with_block("computation-read", 4)
                .with_block("computation-write", 4),
        );
        let mut after = before.memory().clone();
        for _ in 0..size {
            after = after.store(other.clone(), ProgramValue::Int32(MachineTerm::constant(7)));
        }
        let after = crate::kernel::intern_memory(after);
        let left =
            MachineTerm::MemoryLoad(before.clone(), Box::new(pointer.clone()), LoadKind::Int32);
        let right = MachineTerm::MemoryLoad(after, Box::new(pointer.clone()), LoadKind::Int32);
        let read_equality =
            Proposition::ConditionIs(ConditionTerm::equal(left.clone(), right), true);
        let add = |left, right| MachineTerm::Binary {
            format: MachineIntegerType::Int32,
            op: MachineBinaryOp::Add,
            left: Box::new(left),
            right: Box::new(right),
        };
        let rearranged = Proposition::ConditionIs(
            ConditionTerm::equal(
                add(left.clone(), MachineTerm::constant(1)),
                add(MachineTerm::constant(1), left),
            ),
            true,
        );
        let ((resolved, cancelled), work) =
            crate::instrumentation::measure_deterministic_work(|| {
                (computes_leaf(&read_equality), computes_leaf(&rearranged))
            });
        assert!(!resolved);
        assert!(cancelled);
        costs.push(work);
        assert!(!computes_leaf(&Proposition::MemoryLoadable {
            memory: before.memory().clone(),
            base: pointer,
            bytes: MachineTerm::constant(4),
            wide: false,
        }));
    }
    assert!(
        costs[0] > 0 && costs.iter().all(|work| *work == costs[0]),
        "{costs:?}"
    );
}
