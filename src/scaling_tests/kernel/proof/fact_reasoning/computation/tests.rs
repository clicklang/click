// Goal-local computational refusal must not traverse the selected states.
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
        let left = MachineTerm::MemoryLoad(
            ProgramPoint::at(&before),
            Box::new(pointer.clone()),
            LoadKind::Int32,
        );
        let right = MachineTerm::MemoryLoad(
            ProgramPoint::at(&after),
            Box::new(pointer.clone()),
            LoadKind::Int32,
        );
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

#[test]
fn monomial_normalization_work_tracks_written_factors() {
    let samples = [4, 16, 64].map(|size| {
        let factors = (0..size)
            .map(|n| IntegerTerm::var(Variable(880000 + n)))
            .collect::<Vec<_>>();
        let product =
            |values: Vec<IntegerTerm>| values.into_iter().reduce(IntegerTerm::multiply).unwrap();
        let a = product(factors.clone());
        let b = product(factors.into_iter().rev().collect());
        let condition = ConditionTerm::IntegerEqual(a.clone().into(), b.clone().into());
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            integer_linear_comparison(&condition)
        });
        assert_eq!(result, Some(true));
        assert_ne!(
            integer_linear_comparison(&ConditionTerm::IntegerEqual(
                a.into(),
                IntegerTerm::add(b, IntegerTerm::constant_i64(1)).into()
            )),
            Some(true)
        );
        work
    });
    assert!(samples.windows(2).all(|p| p[1] <= 6 * p[0]), "{samples:?}");
}

#[test]
fn distribution_check_is_one_local_step_and_never_expands_a_polynomial() {
    let [a, b, c, d]: [IntegerTerm; 4] =
        std::array::from_fn(|n| IntegerTerm::var(Variable(881000 + n as u64)));
    let mul = IntegerTerm::multiply;
    let add = IntegerTerm::add;
    let step = ConditionTerm::IntegerEqual(
        mul(add(a.clone(), b.clone()), c.clone()).into(),
        add(mul(a.clone(), c.clone()), mul(b.clone(), c)).into(),
    );
    assert!(integer_distribution_step(&step));
    let full = ConditionTerm::IntegerEqual(
        mul(add(a.clone(), b.clone()), add(a.clone(), d.clone())).into(),
        add(
            add(mul(a.clone(), a.clone()), mul(a.clone(), d.clone())),
            add(mul(b.clone(), a), mul(b, d)),
        )
        .into(),
    );
    assert!(!integer_distribution_step(&full));
    assert_eq!(integer_linear_comparison(&full), None);
}
