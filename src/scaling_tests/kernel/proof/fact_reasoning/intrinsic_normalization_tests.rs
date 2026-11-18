// Fixed intrinsic normalization beside growing related and unrelated facts.
#[test]
fn intrinsic_integer_normalization_reads_only_selected_bounds() {
    use crate::kernel::{IntegerTerm, MachineBinaryOp, MachineTerm, SharedIntegerTerm};
    use num_bigint::BigInt;
    let ty = MachineIntegerType::UInt64;
    let word = MachineTerm::Variable(Variable(973_001));
    let a: SharedIntegerTerm = IntegerTerm::from_machine(ty, word.clone()).unwrap().into();
    let b: SharedIntegerTerm = IntegerTerm::Variable(Variable(973_002)).into();
    let one: SharedIntegerTerm = IntegerTerm::constant_i64(1).into();
    let sum: SharedIntegerTerm = IntegerTerm::Add(a.clone(), one).into();
    let actual: SharedIntegerTerm = IntegerTerm::from_machine(
        ty,
        MachineTerm::Binary {
            format: ty,
            op: MachineBinaryOp::Add,
            left: Box::new(word),
            right: Box::new(MachineTerm::uint64_constant(1)),
        },
    )
    .unwrap()
    .into();
    let le = |a: SharedIntegerTerm, b: SharedIntegerTerm| {
        Proposition::condition_is(ConditionTerm::IntegerLessEqual(a, b), true)
    };
    let literal = |n: i64| SharedIntegerTerm::from(IntegerTerm::constant_i64(n));
    let identity =
        Proposition::condition_is(ConditionTerm::IntegerEqual(actual, sum.clone()), true);
    let bridge_bounds = vec![
        le(literal(0), sum.clone()),
        le(sum, IntegerTerm::constant(BigInt::from(u64::MAX)).into()),
    ];
    let product: SharedIntegerTerm = IntegerTerm::Multiply(a.clone(), b.clone()).into();
    let product_goal = le(product, literal(100));
    let product_bounds = vec![
        le(literal(0), a.clone()),
        le(a.clone(), literal(10)),
        le(literal(0), b.clone()),
        le(b, literal(10)),
    ];
    for (goal, bounds) in [(identity, bridge_bounds), (product_goal, product_bounds)] {
        for related in [false, true] {
            let mut curve = Vec::new();
            for size in [4, 16, 64] {
                let mut facts = bounds.clone();
                for i in 0..size {
                    let subject = if related {
                        a.clone()
                    } else {
                        IntegerTerm::Variable(Variable(974_000 + i)).into()
                    };
                    facts.push(le(literal(-1000 - i as i64), subject));
                }
                let facts = PureFactStore::from_ordered(&facts);
                let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                    normalize_using_conditions(&goal, &bounds, &facts)
                });
                result.unwrap();
                curve.push(work);
                assert!(
                    normalize_using_conditions(&goal, &bounds[..bounds.len() - 1], &facts).is_err(),
                    "an omitted bound read ambient facts"
                );
            }
            assert!(curve[0] > 0);
            assert!(
                curve.iter().all(|work| *work <= 3 * curve[0]),
                "intrinsic checking scanned facts (related={related}): {curve:?}"
            );
        }
    }
}
