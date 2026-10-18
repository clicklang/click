// Scaling tests of `src/surface/proof/solver_bridges.rs`: deterministic
// work and proof construction measured at several input sizes.

use super::*;
use crate::surface::proof::pure_theorems::PureTheoremContext;

#[test]
fn failed_integer_bridge_does_not_construct_unused_facts() {
    let mut samples = Vec::new();
    for size in [4, 16, 64] {
        let value = Bitvector32Term::Variable(Variable(910_001));
        let written = ContractExpression::CFragment(CExpression::Variable("x".into()));
        let mut facts = Vec::new();
        let mut surfaces = SurfacePropositionMap::default();
        for index in 0..size {
            let fact = Proposition::ConditionIs(
                ConditionTerm::Bitvector32SignedLessThan(
                    Box::new(value.clone()),
                    Box::new((100 + index).into()),
                ),
                true,
            );
            let surface = relate(
                written.clone(),
                ContractExpression::CFragment(CExpression::Value(int32(100 + index))),
                Relation::Less,
            );
            surfaces.record_lowering(&surface, &fact).unwrap();
            facts.push(fact);
        }
        let context = PureTheoremContext {
            diagnostic_names: Default::default(),
            declaration_bindings: BTreeMap::new(),
            integer_values: crate::persistent::PersistentMap::default(),
            memory: CMemory::new(),
            values: BTreeMap::from([("x".into(), CValue::Int32(value))]),
            array_refs: BTreeMap::new(),
            requires: facts.clone(),
            surface_requirements: surfaces,
        };
        let predicates = PredicateEnvironment::new(&[]);
        let functions = ClickFunctionEnvironment::new(&[]);
        let theorems = TheoremEnvironment::with_standard_library(&[]).unwrap();
        let definitions = SpecDefinitions::new(&predicates, &functions);
        let surface_goal = relate(
            to_integer(&written),
            integer_literal("-1"),
            Relation::LessEqual,
        );
        let lowering = Proof::for_pure_goal(
            "unprovable bridge",
            &facts,
            Proposition::ConditionIs(ConditionTerm::Constant(true), true),
            &context,
            definitions,
            &theorems,
        );
        let goal = lowering
            .lower_surface_proposition(&surface_goal, "test goal")
            .unwrap();
        let proof = Proof::for_pure_surface_goal(
            "unprovable bridge",
            &facts,
            goal,
            surface_goal,
            &context,
            definitions,
            &theorems,
        );
        let before = BRIDGE_ESTABLISHMENTS.with(std::cell::Cell::get);
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            proof.try_bridged_solver_closure()
        });
        assert!(
            result.unwrap().is_none(),
            "upper bounds do not imply x <= -1"
        );
        let constructions = BRIDGE_ESTABLISHMENTS.with(std::cell::Cell::get) - before;
        assert_eq!(
            constructions, 0,
            "an unprovable goal must not construct bridge facts"
        );
        let positive_surface = relate(
            to_integer(&written),
            integer_literal("99"),
            Relation::LessEqual,
        );
        let positive_goal = lowering
            .lower_surface_proposition(&positive_surface, "positive bridge goal")
            .unwrap();
        let positive = Proof::for_pure_surface_goal(
            "one selected bridge",
            &facts,
            positive_goal,
            positive_surface,
            &context,
            definitions,
            &theorems,
        );
        let before = BRIDGE_ESTABLISHMENTS.with(std::cell::Cell::get);
        let closed = positive
            .try_bridged_solver_closure()
            .unwrap()
            .expect("the bound x < 100 proves its Integer reading");
        assert!(closed.is_complete());
        assert_eq!(
            BRIDGE_ESTABLISHMENTS.with(std::cell::Cell::get) - before,
            1,
            "construct the selected bridge once"
        );
        samples.push(work);
    }
    assert!(
        samples.windows(2).all(|pair| pair[1] <= 5 * pair[0]),
        "{samples:?}"
    );
    eprintln!("unprovable integer bridge work: {samples:?}");
}
