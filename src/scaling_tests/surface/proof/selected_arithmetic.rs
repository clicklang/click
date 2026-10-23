// Scaling tests of `src/surface/proof/selected_arithmetic.rs`: deterministic
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
        // `to_integer(x) + 1` is Integer arithmetic, so the goals stay Integer
        // claims: `to_integer(x) <= -1` alone would be the native `x <= -1`,
        // which plain selected-premise arithmetic decides with no bridge.
        let successor = ContractExpression::Add(
            Box::new(to_integer(&written)),
            Box::new(integer_literal("1")),
        );
        let surface_goal = relate(successor.clone(), integer_literal("0"), Relation::LessEqual);
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
            proof.try_bridged_selected_arithmetic()
        });
        assert!(
            result.unwrap().is_none(),
            "upper bounds do not imply x + 1 <= 0"
        );
        let constructions = BRIDGE_ESTABLISHMENTS.with(std::cell::Cell::get) - before;
        assert_eq!(
            constructions, 0,
            "an unprovable goal must not construct bridge facts"
        );
        let positive_surface = relate(successor, integer_literal("100"), Relation::LessEqual);
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
            .try_bridged_selected_arithmetic()
            .unwrap()
            .expect("the bound x < 100 proves x + 1 <= 100");
        assert!(closed.is_complete());
        // Selected-premise arithmetic reads the native bound `x < 100` as its Integer reading,
        // the same fact in its one form, so no carrying bridge is built.
        assert_eq!(
            BRIDGE_ESTABLISHMENTS.with(std::cell::Cell::get) - before,
            0,
            "a native bound needs no constructed bridge"
        );
        samples.push(work);
    }
    assert!(
        samples.windows(2).all(|pair| pair[1] <= 5 * pair[0]),
        "{samples:?}"
    );
    eprintln!("unprovable integer bridge work: {samples:?}");
}

#[test]
fn disequality_refutation_work_ignores_unrelated_facts() {
    let mut samples = Vec::new();
    for size in [4, 16, 64] {
        let (k, j, y) = (
            Bitvector32Term::Variable(Variable(911_001)),
            Bitvector32Term::Variable(Variable(911_002)),
            Bitvector32Term::Variable(Variable(911_003)),
        );
        let written =
            |name: &str| ContractExpression::CFragment(CExpression::Variable(name.into()));
        let mut surfaces = SurfacePropositionMap::default();
        let order = Proposition::ConditionIs(
            ConditionTerm::Bitvector32SignedLessThan(Box::new(k.clone()), Box::new(j.clone())),
            true,
        );
        surfaces
            .record_lowering(&relate(written("k"), written("j"), Relation::Less), &order)
            .unwrap();
        let mut facts = vec![order];
        // Bounds on an unrelated value, which the refutation of `k == j`
        // never reads.
        for index in 0..size {
            let fact = Proposition::ConditionIs(
                ConditionTerm::Bitvector32SignedLessThan(
                    Box::new(y.clone()),
                    Box::new((100 + index).into()),
                ),
                true,
            );
            let surface = relate(
                written("y"),
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
            values: BTreeMap::from([
                ("k".into(), CValue::Int32(k)),
                ("j".into(), CValue::Int32(j)),
                ("y".into(), CValue::Int32(y)),
            ]),
            array_refs: BTreeMap::new(),
            requires: facts.clone(),
            surface_requirements: surfaces,
        };
        let predicates = PredicateEnvironment::new(&[]);
        let functions = ClickFunctionEnvironment::new(&[]);
        let theorems = TheoremEnvironment::with_standard_library(&[]).unwrap();
        let definitions = SpecDefinitions::new(&predicates, &functions);
        let surface_goal = ClickProposition::Comparison {
            left: written("k"),
            operator: ComparisonOperator::NotEqual,
            right: written("j"),
        };
        let lowering = Proof::for_pure_goal(
            "disequality",
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
            "disequality",
            &facts,
            goal,
            surface_goal,
            &context,
            definitions,
            &theorems,
        );
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            proof.try_disequality_by_selected_refutation()
        });
        let closed = result.unwrap().expect("k < j refutes k == j, so k != j");
        assert!(closed.is_complete());
        samples.push(work);
    }
    assert!(
        samples.windows(2).all(|pair| pair[1] <= 2 * pair[0]),
        "{samples:?}"
    );
    eprintln!("disequality refutation work: {samples:?}");
}
