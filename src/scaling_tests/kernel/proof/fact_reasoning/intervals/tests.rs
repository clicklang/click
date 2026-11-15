#[test]
fn one_operation_interval_check_ignores_ambient_related_and_unrelated_facts() {
    let (goal,bounds)=inputs(MachineBinaryOp::Add,1);
    for related in [false,true] {
        let samples=[4,16,64].map(|size| {
            let mut ambient=bounds.clone();
            for index in 0..size {
                let subject=observe(MachineTerm::Variable(Variable(if related {987_701} else {988_000+index})));
                ambient.push(le(literal(-1000-index as i64),subject));
            }
            let facts=ProofFacts::from_ordered(&ambient);
            let (result,work)=crate::instrumentation::measure_deterministic_work(||normalize_using_conditions(&goal,&bounds,&facts));
            result.unwrap();
            assert!(normalize_using_conditions(&goal,&bounds[..1],&facts).is_err());
            work
        });
        assert!(samples[0]>0);
        assert!(samples.iter().all(|work|*work<=2*samples[0]),"ambient scan: {samples:?}");
    }
}
#[test]
fn one_operation_interval_work_tracks_only_explicit_premises() {
    let (goal,bounds)=inputs(MachineBinaryOp::Add,1);
    let samples=[4,16,64].map(|size| {
        let mut selected=bounds.clone();
        for index in 0..size {selected.push(le(literal(-100),observe(MachineTerm::Variable(Variable(988_000+index)))));}
        let facts=ProofFacts::from_ordered(&selected);
        let (result,work)=crate::instrumentation::measure_deterministic_work(||normalize_using_conditions(&goal,&selected,&facts));result.unwrap();work
    });
    assert!(samples.windows(2).all(|pair|pair[1]<=5*pair[0]),"superlinear explicit-input work: {samples:?}");
}
