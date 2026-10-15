// Scaling checks for checked source lease preparation.
use super::*;

#[test]
fn source_scalar_lease_plan_preparation_scales_with_selected_function() {
    let mut measurements = vec![];
    for size in [16, 64, 256, 1024] {
        let mut export = export();
        let statements = &mut export.functions[0].mir.as_mut().unwrap().blocks[0].statements;
        for _ in 0..size {
            statements.insert(0, assign(local("x"), E::Integer { value: 1 }));
        }
        let (program, work) =
            crate::instrumentation::measure_deterministic_work(|| body(&export, "locked-source"));
        assert!(leaves(&program).iter().any(
            |s| matches!(s, CStatement::Assign { source, .. } if source.lease_plan().is_some())
        ));
        measurements.push((size, work));
    }
    eprintln!("source scalar lease preparation: {measurements:?}");
    for pair in measurements.windows(2) {
        assert!(pair[1].1 <= pair[0].1 * 5 + 100, "{measurements:?}");
    }
}

#[test]
fn source_scalar_lease_alias_plan_preparation_scales_with_alias_chain() {
    let mut measurements = vec![];
    for count in [16, 64, 256, 1024] {
        let source = alias_export(count);
        let (program, work) =
            crate::instrumentation::measure_deterministic_work(|| body(&source, "locked-source"));
        let statements = leaves(&program);
        assert_eq!(statements.iter().filter(|s| matches!(s, CStatement::Assign { source, .. } if source.lease_plan().is_some())).count(), 1);
        assert_eq!(
            statements
                .iter()
                .filter(|s| matches!(s, CStatement::EndScalarReference(_)))
                .count(),
            1
        );
        measurements.push((count, work));
    }
    eprintln!("source scalar lease alias preparation: {measurements:?}");
    for pair in measurements.windows(2) {
        assert!(pair[1].1 <= pair[0].1 * 5 + 100, "{measurements:?}");
    }
}

#[test]
fn source_scalar_lease_read_ending_preparation_scales_with_aliases() {
    let mut measurements = vec![];
    for count in [16, 64, 256, 1024] {
        let source = read_export(count);
        let (program, work) =
            crate::instrumentation::measure_deterministic_work(|| body(&source, "locked-source"));
        let endings = leaves(&program)
            .into_iter()
            .filter(|statement| matches!(statement, CStatement::EndScalarReference(_)))
            .count();
        assert_eq!(endings, 1);
        measurements.push((count, work));
    }
    eprintln!("source scalar lease read-ending preparation: {measurements:?}");
    for pair in measurements.windows(2) {
        assert!(pair[1].1 <= pair[0].1 * 5 + 100, "{measurements:?}");
    }
}

#[test]
fn source_scalar_lease_explicit_nested_preparation_is_linear_in_depth() {
    let mut measurements = vec![];
    for depth in [16, 64, 256, 1024] {
        let source = nested_export(depth);
        let (program, work) =
            crate::instrumentation::measure_deterministic_work(|| body(&source, "locked-source"));
        assert_eq!(ends(&program).len(), depth);
        measurements.push((depth, work));
    }
    eprintln!("explicit nested source preparation: {measurements:?}");
    for pair in measurements.windows(2) {
        assert!(pair[1].1 <= pair[0].1 * 5 + 100, "{measurements:?}");
    }
}
