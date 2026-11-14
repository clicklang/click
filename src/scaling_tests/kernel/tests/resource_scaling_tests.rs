//! Deterministic scaling regressions for resource-context validity.
//!
//! A call composes its ensured resources into the caller's frame and checks
//! that the result is still a partition. Only indexed candidates can violate
//! that — an identity held twice, a block owning two ranges, a base an exact
//! pointer equality joins to another block — so the check must cost work
//! logarithmic in the caller's unrelated allocations and instances rather
//! than proportional to them. Each test measures charged deterministic work
//! at four sizes and prints the numbers in its assertion messages.

use super::*;
use crate::kernel::{CompareRelation, MachineIntegerType};

// Keep large explicit-body sweeps separate from ambient-context setup. The
// latter use 4..256 elements (8..512 for the two 64-unit logarithmic slopes):
// even one charged scan exceeds their unchanged logarithmic bounds.
const SIZES: [usize; 4] = [16, 64, 256, 1024];

/// The identity of the block the measured operation targets; the unrelated
/// ones take identities below it.
const TARGET_HEAP: u64 = 1_000_000;

fn heap_base(identity: u64) -> Pointer {
    Pointer {
        block: PointerBlock::Heap(identity),
        offset: PointerOffsetTerm::Constant(0),
    }
}

fn owned_range(base: Pointer, start: u32, end: u32) -> ResourceFact {
    ResourceFact::own_memory(MemoryRange::new(
        base,
        MachineTerm::constant(start),
        MachineTerm::constant(end),
    ))
}

fn owned_instance(identity: u64) -> ResourceFact {
    let schema = ResourceFieldSchema::new(vec![(
        "revision".into(),
        ResourceFieldType::Program(ProgramType::Int32),
    )])
    .unwrap();
    ResourceFact::own(Resource::Instance(
        ResourceInstance::new(
            Variable(identity),
            "counter".into(),
            Vec::new().into(),
            schema,
            vec![int32(0).into()].into(),
        )
        .unwrap(),
    ))
}

/// A caller frame holding `unrelated` heap allocations, each owning one
/// range, and as many unrelated resource instances, beside a target block
/// owning two adjacent ranges.
fn frame_with_unrelated_allocations(unrelated: usize) -> ResourceContext {
    ResourceContext::new()
        .unchecked_with_facts((0..unrelated).flat_map(|index| {
            [
                owned_range(heap_base(index as u64 + 1), 0, 4),
                owned_instance(TARGET_HEAP + 1 + index as u64),
            ]
        }))
        .unchecked_with_facts([
            owned_range(heap_base(TARGET_HEAP), 0, 4),
            owned_range(heap_base(TARGET_HEAP), 4, 8),
        ])
}

fn pointer_equal(left: Pointer, right: Pointer) -> ConditionTerm {
    ConditionTerm::PointerEqual(Box::new(left), Box::new(right))
}

fn symbolic_base(identity: u64) -> Pointer {
    Pointer {
        block: PointerBlock::Symbolic(Variable(identity)),
        offset: PointerOffsetTerm::Constant(0),
    }
}

/// One exact equality naming the target block, so the cross-block alias walk
/// has a candidate to visit.
fn assumptions_aliasing_the_target() -> PureFactContext {
    PureFactContext::new().assume_condition(
        pointer_equal(heap_base(TARGET_HEAP), symbolic_base(2 * TARGET_HEAP)),
        true,
    )
}

fn log2(size: usize) -> f64 {
    (size as f64).log2()
}

fn assert_constant_plus_log_growth(what: &str, samples: &[(usize, usize)], slope: f64) {
    eprintln!("{what} (N, units): {samples:?}");
    let (smallest, base_work) = samples[0];
    for (size, work) in samples {
        let allowed = base_work as f64 + slope * (log2(*size) - log2(smallest));
        assert!(
            (*work as f64) <= allowed,
            "{what}: {size} unrelated resources charged {work} units, above {allowed:.1} \
             (constant plus {slope}·log2 growth): {samples:?}"
        );
    }
}

#[test]
#[ignore = "nightly: 3.8s in the parallel gate"]
fn private_local_copy_ignores_unrelated_resources() {
    for pointer_copy in [false, true] {
        for address_backed in [false, true] {
            let mut samples = Vec::new();
            for size in [8usize, 32, 128, 512] {
                let _session = crate::kernel::VerificationSession::enter();
                crate::kernel::set_never_address_taken_locals(
                    std::iter::once("target".to_string())
                        .chain((0..size).map(|index| format!("beside_{index}")))
                        .collect(),
                );
                let declare = |state: &ExecutionState, name: &str, c_type: ProgramType| {
                    let mut paths = execute_execution_statement_paths(
                        state,
                        &program_declare(name, c_type),
                        &PureFactContext::new(),
                        ExecutionContext::execute_bodies(&ExecutionEnvironment::new()),
                        &mut ExecutionBudget::default(),
                    )
                    .expect("the private local declares");
                    assert_eq!(paths.len(), 1);
                    let StatementOutcome::Normal(next) = paths.remove(0).outcome else {
                        panic!("declaration did not have a normal outcome");
                    };
                    *next
                };
                let (c_type, initial, value, expression) = if pointer_copy {
                    let value = ProgramValue::typed_pointer(
                        heap_base(TARGET_HEAP),
                        ProgramType::UInt8Pointer,
                    );
                    (
                        ProgramType::UInt8Pointer,
                        value.clone(),
                        value.clone(),
                        ProgramExpression::Value(value),
                    )
                } else {
                    (
                        ProgramType::Int32,
                        int32(0),
                        int32(9),
                        crate::kernel::program_expression::int32_literal(9),
                    )
                };
                let mut state = if address_backed {
                    declare(&ExecutionState::new(), "target", c_type)
                } else {
                    ExecutionState::new().with_local("target", initial)
                };
                for index in 0..size {
                    state = declare(&state, &format!("beside_{index}"), ProgramType::Int32);
                }
                let resources = state.resources().clone();
                let (paths, work) = crate::instrumentation::measure_deterministic_work(|| {
                    execute_execution_statement_paths(
                        &state,
                        &program_assign("target", expression.clone()),
                        &PureFactContext::new(),
                        ExecutionContext::execute_bodies(&ExecutionEnvironment::new()),
                        &mut ExecutionBudget::default(),
                    )
                    .expect("the scalar assignment executes")
                });
                assert_eq!(paths.len(), 1);
                let StatementOutcome::Normal(next) = &paths[0].outcome else {
                    panic!("assignment did not have a normal outcome");
                };
                assert_eq!(next.locals().get_native("target").as_deref(), Some(&value));
                assert_eq!(next.resources(), &resources, "ownership must be retained");
                assert_eq!(next.locals().get_native("beside_0").as_deref(), None);
                samples.push((size, work));
            }
            assert_constant_plus_log_growth(
                "private local copy beside automatic storage",
                &samples,
                64.0,
            );
        }
    }
}

#[test]
fn private_owner_projection_does_not_republish_discarded_pairings() {
    let mut samples = Vec::new();
    for size in [16, 32, 64, 128] {
        let _session = crate::kernel::VerificationSession::enter();
        crate::kernel::set_never_address_taken_locals(
            (0..size).map(|index| format!("hidden_{index}")).collect(),
        );
        let mut assumptions = PureFactContext::new();
        for index in 0..size {
            assumptions = assumptions.assume_condition(
                ConditionTerm::equal(
                    MachineTerm::Variable(Variable(93_800 + index as u64)),
                    MachineTerm::constant(index as u32),
                ),
                true,
            );
        }
        let base = ResourceContext::new()
            .unchecked_with_fact(ResourceFact::own_memory(MemoryRange::new(
                heap_base(1),
                0u32.into(),
                1u32.into(),
            )))
            .unchecked_with_fact(ResourceFact::own_memory(MemoryRange::new(
                heap_base(2),
                0u32.into(),
                1u32.into(),
            )));
        let expected = base.observable_facts_assuming_valid(&assumptions);
        let mut resources = base;
        for index in 0..size {
            resources = resources.unchecked_with_fact(ResourceFact::own_memory(MemoryRange::new(
                Memory::local_pointer(&format!("hidden_{index}")),
                0u32.into(),
                1u32.into(),
            )));
        }
        resources.synchronize_memory_equalities(&assumptions);
        let (observed, work) = crate::instrumentation::measure_deterministic_work(|| {
            resources.observable_facts_assuming_valid(&assumptions)
        });
        assert_eq!(observed, expected);
        assert_eq!(
            resources.facts().len(),
            size + 2,
            "projection must retain source authority"
        );
        samples.push((size, work));
    }
    // The retained projection never republishes discarded private pairings;
    // source insertions already advanced its private-owner deltas.
    assert_at_most_linear_growth("private owner projection", &samples, 8);
}

#[test]
fn validity_is_logarithmic_in_unrelated_allocations() {
    let mut samples = Vec::new();
    for size in [4usize, 16, 64, 256] {
        let frame = frame_with_unrelated_allocations(size);
        let assumptions = assumptions_aliasing_the_target();
        let (error, work) = crate::instrumentation::measure_deterministic_work(|| {
            frame.validity_error(&assumptions)
        });
        assert_eq!(error, None, "the frame is a partition");
        samples.push((size, work));
    }
    assert_constant_plus_log_growth("validity of a frame", &samples, 4.0);
}

#[test]
fn ensured_resource_composition_is_logarithmic_in_unrelated_allocations() {
    let mut samples = Vec::new();
    for size in [4usize, 16, 64, 256] {
        let frame = frame_with_unrelated_allocations(size);
        let assumptions = assumptions_aliasing_the_target();
        let ensured = owned_range(heap_base(TARGET_HEAP), 8, 12);
        let (composed, work) = crate::instrumentation::measure_deterministic_work(|| {
            frame
                .clone()
                .try_compose_with_facts_delaying_normalization_with_occurrences(
                    [ensured.clone()],
                    &assumptions,
                )
        });
        let (composed, inserted) = composed.expect("the ensured range is disjoint");
        assert_eq!(inserted.len(), 1);
        assert!(composed.contains_exact_representation(&ensured));
        samples.push((size, work));
    }
    assert_constant_plus_log_growth("composing one ensured range", &samples, 4.0);
}

/// The cross-block walk is driven from the smaller of the context's bases and
/// the equalities, so many unrelated equalities beside a small frame cost as
/// little as many unrelated allocations beside a few equalities.
#[test]
fn validity_is_logarithmic_in_unrelated_pointer_equalities() {
    let mut samples = Vec::new();
    for size in [4usize, 16, 64, 256] {
        let frame = frame_with_unrelated_allocations(2);
        let assumptions = (0..size).fold(assumptions_aliasing_the_target(), |facts, index| {
            facts.assume_condition(
                pointer_equal(
                    symbolic_base(3 * TARGET_HEAP + 2 * index as u64),
                    symbolic_base(3 * TARGET_HEAP + 2 * index as u64 + 1),
                ),
                true,
            )
        });
        let (error, work) = crate::instrumentation::measure_deterministic_work(|| {
            frame.validity_error(&assumptions)
        });
        assert_eq!(error, None, "the frame is a partition");
        samples.push((size, work));
    }
    assert_constant_plus_log_growth("validity beside unrelated equalities", &samples, 4.0);
}

/// Skipping blocks and bases that hold no pair must not skip a violation:
/// each kind is still found beside many unrelated resources, from either
/// side of the alias walk, and reports the same pair.
#[test]
fn indexed_validity_still_finds_every_violation_kind() {
    for size in [0, 3, 64] {
        let frame = frame_with_unrelated_allocations(size);
        let none = PureFactContext::new();

        let overlapping =
            frame
                .clone()
                .unchecked_with_fact(owned_range(heap_base(TARGET_HEAP), 2, 6));
        assert!(
            matches!(
                overlapping.validity_error(&none),
                Some(ResourceContextValidityError::OverlappingOwnedMemoryResources { .. })
            ),
            "a same-block overlap beside {size} allocations"
        );

        let duplicate = frame
            .clone()
            .unchecked_with_fact(owned_instance(TARGET_HEAP + 1));
        let expected_duplicate = if size == 0 {
            None
        } else {
            Some(ResourceContextValidityError::DuplicateOwnedResourceFact(
                owned_instance(TARGET_HEAP + 1),
            ))
        };
        assert_eq!(
            duplicate.validity_error(&none),
            expected_duplicate,
            "a duplicate instance beside {size} allocations"
        );

        let invalid_access = ResourceFact::View(owned_instance(2 * TARGET_HEAP).resource().clone());
        assert_eq!(
            frame
                .clone()
                .unchecked_with_fact(invalid_access.clone())
                .validity_error(&none),
            Some(ResourceContextValidityError::InvalidExclusiveAccess(
                invalid_access
            )),
            "an instance view beside {size} allocations"
        );

        // A second block owning the target's first range, joined to it by an
        // exact equality: once with fewer equalities than bases, once with
        // more, so both drivers of the alias walk find the pair.
        let other = heap_base(3 * TARGET_HEAP);
        let aliased = frame
            .clone()
            .unchecked_with_fact(owned_range(other.clone(), 0, 4));
        let joined = PureFactContext::new()
            .assume_condition(pointer_equal(heap_base(TARGET_HEAP), other.clone()), true);
        let crowded = (0..2 * size + 8).fold(joined.clone(), |facts, index| {
            facts.assume_condition(
                pointer_equal(
                    symbolic_base(4 * TARGET_HEAP + 2 * index as u64),
                    symbolic_base(4 * TARGET_HEAP + 2 * index as u64 + 1),
                ),
                true,
            )
        });
        for assumptions in [&joined, &crowded] {
            assert!(
                matches!(
                    aliased.validity_error(assumptions),
                    Some(ResourceContextValidityError::OverlappingOwnedMemoryResources { .. })
                ),
                "an aliased cross-block overlap beside {size} allocations"
            );
        }
        assert_eq!(aliased.validity_error(&none), None);
    }
}

/// A field-bearing `suffix(p)` whose owned range starts at its own `start`
/// field, and a parent `holder(p)` whose field `at` sets that child's
/// `start` and whose child is passed `p`: the body shapes of a plain-field
/// endpoint and a field-to-field child equation.
fn field_endpoint_definitions() -> Vec<CompositeResourceDefinition> {
    let suffix_schema = ResourceFieldSchema::new(vec![(
        "start".into(),
        ResourceFieldType::Program(ProgramType::Int32),
    )])
    .unwrap();
    let holder_schema = ResourceFieldSchema::new(vec![(
        "at".into(),
        ResourceFieldType::Program(ProgramType::Int32),
    )])
    .unwrap();
    let suffix = CompositeResourceDefinition::new(
        "suffix",
        vec![program_parameter("p", ProgramType::Int32Pointer)],
        None,
        false,
        vec![ResourceSpec::owned_memory(MemorySegment {
            uninitialized: false,
            value_runs: Default::default(),
            base: crate::kernel::program_expression::variable("p"),
            start: crate::kernel::program_expression::variable("start"),
            end: crate::kernel::program_expression::int32_literal(8),
            element_width: 4,
            guard: None,
        })],
        vec![],
    )
    .with_instance_schema(Some(suffix_schema));
    let holder = CompositeResourceDefinition::new(
        "holder",
        vec![program_parameter("p", ProgramType::Int32Pointer)],
        None,
        false,
        vec![],
        vec![],
    )
    .with_children(vec![ResourceChildSpec {
        name: "rest".into(),
        resource: "suffix".into(),
        binding: Variable(90),
        arguments: vec![SpecExpression::ProgramExpression(
            crate::kernel::program_expression::variable("p"),
        )],
        field_bindings: vec![ResourceChildField::Parent(0)],
    }])
    .with_instance_schema(Some(holder_schema));
    // Definitions are looked up by binary search on their names.
    vec![holder, suffix]
}

fn field_endpoint_instance(name: &str, field: &str, identity: u64) -> ResourceInstance {
    ResourceInstance::new(
        Variable(identity),
        name.into(),
        vec![ProgramValue::pointer(heap_base(TARGET_HEAP)).into()].into(),
        ResourceFieldSchema::new(vec![(
            field.into(),
            ResourceFieldType::Program(ProgramType::Int32),
        )])
        .unwrap(),
        vec![int32(2).into()].into(),
    )
    .unwrap()
}

#[test]
fn field_endpoint_fold_and_unfold_ignore_unrelated_resources() {
    let definitions = field_endpoint_definitions();
    let (holder, suffix) = (&definitions[0], &definitions[1]);
    let mut samples = Vec::new();
    for size in [4usize, 16, 64, 256] {
        let parent = field_endpoint_instance("holder", "at", 2 * TARGET_HEAP);
        let child = field_endpoint_instance("suffix", "start", 2 * TARGET_HEAP + 1);
        let frame = ResourceContext::new()
            .unchecked_with_facts((0..size).flat_map(|index| {
                [
                    owned_range(heap_base(index as u64 + 1), 0, 4),
                    owned_instance(TARGET_HEAP + 1 + index as u64),
                ]
            }))
            .unchecked_with_facts([ResourceFact::own(Resource::Instance(parent.clone()))]);
        let state = ExecutionState::new().with_resource_context(frame);
        let assumptions = PureFactContext::new();
        let children = vec![("rest".to_string(), child.identity)];
        let (round_trip, work) = crate::instrumentation::measure_deterministic_work(|| {
            let rewrite = |state: &ExecutionState,
                           instance: &ResourceInstance,
                           definition: &CompositeResourceDefinition,
                           unfold: bool,
                           children: Option<&[(String, Variable)]>| {
                crate::kernel::rewrite_resource_instance_selecting_children(
                    state,
                    instance,
                    definition,
                    &definitions,
                    &assumptions,
                    unfold,
                    children,
                )
                .map(|rewrite| rewrite.state)
            };
            let open = rewrite(&state, &parent, holder, true, Some(&children))?;
            let cells = rewrite(&open, &child, suffix, true, None)?;
            let child_again = rewrite(&cells, &child, suffix, false, None)?;
            rewrite(&child_again, &parent, holder, false, Some(&children))
        });
        let closed = round_trip.unwrap_or_else(|refusal| {
            panic!(
                "the field-endpoint round trip should succeed: {}",
                refusal.describe()
            )
        });
        assert_eq!(
            closed.resources.owned_instance(parent.identity),
            Some(&parent)
        );
        samples.push((size, work));
    }
    assert_constant_plus_log_growth("field-endpoint fold and unfold", &samples, 16.0);
}

/// A field-bearing `window(p)` whose unconditional, unmatched body owns
/// `cells` one-element ranges of `p`, the first starting at its own `start`
/// field: the body shape whose cells a folded instance publishes as read
/// authority to its sibling contract clauses.
fn window_definitions(cells: u32) -> Vec<CompositeResourceDefinition> {
    let schema = ResourceFieldSchema::new(vec![(
        "start".into(),
        ResourceFieldType::Program(ProgramType::Int32),
    )])
    .unwrap();
    let contains = (0..cells)
        .map(|cell| {
            ResourceSpec::owned_memory(MemorySegment {
                uninitialized: false,
                value_runs: Default::default(),
                base: crate::kernel::program_expression::variable("p"),
                start: if cell == 0 {
                    crate::kernel::program_expression::variable("start")
                } else {
                    crate::kernel::program_expression::int32_literal(cell)
                },
                end: crate::kernel::program_expression::int32_literal(cell + 1),
                element_width: 4,
                guard: None,
            })
        })
        .collect();
    vec![
        CompositeResourceDefinition::new(
            "window",
            vec![program_parameter("p", ProgramType::Int32Pointer)],
            None,
            false,
            contains,
            vec![],
        )
        .with_instance_schema(Some(schema)),
    ]
}

fn window_instance(block: u64, identity: u64) -> ResourceFact {
    ResourceFact::own(Resource::Instance(
        ResourceInstance::new(
            Variable(identity),
            "window".into(),
            vec![ProgramValue::pointer(heap_base(block)).into()].into(),
            ResourceFieldSchema::new(vec![(
                "start".into(),
                ResourceFieldType::Program(ProgramType::Int32),
            )])
            .unwrap(),
            vec![int32(0).into()].into(),
        )
        .unwrap(),
    ))
}

/// The views a section's own folded field-bearing instance publishes cost
/// that instance's body: the frame the section is evaluated against may hold
/// any number of unrelated instances of the same family, each with a body
/// of its own, and none of them is evaluated.
#[test]
fn unmatched_instance_body_views_ignore_unrelated_instances() {
    let definitions = window_definitions(4);
    let mut samples = Vec::new();
    for size in [4usize, 16, 64, 256] {
        let frame = ResourceContext::new().unchecked_with_facts((0..size).flat_map(|index| {
            [
                owned_range(heap_base(index as u64 + 1), 0, 4),
                window_instance(index as u64 + 1, TARGET_HEAP + 1 + index as u64),
            ]
        }));
        let state = ExecutionState::new().with_resource_context(frame);
        let target = window_instance(TARGET_HEAP, 2 * TARGET_HEAP);
        let assumptions = PureFactContext::new();
        let (supply, work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::kernel::functions::resource_clause_section_supply(
                &state,
                std::slice::from_ref(&target),
                &definitions,
                &assumptions,
            )
        });
        let published = supply
            .facts()
            .iter()
            .filter(|fact| {
                matches!(fact, ResourceFact::View(Resource::Memory(range))
                    if range.base().block == PointerBlock::Heap(TARGET_HEAP))
            })
            .count();
        assert_eq!(published, 4, "the target body's four cells are published");
        samples.push((size, work));
    }
    assert_constant_plus_log_growth("unmatched instance body views", &samples, 4.0);
}

/// The same publication grows with the instance's own body: one evaluation
/// of each owned clause, and nothing more.
#[test]
#[ignore = "nightly: 0.5s in the parallel gate"]
fn unmatched_instance_body_views_are_linear_in_the_body() {
    // Smaller than `SIZES`: the charged work is linear in the body, but the
    // wall time of publishing a body of 1024 owned cells is tens of seconds
    // in a debug build, which points at uncharged superlinear work somewhere
    // below this call (resource normalization of many same-block ranges is
    // the suspect) and would make this test time out under gate load. The
    // linearity claim is the same at these sizes.
    const BODY_SIZES: [usize; 4] = [4, 16, 64, 256];
    let mut samples = Vec::new();
    for size in BODY_SIZES {
        let definitions = window_definitions(size as u32);
        let state = ExecutionState::new();
        let target = window_instance(TARGET_HEAP, 2 * TARGET_HEAP);
        let assumptions = PureFactContext::new();
        let (supply, work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::kernel::functions::resource_clause_section_supply(
                &state,
                std::slice::from_ref(&target),
                &definitions,
                &assumptions,
            )
        });
        let published = supply
            .facts()
            .iter()
            .filter(|fact| matches!(fact, ResourceFact::View(Resource::Memory(_))))
            .count();
        assert_eq!(published, size, "every owned cell of the body is published");
        samples.push((size, work));
    }
    eprintln!("unmatched instance body views by body size (N, units): {samples:?}");
    let (smallest, base_work) = samples[0];
    let per_clause = base_work as f64 / smallest as f64;
    for (size, work) in &samples {
        let allowed = 2.0 * per_clause * *size as f64 + 8.0;
        assert!(
            (*work as f64) <= allowed,
            "a {size}-clause body charged {work} units, above {allowed:.1} (linear in the \
             body): {samples:?}"
        );
    }
}

/// A field-bearing `holder(p)` whose unconditional, unmatched body owns one
/// field-free composite child, `cells(p)`, which in turn owns `cells`
/// one-element ranges of `p`: the shape of `arena_state` owning
/// `arena_cells`, where the published cells sit one composite below the
/// instance's body.
fn holder_definitions(cells: u32) -> Vec<CompositeResourceDefinition> {
    let schema = ResourceFieldSchema::new(vec![(
        "start".into(),
        ResourceFieldType::Program(ProgramType::Int32),
    )])
    .unwrap();
    let child_contains = (0..cells)
        .map(|cell| {
            ResourceSpec::owned_memory(MemorySegment {
                uninitialized: false,
                value_runs: Default::default(),
                base: crate::kernel::program_expression::variable("p"),
                start: crate::kernel::program_expression::int32_literal(cell),
                end: crate::kernel::program_expression::int32_literal(cell + 1),
                element_width: 4,
                guard: None,
            })
        })
        .collect();
    vec![
        CompositeResourceDefinition::new(
            "cells",
            vec![program_parameter("p", ProgramType::Int32Pointer)],
            None,
            false,
            child_contains,
            vec![],
        ),
        CompositeResourceDefinition::new(
            "holder",
            vec![program_parameter("p", ProgramType::Int32Pointer)],
            None,
            false,
            vec![ResourceSpec::composite(
                ResourceAccessMode::Own,
                "cells".into(),
                vec![crate::kernel::program_expression::variable("p")],
                vec![ProgramType::Int32Pointer],
            )],
            vec![],
        )
        .with_instance_schema(Some(schema)),
    ]
}

fn holder_instance(block: u64, identity: u64) -> ResourceFact {
    ResourceFact::own(Resource::Instance(
        ResourceInstance::new(
            Variable(identity),
            "holder".into(),
            vec![ProgramValue::pointer(heap_base(block)).into()].into(),
            ResourceFieldSchema::new(vec![(
                "start".into(),
                ResourceFieldType::Program(ProgramType::Int32),
            )])
            .unwrap(),
            vec![int32(0).into()].into(),
        )
        .unwrap(),
    ))
}

/// A folded field-bearing instance publishes the cells its body's field-free
/// composite children own, and that costs the instance's own body: the
/// frame may hold any number of unrelated holders, none of them expanded.
#[test]
fn nested_composite_body_views_ignore_unrelated_instances() {
    let definitions = holder_definitions(4);
    let mut samples = Vec::new();
    for size in [4usize, 16, 64, 256] {
        let frame = ResourceContext::new().unchecked_with_facts((0..size).flat_map(|index| {
            [
                owned_range(heap_base(index as u64 + 1), 0, 4),
                holder_instance(index as u64 + 1, TARGET_HEAP + 1 + index as u64),
            ]
        }));
        let state = ExecutionState::new().with_resource_context(frame);
        let target = holder_instance(TARGET_HEAP, 2 * TARGET_HEAP);
        let assumptions = PureFactContext::new();
        let (supply, work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::kernel::functions::resource_clause_section_supply(
                &state,
                std::slice::from_ref(&target),
                &definitions,
                &assumptions,
            )
        });
        let published = supply
            .facts()
            .iter()
            .filter(|fact| {
                matches!(fact, ResourceFact::View(Resource::Memory(range))
                    if range.base().block == PointerBlock::Heap(TARGET_HEAP))
            })
            .count();
        assert!(
            published >= 1,
            "the target's nested cells are published: {:?}",
            supply.facts()
        );
        samples.push((size, work));
    }
    assert_constant_plus_log_growth("nested composite body views", &samples, 4.0);
}

/// The same publication grows with the child's body: one expansion of the
/// owned composite, and nothing more.
#[test]
#[ignore = "nightly: 1.7s in the parallel gate"]
fn nested_composite_body_views_are_linear_in_the_child_body() {
    let mut samples = Vec::new();
    for size in SIZES {
        let definitions = holder_definitions(size as u32);
        let state = ExecutionState::new();
        let target = holder_instance(TARGET_HEAP, 2 * TARGET_HEAP);
        let assumptions = PureFactContext::new();
        let (supply, work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::kernel::functions::resource_clause_section_supply(
                &state,
                std::slice::from_ref(&target),
                &definitions,
                &assumptions,
            )
        });
        let published = supply
            .facts()
            .iter()
            .filter(|fact| matches!(fact, ResourceFact::View(Resource::Memory(_))))
            .count();
        assert!(published >= 1, "the child's cells are published");
        samples.push((size, work));
    }
    eprintln!("nested composite body views by child size (N, units): {samples:?}");
    let (smallest, base_work) = samples[0];
    let per_clause = base_work as f64 / smallest as f64;
    for (size, work) in &samples {
        let allowed = 2.0 * per_clause * *size as f64 + 8.0;
        assert!(
            (*work as f64) <= allowed,
            "a {size}-cell child charged {work} units, above {allowed:.1} (linear in the \
             child): {samples:?}"
        );
    }
}

/// Whether a loop head keeps a cell because the function keeps owning it is
/// one lookup of the cell's base in the kept context's base index: the
/// unrelated ranges the function also keeps add no work.
#[test]
fn a_kept_cell_is_placed_without_visiting_unrelated_ranges() {
    // Objects reached through parameters share one block and differ by a
    // symbolic base, as the arena's descriptors do.
    let object = |identity: u64| Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(identity)), 4),
    };
    let field = |identity: u64, bytes: i64| Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Add(
            Box::new(object(identity).offset),
            Box::new(PointerOffsetTerm::Constant(bytes)),
        ),
    };
    let mut samples = Vec::new();
    for size in [4usize, 16, 64, 256] {
        let kept = ResourceContext::new().unchecked_with_facts(
            (0..size)
                .map(|index| owned_range(object(index as u64 + 1), 0, 16))
                .chain([owned_range(object(TARGET_HEAP), 0, 16)]),
        );
        let assumptions = PureFactContext::new();
        let (held, work) = crate::instrumentation::measure_deterministic_work(|| {
            assumptions.access_held_by_owned_member(&kept, &field(TARGET_HEAP, 8), 4)
        });
        assert!(held, "the kept range holds the cell");
        let (outside, _) = crate::instrumentation::measure_deterministic_work(|| {
            assumptions.access_held_by_owned_member(&kept, &field(TARGET_HEAP, 64), 4)
        });
        assert!(!outside, "a cell past the kept range is not held");
        samples.push((size, work));
    }
    assert_constant_plus_log_growth("kept cell placement", &samples, 4.0);
}

fn variable_range(base: Pointer, start: MachineTerm, end: MachineTerm) -> ResourceFact {
    ResourceFact::own_memory(MemoryRange::new(base, start, end))
}

fn int32_equal(left: u64, right: u64) -> ConditionTerm {
    ConditionTerm::Compare {
        format: MachineIntegerType::Int32,
        relation: CompareRelation::Equal,
        left: Box::new(MachineTerm::Variable(Variable(left))),
        right: Box::new(MachineTerm::Variable(Variable(right))),
    }
}

/// Two held ranges that abut only by a proved endpoint equality merge in
/// normalization, and finding the partner costs the endpoint's equality
/// class: unrelated equalities among other values add no work.
#[test]
fn joining_ranges_by_a_proved_endpoint_ignores_unrelated_equalities() {
    let (end, start) = (3 * TARGET_HEAP, 3 * TARGET_HEAP + 1);
    let mut samples = Vec::new();
    for size in [4usize, 16, 64, 256] {
        let frame = ResourceContext::new().unchecked_with_facts([
            variable_range(
                heap_base(TARGET_HEAP),
                MachineTerm::constant(0),
                MachineTerm::Variable(Variable(end)),
            ),
            variable_range(
                heap_base(TARGET_HEAP),
                MachineTerm::Variable(Variable(start)),
                MachineTerm::constant(16),
            ),
        ]);
        let assumptions = (0..size as u64).fold(
            PureFactContext::new().assume_condition(int32_equal(end, start), true),
            |facts, index| {
                facts.assume_condition(
                    int32_equal(4 * TARGET_HEAP + 2 * index, 4 * TARGET_HEAP + 2 * index + 1),
                    true,
                )
            },
        );
        // The premise set's lazy indexes (the equality graph and the ones
        // any normalization consults) are built once per premise set and
        // shared by every later query. Warm them on an unrelated merge of
        // identically spelled endpoints so the measurement below is the
        // join alone.
        let warm = ResourceContext::new().unchecked_with_facts([
            variable_range(
                heap_base(TARGET_HEAP + 1),
                MachineTerm::constant(0),
                MachineTerm::Variable(Variable(end)),
            ),
            variable_range(
                heap_base(TARGET_HEAP + 1),
                MachineTerm::Variable(Variable(end)),
                MachineTerm::constant(16),
            ),
        ]);
        assert_eq!(warm.normalized(&assumptions).facts().len(), 1);
        assert!(assumptions.int32_values_known_equal(
            &MachineTerm::Variable(Variable(end)),
            &MachineTerm::Variable(Variable(start)),
        ));
        let (normalized, work) = crate::instrumentation::measure_deterministic_work(|| {
            frame.clone().normalized(&assumptions)
        });
        assert_eq!(
            normalized.facts(),
            &[variable_range(
                heap_base(TARGET_HEAP),
                MachineTerm::constant(0),
                MachineTerm::constant(16),
            )],
            "the two ranges join into one"
        );
        samples.push((size, work));
    }
    assert_constant_plus_log_growth("joining by a proved endpoint", &samples, 4.0);
}

/// A call that retires an allocation asks which resource the caller keeps
/// could still refer to it. Only the kept facts that can name the retired
/// block are candidates, and they come from the context's indexes, so kept
/// ranges and instances elsewhere add no work: the answer costs the block's
/// own candidates.
#[test]
fn retirement_stale_check_ignores_unrelated_kept_resources() {
    let allocation = heap_base(TARGET_HEAP);
    let bytes = MachineTerm::constant(16);
    let mut samples = Vec::new();
    for size in [4usize, 16, 64, 256] {
        let unrelated = (0..size).flat_map(|index| {
            [
                owned_range(heap_base(index as u64 + 1), 0, 4),
                owned_instance(TARGET_HEAP + 1 + index as u64),
            ]
        });
        let kept = ResourceContext::new()
            .unchecked_with_facts(unrelated.clone())
            .unchecked_with_fact(owned_range(allocation.clone(), 4, 8));
        let assumptions = PureFactContext::new();
        let (stale, work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::kernel::functions::caller_resource_left_stale_by_retirement(
                &ResourceContext::new(),
                &kept,
                &allocation,
                &HeapExtent::int32(bytes.clone()),
                &assumptions,
            )
            .cloned()
        });
        assert_eq!(
            stale, None,
            "a kept range past the allocation's end is separate from it"
        );
        samples.push((size, work));

        // The same frame keeping a range inside the allocation is refused,
        // so the measurement above is of a check that can say no.
        let overlapping = ResourceContext::new()
            .unchecked_with_facts(unrelated)
            .unchecked_with_fact(owned_range(allocation.clone(), 2, 3));
        assert_eq!(
            crate::kernel::functions::caller_resource_left_stale_by_retirement(
                &ResourceContext::new(),
                &overlapping,
                &allocation,
                &HeapExtent::int32(bytes.clone()),
                &assumptions,
            ),
            Some(&owned_range(allocation.clone(), 2, 3)),
        );
    }
    assert_constant_plus_log_growth("retirement stale check", &samples, 4.0);
}

/// A pointer parameter: every one lives in the single `ExternalArgument`
/// block, at four times its own index variable.
fn parameter_base(identity: u64) -> Pointer {
    Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(identity)), 4),
    }
}

fn parameter_object(identity: u64) -> ResourceFact {
    ResourceFact::own_memory(MemoryRange::new_with_element_width(
        parameter_base(identity),
        MachineTerm::constant(0),
        MachineTerm::constant(3),
        4,
    ))
}

const FIRST_PARAMETER: u64 = 98_000;

/// A frame owning `count` three-field objects of distinct pointer
/// parameters and one folded composite, and the fact context a call sees
/// it through: the frame is a held composition. This is the shape of
/// `examples/arena`'s pipeline, whose four parameters, their regions, and
/// the objects the callees return all share one block.
fn parameter_frame(count: usize) -> (ResourceContext, PureFactContext) {
    let frame = ResourceContext::new()
        .unchecked_with_facts(
            (0..count as u64).map(|index| parameter_object(FIRST_PARAMETER + index)),
        )
        .unchecked_with_fact(ResourceFact::own_composite(
            "holder".into(),
            vec![ProgramValue::pointer(parameter_base(FIRST_PARAMETER - 1))],
        ));
    let assumptions =
        PureFactContext::new().assume_proposition(Proposition::ResourceComposition(frame.clone()));
    (frame, assumptions)
}

const PARAMETER_SIZES: [usize; 4] = [8, 16, 32, 64];

fn assert_at_most_linear_growth(what: &str, samples: &[(usize, usize)], per_item: usize) {
    eprintln!("{what} (N, units): {samples:?}");
    for (size, work) in samples {
        assert!(
            *work <= per_item * size + 64,
            "{what}: {size} owned parameter objects charged {work} units, above \
             {per_item}·N + 64: {samples:?}"
        );
    }
    for pair in samples.windows(2) {
        let [(small, small_work), (large, large_work)] = pair else {
            unreachable!()
        };
        let ratio = *large_work as f64 / (*small_work).max(1) as f64;
        assert!(
            ratio <= 2.5,
            "{what}: work grew by {ratio:.2} from {small} to {large} owned parameter \
             objects, above linear: {samples:?}"
        );
    }
}

/// Composing one more parameter object into the frame compares it only
/// with owned ranges a fact could relate it to: its own root, the roots of
/// its aliases, and the members of its index term's equality class. The
/// other parameters' objects are structurally distinct symbolic bases no
/// fact relates, so an overlap with them cannot be proved and is not asked
/// (validity refuses a proven overlap). Each pair used to be compared, and
/// each comparison searched the composition's projected pairs: cubic.
#[test]
fn composing_a_parameter_object_ignores_unrelated_parameters() {
    let mut samples = Vec::new();
    for size in PARAMETER_SIZES {
        let _session = crate::kernel::VerificationSession::enter();
        let (frame, assumptions) = parameter_frame(size);
        let added = parameter_object(FIRST_PARAMETER + size as u64);
        let (composed, work) = crate::instrumentation::measure_deterministic_work(|| {
            frame
                .clone()
                .try_compose_into_valid_context_delaying_normalization(
                    [added.clone()],
                    &assumptions,
                )
        });
        assert!(composed.is_ok(), "a new parameter's object is disjoint");
        samples.push((size, work));
    }
    assert_constant_plus_log_growth("composing one parameter object", &samples, 8.0);
}

/// The whole-frame validity check is linear: each owned range asks its own
/// keys once.
#[test]
fn validity_of_parameter_objects_is_linear() {
    let mut samples = Vec::new();
    for size in PARAMETER_SIZES {
        let _session = crate::kernel::VerificationSession::enter();
        let (frame, assumptions) = parameter_frame(size);
        let (error, work) = crate::instrumentation::measure_deterministic_work(|| {
            frame.validity_error(&assumptions)
        });
        assert_eq!(error, None, "the frame is a partition");
        samples.push((size, work));
    }
    assert_at_most_linear_growth("validity of a parameter frame", &samples, 16);
}

/// Pruning to related roots must still refuse every overlap a fact proves:
/// the same object twice, a shifted spelling of one object, an object at a
/// parameter an index equality or an exact pointer equality identifies with
/// another, beside many unrelated parameters.
#[test]
fn parameter_validity_still_refuses_related_overlaps() {
    let size = 32;
    let (frame, _) = parameter_frame(size);
    let target = FIRST_PARAMETER + 5;
    let overlaps = |extra: &ResourceFact, assumptions: &PureFactContext| {
        let whole = matches!(
            frame
                .clone()
                .unchecked_with_fact(extra.clone())
                .validity_error(assumptions),
            Some(ResourceContextValidityError::OverlappingOwnedMemoryResources { .. })
        );
        let incremental = matches!(
            frame
                .clone()
                .try_compose_into_valid_context_delaying_normalization(
                    [extra.clone()],
                    assumptions
                ),
            Err(ResourceContextValidityError::OverlappingOwnedMemoryResources { .. })
        );
        assert_eq!(whole, incremental, "both checks decide {extra:?} alike");
        whole
    };
    let none = PureFactContext::new();

    assert!(
        overlaps(&parameter_object(target), &none),
        "the same object owned twice"
    );

    let field = ResourceFact::own_memory(MemoryRange::new_with_element_width(
        parameter_base(target).offset_by_elements(MachineTerm::constant(2), 4),
        MachineTerm::constant(0),
        MachineTerm::constant(1),
        4,
    ));
    assert!(overlaps(&field, &none), "a field of an owned object");

    let other = 2 * FIRST_PARAMETER;
    let aliased = parameter_object(other);
    assert!(!overlaps(&aliased, &none), "an unrelated parameter");
    // Both index terms pinned to one constant: the equality class relates
    // the two roots, and the endpoints then decide the overlap.
    let pinned = PureFactContext::new()
        .assume_condition(
            ConditionTerm::equal(
                MachineTerm::Variable(Variable(other)),
                MachineTerm::constant(7),
            ),
            true,
        )
        .assume_condition(
            ConditionTerm::equal(
                MachineTerm::Variable(Variable(target)),
                MachineTerm::constant(7),
            ),
            true,
        );
    assert!(
        overlaps(&aliased, &pinned),
        "a parameter pinned to the address of an owned one"
    );
    let equal_pointer = PureFactContext::new().assume_condition(
        ConditionTerm::pointer_equal(parameter_base(other), parameter_base(target)),
        true,
    );
    assert!(
        overlaps(&aliased, &equal_pointer),
        "a parameter an exact pointer equality identifies with an owned one"
    );
}

/// Holding a composition no longer states its pairwise separations into the
/// fact context: `N` owned ranges of one block used to project `N(N-1)/2`
/// candidate pairs at insertion.
#[test]
fn holding_a_parameter_composition_states_no_pairs() {
    let mut samples = Vec::new();
    for size in PARAMETER_SIZES {
        let (frame, _) = parameter_frame(size);
        let (assumptions, work) = crate::instrumentation::measure_deterministic_work(|| {
            PureFactContext::new()
                .assume_proposition(Proposition::ResourceComposition(frame.clone()))
        });
        assert_eq!(
            assumptions.memory_separation_candidate_count(
                &PointerBlock::ExternalArgument,
                &PointerBlock::ExternalArgument
            ),
            0
        );
        samples.push((size, work));
    }
    assert_constant_plus_log_growth("holding a parameter composition", &samples, 4.0);
}

/// Asking whether fields of two owned parameter objects are disjoint reads
/// the composition's members of that block once each, not their pairs. The
/// failing query (a pointer no member holds) is the one every ladder that
/// tries this rung and moves on pays.
#[test]
fn one_parameter_separation_query_is_linear_in_the_owned_objects() {
    let mut proved = Vec::new();
    let mut refused = Vec::new();
    for size in PARAMETER_SIZES {
        let _session = crate::kernel::VerificationSession::enter();
        let (_, assumptions) = parameter_frame(size);
        let field = |identity: u64| {
            parameter_base(identity).offset_by_elements(MachineTerm::constant(1), 4)
        };
        let (left, right) = (
            field(FIRST_PARAMETER + size as u64 - 2),
            field(FIRST_PARAMETER + size as u64 - 1),
        );
        let (separate, work) = crate::instrumentation::measure_deterministic_work(|| {
            assumptions
                .pointers_proven_disjoint_by_explicit_range_for_memory_resolution(&left, &right)
        });
        assert!(separate, "two owned members hold the two fields");
        proved.push((size, work));
        let outside = field(3 * FIRST_PARAMETER);
        let (separate, work) = crate::instrumentation::measure_deterministic_work(|| {
            assumptions
                .pointers_proven_disjoint_by_explicit_range_for_memory_resolution(&left, &outside)
        });
        assert!(!separate, "no member holds the second pointer");
        refused.push((size, work));
    }
    assert_at_most_linear_growth("a proved parameter separation", &proved, 64);
    assert_at_most_linear_growth("a refused parameter separation", &refused, 64);
}

/// A separation the composition law proves costs the same work however many
/// other parameter objects share the block: the members filed under the two
/// sides' roots are asked first, and they hold the pair. This is the query a
/// verified call's separation requirement asks (`proves_resource_separate`),
/// in both the pointer and the range form. A query no pair satisfies is
/// still refused, by asking the whole block.
#[test]
fn a_proved_parameter_separation_reads_only_the_nominated_members() {
    let mut pointer_work = Vec::new();
    let mut range_work = Vec::new();
    for size in PARAMETER_SIZES {
        let _session = crate::kernel::VerificationSession::enter();
        let (_, assumptions) = parameter_frame(size);
        let field = |identity: u64| {
            parameter_base(identity).offset_by_elements(MachineTerm::constant(1), 4)
        };
        let range = |identity: u64| {
            Resource::Memory(MemoryRange::new_with_element_width(
                parameter_base(identity),
                MachineTerm::constant(1),
                MachineTerm::constant(2),
                4,
            ))
        };
        let (left, right) = (
            FIRST_PARAMETER + size as u64 - 2,
            FIRST_PARAMETER + size as u64 - 1,
        );
        let (separate, work) = crate::instrumentation::measure_deterministic_work(|| {
            assumptions.pointers_proven_disjoint_by_explicit_range_for_memory_resolution(
                &field(left),
                &field(right),
            )
        });
        assert!(separate, "two owned members hold the two fields");
        pointer_work.push(work);
        let (separate, work) = crate::instrumentation::measure_deterministic_work(|| {
            assumptions.proves_resource_separate(&range(left), &range(right))
        });
        assert!(separate, "two owned members hold the two ranges");
        range_work.push(work);
        // A refusal asks the whole block, through every route; once is
        // enough to see the nomination grants nothing.
        if size == PARAMETER_SIZES[0] {
            assert!(
                !assumptions.proves_resource_separate(&range(left), &range(3 * FIRST_PARAMETER)),
                "no member holds the second range"
            );
            assert!(
                !assumptions.proves_resource_separate(&range(left), &range(left)),
                "one member holds both sides"
            );
        }
    }
    eprintln!("proved parameter separation units, pointer {pointer_work:?}, range {range_work:?}");
    assert!(
        pointer_work.iter().all(|work| *work == pointer_work[0]),
        "a proved pointer separation read unrelated members: {pointer_work:?}"
    );
    assert!(
        range_work.iter().all(|work| *work == range_work[0]),
        "a proved range separation read unrelated members: {range_work:?}"
    );
}

/// Refusing a missing or overlapping field must be as local as proving a
/// separation: the frame's other independent parameters are not candidates.
#[test]
fn refused_parameter_separation_ignores_unrelated_owned_objects() {
    let mut samples = Vec::new();
    for size in PARAMETER_SIZES {
        let _session = crate::kernel::VerificationSession::enter();
        let (frame, mut assumptions) = parameter_frame(size);
        // Real contract entries retain subobject bounds beside their owners.
        // Bounds select no alias, so they must not open the entire block's
        // candidate set when a requested field is missing.
        for fact in frame.facts() {
            let Some(range) = fact.memory_own_range() else {
                continue;
            };
            let extent = SubobjectExtent {
                start: range.base().clone(),
                width: 8u32.into(),
            };
            assumptions = assumptions.assume_proposition(extent.coverage_fact(range));
        }
        let range = |id| {
            Resource::Memory(MemoryRange::new_with_element_width(
                parameter_base(id),
                1u32.into(),
                2u32.into(),
                4,
            ))
        };
        let left = range(FIRST_PARAMETER);
        let outside = range(3 * FIRST_PARAMETER);
        let (refused, work) = crate::instrumentation::measure_deterministic_work(|| {
            !assumptions.proves_resource_separate(&left, &outside)
                && !assumptions.proves_resource_separate(&left, &left)
        });
        assert!(
            refused,
            "unowned or overlapping fields must not be separated"
        );
        samples.push((size, work));
    }
    assert!(
        samples.iter().all(|(_, work)| *work == samples[0].1),
        "{samples:?}"
    );
}

#[test]
fn normalizing_external_ranges_compares_only_related_bases() {
    let mut samples = Vec::new();
    for size in [8_u64, 16, 32, 64] {
        let mut facts = Vec::new();
        for index in 0..size {
            let base = Pointer {
                block: PointerBlock::ExternalArgument,
                offset: PointerOffsetTerm::scale_int32(
                    MachineTerm::Variable(Variable(9 * TARGET_HEAP + index)),
                    4,
                ),
            };
            facts.push(owned_range(base.clone(), 0, 1));
            facts.push(owned_range(base, 1, 2));
        }
        let context = ResourceContext::new().unchecked_with_facts(facts);
        let (normalized, work) = crate::instrumentation::measure_deterministic_work(|| {
            context.normalized(&PureFactContext::new())
        });
        assert_eq!(normalized.facts().len(), size as usize);
        assert!(normalized.facts().iter().all(|fact| {
            let range = fact.memory_own_range().unwrap();
            range.start().as_const() == Some(0) && range.end().as_const() == Some(2)
        }));
        samples.push(work);
    }
    assert!(
        samples.windows(2).all(|pair| pair[1] <= 3 * pair[0] + 32),
        "{samples:?}"
    );
}

fn tag_schema() -> ResourceFieldSchema {
    ResourceFieldSchema::new(vec![(
        "tag".into(),
        ResourceFieldType::Program(ProgramType::Int32),
    )])
    .unwrap()
}

fn layer_name(layer: usize) -> String {
    format!("layer{layer:05}")
}

/// `layers` field-bearing definitions in a chain: the first owns `p[0..1]`,
/// and each later one names the one before it as a child over the same `p`,
/// with its own `tag` as the child's. Installed as a contract interface
/// installs them: sorted by name, with their reach decided.
fn layered_definitions(layers: usize) -> Vec<CompositeResourceDefinition> {
    let mut definitions = (0..layers)
        .map(|layer| {
            let contains = if layer == 0 {
                vec![ResourceSpec::owned_memory(MemorySegment {
                    uninitialized: false,
                    value_runs: Default::default(),
                    base: crate::kernel::program_expression::variable("p"),
                    start: crate::kernel::program_expression::int32_literal(0),
                    end: crate::kernel::program_expression::int32_literal(1),
                    element_width: 4,
                    guard: None,
                })]
            } else {
                Vec::new()
            };
            let children = if layer == 0 {
                Vec::new()
            } else {
                vec![ResourceChildSpec {
                    name: "child".into(),
                    resource: layer_name(layer - 1),
                    binding: Variable(5_000_000 + layer as u64),
                    arguments: vec![SpecExpression::ProgramExpression(
                        crate::kernel::program_expression::variable("p"),
                    )],
                    field_bindings: vec![ResourceChildField::Parent(0)],
                }]
            };
            CompositeResourceDefinition::new(
                layer_name(layer),
                vec![program_parameter("p", ProgramType::Int32Pointer)],
                None,
                false,
                contains,
                vec![],
            )
            .with_instance_schema(Some(tag_schema()))
            .with_children(children)
        })
        .collect::<Vec<_>>();
    definitions.sort_by(|left, right| left.name().cmp(right.name()));
    crate::kernel::owned_footprint_reach::propagate_owned_footprint_reach(&mut definitions);
    definitions
}

fn layered_instance(layers: usize) -> ResourceFact {
    ResourceFact::own(Resource::Instance(
        ResourceInstance::new(
            Variable(2 * TARGET_HEAP),
            layer_name(layers - 1),
            vec![ProgramValue::pointer(heap_base(TARGET_HEAP)).into()].into(),
            tag_schema(),
            vec![int32(0).into()].into(),
        )
        .unwrap(),
    ))
}

/// The owned footprint of the outermost of `N` layered definitions is the one
/// cell the innermost owns, derived with one visit per layer: work linear in
/// the definitions, not a nesting bound. Deciding which definitions reach
/// unnamed memory, once per definition set, is linear too.
#[test]
fn a_layered_footprint_is_linear_in_its_definitions() {
    const LAYER_COUNTS: [usize; 4] = [8, 32, 128, 512];
    let mut derived = Vec::new();
    let mut installed = Vec::new();
    for layers in LAYER_COUNTS {
        let (definitions, work) =
            crate::instrumentation::measure_deterministic_work(|| layered_definitions(layers));
        installed.push((layers, work));
        let state = ExecutionState::new();
        let assumptions = PureFactContext::new();
        let fact = layered_instance(layers);
        let (ranges, work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::kernel::functions::checked_owned_memory_ranges(
                &fact,
                &definitions,
                &state,
                &assumptions,
            )
            .unwrap()
        });
        assert_eq!(
            ranges,
            vec![MemoryRange::new(
                heap_base(TARGET_HEAP),
                MachineTerm::constant(0),
                MachineTerm::constant(1),
            )],
            "a {layers}-layer chain owns exactly the innermost cell"
        );
        derived.push((layers, work));
    }
    eprintln!("layered footprint by layer count (N, units): {derived:?}");
    eprintln!("layered reach by layer count (N, units): {installed:?}");
    for (what, samples) in [("footprint", &derived), ("reach", &installed)] {
        let (smallest, base_work) = samples[0];
        let per_layer = base_work as f64 / smallest as f64;
        for (layers, work) in samples {
            let allowed = 2.0 * per_layer * *layers as f64 + 8.0;
            assert!(
                (*work as f64) <= allowed,
                "a {layers}-layer {what} charged {work} units, above {allowed:.1} (linear in \
                 the definitions): {samples:?}"
            );
        }
    }
}

/// A recursive definition's footprint is unnamed memory, decided from the
/// definition: however many nodes the state knows are live, the derivation
/// does not descend into them.
#[test]
fn a_recursive_footprint_is_constant_in_live_nodes() {
    let mut definitions = vec![CompositeResourceDefinition::new(
        "list",
        vec![program_parameter("p", ProgramType::Int32Pointer)],
        None,
        true,
        vec![
            ResourceSpec::owned_memory(MemorySegment {
                uninitialized: false,
                value_runs: Default::default(),
                base: crate::kernel::program_expression::variable("p"),
                start: crate::kernel::program_expression::int32_literal(0),
                end: crate::kernel::program_expression::int32_literal(1),
                element_width: 4,
                guard: None,
            }),
            ResourceSpec::composite(
                ResourceAccessMode::Own,
                "list".into(),
                vec![crate::kernel::program_expression::pointer_offset_bytes(
                    crate::kernel::program_expression::variable("p"),
                    4,
                )],
                vec![ProgramType::Int32Pointer],
            ),
        ],
        vec![],
    )];
    crate::kernel::owned_footprint_reach::propagate_owned_footprint_reach(&mut definitions);
    let mut samples = Vec::new();
    for nodes in SIZES {
        // The live nodes: a known cell at each of them.
        let memory = (0..nodes).fold(Memory::new(), |memory, node| {
            memory.store(
                Pointer {
                    block: PointerBlock::Heap(TARGET_HEAP),
                    offset: PointerOffsetTerm::Constant(4 * node as i64),
                },
                int32(node as u32),
            )
        });
        let state = ExecutionState::new().with_memory(memory);
        let assumptions = PureFactContext::new();
        let fact = ResourceFact::own(Resource::Composite {
            name: "list".into(),
            arguments: vec![ProgramValue::pointer(heap_base(TARGET_HEAP)).into()].into(),
        });
        let (ranges, work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::kernel::functions::checked_owned_memory_ranges(
                &fact,
                &definitions,
                &state,
                &assumptions,
            )
            .unwrap()
        });
        assert_eq!(ranges, vec![MemoryRange::unnamed_footprint()]);
        samples.push((nodes, work));
    }
    assert_constant_plus_log_growth("a recursive footprint", &samples, 0.0);
}

/// `slot(s)`: the arena's region shape. The body owns the descriptor
/// `s[0..4]` and the cells `s->pool->data[at..end]`, whose base loads the
/// descriptor's first field and then the pool's.
fn slot_definitions() -> Vec<CompositeResourceDefinition> {
    let schema = ResourceFieldSchema::new(vec![
        ("at".into(), ResourceFieldType::Program(ProgramType::Int32)),
        ("end".into(), ResourceFieldType::Program(ProgramType::Int32)),
    ])
    .unwrap();
    let pool = crate::kernel::program_expression::typed_load(
        crate::kernel::program_expression::variable("s"),
        ProgramType::Int32Pointer,
    );
    vec![
        CompositeResourceDefinition::new(
            "slot",
            vec![program_parameter("s", ProgramType::Int32Pointer)],
            None,
            false,
            vec![
                ResourceSpec::owned_memory(MemorySegment {
                    uninitialized: false,
                    value_runs: Default::default(),
                    base: crate::kernel::program_expression::variable("s"),
                    start: crate::kernel::program_expression::int32_literal(0),
                    end: crate::kernel::program_expression::int32_literal(4),
                    element_width: 4,
                    guard: None,
                }),
                ResourceSpec::owned_memory(MemorySegment {
                    uninitialized: false,
                    value_runs: Default::default(),
                    base: crate::kernel::program_expression::typed_load(
                        pool,
                        ProgramType::Int32Pointer,
                    ),
                    start: crate::kernel::program_expression::variable("at"),
                    end: crate::kernel::program_expression::variable("end"),
                    element_width: 4,
                    guard: None,
                }),
            ],
            vec![],
        )
        .with_instance_schema(Some(schema)),
    ]
}

fn external_descriptor(identity: u64) -> Pointer {
    Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(identity)), 4),
    }
}

/// The pointer a load of `cell` reads in `source`, as execution materializes
/// it: the value named by that read.
fn materialized_pointer(source: &Memory, cell: &Pointer) -> ProgramValue {
    ProgramValue::Pointer(PointerValue::from_read(
        Pointer::loaded(&MachineTerm::MemoryLoad(
            crate::kernel::intern_memory_ref(source),
            Box::new(cell.clone()),
            crate::kernel::LoadKind::Int32,
        ))
        .unwrap(),
        ProgramType::Int32Pointer,
        &crate::kernel::intern_memory_ref(source),
        cell,
    ))
}

/// Unfolding a region beside other owned descriptors of its type reads the
/// region's own descriptor field through their materialized `pool` cells.
/// The work is the region body's: one second descriptor argument beside it
/// and any number of unrelated same-type descriptors in their own
/// allocations, each owned and each with its `pool` cell materialized, cost
/// nothing that grows with their number.
#[test]
fn unfold_beside_descriptors_of_its_type_ignores_unrelated_descriptors() {
    let mut samples = Vec::new();
    for size in [4usize, 16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let definitions = slot_definitions();
        let region = external_descriptor(100_000);
        let other = external_descriptor(100_001);
        let entry = Memory::new();
        let pool = match materialized_pointer(&entry, &region) {
            ProgramValue::Pointer(value) => value,
            _ => unreachable!("a pointer cell is materialized as a pointer"),
        };
        let instance = ResourceInstance::new(
            Variable(2 * TARGET_HEAP),
            "slot".into(),
            vec![ProgramValue::typed_pointer(region.clone(), ProgramType::Int32Pointer).into()]
                .into(),
            ResourceFieldSchema::new(vec![
                ("at".into(), ResourceFieldType::Program(ProgramType::Int32)),
                ("end".into(), ResourceFieldType::Program(ProgramType::Int32)),
            ])
            .unwrap(),
            vec![int32(0).into(), int32(2).into()].into(),
        )
        .unwrap();
        let unrelated = (0..size)
            .map(|index| heap_base(index as u64 + 1))
            .collect::<Vec<_>>();
        let memory = unrelated.iter().fold(
            entry
                .clone()
                .store(other.clone(), materialized_pointer(&entry, &other)),
            |memory, descriptor| {
                memory.store(descriptor.clone(), materialized_pointer(&entry, descriptor))
            },
        );
        let frame = ResourceContext::new()
            .unchecked_with_facts(
                unrelated
                    .iter()
                    .map(|descriptor| owned_range(descriptor.clone(), 0, 4)),
            )
            .unchecked_with_facts([
                owned_range(other.clone(), 0, 4),
                ResourceFact::own_memory(MemoryRange::from_pointer_value(
                    &pool,
                    0u32.into(),
                    4u32.into(),
                    4,
                )),
                ResourceFact::own(Resource::Instance(instance.clone())),
            ]);
        let state = ExecutionState::new()
            .with_memory(memory)
            .with_resource_context(frame);
        let assumptions = PureFactContext::new();
        let (unfolded, work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::kernel::rewrite_resource_instance_selecting_children(
                &state,
                &instance,
                &definitions[0],
                &definitions,
                &assumptions,
                true,
                None,
            )
        });
        let unfolded = unfolded.unwrap_or_else(|refusal| {
            panic!(
                "the region unfolds beside {size} descriptors of its type: {}",
                refusal.describe()
            )
        });
        assert!(
            unfolded
                .state
                .resources
                .owned_instance(instance.identity)
                .is_none(),
            "the region is unfolded"
        );
        samples.push((size, work));
    }
    assert_constant_plus_log_growth("unfold beside descriptors of its type", &samples, 16.0);
}

/// A folded `window(p)` of a pointer parameter: its body owns `p[start..1]`
/// at its own field `start = 0`, which is the cell at `p`.
fn parameter_window_instance(parameter: u64, identity: u64) -> ResourceFact {
    ResourceFact::own(Resource::Instance(
        ResourceInstance::new(
            Variable(identity),
            "window".into(),
            vec![ProgramValue::pointer(parameter_base(parameter)).into()].into(),
            ResourceFieldSchema::new(vec![(
                "start".into(),
                ResourceFieldType::Program(ProgramType::Int32),
            )])
            .unwrap(),
            vec![int32(0).into()].into(),
        )
        .unwrap(),
    ))
}

const STORE_WRITTEN_PARAMETER: u64 = 97_000;
const STORE_KEPT_PARAMETER: u64 = 97_001;

/// Frames one store at the written parameter's object as the store
/// statement does: the opened composition first, then the cached cells. It
/// returns the charged work and how many of `kept` cached cells survived.
fn framed_store_beside_instances(state: &ExecutionState, kept: &[Pointer]) -> (usize, usize) {
    let write = parameter_base(STORE_WRITTEN_PARAMETER);
    let assumptions = PureFactContext::new()
        .assume_proposition(Proposition::ResourceComposition(state.resources().clone()));
    let (memory, work) = crate::instrumentation::measure_deterministic_work(|| {
        let assumptions = match crate::kernel::functions::store_opened_instance_composition(
            state,
            &write,
            4,
            &assumptions,
        ) {
            Some(opened) => {
                assumptions.assume_proposition(Proposition::ResourceComposition(opened))
            }
            None => assumptions.clone(),
        };
        state
            .memory
            .clone()
            .without_possible_aliasing_cells(&write, 4, &assumptions)
    });
    let survived = kept
        .iter()
        .filter(|cell| memory.has_known_cell_at(cell))
        .count();
    (work, survived)
}

/// A store beside folded field-bearing instances opens only the instances
/// whose arguments name the base of a cell it could drop. Instances in heap
/// blocks, which a parameter store cannot alias, and instances of other
/// parameters with no cached cell are never visited, however many there are:
/// the work to keep the one cell a folded instance owns is constant in them.
#[test]
fn a_store_opens_no_folded_instance_whose_arguments_name_no_cached_cell() {
    let _armed = crate::kernel::arm_frame_composite_definitions(window_definitions(1));
    let kept = parameter_base(STORE_KEPT_PARAMETER);
    let mut samples = Vec::new();
    for size in [4usize, 16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let frame = ResourceContext::new()
            .unchecked_with_facts((0..size).flat_map(|index| {
                [
                    window_instance(index as u64 + 1, TARGET_HEAP + 1 + index as u64),
                    parameter_window_instance(
                        FIRST_PARAMETER + index as u64,
                        2 * TARGET_HEAP + 1 + index as u64,
                    ),
                ]
            }))
            .unchecked_with_facts([
                parameter_object(STORE_WRITTEN_PARAMETER),
                parameter_window_instance(STORE_KEPT_PARAMETER, 3 * TARGET_HEAP),
            ]);
        let memory = (0..size)
            .fold(Memory::new(), |memory, index| {
                memory.store(heap_base(index as u64 + 1), int32(index as u32))
            })
            .store(kept.clone(), int32(5));
        let state = ExecutionState::new()
            .with_resource_context(frame)
            .with_memory(memory);
        let (work, survived) = framed_store_beside_instances(&state, std::slice::from_ref(&kept));
        assert_eq!(survived, 1, "the folded instance's cell survives the store");
        samples.push((size, work));
    }
    assert_constant_plus_log_growth("a store beside unrelated folded instances", &samples, 8.0);
}

/// The same framing is linear in the folded instances whose arguments name a
/// cached cell's base: each is opened once, one body layer, and keeps its
/// cell.
#[test]
fn a_store_opens_folded_instances_in_work_linear_in_the_aliasing_ones() {
    let _armed = crate::kernel::arm_frame_composite_definitions(window_definitions(1));
    let mut samples = Vec::new();
    for size in PARAMETER_SIZES {
        let _session = crate::kernel::VerificationSession::enter();
        let frame = ResourceContext::new()
            .unchecked_with_facts((0..size).map(|index| {
                parameter_window_instance(
                    FIRST_PARAMETER + index as u64,
                    2 * TARGET_HEAP + 1 + index as u64,
                )
            }))
            .unchecked_with_fact(parameter_object(STORE_WRITTEN_PARAMETER));
        let cells = (0..size)
            .map(|index| parameter_base(FIRST_PARAMETER + index as u64))
            .collect::<Vec<_>>();
        let memory = cells.iter().fold(Memory::new(), |memory, cell| {
            memory.store(cell.clone(), int32(5))
        });
        let state = ExecutionState::new()
            .with_resource_context(frame)
            .with_memory(memory);
        let (work, survived) = framed_store_beside_instances(&state, &cells);
        assert_eq!(survived, size, "every opened instance keeps its cell");
        samples.push((size, work));
    }
    eprintln!("a store beside aliasing folded instances (N, units): {samples:?}");
    for pair in samples.windows(2) {
        let [(small, small_work), (large, large_work)] = pair else {
            unreachable!()
        };
        assert!(
            (*large_work as f64) <= 1.5 * (*large as f64 / *small as f64) * *small_work as f64,
            "a store beside aliasing folded instances: work grew faster than the \
             instances: {samples:?}"
        );
    }
}

/// Without the opening, the same store forgets the cell: a folded instance's
/// body is not a composition member until the store opens it, and with no
/// definitions to open it by there is nothing to open.
#[test]
fn a_store_forgets_a_folded_instance_cell_it_does_not_open() {
    let kept = parameter_base(STORE_KEPT_PARAMETER);
    let frame = ResourceContext::new().unchecked_with_facts([
        parameter_object(STORE_WRITTEN_PARAMETER),
        parameter_window_instance(STORE_KEPT_PARAMETER, 3 * TARGET_HEAP),
    ]);
    let state = ExecutionState::new()
        .with_resource_context(frame)
        .with_memory(Memory::new().store(kept.clone(), int32(5)));
    // No definitions armed: nothing can be opened.
    let (_, survived) = framed_store_beside_instances(&state, std::slice::from_ref(&kept));
    assert_eq!(survived, 0, "an unopened instance keeps nothing");
    let _armed = crate::kernel::arm_frame_composite_definitions(window_definitions(1));
    let (_, survived) = framed_store_beside_instances(&state, std::slice::from_ref(&kept));
    assert_eq!(survived, 1, "the opened instance keeps its cell");
}

#[test]
#[ignore = "nightly: 1.0s in the parallel gate"]
fn shared_view_offset_alias_lookup_is_indexed_and_preserves_occurrences() {
    let base = symbolic_base(TARGET_HEAP);
    let alias = symbolic_base(2 * TARGET_HEAP);
    let index = MachineTerm::Variable(Variable(3 * TARGET_HEAP));
    let displaced = base.offset_by_elements(index.clone(), 1);
    let facts = PureFactContext::new()
        .assume_condition(pointer_equal(alias.clone(), displaced), true)
        .assume_condition(
            ConditionTerm::signed_less_equal(0u32.into(), index.clone()),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_equal(MachineTerm::add(index, 4u32.into()), 16u32.into()),
            true,
        );
    let view = |pointer, end| {
        ResourceFact::view_memory(MemoryRange::new_with_element_width(
            pointer,
            0u32.into(),
            end,
            1,
        ))
    };
    let held = view(base, 16u32.into());
    let required = view(alias.clone(), 4u32.into());
    let mut samples = Vec::new();
    for size in [8usize, 32, 128, 512] {
        let resources = ResourceContext::new_with_equalities(&facts)
            .unchecked_with_facts((0..size).map(|i| view(heap_base(i as u64 + 1), 16u32.into())))
            .unchecked_with_fact(held.clone());
        resources.synchronize_memory_equalities(&facts);
        let occurrence = resources.occurrences_for_fact(&held)[0];
        let (found, work) = crate::instrumentation::measure_deterministic_work(|| {
            resources.view_occurrences_for_fact(&required, &facts)
        });
        assert_eq!(found, vec![occurrence]);
        assert!(
            resources
                .view_occurrences_for_fact(&required, &PureFactContext::new())
                .is_empty()
        );
        assert!(
            resources
                .view_occurrences_for_fact(&view(alias.clone(), 17u32.into()), &facts)
                .is_empty()
        );
        samples.push((size, work));
    }
    assert_constant_plus_log_growth("shared view offset alias", &samples, 64.0);
}

#[test]
fn observable_projection_reuses_private_local_deltas_and_unchanged_queries() {
    for size in [4, 16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        crate::kernel::set_never_address_taken_locals(
            (0..size).map(|index| format!("hidden_{index}")).collect(),
        );
        let assumptions = PureFactContext::new();
        let base = ResourceContext::new().unchecked_with_facts([
            owned_range(heap_base(1), 0, 4),
            owned_range(heap_base(2), 0, 4),
        ]);
        let expected = base.observable_composition();
        let mut resources = base;
        let (_, sequence_work) = crate::instrumentation::measure_deterministic_work(|| {
            for index in 0..size {
                resources = resources.clone().unchecked_with_fact(owned_range(
                    Memory::local_pointer(&format!("hidden_{index}")),
                    0,
                    4,
                ));
                let observed = resources.observable_composition();
                assert!(std::sync::Arc::ptr_eq(&observed.storage, &expected.storage));
            }
        });
        assert!(
            sequence_work <= size * 8 + 16,
            "private insertion/projection N={size}: {sequence_work}"
        );
        let (_, query_work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..16 {
                assert_eq!(
                    resources.observable_facts_assuming_valid(&assumptions),
                    vec![Proposition::ResourceComposition(expected.clone())]
                );
            }
        });
        assert!(query_work <= 32, "unchanged queries N={size}: {query_work}");
        let (_, addressed_work) = crate::instrumentation::measure_deterministic_work(|| {
            resources = resources
                .clone()
                .unchecked_with_fact(owned_range(heap_base(3), 0, 4));
            assert_eq!(resources.observable_composition().facts().len(), 3);
        });
        assert!(
            addressed_work <= 32,
            "addressable delta N={size}: {addressed_work}"
        );
        resources = resources
            .without_exact_representation(&owned_range(heap_base(3), 0, 4))
            .unwrap();
        let removal_root = resources.observable_composition();
        let (_, removal_work) = crate::instrumentation::measure_deterministic_work(|| {
            for index in 0..size {
                resources = resources
                    .clone()
                    .without_exact_representation(&owned_range(
                        Memory::local_pointer(&format!("hidden_{index}")),
                        0,
                        4,
                    ))
                    .unwrap();
                assert!(std::sync::Arc::ptr_eq(
                    &resources.observable_composition().storage,
                    &removal_root.storage
                ));
                assert_eq!(resources.observable_composition(), expected);
            }
        });
        assert!(
            removal_work <= size * 12 + 16,
            "private removal/projection N={size}: {removal_work}"
        );
        eprintln!(
            "observable projection N={size}: insert={sequence_work}, queries={query_work}, addressed={addressed_work}, remove={removal_work}"
        );
    }
}

#[test]
fn observable_projection_queries_do_not_enumerate_retained_owners() {
    let mut costs = Vec::new();
    for size in [4, 16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let context = ResourceContext::new().unchecked_with_facts(
            (0..size).map(|index| owned_range(heap_base(index as u64 + 1), 0, 4)),
        );
        let assumptions = PureFactContext::new();
        context.synchronize_memory_equalities(&assumptions);
        let expected = context.observable_composition();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..16 {
                let result = context.observable_facts_assuming_valid(&assumptions);
                let [Proposition::ResourceComposition(observed)] = result.as_slice() else {
                    panic!("owned composition is observable");
                };
                assert!(std::sync::Arc::ptr_eq(&observed.storage, &expected.storage));
                observed.synchronize_memory_equalities(&assumptions);
            }
        });
        assert!(work <= 256, "retained owner queries N={size}: {work}");
        costs.push(work);
    }
    assert!(
        costs.iter().all(|work| *work == costs[0]),
        "prepared projection costs: {costs:?}"
    );
}

#[test]
fn observable_projection_shares_first_projection_across_cold_forks() {
    for size in [4, 16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        crate::kernel::set_never_address_taken_locals(
            (0..size).map(|index| format!("hidden_{index}")).collect(),
        );
        let root =
            ResourceContext::new().unchecked_with_facts(
                [
                    owned_range(heap_base(1), 0, 4),
                    owned_range(heap_base(2), 0, 4),
                ]
                .into_iter()
                .chain((0..size).map(|index| {
                    owned_range(Memory::local_pointer(&format!("hidden_{index}")), 0, 4)
                })),
            );
        let forks = [root.clone(), root.clone(), root.clone()];
        let expected = root.observable_composition();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for fork in &forks {
                assert!(std::sync::Arc::ptr_eq(
                    &fork.observable_composition().storage,
                    &expected.storage
                ));
            }
        });
        assert!(
            work <= 8,
            "cold fork N={size} repeated {work} projection units"
        );
        let changed = forks[0]
            .clone()
            .unchecked_with_fact(owned_range(heap_base(3), 0, 4));
        assert_eq!(changed.observable_composition().facts().len(), 3);
        assert!(std::sync::Arc::ptr_eq(
            &forks[1].observable_composition().storage,
            &expected.storage
        ));
    }
}

#[test]
fn observable_projection_reuses_local_edits_across_sibling_paths() {
    let mut samples = Vec::new();
    for size in [4usize, 16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        crate::kernel::set_never_address_taken_locals(
            (0..size).map(|i| format!("hidden_{i}")).collect(),
        );
        let assumptions = PureFactContext::new();
        let mut source = ResourceContext::new().unchecked_with_facts([
            owned_range(heap_base(1), 0, 4),
            owned_range(heap_base(2), 0, 4),
        ]);
        for i in 0..size {
            source = source.unchecked_with_fact(owned_range(
                Memory::local_pointer(&format!("hidden_{i}")),
                0,
                4,
            ));
        }
        let expected = source.observable_facts_assuming_valid(&assumptions);
        let sibling = source
            .clone()
            .unchecked_with_fact(owned_range(heap_base(3), 0, 4));
        let (changed, work) = crate::instrumentation::measure_deterministic_work(|| {
            sibling.observable_facts_assuming_valid(&assumptions)
        });
        assert_ne!(changed, expected);
        assert_eq!(
            source.observable_facts_assuming_valid(&assumptions),
            expected
        );
        assert_eq!(
            sibling.observable_facts_assuming_valid(&assumptions),
            changed
        );
        assert_eq!(source.facts().len(), size + 2);
        crate::kernel::withdraw_never_address_taken_locals(&BTreeSet::from(
            ["hidden_0".to_owned()],
        ));
        assert_ne!(
            source.observable_facts_assuming_valid(&assumptions),
            expected
        );
        samples.push((size, work));
    }
    assert_constant_plus_log_growth("observable projection local edit", &samples, 4.0);
}

#[test]
fn observable_projection_tracks_supported_views_caches_and_owner_retirement() {
    for size in [16usize, 32, 64, 128] {
        let _session = crate::kernel::VerificationSession::enter();
        crate::kernel::set_never_address_taken_locals(
            (0..size).map(|i| format!("hidden_{i}")).collect(),
        );
        let assumptions = PureFactContext::new();
        let owner = owned_range(heap_base(1), 0, 4);
        let view =
            ResourceFact::view_memory(MemoryRange::new(heap_base(1), 0u32.into(), 2u32.into()));
        let mut source = ResourceContext::new()
            .unchecked_with_facts([owner.clone(), owned_range(heap_base(2), 0, 4)]);
        for i in 0..size {
            source = source.unchecked_with_fact(owned_range(
                Memory::local_pointer(&format!("hidden_{i}")),
                0,
                4,
            ));
        }
        source.observable_facts_assuming_valid(&assumptions);
        let supported = source
            .clone()
            .unchecked_with_supported_facts(&owner, [view.clone()]);
        let cached = supported
            .clone()
            .with_cached_supported_expansion(&owner, vec![view.clone()]);
        let retired = cached
            .clone()
            .without_fact_delaying_normalization(&owner, &assumptions)
            .expect("the exact owner can be consumed");
        for context in [&supported, &cached, &retired, &source, &cached] {
            let mut fresh = context.clone();
            fresh.observable_projection = Default::default();
            let expected = fresh.observable_facts_assuming_valid(&assumptions);
            assert_eq!(
                context.observable_facts_assuming_valid(&assumptions),
                expected
            );
        }
        assert!(
            !retired.contains_exact_representation(&view),
            "a cached view cannot survive its owner"
        );
        let hidden_owner = owned_range(Memory::local_pointer("hidden_0"), 0, 4);
        let hidden_view = ResourceFact::view_memory(MemoryRange::new(
            Memory::local_pointer("hidden_0"),
            0u32.into(),
            2u32.into(),
        ));
        let hidden_supported = source
            .clone()
            .unchecked_with_supported_facts(&hidden_owner, [hidden_view]);
        assert_eq!(
            hidden_supported.observable_facts_assuming_valid(&assumptions),
            source.observable_facts_assuming_valid(&assumptions)
        );
    }
}

fn argument_base(variable: u64) -> Pointer {
    Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scaled_int32_node(MachineTerm::Variable(Variable(variable)), 4),
    }
}

/// Composing a call's footprint asks whether each pair of its ranges
/// overlaps, rebasing both through the exact aliases the facts state for
/// their bases. Along a path those alias classes grow (`arena`,
/// `first->arena`, `second->arena`, ...), and asking every pair of aliases
/// made the same footprint's composition cost the product of the two classes
/// in endpoint decisions, so each later call in `examples/arena` paid more
/// than the last. An alias pair whose bases are a symbolic distance apart is
/// the same question about equal addresses, so only constant displacements
/// are asked beyond the ranges' own spellings; what remains per extra alias
/// pair is one structural comparison.
#[test]
fn footprint_composition_does_not_decide_every_alias_pair() {
    const STRUCT: u64 = 994_000;
    const ARRAY: u64 = 994_001;
    const LENGTH: u64 = 994_002;
    let footprint = [
        owned_range(argument_base(STRUCT), 0, 2),
        owned_range(argument_base(STRUCT), 2, 4),
        owned_range(argument_base(STRUCT), 4, 6),
        ResourceFact::own_memory(MemoryRange::new(
            argument_base(ARRAY),
            MachineTerm::constant(0),
            MachineTerm::Variable(Variable(LENGTH)),
        )),
    ];
    let mut samples = Vec::new();
    for aliases in [1_u64, 2, 4, 8] {
        let _session = crate::kernel::VerificationSession::enter();
        // A path's order facts about the array length, which an endpoint
        // decision about the array's range searches.
        let ordered = (0..32_u64).fold(PureFactContext::new(), |facts, index| {
            let below = if index == 0 {
                LENGTH
            } else {
                997_000 + index - 1
            };
            facts.assume_condition(
                ConditionTerm::signed_less_than(
                    MachineTerm::Variable(Variable(below)),
                    MachineTerm::Variable(Variable(997_000 + index)),
                ),
                true,
            )
        });
        let assumptions = (0..aliases).fold(ordered, |facts, index| {
            facts
                .assume_condition(
                    pointer_equal(argument_base(STRUCT), argument_base(995_000 + index)),
                    true,
                )
                .assume_condition(
                    pointer_equal(argument_base(ARRAY), argument_base(996_000 + index)),
                    true,
                )
        });
        let (composed, work) = crate::instrumentation::measure_deterministic_work(|| {
            ResourceContext::new().try_compose_with_facts(footprint.iter().cloned(), &assumptions)
        });
        assert!(composed.is_ok(), "the footprint is a partition");
        samples.push((aliases as usize, work));
    }
    eprintln!("footprint composition (aliases per base, units): {samples:?}");
    let (_, base_work) = samples[0];
    for (aliases, work) in &samples {
        // A bounded structural cost per alias pair, never an endpoint
        // decision that searches the path's order facts: asking every pair
        // charged 2198, 5124, 15296 and 52920 units here.
        let allowed = base_work + 48 * aliases * aliases;
        assert!(
            *work <= allowed,
            "composition with {aliases} aliases per base charged {work} units, above \
             {allowed}: {samples:?}"
        );
    }
}

/// One selected overlap question must not enumerate aliases of either base.
/// Setup admits the equalities before measuring the cold query.
#[test]
fn selected_ownership_overlap_ignores_ambient_aliases() {
    let mut samples = Vec::new();
    for count in [4_u64, 16, 64] {
        let _session = crate::kernel::VerificationSession::enter();
        let left = argument_base(998_000);
        let right = argument_base(998_001);
        let assumptions = (0..count).fold(PureFactContext::new(), |facts, index| {
            facts
                .assume_condition(
                    pointer_equal(left.clone(), argument_base(999_000 + index)),
                    true,
                )
                .assume_condition(
                    pointer_equal(right.clone(), argument_base(999_100 + index)),
                    true,
                )
        });
        let range =
            |base| MemoryRange::new(base, 0u32.into(), MachineTerm::Variable(Variable(998_002)));
        let left = range(left);
        let right = range(right);
        let (overlaps, work) = crate::instrumentation::measure_deterministic_work(|| {
            memory_ranges_proven_overlapping(&left, &right, &assumptions)
        });
        assert!(!overlaps, "unrelated bases do not establish overlap");
        samples.push((count, work));
    }
    eprintln!("selected ownership overlap aliases: {samples:?}");
    assert!(
        samples.iter().all(|(_, work)| *work <= samples[0].1 + 64),
        "selected overlap enumerates ambient aliases: {samples:?}"
    );
}

/// A heap allocation of `bytes` bytes at `identity`, its first word written,
/// as a `malloc` that succeeded leaves it: the allocation token and complete
/// byte access, both owned.
fn with_live_allocation(
    (memory, resources): (Memory, ResourceContext),
    identity: u64,
    bytes: u32,
) -> (Memory, ResourceContext) {
    let pending = symbolic_base(identity);
    let (memory, _, base) = memory
        .with_pending_heap_allocation(
            pending.clone(),
            HeapExtent::int32(MachineTerm::constant(bytes)),
            false,
        )
        .resolve_pending_heap_allocation(&pending, true)
        .expect("the pending allocation resolves");
    assert_eq!(base, heap_base(identity));
    let memory = memory.store(base.clone(), int32(identity as u32));
    let resources = resources.unchecked_with_facts([
        ResourceFact::own_allocation(base.clone(), bytes),
        ResourceFact::own_memory(MemoryRange::new_with_element_width(
            base,
            MachineTerm::constant(0),
            MachineTerm::constant(bytes),
            1,
        )),
    ]);
    (memory, resources)
}

/// The allocation the caller has written an `int` into before the call,
/// beside the lent one.
const WRITTEN_INT_HEAP: u64 = TARGET_HEAP + 1;

/// A caller holding `unrelated` live heap allocations beside the target,
/// each reached from its own never-address-taken pointer local, whose
/// automatic storage the caller owns, as C lowering leaves `int *u = malloc(..)`.
fn caller_beside_unrelated_allocations(unrelated: usize) -> ExecutionState {
    let locals = (0..unrelated)
        .map(|index| (format!("u{index}"), index as u64 + 1))
        .chain([("p".to_owned(), TARGET_HEAP)])
        .collect::<Vec<_>>();
    crate::kernel::set_never_address_taken_locals(
        locals.iter().map(|(name, _)| name.clone()).collect(),
    );
    let (mut memory, mut resources) = locals.iter().fold(
        (Memory::new(), ResourceContext::new()),
        |caller, (_, identity)| with_live_allocation(caller, *identity, 16),
    );
    // Writing the `int` retyped its bytes: the caller owns them as one
    // `int` cell and holds the cell's view, supported by that owner, with
    // the owner's cached identity expansion. A lending call's recovery
    // normalizes the caller's resources, dropping and restoring both.
    let written = MemoryRange::new(
        heap_base(WRITTEN_INT_HEAP),
        MachineTerm::constant(0),
        MachineTerm::constant(4),
    );
    let pending = symbolic_base(WRITTEN_INT_HEAP);
    let (written_memory, _, _) = memory
        .with_pending_heap_allocation(pending.clone(), HeapExtent::int32(4), false)
        .resolve_pending_heap_allocation(&pending, true)
        .expect("the pending allocation resolves");
    memory = written_memory.store(heap_base(WRITTEN_INT_HEAP), int32(7));
    let written_owner = ResourceFact::own_memory(written.clone());
    resources = resources
        .unchecked_with_facts([
            ResourceFact::own_allocation(heap_base(WRITTEN_INT_HEAP), 4u32),
            written_owner.clone(),
        ])
        .unchecked_with_supported_facts(&written_owner, [ResourceFact::view_memory(written)])
        .with_cached_supported_expansion(&written_owner, vec![written_owner.clone()]);
    let mut state = ExecutionState::new().with_population_creation_tracking();
    for (name, identity) in &locals {
        let slot = Memory::local_pointer(name);
        memory = memory
            .with_block(slot.block.clone(), 8)
            .store(slot.clone(), ProgramValue::pointer(heap_base(*identity)));
        resources = resources.unchecked_with_fact(owned_range(slot, 0, 8));
        state = state.with_local(name.clone(), ProgramValue::pointer(heap_base(*identity)));
    }
    // The call views `p`'s bytes, so they hold values the caller wrote.
    let memory = memory.with_initialized_object(&heap_base(TARGET_HEAP), 16);
    state
        .with_local("observed", int32(0))
        .with_memory(memory)
        .with_resource_context(resources)
}

/// A call whose contract only `views` a heap range costs work that does not
/// grow with unrelated live allocations, including the observable projection
/// of the caller's resources after it, which every next statement reads.
///
/// The call lends a stable view; recovering it normalizes the caller's
/// resources, which drops and restores the supported view entries and their
/// cached expansions. Before that normalization advanced the observable
/// projection, clearing the expansions replaced the storage root behind the
/// projection's back, the next producer dropped the stale view, and the
/// next observation recomputed it by removing every never-address-taken
/// local's entries, each removal updating the paired memory-equality index again.
/// Measured on 2026-10-15 beside 2, 4, 8 and 16 allocations: 506, 528, 572
/// and 660 units then, 479 at every size since (about 19 units per
/// allocation in the expanded byte-representation round trip).
#[test]
fn a_view_lending_call_and_its_observation_ignore_unrelated_allocations() {
    let helper = program_function(
        ProgramType::Int32,
        "peek",
        vec![program_parameter("data", ProgramType::Int32Pointer)],
        program_return(crate::kernel::program_expression::int32_literal(0)),
    )
    .with_resource_summary(
        vec![ResourceSpec::viewed_memory(MemorySegment::new(
            crate::kernel::program_expression::variable("data"),
            crate::kernel::program_expression::int32_literal(0),
            crate::kernel::program_expression::int32_literal(4),
        ))],
        Vec::new(),
    );
    let environment = ExecutionEnvironment::new()
        .with_function(helper.clone())
        .with_verified_function_rule(VerifiedFunctionRule {
            pointer_result: None,
            function: helper,
            loop_semantics: LoopSemantics::Verify,
            checked_callees: None,
            applied_tactics: Default::default(),
        });
    let call = program_call_assign(
        "observed",
        "peek",
        vec![crate::kernel::program_expression::variable("p")],
    );
    let assumptions = PureFactContext::new();
    let mut samples = Vec::new();
    for size in [2usize, 4, 8, 16] {
        let _session = crate::kernel::VerificationSession::enter();
        let caller = caller_beside_unrelated_allocations(size);
        // The steps before the call have already published the caller's
        // resources to the equality graph, counted its memory's variables,
        // and observed its resources; each of those is a one-time cost of
        // the input, maintained by deltas afterwards.
        caller
            .resources()
            .synchronize_memory_equalities(&assumptions);
        crate::kernel::reasoning::variable_collection::collect_execution_state_bitvector_variables(
            &caller,
            &mut BTreeSet::new(),
        );
        caller
            .resources()
            .observable_facts_assuming_valid(&assumptions);
        let (after, work) = crate::instrumentation::measure_deterministic_work(|| {
            let paths = execute_execution_statement_paths(
                &caller,
                &call,
                &assumptions,
                ExecutionContext::apply_verified_rules(&environment),
                &mut ExecutionBudget::default(),
            )
            .expect("the view-lending call executes");
            let [
                StatementExecutionPath {
                    outcome: StatementOutcome::Normal(after),
                    ..
                },
            ] = paths.as_slice()
            else {
                panic!("the call returns normally: {paths:?}");
            };
            let after = (**after).clone();
            after
                .resources()
                .observable_facts_assuming_valid(&assumptions);
            after
        });
        // The warm projection is the one a cold recomputation gives.
        let observed = after
            .resources()
            .observable_facts_assuming_valid(&assumptions);
        let mut cold = after.resources().clone();
        cold.observable_projection = Default::default();
        assert_eq!(observed, cold.observable_facts_assuming_valid(&assumptions));
        let [Proposition::ResourceComposition(composition)] = observed.as_slice() else {
            panic!("the caller's owned heap is observable: {observed:?}");
        };
        // Every allocation's token and bytes stay; no pointer local's slot is
        // observable.
        assert_eq!(
            composition.facts().len(),
            2 * (size + 1) + 3,
            "{composition:?}"
        );
        assert_eq!(after.resources().facts().len(), 3 * (size + 1) + 3);
        samples.push((size, work));
    }
    assert_constant_plus_log_growth("a view-lending call and its observation", &samples, 4.0);
}

/// Decided-arm read authority selects its definition by name and evaluates
/// only that body's cells, even with unrelated definitions and caller owners.
#[test]
fn matched_input_argument_views_ignore_unrelated_definitions_and_owners() {
    use crate::kernel::{
        AlgebraicSchemas, AlgebraicTerm, AlgebraicTermNode, AlgebraicType, AlgebraicValue,
        AlgebraicValueType, AlgebraicVariantType, ResourceMatchArm, ResourceMatchBody,
    };
    use std::sync::Arc;

    let _session = crate::kernel::VerificationSession::enter();
    let variants: Arc<[AlgebraicVariantType]> = vec![AlgebraicVariantType {
        name: "Held".into(),
        fields: vec![],
    }]
    .into();
    let ty = AlgebraicType {
        rigid: false,
        name: "ArgumentModel".into(),
        arguments: vec![],
        variants: variants.clone(),
        schemas: Arc::new(AlgebraicSchemas::new(std::collections::BTreeMap::from([(
            AlgebraicValueType::Algebraic {
                name: "ArgumentModel".into(),
                arguments: vec![],
            },
            variants,
        )]))),
    };
    let model = AlgebraicTerm {
        algebraic_type: ty.clone(),
        node: AlgebraicTermNode::Constructor {
            variant: "Held".into(),
            fields: vec![],
        },
    };
    let schema = ResourceFieldSchema::new(vec![(
        "model".into(),
        ResourceFieldType::Algebraic(ty.clone()),
    )])
    .unwrap();
    let target = ResourceInstance::new(
        Variable(TARGET_HEAP),
        "zz_target".into(),
        vec![].into(),
        schema.clone(),
        vec![AlgebraicValue::Algebraic(model)].into(),
    )
    .unwrap();
    let mut definition =
        CompositeResourceDefinition::new("zz_target", vec![], None, false, vec![], vec![])
            .with_instance_schema(Some(schema));
    definition.matched = Some(ResourceMatchBody {
        field_index: 0,
        algebraic_type: ty,
        arms: vec![ResourceMatchArm {
            variant: "Held".into(),
            bindings: vec![],
            binding_types: vec![],
            binding_variables: vec![],
            contains: vec![ResourceSpec::owned_memory(MemorySegment::new(
                ProgramExpression::Value(ProgramValue::pointer(heap_base(TARGET_HEAP))),
                crate::kernel::program_expression::int32_literal(0),
                crate::kernel::program_expression::int32_literal(2),
            ))],
            facts: vec![],
            children: vec![],
        }],
    });
    let mut samples = Vec::new();
    for size in [4usize, 16, 64, 256] {
        let mut definitions = (0..size)
            .map(|index| {
                CompositeResourceDefinition::new(
                    format!("a{index:04}"),
                    vec![],
                    None,
                    false,
                    vec![],
                    vec![],
                )
            })
            .collect::<Vec<_>>();
        definitions.push(definition.clone());
        let state = ExecutionState::new().with_resource_context(
            ResourceContext::new().unchecked_with_facts(
                (0..size).map(|index| owned_range(heap_base(index as u64 + 1), 0, 1)),
            ),
        );
        let (views, work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::kernel::functions::instance_arm_read_authority(
                &target,
                &definitions,
                &state,
                &PureFactContext::new(),
            )
        });
        assert_eq!(views.len(), 1);
        assert_eq!(
            views[0],
            ResourceFact::view_memory(MemoryRange::new(
                heap_base(TARGET_HEAP),
                MachineTerm::constant(0),
                MachineTerm::constant(2),
            )),
        );
        samples.push((size, work));
    }
    assert_constant_plus_log_growth("matched input argument views", &samples, 4.0);
}

/// A wide range of 8-byte structs and the byte block of the same bytes stand
/// for each other once `n * 8` is decided not to wrap
/// (`wide_memory_range_respelled` in `primitives/resource_algebra.rs`). Taking
/// the struct range `p[0u64..n]` from the byte block `p[0u64..n * 8u64]` (a
/// call's or loop's entry), the byte block from the struct range (its exit, or
/// `free`), a field read through the struct range, and the refusal that names
/// the undecided product when `n` is unbounded, must each cost work that does
/// not grow with unrelated wide blocks and struct ranges at other bases, nor
/// with struct ranges at other addresses of the target's own block: the
/// re-spelling is a rewrite of the two ranges' endpoints, one decision per
/// symbolic endpoint, after the one indexed supplier is selected.
#[test]
fn respelling_a_wide_struct_range_is_logarithmic_in_unrelated_and_same_block_ranges() {
    let count = |identity: u64| MachineTerm::Variable(Variable((1 << 40) + identity));
    let bytes = |identity: u64| {
        MachineTerm::uint64_multiply(count(identity), MachineTerm::uint64_constant(8))
    };
    let zero = || MachineTerm::uint64_constant(0);
    let byte_block =
        |identity: u64| MemoryRange::new_wide(heap_base(identity), zero(), bytes(identity), 1);
    let struct_range =
        |identity: u64| MemoryRange::new_wide(heap_base(identity), zero(), count(identity), 8);
    // A struct range at a symbolic element of the target block.
    let same_block = |index: u64| {
        MemoryRange::new_wide(
            Pointer {
                block: PointerBlock::Heap(TARGET_HEAP),
                offset: PointerOffsetTerm::scaled_int64_node(
                    MachineTerm::Variable(Variable((1 << 41) + index)),
                    8,
                    true,
                ),
            },
            zero(),
            MachineTerm::uint64_constant(1),
            8,
        )
    };
    let index = MachineTerm::Variable(Variable(1 << 42));
    let bounded = PureFactContext::new()
        .assume_condition(
            ConditionTerm::uint64_less_equal(count(TARGET_HEAP), MachineTerm::uint64_constant(100)),
            true,
        )
        .assume_condition(
            ConditionTerm::uint64_less_than(index.clone(), count(TARGET_HEAP)),
            true,
        );
    let unbounded = PureFactContext::new();
    let frame = |size: usize, target: MemoryRange, assumptions: &PureFactContext| {
        let resources = ResourceContext::new_with_equalities(assumptions)
            .unchecked_with_facts((1..=size as u64).flat_map(|identity| {
                [
                    ResourceFact::own_memory(byte_block(identity)),
                    ResourceFact::own_memory(struct_range(TARGET_HEAP + identity)),
                    ResourceFact::own_memory(same_block(identity)),
                ]
            }))
            .unchecked_with_fact(ResourceFact::own_memory(target));
        resources.synchronize_memory_equalities(assumptions);
        resources
    };
    let field = Pointer {
        block: PointerBlock::Heap(TARGET_HEAP),
        offset: PointerOffsetTerm::Add(
            Box::new(PointerOffsetTerm::scaled_int64_node(
                MachineTerm::int64_multiply(index.clone(), MachineTerm::int64_constant(8)),
                1,
                false,
            )),
            Box::new(PointerOffsetTerm::Constant(4)),
        ),
    };
    let mut take = Vec::new();
    let mut give_back = Vec::new();
    let mut read = Vec::new();
    let mut refuse = Vec::new();
    for size in [4, 8, 16] {
        let _session = crate::kernel::VerificationSession::enter();
        let blocks = frame(size, byte_block(TARGET_HEAP), &bounded);
        let structs = frame(size, struct_range(TARGET_HEAP), &bounded);
        let (taken, work) = crate::instrumentation::measure_deterministic_work(|| {
            blocks.clone().without_fact_incrementally(
                &ResourceFact::own_memory(struct_range(TARGET_HEAP)),
                &bounded,
            )
        });
        assert!(
            taken.is_some(),
            "the struct range is taken from the byte block"
        );
        take.push((size, work));
        let (returned, work) = crate::instrumentation::measure_deterministic_work(|| {
            structs.clone().without_fact_incrementally(
                &ResourceFact::own_memory(byte_block(TARGET_HEAP)),
                &bounded,
            )
        });
        assert!(
            returned.is_some(),
            "the byte block is taken from the struct range"
        );
        give_back.push((size, work));
        let (permitted, work) = crate::instrumentation::measure_deterministic_work(|| {
            structs.permits_memory_read(&field, 4, &bounded)
        });
        assert!(permitted, "a field is read through the struct range");
        read.push((size, work));
        let blocks = frame(size, byte_block(TARGET_HEAP), &unbounded);
        let (refused, work) = crate::instrumentation::measure_deterministic_work(|| {
            let required = ResourceFact::own_memory(struct_range(TARGET_HEAP));
            (
                blocks
                    .clone()
                    .without_fact_incrementally(&required, &unbounded),
                blocks.wide_range_respelling_refusal(&struct_range(TARGET_HEAP), &unbounded),
            )
        });
        assert!(refused.0.is_none(), "an unbounded count may wrap");
        assert!(refused.1.is_some(), "the refusal names the product");
        refuse.push((size, work));
    }
    assert_constant_plus_log_growth("taking a struct range from a byte block", &take, 16.0);
    assert_constant_plus_log_growth("taking a byte block from a struct range", &give_back, 16.0);
    assert_constant_plus_log_growth("a field read through a struct range", &read, 16.0);
    assert_constant_plus_log_growth("refusing an unbounded struct range", &refuse, 16.0);
}
