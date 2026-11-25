// These tests exercise discovery explicitly through kernel::search::ProofSearch.
use super::prelude::*;
mod byte_view_tests;
mod callback_signature_tests;
mod one_byte_one_name_tests;

fn checked_memory_load_equality(
    left: &SymbolicMemory,
    right: &SymbolicMemory,
    pointer: &Address,
    assumptions: &PureFactContext,
) -> bool {
    checked_atomic_load_equality(
        &OldMachineTerm::read_named(
            ProgramPoint::at(&(intern_memory_ref(left))),
            Box::new(pointer.clone()),
            crate::kernel::LoadKind::Int32,
        ),
        &OldMachineTerm::read_named(
            ProgramPoint::at(&(intern_memory_ref(right))),
            Box::new(pointer.clone()),
            crate::kernel::LoadKind::Int32,
        ),
        assumptions,
    )
}

/// Instantiate the explicit elements law and discharge its written premise.
pub(in crate::kernel) fn explicit_signed_elements(
    base: Address,
    ty: ProgramType,
    i: OldMachineTerm,
    j: OldMachineTerm,
    facts: PureFactContext,
) -> PureFactContext {
    let law = crate::kernel::prove_separation_elements(
        OldPointer::new(base, ty.pointer_to().unwrap()),
        ty.byte_width(),
        MachineIntegerType::Int32,
        i,
        j,
    );
    let Proposition::Implies(premise, conclusion) = law.proposition() else {
        panic!("elements law has one premise");
    };
    assert!(
        facts.proves_exact(premise),
        "elements requires unequal indices"
    );
    facts.assume_proposition(
        crate::kernel::region_footprint::byte_premise(conclusion)
            .expect("element separation has byte coordinates"),
    )
}

/// Apply the same explicit footprint-preservation primitive as a written
/// certificate. Tests supply the selected transition and prove its separation;
/// the logical read producers provide both observations without reconstruction.
pub(in crate::kernel) fn explicit_frame(
    before: &SymbolicMemory,
    after: &SymbolicMemory,
    address: &Address,
    ty: ProgramType,
    effects: &[Proposition],
    facts: &PureFactContext,
) -> Option<(ProgramValue, ProgramValue, Proposition)> {
    use crate::kernel::eval::typed_reads::ReadScope;
    let entry = ExecutionState::new().with_memory(before.clone());
    let exit = entry.clone().with_memory(after.clone());
    let effects = effects
        .iter()
        .cloned()
        .map(ExecutionPureFact::certified)
        .collect::<Vec<_>>();
    let footprint = Resource::Footprint(crate::kernel::RegionFootprint::transition(
        "selected transition".into(),
        &entry,
        &exit,
        &effects,
    ));
    let kept = Resource::Memory(MemoryRange::new_with_element_width(
        address.clone(),
        0u32.into(),
        1u32.into(),
        ty.byte_width(),
    ));
    // Establish each explicitly selected member's separation, then apply the
    // footprint rule to those facts, as normalize(using: [...]) does.
    let Resource::Footprint(region) = &footprint else {
        unreachable!()
    };
    let mut selected = PureFactContext::new();
    for member in &region.members {
        let member = crate::kernel::region_footprint::byte_resource(member)?;
        let kept = crate::kernel::region_footprint::byte_resource(&kept)?;
        if !facts.proves_resource_separate(&member, &kept) {
            return None;
        }
        selected = selected.assume_proposition(Proposition::ResourceSeparate {
            left: Box::new(member),
            right: Box::new(kept),
        });
    }
    if !crate::kernel::region_footprint::separate_using(&footprint, &kept, &selected) {
        return None;
    }
    let separation = Proposition::ResourceSeparate {
        left: Box::new(footprint),
        right: Box::new(kept),
    };
    let _reads = ReadScope::enter();
    let observe = |state: &ExecutionState| {
        let paths = crate::kernel::eval::evaluate_logical_memory_load_paths(
            state.memory(),
            address.clone(),
            ty,
            Default::default(),
            Vec::new(),
            &PureFactContext::new(),
        );
        let [path] = paths.as_slice() else {
            panic!("one logical observation");
        };
        let ExpressionOutcome::Value(value) = &path.outcome else {
            panic!("logical read produces a value");
        };
        crate::kernel::eval::typed_reads::record_at(&state.program_point(), address, value);
        value.clone()
    };
    let old = observe(&entry);
    let new = observe(&exit);
    let condition = match (new.numeric_value(), old.numeric_value()) {
        (ProgramValue::Parameter(a), ProgramValue::Parameter(b)) => {
            ConditionTerm::AlgebraicEqual(a.clone(), b.clone())
        }
        (ProgramValue::Pointer(a), ProgramValue::Pointer(b)) => {
            ConditionTerm::pointer_equal(a.clone(), b.clone())
        }
        (ProgramValue::Int32(a), ProgramValue::Int32(b)) => {
            ConditionTerm::equal(a.clone(), b.clone())
        }
        (ProgramValue::UInt8(a), ProgramValue::UInt8(b)) => ConditionTerm::machine_compare(
            MachineIntegerType::UInt8,
            CompareRelation::Equal,
            a.clone(),
            b.clone(),
        ),
        (ProgramValue::UInt64(a), ProgramValue::UInt64(b)) => {
            ConditionTerm::uint64_equal(a.clone(), b.clone())
        }
        other => panic!("unsupported test observation: {other:?}"),
    };
    let result = Proposition::condition_is(condition, true);
    crate::kernel::proof::preservation::apply(&separation, None, &result, |p| p == &separation)
        .expect("explicit preservation");
    Some((old, new, result))
}

mod canonicalization_tests;
mod contract_execution_tests;
mod execution_tests;
mod expression_tests;
mod memory_reasoning_tests;
mod proof_reasoning_tests;
mod representation_copy_tests;
mod resource_tests;
mod state_identity_tests;
mod thread_transition_tests;
mod wide_address_tests;
mod wide_comparison_tests;
mod wide_division_tests;
mod wide_multiply_tests;
mod wide_scalar_tests;
mod wide_storage_tests;

/// Contract certification calls no general prover: every proposition it
/// certifies is decided by an exact rule of its own, a completion match,
/// or a kind-specific bounded rule, never by handing the question to
/// `PureFactContext::proves`.
#[test]
fn contract_certification_calls_no_general_prover() {
    let needle = [".prov", "es("].concat();
    let sources = [
        "src/kernel/api/contract_certification.rs",
        "src/kernel/api/contract_certification/contract_claims.rs",
    ];
    let offenders = sources
        .iter()
        .filter(|relative| {
            let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join(relative);
            std::fs::read_to_string(path)
                .expect("certification source is readable")
                .contains(&needle)
        })
        .collect::<Vec<_>>();
    assert!(
        offenders.is_empty(),
        "contract certification hands a proposition to the general prover: {offenders:?}"
    );
}

/// Boundaries whose load equality is present in the recorded memory DAG must
/// not regain the ambient whole-context prover. Framed atomic transport still
/// uses that prover until its assumption-dependent hop has typed evidence.
#[test]
fn migrated_load_equality_consumers_use_recorded_dag_evidence() {
    let needle = ["c_memory_load", "_is_unchanged("].concat();
    let sources = [
        "src/kernel/api/contract_certification.rs",
        "src/kernel/api/contract_certification/contract_claims.rs",
        "src/kernel/loops.rs",
        "src/kernel/primitives/resource_algebra.rs",
        "src/kernel/proof/fact_reasoning.rs",
        "src/surface/proof.rs",
    ];
    let offenders = sources
        .iter()
        .filter(|relative| {
            let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join(relative);
            std::fs::read_to_string(path)
                .expect("load-equality consumer source is readable")
                .contains(&needle)
        })
        .collect::<Vec<_>>();
    assert!(
        offenders.is_empty(),
        "migrated load-equality consumer invokes the global prover: {offenders:?}"
    );
}

/// The kernel reads no environment variable: its behaviour is fixed, and
/// its test-only audits are switched on by the tests that run them. Every
/// A/B handle it once read kept a second code path alive.
#[test]
fn kernel_source_reads_no_environment_variable() {
    fn source_files(directory: &std::path::Path, files: &mut Vec<std::path::PathBuf>) {
        for entry in std::fs::read_dir(directory).expect("kernel source directory is readable") {
            let path = entry.expect("kernel source entry is readable").path();
            if path.is_dir() {
                source_files(&path, files);
            } else if path.extension().is_some_and(|extension| extension == "rs") {
                files.push(path);
            }
        }
    }
    let kernel = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("src/kernel");
    let mut files = Vec::new();
    source_files(&kernel, &mut files);
    assert!(files.len() > 20, "the kernel source tree was not found");
    let offenders = files
        .iter()
        .filter(|path| {
            let source = std::fs::read_to_string(path).expect("kernel source is readable");
            source.contains(&["env", "::var"].concat())
        })
        .map(|path| path.display().to_string())
        .collect::<Vec<_>>();
    assert!(
        offenders.is_empty(),
        "kernel sources read an environment variable: {offenders:?}"
    );
}

fn memory_range(
    base: Address,
    start: impl Into<OldMachineTerm>,
    end: impl Into<OldMachineTerm>,
) -> MemoryRange {
    MemoryRange::new(base, start.into(), end.into())
}

fn view_memory_fact(
    base: Address,
    start: impl Into<OldMachineTerm>,
    end: impl Into<OldMachineTerm>,
) -> ResourceFact {
    ResourceFact::view_memory(memory_range(base, start, end))
}

fn own_memory_fact(
    base: Address,
    start: impl Into<OldMachineTerm>,
    end: impl Into<OldMachineTerm>,
) -> ResourceFact {
    ResourceFact::own_memory(memory_range(base, start, end))
}

fn view_memory_context(
    base: Address,
    start: impl Into<OldMachineTerm>,
    end: impl Into<OldMachineTerm>,
) -> ResourceContext {
    ResourceContext::new().unchecked_with_fact(view_memory_fact(base, start, end))
}

fn own_memory_context(
    base: Address,
    start: impl Into<OldMachineTerm>,
    end: impl Into<OldMachineTerm>,
) -> ResourceContext {
    ResourceContext::new().unchecked_with_fact(own_memory_fact(base, start, end))
}

fn assert_checkable_derivation(assumptions: &PureFactContext, proposition: &Proposition) {
    let derivation =
        crate::kernel::search::ProofSearch::derive_proposition(assumptions, proposition)
            .expect("expected an explicit proposition derivation");
    assert_eq!(derivation.conclusion(), proposition);
    assert!(
        derivation.check(assumptions),
        "explicit proposition derivation must check"
    );
}

fn arc_pointer(offset: i64) -> Address {
    Address {
        base: "arg-memory".into(),
        offset: AddressOffset::Constant(offset),
    }
}

mod external_array_tests;
mod iterated_ownership_tests;
mod memory_dag_tests;
#[path = "../scaling_tests/kernel/tests/memory_scaling_tests.rs"]
mod memory_scaling_tests;
#[path = "../scaling_tests/kernel/tests/resource_scaling_tests.rs"]
mod resource_scaling_tests;
mod scalar_array_tests;

mod borrow_model_tests;
mod heap_tests;
mod object_cell_tests;
