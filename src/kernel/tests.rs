// The proposition search these tests exercise is Surface planning now; see
// `src/surface/planning/proposition_search.rs`. The kernel itself never
// calls it, so the tests import the planner explicitly.
use super::prelude::*;
use crate::surface::planning::proposition_search::PropositionSearch;
mod byte_view_tests;
mod callback_signature_tests;
mod one_byte_one_name_tests;

fn checked_memory_load_equality(
    left: &CMemory,
    right: &CMemory,
    pointer: &Pointer,
    assumptions: &PureFactContext,
) -> bool {
    checked_atomic_load_equality(
        &Bitvector32Term::MemoryLoad(
            intern_c_memory_ref(left),
            Box::new(pointer.clone()),
            crate::kernel::LoadKind::Int32,
        ),
        &Bitvector32Term::MemoryLoad(
            intern_c_memory_ref(right),
            Box::new(pointer.clone()),
            crate::kernel::LoadKind::Int32,
        ),
        assumptions,
    )
}

/// Instantiate the explicit elements law and discharge its written premise.
pub(in crate::kernel) fn explicit_signed_elements(
    base: Pointer,
    ty: CType,
    i: Bitvector32Term,
    j: Bitvector32Term,
    facts: PureFactContext,
) -> PureFactContext {
    let law = crate::kernel::prove_separation_elements(
        CPointerValue::new(base, ty.pointer_to().unwrap()),
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
    before: &CMemory,
    after: &CMemory,
    address: &Pointer,
    ty: CType,
    effects: &[Proposition],
    facts: &PureFactContext,
) -> Option<(CValue, CValue, Proposition)> {
    use crate::kernel::eval::typed_reads::ReadScope;
    use crate::kernel::proof::transport_certificate::{TransportCertificate, TransportNode};
    let entry = CState::new().with_memory(before.clone());
    let exit = entry.clone().with_memory(after.clone());
    let effects = effects
        .iter()
        .cloned()
        .map(ExecutionPureFact::certified)
        .collect::<Vec<_>>();
    let footprint = CResource::Footprint(crate::kernel::RegionFootprint::transition(
        "selected transition".into(),
        &entry,
        &exit,
        &effects,
    ));
    let kept = CResource::Memory(CMemoryRange::new_with_element_width(
        address.clone(),
        0u32.into(),
        1u32.into(),
        ty.byte_width(),
    ));
    // Establish each explicitly selected member's separation, then apply the
    // footprint rule to those facts, as normalize(using: [...]) does.
    let CResource::Footprint(region) = &footprint else {
        unreachable!()
    };
    let mut selected = PureFactContext::new();
    for member in &region.members {
        let member = crate::kernel::region_footprint::byte_resource(member)?;
        let kept = crate::kernel::region_footprint::byte_resource(&kept)?;
        if !facts.proves_resource_separate(&member, &kept) {
            return None;
        }
        selected = selected.assume_proposition(Proposition::CResourceSeparate {
            left: Box::new(member),
            right: Box::new(kept),
        });
    }
    if !crate::kernel::region_footprint::separate_using(&footprint, &kept, &selected) {
        return None;
    }
    let separation = Proposition::CResourceSeparate {
        left: Box::new(footprint),
        right: Box::new(kept),
    };
    let _reads = ReadScope::enter();
    let observe = |memory: &CMemory| {
        let paths = crate::kernel::eval::evaluate_logical_memory_load_paths(
            memory,
            address.clone(),
            ty,
            Default::default(),
            Vec::new(),
            &PureFactContext::new(),
        );
        let [path] = paths.as_slice() else {
            panic!("one logical observation");
        };
        let CExpressionOutcome::Value(value) = &path.outcome else {
            panic!("logical read produces a value");
        };
        value.clone()
    };
    let old = observe(before);
    let new = observe(after);
    let condition = match (new.numeric_value(), old.numeric_value()) {
        (CValue::Parameter(a), CValue::Parameter(b)) => {
            ConditionTerm::AlgebraicEqual(a.clone(), b.clone())
        }
        (CValue::Pointer(a), CValue::Pointer(b)) => {
            ConditionTerm::pointer_value_equal(a.clone(), b.clone())
        }
        (CValue::Int32(a), CValue::Int32(b)) | (CValue::UInt8(a), CValue::UInt8(b)) => {
            ConditionTerm::equal(a.clone(), b.clone())
        }
        (CValue::UInt64(a), CValue::UInt64(b)) => ConditionTerm::uint64_equal(a.clone(), b.clone()),
        other => panic!("unsupported test observation: {other:?}"),
    };
    let result = Proposition::ConditionIs(condition, true);
    let certificate = TransportCertificate {
        nodes: vec![
            TransportNode::Premise {
                proposition: separation.clone(),
                result: separation.clone(),
            },
            TransportNode::Preserve {
                field: None,
                effect: None,
                separation: 0,
                result,
            },
        ],
        conclusion: 1,
    };
    Some((
        old,
        new,
        certificate
            .apply(|p| p == &separation)
            .expect("explicit frame certificate"),
    ))
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

/// Certifies a contract from the kernel's own checked executions of the
/// function, one per resource-guard case, the way the surface certifies a
/// proof's artifacts: certification itself never executes a body.
/// The supplied state and arguments come from the test, not Surface entry
/// lowering. This helper does not establish that they represent the complete
/// input domain needed when packaging a reusable function rule.
fn certify_contract_with_kernel_artifacts(
    state: CState,
    function: CFunction,
    arguments: Vec<CExpression>,
    derived_entry_facts: Vec<Proposition>,
    environment: CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
    mode: CFunctionContractExecutionMode,
) -> CFunctionContractExecution {
    let assume_all = |facts: &[Proposition]| {
        facts
            .iter()
            .fold(PureFactContext::new(), |assumptions, fact| {
                assumptions.assume_proposition(fact.clone())
            })
    };
    let cases = crate::kernel::api::contract_certification::contract_resource_condition_cases(
        &state,
        &function,
        &arguments,
        &assume_all(&derived_entry_facts),
    )
    .unwrap_or_else(|| vec![Vec::new()]);
    let artifacts = cases
        .iter()
        .map(|case_facts| {
            let mut facts = derived_entry_facts.clone();
            facts.extend(case_facts.iter().cloned());
            prove_checked_c_function_execution_with_environment(
                state.clone(),
                function.clone(),
                arguments.clone(),
                assume_all(&facts),
                environment.clone(),
                execution_semantics,
                mode,
            )
        })
        .collect::<Vec<_>>();
    prove_c_function_contract_execution_paths_with_checked_artifacts(
        state,
        function,
        arguments,
        environment,
        execution_semantics,
        mode,
        &artifacts,
    )
}

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
    base: Pointer,
    start: impl Into<Bitvector32Term>,
    end: impl Into<Bitvector32Term>,
) -> CMemoryRange {
    CMemoryRange::new(base, start.into(), end.into())
}

fn view_memory_fact(
    base: Pointer,
    start: impl Into<Bitvector32Term>,
    end: impl Into<Bitvector32Term>,
) -> CResourceFact {
    CResourceFact::view_memory(memory_range(base, start, end))
}

fn own_memory_fact(
    base: Pointer,
    start: impl Into<Bitvector32Term>,
    end: impl Into<Bitvector32Term>,
) -> CResourceFact {
    CResourceFact::own_memory(memory_range(base, start, end))
}

fn view_memory_context(
    base: Pointer,
    start: impl Into<Bitvector32Term>,
    end: impl Into<Bitvector32Term>,
) -> ResourceContext {
    ResourceContext::new().unchecked_with_fact(view_memory_fact(base, start, end))
}

fn own_memory_context(
    base: Pointer,
    start: impl Into<Bitvector32Term>,
    end: impl Into<Bitvector32Term>,
) -> ResourceContext {
    ResourceContext::new().unchecked_with_fact(own_memory_fact(base, start, end))
}

fn assert_checkable_derivation(assumptions: &PureFactContext, proposition: &Proposition) {
    let derivation = assumptions
        .derive_proposition(proposition)
        .expect("expected an explicit proposition derivation");
    assert_eq!(derivation.conclusion(), proposition);
    assert!(
        derivation.check(assumptions),
        "explicit proposition derivation must check"
    );
}

fn arc_pointer(offset: i64) -> Pointer {
    Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::Constant(offset),
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

mod heap_tests;
mod loan_model_tests;
