//! Explicit representation laws. Each application names one word and four
//! character reads in the same state; no memory-history search is involved.
use super::prelude::*;

pub(crate) fn prove_uint32_from_le_bytes(pointer: CPointerValue) -> Result<Theorem, String> {
    if pointer.c_type().pointee_type() != Some(CType::UInt32) {
        return Err("uint32_from_le_bytes requires a uint32 pointer".into());
    }
    let state = CState::new();
    let base = SpecExpression::Value(CValue::Pointer(pointer.clone()));
    let view = SpecProposition::MemoryLoadable {
        memory: SpecMemory::Current,
        base: base.clone(),
        start: SpecExpression::Value(CValue::Int32(0u32.into())),
        end: SpecExpression::Value(CValue::Int32(1u32.into())),
        element_width: 4,
    };
    let endian = Proposition::Predicate {
        name: LITTLE_ENDIAN_PREDICATE_NAME.into(),
        arguments: vec![],
    };
    let assumptions = PureFactContext::new().allow_symbolic_contract_loads();
    let (view, _, _) =
        super::api::c_lower_spec_proposition_at_state(&state, &view, Some(&state), &assumptions)?;
    let mut premises = vec![endian, view];
    let assumptions = premises
        .iter()
        .fold(assumptions, |facts, p| facts.assume_proposition(p.clone()));
    let word = SpecExpression::MemoryLoad {
        memory: SpecMemory::Current,
        pointer: Box::new(base.clone()),
        value_type: CType::UInt32,
    };
    let (defined, _, _) = super::api::c_lower_spec_proposition_at_state(
        &state,
        &SpecProposition::Defined(word.clone()),
        Some(&state),
        &assumptions,
    )?;
    premises.push(defined.clone());
    for guard in super::stated_loadable_extent_guards(&premises[1]) {
        if !premises.contains(&guard) {
            premises.push(guard);
        }
    }
    let assumptions = assumptions.assume_proposition(defined);
    let bytes = SpecExpression::Cast(Box::new(base), CType::UInt8Pointer);
    let byte = |index: u32| {
        crate::instrumentation::record_deterministic_work(1);
        SpecExpression::Cast(
            Box::new(SpecExpression::MemoryLoad {
                memory: SpecMemory::Current,
                pointer: Box::new(SpecExpression::PointerOffset {
                    pointer: Box::new(bytes.clone()),
                    elements: Box::new(SpecExpression::Value(CValue::Int32(index.into()))),
                    byte_width: 1,
                }),
                value_type: CType::UInt8,
            }),
            CType::UInt32,
        )
    };
    let mut packed = byte(0);
    for index in 1..4 {
        packed = SpecExpression::BitwiseOr(
            Box::new(packed),
            Box::new(SpecExpression::ShiftLeft(
                Box::new(byte(index)),
                Box::new(SpecExpression::Value(CValue::UInt32((index * 8).into()))),
            )),
        );
    }
    let conclusion = SpecProposition::Comparison {
        left: word,
        operator: CComparisonOperator::Equal,
        right: packed,
    };
    let (conclusion, _, _) = super::api::c_lower_spec_proposition_at_state(
        &state,
        &conclusion,
        Some(&state),
        &assumptions,
    )?;
    Ok(Theorem::new(
        premises
            .into_iter()
            .rev()
            .fold(conclusion, |body, premise| {
                Proposition::Implies(Box::new(premise), Box::new(body))
            }),
    ))
}

#[cfg(test)]
mod scaling_tests {
    include!("../scaling_tests/kernel/byte_representation_laws.rs");
}
