//! Resource policy, independent of artifact correctness and C++ semantics.
//!
//! Check serialized nesting before deserialization or recursive semantic walks.
//! This scanner does not establish JSON validity; serde still checks the grammar.

use super::CppExport;

pub(super) const MAX_RECORDS: usize = 256;
pub(super) const MAX_CONSTANTS: usize = 1024;
pub(super) const MAX_FUNCTIONS: usize = 1024;
pub(super) const MAX_CALL_DEPTH: usize = 64;
const MAX_JSON_CONTAINERS: usize = 65_536;
const MAX_JSON_NESTING: usize = 96;

pub(super) fn limit(name: &str, observed: usize, maximum: usize) -> Result<(), String> {
    if observed > maximum {
        Err(format!(
            "C++ artifact budget exhausted: {name} ({observed} > {maximum})"
        ))
    } else {
        Ok(())
    }
}

pub(super) fn check_inventories(export: &CppExport) -> Result<(), String> {
    limit("record declarations", export.records.len(), MAX_RECORDS)?;
    limit(
        "constant declarations",
        export.constants.len(),
        MAX_CONSTANTS,
    )?;
    limit(
        "function declarations",
        export.reachable_functions.len() + 1,
        MAX_FUNCTIONS,
    )
}

pub(super) fn check_serialized(bytes: &[u8]) -> Result<(), String> {
    let mut quoted = false;
    let mut escaped = false;
    let mut nesting = 0usize;
    let mut containers = 0usize;
    crate::instrumentation::record_deterministic_work(bytes.len());
    for &byte in bytes {
        if quoted {
            if escaped {
                escaped = false;
            } else if byte == b'\\' {
                escaped = true;
            } else if byte == b'"' {
                quoted = false;
            }
        } else {
            match byte {
                b'"' => quoted = true,
                b'{' | b'[' => {
                    nesting += 1;
                    containers += 1;
                    limit("serialized nesting", nesting, MAX_JSON_NESTING)?;
                    limit("serialized containers", containers, MAX_JSON_CONTAINERS)?;
                }
                b'}' | b']' => nesting = nesting.saturating_sub(1),
                _ => {}
            }
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn serialized_budget_counts_containers_without_interpreting_strings() {
        let escaped = serde_json::to_vec(&"[{}]\\\"[{}]").unwrap();
        check_serialized(&escaped).unwrap();
        let nesting = vec![b'['; MAX_JSON_NESTING + 1];
        assert!(
            check_serialized(&nesting)
                .unwrap_err()
                .contains("serialized nesting")
        );
        let containers = "[],".repeat(MAX_JSON_CONTAINERS + 1);
        assert!(
            check_serialized(containers.as_bytes())
                .unwrap_err()
                .contains("serialized containers")
        );
        // Budget checks do not turn malformed input into an accepted artifact.
        check_serialized(b"{]").unwrap();
        assert!(serde_json::from_slice::<CppExport>(b"{]").is_err());
    }

    #[test]
    fn serialized_budget_work_is_linear_in_input_bytes() {
        for size in [8, 32, 128, 512] {
            let input = format!("[{}]", "{},".repeat(size));
            let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                check_serialized(input.as_bytes())
            });
            result.unwrap();
            assert_eq!(work, input.len());
        }
    }

    #[test]
    fn named_inventory_budgets_accept_the_boundary_and_reject_the_next_entry() {
        for (name, maximum) in [
            ("record declarations", MAX_RECORDS),
            ("constant declarations", MAX_CONSTANTS),
            ("function declarations", MAX_FUNCTIONS),
        ] {
            limit(name, maximum, maximum).unwrap();
            assert!(
                limit(name, maximum + 1, maximum)
                    .unwrap_err()
                    .contains(name)
            );
        }
    }
}
