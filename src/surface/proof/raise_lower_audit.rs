//! A check that lowering undoes raising.
//!
//! Every kernel term a proof state holds must satisfy `lower(raise(x)) == x`
//! (`docs/internals/raise-lower-principle.md#the-raise-lower-principle`). Setting
//! `CLICK_RAISE_LOWER=<path>` raises each fact a checked step adds, and the
//! goal it leaves focused, with the canonical raiser goal presentation uses
//! (`Proof::structural_proposition_candidate`: the step's fixed state, its
//! entry state and the path's recorded points). It lowers
//! that Surface form again in the same proof and appends one line saying how the
//! round trip ended. `scripts/raise-lower.sh` runs the corpus under it.
//!
//! This checks the canonical Surface form. The raise-lower census separately
//! measures facts that cannot be raised; a mismatch here is a raised form
//! that lowers to a different term.
//!
//! The audit only observes: it charges no budget, records no search note,
//! and does not change the proof or its report.

#[cfg(test)]
use crate::kernel::Proposition;
use std::fs::File;
use std::io::Write;
use std::sync::{Mutex, OnceLock};

fn sink() -> Option<&'static Mutex<File>> {
    static SINK: OnceLock<Option<Mutex<File>>> = OnceLock::new();
    SINK.get_or_init(|| {
        let path = std::env::var_os("CLICK_RAISE_LOWER")?;
        File::options()
            .create(true)
            .append(true)
            .open(path)
            .ok()
            .map(Mutex::new)
    })
    .as_ref()
}

#[cfg(test)]
thread_local! {
    /// The lines a test is capturing, in place of the file sink.
    static CAPTURE: std::cell::RefCell<Option<Vec<String>>> = const { std::cell::RefCell::new(None) };
}

/// Runs `run` with the audit recording to memory, and returns its lines.
#[cfg(test)]
pub(crate) fn capture(run: impl FnOnce()) -> Vec<String> {
    CAPTURE.with(|lines| lines.replace(Some(Vec::new())));
    run();
    CAPTURE.with(|lines| lines.take()).unwrap_or_default()
}

pub(super) fn enabled() -> bool {
    #[cfg(test)]
    if CAPTURE.with(|lines| lines.borrow().is_some()) {
        return true;
    }
    sink().is_some()
}

/// How one round trip ended.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum RoundTrip {
    /// The raised form lowered back to the same term, up to bound names.
    Same,
    /// It lowered to the same comparison stated with the other polarity,
    /// such as `a < b` held false for `a >= b`: a normalization, not the
    /// same term.
    Polarity,
    /// It lowered to a different term.
    Differs,
    /// The raised form did not lower.
    Unlowered,
    /// The raiser produced no Surface form.
    Unraised,
    /// The proof state has no fixed state to raise at (a pure theorem).
    NoState,
}

impl RoundTrip {
    fn tag(self) -> &'static str {
        match self {
            Self::Same => "same",
            Self::Polarity => "polarity",
            Self::Differs => "differs",
            Self::Unlowered => "unlowered",
            Self::Unraised => "unraised",
            Self::NoState => "no-state",
        }
    }
}

/// Classifies the lowering of a raised form against the original term.
pub(super) fn classify(
    original: &crate::kernel::Proposition,
    lowered: &crate::kernel::Proposition,
) -> RoundTrip {
    if crate::kernel::fact_stability::same_up_to_binders(original, lowered) {
        RoundTrip::Same
    } else if super::condition_polarity_equivalent(lowered, original) {
        RoundTrip::Polarity
    } else {
        RoundTrip::Differs
    }
}

/// Appends one audit line: the outcome, the role (`fact` or `goal`), the
/// census kind, the claim, the tactic, the origin (`written` or `smart`),
/// the original term's diagnostic rendering, the raised form, and for
/// `differs` the lowered term's rendering.
#[allow(clippy::too_many_arguments)]
pub(super) fn record(
    outcome: RoundTrip,
    role: &str,
    kind: &str,
    claim: &str,
    tactic: &str,
    original: &str,
    raised: &str,
    lowered: &str,
) {
    if !enabled() {
        return;
    }
    let field = |text: &str| -> String {
        text.chars()
            .map(|c| if c == '\n' || c == '\t' { ' ' } else { c })
            .take(300)
            .collect()
    };
    let origin = if crate::instrumentation::smart_tactic_active() {
        "smart"
    } else {
        "written"
    };
    let line = format!(
        "{}\t{role}\t{kind}\t{claim}\t{tactic}\t{origin}\t{}\t{}\t{}\n",
        outcome.tag(),
        field(original),
        field(raised),
        field(lowered),
    );
    #[cfg(test)]
    if CAPTURE.with(|lines| {
        lines
            .borrow_mut()
            .as_mut()
            .map(|lines| lines.push(line.clone()))
            .is_some()
    }) {
        return;
    }
    if let Some(sink) = sink()
        && let Ok(mut file) = sink.lock()
    {
        let _ = file.write_all(line.as_bytes());
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::{
        CompareRelation, ConditionTerm, MachineIntegerType, MachineTerm, Variable,
    };

    fn compare(relation: CompareRelation, value: bool) -> Proposition {
        Proposition::condition_is(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation,
                left: Box::new(MachineTerm::Variable(Variable(7))),
                right: Box::new(MachineTerm::constant(10)),
            },
            value,
        )
    }

    #[test]
    fn a_round_trip_is_classified_by_the_term_it_lowers_to() {
        let less = compare(CompareRelation::LessThan, true);
        assert_eq!(classify(&less, &less), RoundTrip::Same);
        assert_eq!(
            classify(&less, &compare(CompareRelation::Equal, true)),
            RoundTrip::Differs
        );
    }

    /// A pointer a pure function returns raises as that call, and a read
    /// through it as a typed read through the call; a pointer argument of a
    /// Click call with no proof name raises as the pointer itself; and a
    /// constant byte span that is not a whole number of words raises over a
    /// byte view.
    #[test]
    fn pure_call_pointers_pointer_arguments_and_byte_spans_round_trip() {
        for (name, text, original) in [
            (
                "resource_child_pure_arguments.md",
                include_str!("../../../mdtests/resource_child_pure_arguments.md"),
                "model_pointer(Address::At(p)) == p",
            ),
            (
                "resource_child_pure_arguments_recursive.md",
                include_str!("../../../mdtests/resource_child_pure_arguments_recursive.md"),
                "old(*root_pointer(Tree::Leaf(left, 2))) == 2",
            ),
            (
                "const_pointer_parameter_fact_survives_a_step.md",
                include_str!("../../../mdtests/const_pointer_parameter_fact_survives_a_step.md"),
                "same(p, p) == 1",
            ),
            (
                "an_ordinary_exit_produces_a_composite_whose_body_facts_hold.md",
                include_str!(
                    "../../../mdtests/an_ordinary_exit_produces_a_composite_whose_body_facts_hold.md"
                ),
                "viewable(p[0..6])",
            ),
        ] {
            let lines = round_trips(name, text);
            assert!(
                lines.contains(&("same".to_string(), original.to_string())),
                "{name}: {original}: {lines:#?}"
            );
            assert!(
                !lines
                    .iter()
                    .any(|(outcome, line)| line == original && outcome != "same"),
                "{name}: {original}: {lines:#?}"
            );
        }
    }

    /// A read through a pointer a call returned raises as a read through
    /// that call's result, at the read's own state, whether at the result
    /// or displaced from it.
    #[test]
    fn reads_through_a_call_result_round_trip() {
        for (name, text, original) in [
            (
                "a_call_result_is_spelled_by_its_call.md",
                include_str!("../../../mdtests/a_call_result_is_spelled_by_its_call.md"),
                "old(*statement(0).call(make, 0).result) == 7",
            ),
            (
                "undeclared_aggregate_call_has_a_separate_copy.md",
                include_str!("../../../mdtests/undeclared_aggregate_call_has_a_separate_copy.md"),
                "old(*&statement(0).call(make_pair, 0).result[4]) == 4",
            ),
        ] {
            let lines = round_trips(name, text);
            assert!(
                lines.contains(&("same".to_string(), original.to_string())),
                "{name}: {original}: {lines:#?}"
            );
        }
    }

    /// A checked read of a caller's struct field the path leaves unchanged
    /// reads the cell at its function-entry version; it raises as the field
    /// read at entry.
    #[test]
    fn an_entry_version_field_read_round_trips() {
        let lines = round_trips(
            "arena_prefix_free_reads_region_arena.md",
            include_str!("../../../mdtests/arena_prefix_free_reads_region_arena.md"),
        );
        for original in ["old(region->start) == s", "old(region->end) == e"] {
            assert!(
                lines.contains(&("same".to_string(), original.to_string())),
                "{original}: {lines:#?}"
            );
        }
    }

    /// The round trips `fixture` records, as `(outcome, original)` pairs.
    fn round_trips(name: &str, text: &str) -> Vec<(String, String)> {
        let fixture = crate::cli::parse_mdtest(std::path::Path::new(name), text).unwrap();
        let sources = fixture
            .c_sources
            .iter()
            .map(|(name, source)| (name.as_str(), source.as_str()))
            .collect::<Vec<_>>();
        capture(|| {
            let _ = crate::surface::verify_c_sources(
                fixture.click_source.as_deref().unwrap(),
                &sources,
            );
        })
        .iter()
        .map(|line| {
            let fields = line.split('\t').collect::<Vec<_>>();
            (fields[0].to_string(), fields[6].to_string())
        })
        .collect()
    }

    /// A pointer a call returned raises as that call's result, and a read
    /// at an earlier point as `at(point, ..)`: the audit raises with the
    /// path's recorded points, as goal presentation does.
    #[test]
    fn call_result_pointers_and_earlier_reads_round_trip() {
        let lines = round_trips(
            "a_call_result_is_spelled_by_its_call.md",
            include_str!("../../../mdtests/a_call_result_is_spelled_by_its_call.md"),
        );
        for original in [
            "statement(0).call(make, 0).result == h[0]",
            "at(statement(0).exit, h[0]) == h[0]",
        ] {
            assert!(
                lines.contains(&("same".to_string(), original.to_string())),
                "{original}: {lines:#?}"
            );
        }
        let lines = round_trips(
            "a_guarded_memset_value_claim_crosses_a_disjoint_store.md",
            include_str!(
                "../../../mdtests/a_guarded_memset_value_claim_crosses_a_disjoint_store.md"
            ),
        );
        assert!(
            lines.contains(&("same".to_string(), "statement(0).result == dst".to_string())),
            "{lines:#?}"
        );
    }

    /// A 64-bit equality reads both words at its format, so a `uint64`
    /// call in it raises as the call, not cast to `int64`, which would lower
    /// to a different term.
    #[test]
    fn a_wide_call_result_equality_round_trips_without_a_cast() {
        let lines = round_trips(
            "a_wide_call_result_equality_raises_without_a_cast.md",
            include_str!("../../../mdtests/a_wide_call_result_equality_raises_without_a_cast.md"),
        );
        let fact = "statement(0).call(add, 0).result == click::integer::uint64_wrapping_add(a, b)";
        assert!(
            lines.contains(&("same".to_string(), fact.to_string())),
            "{lines:#?}"
        );
    }

    /// A read in a 64-bit equality raises as the read as written, not as a
    /// typed word read at the equality's signedness (`load<int64>(..)`),
    /// which lowers to a different read: `left()`'s result equals the
    /// counter it read after the call.
    #[test]
    fn a_wide_read_equality_round_trips_as_the_written_read() {
        let lines = round_trips(
            "private_state_mutation_reset.md",
            include_str!("../../../mdtests/private_state_mutation_reset.md"),
        );
        let fact = "statement(4).call(left, 0).result == at(<state A>, state[0])";
        assert!(
            lines
                .iter()
                .any(|(outcome, original)| outcome == "same" && original.starts_with(fact)),
            "{lines:#?}"
        );
    }

    /// A parameter named `result` raises as `program::result`, so a read
    /// through it lowers back to that parameter, not to the returned
    /// pointer that bare `result` names after the return.
    #[test]
    fn a_parameter_named_result_round_trips_as_program_result() {
        let lines = round_trips(
            "result_parameter_false_field_postcondition.md",
            include_str!("../../../mdtests/result_parameter_false_field_postcondition.md"),
        );
        assert!(!lines.is_empty());
        assert!(
            lines.iter().all(|(outcome, _)| outcome == "same"),
            "{lines:#?}"
        );
    }

    /// `rewrite` states its result in the one form for a comparison of
    /// exact observations: substituting into `to_integer(x) ==
    /// to_integer(y)` leaves `old(n[0]) == 0`, not `to_integer(old(n[0]))
    /// == 0`, which lowers to the native comparison and would not round-trip.
    #[test]
    fn rewritten_observation_comparisons_round_trip() {
        let fixture = crate::cli::parse_mdtest(
            std::path::Path::new("a_loop_condition_s_call_and_test_are_the_loop_s_own.md"),
            include_str!("../../../mdtests/a_loop_condition_s_call_and_test_are_the_loop_s_own.md"),
        )
        .unwrap();
        let sources = fixture
            .c_sources
            .iter()
            .map(|(name, source)| (name.as_str(), source.as_str()))
            .collect::<Vec<_>>();
        let lines = capture(|| {
            let _ = crate::surface::verify_c_sources(
                fixture.click_source.as_deref().unwrap(),
                &sources,
            );
        });
        let rewrites = lines
            .iter()
            .map(|line| line.split('\t').collect::<Vec<_>>())
            .filter(|fields| fields[4] == "rewrite")
            .collect::<Vec<_>>();
        assert!(!rewrites.is_empty());
        assert!(
            rewrites.iter().all(|fields| fields[0] == "same"),
            "{rewrites:#?}"
        );
    }

    /// An Integer comparison over a C conditional raises with machine
    /// operands, `(if old(n[0]) == 0 { 0 } else { 1 }) == 1`: lowering keeps
    /// that comparison Integer, as the fact is. Explicit `to_integer`
    /// observations would lower to the native comparison instead.
    #[test]
    fn an_integer_comparison_over_a_conditional_round_trips() {
        let lines = round_trips(
            "a_loop_condition_s_call_and_test_are_the_loop_s_own.md",
            include_str!("../../../mdtests/a_loop_condition_s_call_and_test_are_the_loop_s_own.md"),
        );
        let fact = "to_integer(if old(n[0]) == 0 { 0 } else { 1 }) == 1";
        assert!(
            lines.contains(&("same".to_string(), fact.to_string())),
            "{lines:#?}"
        );
        assert!(
            !lines.contains(&("differs".to_string(), fact.to_string())),
            "{lines:#?}"
        );
    }

    /// A goal naming an `intro` binder raises through that binder's name,
    /// as premise raising does: `0 <= k and k < 3` after `intro()`.
    #[test]
    fn an_intro_binder_goal_raises_with_its_binder_name() {
        let lines = round_trips(
            "copy3_array_demo.md",
            include_str!("../../../mdtests/copy3_array_demo.md"),
        );
        let goal = "0 <= k and k < 3";
        assert!(
            lines.contains(&("same".to_string(), goal.to_string())),
            "{lines:#?}"
        );
        assert!(
            !lines.contains(&("unraised".to_string(), goal.to_string())),
            "{lines:#?}"
        );
    }

    /// A resource fact over a declared composite raises as the composite's
    /// name applied to its arguments, a local's storage as `&pool`:
    /// `contains(slot(&pool, p), p[0])`.
    #[test]
    fn a_declared_composite_resource_fact_round_trips() {
        let lines = round_trips(
            "authority_wildcard_create_private_body.md",
            include_str!("../../../mdtests/authority_wildcard_create_private_body.md"),
        );
        let fact = "contains(slot(&pool, p), p[0])";
        assert!(
            lines.contains(&("same".to_string(), fact.to_string())),
            "{lines:#?}"
        );
    }

    #[test]
    fn a_checked_step_records_how_each_added_fact_round_trips() {
        let fixture = crate::cli::parse_mdtest(
            std::path::Path::new("a_hidden_record_is_shown_beside_its_resource.md"),
            include_str!("../../../mdtests/a_hidden_record_is_shown_beside_its_resource.md"),
        )
        .unwrap();
        let sources = fixture
            .c_sources
            .iter()
            .map(|(name, source)| (name.as_str(), source.as_str()))
            .collect::<Vec<_>>();
        let lines = capture(|| {
            let _ = crate::surface::verify_c_sources(
                fixture.click_source.as_deref().unwrap(),
                &sources,
            );
        });
        let unfold = |outcome: &str, original: &str| {
            lines.iter().any(|line| {
                let fields = line.split('\t').collect::<Vec<_>>();
                fields[0] == outcome
                    && fields[1] == "fact"
                    && fields[4] == "unfold"
                    && fields[6] == original
            })
        };
        // The unfolded viewability round-trips, and so does the hidden
        // record's value: raised with the entry state, it is
        // `old(pair(p).first.v)`.
        assert!(
            unfold("same", "viewable((p as (uint8 *))[0..8])"),
            "{lines:#?}"
        );
        assert!(unfold("same", "<unnamed A> >= 0"), "{lines:#?}");
    }
}
