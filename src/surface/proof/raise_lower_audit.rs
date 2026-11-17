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
        Proposition::ConditionIs(
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
