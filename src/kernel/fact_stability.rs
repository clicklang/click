//! A check that lowering is fact-stable.
//!
//! Facts may decide whether lowering succeeds, discharge its obligations,
//! and add side facts, but they never change the term it produces: when
//! lowering succeeds under facts and under no facts, the two terms are the
//! same up to the names of bound variables (`docs/internals/spellability.md`).
//! A lowering that rewrites through a fact, such as `f(a)` to `g(b)` because
//! `f(a) == g(b)` is known, yields a term no other context lowers to, so the
//! fact holding it cannot be spelled.
//!
//! Setting `CLICK_FACT_STABILITY=<path>` lowers every checked proof
//! proposition a second time with the same policy and no facts, and appends
//! one line per lowering whose fact-free term differs. The check only
//! observes; the lowering's own result is unchanged.

#[cfg(test)]
use crate::kernel::{CompareRelation, MachineIntegerType};
use std::io::Write;

use super::Proposition;

thread_local! {
    /// Set while the fact-free lowering runs, so it is not checked in turn.
    static SHADOWING: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

#[cfg(test)]
thread_local! {
    static CAPTURE: std::cell::RefCell<Option<Vec<String>>> = const { std::cell::RefCell::new(None) };
}

/// Runs `run` with the check recording to memory, and returns its lines.
#[cfg(test)]
pub(crate) fn capture(run: impl FnOnce()) -> Vec<String> {
    CAPTURE.with(|lines| lines.replace(Some(Vec::new())));
    run();
    CAPTURE.with(|lines| lines.take()).unwrap_or_default()
}

pub(crate) fn enabled() -> bool {
    if SHADOWING.with(std::cell::Cell::get) {
        return false;
    }
    #[cfg(test)]
    if CAPTURE.with(|lines| lines.borrow().is_some()) {
        return true;
    }
    crate::instrumentation::fact_stability_sink().is_some()
}

/// The outcome of the fact-free lowering beside the lowering under facts.
pub(crate) enum FactFree {
    /// It produced this one term.
    Term(Proposition),
    /// It produced this many paths, not one: under facts, the facts chose.
    Paths(usize),
    /// It was refused, which facts are allowed to decide.
    Refused,
}

/// Runs `lower` as the fact-free lowering.
pub(crate) fn shadow<T>(lower: impl FnOnce() -> T) -> T {
    struct Restore;
    impl Drop for Restore {
        fn drop(&mut self) {
            SHADOWING.with(|flag| flag.set(false));
        }
    }
    SHADOWING.with(|flag| flag.set(true));
    let _restore = Restore;
    crate::instrumentation::without_charging(lower)
}

/// Records `site` when its lowering under facts differs from its fact-free
/// lowering.
pub(crate) fn compare(site: &str, with_facts: &Proposition, fact_free: &FactFree) {
    let line = match fact_free {
        FactFree::Term(term)
            if crate::kernel::api::contract_certification::propositions_alpha_equivalent(
                with_facts, term,
            ) =>
        {
            return;
        }
        FactFree::Refused => return,
        FactFree::Term(term) => format!(
            "differs\t{site}\t{}\t{}\t{}\n",
            bounded(with_facts),
            bounded(term),
            thread_name()
        ),
        FactFree::Paths(count) => format!(
            "paths:{count}\t{site}\t{}\t\t{}\n",
            bounded(with_facts),
            thread_name()
        ),
    };
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
    if let Some(sink) = crate::instrumentation::fact_stability_sink()
        && let Ok(mut file) = sink.lock()
    {
        let _ = file.write_all(line.as_bytes());
    }
}

/// The running thread's name, which names the mdtest fixture under
/// `scripts/fact-stability.sh`.
fn thread_name() -> String {
    std::thread::current().name().unwrap_or("").to_string()
}

fn bounded(proposition: &Proposition) -> String {
    format!("{proposition:?}")
        .chars()
        .filter(|c| *c != '\n' && *c != '\t')
        .take(4000)
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::{Bitvector32Term, ConditionTerm, Variable};

    #[test]
    fn a_proposition_lowered_without_consulting_facts_is_stable() {
        let c = "int32 id(int32 x) { return x; }";
        let click = r#"verifying "f.c";

int32 id(int32 x) {
    requires 0 <= x and x <= 10;
    ensures result == x;
} by {
    have x <= 10;
    execute();
    simp();
}
"#;
        let lines = capture(|| {
            crate::surface::verify_c0_sources(click, &[("f.c", c)]).unwrap();
        });
        assert!(lines.is_empty(), "{lines:#?}");
    }

    #[test]
    fn a_term_that_differs_from_its_fact_free_lowering_is_reported() {
        let decided = Proposition::ConditionIs(ConditionTerm::Constant(true), true);
        let written = Proposition::ConditionIs(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: Box::new(Bitvector32Term::Variable(Variable(7))),
                right: Box::new(Bitvector32Term::Constant(0)),
            },
            true,
        );
        let lines = capture(|| {
            compare("site", &decided, &FactFree::Term(written.clone()));
            compare("site", &written, &FactFree::Term(written.clone()));
            compare("site", &written, &FactFree::Refused);
            compare("site", &written, &FactFree::Paths(2));
        });
        assert_eq!(lines.len(), 2, "{lines:#?}");
        assert!(lines[0].starts_with("differs\tsite\t"), "{lines:#?}");
        assert!(lines[1].starts_with("paths:2\tsite\t"), "{lines:#?}");
    }
}
