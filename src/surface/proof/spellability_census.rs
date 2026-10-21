//! A measurement of the facts Click cannot spell.
//!
//! Every fact a proof state holds, and every goal it focuses, must have a
//! Click spelling that lowers back to it: expansion writes the proof out as
//! steps a person could have written, so whatever those steps cite or prove
//! must be writable (`docs/internals/spellability.md`). Setting
//! `CLICK_SPELLABILITY_CENSUS=<path>` appends one line per fact a checked
//! step adds, and per goal it leaves focused, saying whether the premise
//! speller found a spelling. `scripts/spellability-census.sh` runs the
//! corpus under it and summarizes the misses by kind.
//!
//! The census only observes: it never changes a proof, and without the
//! variable it costs one cached check per step.

use std::fs::File;
use std::io::Write;
use std::sync::{Mutex, OnceLock};

use crate::kernel::{ConditionTerm, Proposition, Term};

fn sink() -> Option<&'static Mutex<File>> {
    static SINK: OnceLock<Option<Mutex<File>>> = OnceLock::new();
    SINK.get_or_init(|| {
        let path = std::env::var_os("CLICK_SPELLABILITY_CENSUS")?;
        File::options()
            .create(true)
            .append(true)
            .open(path)
            .ok()
            .map(Mutex::new)
    })
    .as_ref()
}

pub(super) fn enabled() -> bool {
    sink().is_some()
}

/// What a censused proposition is, by its outermost kernel form. A quantifier
/// or implication is classified by the atom it finally concludes, since that
/// is what decides whether a spelling exists.
pub(super) fn kind(proposition: &Proposition) -> String {
    match proposition {
        Proposition::ForAll { body, .. } => format!("forall/{}", kind(body)),
        Proposition::Exists { body, .. } => format!("exists/{}", kind(body)),
        Proposition::Implies(_, body) => format!("implies/{}", kind(body)),
        Proposition::And(left, _) => format!("and/{}", kind(left)),
        Proposition::Or(left, _) => format!("or/{}", kind(left)),
        Proposition::Not(body) => format!("not/{}", kind(body)),
        Proposition::Equal(left, _) => format!(
            "equal:{}",
            match left {
                Term::Bitvector32(_) => "bitvector",
                Term::Integer(_) => "integer",
                Term::Algebraic(_) => "algebraic",
                Term::Sequence(_) => "sequence",
                Term::CValue(_) => "c-value",
                Term::PointerOffset(_) => "pointer-offset",
                Term::CMemory(_) => "memory",
                Term::CState(_) => "state",
                _ => "outcome",
            }
        ),
        Proposition::ConditionIs(condition, _) => {
            format!("condition:{}", condition_kind(condition))
        }
        Proposition::Predicate { name, .. } if name.starts_with("__click") => {
            "predicate:internal".into()
        }
        Proposition::Predicate { .. } => "predicate".into(),
        other => {
            let debug = format!("{other:?}");
            debug
                .split(|c: char| !c.is_alphanumeric())
                .next()
                .unwrap_or("other")
                .to_owned()
        }
    }
}

fn condition_kind(condition: &ConditionTerm) -> String {
    let debug = format!("{condition:?}");
    debug
        .split(|c: char| !c.is_alphanumeric())
        .next()
        .unwrap_or("condition")
        .to_owned()
}

/// Appends one census line: `spelled|unspelled`, the role (`fact` or
/// `goal`), the kind, the claim, the tactic, the origin (`written` for a step
/// a person wrote, `smart` for one a smart tactic's search took, which matters
/// only if that search succeeds), and the diagnostic rendering.
pub(super) fn record(spelled: bool, role: &str, kind: &str, claim: &str, tactic: &str, text: &str) {
    let Some(sink) = sink() else {
        return;
    };
    let text: String = text
        .chars()
        .map(|c| if c == '\n' || c == '\t' { ' ' } else { c })
        .take(300)
        .collect();
    let origin = if crate::instrumentation::smart_tactic_active() {
        "smart"
    } else {
        "written"
    };
    let line = format!(
        "{}\t{role}\t{kind}\t{claim}\t{tactic}\t{origin}\t{text}\n",
        if spelled { "spelled" } else { "unspelled" }
    );
    if let Ok(mut file) = sink.lock() {
        let _ = file.write_all(line.as_bytes());
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::{Bitvector32Term, Sort, Variable};

    #[test]
    fn a_censused_fact_is_classified_by_the_atom_it_concludes() {
        let atom = Proposition::ConditionIs(
            ConditionTerm::Bitvector32Equal(
                Box::new(Bitvector32Term::Variable(Variable(1))),
                Box::new(Bitvector32Term::Constant(0)),
            ),
            true,
        );
        let guarded = Proposition::ForAll {
            var: Variable(1),
            sort: Sort::CInt32,
            body: Box::new(Proposition::Implies(
                Box::new(atom.clone()),
                Box::new(atom.clone()),
            )),
            name: Default::default(),
        };
        assert_eq!(kind(&atom), "condition:Bitvector32Equal");
        assert_eq!(kind(&guarded), "forall/implies/condition:Bitvector32Equal");
        assert_eq!(
            kind(&Proposition::Predicate {
                name: "__click_internal".into(),
                arguments: Vec::new(),
            }),
            "predicate:internal"
        );
    }
}
