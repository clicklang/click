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

#[cfg(test)]
use crate::kernel::{CompareRelation, MachineIntegerType};
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

#[cfg(test)]
thread_local! {
    /// The lines a test is capturing, in place of the file sink.
    static CAPTURE: std::cell::RefCell<Option<Vec<String>>> = const { std::cell::RefCell::new(None) };
}

/// Runs `run` with the census recording to memory, and returns its lines.
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
    // A machine comparison or overflow test names its format and relation.
    if let Some((op, _, _)) = condition.as_bitvector_comparison() {
        let kind = if op.is_overflow() {
            "Overflows"
        } else {
            "Compare"
        };
        return format!("{kind}({} {})", op.format().name(), op.c_symbol());
    }
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
    if !enabled() {
        return;
    }
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
    use crate::kernel::{Bitvector32Term, Sort, Variable};

    #[test]
    fn hidden_child_fields_have_structural_resource_spellings() {
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
            let error = crate::surface::verify_c0_sources(
                fixture.click_source.as_deref().unwrap(),
                &sources,
            )
            .unwrap_err();
            assert!(
                error.to_string().contains("`ensures result >= 1` failed"),
                "{error}"
            );
        });
        let fields = lines
            .iter()
            .filter(|line| {
                let parts = line.split('\t').collect::<Vec<_>>();
                parts.get(1) == Some(&"fact")
                    && parts.get(2) == Some(&"condition:Compare(int32 ==)")
                    && parts.get(4) == Some(&"unfold")
            })
            .collect::<Vec<_>>();
        assert!(!fields.is_empty(), "{lines:#?}");
        let rewrites = lines
            .iter()
            .filter(|line| {
                let parts = line.split('\t').collect::<Vec<_>>();
                parts.get(1) == Some(&"goal")
                    && parts.get(4) == Some(&"rewrite")
                    && parts.get(5) == Some(&"smart")
            })
            .collect::<Vec<_>>();
        assert!(!rewrites.is_empty(), "{lines:#?}");
        assert!(
            rewrites.iter().all(|line| line.starts_with("spelled\t")),
            "{rewrites:#?}"
        );
        assert!(
            fields.iter().all(|line| line.starts_with("spelled\t")),
            "{fields:#?}"
        );
    }

    #[test]
    fn a_joined_read_definition_keeps_a_spellable_memory_version() {
        let fixture =
            include_str!("../../../mdtests/a_join_forgets_a_cell_the_arms_disagree_on.md");
        let c = fixture
            .split("```c filename=")
            .nth(1)
            .unwrap()
            .split_once('\n')
            .unwrap()
            .1
            .split("```")
            .next()
            .unwrap();
        let click = fixture
            .split("```click\n")
            .nth(1)
            .unwrap()
            .split("```")
            .next()
            .unwrap();
        let lines = capture(|| {
            let error = crate::surface::verify_c0_sources(
                click,
                &[("a_join_forgets_a_cell_the_arms_disagree_on.c", c)],
            )
            .unwrap_err();
            assert!(
                error.to_string().contains("`ensures result == 0` failed"),
                "{error}"
            );
        });
        let reads = lines
            .iter()
            .filter(|line| {
                let fields = line.split('\t').collect::<Vec<_>>();
                fields.get(1) == Some(&"fact")
                    && fields.get(2) == Some(&"condition:Compare(int32 ==)")
                    && fields.get(4) == Some(&"step")
            })
            .collect::<Vec<_>>();
        assert!(!reads.is_empty(), "{lines:#?}");
        assert!(
            reads.iter().all(|line| line.starts_with("spelled\t")),
            "{reads:#?}"
        );
    }

    #[test]
    fn algebraic_match_arm_values_name_unfold_facts() {
        let source = r#"
verifying "keep.c";
function is_cons(xs: List<int32>) -> Bool {
    match xs { List::Nil => false, List::Cons(value, tail) => true, }
}
resource modeled(p: int32*) { field items: List<int32>; owns *p; }
void keep(int32* p) {
    owns before: modeled(p);
} by {
    match before.items {
        List::Nil => { step_until(function.exit); solve(); },
        List::Cons(value, tail_items) => {
            unfold(is_cons(List::Cons(value, tail_items)));
            step_until(function.exit);
            solve();
        },
    }
}
"#;
        let lines = capture(|| {
            crate::surface::verify_c0_sources(source, &[("keep.c", "void keep(int32 *p) {}")])
                .unwrap();
        });
        let facts = lines
            .iter()
            .filter(|line| {
                let fields = line.split('\t').collect::<Vec<_>>();
                fields.get(1) == Some(&"fact")
                    && fields.get(2) == Some(&"condition:BoolApplication")
            })
            .collect::<Vec<_>>();
        assert!(!facts.is_empty(), "{lines:#?}");
        assert!(
            facts.iter().all(|line| line.starts_with("spelled\t")),
            "{facts:#?}"
        );
    }

    fn check_algebraic_condition_fixture(fixture: &str) {
        let source = fixture
            .split("```click\n")
            .nth(1)
            .unwrap()
            .split("```")
            .next()
            .unwrap();
        let lines = capture(|| {
            crate::surface::verify_click_theorems(source).unwrap();
        });
        let equalities = lines
            .iter()
            .filter(|line| line.split('\t').nth(2) == Some("condition:BoolEqual"))
            .collect::<Vec<_>>();
        assert!(!equalities.is_empty(), "{lines:#?}");
        assert!(
            equalities.iter().all(|line| line.starts_with("spelled\t")),
            "{equalities:#?}"
        );
    }

    #[test]
    fn nested_algebraic_conditions_in_list_facts_are_spelled() {
        check_algebraic_condition_fixture(include_str!(
            "../../../mdtests/stdlib_list_compositionality.md"
        ));
    }

    #[test]
    fn rigid_algebraic_conditions_in_list_facts_are_spelled() {
        check_algebraic_condition_fixture(include_str!(
            "../../../mdtests/algebraic_parametric_theorems.md"
        ));
    }

    #[test]
    fn generic_list_calls_keep_exact_spellings_after_unfold_and_intro() {
        for fixture in [
            include_str!("../../../mdtests/constructor_type_arguments_are_inferred.md"),
            include_str!(
                "../../../mdtests/a_proof_binder_has_its_type_for_constructor_inference.md"
            ),
        ] {
            let source = fixture
                .split("```click\n")
                .nth(1)
                .unwrap()
                .split("```")
                .next()
                .unwrap();
            let lines = capture(|| {
                crate::surface::verify_click_theorems(source).unwrap();
            });
            let facts = lines
                .iter()
                .filter(|line| line.split('\t').nth(1) == Some("fact"))
                .collect::<Vec<_>>();
            assert!(!facts.is_empty());
            assert!(
                facts.iter().all(|line| line.starts_with("spelled\t")),
                "{facts:#?}"
            );
        }
    }

    #[test]
    fn generic_list_proof_expands_and_rechecks_without_implicit_search() {
        let source = r#"
import click::list;
theorem only_element(v: int32, x: int32) {
    requires list::contains(List<int32>::Cons(v, List<int32>::Nil), x);
    ensures v == x;
}
"#;
        let expanded = crate::surface::expansion::expand_c0_claim_source_by_label(
            source,
            &[],
            "only_element.ensures_0",
        )
        .unwrap();
        crate::surface::proof::without_implicit_auto(|| {
            crate::surface::verify_click_theorems(&expanded).unwrap();
        });
    }

    #[test]
    fn boolean_function_unfold_facts_and_goals_have_exact_spellings() {
        let fixture = include_str!("../../../mdtests/a_bool_pure_function_states_a_claim.md");
        let source = fixture
            .split("```click\n")
            .nth(1)
            .unwrap()
            .split("```")
            .next()
            .unwrap();
        let lines = capture(|| {
            crate::surface::verify_click_theorems(source).unwrap();
        });
        let bool_lines = lines
            .iter()
            .filter(|line| {
                line.split('\t')
                    .nth(2)
                    .is_some_and(|kind| kind.contains("Bool"))
            })
            .collect::<Vec<_>>();
        assert!(!bool_lines.is_empty(), "{lines:#?}");
        assert!(
            bool_lines.iter().all(|line| line.starts_with("spelled\t")),
            "{bool_lines:#?}"
        );
    }

    #[test]
    fn boolean_function_proof_expands_and_rechecks_without_implicit_search() {
        let fixture = include_str!("../../../mdtests/a_bool_pure_function_states_a_claim.md");
        let source = fixture
            .split("```click\n")
            .nth(1)
            .unwrap()
            .split("```")
            .next()
            .unwrap();
        let expanded = crate::surface::expansion::expand_c0_claim_source_by_label(
            source,
            &[],
            "chosen_positive.ensures_0",
        )
        .unwrap();
        crate::surface::proof::without_implicit_auto(|| {
            crate::surface::verify_click_theorems(&expanded).unwrap();
        });
    }

    #[test]
    fn introduced_narrow_binder_bounds_have_checked_spellings() {
        for ty in ["int8", "uint8", "int16", "uint16"] {
            let source = format!(
                r#"
                theorem bounded() {{
                    ensures forall (x: {ty}) {{ x == x }} by {{
                        intro() as value;
                        normalize();
                    }}
                }}
            "#
            );
            let lines = capture(|| {
                crate::surface::proof::without_implicit_auto(|| {
                    crate::surface::verify_click_theorems(&source).unwrap();
                });
            });
            // An 8- or 16-bit binder is a value of its own format, so its
            // range is the format's and intro states no bound fact; what the
            // census records is spelled.
            let facts = lines
                .iter()
                .filter(|line| line.split('\t').nth(1) == Some("fact"))
                .collect::<Vec<_>>();
            assert!(facts.is_empty(), "{ty}: {facts:#?}");
            assert!(!lines.is_empty(), "{ty}");
            assert!(
                lines.iter().all(|line| line.starts_with("spelled\t")),
                "{ty}: {lines:#?}"
            );
        }
    }

    #[test]
    fn an_obligation_probe_does_not_duplicate_the_unfold_census() {
        let source = r#"
            predicate positive(x: int32) { x > 0 }
            theorem from_positive(x: int32) {
                requires positive(x);
                ensures x > 0 by { unfold(positive); assumption(); }
            }
        "#;
        let checked = capture(|| {
            crate::surface::proof::without_implicit_auto(|| {
                crate::surface::verify_click_theorems(source).unwrap();
            });
        });
        let probed = capture(|| {
            crate::surface::verify_click_theorems(source).unwrap();
        });
        assert!(
            checked
                .iter()
                .any(|line| line.split('\t').nth(4) == Some("unfold"))
        );
        assert_eq!(probed, checked, "probing is not another accepted operation");
    }

    /// After `a[i] = 5`, `a[i]` names the read at the store's version, so a
    /// rewrite that moves `a[j]` to `a[i]` leaves the goal `a[i] == 5`: the
    /// rewritten read is named as writing `a[i]` names it, not folded to the
    /// stored `5` (which would leave `true`, a goal no longer about `a`).
    #[test]
    fn a_rewrite_to_a_stored_cell_keeps_the_read_in_the_goal() {
        let c = "void set(int32* a, int32 i, int32 j) { a[i] = 5; }";
        let click = r#"verifying "set.c";
void set(int32* a, int32 i, int32 j) {
    requires 0 <= i and i < 4;
    requires i == j;
    owns a[0..4];
    ensures a[j] == 5;
} by {
    step_until(function.exit);
    rewrite(j == i);
}
"#;
        let lines = capture(|| {
            crate::surface::verify_c0_sources(click, &[("set.c", c)]).unwrap();
        });
        let rewritten = lines
            .iter()
            .filter(|line| {
                let fields = line.split('\t').collect::<Vec<_>>();
                fields.get(1) == Some(&"goal") && fields.get(4) == Some(&"rewrite")
            })
            .collect::<Vec<_>>();
        assert!(!rewritten.is_empty(), "{lines:#?}");
        assert!(
            rewritten
                .iter()
                .all(|line| line.starts_with("spelled\t")
                    && line.trim_end().ends_with("\ta[i] == 5")),
            "{rewritten:#?}"
        );
    }

    #[test]
    fn facts_an_unfold_adds_at_the_execution_frontier_are_spelled() {
        let c = "struct cell { int32 value; int32 other; };\n\
                 void bump(struct cell* p) { int32 seen = p->other; p->value = seen; }";
        let click = r#"resource flat(p: struct cell*) {
    owns p->value;
    owns p->other;
}

verifying "f.c";

void bump(struct cell* p) {
    owns flat(p);
} by {
    step();
    unfold(flat(p));
    step_until(function.exit);
    fold(flat(p));
    solve();
}
"#;
        let lines = capture(|| {
            crate::surface::verify_c0_sources(click, &[("f.c", c)]).unwrap();
        });
        let unfold_facts = lines
            .iter()
            .filter(|line| {
                let fields = line.split('\t').collect::<Vec<_>>();
                fields.get(1) == Some(&"fact") && fields.get(4) == Some(&"unfold")
            })
            .collect::<Vec<_>>();
        assert!(!unfold_facts.is_empty(), "{lines:#?}");
        assert!(
            unfold_facts
                .iter()
                .all(|line| line.starts_with("spelled\t")),
            "{unfold_facts:#?}"
        );
    }

    #[test]
    fn an_unfold_fact_over_a_match_arm_binder_is_spelled_through_it() {
        let c = "struct node { uint64 tag; };\n\
                 void pack(struct node *p, struct node *id) { p->tag = 7; }";
        let click = r#"verifying "f.c";
spec enum Identity { At(struct node*) }
resource modeled(p: struct node*) {
    field model: Identity;
    match model { Identity::At(id) => { owns p->tag; fact p == id; }, }
}
resource tag_at(p: struct node*) { owns p->tag; }
void pack(struct node* p, struct node* id) {
    consumes before: modeled(p);
    ensures 1 == 1;
} by {
    match before.model { Identity::At(model_id) => {
        unfold(before);
        fold(tag_at(model_id));
        unfold(tag_at(model_id));
        step();
        fold(tag_at(model_id));
        step_until(function.exit); solve();
    }, }
}
"#;
        let lines = capture(|| {
            crate::surface::verify_c0_sources(click, &[("f.c", c)]).unwrap();
        });
        // The arm binder `model_id` names the only spelling of this range.
        let binder_fact = lines
            .iter()
            .find(|line| line.ends_with("\tviewable((model_id as (uint8 *))[0..8])\n"))
            .unwrap_or_else(|| panic!("{lines:#?}"));
        assert!(binder_fact.starts_with("spelled\t"), "{binder_fact}");
    }

    #[test]
    fn a_rewritten_goal_with_no_written_template_is_spelled() {
        // `unfold(Adds)` opens a contract's obligation, which no written
        // proposition spells; the goals the rewrites inside `solve` leave are
        // spelled from the kernel goal instead.
        let c = "int32 add3(int32 x) { return x + 3; }";
        let click = r#"verifying "f.c";

contract int32 Adds(int32 x) {
    let amount: int32;
    requires 0 <= x and x <= 1000;
    requires 0 <= amount and amount <= 1000;
    ensures result == x + amount;
}

int32 add3(int32 x) {
    requires 0 <= x and x <= 1000;
    ensures result == x + 3;
}

theorem add3_adds_four() {
    ensures Adds(&add3, { amount: 4 }) by {
        unfold(Adds);
        solve();
    }
}
"#;
        let lines = capture(|| {
            let _ = crate::surface::verify_c0_sources(click, &[("f.c", c)]);
        });
        let rewritten_goals = lines
            .iter()
            .filter(|line| {
                let fields = line.split('\t').collect::<Vec<_>>();
                fields.get(1) == Some(&"goal") && fields.get(4) == Some(&"rewrite")
            })
            .collect::<Vec<_>>();
        assert!(!rewritten_goals.is_empty(), "{lines:#?}");
        assert!(
            rewritten_goals
                .iter()
                .all(|line| line.starts_with("spelled\t")),
            "{rewritten_goals:#?}"
        );
    }

    #[test]
    fn a_censused_fact_is_classified_by_the_atom_it_concludes() {
        let atom = Proposition::ConditionIs(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: Box::new(Bitvector32Term::Variable(Variable(1))),
                right: Box::new(Bitvector32Term::Constant(0)),
            },
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
        assert_eq!(kind(&atom), "condition:Compare(int32 ==)");
        assert_eq!(kind(&guarded), "forall/implies/condition:Compare(int32 ==)");
        assert_eq!(
            kind(&Proposition::Predicate {
                name: "__click_internal".into(),
                arguments: Vec::new(),
            }),
            "predicate:internal"
        );
    }
}
