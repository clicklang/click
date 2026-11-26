//! Quantifier binders as their own variables.
//!
//! A quantifier's bound variable is `Variable::bound(h)`, where `h` is the
//! quantifier's height: one more than the tallest quantifier in its body, so
//! an innermost quantifier has height 0. The height depends only on the
//! quantifier's own body, so it is unchanged when the quantifier is placed
//! under another one or when an enclosing quantifier is opened. Quantifiers
//! that enclose one another have different heights, so an occurrence of
//! `Bound(h)` names exactly one of them, and no producer of free variables
//! can mint a `Bound` identity.
//!
//! Closing builds a quantifier from a body over a free variable. Opening
//! (`intro`, `instantiate`, `choose`) replaces the binder by a free variable
//! or a term, with the substitution functions every other rewrite uses.

use super::*;

/// The height a quantifier over `body` takes: one more than the tallest
/// quantifier `body` contains, or 0 when it contains none. Quantifiers occur
/// only in a proposition's connective structure, and each records its own
/// height, so the walk stops at the outermost quantifiers below `body`'s root:
/// work is proportional to the connectives above them. An occurrence of a
/// variable, bound or free, does not count.
pub(crate) fn quantifier_height_over(body: &Proposition) -> u64 {
    let mut height = 0;
    let mut pending = vec![body];
    while let Some(proposition) = pending.pop() {
        match proposition {
            Proposition::And(left, right)
            | Proposition::Or(left, right)
            | Proposition::Implies(left, right) => {
                pending.push(left);
                pending.push(right);
            }
            Proposition::Not(inner) => pending.push(inner),
            Proposition::ForAll { var, .. } | Proposition::Exists { var, .. } => {
                height = height.max(var.height() + 1);
            }
            _ => {}
        }
    }
    height
}

/// `body` with the variable `from`, of `sort`, renamed to `to`. A machine
/// integer and a pointer variable are one program variable: a quantifier of
/// either sort binds its variable as a machine term and as a symbolic address
/// base, so both forms are renamed.
pub(crate) fn rename_quantified_variable(
    body: &Proposition,
    from: Variable,
    to: Variable,
    sort: &Sort,
) -> Option<Proposition> {
    // A rename changes no value, so it reduces nothing: a written `match` on
    // a known constructor stays as written.
    proof::term_rewrite::without_match_reduction(|| rename_unreduced(body, from, to, sort))
}

fn rename_unreduced(
    body: &Proposition,
    from: Variable,
    to: Variable,
    sort: &Sort,
) -> Option<Proposition> {
    let rename_program_occurrences = |body: &Proposition, pointer: Address| {
        let renamed =
            substitute_int32_variable_in_proposition(body, from, OldMachineTerm::Variable(to));
        let renamed =
            proof::restore_range_span_spelling(body, renamed, from, &OldMachineTerm::Variable(to));
        // What is left of `from` after the machine-term rename is an address
        // base, possibly behind a load variable; without one, the body is done.
        if !mentions_possibly(&renamed, from) {
            return Some(renamed);
        }
        // The rewrite walks every carrier, so an address based on `from`
        // inside a machine term (the pointer of a load) is renamed too.
        let mut rewrite = proof::term_rewrite::TermRewrite::for_pointer_variable(from, &pointer);
        // A load variable names a read whose address may be based on `from`.
        rewrite.enable_registered_load_resolution();
        let rewritten = rewrite.substitute_proposition(&renamed);
        if rewrite.refusal().is_some() {
            return None;
        }
        // The rewrite rebuilds what it walks; keep the input, with its shared
        // terms, when no address was based on `from`.
        Some(if rewritten == renamed {
            renamed
        } else {
            rewritten
        })
    };
    match sort {
        Sort::ProgramPointer(program_type) | Sort::ProgramObjectPointer(program_type, _) => {
            let pointer = if matches!(program_type, ProgramType::FunctionPointer(_)) {
                Address::symbolic_function(to)
            } else {
                Address::symbolic(to)
            };
            rename_program_occurrences(body, pointer)
        }
        // A rename cannot capture and changes no value, so it walks every
        // carrier, where the general Integer substitution refuses a
        // proposition holding a value it cannot rewrite, such as a machine
        // read, even when the variable does not occur in it. The rewrite
        // rebuilds what it walks through normalizing constructors, which would
        // reduce a written `match` on a known constructor, so a body in which
        // it replaced nothing is kept as written.
        Sort::Integer => {
            let integer = std::collections::BTreeMap::from([(from, IntegerTerm::var(to))]);
            typed_rename(body, &Default::default(), &integer, &Default::default())
        }
        Sort::Algebraic(algebraic_type) => {
            let algebraic = std::collections::BTreeMap::from([(
                from,
                AlgebraicTerm {
                    algebraic_type: algebraic_type.clone(),
                    node: AlgebraicTermNode::Variable(to),
                },
            )]);
            typed_rename(body, &Default::default(), &Default::default(), &algebraic)
        }
        _ => rename_program_occurrences(body, Address::symbolic(to)),
    }
}

/// The binder and body of a quantifier of `sort` over `body`, whose free
/// variable `free` becomes the binder.
pub(crate) fn close_quantifier(
    free: Variable,
    sort: &Sort,
    body: &Proposition,
) -> Option<(QuantifierBinder, Proposition)> {
    debug_assert!(!free.is_bound(), "a quantifier closes over a free variable");
    let binder = QuantifierBinder::of_height(quantifier_height_over(body));
    let body = rename_quantified_variable(body, free, *binder, sort)?;
    Some((binder, body))
}

/// `forall free: sort. body`, closed over `free`.
pub(crate) fn close_forall(
    name: BinderName,
    free: Variable,
    sort: Sort,
    body: &Proposition,
) -> Option<Proposition> {
    let (var, body) = close_quantifier(free, &sort, body)?;
    Some(Proposition::ForAll {
        var,
        sort,
        body: Box::new(body),
        name,
    })
}

/// `exists free: sort. body`, closed over `free`.
pub(crate) fn close_exists(
    name: String,
    free: Variable,
    sort: Sort,
    body: &Proposition,
) -> Option<Proposition> {
    let (var, body) = close_quantifier(free, &sort, body)?;
    Some(Proposition::Exists {
        name,
        var,
        sort,
        body: Box::new(body),
    })
}

/// Whether a quantifier keeping `binder` over `body` keeps its binders
/// distinct: every quantifier `body` contains is shorter than `binder`.
/// A rewrite that rebuilds a quantifier around a transformed body keeps its
/// binder; this is the condition that makes that valid.
pub(crate) fn binder_covers_body(binder: QuantifierBinder, body: &Proposition) -> bool {
    quantifier_height_over(body) <= binder.height()
}

impl QuantifierBinder {
    /// The binder a rewrite rebuilds a quantifier around, from the bound
    /// variable it read from that quantifier.
    pub(crate) fn retained(variable: Variable) -> Self {
        debug_assert!(variable.is_bound(), "a retained binder is a bound variable");
        Self::of_height(variable.0)
    }
}

/// `forall var: sort. body`: rebuilt around `var` when it is already the
/// bound variable of the quantifier `body` came from, or closed over `var`
/// when it is free.
pub(crate) fn forall_over(
    name: BinderName,
    var: Variable,
    sort: Sort,
    body: &Proposition,
) -> Option<Proposition> {
    if !var.is_bound() {
        return close_forall(name, var, sort, body);
    }
    let var = QuantifierBinder::retained(var);
    debug_assert!(binder_covers_body(var, body));
    Some(Proposition::ForAll {
        var,
        sort,
        body: Box::new(body.clone()),
        name,
    })
}

/// `exists var: sort. body`, as [`forall_over`] builds a universal.
pub(crate) fn exists_over(
    name: String,
    var: Variable,
    sort: Sort,
    body: &Proposition,
) -> Option<Proposition> {
    if !var.is_bound() {
        return close_exists(name, var, sort, body);
    }
    let var = QuantifierBinder::retained(var);
    debug_assert!(binder_covers_body(var, body));
    Some(Proposition::Exists {
        name,
        var,
        sort,
        body: Box::new(body.clone()),
    })
}

/// `proposition` with every quantifier at its own height, so two
/// propositions that differ only in their binders' heights are the same
/// value. A quantifier a rewrite rebuilt around a shortened body keeps a
/// taller binder than it needs; this gives it the height its body asks for.
/// The walk is bottom-up over the connectives and quantifiers: when an inner
/// quantifier takes its smaller height, every quantifier enclosing it still
/// has its taller one, so no occurrence is renamed into another binder. A
/// quantifier inside a term keeps its binder. Work is one rename per binder.
pub(crate) fn canonical_binders(proposition: &Proposition) -> Proposition {
    match proposition {
        Proposition::And(left, right) => Proposition::And(
            Box::new(canonical_binders(left)),
            Box::new(canonical_binders(right)),
        ),
        Proposition::Or(left, right) => Proposition::Or(
            Box::new(canonical_binders(left)),
            Box::new(canonical_binders(right)),
        ),
        Proposition::Implies(left, right) => Proposition::Implies(
            Box::new(canonical_binders(left)),
            Box::new(canonical_binders(right)),
        ),
        Proposition::Not(body) => Proposition::Not(Box::new(canonical_binders(body))),
        Proposition::ForAll {
            var,
            sort,
            body,
            name,
        } => {
            let (var, body) = canonical_quantifier(*var, sort, body);
            Proposition::ForAll {
                var,
                sort: sort.clone(),
                body: Box::new(body),
                name: name.clone(),
            }
        }
        Proposition::Exists {
            name,
            var,
            sort,
            body,
        } => {
            let (var, body) = canonical_quantifier(*var, sort, body);
            Proposition::Exists {
                name: name.clone(),
                var,
                sort: sort.clone(),
                body: Box::new(body),
            }
        }
        _ => proposition.clone(),
    }
}

fn canonical_quantifier(
    binder: QuantifierBinder,
    sort: &Sort,
    body: &Proposition,
) -> (QuantifierBinder, Proposition) {
    let body = canonical_binders(body);
    let canonical = QuantifierBinder::of_height(quantifier_height_over(&body));
    if canonical == binder {
        return (binder, body);
    }
    match rename_quantified_variable(&body, *binder, *canonical, sort) {
        Some(renamed) => (canonical, renamed),
        None => (binder, body),
    }
}

/// `forall var: sort. body` closed over `var`, for tests that build a
/// quantifier by hand.
#[cfg(test)]
pub(crate) fn test_forall(
    name: BinderName,
    var: Variable,
    sort: Sort,
    body: Proposition,
) -> Proposition {
    forall_over(name, var, sort, &body).expect("a test quantifier closes")
}

/// `exists var: sort. body` closed over `var`, for tests.
#[cfg(test)]
pub(crate) fn test_exists(
    name: String,
    var: Variable,
    sort: Sort,
    body: Proposition,
) -> Proposition {
    exists_over(name, var, sort, &body).expect("a test quantifier closes")
}

/// The binder of a quantifier whose body contains no quantifier, for a
/// producer that builds such a body over the binder directly instead of
/// closing one built over a free variable.
pub(crate) const fn innermost_binder() -> QuantifierBinder {
    QuantifierBinder::of_height(0)
}

/// A fresh free variable and `body` with the quantifier's bound variable
/// `binder` renamed to it: the body as a step that opens the quantifier sees
/// it. For planning code that compares a quantified goal's body with other
/// facts; the variable is fresh, so no fact already mentions it.
pub(crate) fn open_quantifier(
    binder: QuantifierBinder,
    sort: &Sort,
    body: &Proposition,
) -> Option<(Variable, Proposition)> {
    let witness = opening_witness()?;
    let opened = rename_quantified_variable(body, *binder, witness, sort)?;
    Some((witness, opened))
}

/// Whether `body` may mention `from`: it occurs among the body's variables,
/// address bases included, or the body holds a load variable, whose read
/// may.
fn mentions_possibly(body: &Proposition, from: Variable) -> bool {
    let mut variables = proposition_variables(body);
    reasoning::collect_proposition_capture_variables(body, &mut variables);
    // An unregistered load variable names no read, so it hides nothing.
    variables.contains(&from)
        || variables.iter().any(|variable| {
            is_load_variable(variable) && eval::registered_load_for_variable(variable).is_some()
        })
}

fn typed_rename(
    body: &Proposition,
    program: &std::collections::BTreeMap<
        Variable,
        proof::term_rewrite::TypedProgramValueReplacement,
    >,
    integer: &std::collections::BTreeMap<Variable, IntegerTerm>,
    algebraic: &std::collections::BTreeMap<Variable, AlgebraicTerm>,
) -> Option<Proposition> {
    let mut rewrite =
        proof::term_rewrite::TermRewrite::for_typed_variables(program, integer, algebraic);
    let renamed = rewrite.substitute_proposition(body);
    if rewrite.refusal().is_some() {
        return None;
    }
    Some(if rewrite.replaced_anything() {
        renamed
    } else {
        body.clone()
    })
}

/// `forall b1. forall b2. ... body`, closed over `binders` (outermost first)
/// in one pass over `body`. Closing them one at a time renames through the
/// body once per binder, quadratic in their number; here every binder is
/// renamed at once. A binder's height is fixed by its position: the
/// innermost is one taller than the tallest quantifier in `body`.
pub(crate) fn close_foralls(
    binders: &[(BinderName, Variable, Sort)],
    body: &Proposition,
) -> Option<Proposition> {
    let base = quantifier_height_over(body);
    let machine = |sort: &Sort| {
        matches!(
            sort,
            Sort::ProgramInt32 | Sort::Bitvector32 | Sort::ProgramInt64 | Sort::ProgramInteger(_)
        )
    };
    if binders.len() < 2 || !binders.iter().all(|(_, _, sort)| machine(sort)) {
        let mut proposition = body.clone();
        for (name, var, sort) in binders.iter().rev() {
            proposition = close_forall(name.clone(), *var, sort.clone(), &proposition)?;
        }
        return Some(proposition);
    }
    let count = binders.len() as u64;
    let heights = binders
        .iter()
        .enumerate()
        .map(|(position, (_, var, _))| (*var, base + count - 1 - position as u64))
        .collect::<Vec<_>>();
    let program = heights
        .iter()
        .map(|(var, height)| {
            (
                *var,
                proof::term_rewrite::TypedProgramValueReplacement::Bitvector(
                    OldMachineTerm::Variable(Variable::bound(*height)),
                ),
            )
        })
        .collect::<std::collections::BTreeMap<_, _>>();
    let renamed = proof::term_rewrite::without_match_reduction(|| {
        typed_rename(body, &program, &Default::default(), &Default::default())
    })?;
    let mut proposition = renamed;
    for ((name, _, sort), (_, height)) in binders.iter().zip(&heights).rev() {
        proposition = Proposition::ForAll {
            var: QuantifierBinder::of_height(*height),
            sort: sort.clone(),
            body: Box::new(proposition),
            name: name.clone(),
        };
    }
    Some(proposition)
}

thread_local! {
    /// How many witnesses this verification session has opened quantifiers
    /// at. A session numbers its own from zero, so the identities a proof
    /// opens with, and every order that follows from them, do not depend on
    /// what the thread verified before.
    static OPENING_WITNESSES: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
}

/// A free variable no other producer mints, for opening a quantifier where
/// no proof state reserves identities: a derivation, a planner's comparison,
/// a frame check. Numbered per verification session.
pub(crate) fn opening_witness() -> Option<Variable> {
    OPENING_WITNESSES.with(|count| {
        let next = count.get();
        count.set(next.checked_add(1)?);
        Some(Variable::opening(next))
    })
}

pub(crate) fn opening_witness_count() -> u64 {
    OPENING_WITNESSES.with(std::cell::Cell::get)
}

pub(crate) fn reset_opening_witnesses(count: u64) {
    OPENING_WITNESSES.with(|witnesses| witnesses.set(count));
}
