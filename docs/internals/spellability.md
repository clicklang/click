# Spellability

Every fact a proof state holds, and every goal it focuses, has a Click
spelling: Surface Click source that a person could write in a proof and that
lowers back to that exact fact. This is a design rule, not a presentation
goal.

## Why the rule exists

`click expand` replaces each smart step with the simple steps a person could
have written ([Expansion](../concepts/expansion.md)), and the [slow-part
rule](verifier-design.md#the-slow-part-rule) admits a search only when its
result can be written out that way. A simple step names what it cites and what
it proves: a `have`, a `using { ... }` premise, a witness, an `instantiate`
argument. So every fact a smart step relies on, and every goal it leaves, must
be writable, or the smart step cannot be expanded.

When a fact has no spelling, today's code works around it rather than failing:

- a smart tactic declines a route whose premise it cannot cite, even though
  the kernel holds the premise (`simp`, the solver bridges, the implicit
  `auto`), so a provable goal fails as a bounded miss;
- a recorded spelling that does not check is dropped, so later steps cannot
  cite the fact;
- a diagnostic prints a placeholder (`<unnamed A>`, `<pointer A>`,
  `<state A>`) or an angle-bracket description in place of the fact;
- expansion refuses its own output when a placeholder leaks into it.

None of these is unsound, since every cited spelling is lowered again and
checked. Each one costs completeness, expansion, or a readable report.

## The rule

- **Spell by construction, not by search.** A fact's spelling follows from
  the fact and the names in scope. Code must not search a list of strategies
  for a spelling and fall back to a placeholder, to another renderer, to
  `None`, or to dropping the fact.
- **Name a value where it is introduced.** A step that introduces a fresh
  value or memory state (a call result, a havoc, an allocation, a state
  between recorded points) gives it a name from its provenance at that
  point. Do not recover a name later from whatever locals happen to hold the
  value.
- **Every fact kind has syntax.** A kernel fact that a proof state can hold
  has a Surface form. Adding a kernel fact or term form includes adding its
  Surface form and its spelling, in the same change.
- **A spelling lowers back to its fact.** The spelling of a fact, lowered in
  the same context, is that fact.

A fact that exists only inside one kernel step, and never becomes a proof
state's fact or goal, needs no spelling.

## When a fact has no spelling

Report it as a tooling defect (the `inexpressible-fact` outcome in
[tracing](../concepts/tracing.md)), and fix it by naming the value at its
introduction or by adding the Surface form. Do not add a fallback, a
placeholder, a skipped candidate, or a declining route to work around it.

## Measuring the gap

`scripts/spellability-census.sh` runs the mdtest corpus with
`CLICK_SPELLABILITY_CENSUS` set (`src/surface/proof/spellability_census.rs`).
Each checked step records, for every fact it adds and for the goal it leaves
focused, whether the premise speller finds a checked spelling. The script
prints the misses grouped by kind. It separates steps a person wrote from
steps a smart tactic's search took: a search step needs a spelling only when
its search succeeds and is expanded, but a written step's facts and goal may
be cited by the next written step. The census only observes; it does not
change any proof.

The census sorts a miss into one of four gaps, each with its own fix:

- **Writable but not found.** The fact has Click syntax and its operands
  have names, but the premise speller's search misses it: reflexive pointer
  equalities such as `p == p`, `viewable(p[0..1])` after an `unfold`, an
  applied theorem's conclusion such as `cd(n - 1) == 0`, and goals with no
  recorded presentation. The fix is the total speller.
- **A value with no name.** The fact mentions a value or address nothing
  names, printed `<unnamed A>` or `<pointer A>`: a callee's result, a havoc,
  an allocation. The fix is naming at introduction.
- **No syntax.** The fact's kind has no Surface form: resources held together,
  writability, the memory a step may change.
- **Internal predicates.** `__click_` predicates, such as subobject coverage
  and volatile events, that a proof state holds as facts. Each either gets a
  Surface form or stops being a proof-state fact. `held`, `same_object`, and
  contract facts are not internal: the kernel names them under `__click_`, and
  `kernel::predicate_source_name` gives the Click name that lowers to each.
  The printer, synthesis, and the internal-premise filter all read that one
  mapping.
