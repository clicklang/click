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
  the kernel holds the premise (`simp`, its arithmetic bridges, the implicit
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
  Recorded points index each integer value, and each pointer's block, by the
  point and the local it was first given to (`RecordedSnapshots::value_points`
  and `pointer_points`, filled from the locals each recorded state changed),
  and the structural speller writes `at(point, ...)` from that index for a
  value no nearer state names. A load made in a memory no point records, as
  inside a call, is read at the nearest recorded memories after it.
- **Every fact kind has syntax.** A kernel fact that a proof state can hold
  has a Surface form. Adding a kernel fact or term form includes adding its
  Surface form and its spelling, in the same change.
- **A spelling lowers back to its fact.** The spelling of a fact, lowered in
  the same context, is that fact.
- **A refined goal keeps a spelling.** A step that refines a goal carries the
  goal's written spelling forward where it can, as `rewrite` rewrites it, and
  otherwise spells the new kernel goal (`Proof::spelled_goal`). A smart
  tactic's search skips this; expansion writes its steps out as written ones.

A fact that exists only inside one kernel step, and never becomes a proof
state's fact or goal, needs no spelling.

## Kernel authority

Some kernel propositions are checked context, not proof-state facts: a
resource composition (resources held together) and a predicate with no Click
name, such as subobject coverage or a volatile event. The kernel stores,
transports, and validates them with every other fact, so a step's delta still
justifies each one. No surface view presents or cites them: the census,
proof traces, diagnostics, and premise spelling all skip them, and a closing
step reads them from its context. One classification,
`Proposition::is_kernel_authority`, decides membership; code must not
special-case a composition or a `__click_` name elsewhere.

`held`, `same_object`, and contract facts are not authority even though the
kernel names them under `__click_`: `kernel::predicate_source_name` gives the
Click name that lowers to each, and the printer, synthesis, and authority
classification all read that one mapping.

Making a proposition kind authority is a design decision, never a way to
avoid spelling a fact a proof could need to cite.

## Lowering is fact-stable

Facts may decide whether lowering succeeds, discharge its obligations, and
add side facts beside its term. They never change the term: when a
proposition lowers both under facts and under no facts, the two terms are
the same up to the names of bound variables. A lowering that rewrites
through a fact, `f(a)` to `g(b)` because `f(a) == g(b)` is known, yields a
term that another context's lowering of the same text does not reach: `a ==
c` then no longer gives `f(a) == f(c)` by rewriting, and the fact holding
it has no spelling. Equalities belong to the equality graph, which every
check consults; they are not folded into terms.

The rule is about facts, not state. A term may depend on the program point,
the memory, and the resources held there; two contexts holding the same
resources under different facts must produce the same term. A memory read
is named by the address it was written with and the state of the cell or
resource it reads, so a write to a separately owned cell leaves it alone.
A read whose cell is found only through a fact, such as reading `a[k]`
while owning `a[i]`, which needs `k == i`, stays a read of the region's
state; the equality graph relates it to the stored value. Facts may still
prove the read is permitted. A fact an unfold adds is an ordinary fact.

`CLICK_FACT_STABILITY=<path>` lowers each checked proof proposition again
under the same policy with no facts (`kernel::fact_stability`) and records
every lowering whose term differs. `scripts/fact-stability.sh` runs the
mdtest corpus under it and groups the differences by where the two terms
first diverge. The corpus still has fact-dependent lowerings: comparisons
folded to constants, reads and pointer reads resolved through known values
or aliases, comparison kinds chosen by known provenance, and decided guards
and disjuncts dropped. Each is a defect to remove, by moving the equality
into the check that needs it.

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
change any proof. A unit test can record the same lines in memory with
`spellability_census::capture` and assert that a step's facts are spelled.

The census sorts a miss into one of three gaps, each with its own fix:

- **Writable but not found.** The fact has Click syntax and its operands
  have names, but the premise speller's search misses it: reflexive pointer
  equalities such as `p == p`, `viewable(p[0..1])` after an `unfold`, an
  applied theorem's conclusion such as `cd(n - 1) == 0`, and goals with no
  recorded presentation. The fix is the total speller.
- **A value with no name.** The fact mentions a value or address nothing
  names, printed `<unnamed A>` or `<pointer A>`: a callee's result, a havoc,
  an allocation. The fix is naming at introduction.
- **No syntax.** The fact's kind has no Surface form: writability, the
  memory a step may change.

The census does not count [kernel authority](#kernel-authority).
