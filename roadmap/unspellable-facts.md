# Unspellable facts: make every proof-state fact round-trip

Priority: P1.

Soundness: incomplete. Every cited spelling is lowered again and checked, so
no false acceptance is known. A fact with no spelling costs completeness (a
smart tactic declines a route whose premise it cannot cite), expansion
(`click expand` cannot write the step out) and readable reports
(placeholders such as `<unnamed A>`).

This is a handoff document for the work in progress. The rule itself, and
the tools that measure it, are in [Spellability](../docs/internals/spellability.md);
read that first.

## Shared SurfaceTerm and KernelTerm migration (2026-10-31)

The user approved a staged unification of source expressions and kernel
expression trees, rather than implementing round-tripping independently for
each term family. The first slice is on `codex/unified-terms`:

- `SurfaceTerm` is the source expression enum; `ContractExpression` is a
  compatibility alias.
- `KernelTerm` is a typed immutable DAG. Integer arithmetic and calls have
  `KernelTerm` children. Construction preserves operations and does not read
  assumed equalities or prove definedness.
- Integer certificate arithmetic and ordinary Integer arithmetic on existing
  values construct this tree; Integer and pure-call raising consume it. The current checker still receives the old terms
  through lossless bridges. Converted shared nodes cache the bridge, with
  weak reverse links, so repeated steps do not rewalk growing expressions.
- Explicit legacy leaves retain unmigrated values, including complete pointer
  payloads and their auxiliary qualifiers. These leaves and their adapters
  are temporary, not completion of the unification.

The first slice merged as PR #2192 (`710258f93`). The ordinary-Integer
follow-up is on `codex/unified-terms-ordinary`, integrated onto that master.

The updated full gate passed: 6,957 unit/API/import/scaling tests, 58 examples, and
4,935 mdtests. It took 10m15s, exceeding the ten-minute target by 15 seconds;
no limits changed and no nightly suite ran. The first slice's full mdtest
fact-stability audit passed with zero differences. The ordinary-Integer
follow-up's focused `integer` audit found a pre-existing failure in
`integer_sum_range_fold`: its entry proof used `assumption()` for a bound
containing `-1000 * 0`, relying on the old lowering-time simplification.
The same failure reproduced at the first slice's commit `fc5dc0d81`.
The fixture now proves each initial multiplication equals zero and combines
that equality with its existing bound using an arithmetic certificate. Its
termination certificates also now prove mathematical Integer differences,
rather than the former machine subtraction. The focused `integer` rerun
passed all 248 selected fixtures with zero fact-dependent lowerings.
The rewrite scaling regression now uses fresh selected variables at each size
so all samples start cold; its exact work-equality assertion remains intact.

The follow-up increment migrates ordinary Integer negation, addition,
subtraction, multiplication and constant-nonzero-divisor quotient/remainder.
Deferred operands and symbolic-divisor obligations retain their evaluation
forms. The repeated-squares scaling test now covers ordinary lowering too.

The ordinary-Integer follow-up merged as PR #2196 (`170c72d43`). The next
slice, on `codex/kernel-machine-terms`, migrates machine argument bridges:
shared nodes for exact literals, variables, non-shift binary operations,
complement and casts. Result types remain distinct from operation formats.
Pointer-carrying integer records stay intact. Shifts, loads and binders remain
legacy leaves; machine lowering/execution producers have not migrated yet.
Machine export is linear in the explicit boxed output, with no cache that
clones every intermediate subtree. Round-trip coverage exposed a cast-chain
collapse defect: `(x as int128) as int64` lost its intermediate cast and
produced a generic cast that direct syntax lowered to `Int64From32` instead.
Keep wide symbolic chains intact, retain the established 32-bit word rules,
and spell wide casts and literals structurally. The C++ round-trip contract
then exposed a reliance on constructor folding; extend the existing indexed
e-graph cast-composition rules to 128-bit intermediates instead. A regression
keeps the cast syntax distinct while proving the equality, rejects lossy
round trips, and scales selected chains beside unrelated classes.
The normal gate passed: 6,979 unit/API/import/scaling tests, 58 examples and
4,936 mdtests (10m06s, with the ten-minute timing warning). The subsequent
fact-stability audit exposed diagnostic work consuming the proof budget:
alpha comparison was charged, and the existing uncharged scope suppressed
explicit records but not checkpoints. Both paths now exclude audit work;
limits and ordinary verification charges are unchanged. All 27 focused
accounting tests passed, and the full 4,936-fixture fact-stability audit
passed with zero lowering differences. No nightly suite or limits were changed.

The shift follow-up extends those binary nodes to both shift operators.
The old shift producer already converts counts to the left operand's carrier
width; preserve the conversion structurally rather than assigning a new source
count type. Coverage includes narrower and wider counts with both signednesses,
plus mixed arithmetic/shift chains beside unrelated terms. The mixed signedness
case exposed a pre-existing spelling defect: zero-extending the word of signed
`x` printed as `x as uint64`, which sign-extends instead. Widening spellings
now explicitly retain the source `int32`/`uint32` interpretation before the
64-bit cast. Validation: 76 focused tests passed; shift-fixture fact-stability
audit passed with zero differences; full gate passed in 9m50s (6,981 unit/import/
scaling tests, 58 examples, 4,936 mdtests). PR #2202 entered the merge queue
while this follow-up was validating, then left it after the Rust scalar-slice
integration test hit its 30-second limit. Its three negative mutations had
reverified every unrelated function. Keep the full positive check, but check
each mutation against its affected independent function. Separate the full
positive suite and negative proof search into ordinary gate tests, retaining
every case and the 30-second bound. They took 11.1s and 10.3s respectively in
the integrated parallel gate. No limits or cases are removed. The follow-ups
update the same PR.

The next local increment migrates all six specialized 32/64-bit conversions
to shared cast nodes. Their source/destination formats and operands are explicit;
a transitional encoding tag preserves the exact old constructor, distinct from
a generic cast. Tests cover all six encodings, repeated import identity, typed
children, and linear cast-chain work beside unrelated terms. All 78 focused
bridge/spelling tests passed. After merging current master (`aece82749`), the
full gate passed: 6,998 unit/import/scaling tests, 58 examples, 4,948 mdtests.
Elapsed 13m07s included a 3m05s rebuild; unit and fixture phases totaled about
9m46s, and the overall gate emitted its ten-minute timing warning. The focused
machine-fixture fact-stability audit passed with zero differences. No nightly
suite was run.

PR #2219 merged. The next slice, `codex/kernel-integer-comparisons`, moves
all six mathematical-Integer comparisons out of `LegacyBool`. Shared nodes retain
the exact operator and ordered Integer children. Import/export neither decides
the comparison nor swaps its operands. Tests reconstruct each operator after
dropping the source, spell comparisons inside Boolean-to-machine conversions,
and grow shared Integer operands beside unrelated terms. Condition producers
and the remaining overflow, pointer, memory and algebraic conditions remain
separate migrations. Validation: all 86 focused bridge and spelling tests passed.
`scripts/check.sh --no-fail-fast` passed 7,030 unit/import/scaling tests,
58 examples and 4,953 mdtests in 11m32s (ten-minute timing warning).
Separate fact-stability audits passed 248 integer and 20 bool fixtures with
zero differences. No nightly suite ran and no limits changed.

PR #2212 merged. The next slice, `codex/kernel-bool-conversions`, introduces a
logical Bool sort in the shared tree and migrates Boolean-to-machine conversions.
Their conditions expose literals, variables, machine comparisons, equality,
conditionals and calls as typed children. Other condition sorts keep complete
legacy payloads, including pointer metadata; this does not migrate all condition
producers. Comparison format remains structural even when fact equality ignores
signedness. Raising writes the existing Boolean cast syntax with the Surface
operand retained. Validation: all 134 focused bridge, spelling and conversion tests passed.
`scripts/check.sh --no-fail-fast` passed 7,022 unit/import/scaling tests,
58 examples and 4,953 mdtests in 11m14s, with the ten-minute timing warning.
The separate fact-stability audits passed 20 bool and 248 integer fixtures
with zero differences. No nightly suite ran and no limits changed.

PR #2211 subsequently merged as `617ab6c8a`. The next slice on
`codex/kernel-boolean-integers` migrates the reverse direction: mathematical
Integer-to-machine conversions. A shared node retains the explicit destination
and Integer child, and the speller emits the existing `to_int32`, `to_uint64`,
etc. calls. This also fills the old bitvector speller's explicit refusal for
these conversions. Boolean conversions still require migrating their condition
operand; no condition or pointer semantics change in this slice.
Validation: `scripts/check.sh --no-fail-fast` passed all 7,024 unit/import/scaling
tests, 58 examples and 4,953 mdtests in 10m37s (ten-minute timing warning).
All 17 focused bridge/spelling tests passed. The focused integer fact-stability
audit passed 248 fixtures with zero differences, matching the pre-change audit.
No nightly suite ran and no limits changed.

PR #2202 merged as `5211102e4`. On `codex/kernel-integer-observations`, the
next increment moves `IntegerTerm::Machine` observations into shared typed
nodes. Source interpretation is explicit, including signedness, and raising
keeps the required cast inside snapshot selectors. Exact bridge reconstruction
is tested after dropping the old source; scaling grows the selected machine
operand beside unrelated terms. Boolean casts and Integer-to-machine conversion
remain separate migrations. Narrow observations keep their existing spelling;
added narrowing/promotion casts change their structure. Observation casts use
Surface CUnary operands, preserving resource fields and scoped names instead
of projecting them into C fragments. The full gate passed: 7,015 tests, 58
examples and 4,949 mdtests in 10m12s (timing warning). All 83 focused tests and
248 integer-fixture fact-stability audits passed, with zero differences.
No nightly suite ran and no limits were raised.

Next: migrate the remaining ordinary expression producers and machine arithmetic onto the
shared tree, then replace checker adapters with typed views. Algebraic values,
binders, full pointers and loads follow; facts and goals should ultimately
have common term operands. Keep definedness as separately scoped obligations.
The proposed three-field `CPointer` representation is not settled. This first
slice changes no pointer semantics and does not claim to resolve #2179 or the
remaining census misses. See [the migration boundary](../docs/internals/spellability.md#shared-term-migration).

## Structural mathematical arithmetic (2026-10-31)

The next two Integer defects are constant folding during lowering and missing
mathematical type context after a rewrite removes the last typed operand.
For example, the raw fact `IntegerEqual(Add(1, 1), 2)` previously lowered back
to `true`; a large literal-only addition could instead parse as C arithmetic.

This increment retains Integer operation and comparison nodes in source
lowering, specification evaluation and generic substitution. Signed numerals
remain constants, distinguished from negation nodes by a typed operand.
Generated comparisons spell their left operand as a typed local expression,
for example `(let integer_value: Integer = 1 + 1; integer_value) == 2`.

Checking evaluates literal arithmetic under the numeric budget, caching shared
nodes and refusing symbolic nonlinear operand DAGs in constant time. Native
comparison views recognize arithmetic bounds such as `-2147483647 - 1`
without rewriting the original fact. Compound views have a maintained index
with source support counts; zero/unit identities join equality-graph classes.
No lowering path consults equality facts to choose the produced term.

The full `scripts/check.sh --no-fail-fast` gate passed: 6,909 unit/API/import/
scaling tests, 58 examples and 4,922 mdtests, with pinned frontends required.
It took 10m45s including a 52.8s test-binary rebuild; unit and fixture phases
took 265.6s and 311.0s. This exceeds the ten-minute wall-time target. No limits
were raised and no nightly suite ran. Earlier failures exposed proof steps
that depended on implicit folding; they now use arithmetic checking or state
the required machine observation explicitly, without changing C or contracts.
Both fresh ordinary-corpus audits passed when run separately: 23,986 census
observations, 1,596 written misses (previously 1,615), 3,141 smart misses
(previously 3,167), and zero fact-stability differences. The numeric-only
Integer goal misses fell from 68 to zero; all Integer goal-miss observations
fell from 804 to 777. Counts are observations, not distinct defects, and the
retained structure also changes which proof steps are observed.

Running both flags together still rejects the false claim in
`solve_false_list_position_is_prompt`, but exhausts its 100,000-unit smart
budget instead of producing the expected diagnostic. The ordinary full gate,
individual flag probes and both separate full audits pass. This combined
audit accounting issue remains; no budget was increased. The separate audits
ran concurrently (about 483s each), so their timings are not serial benchmarks.

Remaining smart groups include Integer equality rewrite goals (322), int32
equality rewrite goals (311), loadability step facts (254), pointer-value step
facts (224), and Integer ordering rewrite goals (180). Representative remaining
Integer goals include `to_integer(0 + (n + m)) == to_integer(n) + to_integer(m)`;
trace their exact failing subterm next rather than assuming they are the same
literal-context defect. Overall spellability acceptance remains incomplete.

## Smart refined-goal spellings (2026-10-31)

The ten rewrite-goal misses exposed by the nested resource field increment
were an explicit smart-search shortcut: `Proof::spelled_goal` returned `None`
while search was active. Surface substitution cannot always carry the goal
forward when its operand and the selected equality use different spellings
of the same kernel term (`result` versus `old(p->n)`, for example).

Smart refinements now reconstruct their goal from source names, current and
entry states, and indexed recorded points, using the structural speller
directly rather than premise-spelling search. Scalar goal reconstruction
selects the indexed first holder and does not scan alternative local aliases.
The candidate must lower to the exact successor; this retains presentation
and does not prove the outstanding goal. Written refinement behavior is
unchanged. The original false hidden-record claim is still rejected, and its
smart rewrite goals now all retain spellings.

A deterministic regression at 16, 64, 256 and 1,024 ambient facts and local
names, including many holders of the same value, pins bounded spelling work
and checks that spelling does not admit the unsupported goal. All 236 focused
rewrite tests passed. The full `scripts/check.sh --no-fail-fast` passed:
6,903 unit/API/import/scaling tests, 58 examples and 4,922 mdtests, with pinned
frontends required. Its 10m18s wall time exceeded the ten-minute target by
18 seconds (preceding gate: 9m19s); unit and fixture phases took 279.5s and
322.3s. No limits were raised and no nightly suite ran.

The combined ordinary-corpus census and fact-stability audit passed in
252.29s: 23,786 observations, 1,615 written misses (unchanged), 3,167 smart
misses (previously 6,620), and zero fact-stability differences. The extra
observations reflect further search steps made available by retained goal
spellings; these are observation counts, not distinct defects. Remaining
smart groups include Integer equality rewrite goals (339), int32 equality
rewrite goals (311), loadability step facts (254), pointer-value step facts
(224), and Integer less-or-equal rewrite goals (214). Overall spellability
acceptance remains incomplete.

## Nested resource field selectors (2026-10-30)

The hidden-child equality in `a_hidden_record_is_shown_beside_its_resource`
now round-trips. `pair(p).first.v` selects the retained hidden field in the
unique in-scope instance with exactly that written resource target;
`whole.first.v` also selects the slot through a named parent. `old(...)`
keeps the entry value accessible after unfolding. The current path requires
the parent to be held. Selection neither opens the child nor grants memory
permissions, and it does not use equality facts to resolve arguments.
Ordinary call selectors currently exclude explicit type/resource arguments;
ambiguous targets require an instance name.

Parser targets now maintain inverse indexes for written calls and exact
hidden targets, replacing the old hidden-binder scan. Child bindings that
retain a parent clause only as a parser placeholder do not enter the call
index; scoped removal/restoration preserves that distinction. A deterministic
regression at 16, 64, 256 and 1,024 unrelated and same-call targets checks
constant selection/refusal work. Entry model-field provenance records a
source call spelling for unnamed parents. Existing kernel projection and
ownership rules are unchanged.

The original census regression passes and still rejects the false return
claim. Four mdtests cover call/named paths, old values across unfold/refold,
absent current parents and ambiguous selectors. The full
`scripts/check.sh --no-fail-fast` gate passed in 9m19s: 6,902 unit/API/import/
scaling tests, 58 examples and 4,922 mdtests, with pinned frontends required.
An earlier run timed out in the existing Rust scalar-slice import test; it
passed alone in 17.8s and in the final parallel gate in 18.3s under the same
30-second limit (preceding checkpoint: 19.4s). No limits were raised and no
nightly suite ran.

The combined ordinary-corpus audit passed in 216.53s: 22,994 observations,
1,615 written misses (previously 1,621), 6,620 smart misses (previously 6,610),
and zero fact-stability differences. The ten additional smart misses are
rewrite goals from the original false `get` claim: making the hidden-field
equality citable exposes more rewrite attempts, whose resulting goals still
have no recorded surface spelling. A focused audit reproduces all ten in
`a_hidden_record_is_shown_beside_its_resource`; its four written observations
are now spelled. These counts are observations, not distinct defects, and
the remaining rewrite-goal spelling gap is not hidden or bypassed.

## Structural read definitions (2026-10-31)

The `CellsForgotten` miss in
`a_join_forgets_a_cell_the_arms_disagree_on` is a representation mismatch,
not an unnamed new program time. The branch join keeps the untouched right
field and makes the written left field unknown. Reading the latter emits a
load-definition equation whose raw RHS drops the unrelated cached right field;
its canonical read handle already names the joined memory. Lowering that RHS
therefore produces the handle, not the raw representation retained in the fact.

Read producers now retain the exact registered descriptor and emit their
citable equations using the structural read handles that source lowering uses.
The descriptor stays in producer metadata. Typed-read consumers preserve its
exact epoch, address and kind through indexed lookups. Stored values are never
substituted into these terms; read-over-write remains checking authority.
The census regression checks that the equation round-trips while the original
false return claim is still rejected. Cache-chain scaling and changed
width/address/epoch controls accompany the change. The first full run exposed
five wide-read fixture failures: the old raw definition had a width-check
exception for its hard-coded 32-bit comparison. The producer now emits the
read's actual carrier width, with a 32/64/128-bit regression. The shared
verified-definition classifier also recognizes this structural form, preserving
its existing exclusion from pointless smart equality rewrites.

All 85 focused tests pass. The final `scripts/check.sh --no-fail-fast` gate
passed in 9m24s: 6,900 unit/API/import/scaling tests, 58 example projects, and
4,918 mdtests, with both pinned frontends required. No limits were raised and
no nightly suite ran. The fresh combined census and fact-stability audit
passed in 220.64s: 22,970 observations, 1,621 written misses (down from 1,721),
6,610 smart misses (down from 6,772), zero Boolean misses, and zero
fact-stability differences. Census observations are not distinct defects;
other fact families remain to be repaired.

## Discarded call results and historical model fields (2026-10-31)

The two remaining smart Boolean misses in
`cpp_generic_class_state_in_a_resource` shared a discarded `pop` return value.
One also needed the list produced by the preceding `push`; the other needed
its contract-entry list. The code kept execution snapshots, but discarded the
unassigned return value and indexed only scalar model-field history.

The checked call transition now retains its exact non-void result. Recording
the call exit gives it `<region>.result` independently of destination locals;
Boolean and integer synthesis uses an indexed reverse lookup. Resource-field
history now includes symbolic algebraic values. Synthesis selects the exact
field in the current state, at entry (`old`), or at its indexed historical
point (`at`). Neither path recovers names by searching equalities or history.
The original C++ source and contracts are unchanged.

Focused checks eliminate both Boolean misses in the original fixture and cover
unassigned integer/Boolean results and void-call rejection. Deterministic tests
at 16, 64, 256, and 1,024 entries cover result replacement/removal, independent
snapshot branches, and historical field lookup after unrelated state changes.
The full `scripts/check.sh --no-fail-fast` gate passed on upstream #2171:
6,896 unit/API/import/scaling tests and all four fixture aggregates (58 example
projects and 4,918 mdtests). It took 12m53s, including a 3m12s rebuild, exceeding
the ten-minute target; test phases took 258s and 300s. No limits were raised and
no nightly suite ran. A fresh combined ordinary-corpus census and fact-stability
audit passed in 227s on that same binary: 23,003 observations, 1,721 written
misses and 6,772 smart misses, versus 1,783 and 6,792 at the preceding checkpoint.
Both written and smart Boolean misses are zero, as are fact-stability
differences. These are observation counts, not distinct defects. The largest
remaining written groups are int32 equalities (357), loadability (228), pointer
value equalities (136), Integer less-or-equal (133), and algebraic equalities
(122). Overall spellability acceptance remains incomplete.

## Current arithmetic checkpoint (2026-10-30)

The pointer migration has moved on to arithmetic definedness. This source tree
contains the core arithmetic migration, merged as
[PR #2160](https://github.com/clicklang/click/pull/2160), with its pushed commit
verified upstream. It was prepared on `codex/structural-arithmetic-definedness`.
The integration history remains in
`codex/arithmetic-landing`; `codex/arithmetic-definedness` is its preserved earlier
checkpoint. The pointer checkpoint below is historical. The preparatory PRs
#2155 through #2159 are merged and their pushed commits were verified upstream.

- Machine arithmetic lowers structurally and retains its domain as ordinary
  scoped proof obligations. Context can discharge those obligations but cannot
  change the term. Quantified domains follow the chosen polarity: an existential
  needs a defined true witness, a negated existential excludes every candidate
  with a defined false body, and universal/negated-universal claims are dual.
- Claim goals now retain their evaluation obligations. Ordinary proof checking
  discharges them in the actual branch context and retains generated proof steps
  for expansion. Final certification consumes the checked path's completion;
  it does not lower and prove the same claim again. Producer-owned path receipts
  and identity indexes avoid repeated premise and path scans. The certification
  increment passed 61 focused tests and all 1,060 scaling tests before integration.
- Signed/unsigned 32/64-bit arithmetic, shifts, and supported 128-bit
  multiplication/division/remainder use structural terms with separate domains.
  Integration exposed a Rust-specific shift distinction: Rust permits signed
  wrapping left shifts, whereas C requires a nonnegative representable result.
  Rust shifts now retain their own semantics through logical expressions and
  resource operands; C's domain remains unchanged. Count obligations are
  discharged only by established facts, never by pending obligations themselves.
- Global-array loads now use the same declaration and address indexes as static
  arrays when spelling values. This fixes the original alias-load fixture's
  `old(g[0])` requirement. Both its generated proofs expanded and rechecked
  without implicit solving; all 58 synthesis tests passed, including an exact
  round-trip test for an overwritten multidimensional global element. The
  standalone fix is [PR #2152](https://github.com/clicklang/click/pull/2152),
  merged and verified in upstream. Its full gate passed (6,833 unit tests, 58 examples,
  4,895 mdtests), taking 10m33s, 33 seconds over the target.
- The lexicographic recursive-measure example needs explicit links for the
  machine subtraction's integer observation and the first component's strict
  decrease. The original C and contract pass with those proof links.

The earlier integrated `scripts/check.sh --no-fail-fast` gate passed: 6,862 unit/API/
import/scaling tests and all four fixture aggregates (58 example projects and
4,916 mdtests), with both pinned frontends required. It took 10m07s, seven seconds over the ten-minute target. No nightly
suite ran. The previous five fixture failures are repaired: the recursive proof
has explicit links, and the four negative controls retain their actual domain
and checked context. Rust resource shift controls also pass, including unknown
and invalid count rejection.

A combined census/fact-stability audit of that earlier ordinary mdtest corpus also
passed (231s), using that exact binary. It recorded 23,038 census observations:
8,853 written and 14,185 smart. There are 2,081 written spelling misses and 6,885
smart misses; these are observations, not distinct defects. The largest written
categories include int32 equalities (375), loadability (228), Integer ordering
goals (228), and algebraic equalities (193). Acceptance is not complete.

The earlier stability audit recorded 199 differences across five fixtures: 98
each in the two unsigned-loop-counter fixtures, plus one each in
`a_bounded_variable_tag_preserves_an_incoming_word_relationship`,
`a_checked_low_tag_add_preserves_an_incoming_word_relationship`, and
`tagged_pointer_explicit_round_trip`. These are observations, not distinct bugs.

The index-conversion cause is confirmed: `pointer_index_term` chose a signed
index for a bounded uint32 and a widened index otherwise, changing the address
and hence the deterministic load identity. The fresh baseline on merged #2160
recorded 72 differences across the two loop fixtures. The indexing fix on
`codex/stable-array-indices` always observes the completed unsigned expression
by exact zero extension, independent of facts. Its structural inverse spells
ordinary `a[i]` for narrow and native wide indices, including Rust `usize`.
The common range checker uses maintained unsigned order bounds for that widened
value; it does not ask the general solver or scan unrelated bounds. Both
original loop proofs pass unchanged and now record zero stability differences.
Masked pointer-table cases also need intrinsic bounds retained at graph-node
creation and wide-offset equalities translated to full-width index equalities.
The next table-read case inherits the one new address disequality; it does not
replay the earlier case facts. The positive table examples and false-first-entry
control retain their original C, contracts, and expectations.

This indexing increment passed `scripts/check.sh --no-fail-fast` with both
frontends required: 6,874 unit/API/import/scaling tests, 58 example projects,
and 4,916 mdtests. The gate took 11m55s, above its ten-minute target. No limits
were raised and no nightly suite ran. The focused selection passed all 1,284
checks before the final gate. The fresh ordinary-mdtest stability audit passed
in 233s on the same binary and recorded exactly three differences, one in each
of the pointer-tag fixtures named above. No index-related differences remain
in this corpus.

The pointer-tag increment on `codex/structural-pointer-tags` keeps the numeric
uint64 `&` term structural. `bounded_uint64_tag_equation` uses the previous
fixed-size exact bound lookups to emit a separate equality instead of removing
the tag from the result. Addition still requires the low-bit prefix clear;
missing bounds, incomplete masks, and possible carries produce no equality.
The explicit round-trip fixture now rewrites `color == 1` and certifies the
full tagged-and-masked expression. Its old certificate relied on lowering
silently removing the tag. The C and contracts are unchanged.

All 27 tag-related fixtures pass with zero observed stability differences.
Regression coverage checks structural lowering with and without bounds,
equality refusal when premises are missing, and deterministic work with
4/16/64/256 unrelated facts and additional bounds on the same tag. All 1,227
focused tests passed, including every scaling test. The full
`scripts/check.sh --no-fail-fast` gate passed with both frontends required:
6,877 unit/API/import/scaling tests, 58 example projects, and 4,916 mdtests.
It took 10m48s, above the ten-minute target; no limits were raised and no
nightly suite ran. A fresh ordinary-mdtest stability audit on the same binary
passed all 4,916 fixtures in 218s and recorded zero differences, down from
the three pointer-tag observations. This does not settle the spelling census.
Atomic division/shift overflow-domain spellings also still need targeted auditing.

A fresh census after the pointer-tag fix passed all 4,916 ordinary mdtests
in 229s: 23,042 observations, with 2,040 written and 6,870 smart misses. These
are observations, not distinct defects. A direct atomic-domain spelling audit
found six missing positive-overflow spellings (add/subtract/multiply at int32
and int64), plus both polarities of division and left-shift overflow at both
widths. The polarity increment on `codex/arithmetic-domain-spellings` spells
positive add/subtract/multiply overflow as `not defined(expression)` and keeps
negative overflow as `defined(expression)`. Exact round-trip tests cover both
polarities and widths. It changes synthesis only, not evaluation or domains.
The full `scripts/check.sh --no-fail-fast` gate passed with both frontends
required: 6,877 unit/API/import/scaling tests, 58 examples, and 4,916 mdtests.
It took 11m05s, above the ten-minute target. No limits were raised and no
nightly suite ran.

The division/shift atoms remain separate: `defined(a / b)` also includes the
nonzero-divisor requirement, and `defined(a << b)` also includes count/sign
requirements. Substituting those compound propositions for an atomic fact is
not a round-trip. Their reproductions are retained for the next spelling design
step; no syntax or domain semantics have been changed for them.

The next increment, `codex/bool-fact-spellings`, reconstructs Boolean calls,
equalities, conditionals, and Boolean call arguments through their existing
Surface forms. The original `a_bool_pure_function_states_a_claim` fixture
reproduced missing unfold facts and a goal before the fix. Pure-theorem premise
synthesis now uses the retained source state and selected source-name lookups;
it no longer reconstructs an int32-only parameter environment. Rewriting also
keeps a condition claim in lowering's truth-polarity form: rewriting to
`not even(0)` at false polarity produces `even(0)` at true polarity.

Five focused checks pass: the original fixture has no Boolean spelling misses,
both polarities round-trip exactly, expansion rechecks without implicit search,
the rewrite produces the exact polarity, and synthesis work grows with the
Boolean expression rather than unrelated names. The full
`scripts/check.sh --no-fail-fast` gate passed with both frontends required:
6,883 unit/API/import/scaling tests, 58 examples, and 4,916 mdtests, in 9m09s.
The combined ordinary-mdtest census/stability audit passed on the same binary
in 219s with zero fact-stability differences. Original fixture proofs are unchanged.

The fresh census records 22,858 observations: 1,923 written and 6,798 smart
misses. Written Boolean misses are 23, versus 35 at the preceding census
checkpoint; the original Boolean fixture goes from 10 misses to zero. Remaining
Boolean misses involve generic list calls and algebraic arguments, including
unnamed values in stack resource cases. They remain open; this increment does
not establish complete Boolean or algebraic spelling coverage. Counts are
observations, not distinct defects. No nightly suite ran and no limits changed.

The following increment, `codex/generic-fact-spellings`, fixes two reproduced
causes of generic-call misses. Calls now spell their declared name, without the
kernel's `::<...>` instance suffix; typed arguments reconstruct the instance.
Pure premise synthesis includes variables inside opaque applications and reuses
the existing goal/proof-local binder names, including `obtain` witnesses and
shadowing. The original constructor-inference and proof-binder fixtures have
no fact spelling misses in focused checks. Concrete and nested instances survive
printing, parsing, and exact re-lowering; a generic-list proof expands and
rechecks with implicit search disabled. This does not name previously unnamed
resource fields or add pointer/rigid-parameter call-argument synthesis. The full
`scripts/check.sh --no-fail-fast` gate passed in 9m18s with both frontends
required: 6,887 unit/API/import/scaling tests, 58 examples, and 4,916 mdtests.
No nightly suite ran and no limits changed.

The combined ordinary-mdtest audit passed all 4,916 fixtures in 228s with zero
fact-stability differences. Its 22,858 census observations contain 1,822 written
and 6,788 smart misses, down from 1,923 and 6,798. Written Boolean misses fall
from 23 to 5 (smart Boolean misses from 8 to 2): three observations of unnamed
list tails in C++ stack `pop` proofs and two `contains_cons` equalities at rigid
`T` and `List<int32>`. These are the next reproduced spelling cases; counts
remain observations, not distinct defects.

The next spelling increment addresses those five written Boolean observations.
The two `contains_cons` cases lacked synthesis for `AlgebraicEqual` inside a
Boolean expression. The three stack observations already had match-arm source
names, but premise synthesis ignored `AlgebraicVariable` bindings and algebraic
synthesis did not consult proof-local names. Generic constructors additionally
omitted C type-parameter fields. These paths now use the existing comparisons
and bindings without changing lowering or consulting facts. Focused census
regressions cover the original rigid/nested list fixtures and an execution
match arm. The unchanged generic-resource and concrete negative-stack fixtures
have no written Boolean misses in focused audits.
The full `scripts/check.sh --no-fail-fast` gate passed with both frontends
required: 6,890 unit/API/import/scaling tests, 58 examples, and 4,916 mdtests.
It took 12m49s, exceeding the ten-minute target, including a 3m32s rebuild after
a baseline comparison. Unit and fixture phases took 251s and 289s respectively.
No limits were raised and the nightly suite was not run.
The fresh combined audit passed all 4,916 ordinary mdtests in 225s with zero
fact-stability differences. Written Boolean misses are now zero; two smart
Boolean equalities involving returned values remain. There are 22,961 census
observations, with 1,783 written and 6,792 smart misses (previously 1,822 and
6,788 over 22,858 observations). Better premise spellings change some proof
routes, so counts are observations rather than a fixed set of defects. The
additional misses are rewritten algebraic/Integer goals in stack proofs.
A separately selected off-corpus `cpp_class_object_state_named_in_a_proof`
fixture still fails at `push` tactic 7's child-resource argument equality; the
same failure was reproduced at the preceding commit `fcb89b37d`.


An attempted standalone certification extraction on upstream after #2152 is
**not publishable**: `codex/final-certification-slice` at `6ec3c8a95` failed its
full gate (6,841 of 6,842 units passed; fixture phase was not reached). The
unchanged negative test `forward_conversion_requires_symbolic_argument_definedness`
incorrectly accepts an unbounded `to_integer(x + 1) == to_integer(x + 1)` claim.
The integrated migration rejects it correctly.

The old arithmetic producer emits `!overflow` as a success-path fact and a
separate UB path; logical lowering drops the UB path. Claim focus imports that
success fact, so consuming the completion without final reconstruction is unsafe
until the producer makes it a mandatory obligation instead. Do not weaken the
negative test or add a new finalizer recheck. The PR boundary must keep receipt
consumption after all structural-domain producers, including shifts, wide arithmetic
and Rust shift corrections. A possible earlier
slice retains claim obligations, ordinary scoped discharge and diagnostics while
leaving the existing finalizer unchanged. That safe slice merged as PR #2155
and its pushed commit was verified in upstream. Its full gate passed (6,841 tests, 58 examples,
4,895 mdtests; 10m43s). After applying the identical patch to current master,
1,123 focused/scaling checks passed, including the unchanged overflow rejection.
The earlier failing extraction is preserved only as evidence.

The refreshed integration in `codex/arithmetic-landing` at `70970d005` includes
current unsigned-term representation changes and the code from merged PRs
#2155 and #2156. Its full `scripts/check.sh --no-fail-fast` gate passed:
6,866 unit/API/import/scaling tests and all four fixture groups, in 9m25s.
The older `codex/arithmetic-definedness` checkpoint remains preserved.

Refreshing exposed one shared checker omission: 32-bit word equality consulted
signed bounds only, missing that an unsigned strict predecessor makes a divisor
nonzero. The integration fixes this using the two indexed domain lookups already
used for 64-bit equality, with signed-evidence and flat-query-work regressions.
The unchanged remainder proof now passes. This checker fix merged as PR #2157.
Rust shift source identity merged as PR #2158, preserving old evaluator behavior
until the core migration. Mathematical certificate intermediates and the two
recursive proof adaptations merged as PR #2159. All pushed commits were
verified upstream.

Final core validation at `ec2ccbd08` passed the full
`scripts/check.sh --no-fail-fast` gate: 6,868 unit/API/import/scaling tests and all
four fixture groups, exit 0. Runtime was 15m21s (3m54s compilation, 306.7s units,
359.3s fixtures), exceeding the ten-minute budget. No limits were raised and no
nightly suite ran. The final code tree includes both preparatory PRs; only this
checkpoint documentation changed afterward. The earlier census and stability
figures above have not been rerun on this final tree; full spellability acceptance
remains incomplete.

## Arithmetic migration: landing order

The arithmetic migration separates structural terms from definedness
obligations. Its required dependency order is:

1. Retain claim evaluation obligations and discharge them during ordinary
   proof checking, preserving their certificates and diagnostics. Keep the
   existing final certification behavior in this increment.
2. Migrate partial arithmetic producers to structural terms with mandatory
   obligations, including quantified domains, shifts, wide arithmetic, and
   Rust's distinct shift semantics.
3. Consume the already-checked claim completion during final certification,
   removing its repeated lowering and proof attempt.

Step 1 landed separately; this core update combines steps 2 and 3.
The third step cannot land first: legacy arithmetic success paths can carry
"no overflow" as a path fact. Early completion consumption with those old
producers incorrectly accepts an unbounded `to_integer(x + 1) ==
to_integer(x + 1)` claim. The existing negative test
`forward_conversion_requires_symbolic_argument_definedness` caught this in an
experimental extraction; that extraction was not published. The complete
migration rejects the claim. Preserve this control throughout the staged
landing, and do not add a new finalizer recheck as a compatibility workaround.

## The goal

For every kernel term a proof state holds, `lower(raise(x)) == x`. That needs
two things:

1. **Lowering is structural and fact-stable.** A lowered term has the
   structure of its surface text. Facts may decide whether lowering succeeds
   and add side facts, but they never choose the term. Equalities live in
   the equality graph and the comparison form, which every check consults.
2. **Every kernel term and fact kind has a Surface spelling.** A value is
   named where it is introduced (a call result, a havoc, an allocation), and
   every fact kind has syntax.

## Decisions already made by the user

- Make lowerings structural in small PRs. Ask only when a step needs a
  decision, not about ordering.
- `A implies B` and `A or B` guard the right side's definedness
  obligations: `A implies obl`, `A or obl`. Kernel `/` by zero is an opaque
  total term. A Click `/` that returns an option is a possible future
  change, owned by the integer thread.
- Fact-dependent integer lowerings belong to the integer thread, recorded in
  [standard-library.md](standard-library.md#fact-dependent-integer-lowerings):
  spec `/` and `%`, `byte_stride_index` and `pointer_index_term`.
- The empty population is handled by a real kernel axiom,
  `population_member_count_zero`: `count(R(a, _)) == 0` implies
  `count(R(a, k)) == 0`. The user accepted this to keep the work moving.
- A call's result is spelled `<region>.result`, beside the region's
  `entry` and `exit` points. It is not a magic `result` word inside `at(...)`.
- **Stepping must stay near linear.** A proof may take n² work, but stepping
  through a function of n statements must not. Adding to the equality graph
  during a step is fine when finding the addition is cheap: no work that
  repeats per step over the whole history.
- **Prefer one-step frame decisions.** Each step decides what it keeps,
  looking one step back with the facts it has. Don't walk back n steps for
  every query. A proof restates a frame that needs a fact learned only
  later.

## Landed

- Structural lowerings for membership disjunction, null-pointer class
  evidence, `count(reference)` anchors, the empty range fold, wildcard
  population members, a zero pointer offset, `held(m)`, and `or`/`implies`
  obligations.
- The population axiom, and the `old(count(R(a, k)))` spelling of an exact
  member's entry count.
- `<region>.result`, with call results spelled by their call in traces,
  ranges and unwound reports.
- An entry-snapshot resource argument is read as written, with no fact
  search.
- Frame walks (see [fact-aware-frame-walks.md](fact-aware-frame-walks.md)):
  - the fact-aware cell walk resumes the memoized version walk;
  - C program reads (`cell_value_on_path`) go through that one walk.

## In progress: pointer reads named by version

The largest remaining known violation, listed in
[Spellability](../docs/internals/spellability.md#lowering-is-structural): a
logical pointer read lowers to the pointer stored in its cell, through the
fact-consulting fold `memory_provenance::complete_pointer_read_value` and the
stored-pointer fold in `Pointer::loaded`. So `p->next` after `p->next = q`
lowers to `q`, and `lower(raise(x)) == x` fails.

**Branch.** The work in progress is on `claude/pointer-reads-wip`. It has
15 checkpoint commits, about +680/−60 lines across 17 files, and was rebased
onto master after the frame-walk PRs. Expect to cut it into small PRs; it
should not land as one piece.

**What it does:**

- **Version names.** A logical read of a pointer cell lowers to the read at
  the cell's version (`logical_read_names_its_version` includes pointers;
  `CMemory::symbolic_pointer_version_load`; `Pointer::version_read`).
- **Pointer read-over-write authority.** `pointer_read_over_write_value`
  answers with the pointer the read's snapshot stores at its address, when
  the fact-free version walk shows it (`memory_shown_cell_value`). That
  answer is memoized per snapshot. It refuses a cell that only a fact kept.
  It is used in:
  - comparison forms, for `PointerEqual` and `PointerValueEqual`;
  - equality-graph registration, as term metadata
    (`register_logical_read_values`);
  - block distinctness (`loaded_pointer_stored_block`).
- **Addresses offset from a read.** An address offset from a pointer read
  reaches its stored cell through the stored pointer
  (`stored_pointer_address`). It is used by the integer read-over-write
  authority, and by the exact-address lookup for values that don't name
  their version, such as generic `T`.
- **Rewriting** moves through pointer reads (`equality_rewrite.rs`,
  `term_rewrite.rs`).
- **Tests.** The unit tests that pinned the fold are updated, and there is a
  new mdtest, `a_read_of_a_stored_pointer_cell_stays_a_read.md`.

**Original checkpoint status.** The unit phase had the 15 failures below.
Its fixture phase had not run because the gate stopped after the unit phase.
See the integration checkpoint below for subsequent results.

- **Nine Rust/Charon tests:**
  - `charon_box_fields_take_and_assign_through_self`
  - `charon_generic_container_refuses_a_stronger_put_and_a_false_caller`
  - `charon_generic_container_verifies_through_a_dyn_container`
  - `charon_generic_stack_verifies_once_for_every_type`
  - `charon_recursive_drop_frees_every_node`
  - `charon_recursive_drop_glue_needs_ownership_and_a_measure`
  - `charon_stack_refuses_false_push_pop_and_round_trip_claims`
  - `trait_objects::charon_inline_match_over_a_held_resource_field_refines_itself`
  - `trait_objects::charon_trait_functions_are_defined_from_a_held_resource`

  Most report either "return resource observation has a different checked
  exchange" or a `fold` that cannot establish a body fact. `Stack::push`
  in `design/charon-trial/generic-stack` verifies; `pop` fails at its
  second `fold`.
- **Six unit tests** that pin the old stored-value behavior:
  - `memory_loads::tests::a_symbolic_pointer_read_recovers_the_complete_stored_value`
  - `memory_loads::tests::forced_logical_pointer_reads_keep_the_snapshot_identity_of_cached_values`
  - `memory_loads::tests::scaling_tests::cached_pointer_reads_retain_their_current_cell_identity`
  - `memory_loads::tests::unknown_pointer_in_fresh_storage_does_not_inherit_storage_provenance`
  - `retained_aggregate_resource_values_tests::scaling_tests::retained_resource_fields_preserve_lvalues_and_scale_with_expression`
  - `statement_steps::explicit_transport_keeps_evaluated_tagged_pointer_sources_after_a_join`

  Each needs checking: either the expectation moves to "the read keeps its
  name, and the authority relates it", or it is a real loss.

**Why the Rust tests fail: frames the old fold supplied silently.**
Take `pop`:

```rust
let node = self.head.take()?;
self.head = node.next;
// ...
free(node);
```

At exit, `self.head` is a version name. To match the owned
`allocation(p)` and `*p`, a check must relate it to the pointer stored by
`self.head = node.next`, which means crossing `free(node)`. Memory alone
cannot show the freed block (a pointer read) separate from `self`. The old
fold crossed it through facts inside lowering.

A separate import defect obscured a diagnostic probe: Rust record pointer
fields lost their nominal pointee name, so `self.head.next` fell back to an
untyped load at offset zero instead of the declared eight-byte pointer field
at offset eight. Comparing `self.head` with `old(self.head.next)` then paired
a pointer with `int32`; the rejected comparison reported only "0 paths".
Retaining the field's pointee layout restores the typed nested read. Rejected
specification comparisons now retain their operand types and operator for
the proof diagnostic. This fixes the probe's lowering, not the remaining
nested frame equality.

Two shared read-definition prerequisites are now covered independently of the
pointer-read migration. Direct pointer-read names retain their producer-recorded
projection edges in the equality graph, just as scalar-backed names do. A
successful resource fold/unfold also retains its child reads' checked definitions
in the caller's graph; previously they stayed in a temporary opening context.
A refused exchange publishes none. These are internal read definitions, not
new public proof-state facts. Both changes avoid fact-aware query fallbacks and
have deterministic scaling coverage for selected chains and unrelated state.

### Integration checkpoint (2026-10-27)

The migration is continued on `codex/unspellable-free-investigation`, rebased
onto `14aa465dd` (including the importer fix #2065 and read-definition fix
#2073). The owned free-frame prototype remains on that branch; its frame
facts are checked consequences of the free, not unconditional metadata.

PR #2075 (`c4a8153a6`) moves the published return resource exchange inside
the kernel operation and returns its constructed state and facts. The
follow-up uses the retained C-body successor during final return certification
instead of comparing it with a regenerated representation. Existing path
premise checks still run; this does not remove all legacy trace replay.

Abstract-value reads now participate in typed address congruence. Their
pointer operands register through the common graph walk, and exact producer
projection edges connect their snapshot names. Structural read naming also
retains the original observation as a width-specific definition: naming had
already justified that relation but discarded the original snapshot. The
new graph edges change no lowered terms, scan no facts or memory history,
and never cross an actual affecting store or mix read types or access widths.

With these increments and the WIP full-pointer substitution correction, the
unchanged generic Stack proof verifies end to end, including `push` and
`pop`. Focused regressions check late aliases, nested pointer definitions,
projection/origin relations, type and width separation, writes, and fact
withdrawal. Deterministic scaling covers 8/16/32/64 reads and up to 256
unrelated facts. The complete migration still needs a green gate and the
remaining spellability/fact-stability acceptance work below.


The integrated migration unit gate ran 6,620 tests: 6,609 passed and 11
failed (five Rust container/drop tests and the six representation tests
listed above). Box fields, generic Stack, and both held-resource trait tests
now pass. The false-Stack-claims test still refuses verification, but earlier
than its expected diagnostic at a concrete `Stack::pop` payload fold.

The separately invoked fixture phase passed the C++ and sidecar aggregates.
Eight examples failed: `arena`, `binary-tree`, `concurrency-fork-join`,
`input-cursor`, `owned-segmented-buffer`, `owned-string`, `owned-vector`, and
`perpetual-service`. The main mdtests reported nine failures and then remained
in `rewrite_through_a_loaded_pointer_field.md`; that process was stopped
at 416 seconds after all other main fixtures had finished. This is an
unresolved migration tooling blocker, not a completed fixture verdict.
The obsolete `execute()` in `a_read_of_a_stored_pointer_cell_stays_a_read.md`
was subsequently replaced by `step_until(function.exit)` and passed in a
focused rerun. The eight other reported failures are:

- `aggregate_parameter_old_pointee.md`
- `aggregate_parameter_pointee_expires.md`
- `aggregate_parameter_pointee_contract.md`
- `aggregate_parameter_pointee_resource.md`
- `an_entry_view_names_the_entry_address.md`
- `authority_ordinary_exit_aggregate_parameter_pointee.md`
- `c_produced_resource_over_returned_struct_field.md`
- `cpp_generic_class_state_in_a_resource.md`

The isolated abstract-read follow-up passed `scripts/check.sh`: 6,620
unit/API/import/scaling tests and all four fixture aggregates (13m41s,
report-only ten-minute budget warning). The loaded-pointer fixture passed
in 0.27 seconds there; the stall is reproduced on the broader migration.

The loaded-pointer stall was reduced to a same-thread equality-graph deadlock:
read-definition registration called `last_same_named_cell`, which re-ran the
stop's effect check and attempted to lock that same graph. Retaining the stop
reason alongside the existing `(snapshot, address, width)` version memo fixes
the stall without changing the endpoint or the checked proof. The original
fixture passed in 0.68 seconds; all 56 focused tracker/fixture tests passed.
The new regressions check that later graph growth does not reclassify the
retained decision, and measure 8/16/32/64 new steps plus 0/16/64/256 unrelated
names. A focused before/after fact-stability audit of the stored-pointer
fixture passed with zero differences. The isolated full `scripts/check.sh` passed all 6,622 unit/API/import/scaling
tests and all four fixture aggregates in 15m53s (report-only budget warning;
a separate migration diagnostic build ran concurrently).
No nightly suite was run; the full migration acceptance audits remain open.

A further recursive-drop proof reduction exposed an independent return-proof
bookkeeping defect on master: standalone pure-function `unfold` added its
equation to the branch, but a subsequent `have` and resource fold lost that
evidence at final return certification. The operation now retains its
constructed proposition under the pre-unfold facts on the selected return
path. It adds no equality reasoning or lowering changes. The small C
regression is `return_fold_retains_post_return_function_unfold.md`; companion
tests cover expansion, false-equation rejection, and 4/8/16/32 explicit
unfolds. This repairs that reduced defect, not the remaining migration Rust
proofs as a whole.

The next generic-container reduction found a separate evidence-retention
bug: a certified full-pointer read equation can normalize to address equality
when its designation and bounds already match. The temporary-read retention
helper recognized only the unsimplified full-value equation and dropped the
address equation. It now retains either exact producer conclusion, without
adding object authority or a consumer-specific fallback. The kernel
regression checks uncertified evidence, branch isolation, and distinct
object designations; scaling covers 8/16/32/64 equations and up to 256
unrelated facts. The container proof still has a separate mismatch between
its logical read and its fold-computed child argument; this increment does
not claim to finish that proof or the migration.

The next isolated increment connects direct pointer reads to the existing
width-specific observation registry and refreshes a selected read when its
recorded sources change. A reverse observation-to-name index retains older
observations after a name is reused. These are structural definition edges,
including pointer designation and extent; no facts are folded into lowered
terms. The regression registers both endpoints before the later definition
arrives, then checks existing and fresh graphs, with a partial-write negative
control. Scaling covers 8/16/32/64 observations and 0/16/64/256 unrelated names.

In the WIP, the explicit child-pointer rewrite now gets past the container's
child-tail argument check, but a generic payload read still fails across two
projected snapshots. The ordinary scaling selection also finds a separate
pre-existing migration failure in
`checked_child_read_definitions_scale_with_exchanges_not_ambient_facts`;
the saved pre-fix and candidate binaries have identical failing work counts.
The migration is not green, and its remaining fixture and acceptance audits
have not been rerun for this increment.

The child-resource scaling defect is now reduced to empty memory-index setup:
a temporary opening context discarded the caller checkpoint. Once the index
held two memory cells, the following fold replayed unrelated caller equality
history from the root. The reduced test grows from 1,248 to 13,536 work units
with 256 unrelated equalities before the fix. Resource opening now captures
the caller's closed graph when its memory input is empty, and the index keeps
that one selected checkpoint through later empty setup. Its empty payload is
refreshed without retaining arbitrary old views or scanning resource history.

The migration's complete ordinary scaling selection plus the new context
isolation regression passes (973 tests). The isolation control checks that a
weaker caller cannot consume memory using an alias held only in the opening
context. Lowering and the free/frame rules are unchanged. This repairs the
scaling blocker; it does not complete the generic-payload frame proof or the
migration's remaining fixture and spellability acceptance work.

### Decision: the free decides its frame from proven separation

The user chose the executor to require separation, with the step recording
ownership-supported before/after read equalities in the equality graph.
The process must be deterministic and indexed, looking one step back; no
history scan per query and no fact-aware fallback inside individual checks.

The investigation found a stale cache entry, but no false verification:

- A helper returning `p + 2` for an `int32*` gives an interior alias eight
  bytes into the allocation. Reading through it before `free(p)` verifies;
  reading after the free is refused for missing read authority. See
  `an_interior_call_alias_can_be_read_before_free.md` and
  `an_interior_call_alias_cannot_be_read_after_free.md` in `mdtests/`.
- The kernel reproduction `free_retires_a_cached_interior_alias` showed that
  `free_heap_block` nevertheless kept a cached value under a symbolic
  `q == p + 8` spelling. The same-offset test in
  `heap_allocation_may_contain_pointer` did not identify this interior alias.
  Cache retention therefore cannot be used as the walk's separation rule.

The first increment requires complete-cell ownership in the checked residual
frame before keeping an uncertain cached cell. The step has already consumed
the allocation’s complete ownership and checked the resources that survive;
its residual owners are separate from the consumed bytes by construction.
`owned_memory_member_covering_access` selects a cell’s owner through the
address-class access index. Unknown cells are forgotten; structurally distinct
blocks remain untouched. The allocation-status helper is not a separation
authority.

The migration checkpoint records supported pointer-cell frame equalities at
the free step, with deterministic full-step scaling coverage. That increment
has not landed; remaining container and concrete recursive-drop failures must
be resolved before the pointer-read migration is green.

### Also tried, and why it was dropped

- **A fallback in each check.** `pointers_proven_equal_for_memory_resolution`
  resolved a read through the fact-aware walk. It made `allocation(self.head)`
  match, but only because it used the cache of a snapshot where the walk
  stopped at an edge it could not cross. The codebase deliberately refuses
  that: see the comments in `checked_pointer_read_endpoint_and_kind` and
  `graph_for_memory_query` about weakened contexts. A fallback in each check
  is also the scattering that
  [fact-aware-frame-walks.md](fact-aware-frame-walks.md) forbids.
- **Frames written in the proof.** `have self.head == at(region(120).exit,
  self.head)` closes the allocation. The follow-up
  `have self.head.next == at(region(120).exit, self.head.next)` does not
  close by `solve`.

## Other remaining work

- **Known fact-dependent lowerings** (see
  [Spellability](../docs/internals/spellability.md#lowering-is-fact-stable)):
  comparisons folded to constants, decided guards and disjuncts dropped, and
  comparison kinds chosen by known provenance. `CLICK_FACT_STABILITY=<path>`
  with `scripts/fact-stability.sh` lists the current ones over the mdtest
  corpus.
- **Naming at introduction.** Call results are done. Havoc values,
  allocations, and states between recorded points still print as
  placeholders in some reports. `scripts/spellability-census.sh` finds them.
- **Syntax for missing fact kinds.** Writability, and the memory a step may
  change (the census "no syntax" gap).
- **The total speller.** Replace the premise speller's search and its
  fallbacks with spelling by construction (the census "writable but not
  found" gap).
- **Enforcement.**
  - A census ratchet: the count of written-step misses may only fall.
  - A test-build assertion that `lower(raise(x)) == x` holds for every fact
    a checked step adds.

## Acceptance criteria

- `complete_pointer_read_value` and the stored-pointer fold in
  `Pointer::loaded` are deleted. The generic-stack, generic-container,
  recursive-drop and trait-object Charon fixtures verify unchanged, or with
  frame steps the user accepts.
- `scripts/fact-stability.sh` reports no differences.
- The spellability census reports no misses for written steps, and a
  ratchet test keeps it there.
- A test-build assertion checks `lower(raise(x)) == x` on every fact a
  checked step adds.
- No stepping scaling regression: the frame work above keeps stepping
  linear in the number of statements.


### Copied root extents and example checkpoint

The arena refusal after address-class discovery was in the shared typed range
matcher: a read has an opaque extent, while a held heap-root range has a known
extent with no opaque name. A full pointer-value equality now connects that
read extent to the graph's root-extent tag. Numeric address equality alone does
not; a bounded subobject remains distinct. Lookup uses the selected extent
class, with deterministic tests for growing alias chains and unrelated facts.

`a_copied_heap_pointer_retains_its_root_extent.md` reproduces the refusal on the
pointer migration before this fix and verifies afterward. On the migration,
`arena` and `owned-vector` now pass. Explicit proof links also make the other
six previously failing examples pass individually, without C or contract edits;
those proof changes remain on the migration branch. This is not a full migration
acceptance verdict. The full census and fact-stability audit remain in progress.

The isolated extent fix passed `scripts/check.sh`: 6,672 unit/API/import/scaling
tests and all four fixture aggregates, in 14m20s while a separate audit ran
concurrently (report-only budget warning). No nightly suite ran.

### Complete pointer frames at their producers (2026-10-28)

The stored-read definition and comparison prerequisites have merged (#2098,
#2099), followed by cold pointer-domain query registration (#2100). The last
fix passed 6,693 tests and all four fixture aggregates; fresh domain queries
no longer depend on a preceding address query.

The free now publishes complete before/after pointer-value equalities for
cells its own retention pass kept using checked residual ownership. The pass
collects these cells while making the existing retention decision. Their
names remain structural; the graph learns the frame only from the step's
facts, and restricting those facts withdraws its authority.

A typed C read using a scalar cache also needs to preserve the complete
pointer's domain. On the rebased migration, the unchanged generic-stack and
recursive-drop `pop` proofs failed to fold the remaining node even though a
redundant `have self.head == old(self.head.next)` repaired them. The numeric
address was already equal; an eight-byte read's domain was missing its frame
across an earlier store. The read now selects its already-computed structural
boundary, checks that one edge with indexed complete-byte separation, and
emits the full pointer-value equality. It does not walk history or add a
resource-check fallback. Four-byte ownership does not justify this frame.

These producer changes close the three Rust failures exposed by rebasing the
migration onto #2099 without further edits to its Rust proofs. The two
generic-container controls also pass. Reduced tests cover a partial overwrite,
missing or partial ownership, and harmless later stores hiding the relevant
boundary. Deterministic tests cover consecutive frees including fact insertion,
read-frame chains, and unrelated owners. The logical-lowering switch and the
full spelling/fact-stability acceptance audit remain separate work.


The first frame gate passed all 6,700 unit/API/import/scaling tests, then
`arena` exposed an existing resource-index counter underflow. The reduced repair
is PR #2101 (auto-merge requested): retain an immutable graph checkpoint matching
the payload, and register changed suppliers' definitions before applying merge
deltas, including removed suppliers. Its full gate passed 6,696 tests and all
four fixture aggregates in 9m26s. Two small regressions distinguish query-time
registration from removal-time registration; deterministic scaling covers both.
The repaired frame branch verifies `arena`; its full gate is being rerun.
