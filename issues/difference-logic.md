# Difference logic: the fast path for arithmetic requirements and conditions

Priority: P1.

Soundness: not soundness. This replaces how the kernel decides arithmetic
conditions during simple checking, not what it accepts: every answer is a
consequence of the path's own condition facts by difference-logic rules, the
same facts the current decision reads. The new structure is kernel code and
is held to the same agreement tests as the decision it stands in for.

## Why this is P1

[simplify-step.md](simplify-step.md) requires every simple tactic's
requirements to be closed by a fast path ("an exact or indexed lookup, or a
bounded local kernel decision about the affected operation") or by an
expandable implicit `auto`, and its final step removes the hidden search. It
notes the largest route its census does not count yet: the kernel's own
condition evaluation, which calls the general condition decision
`PureFactContext::decide` on every C comparison, overflow check, and pointer
bound it evaluates. That decision searches the whole path. Removing it needs
a fast path that still answers the ordinary questions; this issue builds it.

## The violated invariant

A simple step's cost must not grow with unrelated path facts
([verification efficiency](../docs/internals/verification-efficiency.md)).
`bugs/sequential-loop-clause-grows-with-earlier-loops.md` shows it does:
each earlier loop leaves facts about its own copy of the loop variable
(`0 <= i_j`, `i_j <= 4`, `!(i_j < 4)`), all meeting at the constant bound.
Evaluating a later loop's `i < 4`, `has_lower_bound_above` takes every `i_j`
filed under `4` as a candidate and runs a nested decision for each, so a loop
clause costs about the square of the loops before it.
[#831](https://github.com/clicklang/click/pull/831) made the order walk
inside those decisions cheaper; the candidates, and the other rules that read
the whole path, remain. The intended regression is that shape:
`python3 scripts/step-scaling-hunt.py loops --sizes 8,16,32,64`, whose largest
loop clause charges 15,094, 58,744, 235,898 and 949,628 units today.

## What the decision is mostly used for

Measured on `cb2bf3c` with a temporary switch that made the executor decide
conditions only by exact lookups and a condition's own form
(`decide_with_facts`, `condition_is_decided`, and the consistency check when a
path fact is added), smart tactics keeping full reasoning, then with a
difference-logic oracle standing in for the general decision:

| Executor decides by | mdtests failing (of 3,853) | examples failing (of 50) |
| --- | --- | --- |
| general `decide` (today) | 0 | 0 |
| exact lookups only | 622 | 28 |
| exact + per-value bounds | 236 | 18 |
| exact + difference logic | 58 | 9 |

No refusal test became accepted under any of them.

Most of the general decision's use is one-step arithmetic about the operation
itself: `i + 1` cannot overflow given `i < 4`, `bytes[index]` is in bounds
given `index < length`, `n - 1` is defined given `0 < n`. Branch pruning is a
small share. All of it is difference logic: constraints `x - y <= c` and
constant bounds.

What the 58 still need:

- Bound tightening at the end of a range: `-x` and `x / y` need
  `x != INT_MIN`, which with `x >= INT_MIN` is `x >= INT_MIN + 1`.
- Shifts by a constant (`x << 1` is `2 * x`), and the range of a narrow type
  (`int8`, promoted `uint8`) as a node's initial bound.
- Bounds of loaded values that come from memory or resource facts rather than
  condition facts (`sum + node->value`).
- Pointer questions (alignment, disequality, deciding a pointer comparison),
  which belong to the equality graph's pointer side, about a dozen.
- Loop-invariant closures that met infeasible paths the weaker pruning left
  in, about eight; not yet diagnosed.

Seven of the nine failing examples are Rust imports, which use conversions
(`usize`, `u64`) the oracle did not model.

## Design

`DifferenceGraph`, beside `EqualityGraph` and keyed by its classes.

- **Nodes** are `int32`, `int64` and `uint64` equality classes. Their values
  are mathematical integers, so nodes of different widths can be related
  (sign extension is an exact link).
- **Edges** are constraints `x - y <= c`. A true order or equality fact is one
  or two edges; a false one is its negation. A constant bound is an edge to
  the zero node, so a constant is never a node: facts about unrelated values
  never meet at a shared constant.
- **Wrapping.** A term `x + k` is linked to `x` (`t - x <= k` and
  `x - t <= -k`) only once `x`'s bounds show the sum cannot wrap. That is the
  same question as the overflow check, answered from the same bounds.
- **Insertion** propagates bounds along the new edge's neighbourhood with a
  bounded worklist, so `x < y` with `y <= 100` records `x <= 99` when it is
  assumed. A negative cycle is a contradiction; a zero-weight cycle is an
  equality, passed to `EqualityGraph`. A merge there merges nodes here.
- **Bounded work.** Propagation, the cycle check and a path query each
  follow at most `EDGE_LIMIT` edges. A value many others are bounded by (an
  array length `n` with `v_i <= n`) then costs the same however many there
  are. A node whose push was cut short is marked, and reading a neighbour's
  interval pulls one hop from marked nodes. Past the limit the graph stays
  sound and answers less: stored bounds remain true, only looser.
- **Queries** are reads: an order or overflow question compares stored
  bounds, and a relation between two values reads their edge or a bounded
  path inside their own component. Neither depends on facts about other
  values.
- **Persistence.** Like the equality graph, it is shared between proof
  branches and extended in work proportional to the delta.

Out of scope: `x + y <= c` between two variables, multiplication and division
of two variables, and other non-linear arithmetic. Those stay with smart
tactics and implicit `auto`.

## Plan

Each step is its own pull request.

1. **The structure (landed).** `DifferenceGraph`
   (`src/kernel/difference_graph.rs`) with insertion, interval propagation,
   wrap-checked links, contradiction detection, and queries for orders,
   equalities and add/subtract/multiply overflow. Nodes are keyed by term;
   an equality is two edges. It is tested on its own and consulted nowhere
   yet: `decisions_hold_in_every_model_and_are_complete` enumerates every
   model of generated bounded fact sets and requires each answer to hold in
   all of them and each entailed order to be answered, and
   `work_is_independent_of_unrelated_bounded_values` pins insertion and
   query work at 2, 0 and 1 units beside 16 to 1,024 unrelated values.
2. **Fast path in condition evaluation (landed).** Each fact context keeps
   its graph (`ContextDifferenceGraph`): assumed condition facts extend it,
   a withdrawn one clears it, and the next query rebuilds it. The kernel's
   condition evaluation (`decide_with_facts`, the path-fact consistency
   check, `condition_is_decided`) asks it after exact lookups and before the
   general decision. The census route
   `HiddenPrerequisiteRoute::KernelCondition` counts what the general
   decision still settles: 2,029 conditions, 96 path facts and 9
   path-fact decisions over the mdtests, and 538 and 24 over the examples.
   Two consequences:
   - The graph answers only the absence of overflow. An arithmetic
     certificate's intermediate sums (`n + 2147483647` in an `add` step) are
     lowered through the C evaluator, which reads an undecided overflow as
     a value; proving such an overflow certain made those lowerings fail.
     Lowering certificate terms as mathematical integers would lift this.
   - Deciding more changes some proofs' shape. A loop's invariant bundle can
     lose conjuncts the graph now settles during evaluation, so a proof that
     spelled them out must drop them (`examples/arena`), as
     [simplify-step.md](simplify-step.md) accepts. An `ensuring` join whose
     arms now prove a term defined from their own bounds is refused at the
     successor instead, which now says the join does not carry that bound.
   - A path fact the graph shows implied is not added to the path, as when
     the general decision showed it. Step 3 has the general decision consult
     the graph, so a reasoner that asks only it still rederives such a fact.
   Indexing by equality class is partial: a fresh name equated to a value
   names that value's node (`many_names_for_one_value_stay_one_node`), and
   an equality between two values that already have nodes is two edges.
   A sum `x + k` whose base's bounds already rule out wrapping names `x`'s
   node at offset `k` (`offsets_of_a_bounded_value_share_its_node`); only a
   sum still waiting on those bounds gets a node of its own.
3. **Close the gap.** Range-end tightening, constant shifts, narrow-type
   ranges, load bounds, and routing pointer questions to the equality graph,
   each lowering that count.
   - *Landed:*
     - Compound sums, differences and products are bounded by interval
       arithmetic over their operands, `x - y` also by the graph's bound on
       the difference, whenever the exact result stays in its domain. A
       compound term that has a node of its own takes the narrower of the
       two intervals.
     - `x != c` is recorded and moves an interval end off `c`.
     - Overflow conditions recorded false are keyed by their operands'
       graph values, so either operand order or another name for an
       operand finds them.
     - Division and constant-count shift overflow are answered.
     - `x ^ MIN`, C's unsigned order spelled as a signed one, is linked to
       `x` once either side's sign is known.
     - A remainder by a constant is bounded by its dividend's sign and the
       divisor.
     - A side with no node of its own is compared by interval.
     - A contradictory graph, meaning a dead path, answers that an overflow
       is absent.
     - A question whose load is spelled as the load itself is also asked
       in canonical form, where the load is its load variable, as the
       facts name it. This settles every path-fact consistency check the
       general decision still made: 96 over the mdtests and 24 over the
       examples.
     - Propagation and path walks are bounded (`EDGE_LIMIT`), and the
       general decision reads the context's graph first when it is built.
       Deciding more there changed four refusals' messages. Three are now
       more specific. A range whose extent guard the context refutes now
       says why it was dropped ("too wide to be a 32-bit byte extent")
       instead of "0 paths". The fourth,
       `call_refusal_names_the_cell_an_earlier_argument_reserved`, now
       reaches its note with `i < j`, because equal indices are refused
       earlier for overlapping owners.
     - Most general decisions had been overflow checks on such terms
       (`(x - y) - 1`, `(0 - x) + 1`). After these changes the census is 48
       conditions and 7 path-fact decisions over the mdtests, and 21 over
       the examples.
     - An offset comparison of `int32` elements is an index comparison.
     - Zero extension (`u32 as i64`, `Int64FromUInt32`, `UInt64FromInt32`)
       links to its operand when that is non-negative, and lands in
       `[0, 2^32)` otherwise. Unsigned division by a positive divisor is
       bounded by interval.
     - Pointer equality facts form classes with known-unequal classes inside
       the graph (`p == null`, `q != null`, so `p != q`). Two pointers of one
       block are equal exactly when their offsets are, so the offset question
       the kernel asks for `p == q` is answered from them. `EqualityGraph`
       has no disequalities, which is why this lives here.
     - The fast path also asks the context's keyed pointer disequality rule
       (`decide_pointer_disequality`: null-ness by offset, separation by
       anchor pair), which searches nothing. The `path facts` site asks the
       merged context's fast path before the general decision, so a
       comparison's assumed two-owner composition is read there.
     - After these, the census over the whole mdtests is 32 conditions and
       no `path facts` decisions, measured on master `d7501d30f` with
       `branching_graph_dfs` masked. That fixture now explicitly retains
       its old child-index bounds and passes in the full corpus.
   - *Tag bits:* the graph tracks known low bits of 64-bit values
     (`x ≡ r mod 2^k`) from `x & (2^k - 1) == c` facts and 64-bit
     equalities. Residues survive the wrapping sums a tagged word is built
     from, scaled offsets contribute `0 mod 2^tz(w)`, and `addr(p + o)` is
     `addr(p) + o`. A 64-bit word equality the graph leaves open goes to the
     existing pointer-tag rules (`decide_pointer_word_equality_citing`),
     whose leaves then ask only the fast decisions. With the general
     decision dropped, every mdtest and example the assessment listed now
     verifies, except the tag-free `rbtree-augmented` guard below.
   - *Left:*
     - a sum bounded by its guard, `a <= INT_MAX - b`, which is not a
       difference constraint. Simple checking deliberately does not
       rediscover it: `explicit_nonnegative_add_definedness_certifies_the_whole_contract`
       requires the lemma `int32_nonnegative_add_within_max_is_defined`.
       `rbtree-augmented` relies on the general decision for it;
     - certain overflows, which the graph does not answer.
   - *Landed after the assessment:* a narrow integer cast (`int8`,
     `uint8`, `int16`, `uint16`, `int32` as `int32` values) links to its
     operand once their intervals leave one multiple of the modulus between
     them, so `(int8) v == -56` with `0 <= v <= 255` gives `v == 200`. An
     unsigned `a - b` with `b <= a` is at most `a`, which bounds a non-empty
     suffix. The fast path asks the keyed disjunction rule for division
     overflow (`divide_overflow_excluded_by_disjunction`).
4. **Remove the general decision from simple checking.** A condition the fast
   path leaves undecided keeps both branches, and an arithmetic requirement it
   leaves open goes to implicit `auto`, as
   [simplify-step.md](simplify-step.md) decides. Rerun the corpus, migrate the
   proofs that change, and close the loop bug.
   - *Assessed* on master `fefd3ac92`, by dropping every general decision at
     the kernel's condition sites (`decide_with_facts`, path fact, path
     facts, loop condition): 20 of about 4,006 mdtests and 5 of 54 examples
     failed. Every failure was a refusal, and no test expecting a refusal
     passed. Conversions and pointer equality (above) have since cleared
     8 of the 20 mdtests and 3 of the 5 examples. The rest are listed under
     *Left* above. The `step` refusals among them ("got 2 feasible condition
     paths") are expected under this phase, which keeps both branches.
   - *The loop bug is not in these sites.* With every kernel-site general
     decision dropped, `scripts/step-scaling-hunt.py loops` charges the same
     4,598 / 15,260 / 59,046 / 132,782 units at N = 4 / 8 / 16 / 24. 93% of
     that time is the smart `loop` clause's own search, which calls
     `PureFactContext::decide` directly. Closing the bug means changing what
     that search asks, or having it read the difference graph, in addition
     to this phase.

## Acceptance criteria

- Simple checking decides arithmetic conditions and requirements without
  `PureFactContext::decide`; the census of such decisions is zero.
- The `loops` shape's largest loop clause is constant in the number of
  earlier loops at four sizes, as a deterministic regression.
- Insertion and query work in `DifferenceGraph` is constant in unrelated
  facts at four sizes.
- Generated-case tests show `DifferenceGraph` never decides a condition the
  facts do not entail.
- `scripts/check.sh` passes, `bugs/sequential-loop-clause-grows-with-earlier-loops.md`
  is deleted, and `docs/internals/verification-efficiency.md` describes the
  structure.

## Not in scope

- Non-linear arithmetic and relations between sums of variables.
- Completeness of implicit `auto` for what the fast path leaves open.
