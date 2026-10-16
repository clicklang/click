# A loop clause grows with the loops before it

A `loop { decreases ...; invariant ...; }` clause over one small loop costs
work that grows roughly quadratically with the number of earlier loops in the
function, so a function of N sequential loops is roughly cubic: 64
four-iteration loops take 47 seconds.

Reproduced on master `e28770b20` with `scripts/step-scaling-hunt.py`:

```c
int32 caller(int32* p) {        /* owns p[0..4] */
    int32 i;
    i = 0;
    while (i < 4) { p[i] = 0; i = i + 1; }
    i = 0;
    while (i < 4) { p[i] = 1; i = i + 1; }
    ...                          /* N loops */
    return 0;
}
```

each proved by `step(); loop { decreases 4 - i; invariant i >= 0;
invariant i <= 4; }`.

```sh
python3 scripts/step-scaling-hunt.py loops --sizes 4,8,16,24
```

The last loop clause charges 4,460, 15,054, 58,704 and 132,304 units at
N = 4, 8, 16 and 24 (2.6 s for that one clause at N = 24). At N = 64 the 52nd
clause alone took 51 s and the run hit the ten-minute bound.

Diagnosis (master `b769df57d`): each loop leaves facts about its own copy
of the loop variable on the path (`0 <= i_j`, `i_j <= 4`, `!(i_j < 4)`), and
nothing drops them when `i = 0` makes that copy dead. All of them meet at
the constant bound `4`. Deciding a later loop's `i < 4`,
`has_lower_bound_above` takes every `i_j` filed under `4` as a candidate
lower bound and decides `i_j > i` for each, so a decision makes one
candidate decision per earlier loop, and each of those runs the decision
procedure's rules over the whole path.

Partly fixed: the order walk those decisions run (`has_order_path`) read
every order fact at every node it reached, and walks from the same source
repeated the same exploration. It now reads the edges filed under the
node's equality-graph class (`TransportEdgeIndex`) and shares a source's
reachable states (`TransportReach`). Charged work is unchanged (the scan
charged nothing for the facts it read), but N = 32 verifies in 6.6 s
instead of 70 s, and N = 64 verifies in 47 s where it hit the ten-minute
bound.

What remains: the clause still makes one candidate decision per earlier
loop, and each still runs other per-decision rules that read the whole
path (`has_condition_fact`'s scanned fallback, the 64-bit order-fact
scan), so a clause's work and
time are still about quadratic in the earlier loops. Indexing those rules
would leave the candidate count linear; a constant clause needs the dead
copies' facts not to be candidates at all, for example by retiring facts
whose terms nothing live mentions.

The direct-equality constant lookup no longer scans the path at every
equality hop. It reads a persistent adjacency index of the exact written
int32 equality endpoints. With 16, 64, 256 and 1,024 unrelated equality and
order entries, two queries inspect three relevant edges and charge six
units at every size. This removes that individual ambient scan; it does not
remove the growing lower-bound candidate count or close this bug.

The quadratic part is gone. Simple checking no longer calls the general
decision (see "Condition decisions in simple checking" in
`docs/internals/verification-efficiency.md`), so no candidate lower bounds
are decided. The largest loop clause now charges 1,847, 2,485, 3,759 and
5,031 units at N = 4, 8, 16 and 24, about 160 per earlier loop. A trace of
deterministic work at N = 8, 16 and 24 puts that growth in two places:

- About two thirds rebuilds fact contexts from the path's propositions
  (`assumptions_from_propositions` at the loop's preservation proof, its
  state join, and `have` lowering), which re-registers every earlier loop's
  facts in the equality and difference graphs
  (`register_expression_operands`, `TermClasses::root`,
  `retain_signed_int32_interval`, `DifferenceGraph::tighten`).
- The rest was per-loop scans of the whole function's C source. These now
  run once per function. The address-taken locals and the loop list are
  computed once in the termination check
  (`many_ranked_loops_in_one_function_cost_linear_termination_work`). The
  loop step reuses the claim's source layout, which keeps the address-taken
  locals and the local pointee types. The largest loop clause now charges
  1,732, 2,262, 3,320 and 4,376 units at N = 4, 8, 16 and 24, about 132 per
  earlier loop.

The fact-context rebuilds are now mostly gone. A loop step's `have`
lowering, the back-edge join (`check_loop_state_join` and the preservation
join) and the exit-condition lowering now read the context their fact list
or proof already keeps (`PureFactList::context`, `ProofFacts`), extended by
the step's own facts. The loop step also builds the path list's context and
transport context once, before its executions copy the list. The largest
clause now charges 1,388, 1,566, 1,920 and 2,272 units at N = 4, 8, 16 and
24, about 44 per earlier loop.

The `loop` tactic no longer rebuilds what the proof keeps. It copied the
path's facts into a flat list and then built two things from every fact: the
list's direct-transport context, and the initialization proof's indexed
`ProofFacts`. The proof now keeps the transport context once a loop asks for
it, extending it as facts arrive (`ProofFacts::with_direct_transport_assumptions`),
and the list carries the `ProofFacts` it was copied from, which the
initialization proof and the automatic preservation body extend by the
loop's own facts (`PureFactList::from_proof_facts`, `proof_facts`). The order
the list presents facts in was never the obstacle: a context is the facts
it assumes, and the list already kept the proof's main context in the same
way. `sequential_loops_build_the_same_context_entries_each` counts every
context entry built, charged or not, at 3, 6 and 12 loops: 80 per loop at
both steps, where either rebuild makes the count grow.

Two kernel scans grew with the loop rules. Each `loop` tactic builds an
environment holding every earlier loop's verified rule, and adding a rule
reset the environment's variable index, so the next statement collected the
variables of every rule again, each rule's whole required context included.
Each rule now indexes its own variables once, shared by its clones, and the
environment's index of its other parts survives adding rules
(`adding_a_loop_rule_collects_only_that_rules_variables`). Finding the rule
for a loop also checked every rule's required context before comparing its
loop statement; it now compares the statement first.

The largest loop clause now charges 1,484, 1,596, 1,820 and 2,268 units at
N = 8, 16, 32 and 64. At N = 5 the clauses charge 1,442, 1,351, 1,353, 1,357
and 1,359, which the gate holds flat
(`sequential_loop_clauses_cost_the_same_at_every_position`). N = 64 verifies
in 1.0 s instead of 1.6 s, and N = 192 in 5.6 s instead of 15.2 s.

The last charged growth is gone. Preparing a loop head restored the entry
state's block table over the havocked one by re-inserting every block,
which gave the table a new root even when nothing changed, so the
comparison with the head state that follows walked every block the path
had declared. It now writes only the blocks that differ
(`SnapshotMap::overwrite_with`, which walks the paths the two tables do not
share), and the comparison is constant. Clause work at N = 64 now runs
1,347, 1,351, 1,353, 1,355, 1,355, 1,355 and 1,357 across the loops: what
remains is the logarithmic depth of the head's memory-history comparison
(`record_c_memory_derivation`). The largest clause, 2,266 at N = 64, is the
first: it pays once for claim-wide setup proportional to the function, and
no later clause pays it again. `sequential_loops_build_the_same_context_entries_each`
now also holds the last of twelve clauses to the second's work; the old
restore made it 1,375 against 1,351.

Each loop step also copied the whole grouped proof: binding the loop's
clause copied the function block, and the block held the claim's whole
proof script, two tactics per loop. The block now shares it. N = 192
verifies in 5.3 s instead of 5.7 s.

What remains is uncharged time linear in the earlier loops at each loop, so
the 192nd loop clause takes about 40 ms where the second takes 14 ms:

- Collecting the variables of the whole path context, for fresh-variable
  reservations: once when a loop's rule first joins an environment
  (`collect_verified_loop_rule_variables`), at the loop head's fresh locals
  (`statement_kernel_variables`), and for the preservation contexts
  (`c_loop_preservation_contexts_with_mode`); about 8% of N = 192. An exact
  fix keeps a variable index beside the context's facts.
- Applying the loop's verified rule checks its whole required context,
  which is the path's context at the loop (`applicable_verified_loop_rule`).
- The loop step copies the path's facts into flat lists
  (`PureFactList::from_proof_facts` and its clones) and every earlier rule
  into its environment, and re-annotates the whole function
  (`annotated_function_with_assumptions`, about 0.5 ms at every N).

Acceptance: a multi-size regression over `loops` shows each loop clause's
work and time constant in the number of earlier loops, up to logarithmic
factors; each loop's invariants and termination are still checked; no budget
or threshold is raised.
