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
decision (`issues/difference-logic.md` step 4), so no candidate lower bounds
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

What remains is the context built at each `loop` tactic from the proof's
facts (`PureFactList::from_source` in `apply_frontier_local_loop`). Its
transport context, and the initialization proof's `ProofFacts`
(`for_fixed_state`), are built from every path fact. They cannot be carried
as a prefix, because an execution proof's statement steps put their
transported facts ahead of the ambient ones (`ProofFacts` prioritized
batches), so the list arrives at each loop in a new order. The loop step
also re-annotates the whole function (`annotated_function_with_assumptions`,
`to_kernel_function`). That work is charged nothing, so it shows only in
time. Building `ProofFacts` fact by fact from a kept prefix was tried and
cost more than the full build.

The gate records the drift: `known_drift_sequential_loop_clauses` in
`src/scaling_tests/surface/tests/step_shape_scaling_tests.rs` fails once the
clauses stop growing, and then becomes an ordinary no-drift test.

Acceptance: a multi-size regression over `loops` shows each loop clause's
work and time constant in the number of earlier loops, up to logarithmic
factors; each loop's invariants and termination are still checked; no budget
or threshold is raised.
