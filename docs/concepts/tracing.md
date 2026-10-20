# Tracing a failed proof

This page is the procedure for repairing a failed proof from its diagnostic
and `--trace-proof` output: find the goal that could not be proved, prove it
through explicit intermediate goals, and stop at one of six outcomes. It
replaces trial-and-error tactic variation with a decomposition that each
attempt must advance.

[Proof-failure triage](proof-failure-triage.md) classifies a failure once it
is understood. This page is how you come to understand it.

## Every proof error has a goal

Click reports four kinds of error. Only a proof error enters this procedure.

| Error kind | What it means | What to do |
| --- | --- | --- |
| `syntax error` | The sidecar does not parse. | Fix the source at the reported line. |
| `type error` | The sidecar parses but does not elaborate. | Fix the named declaration. |
| `internal error` | The verifier failed. | Reduce and report it ([outcome 2](#outcomes)). |
| `proof error` | A checked operation could not establish something. | Follow the procedure below. |

A proof error names its **goal**: the proposition that had to be true at a
program point and was not proved there. A goal can come from an `ensures`
clause, a written `have`, a call's precondition, a definedness requirement such
as the absence of signed overflow, or a memory access. The report prints it on
a `goal:` line. Whatever its source, a goal is proved the same way: by `auto`
when the proof is omitted, by an implicit `auto` when `step()` or `execute()`
leaves a requirement open, or by explicit tactics you write.

A goal is read in the state where it is required. A requirement of a C
statement is a goal at that statement's pre-state, so an explicit proof can
prove it just before the statement, with a `have` or a step's `requires`
entry.

## Getting a trace

Read the ordinary report first. It gives the goal, the branch facts, and the
failing tactic. When the goal alone does not explain the failure, rerun the
command the report prints under `To get a trace:`:

```text
click verify --trace-proof PROOF SIDECAR
click verify --trace-proof PROOF --trace-to LINE SIDECAR
```

`PROOF` is the function, theorem, or tactic name, and `SIDECAR` is the
`.click` file. `--trace-to LINE` stops at the written tactic on that line, even
in a proof that succeeds; use it to see the facts available at a point where
you intend to write a `have`.

The trace lists each checked step on the failing path and the facts it added
(`adds:`), then a `failed check` section with the goal, the resources held,
and the available premises. Those premises are what an explicit proof of the
goal can use. [Reading trace output](#reading-trace-output) describes the
notation.

## The procedure

1. **Record the goal.** Write down the failing goal `G`, the program point
   where it is required, and the premises available there. If the report has
   no `goal:` line, or you cannot read it, stop at outcome 2.
2. **Decide whether `G` is true.** Check it against the contract, the branch
   facts, and the C semantics. If it is false on some execution the contract
   admits, stop at outcome 6.
3. **Write the argument.** State why `G` follows from the premises as a chain
   of intermediate goals: the premises imply `A`, `A` implies `B`, and `B`
   implies `G`. Write each link as a `have` at the program point, so the proof
   checks it. If you cannot state the argument, stop at outcome 3. If you
   cannot write one of the intermediate goals in Click, stop at outcome 4.
4. **Run it.** The first link that fails is the new `G`. Return to step 1 with
   it.
5. **Refine a link that does not close.** A link `A implies B` that `auto`
   does not prove is too big. Split it into smaller links, `A implies C`,
   `C implies D`, `D implies B`, and run again. Stop splitting when a link is
   a single simple tactic: one `apply`, `unfold`, `step()`, rewrite, or
   arithmetic step. If that simple tactic is refused, stop at outcome 5.

Before each run, say in one line which link is new and why it should hold.
Changing a tactic, its spelling, or its position without changing the chain is
not a new attempt. Do not edit `auto`, raise a budget, or change the C to get
past a link.

## Outcomes

The procedure ends at exactly one of these:

1. **Proved.** The proof verifies. Keep the explicit links that `auto` needed;
   they document the argument.
2. **Diagnostic defect.** The failure has no `goal:` line, the goal cannot be
   read (for example, it is spelled with placeholders such as
   `<unnamed A>` that no proof can name), or the refusal is not "goal `G` was
   not proved". Reduce it to a small sidecar and file it in `bugs/`, or report
   it.
3. **No argument.** You cannot say why `G` holds. Report `G`, the premises,
   and what you tried; a person or a stronger prover must supply the idea.
4. **Inexpressible intermediate goal.** The argument needs a fact Click cannot
   write: a missing predicate, quantifier form, memory spelling, or resource
   form. Report the intermediate goal in mathematical form and the reduced
   sidecar. This is missing functionality.
5. **Refused simple step.** Every link is written, and one link is a single
   named simple tactic that should apply but is refused. Report the link, the
   tactic, and its refusal. This is a verifier bug or a missing rule.
   "`auto` did not prove it" is never outcome 5: it means the link is still
   too big.
6. **False goal.** `G` does not hold on some execution: give the
   counterexample. The fix belongs in the contract or the C, not the proof.
   Do not weaken a claim or add a precondition on your own; report the
   counterexample and the proposed change. A false goal can also mean the C
   has a bug.

Outcomes 2, 4, and 5 are tool problems: preserve a reduced reproduction.
Changing the verifier, its diagnostics, or its tactics in response requires
the maintainer's approval, except for a reproduced bug in existing behavior.
Outcomes 3 and 6 go to the person you are working for.

## Worked example

`frame` returns one more than the product its callee computes:

<!-- verified-example: mdtests/tracing_a_nonlinear_bound_is_the_refused_goal.md -->
```c
int area(int w, int h) { return w * h; }
int frame(int w, int h) {
    int inner = area(w, h);
    return inner + 1;
}
```

<!-- verified-example: mdtests/tracing_a_nonlinear_bound_is_the_refused_goal.md -->
```click
int32 frame(int32 w, int32 h) {
    requires w >= 0 and w <= 1000;
    requires h >= 0 and h <= 1000;
    ensures result == w * h + 1;
}
```

With `area`'s contract stating `result == w * h` under the same bounds, the
omitted proof's `auto` is refused. The report ends with the goal and how to
prove it (abbreviated):

```text
proof error:
  `frame.ensures_0` tactic 0
  `execute()` produced undefined behavior
  signed overflow
  ...
  `return inner + 1;`

tactic: step
  ...
goal: inner <= 2147483646
help: to prove the goal explicitly, step to this statement and prove it there with `have <goal> by { ... }`
```

1. **Goal.** `inner <= 2147483646` before `return inner + 1;`. The trace's
   failed check lists the bounds on `w` and `h`, and the call step added
   `inner == w * h`.
2. **True?** Yes: `w * h` is at most `1000 * 1000`.
3. **Argument.** `inner == w * h`, `w * h <= 1000000`, and `1000000 <=
   2147483646`. The middle link is the one `auto` did not derive, because it
   is nonlinear.
4. **Write it.** Step through the declaration and the call, then state the
   link:

<!-- verified-example: mdtests/tracing_an_intermediate_goal_proves_the_bound.md -->
```click
    ensures result == w * h + 1 by {
        step(); step();
        have w * h <= 1000000 by auto();
        execute();
    }
```

The proof verifies: outcome 1. Had `have w * h <= 1000000 by auto();` been
refused, it would be the new goal, to split further, for example through
`w * h <= 1000 * h`.

## Reading trace output

An explicitly requested `--trace-proof` keeps its typed diagnostic notation:
readable Click expressions are used there only when they preserve the checked
operands, and otherwise a memory operand prints as
`read<Bits64>(snapshot#1, pointer=value#1)`, in an added fact just as in a goal.
The width, snapshot, and address remain visible even when the source wrote only
`parent->__rb_parent_color`.

Within a trace, goals, requirements, and traced facts share names and snapshot labels. A bounded legend defines
generated addresses and snapshots, including immutable proof names, pointer-read
constructions, pure pointer calls with their typed arguments, byte offsets,
and memory constructions with their inputs. Pure-call arguments retain model
identities and read snapshots; nested pointer arguments have their own legend
definitions. These constructions explain labels and add no proof evidence. An
initial empty memory is an explicit root. Other snapshots describe a recorded
transition or an internal transformation, such as projecting a source memory
for a particular pointer read, substituting a variable, or joining branch
memories. Read projections name their source snapshot and pointer. Seeded cells
name their source and stride; call and loop effects show their write footprints
when those are specified. Recorded marks and program points appear in these
definitions when they match the snapshot.

A memory-history explanation identifies a blocking store, its snapshot, and the
checked read range and write width. Its result is retained at failure time, so
formatting does not repeat the check under a different verification context.
This diagnostic walks recorded memory history
without using the proof context's equality and ownership facts. Failure to show
separation in that walk does not mean the proof has no separating evidence.
Subsequent transitions mentioned by the explanation are memory transitions, not
necessarily C statements.

Construction records travel with snapshots across threads and are excluded from
memory equality and proof evidence. A missing record on a noninitial snapshot is
reported as an internal recording defect, not a normal unknown origin. New memory
constructors must retain their operation and inputs; snapshots changed without
updating their record must not inherit an old explanation. Referenced labels are
expanded within the report budget, with display omissions explicit. Source marks
and program points are used only for matching snapshots, never guessed from nearby
statements. These definitions describe constructions, not additional checked
equalities or a complete execution history.

Each trace addition uses `adds:` followed by the same proposition form used
for `goal:` and requirements. Typed diagnostic notation is used wherever a
source expression would hide checked identities. This includes pointer and scalar equalities,
viewability with byte extents, model/function equalities, resource containment,
validated resource-composition entries, and distinct volatile-write events.
Internal notation is not promised to be valid Click proof input. Read types,
read snapshots, arithmetic widths, and signedness remain visible. Resource
compositions list up to eight entries with ownership quantities or view access;
omitted entries and support details are explicit. A write event records an
access, not an equality about the current memory contents.

Only the new facts at each checked step are printed, not the accumulated set.

A failure trace also ends with a separately labelled `failed check`. It retains
the refusal, checking stage, proof context, up to sixteen available premises,
and up to twelve resources from the retained C state, even when the first operation fails before a checked step can
be recorded. For postcondition failures, current-state names and resources come from the
selected outcome; permissions consumed by a call are not shown as still held.
The failed check is not an accepted execution step. A proposition
proof has a fixed execution state; an execution tactic refused there names that
restriction rather than implying that the tactic is unavailable everywhere.
When an explicit script ends with a goal still open, its failure retains the
checked prefix and the remaining goal and premises after those steps, rather
than the state at script entry. This includes execution `have` bodies and pure
theorem scripts.

Written `simp` failures retain a bounded sample of the read-value queries and
cell walks actually performed during that attempt. Ordinary errors summarize
up to two observations of each kind and eight available premises; traces show
up to sixteen observations of each kind, with shared
snapshot and address labels, access widths, stopping reasons and query modes.
These records include speculative search queries and are not additional proof
facts or a claim that one observed stop explains the entire search failure.
A check with no instrumented memory query says so in its trace. The capture
limit bounds diagnostic storage and does not stop or change verification.
Supplemental memory-history explanations are labelled separately: their walk
does not use the failing check's equality or ownership context. Actual query
observations retain the context's result without rerunning it while printing.

A loop-closure search error names its unresolved obligation from the member
planner or the retained focused goal, including when that search exhausted its work budget.
If no individual obligation was retained, the diagnostic says that the failure
applies to the bundle search. A budget refusal reports an unfinished proof
attempt; it does not establish that the named obligation is false.

A failed pointer-valued resource child argument comparison reports the exact
supplied and required values and the argument position. Up to four explicit
equalities sharing the supplied value may be shown as potentially relevant
evidence. That selection is diagnostic guidance, not a claim about the cause
of failure or a prescription for the missing proof. The comparison uses the
same value and snapshot labels as the preceding trace facts.
These details are diagnostic only and do not add equalities or change proof
checking.
