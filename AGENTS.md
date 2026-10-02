# Working on Click

## Develop in a fork and contribute through pull requests

The upstream repository is `clicklang/click`. Humans and agents must develop
in their own fork and open a pull request against upstream `master` as soon as
they have a coherent, green, reviewable unit of work. Do not wait for a larger
effort to finish; use a draft pull request if more work is expected before it
is ready to merge. Do not push development branches or changes directly to the
upstream repository, even with write or admin access. Maintainers integrate
reviewed changes through pull requests.

Each task thread, whether a human working session or one agent, has at most
one open pull request at a time. While it is open, add each further coherent
green increment to that same branch and pull request, even when the increment
is a different chunk of the effort or an unrelated fix found along the way, and
describe each increment in the pull request body. Do not open a second pull
request, and do not stack pull requests on one another. Once the thread's pull
request merges or is closed, start later work from current upstream `master` on
a new branch and pull request. A thread that opens many pull requests floods the
merge queue, which merges one at a time, and turns every failure low in a stack
into a blocked chain.

Upstream `master` requires a pull request, a passing GitHub Actions `test`
check, and the merge queue. The queue runs `scripts/check.sh` on the prospective
upstream tree and merges one pull request at a time. Do not merge directly or
bypass the queue.

### Lacker and agent merge-queue loop

Use this preferred path when Lacker is working with an agent authenticated to
GitHub as `lacker` and has authorized the agent to deliver the change. Other
contributors follow the normal PR and review process.

1. Before follow-up work, inspect the thread's PR. If it is still open, add
   the new work to that PR, whatever it is. If it merged, create a new PR for
   the new work.
2. Make a coherent change and use judgment to choose useful local checks. A
   full `scripts/check.sh` run is not required before every PR; report the
   checks that did run.
3. Push the branch to the fork and create or update the PR against upstream
   `master`.
4. Immediately request **Merge when ready**, even while checks are running:
   run `gh pr merge <PR> --auto`. GitHub records the request and puts the PR
   into the merge queue once its requirements pass. Do not wait for CI to
   finish before requesting this. The **Allow auto-merge** repository setting
   must be enabled; it is enabled on `clicklang/click`.
5. Once GitHub confirms the request, continue with the next work without
   waiting for the check or merge to finish.
6. On the next update, inspect the PR again. Update the same open PR and run
   `gh pr merge <PR> --auto` again if needed: a push to a PR in the merge queue
   takes it out of the queue until its checks pass again. If it merged, open a
   new PR.
7. If checks fail, a conflict appears, or GitHub removes the PR from the
   queue, resolve the problem, update the PR, and register the merge request
   again. Then continue with the next work.

If GitHub reports that auto-merge is not allowed, report the repository
setting as a blocker to the maintainer; do not wait for CI as a workaround.
Never use `--admin`, merge directly, or bypass required checks or review rules.

Use `origin` for the contributor's fork and `upstream` for
`git@github.com:clicklang/click.git`. Set `remote.pushDefault` to `origin`
and `push.default` to `current` so ordinary pushes go to the fork even when
a local branch tracks upstream. Verify the push destination before pushing;
do not assume an existing checkout's `origin` is a fork. See the
[contribution workflow](docs/internals/contributing.md#fork-and-pull-request-workflow)
for setup commands.

## Isolate work from the primary checkout

Unless already operating in a task-specific worktree, create a dedicated Git
branch and worktree before editing files. Perform implementation, experiments,
formatting, tests, and commits there. Treat the shared primary checkout as an
integration checkout, not a development workspace; do not expose other agents
to partially implemented or failing changes.

Submit coherent changes and use judgment to select useful local checks. A full
local `scripts/check.sh` run is not required before every pull request; PR CI
and the merge queue run the full gate. For prose-only changes, the focused
documentation gate is available. Report which checks ran in the pull request.
If upstream has moved, update the task branch and rerun affected checks before
merging.

If updating the local primary checkout after a pull request merges, verify
that it is clean and fast-forward it from upstream with Git. Never copy
uncommitted files into it or merge an unreviewed task branch into upstream
`master`. Stop and coordinate if unrelated changes prevent the update.

Before integrating tested work into a local branch in the fork, run the relevant
focused and full gates in the task worktree, verify that the primary checkout
is clean, and confirm that its base has not moved unexpectedly. If the base did
move, update the task branch and rerun any affected gates before integration.
Move the tested commit into the primary branch with Git rather than copying
uncommitted files. Never overwrite unrelated changes in the primary checkout;
stop and coordinate if it is dirty or integration conflicts.

Keep failed prototypes and incomplete investigations confined to their task
worktree. Restore or replace them with a green checkpoint before committing,
and do not merge or push them to the primary branch. These rules always apply.

Run long-running Git operations that move `HEAD`, such as `git bisect`, in a
throwaway worktree rather than the one holding the change. Bisecting in place
leaves the task worktree on an unrelated commit and turns a routine stash pop
into a conflict against the wrong base.

## Judge green from `scripts/check.sh`

`scripts/check.sh` is the gate, and CI runs exactly that script so the two
cannot drift. Decide pass or fail from its exit status.

Never decide from piped `cargo test` output. A shell pipeline reports its last
command's status, so `cargo test | tail` exits 0 while the suite is failing;
this is how a broken mdtest survived 54 commits undetected. Piping is fine for
reading output, but the verdict comes from an unpiped run. The default `cargo
test --lib` is also not the gate: it passes while both proof-fixture gates
fail.

## File bugs freely; create issues only when the user explicitly asks

`bugs/` and `issues/` are different lists with different rules.

**Bugs: file them without asking.** A bug is a defect in what Click already
claims to do, with a reproduction. Humans and agents should file one whenever
they find one and do not fix it in the same change:

- the verifier accepts something false, or refuses something the
  documentation or a neighbouring case says it supports;
- a tool crashes, hangs, exceeds a budget without a prompt local failure, or
  disagrees with another tool (`verify`, `expand`, `audit`, `profile`);
- a diagnostic is inaccurate or misleading: it names the wrong construct,
  suggests a command or syntax that is then rejected, or reports a cause
  that is not the cause;
- a diagnostic is a wall of text: repeated or unbounded raw internal state
  where a bounded, actionable message belongs.

File one kebab-case `.md` file per independent bug in `bugs/` plus a one-line
entry in `bugs/README.md`. State the violated invariant, a small intended
regression, and acceptance criteria, written so a fresh agent can act on the
file alone. Reproduce it first: an observation that was seen once, or inferred
from reading code, is reported to the user, not filed. Tell the user what was
filed. Delete the file and its list line when the fix, its regression
coverage, and any documentation land.

**Issues: only the user approves them.** An issue is roadmap: a missing
feature, a design gap, deferred work, a new milestone, or a change of
direction. Do not create new issue files or new issue-list entries unless the
user explicitly asks you to. Finding such a gap is not authorization to file
one; report it to the user instead. A general request to implement,
investigate, or fix something does not implicitly authorize new issues, and
neither does another document that recommends filing one. Do not file
roadmap work in `bugs/` to avoid this rule: when it is unclear whether
something is a bug or an issue, report it to the user.

When requested, create one kebab-case `.md` file per independent problem in
`issues/` plus a one-line entry in `issues/README.md`, with the same three
parts as a bug. Delete the file and its list line when the fix, its
regression coverage, and any documentation land.

## Existing C is the verification boundary

Click exists to prove properties of existing C programs. Adoption in a large
codebase must not require refactoring working implementation code into a shape
the verifier happens to prefer. For C inside Click's supported semantics, a
true claim that cannot yet be proved is a Click language, model, or tooling gap.
It is not permission to weaken, specialize, reroute, or cosmetically rewrite
the C until the proof passes.

Treat C source as fixed when adding a sidecar or repairing a proof. Put the
adaptation in contracts, lemmas, resources, tactics, lowering, or the kernel.
In particular, do not add no-op branches, proof-only locals, redundant
assignments, specialized helper calls, or alternate control flow to expose a
friendlier proof state. Do not change identifier spellings to avoid a lowering
or snapshot bug.

A C change is in scope only when it is independently desirable as a program
change, fixes an actual C bug or undefined behavior, or is a documented
semantics-preserving translation into the currently supported C0 subset. Keep
the original source as the regression whenever verifier work exposes a gap.
Synthetic examples may be small, but they must not be presented as evidence
that Click handles an awkward source pattern that the example has edited away.

## Tooling stability comes first

Verifier and proof-tooling problems block feature and example work. Stop the
current feature when any of these occurs:

- verification is unexpectedly slow or crosses a tactic budget without a
  prompt, local failure;
- a smart tactic reports success but its generated certificate does not verify;
- `click expand` fails, emits an unverifiable rewrite, or disagrees with
  `click profile` or `click audit`;
- a normal diagnostic expands into a huge repeated raw internal-state dump;
  bounded user-approved goal, premise, and search context is useful and
  should be retained, while repeated raw memory snapshots remain a defect; or
- an example needs unnatural C or irrelevant proof bookkeeping to route around
  verifier behavior.

Smart-search failure is expected when it is prompt, bounded, and actionable.
It is not a reason to stop feature work or modify shared heuristics. Prefer a
smaller smart tactic or an explicit sequence of relevant simple steps. Search
completeness is a non-goal; sound certificate validation, enforced bounds, useful diagnostics,
and sufficient simple tactics are requirements.

Reduce and fix the tooling problem before resuming feature work. If it cannot
be fixed in the same coherent chunk, report the blocker and a proposed
regression to the user, then restore the worktree to a green, check-in-ready
checkpoint. File it in `bugs/` when it is a bug; create an issue only if the user
explicitly asks. Do not silently
work around the problem, raise time limits, accept a slow successful run, or
leave the only reproduction inside an
unverified example.

After any timeout or interrupted bounded command, confirm that its verifier
process tree exited before trusting later timing results. Stale workers are a
tooling failure, not background noise.

Do not build Click workflows by recursively spawning Click commands, hidden
child modes, test-binary wrappers, stderr scraping, or shell redirect/move
recipes. CLI subcommands and fixture gates should call the shared bounded
verification engine directly. Keep OS process isolation only as a narrow,
owned crash-containment boundary.

This priority is deliberate: Click's examples and language features depend on
fast verification, checkable certificates, working expansion, and actionable
diagnostics. Building above a broken proof-tool boundary makes later failures
harder to interpret.

Establish correctness before performance optimization. Run ordinary
verification first; when it reports a prompt proof failure, repair that proof
before profiling or expanding it. Profile a non-verifying target only when a
timeout or unexpected slowness is itself the tooling problem being diagnosed,
and treat that result as an incomplete diagnostic frontier, not an
optimization profile. Never expand a tactic from an incomplete run.

See `issues/README.md` for issue policy and
`docs/concepts/proof-failure-triage.md` for failure classification, and
`docs/internals/testing.md` for the performance and expansion workflow.

## Scalable verification is a correctness requirement

A project written entirely with explicit simple tactics must verify in work
approximately linear, up to logarithmic indexing factors, in the selected C
source, Click source, and certificate. A simple tactic may do work
proportional to its explicit input, the affected C operation, and the proof
state or certificate delta it produces. It must not scan or clone unrelated
project-wide or path-wide state.

Do not introduce complete-environment clones per function, complete-state or
history clones per tactic, linear exact-premise searches, eager pairwise
derived facts, or caches keyed by deep structural comparison on a verifier hot
path. Smart-tactic expansion removes search; it is not a remedy for a slow
simple checker.

Performance-sensitive representation changes require deterministic scaling
regressions over multiple input sizes. A fixed corpus timing or a faster warm
run is supporting evidence, not proof of acceptable asymptotic behavior. The
canonical complexity contract, output-sensitive exceptions, and review rules
are in `docs/internals/verification-efficiency.md`.
