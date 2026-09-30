# Contributing to Click

## Fork and pull request workflow

Humans and agents contribute through a fork of
[clicklang/click](https://github.com/clicklang/click). Develop in your fork and
open a pull request against upstream `master` when the change is ready. This
also applies to maintainers with write or admin access: push development
branches to the fork, and integrate reviewed changes through pull requests.

For a new checkout, create a personal fork on GitHub, then run these commands.
Replace `YOUR_GITHUB_LOGIN` with the fork owner's login:

```console
git clone git@github.com:YOUR_GITHUB_LOGIN/click.git
cd click
git remote add upstream git@github.com:clicklang/click.git
git config remote.pushDefault origin
git config push.default current
git fetch upstream
git worktree add -b codex/your-change ../click-your-change upstream/master
cd ../click-your-change
```

Use `origin` for the fork and `upstream` for the organization repository. In an
existing checkout whose `origin` points to `clicklang/click`, rename that
remote to `upstream` and add the fork as `origin` before pushing. Verify both
destinations with `git remote -v`. The push settings above send ordinary
pushes to the fork even when a local branch tracks upstream. Agents use the
`codex/` branch prefix by default; humans can choose a descriptive branch name.

Perform edits, experiments, tests, and commits in the task worktree. Keep the
shared primary checkout clean. Follow the isolation and tooling rules in
[AGENTS.md](https://github.com/clicklang/click/blob/master/AGENTS.md).

Before submission, run focused checks and `scripts/check.sh` unpiped. For
changes limited to prose or documentation metadata, use
`scripts/check.sh --docs-only`. Commit a coherent passing change, then push
the task branch to the fork:

```console
git push -u origin HEAD
```

Open a pull request on GitHub from that fork branch to `clicklang/click`'s
`master`. Describe the problem, the resulting behavior, and validation. Keep
review updates on the same fork branch. If upstream moves, update the branch
and rerun affected checks before merging. After the pull request merges,
fast-forward a clean local primary checkout from upstream with Git.

The test workflow runs on pull requests, including those from forks. Fork
pull requests do not need repository secrets for the test gate; GitHub may
require a maintainer to approve an outside contributor's workflow run. Release
publishing uses version-tag pushes, so opening a pull request does not publish
a release.

## Implementing a change

Most Click changes should start from a proof need, not from an isolated syntax
idea.

The default workflow is:

1. Find the smallest nearby mdtest.
2. Add or change a test that shows the desired behavior.
3. Confirm the expected failure.
4. Implement the smallest parser, lowering, kernel, or prover change.
5. Add unit tests if the change is below the mdtest level.
6. Update the relevant reference entry and public-surface inventory.
7. Run focused tests, then run `scripts/check.sh` unpiped.

The feature playbook is the detailed checklist.

## Where new concepts belong

Prefer this order:

1. An ordinary Click definition in `stdlib/prelude.click`.
2. Deterministic proof support for a general pattern.
3. A new tactic if users need explicit control.
4. New syntax only when existing syntax cannot express the concept clearly.

This keeps the language smaller and makes kernel support more reusable.

## Contributor reading path

If you are changing Click itself, read:

1. [What Click proves](../concepts/what-click-proves.md), for the user-facing
   boundary;
2. the relevant [concept page](../concepts/index.md), for the mental model;
3. the relevant [technical reference](../reference/index.md), for the public
   contract;
4. the [feature playbook](feature-playbook.md), for the change workflow;
5. [Architecture](architecture.md) and [Kernel](kernel.md), for module and
   trust boundaries.

## Documentation ownership

The technical reference, concepts, and internals in this site are intentionally
AI-written and AI-maintained. Keep them factual, exhaustive, source-backed, and
consistent with the local [documentation style](../style.md). Update the
machine-readable inventory or fixture mapping whenever a public surface
changes. The future human-written guide is a separate work with its own voice;
don't move or rewrite it as part of technical-reference maintenance without
explicit authorization.

## Working conventions

- Gate: `scripts/check.sh` is the full green-tree verdict, and CI runs the same
  script for code-affecting changes. Run it unpiped. It covers formatting,
  documentation, library and binary tests, mdtests, and examples, using
  nextest. For changes limited to prose or documentation metadata, run
  `scripts/check.sh --docs-only`; it renders and checks the documentation
  without running unrelated unit or verifier tests. `mdtests/` Markdown is
  executable proof input, so changes there require the full gate.
- Probe pattern: env-gated eprintln/file dumps at the failing check,
  run under a filter, strip probes before committing.
- Bound any new recursive prover arm by the inputs it walks: the term's
  structure, a strictly decreasing snapshot id, or a cycle check on the
  query. Never by a count or a depth cut, which turn a slow query into a
  wrong-shaped answer and defeat memoization. Structural recursion on deep
  terms has overflowed the stack before; the verifier threads carry the
  stack for it, and a scaling regression over several input sizes pins the
  bound.
- SOUNDNESS TRAP: never drop havoc/call-havoc blocks from canonical
  load memories; kernel test
  `memory_load_equality_does_not_ignore_loop_havoc_identity` guards it.
- Reproduce stale timing claims before acting on them; slow-but-passing
  is a reportable finding, not a resting state.
- Known bugs and pending decisions live in `issues/`, one file each.
