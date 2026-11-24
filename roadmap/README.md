# Roadmap

## P1: before launch (5)

The launch covers C, C++, and Rust, with Linux rbtree as the main
demonstration. Reproduced false acceptances are P1.

- [Verify the pinned Linux rbtree implementation](rbtree-example.md)
- [Ship Rust on both launch hosts and support crates with dependencies](rust-support.md)
- [Deliver a Rust language baseline that ordinary small crates meet](rust-language-baseline.md)
- [Finish the smart-tactic checking and search boundaries](smart-tactics.md)
- [Finish the KernelTerm / SurfaceTerm split](kernel-term-split.md)

## P2: after launch (1)

- [Eliminate quadratic work in simple checking](scaling.md)

Use feedback from real projects to prioritize additional work after launch.

## Maintaining the roadmap

Each file here is one roadmap item: a missing feature, design gap, deferred
work, or milestone. Agents must not create new roadmap items unless the user
explicitly asks them to. Discovering a roadmap gap during other work is not
authorization; report it to the user instead. This applies to missing
features, design gaps, deferred work, and new milestones, even when another
document recommends filing one. Defects with a reproduction are not roadmap
items. Defects found through the proof-repair skill go to GitHub issues
after user approval, including during internal development. Other internally
discovered defects go in [`bugs/`](../bugs/README.md), which also requires
asking the user first. Defects reported by Click's users are GitHub issues too.

When requested, use one `.md` file per independent open problem. Each item
contains a small intended regression, the violated invariant, and acceptance criteria. Delete
an item when its fix, regression coverage, and documentation land. Do not
leave the only reproduction in an uncommitted example, and do not quarantine
a regression (in `tests/mdtests.rs` or `tests/examples.rs`) without a
corresponding item here.

Policy lives in the docs, not here: `AGENTS.md` for when tooling failures
block feature work and the user-authorization rule for new roadmap items, the
[proof-failure triage guide](../docs/concepts/proof-failure-triage.md) for
classifying a failure before filing (including the smart-versus-simple
tactic rule), [Testing Click](../docs/internals/testing.md) for
quarantine, profiling order, and the expansion workflow, and
[Verification Efficiency](../docs/internals/verification-efficiency.md) for
the complexity contract and scaling-regression policy. Proposals without a
failing deterministic curve are not open roadmap items; when the user requests
one, scope it narrowly to the evidence.

Every roadmap item states `Priority: P1.` or `Priority: P2.` directly under its
title. Directly under that, a `Soundness:` paragraph gives one label and a
written argument for it. A bug in [`bugs/`](../bugs/README.md) puts the
`Soundness:` paragraph directly under its title. The labels are:

- `unsound`: Click can verify a claim that is false for the program built for
  the named target. The paragraph gives the reproduction, or an argument that
  a false claim verifies.
- `incomplete`: Click refuses, or cannot state, something true. No false
  acceptance is known.
- `soundness-adjacent`: no false acceptance is known, but there is a trust or
  model gap a reviewer would ask about. Examples: a modeled assumption that
  differs from the real toolchain, a meaningless claim that Click accepts
  with a Click-specific meaning, or a check that holds only because another
  rule happens to enforce it.
- `not soundness`: features, tooling, documentation and performance.

A suspected false acceptance stays `soundness-adjacent` until it is
reproduced. To move a file off `unsound`, the reproduction must stop
verifying. Narrowing the documented claim does not count. Re-check the label
whenever the file's reproduction or scope changes.
