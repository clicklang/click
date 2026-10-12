# SMT-backed automation with kernel-checked certificates

Priority: P1.

Proof size, automation and proof workflow are the parts of the
[launch design review](design-review.md) that matter most. Its items P1–P4,
W4 and W5 depend on this issue. This issue makes `simp`, `arithmetic` and
`auto` call an SMT solver to find proofs, and makes Click turn each solver
result into a certificate that the kernel checks. This is the "hammer" pattern
used by Isabelle's Sledgehammer, SMTCoq and Lean's `omega`/`linarith`.

## Violated invariant

Click's priorities are, in order:

1. C, C++ and Rust;
2. uncooperative existing code;
3. fast verification of large files without trial and error.

The third priority is not met. Today `by auto;` means exactly
`execute(); simp();`, and `simp` is a heuristic normalizer with fixed limits
("up to eight variables", "nested at most twice",
`docs/reference/tactics/index.md`). Several kinds of reasoning are done by
hand:

- linear arithmetic, transitivity chains and width bridges are written out
  step by step;
- facts that `simp` cannot find are restated in `using { ... }`;
- `arithmetic_certificate` blocks are written out by hand.

The result is that proofs are 6–120 times the size of the C they verify
(design-review item P1), and getting a step through takes trial and error.
SMT-based tools such as Dafny and Verus do this reasoning without being
asked. Click can do the same while keeping its rule that only the kernel
decides a verdict.

## Design

The solver only searches; it never decides. A step is accepted only when its
reconstructed certificate checks in the kernel, as every smart tactic's
expansion does today.

- **Flakiness and slowness affect search only.** Once a certificate exists,
  checking it is fast and deterministic. The solver runs again only when the
  cached certificate no longer checks, for example after the C or the
  specification changes.
- **Failure decomposes.** When the solver gives up, the author splits the
  goal with `have` or a case split, and each piece goes back to `auto`.
  Click executes C one step at a time, so its queries are small and local.
  Dafny-style verification instead sends one large formula per method.
- **The proof stays inspectable.** `click expand` prints the reconstructed
  certificate.

## Stages

Do the stages in order. Each stage is useful on its own.

1. **Arithmetic and equality oracle.**
   - For linear integer arithmetic, the solver returns Farkas coefficients.
     Click's `arithmetic_certificate` steps (`premise`, `scale`, `add`) are
     already Farkas proofs, so the translation is direct.
   - For equality, congruence closure returns a path of rewrites, which Click
     emits as `rewrite` steps.
   - The oracle sits behind `simp` and `arithmetic`.
2. **Premise selection from the unsat core.** The solver reports which
   premises it used. Click fills in `using { ... }` itself, so authors no
   longer restate propositions to cite them. This removes most of the need
   for named facts (design-review P4).
3. **Certificates outside the sidecar.** The source keeps saying `by auto;`.
   The reconstructed certificate is stored in a cache or lock file next to the
   sidecar, like the existing import locks. `click verify` checks the cached
   certificate and, on a miss, searches again within a work budget. Sidecars
   stay small, and unreadable expansions stop being committed (design-review
   W4). Per-claim caching also speeds up large proofs (design-review W5).
4. **Mathematical integers in specifications** (design-review P2). Solvers
   handle unbounded linear integer arithmetic well and machine-width
   arithmetic poorly. Unbounded specification integers help both the solver
   and the author.

## Out of scope

- Full reconstruction of solver proofs that use quantifiers. Start where
  certificates are simple.
- Induction and recursive resource predicates. These stay in the tactic layer
  (`fold`, `unfold`, induction), because solvers are weak at them.

## Risks

- **Reconstruction is the main engineering cost.** Stage 1 limits it to
  Farkas and congruence certificates.
- **Click would ship a solver binary** (Z3 or cvc5) and pin its version.
  Solver output must not affect a verdict except through a checked
  certificate.
- **Search must stay bounded.** A solver call runs under a deterministic work
  or time budget, and the call fails locally and promptly when the budget is
  exhausted. A slow solver run is a tooling failure under `CLAUDE.md`, not a
  successful slow run.
- **Scaling.** Each query must be built from the explicit premises and the
  affected proof state, never from project-wide or path-wide state
  (`docs/internals/verification-efficiency.md`).

## Regression

Prototype stage 1 behind `simp` and `arithmetic`, then measure the change in
proof size and verification time on three cases:

- `examples/rust-byte-sum`, the loop and arithmetic case;
- `examples/bounded-pool`, the overflow-bridging case (about 270 lines of
  `arithmetic_certificate` today);
- one `examples/rbtree-erase` case file, the scale case.

Rewrite each case to rely on the oracle, while keeping the C unchanged. Add
mdtests for:

- a linear-arithmetic goal proved by `simp` with no hand-written certificate;
- a congruence goal proved the same way;
- a goal the solver cannot prove, which fails promptly and boundedly with an
  actionable diagnostic.

## Acceptance criteria

- `simp` and `arithmetic` prove linear integer arithmetic and congruence goals
  through the solver. Every accepted step is justified by a kernel-checked
  certificate, which `click expand` prints.
- Verification with a warm certificate cache does not call the solver, and its
  verdict is deterministic.
- A solver timeout, crash or wrong answer can only cause a local, bounded
  failure. It can never cause acceptance.
- The three regression cases shrink, and the measured sizes and times are
  recorded in this file. If they do not shrink substantially, record that,
  and rule on stages 2–4 before continuing.
- `docs/reference/tactics/index.md` describes the oracle, its budget and the
  certificate cache.
