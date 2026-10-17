# Nightly pointer-theorem loop audit rejects its original fixture

Soundness: incomplete. The nightly audit regression fails while verifying
its original proof, before it can check pointer-theorem expansion or audit
any site. This reproduction does not demonstrate acceptance of a false
claim. It may be fixture drift rather than a verifier defect.

Reproduced at cf6c2c6928e32fcaa1742ebf0b130f5c688af058, with production
code at 9a4314b814c80d440020e94a95967aa8300d5390, using Rust 1.98.1
and the ordinary unoptimized test profile:

```sh
RUST_MIN_STACK=8388608 cargo test --bin click \
  audit::tests::loop_expansion_preserves_match_pointer_theorem_arguments_and_audits_every_site \
  -- --exact --include-ignored --nocapture
```

The unchanged test in src/bin/click-audit/tests.rs reads
mdtests/rb_ascending_walk_to_root.md, adds ptr_self and ptr_equal theorems
and calls inside the loop's match arm, and removes
`initialize by simp();`. Its first whole-original verification fails:

```text
the original loop must verify before expansion:
execution proof traversal at statement(0) is missing prerequisite
(loop has neither a safe exit nor a safe iteration): false == true
C statement at rb_ascending_walk_to_root.c:4:5:
while (parent != 0) { … }
```

The reported claim is rb_root_of.contract, tactic 0 (loop).
The failure occurred in about 2.3 seconds, without exhausting a budget.
It was observed while assessing a performance optimization; that candidate
was restored completely and its failed baseline was excluded from all
timing savings.

Investigate the original proof's initialization and preserve path before
changing the verifier. Keep the existing C program and both pointer-theorem
argument patterns. If the test's removal of initialization is stale, repair
the fixture explicitly rather than weakening the audit.

Acceptance: the named test verifies its original, expands with both
`apply(ptr_self(identity))` and
`apply(ptr_equal(identity, parent))` retained, and audits every inventoried
site with its existing verification and fixed-point checks.
