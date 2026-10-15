# A work-budget stop during C parsing is reported as a syntax error

Soundness: not soundness. The diagnostic labels a budget stop as a
syntax error. The verdict is correct, because the run did stop, and no
proof result is affected.

The C parser's cooperative checkpoint (`checkpoint` in
`src/languages/c/syntax.rs`) turns an exceeded run budget into a
`C0SyntaxError` whose message starts "C parsing stopped:". With a
deterministic work limit, the CLI prints that as a syntax error with the
kind `syntax error`, even though the source parses.

On master `7f2047bfd`:

```sh
click verify --work-limit 1 mdtests/scalar.md
```

```text
syntax error:
  failed to parse C source `scalar.c`
  scalar.md:7
  C parsing stopped
  the run exhausted its deterministic whole-run work budget after 2 units (1 limit) while running external dependency summary > source resolution phase; ...
```

`click audit --claim scalar.arithmetic_result --verification-work-limit 1
mdtests/scalar.md` prints the same thing under the failed claim, with
`error kind: syntax error`.

The crash-containment form of the same stop (`--time-limit 1ms`) is
presented as "click verify was stopped after ..." instead (see the test near
`src/bin/click-verify.rs:2675`). So only the deterministic work-budget path
mislabels it. A user, or a harness that keys on the error kind, is told to
look for a syntax error in valid C.

The violated invariant is that a diagnostic names its actual cause
([bugs/README.md](README.md): inaccurate or misleading diagnostics).

## Acceptance criteria

- A work-budget stop during C parsing reports a budget or limit error kind,
  not `syntax error`, and does not begin with `syntax error:`. The
  remaining message, naming the budget and the phase, is kept.
- A regression runs `click verify --work-limit 1` on a valid one-function
  source and checks the error kind and heading. The existing time-limit
  test keeps passing.
