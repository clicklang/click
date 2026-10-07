# The project verdict accepts `extern` contracts that sibling sidecars contradict

## Violated invariant

`click verify <project-directory>` reports `verified N sidecars in 1 project`
and exits 0 only when every selected claim holds. A verified C function's
claim includes termination (`docs/concepts/what-click-proves.md`, "Termination
is part of the claim"). Within one sidecar the kernel/surface enforce this:
mutual recursion without `decreases` is refused
(`could not certify termination for f`), and declaring `extern` a function
that a `verifying` source of the same sidecar defines is refused
(`src/surface/verification.rs:6531`, "external function `g` is also defined by
a `verifying` source").

Across sidecars of one project neither check runs. Each sidecar treats the
other sidecar's function as an `extern` assumption, so two sidecars can
assume each other's contracts and the project verdict accepts both. The
project verdict then asserts two functions terminate and return 42 when
neither terminates. The same gap lets a sidecar assume a *false* `extern`
contract for a function that another sidecar of the same project verifies
with a different (true) contract; the project verdict still exits 0.

Responsible code: `src/bin/click-verify.rs:325` (`verify_directory`) verifies
each sidecar independently; `verify_c0_project` /
`c0_project_summary` (`src/surface/verification.rs`) summarise external
dependencies per sidecar only ("external assumptions: f -> g") and never
reconcile a sidecar's `extern` declarations against definitions and contracts
verified by sibling sidecars. Termination certification
(`src/kernel/termination.rs`, `c_verified_function_termination_rules`) ranks
only calls whose callee has a body in the sidecar; an `extern` callee is
assumed to return.

## Reproduction

Circular shape, four files in one project directory:

```c
// a.c
int32 g(int32 x);
int32 f(int32 x) { return g(x); }
```

```c
// b.c
int32 f(int32 x);
int32 g(int32 x) { return f(x); }
```

```click
// a.click
verifying "a.c";
extern int32 g(int32 x) { ensures result == 42; }
int32 f(int32 x) { ensures result == 42; } by { execute(); simp(); }
```

```click
// b.click
verifying "b.c";
extern int32 f(int32 x) { ensures result == 42; }
int32 g(int32 x) { ensures result == 42; } by { execute(); simp(); }
```

The second shape in full:

```c
// a.c
int32 g(int32 x);
int32 f(int32 x) { return g(x); }
```

```c
// b.c
int32 g(int32 x) { return x; }
```

```click
// callee.click
verifying "b.c";
int32 g(int32 x) { ensures result == x by auto; }
```

```click
// caller.click
verifying "a.c";
extern int32 g(int32 x) { ensures result == 42; }
int32 f(int32 x) { ensures result == 42; } by { execute(); simp(); }
```

Observed:

```
$ click verify <project-dir>
external assumptions: f -> g
2 selected proofs verified
verified .../a.click
external assumptions: g -> f
2 selected proofs verified
verified .../b.click
verified 2 sidecars in 1 project
$ echo $?
0
```

`f(x)` and `g(x)` never return. Putting both functions in one sidecar is
refused (`could not certify termination for f: the recursive call to g is
ranked by no function-level decreases measure`), and declaring `g` `extern`
in a sidecar that also verifies `b.c` is refused.

Second shape, a contradicted assumption: `caller.click`
verifies `a.c` (`f` calls `g`) and declares `extern int32 g(int32 x) { ensures
result == 42; }`; `callee.click` verifies `b.c` where `g` returns `x` with the
verified contract `ensures result == x`. `click verify <project-dir>` exits 0 with `verified 2 sidecars in 1
project` although `f`'s `ensures result == 42` is false and the project itself
contains the verified contract that contradicts the assumption.

## Intended regression

A test in `src/bin/click-verify/incremental_tests.rs` (or a project fixture
under `tests/`) that builds both directories above and asserts that
`click verify <dir>` exits nonzero, naming the `extern` declaration that a
sibling sidecar defines (and, for the first shape, the unranked cross-sidecar
recursion `f -> g -> f`).

## Acceptance criteria

- Directory verification reconciles every `extern` contract declared by one
  sidecar against the functions defined by the project's `verifying` sources:
  a definition exists in the project and its verified contract is identical
  (or the declaration is refused the way `src/surface/verification.rs:6531`
  refuses it within one sidecar).
- Termination certification treats a call to a function defined elsewhere in
  the project as a call with a body: cross-sidecar recursion without a
  ranking is refused, or the project verdict explicitly reports the claim as
  conditional and exits nonzero.
- Both project shapes above exit 1; `examples/multifile-registry` and existing
  multi-sidecar fixtures are unaffected (they use `verifying` for every
  definition rather than `extern`).
- The `external assumptions:` line stays for genuinely external (undefined in
  the project) functions.
