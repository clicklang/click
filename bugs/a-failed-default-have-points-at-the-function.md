# A failed `have P;` points at the function, not the `have`

## Violated invariant

A refused tactic's diagnostic names the tactic and points at its source
location. A `have P;` with no written proof, or `have P by solve();`, whose
search misses is reported as "`solve` failed for `f.contract`: could not
establish `P`" with the source pointer on the function's first line. The
`have` that failed is not located. Before `auto` was removed from the parser,
`have P by auto();` ran the same search and was refused at the `have`, as
"`f.contract` tactic N: `auto` could not prove `P`"; that path
(`source_have_error` in `src/surface/proof/checked_drivers/proof_execution.rs`)
is now reachable only from an internal `SourceProof::Tactic(SmartTactic::Auto)`.

## Reproduction

`f.c`:

```c
int helper(void) { return 1; }
int f(void) { int x; x = helper(); return x; }
```

`f.click`:

```click
verifying "f.c";
int32 helper() { ensures result == 1; }
int32 f() { ensures result == 1; } by {
    step();
    step();
    have x == 2;
}
```

`click verify f.click` prints the `solve` refusal with `--> f.click:3:1`, the
line of `int32 f()`, rather than line 6. The same happens on master before the
removal of `auto` (with `simp` in place of `solve`).

## Intended regression

An mdtest whose `have` fails by search, expecting a message that names the
`have`'s tactic index or position, for example "tactic 2", next to "could not
establish `x == 2`".

## Acceptance criteria

- A search miss of `have P;` and of `have P by solve();` is refused at the
  `have`: its message names the tactic, and the source pointer is on the
  `have`'s line.
- The checked prefix in its trace is unchanged
  (`have_failure_trace_retains_checked_call_prefix` in
  `src/surface/tests/diagnostic_tests.rs`).
