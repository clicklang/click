# Named-contract `step` hint maps a produced handle

Soundness: not soundness. Every step below is refused or accepted correctly;
the defect is a hint that tells the user to write a spelling Click refuses.

The violated invariant: a refusal's suggested spelling is one the same tactic
accepts. For a contract with a `consumes` handle and a `produces` handle,
`step(Repair)` suggests `step(Repair, { input: ..., output: ... })`, mapping
both handles. Writing that is refused because a produced handle must be
introduced by a `let` pattern, as [named contracts with resource
bindings](../docs/reference/tactics/index.md#named-contracts-with-resource-bindings)
documents. The accepted form is
`let { output: done } = step(Repair, { input: dirty });`. The hint is built in
`src/surface/proof/proof_object/execution_statements.rs` (around line 1127)
from every named parameter, without separating `produces` handles.

The second refusal is also mislabeled: it is printed as a `syntax error` and
points at the contract declaration instead of the `step` line.

```c filename=r.c
void indirect(int (*callback)(int *), int *x) { callback(x); }
```

```click
verifying "r.c";

resource Dirty(p: int32*) { field value: int32; owns p[0..1]; fact p[0] == value; }
resource Ready(p: int32*) { field value: int32; owns p[0..1]; fact p[0] == value; }

contract int32 Repair(int32* p) {
    consumes input: Dirty(p);
    produces output: Ready(p);
    ensures output.value == 1;
}

void indirect(int32 (*callback)(int32*), int32* x) {
    requires Repair(callback);
    consumes dirty: Dirty(x);
    produces done: Ready(x);
    ensures done.value == 1;
} by {
    step(Repair);
    execute();
    simp();
}
```

`click verify` prints:

```text
proof error:
  contract `Repair` declares resource handles; write `step(Repair, { input: ..., output: ... })` with one instance for each of `input`, `output`

tactic@18:
  step(Repair);
refused by: `step` (simple: a refusal within its documented behavior is a bug)
see: click docs step
```

Following the hint, `step(Repair, { input: dirty, output: done });` prints:

```text
syntax error:
  z.click:18
  `Repair` produces `output`; introduce it with `let { output: name } = step(...)`

  --> z.click:6:1
  6 | contract int32 Repair(int32* p) {
    | ^^^^^^^^
```

(with the `.click` file's own name in place of `z.click`).
`let { output: done } = step(Repair, { input: dirty });` verifies.

## Acceptance criteria

- The `step(Repair)` refusal suggests
  `let { output: ... } = step(Repair, { input: ... })`: the map lists only
  the non-`produces` handles and the `let` pattern names every `produces`
  handle. With no `produces` handles, the hint is unchanged.
- Substituting names into the suggested spelling verifies for the
  reproduction.
- The produced-handle-in-map refusal is a proof error pointing at the `step`
  line, not a syntax error at the contract.
- A regression keeps the source pattern: a function-pointer contract with one
  `consumes` and one `produces` handle, stepped with a bare `step(Repair)`.
