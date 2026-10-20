# Resource tactics after function exit get the generic driver error

Soundness: not soundness. Each step is correctly refused; the defect is the
message. The documented reason, that the tactic must run before execution
reaches function exit, is never shown; the user gets the catch-all "no checked
proof driver accepts this proof script's shape" text, whose advice (remove
tactics from the end, `outcomes`, `have`) does not describe the problem.

The violated invariant: a refusal that the reference documents with a specific
reason reports that reason. The [tactic
reference](../docs/reference/tactics/index.md) lists "After the function exit:
take before `execute()` reaches the exit" for `take`, `give`, and `gather`,
and "At function exit (after `execute()` or the last `step()`), `mark` is
refused". The checked steps already have the specific text:
`src/surface/proof/proof_object/resource_steps.rs` builds
"`{name}` must run before execution reaches function exit" (line ~2091) and
"`observe` must run before execution reaches function exit" (line ~2174), but
those errors do not reach the user for `take`, `gather`, `observe`, or `mark`.
(`unfold` after `execute()` is accepted, as documented for a function
outcome, so it is not a control here.)

```c filename=o.c
int f(int *p) { return p[0]; }
```

```click
resource cell1(p: int32*) {
    owns p[0..1];
    fact p[0] >= 0;
}

verifying "o.c";

int32 f(int32* p) {
    owns cell1(p);
    ensures result >= 0;
} by {
    execute();
    observe(cell1(p));
    simp();
}
```

`click verify` prints:

```text
proof error:
  `f.contract`
  no checked proof driver accepts this proof script's shape for these 2 contract claims
  `f.owns_0: cell1(p)`, `f.ensures_0: result >= 0`, and none reported a tactic it refused. No listed claim was shown false. To find the tactic no driver supports here, remove tactics from the end of the script until it is accepted. Every terminal path must establish every listed claim. If `step()` reaches a maybe-throwing call, use `outcomes { returned => { ... } threw => { ... } }` to handle its two successors. For proposition-only work, move the operation into `have proposition by { ... }`.

tactic@13:
  observe(cell1(p));
refused by: `observe` (simple: a refusal within its documented behavior is a bug)
see: click docs observe
```

Replacing `observe(cell1(p));` with `mark done;` prints the same generic text
pointing at `mark done;` with `refused by: \`mark\``. Moving either step
before `execute();` verifies.

The same happens for `take` and `gather`:

```c filename=t.c
void f(int *data, int *occupied, int capacity, int index) { }
```

```click
resource cells(data: int32*, occupied: int32*, capacity: int32) {
    owns occupied[0..capacity];
    forall (k: int32) where 0 <= k and k < capacity {
        if occupied[k] == 0 {
            owns data[k..k + 1];
        }
    }
}

verifying "t.c";

void f(int32* data, int32* occupied, int32 capacity, int32 index) {
    owns cells(data, occupied, capacity);
    requires 0 <= index; requires index < capacity; requires occupied[index] == 0;
} by {
    unfold(cells(data, occupied, capacity));
    execute();
    take(data[index..index + 1]);
    give(data[index..index + 1]);
    fold(cells(data, occupied, capacity));
    simp();
}
```

prints the generic "no checked proof driver accepts this proof script's shape
for the contract claim `f.owns_0: cells(data, occupied, capacity)`" text at
`take(data[index..index + 1]);`. Moving `execute();` after the `fold`
verifies. For `gather`, with the same resource and C file, the contract

```click
void f(int32* data, int32* occupied, int32 capacity, int32 index) {
    requires 0 <= capacity;
    owns occupied[0..capacity];
    owns data[0..capacity];
    requires forall (k: int32) { 0 <= k and k < capacity implies occupied[k] == 0 };
} by {
    execute();
    gather(cells(data, occupied, capacity));
    scatter(cells(data, occupied, capacity));
    simp();
}
```

gets the same generic text at the `gather`; with `execute();` moved to just
before `simp();` it verifies.

## Acceptance criteria

- Each reproduction (`observe`, `mark`, `take`, `gather` after `execute()`)
  prints a message naming the tactic and saying it must run before execution
  reaches function exit, pointing at that tactic, without the generic driver
  paragraph.
- `give` and `scatter` after exit get the same specific message.
- Regressions keep each source pattern: the tactic written directly after an
  `execute()` that reaches function exit.
