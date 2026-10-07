# A nested loop with an inner `break` is refused under concrete execution

## Violated invariant

`break` and nested loops are both documented C0 and both are executed
concretely by `execute()` when the loops carry no annotations
(`docs/concepts/loops-and-invariants.md`). A single loop with a `break` and
nested loops without one both verify. Nesting the two is refused with an
internal message:

```text
`execute()` recorded condition evidence the proof object rejected
condition evidence was recorded with no source statement remaining
```

The message names no source construct and suggests nothing; it is a
proof-object consistency check failing, not a verdict about the program.
The refusal is independent of where the inner counter is declared, of
whether the `break` is braced, of the trip counts, and of whether `auto` or
`execute(); simp();` drives the proof. The condition evidence that is
rejected is presumably the inner guard or the `break` condition recorded
after the inner loop's `break` has left the body with no statement left on
the inner frontier, while the outer loop's step still expects one; the
responsible code is the concrete loop route in
`src/kernel/eval/statements.rs` (`execute_c_while_paths`) together with
`record_condition_transition` / `check_condition_evidence` in
`src/kernel/proof/execution.rs`.

## Reproduction

```c filename=nb.c
int32 f(int32 x) {
    int32 i = 0;
    int32 s = 0;
    while (i < 3) {
        int32 j = 0;
        while (j < 3) {
            if (j == 1) break;
            s = s + 1;
            j = j + 1;
        }
        i = i + 1;
    }
    return s;
}
```

```click
verifying "nb.c";
int32 f(int32 x) { ensures result == 3; } by { execute(); simp(); }
```

Observed on 2026-10-07: exit 1 with the message above. Removing the `break`
(`ensures result == 9`) verifies; removing the outer loop (`ensures result ==
1`) verifies.

## Intended regression

The reproduction as a positive mdtest, with one variant whose outer body
uses the inner counter after the inner loop breaks (`s = s + j` under
`ensures result == 6`), and the negative `ensures result == 4` refused with
an evaluated left side.

## Acceptance criteria

- A `break` out of an inner concrete loop resumes the outer body at the
  statement after the inner loop, and the function verifies.
- The internal-consistency message is not reachable from this shape; a
  refusal that remains names the statement it concerns.
- `scripts/check.sh` passes.
