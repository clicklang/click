# Outcome `auto` search loses a clause among many `ensures`

Soundness: not soundness. A valid proof is refused; nothing false is
accepted.

`int32 caller(int32 x) { return x; }` with `requires 0 <= x; requires
x <= 1000;` and the clauses `ensures result >= x - i` for `i` in `0..N`
verifies by `step(); simp();` for N up to 56 and is refused at N = 64:

```text
checked outcome `auto` search did not retain a complete proof for `caller.ensures_63`
`ensures result >= (x - 63)` failed for `caller.ensures_63` path 0
```

Every clause is the same easy shape and the charged work is tiny (`simp` 50
units at both sizes), so this is a structural cap, not the budget: whether a
clause closes depends on how many other clauses the function has.

## Reproduction

```sh
python3 - 64 > /tmp/many_ensures.md <<'PY'
import sys
n = int(sys.argv[1])
ens = "\n".join(f"    ensures result >= x - {i};" for i in range(n))
click = f'verifying "hunt.c";\n\nint32 caller(int32 x) {{\n    requires 0 <= x;\n    requires x <= 1000;\n{ens}\n}} by {{\n    step();\n    simp();\n}}'
print(f"# many ensures {n}\n\n```c filename=hunt.c\nint32 caller(int32 x) {{\n    return x;\n}}\n```\n\n```click\n{click}\n```\n\n```expect\npass\n```")
PY
target/profiling/click verify /tmp/many_ensures.md
```

N = 56 verifies; N = 64 is refused.

## Acceptance criteria

- The N = 64 and N = 256 programs above verify by `step(); simp();`.
- A regression checks that each clause closes independently of how many
  other `ensures` clauses the function declares.
