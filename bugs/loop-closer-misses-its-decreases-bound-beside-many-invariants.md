# Loop closer misses its `decreases` bound beside many invariants

Soundness: not soundness. A valid loop proof is refused; nothing false is
accepted.

A loop that updates N counters alongside its index, with one invariant per
counter, verifies for N up to 28 and is refused at N = 32. The obligation left
open is the `decreases 4 - i` bound, which mentions only `i` and the bounds
`0 <= i <= 4` that are invariants in every size:

```text
closure body did not prove every invariant obligation
`0 <= ((0 - at(statement(67).entry, i)) + 3)` remained open; this loop
declares `decreases`, so the bundle also has `0 <= 4 - i` at the back edge
```

The work charged is far below the budget (`loop` 30,881 units at N = 32;
36,583 at N = 28), so this is not budget exhaustion: an obligation the
closer proves beside 28 unrelated invariants is lost beside 32. Whether a
smart closer proves a fact must not depend on how many unrelated invariants
the loop carries (`docs/internals/verification-efficiency.md`, and the
bounded-miss rule in `docs/concepts/proof-failure-triage.md`, which expects
a miss to be local, not a function of unrelated state).

## Reproduction

```sh
python3 - 32 > /tmp/loop_state.md <<'PY'
import sys
n = int(sys.argv[1])
decls = "\n".join(f"    int32 v{i};" for i in range(n))
inits = "\n".join(f"    v{i} = 0;" for i in range(n))
upd = "\n".join(f"        v{i} = v{i} + 1;" for i in range(n))
c = f"int32 caller() {{\n    int32 i;\n{decls}\n    i = 0;\n{inits}\n    while (i < 4) {{\n{upd}\n        i = i + 1;\n    }}\n    return i;\n}}"
inv = " ".join(f"invariant v{j} == i;" for j in range(n))
steps = "\n".join("    step();" for _ in range(2 * n + 2))
click = f'verifying "hunt.c";\n\nint32 caller() {{\n    ensures result == 4;\n}} by {{\n{steps}\n    loop {{ decreases 4 - i; invariant i >= 0; invariant i <= 4; {inv} }}\n    step();\n    simp();\n}}'
print(f"# loop state {n}\n\n```c filename=hunt.c\n{c}\n```\n\n```click\n{click}\n```\n\n```expect\npass\n```")
PY
target/profiling/click verify /tmp/loop_state.md
```

N = 28 verifies; N = 32 is refused as above.

## Acceptance criteria

- The N = 32 and N = 64 programs above verify.
- A regression shows the loop closer proving the same `decreases` obligation
  beside 4, 32 and 64 unrelated counter invariants, with work bounded by the
  invariants it checks.
