# Smart `execute` overflows the stack on deeply nested `if`s

Soundness: not soundness. The verifier aborts with a stack overflow before
reaching a verdict; nothing is accepted.

`execute()` on a function whose body nests `if` statements about 110 deep
aborts the process (`fatal runtime error: stack overflow`). Nested ifs of
that depth have only depth + 1 paths, so the verifier should decide them, or
refuse them with a diagnostic, without exhausting the native stack. At 96
levels the same proof verifies in under half a second.

## Reproduction

Generate the function with `depth` nested ifs and verify it with the
profiling build (`cargo build --profile profiling --bin click`):

```sh
python3 - 112 > /tmp/nested_ifs.md <<'PY'
import sys
n = int(sys.argv[1])
params = ", ".join(f"int32 a{i}" for i in range(n))
body = "".join("    " * (i + 1) + f"if (a{i} > 0) {{\n" for i in range(n))
body += "    " * (n + 1) + "s = 1;\n" + "".join("    " * (n - i) + "}\n" for i in range(n))
c = f"int32 caller({params}) {{\n    int32 s;\n    s = 0;\n{body}    return s;\n}}"
click = f'verifying "hunt.c";\n\nint32 caller({params}) {{\n    ensures result >= 0;\n}} by {{\n    execute();\n    simp();\n}}'
print(f"# nested ifs {n}\n\n```c filename=hunt.c\n{c}\n```\n\n```click\n{click}\n```\n\n```expect\npass\n```")
PY
target/profiling/click verify /tmp/nested_ifs.md
```

Depth 96 verifies; depth 112 aborts. Under `gdb` the stack is about 98
frames of
`try_focused_execute_to_exit_within` (`src/surface/proof/proof_object/execution_joins.rs`,
the arm loop near line 3280), roughly 85 KB of stack per nesting level: the
focused execution recurses into each split arm on the native stack.

## Acceptance criteria

- The depth-112 and depth-256 functions above verify (or are refused with a
  diagnostic) without a stack overflow, in a default-stack test thread.
- Stack use of focused execution does not grow with branch nesting depth, for
  example by driving nested arms from an explicit work stack, as the proof-node
  chain already is.
- A regression test runs the deep case at a size that overflows today.
