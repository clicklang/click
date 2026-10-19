# C frontend overflows before executing deeply nested ifs

Soundness: not soundness. The process aborts before reaching a verdict.

This is separate from focused execution's branch traversal. In an unoptimized
build, the source parser overflows on the native program below at depth 96,
during source resolution, before verifier-core execution starts. A stack trace
repeats `Parser::parse_statement_slow`, `parse_controlled_statement`, and
`parse_block_statement`, with the expression-precedence parser above them.

Preparing the syntax on a larger test-setup thread also reveals a second
frontend recursion: `C0Statement::to_kernel_statement_with_control_targets`
overflows while lowering depth 112 on a two-megabyte thread. These are frontend
stack costs; the prepared native function's focused execution is covered by
its own depth-112/256 constrained-stack regression.

## Reproduction

Build with `cargo build --bin click`, generate this mdtest, and run
`CLICK_TIMINGS=1 target/debug/click verify /tmp/nested-ifs.md` on the normal
main-thread stack. The last phase started is `source resolution`.

```sh
python3 - > /tmp/nested-ifs.md <<'PYGEN'
n = 96
params = ", ".join(f"int32 a{i}" for i in range(n))
body = "".join(f"if (a{i} > 0) {{\n" for i in range(n))
body += "s = 1;\n" + "}\n" * n
c = f"int32 caller({params}) {{ int32 s; s = 0;\n{body}return s; }}"
proof = f'verifying "hunt.c"; int32 caller({params}) {{ ensures result >= 0; }} by {{ execute(); simp(); }}'
print(f"# nested ifs\n\n```c filename=hunt.c\n{c}\n```\n\n```click\n{proof}\n```\n\n```expect\npass\n```")
PYGEN
```

## Acceptance criteria

- Parse and lower depth-112 and depth-256 versions on ordinary stacks, or
  refuse them with a diagnostic before native stack exhaustion.
- Keep the native program unchanged and do not increase verifier stack sizes
  as the repair.
- Cover both frontend stages separately from the focused-execution regression.
