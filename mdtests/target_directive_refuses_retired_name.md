# A retired single-name target is refused with its replacement

Targets were once spelled as one name, such as `x86_64-linux-kernel`. They are
now a target triple and a mode, so a sidecar that still names the old
spelling is refused with the directives that replace it.

```c filename=answer.c
int32_t answer(void) {
    return 1;
}
```

```click
target "x86_64-linux-kernel";
verifying "answer.c";

int32 answer() {
    ensures result == 1;
} by {
    execute();
    simp();
}
```

```expect
fail: C target `x86_64-linux-kernel` is retired; use target `x86_64-unknown-linux-gnu` with mode `kernel`
```
