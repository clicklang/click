# A pure pointer identity does not equate unrelated parameters

```c filename=probe.c
void probe(int *p, int *q) {}
```

```click
verifying "probe.c";
function identity(p: int32*) -> int32* { p }
void probe(int32* p, int32* q) {
    ensures p == q;
} by {
    have identity(q) == q by { unfold(identity(q)); close(); }
    have p == q by { close() using { }; }
}
```

```expect
fail: `close() using` could not prove the current goal from only its listed premises
```
