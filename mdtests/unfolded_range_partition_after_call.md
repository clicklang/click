# Unfolded range partition after a call

The selected range and the separately owned slot remain independent members
of the partition even when the range retains earlier pointer-carrier metadata.

```c filename=probe.c
struct buffer { int *data; };
void idle(struct buffer *b) {}
void probe(struct buffer *b, int *slot) { idle(b); }
```

```click
verifying "probe.c";
resource buffer(b: struct buffer*) {
    field lo: int32;
    field hi: int32;
    owns *b;
    owns b->data[lo..hi];
    fact 0 <= lo;
    fact lo < hi;
    fact hi <= 100;
}
void idle(struct buffer* b) { owns r: buffer(b); }
void probe(struct buffer* b, int32* slot) {
    owns r: buffer(b);
    owns *slot;
} by {
    step(idle, { r: r });
    let { lo: lo, hi: hi } = unfold(r);
    have separate(memory(*slot), memory(b->data[(lo as int32)..(hi as int32)])) by { assumption(); }
    let r = fold(buffer(b), { lo: lo, hi: hi });
}
```

```expect
pass
```
