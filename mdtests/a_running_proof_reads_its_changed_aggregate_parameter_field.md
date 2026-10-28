# A running proof reads the callee's changed parameter field

```c filename=aggregate_field_write.c
struct packet { int32* data; };
void redirect(struct packet input, int32* q) { input.data = q; }
```

```click
verifying "aggregate_field_write.c";
void redirect(struct packet input, int32* q) {
    requires input.data != q;
    ensures q == old(q);
} by {
    step();
    have input.data == q by { normalize(); }
}
```

```expect
pass
```
