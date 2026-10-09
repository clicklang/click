# A logical pointer field does not keep its pointee alive

The descriptor retains its pointer value, but releasing the backing allocation
prevents carrying the element value from function entry to the outcome.

```c filename=aggregate_parameter_pointee_expires.c
struct packet { int32* data; };
void dispose(struct packet input) { free(input.data); }
```

```click
verifying "aggregate_parameter_pointee_expires.c";
resource cell(p: int32*) {
    owns allocation(p, 4);
    owns p[0..1];
}
void dispose(struct packet input) {
    consumes cell(input.data);
    ensures input.data[0] == old(input.data[0]);
} by { unfold(cell(input.data)); execute(); simp(); }
```

```expect
fail: an allocation was released in between
```
