# Free accepts an owned pointer copied into an aggregate parameter

The allocation token names the entry field read. The C operand reads the
private parameter copy; resource discovery must follow its producer definition.

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
} by { unfold(cell(input.data)); }
```

```expect
pass
```
