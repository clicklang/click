# Aggregate temporary storage has ended at the source statement's exit

```c filename=aggregate_exit.c
struct box { int32 items[1]; };
struct box make() { struct box out = {{7}}; return out; }
int32 read() { int32* p = make().items; return p[0]; }
```

```click
verifying "aggregate_exit.c";
struct box make() { ensures result.items[0] == 7; }
int32 read() { ensures result == 7; }
```

```expect
fail: invalid memory access
```
