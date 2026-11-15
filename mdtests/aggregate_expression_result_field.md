# A struct call result has a source field spelling

```c filename=aggregate_field.c
struct box { int32 value; };
struct box make(int32 value) { struct box out = {value}; return out; }
static int32 relay(struct box input) { return input.value; }
int32 read(int32 value) { return make(value).value; }
int32 nested(int32 value) { return relay(make(value)); }
```

```click
verifying "aggregate_field.c";
struct box make(int32 value) { ensures result.value == value; }
int32 read(int32 value) { ensures result == value; } by {
    step();
    have statement(0).call(make, 0).result.value == value;
}
int32 nested(int32 value) { ensures result == value; }
```

```expect
pass
```
