# Aggregate expression results are named by their source steps

```c filename=aggregate_steps.c
struct inner { int32 value; };
struct pair { int32 left; int32 right; struct inner nested; int32 items[2]; int32* data; };
struct pair make(struct pair input) { return input; }
int32 call_field(struct pair input) { return make(input).right; }
int32 constant_conditional(struct pair input) {
    struct pair output = 0 ? make(input) : input;
    return output.right;
}
int32 conditional_field(struct pair input, int32 choose) {
    struct pair output = choose ? make(input) : input;
    return output.right;
}
```

```click
verifying "aggregate_steps.c";
struct pair make(struct pair input) {
    ensures result.left == input.left;
    ensures result.right == input.right;
    ensures result.nested.value == input.nested.value;
    ensures result.items[1] == input.items[1];
    ensures result.data == input.data;
}
int32 call_field(struct pair input) {
    ensures result == input.right;
} by {
    step();
    have statement(0).call(make, 0).result.right == input.right;
    have statement(0).call(make, 0).result.nested.value == input.nested.value;
    have statement(0).call(make, 0).result.items[1] == input.items[1];
    have statement(0).call(make, 0).result.data == input.data;
}
int32 constant_conditional(struct pair input) {
    ensures result == input.right;
} by {
    step_until(statement(1).entry);
    have statement(0).ternary(0).result.right == input.right;
}
int32 conditional_field(struct pair input, int32 choose) {
    ensures result == input.right;
}
```

```expect
pass
```
