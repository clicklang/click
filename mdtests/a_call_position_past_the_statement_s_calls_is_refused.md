# A call position past the statement's calls is refused

`statement(0)` makes one call, through `table->subtract`, so `call(1)` names
nothing; the refusal says how many calls the statement makes.

```c filename=pointer_call_position_past.c
struct callback_table {
    int32 (*add)(int32, int32);
    int32 (*subtract)(int32, int32);
};

int32 compute(struct callback_table* table, int32 left, int32 right) {
    int32 d = table->subtract(left, right);
    return d;
}
```

```click
verifying "pointer_call_position_past.c";

contract int32 Addition(int32 left, int32 right) {
    requires defined(left + right);
    ensures to_integer(result) == to_integer(left + right);
}

contract int32 Difference(int32 left, int32 right) {
    requires defined(left - right);
    ensures to_integer(result) == to_integer(left - right);
}

resource callback_suite(table: struct callback_table*) {
    owns table->add;
    owns table->subtract;
    fact Addition(table->add);
    fact Difference(table->subtract);
}

int32 compute(struct callback_table* table, int32 left, int32 right) {
    views callback_suite(table);
    requires defined(left - right);
    ensures to_integer(result) == to_integer(left - right);
} by {
    with(callback_suite(table)) {
        step(); step();
        have to_integer(statement(0).call(1).result) == to_integer(left - right);
    }
}
```

```expect
fail: makes 1 call(s), so it has no `call(1)`
```
