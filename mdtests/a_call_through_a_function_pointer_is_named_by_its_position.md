# A call through a function pointer is named by its position

`table->subtract(left, right)` calls whatever the field holds, so no function
names it. It is `statement(0).call(0)`, the statement's first call of any
callee, and its result is `statement(0).call(0).result`. No local holds the
pointer: the call goes through the field.

```c filename=pointer_call_position.c
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
verifying "pointer_call_position.c";

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
        have to_integer(statement(0).call(0).result) == to_integer(left - right);
    }
}
```

```expect
pass
```
