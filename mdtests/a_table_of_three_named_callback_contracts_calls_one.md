# a table of three named callback contracts calls one

A resource packages three function-pointer fields, each with its own named
contract. A verified helper borrows the table and calls the `subtract`
callback, and a caller reaches it through the helper's contract. The three
contract facts are indexed by name side by side, so the call finds
`Difference` among `Addition` and `Negation`. At the outer call the helper's
`defined(left - right)` requirement joins the condition facts consulted when
the viewed table's fields are loaded. This catches a named contract index that
loses or misfiles one of several contract facts held at once, and a call-site
load index that cannot take a subtraction overflow fact.

```c filename=a_table_of_three_named_callback_contracts_calls_one.c
struct callback_table {
    int32 (*add)(int32, int32);
    int32 (*subtract)(int32, int32);
    int32 (*negate)(int32);
};

int32 compute_difference(struct callback_table* table, int32 left, int32 right) {
    return table->subtract(left, right);
}

int32 run(struct callback_table* table, int32 left, int32 right) {
    return compute_difference(table, left, right);
}
```

```click
verifying "a_table_of_three_named_callback_contracts_calls_one.c";

contract int32 Addition(int32 left, int32 right) {
    requires defined(left + right);
    ensures result == left + right;
}

contract int32 Difference(int32 left, int32 right) {
    requires defined(left - right);
    ensures result == left - right;
}

contract int32 Negation(int32 value) {
    requires defined(0 - value);
    ensures result == 0 - value;
}

resource callback_suite(table: struct callback_table*) {
    owns table->add;
    owns table->subtract;
    owns table->negate;
    fact Addition(table->add);
    fact Difference(table->subtract);
    fact Negation(table->negate);
}

int32 compute_difference(struct callback_table* table, int32 left, int32 right) {
    views callback_suite(table);
    requires defined(left - right);
    ensures result == left - right;
} by {
    open(callback_suite(table)) {
        execute();
        simp();
    }
}

int32 run(struct callback_table* table, int32 left, int32 right) {
    views callback_suite(table);
    requires defined(left - right);
    ensures result == left - right;
} by {
    execute();
    simp();
}
```

```expect
pass
```
