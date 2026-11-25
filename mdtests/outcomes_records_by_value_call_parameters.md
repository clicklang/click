# By-value parameters in both call outcomes

The record fields in the callee’s contract refer to the copy made at call
entry. Both arms of `outcomes` can refer to that copy.

```c filename=outcomes_records_by_value_call_parameters.c
struct Value { int field; };

int helper(struct Value input) { return input.field; }

int caller(int field) {
    struct Value input = {field};
    return helper(input);
}
```

```click
verifying "outcomes_records_by_value_call_parameters.c";

int32 helper(struct Value input) throws int32 {
    ensures result == old(input.field);
    exceptional ensures exception == old(input.field);
}

int32 caller(int32 field) throws int32 {
    ensures result == field;
    exceptional ensures exception == field;
} by {
    step_until(call(0).entry);
    outcomes {
        returned => {
            have at(call(0).entry, call(0).parameter(input).field) == field by { close(); }
            step_until(function.exit);
        }
        threw => {
            have at(call(0).entry, call(0).parameter(input).field) == field by { close(); }
        }
    }
}
```

```expect
pass
```
