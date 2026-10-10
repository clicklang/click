# Postfix update assignment consumes the original value

The unchanged C example now verifies that assigning `i++` captures the old
value while the update still occurs.

```c filename=statement_update_rejects_expression.c
int32 statement_update_rejects_expression() {
    int32 i;
    int32 j;
    i = 0;
    j = i++;
    return j;
}
```

```click
verifying "statement_update_rejects_expression.c";

int32 statement_update_rejects_expression() {
    ensures result == 0 by auto;
}
```

```expect
pass
```
