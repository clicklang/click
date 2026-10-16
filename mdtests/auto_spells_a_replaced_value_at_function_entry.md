# auto spells a replaced value at function entry

After `*p = *p - 1`, the new `*p` is the machine difference of the old value
and `1`. To show it stays nonnegative, `auto` relates it to the Integer
`to_integer(old(*p)) - 1` with `integer_operation_identity`; the operand is
spelled `old(*p)`, the entry reading of the written `*p`. The requirement
`*p >= 1` is a native bound, read as `1 <= to_integer(old(*p))`.

```c filename=auto_spells_a_replaced_value_at_function_entry.c
void decrement(int *p) { *p = *p - 1; }
```

```click
arithmetic "integer";
verifying "auto_spells_a_replaced_value_at_function_entry.c";

void decrement(int32 *p) {
    owns *p;
    requires *p >= 1;
    ensures 0 <= to_integer(*p);
}
```

```expect
pass
```
