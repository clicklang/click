# An operation identity bound outside its type is refused

`integer_operation_identity` needs both named bounds inside the operation's
type. A lower bound of `-1` is one below `unsigned int`'s range, so the
certificate does not show that the subtraction does not wrap.

```c filename=an_operation_identity_bound_outside_its_type_is_refused.c
unsigned decrement(unsigned x) { return x - 1u; }
```

```click
verifying "an_operation_identity_bound_outside_its_type_is_refused.c";
uint32 decrement(uint32 x) {
    ensures to_integer(result) == to_integer(x) - 1;
} by {
    execute();
    have -1 <= to_integer(old(x)) - 1 by auto();
    have to_integer(old(x)) - 1 <= 4294967295 by auto();
    arithmetic_certificate rules {
        premise 0: -1 <= to_integer(old(x)) - 1 => -1 <= to_integer(old(x)) - 1;
        premise 1: to_integer(old(x)) - 1 <= 4294967295 => to_integer(old(x)) - 1 <= 4294967295;
        integer_operation_identity bounds [0, 1] => to_integer(result) == to_integer(old(x)) - 1;
        conclusion 0;
    }
}
```

```expect
fail: arithmetic_certificate
```
