# An in-range machine difference is its Integer difference

`integer_operation_identity` relates a machine `+` or `-` to the same
operation on its operands' Integer values when two named bounds put the
Integer result inside the operation's type. Here the unsigned subtraction
cannot wrap because `x` is at least one.

```c filename=an_in_range_machine_difference_is_its_integer_difference.c
unsigned decrement(unsigned x) { return x - 1u; }
```

```click
verifying "an_in_range_machine_difference_is_its_integer_difference.c";
uint32 decrement(uint32 x) {
    requires 1 <= to_integer(x);
    ensures to_integer(result) == to_integer(x) - 1;
} by {
    execute();
    have 0 <= to_integer(old(x)) - 1 by auto();
    have to_integer(old(x)) - 1 <= 4294967295 by auto();
    arithmetic_certificate rules {
        premise 0: 0 <= to_integer(old(x)) - 1 => 0 <= to_integer(old(x)) - 1;
        premise 1: to_integer(old(x)) - 1 <= 4294967295 => to_integer(old(x)) - 1 <= 4294967295;
        integer_operation_identity bounds [0, 1] => to_integer(result) == to_integer(old(x)) - 1;
        conclusion 0;
    }
}
```

```expect
pass
```
