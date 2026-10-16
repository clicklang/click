# auto proves an in-range machine sum is its Integer sum

Under `arithmetic "integer";` a contract about `x - 1` or `a + b` compares
exact Integers, while the C function computes them in its machine type. When
the facts bound the Integer result inside that type, `auto` proves the two
agree: it bounds the result from the facts and the operands' type ranges,
applies `integer_operation_identity`, and closes the goal, with no bridge
lemma (`mdtests/an_in_range_machine_difference_is_its_integer_difference.md`
writes that certificate by hand).

```c filename=auto_proves_an_in_range_machine_sum_is_its_integer_sum.c
unsigned decrement(unsigned x) { return x - 1u; }
int add(int a, int b) { return a + b; }
```

```click
arithmetic "integer";
verifying "auto_proves_an_in_range_machine_sum_is_its_integer_sum.c";

uint32 decrement(uint32 x) {
    requires 1 <= x;
    ensures result == x - 1;
}

int32 add(int32 a, int32 b) {
    requires 0 <= a;
    requires a <= 100;
    requires 0 <= b;
    requires b <= 100;
    ensures result == a + b;
}
```

```expect
pass
```
