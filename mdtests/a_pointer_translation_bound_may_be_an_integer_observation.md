# A pointer translation bound may be an Integer observation

Under `arithmetic "integer";` a comparison that does arithmetic compares
exact Integers, so `n - k < 18446744073709551615u64` is Integer subtraction
and does not bound the `uint64` offset `n - k`. Translating `p == a + (n - k)`
one element on needs that machine bound; it is written as the Integer
observation `to_integer(n - k) < 18446744073709551615`, which holds exactly
when the native bound does, and `arithmetic` cites it as that bound.

```c filename=a_pointer_translation_bound_may_be_an_integer_observation.c
int at_offset(int *a, unsigned long n, unsigned long k) {
    int *p = a + (n - k);
    return 0;
}
```

```click
arithmetic "integer";

verifying "a_pointer_translation_bound_may_be_an_integer_observation.c";
int32 at_offset(int32* a, uint64 n, uint64 k) {
    requires k <= n and n <= 100u64;
    views a[0..n];
} by {
    execute_until(assignment(p, 0));
    step();
    have to_integer(n - k) < 18446744073709551615 by auto();
    have p + 1 == a + ((n - k) + 1u64) by {
        arithmetic() using {
            p == a + (n - k);
            to_integer(n - k) < 18446744073709551615;
        };
    }
    execute();
}
```

```expect
pass
```
