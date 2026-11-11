# A store index fact may be required as an Integer or as an `int32` word

The store-time check reads the disequality of the two `int32` index words,
`((m - 1) as int32) != 0`. `m - 1 != 0` is the mathematical Integer fact
`to_integer(m) - 1 != 0`, a different fact. Where the bounds keep `m - 1` in
range, `solve` proves the word fact from the Integer one by cases on the
word equality: that arm proves `m - 1 == 0` and contradicts the stated fact.
The implicit tail then keeps `q[0]` across the store. A stated word fact is
read directly, and either may be required or stated with `have`.

```c filename=a_store_index_fact_may_be_the_integer_or_the_word.c
int required_integer(int m) {
    int *q = malloc(m * sizeof(int));
    if (q == 0) {
        return 0;
    }
    q[0] = 7;
    q[m - 1] = 1;
    int r = q[0];
    free(q);
    return r;
}

int required_word(int m) {
    int *q = malloc(m * sizeof(int));
    if (q == 0) {
        return 0;
    }
    q[0] = 7;
    q[m - 1] = 1;
    int r = q[0];
    free(q);
    return r;
}
```

```click
verifying "a_store_index_fact_may_be_the_integer_or_the_word.c";

int32 required_integer(int32 m) {
    requires 1 <= m;
    requires m <= 1000;
    requires m - 1 != 0;
    ensures result == 0 or result == 7;
}

int32 required_word(int32 m) {
    requires 1 <= m;
    requires m <= 1000;
    requires ((m - 1) as int32) != 0;
    ensures result == 0 or result == 7;
}
```

```expect
pass
```
