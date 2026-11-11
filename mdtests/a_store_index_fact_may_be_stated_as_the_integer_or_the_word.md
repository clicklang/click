# A store index fact may be stated as an Integer or as an `int32` word

The proof states the index disequality with `have`, as the Integer fact
`m - 1 != 0` or as the `int32` word fact `((m - 1) as int32) != 0`, before the
implicit tail runs the C. A stated word fact is read directly by the store;
the implicit tail carries a stated Integer fact to the word fact, as
`a_store_index_fact_may_be_the_integer_or_the_word.md` describes.

```c filename=a_store_index_fact_may_be_stated_as_the_integer_or_the_word.c
int stated_integer(int m) {
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

int stated_word(int m) {
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
verifying "a_store_index_fact_may_be_stated_as_the_integer_or_the_word.c";

int32 stated_integer(int32 m) {
    requires 2 <= m;
    requires m <= 1000;
    ensures result == 0 or result == 7;
} by {
    have m - 1 != 0 by solve();
}

int32 stated_word(int32 m) {
    requires 2 <= m;
    requires m <= 1000;
    ensures result == 0 or result == 7;
} by {
    have ((m - 1) as int32) != 0 by solve();
}
```

```expect
pass
```
