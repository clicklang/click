# A store leaves a different array element unchanged

The store to `p[1]` leaves the read of `p[0]` unchanged. After the store,
`close()` uses the fact from the unfolded precondition to establish
`p[0] == 7` before the return reads it.

```c filename=simple_statement_step_explicit_transport.c
int32 set_second_return_first(int32 p[2]) {
    p[1] = 9;
    return p[0];
}
```

```click
verifying "simple_statement_step_explicit_transport.c";

predicate first_is_seven(p: int32[]) {
    p[0] == 7
}

int32 set_second_return_first(int32 p[2]) {
    requires first_is_seven(p);
    owns p[0..2];

    ensures result == 7;
} by {
    unfold(first_is_seven(p));
    step();
    have p[0] == 7 by { close(); }
    step();
    close();
}
```

```expect
pass
```
