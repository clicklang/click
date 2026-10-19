# A written simp that closes nothing is refused

After execution a written `simp() using` acts on the first open goal. Here
it cites a premise that does not hold, so it closes nothing and is refused
with that goal. It used to be skipped, leaving the implicit `auto` to close
the claim and `click expand` to drop the written tactic.

```c filename=a_written_simp_that_closes_nothing_is_refused.c
int32 zero(void) {
    return 0;
}
```

```click
verifying "a_written_simp_that_closes_nothing_is_refused.c";

int32 zero() {
    ensures result == 0 by {
        execute();
        simp() using { 1 == 2; }
    }
}
```

```expect
fail: did not retain a complete transition for every pending claim
```
