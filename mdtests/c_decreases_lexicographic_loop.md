# a loop measure can use lexicographic phases

```c filename=c_decreases_lexicographic_loop.c
int32 phase_count(int32 n) {
    int32 i;
    int32 j;
    i = n;
    j = 2;
    while (i > 0) {
        if (j > 0) {
            j = j - 1;
        } else {
            i = i - 1;
            j = 2;
        }
    }
    return i;
}
```

```click
verifying "c_decreases_lexicographic_loop.c";

int32 phase_count(int32 n) {
    requires n >= 0;
    ensures result == 0;
} by {
    step();
    step();
    step();
    step();
    loop {
        decreases (i, j);
        invariant i >= 0;
        invariant j >= 0;
        invariant j <= 2;
        initialize by simp();
        preserve by {
            if j > 0 {
                have 0 <= to_integer(j - 1) by auto();
                step();
                step();
                have j >= 0 by { arithmetic() using { 0 <= j; }; }
                simp();
            } else {
                have 0 <= to_integer(i - 1) by auto();
                step();
                step();
                step();
                have i >= 0 by { arithmetic() using { 0 <= i; }; }
                simp();
            }
        }
    }
    step();
    simp();
}
```

```expect
pass
```
