# recursive calls after a switch owe ordinary descent obligations

Neither a case's `break` nor its fall-through path skips the recursive call
that follows the switch. The decreasing function beside it is valid; the
unchanged argument in `spin_past_a_switch` must fail at the call itself.
This remains a regression for the legacy walk's former dropped-path bug,
now enforced by ordinary execution rather than a second walk over C.

```c filename=c_decreases_checks_past_a_switch.c
int32 spin_past_a_switch(int32 n) {
    int32 result;
    result = 0;
    switch (n) {
        case 0:
            break;
        default:
            break;
    }
    if (n > 0) {
        result = spin_past_a_switch(n);
    }
    return result;
}

int32 descends_past_a_switch(int32 n) {
    int32 result;
    result = 0;
    switch (n) {
        case 0:
            break;
        default:
            break;
    }
    if (n > 0) {
        result = descends_past_a_switch(n - 1);
    }
    return result;
}
```

```click
verifying "c_decreases_checks_past_a_switch.c";

int32 descends_past_a_switch(int32 n) {
    decreases n;
    ensures result == 0;
}

int32 spin_past_a_switch(int32 n) {
    decreases n;
    ensures result == 0;
}
```

```expect
fail: spin_past_a_switch recursion measure: `n` decreases at the recursive call
```
