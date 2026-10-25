# A script that stops with C left is finished by the implicit tail

Every function proof ends with the same implicit tail: the C that remains is
executed, splitting at an undecided `if`, and each goal still open at function
exit is closed. A script may stop after any statement, before a branch
included, and an omitted proof is the empty script. The tail is charged to
the smart budget at the site after the script's last tactic.

```c filename=a_script_that_stops_with_c_left_is_finished.c
int32 magnitude(int32 x) {
    int32 y = 0;
    if (x > 0) {
        y = x;
    } else {
        y = -x;
    }
    return y;
}
```

```click
verifying "a_script_that_stops_with_c_left_is_finished.c";

int32 magnitude(int32 x) {
    requires x > -100 and x < 100;
    ensures result >= 0;
} by {
    step();
}
```

```expect
pass
```
