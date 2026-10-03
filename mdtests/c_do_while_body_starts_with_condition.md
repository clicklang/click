# A `do ... while` body may begin with an `if`

A `do ... while` runs its body before its condition is read, so a condition
decided at the loop's head belongs to the body's first statement. The proof
object descended into the body for a statement but not for a condition, and
refused a body that begins with an `if`, wherever the loop stood. The
functions cover a loop that opens the function and one that does not, a
`break`, a `continue`, a nested loop, and a loop that iterates.

```c filename=c_do_while_body_starts_with_condition.c
int32 first(int32 v) {
    do {
        if (v == 7)
            v = 3;
    } while (0);
    return v;
}

int32 later(int32 v) {
    v = v + 0;
    do {
        if (v == 7)
            v = 3;
    } while (0);
    return v;
}

int32 breaks(int32 v) {
    do {
        if (v == 7)
            break;
        v = 3;
    } while (0);
    return v;
}

int32 continues(int32 v) {
    do {
        if (v == 7)
            continue;
        v = 3;
    } while (0);
    return v;
}

int32 nested(int32 v) {
    do {
        do {
            if (v == 7)
                v = 3;
        } while (0);
    } while (0);
    return v;
}

int32 iterates(int32 v) {
    int32 i = 0;
    do {
        if (v == 7)
            v = 3;
        i++;
    } while (i < 2);
    return v;
}
```

```click
verifying "c_do_while_body_starts_with_condition.c";

int32 first(int32 v) {
    requires v == 7;
    ensures result == 3 by auto;
}

int32 later(int32 v) {
    requires v == 1;
    ensures result == 1 by auto;
}

int32 breaks(int32 v) {
    requires v == 7;
    ensures result == 7 by auto;
}

int32 continues(int32 v) {
    requires v == 7;
    ensures result == 7 by auto;
}

int32 nested(int32 v) {
    requires v == 7;
    ensures result == 3 by auto;
}

int32 iterates(int32 v) {
    requires v == 7;
    ensures result == 3 by auto;
}
```

```expect
pass
```
