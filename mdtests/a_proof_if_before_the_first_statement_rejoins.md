# A proof `if` before the first statement rejoins

A proof `if` written before any statement has run rejoins like any other: the arms continue from the bound entry state, and what follows runs once with the facts both arms proved.

```c filename=a_proof_if_before_the_first_statement_rejoins.c
int32 f(int32 x) {
    if (x > 0) {
        return 1;
    }
    return 0;
}
```

```click
verifying "a_proof_if_before_the_first_statement_rejoins.c";

int32 f(int32 x) {
    requires x == 1 or x == 2;
    ensures result == 1;
} by {
    if x == 1 {
        have x > 0;
    } else {
        have x > 0;
    }
    execute();
}
```

```expect
pass
```
