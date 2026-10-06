# A proof-level `if` with `ensuring` rejoins through its interface

`ensuring` names what the proof keeps after the `if`, as it does on a
`branch`. Both arms must establish each interface fact; the proof then
continues once, from the state the interface describes. Here the arms only
reason, and the interface keeps the value of `a` they both hold.

```c filename=proof_if_ensuring_rejoins.c
int32 bump(int32 x) {
    int32 a;
    a = 0;
    a = a + 1;
    return a;
}
```

```click
verifying "proof_if_ensuring_rejoins.c";

int32 bump(int32 x) {
    ensures result == 1;
} by {
    step();
    step();
    if x <= 0 ensuring {
        fact a == 0;
    } then {
        have x <= 0 or x > 0 by { simp(); }
    } else {
        have x <= 0 or x > 0 by { simp(); }
    }
    step();
    step();
    simp();
}
```

```expect
pass
```
