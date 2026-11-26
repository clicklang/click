# simple proof tactics

These proofs show how `close` discharges an available fact or a reflexive goal
and how `rewrite` substitutes one side of a cited equality for the other.

```c filename=simple_tactics.c
int32 identity(int32 x) {
    return x;
}
```

```click
verifying "simple_tactics.c";

theorem exact_known(x: int32) {
    requires x >= 0;

    ensures x >= 0 by {
        close();
    }
}

theorem reflexive_identity(x: int32) {
    ensures x + 1 == x + 1 by {
        close();
    }
}

theorem rewritten_identity(x: int32, y: int32) {
    requires x == y;

    ensures x + 1 == y + 1 by {
        rewrite(x, y);
        close();
    }
}

int32 identity(int32 x) {
    requires x == 7;
    ensures result == 7;
} by {
    step_until(function.exit);
    rewrite(x, 7);
    close();
}
```

```expect
pass
```
