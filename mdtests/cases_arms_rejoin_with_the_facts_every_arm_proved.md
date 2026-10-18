# The arms of `cases` rejoin with the facts every arm proved

With tactics written after it, the arms of `cases` rejoin, as a proof `if`'s do: the proof continues once, here before the first statement, with the facts every arm proved. `x > 0` holds in each arm, so it survives the join, and `execute()` runs once with it.

```c filename=cases_arms_rejoin_with_the_facts_every_arm_proved.c
int32 f(int32 x) {
    if (x > 0) {
        return 1;
    }
    return 0;
}
```

```click
verifying "cases_arms_rejoin_with_the_facts_every_arm_proved.c";

int32 f(int32 x) {
    requires x == 1 or x == 2 or x == 3;
    ensures result == 1;
} by {
    cases {
        x == 1 => { have x > 0; }
        x == 2 => { have x > 0; }
        x == 3 => { have x > 0; }
    }
    execute();
}
```

```expect
pass
```
