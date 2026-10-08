# An integer variable remains an integer even when it is known to be zero.

```c filename=user_tactic_null_pointer.c
struct node { int32 value; };
void user(int32 zero) {}
```

```click
verifying "user_tactic_null_pointer.c";

tactic nulls(p: struct node*, q: int32*, count: int32) {
    requires p == 0;
    requires q == 0;
    requires count == 0;
    ensures p == 0;
    ensures q == 0;
    ensures count == 0;
} by {
    have p == 0 by { assumption(); }
    have q == 0 by { assumption(); }
    have count == 0 by { assumption(); }
}

void user(int32 zero) {
    requires zero == 0;
    ensures 1 == 1;
} by {
    nulls(zero, 0, 0);
    execute(); simp();
}
```

```expect
fail: fold initializer has the wrong type
```
