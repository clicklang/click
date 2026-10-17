# A closer after execution acts on the first open claim

After execution the open goals are the proposition claims, in contract order,
and a closer acts on the first of them. Here the first claim is `2 + 2 == 4`,
which no available fact states, so `assumption()` is refused for that goal. It
does not look further down the list for a claim it could close, as it used to:
`result == n` waits for its turn.

```c filename=a_closer_after_execution_acts_on_the_first_open_claim.c
int32 f(int32 n) {
    return n;
}
```

```click
verifying "a_closer_after_execution_acts_on_the_first_open_claim.c";

int32 f(int32 n) {
    ensures 2 + 2 == 4;
    ensures result == n;
} by {
    execute();
    assumption();
    normalize();
}
```

```expect
fail: `assumption` found no available fact or held instance for the current goal `(2 + 2) == 4`
```
