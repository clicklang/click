# Outcome tactic obligations precede its effects

The tactic's promise about its output cannot prove its own requirement.

```c filename=tactic_requires_at_exit.c
int32 directly(void) { return 0; }
```

```click
verifying "tactic_requires_at_exit.c";

resource counter() { field next: int32; }

tactic make_counter(n: int32) {
    requires 1 <= n;
    produces item: counter();
    ensures 1 <= item.next;
} by {
    let item = fold(counter(), { next: n });
}

int32 directly() {
    produces c: counter();
} by {
    step_until(function.exit);
    let { item: c } = make_counter(result);
}
```

```expect
fail: requires
```
