# A refuted match arm's bridge at function exit rejects a false have

The bridge `have` of a refuted arm at function exit is checked like any other
step, so a false one is refused rather than deferred to an outcome path that
does not exist. Before this was fixed, this proof verified. The positive is
[`a_refuted_match_arm_bridge_at_function_exit_is_checked.md`](a_refuted_match_arm_bridge_at_function_exit_is_checked.md).

```c filename=a_refuted_match_arm_bridge_at_function_exit_rejects_a_false_have.c
int id(int x) { return x; }
```

```click
verifying "a_refuted_match_arm_bridge_at_function_exit_rejects_a_false_have.c";

spec enum Tag { A, B }
resource tag() { field model: Tag; }

int id(int x) {
    owns r: tag();
    requires r.model != Tag::A;
    ensures result == x;
    ensures r.model == old(r.model);
} by {
    execute();
    match r.model ensuring { fact result == x; } {
        Tag::A => { have x == x + 1 by simp(); contradiction(r.model == Tag::A); },
        Tag::B => { },
    }
    simp();
}
```

```expect
fail: `simp` failed
```
