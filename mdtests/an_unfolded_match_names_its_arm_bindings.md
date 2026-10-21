# An unfolded match names its arm bindings

Unfolding a function whose body is a `match` puts the match into the goal. Each
arm's pattern binds the fields its body reads, so the binding and its use print
alike.

```c filename=an_unfolded_match_names_its_arm_bindings.c
void unused(void) {}
```

```click
verifying "an_unfolded_match_names_its_arm_bindings.c";

spec enum Ctx { Top, Up(Ctx) }

function d(c: Ctx) -> Integer decreases c {
    match c { Ctx::Top => 0, Ctx::Up(u) => 1 + d(u) }
}

theorem t(c: Ctx) {
    ensures d(c) >= 0 by {
        unfold(d(c));
        contradiction(1 == 5);
    }
}
```

```expect
fail: goal: match c { Top => 0, Up(k) => 1 + d(k) } >= 0
```
