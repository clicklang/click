# Shared conditional match identity

```c filename=shared_conditional_algebraic_guard_refusal.c
void unused(void) {}
```

```click
verifying "shared_conditional_algebraic_guard_refusal.c";
spec enum Payload { Item(int32), Empty }
function flag(x: Payload) -> int32 { 1 }
function joined(x: Payload, other: Payload) -> int32 {
    if x == other { match x { Payload::Item(n) => n, Payload::Empty => 0, } } else { 0 }
}
theorem identity(x: Payload, a: Payload, b: Payload) {
    ensures joined(x, a) == joined(x, b) by {
        unfold(joined(x, a));
        unfold(joined(x, b));
        normalize();
    }
}
```

```expect
fail: `normalize` goal did not normalize to true
```
