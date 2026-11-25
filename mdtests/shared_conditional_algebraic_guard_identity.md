# Shared conditional match identity

```c filename=shared_conditional_algebraic_guard_identity.c
void unused(void) {}
```

```click
verifying "shared_conditional_algebraic_guard_identity.c";
spec enum Payload { Item(int32), Empty }
function flag(x: Payload) -> int32 { 1 }
function joined(x: Payload, unused: int32) -> int32 {
    if x == Payload::Empty() { match x { Payload::Item(n) => n, Payload::Empty => 0, } } else { 0 }
}
theorem identity(x: Payload, a: int32, b: int32) {
    ensures joined(x, a) == joined(x, b) by {
        match x {
            Payload::Item(n) => {
                rewrite(x, Payload::Item(n));
                unfold(joined(Payload::Item(n), a));
                unfold(joined(Payload::Item(n), b));
                close();
            },
            Payload::Empty => {
                rewrite(x, Payload::Empty);
                unfold(joined(Payload::Empty, a));
                unfold(joined(Payload::Empty, b));
                close();
            },
        }
    }
}
```

```expect
pass
```
