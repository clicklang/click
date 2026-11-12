# Shared conditional match identity

```c filename=shared_conditional_match_identity.c
void unused(void) {}
```

```click
verifying "shared_conditional_match_identity.c";
spec enum Payload { Item(int32), Empty }
function flag(x: Payload) -> int32 { 1 }
function joined(x: Payload, unused: int32) -> int32 {
    if flag(x) == 1 { match x { Payload::Item(n) => n, Payload::Empty => 0, } } else { 0 }
}
theorem identity(x: Payload, a: int32, b: int32) {
    ensures joined(x, a) == joined(x, b) by {
        unfold(joined(x, a));
        unfold(joined(x, b));
        normalize();
    }
}
```

```expect
pass
```
