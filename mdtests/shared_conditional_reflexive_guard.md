# A rewritten algebraic guard normalizes within a retained conditional

```c filename=shared_conditional_reflexive_guard.c
void unused(void) {}
```

```click
verifying "shared_conditional_reflexive_guard.c";
spec enum Payload { Item(int32) }
function joined(a: Payload, b: Payload) -> int32 { if a == b { 1 } else { 0 } }
theorem identity(a: Payload, b: Payload) {
    requires b == a;
    ensures joined(a, b) == 1 by {
        unfold(joined(a, b));
        rewrite(b == a);
        have a == a by { normalize(); }
        normalize();
    }
}
function joined_uint32(a: Payload, b: Payload) -> uint32 { if a == b { 1 as uint32 } else { 0 as uint32 } }
theorem identity_uint32(a: Payload, b: Payload) {
    requires b == a;
    ensures joined_uint32(a, b) == (1 as uint32) by {
        unfold(joined_uint32(a, b));
        rewrite(b == a);
        normalize();
    }
}
function joined_int64(a: Payload, b: Payload) -> int64 { if a == b { 1 as int64 } else { 0 as int64 } }
theorem identity_int64(a: Payload, b: Payload) {
    requires b == a;
    ensures joined_int64(a, b) == (1 as int64) by {
        unfold(joined_int64(a, b));
        rewrite(b == a);
        normalize();
    }
}
function joined_uint64(a: Payload, b: Payload) -> uint64 { if a == b { 1 as uint64 } else { 0 as uint64 } }
theorem identity_uint64(a: Payload, b: Payload) {
    requires b == a;
    ensures joined_uint64(a, b) == (1 as uint64) by {
        unfold(joined_uint64(a, b));
        rewrite(b == a);
        normalize();
    }
}
```

```expect
pass
```
