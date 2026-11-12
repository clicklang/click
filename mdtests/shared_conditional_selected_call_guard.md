# Shared conditional selected call guard

Unfolding a machine equality introduces an Integer observation of a shared
conditional. After rewriting its guard and arm, selecting the arm must retain
the same numeric identity as the independently cited opaque call.

```c filename=shared_conditional_selected_call_guard.c
void unused(void) {}
```

```click
verifying "shared_conditional_selected_call_guard.c";
spec enum Payload { Item(int32) }
function flag(x: Payload) -> int32 { 1 }
function value(x: Payload) -> int32 { match x { Payload::Item(n) => n, } }
function wrapped(x: Payload) -> Payload { x }
function joined(x: Payload) -> int32 { if flag(x) == 1 { value(x) } else { 0 } }
theorem selected(x: Payload) {
    requires flag(x) == 1;
    requires value(x) == 1;
    requires flag(wrapped(x)) == flag(x);
    requires value(wrapped(x)) == value(x);
    ensures joined(wrapped(x)) == 1 by {
        unfold(joined(wrapped(x)));
        rewrite(flag(wrapped(x)) == flag(x));
        rewrite(value(wrapped(x)) == value(x));
        normalize() using { flag(x) == 1; value(x) == 1; };
    }
}
```

```expect
pass
```
