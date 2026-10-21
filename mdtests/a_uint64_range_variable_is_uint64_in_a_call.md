# A uint64 range variable is uint64 in a call

The variable of `(0u64..n).all(|k| { ... })` has the bounds' type, `uint64`,
everywhere in the body, including as a pure-function argument, in a
requirement and in an ensures.

```c filename=a_uint64_range_variable_is_uint64_in_a_call.c
void unused(void) {}
```

```click
verifying "a_uint64_range_variable_is_uint64_in_a_call.c";

function g(a: uint64) -> uint64 { a }

theorem required(n: uint64, u: uint64) {
    requires (0u64..n).all(|k| { g(k) == k });
    requires u < n;
    ensures g(u) == u by {
        instantiate((0u64..n).all(|k| { g(k) == k }), u);
    }
}

theorem ensured(n: uint64) {
    ensures (0u64..n).all(|k| { g(k) == k }) by {
        intro();
        intro();
        unfold(g(k));
    }
}
```

```expect
pass
```
