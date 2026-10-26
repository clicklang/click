# Pointer translation uses explicit bounds on a computed index

The index remains an opaque signed word. Its cited upper bound makes the outer
increment nonwrapping; the rule does not infer arithmetic bounds for its parts.

```click
theorem advance(p: const uint8*, bytes: const uint8*, n: uint64, remaining: int32) {
    requires defined(n as uint32 as int32 - remaining);
    requires to_integer((n as uint32 as int32 - remaining)) < 2147483647;
    requires p == bytes + (n as uint32 as int32 - remaining);
    ensures p + 1 == bytes + (n as uint32 as int32 - remaining + 1) by {
        solve() using {
            p == bytes + (n as uint32 as int32 - remaining);
            to_integer((n as uint32 as int32 - remaining)) < 2147483647;
        };
    }
}
```

```expect
pass
```
