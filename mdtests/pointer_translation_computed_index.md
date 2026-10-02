# Pointer translation uses explicit bounds on a computed index

The index remains an opaque signed word. Its cited upper bound makes the outer
increment nonwrapping; the rule does not infer arithmetic bounds for its parts.

```click
theorem advance(p: const uint8*, bytes: const uint8*, n: uint64, remaining: int32) {
    requires defined((int32)(uint32)n - remaining);
    requires ((int32)(uint32)n - remaining) < 2147483647;
    requires p == bytes + ((int32)(uint32)n - remaining);
    ensures p + 1 == bytes + ((int32)(uint32)n - remaining + 1) by {
        arithmetic() using {
            p == bytes + ((int32)(uint32)n - remaining);
            ((int32)(uint32)n - remaining) < 2147483647;
        }
    }
}
```

```expect
pass
```
