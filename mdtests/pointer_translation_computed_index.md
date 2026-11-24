# Pointer translation uses explicit bounds on a computed index

The index remains an opaque signed word. Its cited upper bound makes the outer
increment nonwrapping; the rule does not infer arithmetic bounds for its parts.

```click
theorem advance(p: const uint8*, bytes: const uint8*, n: uint64, remaining: int32) {
    requires defined(n as uint32 as int32 - remaining);
    requires to_integer((n as uint32 as int32 - remaining)) < 2147483647;
    requires p == bytes + (n as uint32 as int32 - remaining);
    ensures p + 1 == bytes + (n as uint32 as int32 - remaining + 1) by {
        apply(click::integer::int32_subtract_to_integer(n as uint32 as int32, remaining));
        have to_integer(n as uint32 as int32) - to_integer(remaining) < 2147483647 by {
            rewrite(to_integer(n as uint32 as int32) - to_integer(remaining),
                    to_integer(n as uint32 as int32 - remaining));
            close();
        }
        have (n as uint32 as int32 - remaining) < 2147483647 by close();
        have defined((n as uint32 as int32 - remaining) + 1) by {
            apply(click::integer::int32_increment_below_max_is_defined((n as uint32 as int32 - remaining)));
        }
        have (bytes + (n as uint32 as int32 - remaining)) + 1 == bytes + ((n as uint32 as int32 - remaining) + 1) by {
            apply(click::integer::uint8_pointer_add_associate_int32(bytes, (n as uint32 as int32 - remaining), 1));
        }
        rewrite(p, bytes + (n as uint32 as int32 - remaining));
        close();
    }
}
```

```expect
pass
```
