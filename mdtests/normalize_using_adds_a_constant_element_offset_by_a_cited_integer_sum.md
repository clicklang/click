# `normalize using` adds a constant element offset by a cited Integer sum

A constant offset is a whole number of elements, so it takes part in the
cited index sum like an index does. `(bytes + prefix) + 3` and
`bytes + total` are one address when a cited premise states that `total` is
`prefix` plus 3, exactly. This is how a byte read through a pointer at a
symbolic position, `q[3]` for `q == p + k`, is shown to read `p[k + 3]`.

```click
import click::integer;

theorem byte_constant_suffix(bytes: uint8[], prefix: uint64, total: uint64) {
    requires to_integer(total) == to_integer(prefix) + 3;
    ensures (bytes + prefix) + 3 == bytes + total by {
        normalize() using { to_integer(total) == to_integer(prefix) + 3; };
    }
}

theorem byte_constant_suffix_of_a_native_sum(bytes: uint8[], prefix: uint64) {
    requires to_integer(prefix + 3u64) == to_integer(prefix) + 3;
    ensures (bytes + prefix) + 3 == bytes + (prefix + 3u64) by {
        normalize() using { to_integer(prefix + 3u64) == to_integer(prefix) + 3; };
    }
}

theorem word_constant_suffix(words: int32[], prefix: uint64, total: uint64) {
    requires 1 + to_integer(prefix) == to_integer(total);
    ensures words + total == (words + prefix) + 1 by {
        normalize() using { 1 + to_integer(prefix) == to_integer(total); };
    }
}
```

```expect
pass
```
