# A cited Integer sum relates element indices

An offset is the exact sum of its indices times the element width, for every
index type. So `(bytes + prefix) + suffix` and `bytes + total` are one address
when a cited premise states `total`'s exact value as the sum of the other two,
in either order or orientation. When both sides share a base offset, apply
the same theorem at the shifted pointer.

```click
import click::integer;

theorem unsigned_offset_sum(bytes: uint8[], prefix: uint64, suffix: uint64, total: uint64) {
    requires to_integer(total) == to_integer(prefix) + to_integer(suffix);
    ensures (bytes + prefix) + suffix == bytes + total by {
        solve() using { to_integer(total) == to_integer(prefix) + to_integer(suffix); };
    }
}

theorem signed_offset_sum(words: int32[], prefix: int32, suffix: int32, total: int32) {
    requires to_integer(suffix) + to_integer(prefix) == to_integer(total);
    ensures words + total == (words + prefix) + suffix by {
        solve() using { to_integer(suffix) + to_integer(prefix) == to_integer(total); };
    }
}

theorem shared_offsets_cancel(bytes: uint8[], base: uint64, prefix: uint64, suffix: uint64, total: uint64) {
    requires to_integer(total) == to_integer(prefix) + to_integer(suffix);
    ensures ((bytes + base) + prefix) + suffix == (bytes + base) + total by {
        apply(unsigned_offset_sum(bytes + base, prefix, suffix, total));
    }
}

theorem loads_agree(bytes: uint8[], prefix: uint64, suffix: uint64, total: uint64) {
    requires to_integer(total) == to_integer(prefix) + to_integer(suffix);
    ensures (bytes + prefix)[suffix] == bytes[total] by {
        have (bytes + prefix) + suffix == bytes + total by {
            solve() using { to_integer(total) == to_integer(prefix) + to_integer(suffix); };
        }
        rewrite((bytes + prefix) + suffix, bytes + total);
        solve();
    }
}
```

```expect
pass
```
