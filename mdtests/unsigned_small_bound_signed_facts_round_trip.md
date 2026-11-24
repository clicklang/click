# A small unsigned bound retains a typed signed range

The derived signed facts use an explicit conversion of a native uint32 value.
They can be cited by simple proof steps and raised back to the same terms.
A value already converted from int32 retains its signed source.

```click
theorem native_unsigned_bound(x: uint32) {
    requires x <= 256u32;
    ensures 0 <= (x as int32) and (x as int32) <= 256 by { close(); }
}

theorem strict_unsigned_bound(x: uint32) {
    requires x < 257u32;
    ensures 0 <= (x as int32) and (x as int32) < 257 by { close(); }
}

theorem converted_signed_bound(x: int32) {
    requires (x as uint32) <= 256u32;
    ensures 0 <= x and x <= 256 by { close(); }
}
```

```expect
pass
```
