# Unfolded algebraic calls keep numeric argument identity

The call result's retained numeric arguments must preserve reflexivity after
unfolding, including a call inside the division argument.

```click
import click::rust::slice;
function half(s: Slice<uint8>) -> Slice<uint8> {
    slice::from_raw_parts(slice::as_ptr(s), slice::len(s) / 2u64)
}
theorem unfolded_half(s: Slice<uint8>) {
    requires slice::len(s) == 4u64;
    ensures half(s) == slice::from_raw_parts(slice::as_ptr(s), slice::len(s) / 2u64) by {
        unfold(half(s));
        normalize();
    }
}
```

```expect
pass
```
