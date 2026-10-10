# C-string length witnesses carry viewability

`cstr_len` is an existentially usable description of a terminated byte
prefix. Its witness must also authorize the complete prefix, so a caller can
pass that range to a memory-reading external contract without separately
repeating the hidden length's viewability fact.

```c filename=cstr_loadable_witness.c
uint64 cstr_loadable_witness(uint8 source[], uint64 len) {
    return len;
}
```

```click
verifying "cstr_loadable_witness.c";

theorem cstr_len_exposes_viewable(source: uint8[], len: uint64) {
    requires cstr_len(source, len);

    ensures viewable(source[0..len + 1u64]) by {
        apply(cstr_len_is_viewable(source, len));
    }
}

uint64 cstr_loadable_witness(uint8 source[], uint64 len) {
    requires cstr_len(source, len);
    requires viewable(source[0..len + 1u64]);

    ensures result == len;
} by {
    execute();
    simp();
}
```

```expect
pass
```
