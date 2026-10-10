# Dynamic range transport is required across a local declaration

```c filename=cstr_dynamic_transport_required.c
uint64 read_terminator(uint8 bytes[], uint64 known_len) {
    uint64 length;
    length = strlen(bytes);
    return length;
}
```

```click
verifying "cstr_dynamic_transport_required.c";

uint64 read_terminator(uint8 bytes[], uint64 known_len) {
    requires cstr_readable(bytes);
    requires cstr_readable_len(bytes, known_len);
    requires known_len < 18446744073709551615u64;
    requires viewable(bytes[0..known_len + 1u64]);
    ensures result < 18446744073709551615u64 by {
        unfold(cstr_readable);
        unfold(cstr_readable_len);
        execute_until(statement(1));
        have viewable(bytes[0..known_len + 1u64]) by {
            assumption();
        }
    }
}
```

```expect
fail: assumption` requires the current goal as an available semantic fact
```
