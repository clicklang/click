# strlen of an empty string and memcmp use the catalog contracts

The standard library's libc catalog supplies `strlen` and `memcmp`
contracts without declarations in the sidecar. `strlen` on a readable C
string whose first byte is the terminator returns zero through the catalog's
`old(bytes[0]) == '\0' implies result == 0u64` postcondition, and `memcmp`
over a viewable two-byte range discharges its range and per-byte `defined`
preconditions from the caller's `viewable` requirement. This catches a catalog contract whose
precondition or postcondition is not lowered and checked at a call.

```c filename=strlen_of_an_empty_string_and_memcmp_use_the_catalog_contracts.c
uint64 empty_length(uint8 text[]) {
    uint64 length;
    length = strlen(text);
    return length;
}

int32 compare_self(uint8 bytes[]) {
    return memcmp(bytes, bytes, 2);
}
```

```click
verifying "strlen_of_an_empty_string_and_memcmp_use_the_catalog_contracts.c";

uint64 empty_length(uint8 text[]) {
    requires cstr_readable(text);
    requires text[0] == '\0';
    ensures result == 0u64 by { execute(); simp(); }
}

int32 compare_self(uint8 bytes[]) {
    requires viewable(bytes[0..2]);
    ensures 1 == 1 by { execute(); simp(); }
}
```

```expect
pass
```
