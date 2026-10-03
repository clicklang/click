# A uint64 bound follows a constant length equality

A slice bounds check must retain the 64-bit comparison: a high-word index
cannot be truncated before deciding whether it is below the length.
The checker transports an existing order fact through the length's constant
equality by reading only the queried equality components.

```c filename=uint64_order_through_constant_length.c
int32 below(uint64 index, uint64 length) {
    if (index < length) {
        return 1;
    }
    return 0;
}
```

```click
verifying "uint64_order_through_constant_length.c";
int32 below(uint64 index, uint64 length) {
    requires index < 4u64;
    requires length == 4u64;
    ensures result == 1;
} by { execute(); simp(); }
```

```expect
pass
```
