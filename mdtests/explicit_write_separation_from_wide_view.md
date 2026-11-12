# A write proves a wide-view separation obligation explicitly

The separation spelling also lowers its range-formation prerequisites.
The driver must accept that complete goal and retain the separation proof.

```c filename=a_separation_from_a_64_bit_range.c
unsigned char set_and_read(int *value, const unsigned char *bytes, unsigned long length, unsigned long index) {
    *value = 7;
    return bytes[index];
}
```

```click
verifying "a_separation_from_a_64_bit_range.c";
uint8 set_and_read(int32* value, const uint8* bytes, uint64 length, uint64 index) {
    requires index < length;
    requires separate(memory(value[0..1]), memory(bytes[0..length]));
    owns value[0..1];
    views bytes[0..length];
    ensures result == old(bytes[index]);
    ensures value[0] == 7;
} by {
        have separate(memory(value[0..1]), memory(bytes[0..length])) by { assumption(); }
        step() by { assumption(); }
}
```

```expect
pass
```
