# A `void *` step in a spec reads the next byte

`q + 1` is one byte past `q`, so reading it as a `uint8` reads byte 1 of the
buffer, the byte the C body reads. A four-byte step would read byte 4.

```c filename=void_pointer_spec_step_reads_the_next_byte.c
uint8 second(void *q) {
    return ((uint8 *)q)[1];
}
```

```click
verifying "void_pointer_spec_step_reads_the_next_byte.c";

uint8 second(void *q) {
    views (q as (uint8 *))[0..2];
    ensures result == *((q + 1) as (uint8 *));
}
```

```expect
pass
```
