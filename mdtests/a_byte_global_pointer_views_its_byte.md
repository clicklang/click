# A byte global pointer views its byte

`current` is a global `uint8 *`, so `views current[0..1]` is one byte and
`current[0]` reads it. Click once took no element type from a global
pointer and counted the range as one `int32` cell, so the contract did not
close. The `int32` form is `resource_address_view.md`.

```c filename=byte_address_view.c
uint8 value = 7;
uint8* current = &value;
uint8 read() { return current[0]; }
```

```click
verifying "byte_address_view.c";
uint8 read() {
    views current;
    views current[0..1];
    ensures result == current[0];
}
```

```expect
pass
```
