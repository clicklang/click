# A descriptor field is unchanged by a separated pointee store
```c filename=probe.c
struct Descriptor { int32 length; int32 *data; };
void write_first(struct Descriptor *owner) {
    owner->length = 7;
}
```
```click
verifying "probe.c";
void write_first(struct Descriptor *owner) {
    owns *owner;
    ensures owner->length == old(owner->length);
} by {
    step();
    transport(old(owner->length) == old(owner->length),
              owner->length == old(owner->length)) using {
    };
    step_until(function.exit);
}
```
```expect
fail: `transport using` found no frame evidence
```
