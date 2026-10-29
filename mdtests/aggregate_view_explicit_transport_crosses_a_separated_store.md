# A descriptor field is unchanged by a separated pointee store
```c filename=probe.c
struct Descriptor { int32 length; int32 *data; };
void write_first(struct Descriptor *owner) {
    owner->data[0] = 7;
}
```
```click
verifying "probe.c";
void write_first(struct Descriptor *owner) {
    views *owner;
    owns owner->data[0];
    requires separate(memory(owner->data[0..1]), memory(*owner));
    ensures owner->length == old(owner->length);
} by {
    step();
    transport(old(owner->length) == old(owner->length),
              owner->length == old(owner->length)) using {
        at(function.entry, separate(memory(owner->data[0..1]), memory(*owner)));
    };
    step_until(function.exit);
}
```
```expect
pass
```
