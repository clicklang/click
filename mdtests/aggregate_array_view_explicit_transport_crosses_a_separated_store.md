# A descriptor field is unchanged by a separated pointee store
```c filename=probe.c
struct Descriptor { int32 length; int32 *data; };
void write_first(struct Descriptor *owner) {
    owner[1].data[0] = 7;
}
```
```click
verifying "probe.c";
void write_first(struct Descriptor *owner) {
    views owner[0..2];
    owns owner[1].data[0];
    requires separate(memory(owner[1].data[0..1]), memory(owner[0..2]));
    ensures owner[1].length == old(owner[1].length);
} by {
    step();
    transport(old(owner[1].length) == old(owner[1].length),
              owner[1].length == old(owner[1].length)) using {
        at(function.entry, separate(memory(owner[1].data[0..1]), memory(owner[0..2])));
    };
    step_until(function.exit);
}
```
```expect
pass
```
