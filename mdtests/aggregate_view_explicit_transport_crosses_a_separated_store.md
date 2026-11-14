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
    have contains(memory(owner->data[0..1]), memory(owner->data[0..1])) by { normalize(); }
    have contains(memory(*owner), memory((&owner->length)[0..1])) by { normalize(); }
    have separate(memory(owner->data[0..1]), memory((&owner->length)[0..1])) by {
        apply(click::separation::separate_restrict(memory(owner->data[0..1]), memory(*owner), memory(owner->data[0..1]), memory((&owner->length)[0..1]))) using {
            separate(memory(owner->data[0..1]), memory(*owner));
            contains(memory(owner->data[0..1]), memory(owner->data[0..1]));
            contains(memory(*owner), memory((&owner->length)[0..1]));
        };
    }
    step();
    have separate(statement(0).footprint, memory((&owner->length)[0..1])) by {
        normalize() using { at(statement(0).entry, separate(memory(owner->data[0..1]), memory((&owner->length)[0..1]))); };
    }
    have owner->length == old(owner->length) by {
        preserve(separate(statement(0).footprint, memory((&owner->length)[0..1])));
    }
    step_until(function.exit);
}
```
```expect
pass
```
