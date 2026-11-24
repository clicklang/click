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
    have contains(memory(owner[1].data[0..1]), memory(owner[1].data[0..1])) by { apply(click::separation::contains_refl(memory(owner[1].data[0..1]))); }
    have contains(memory(owner[0..2]), memory((&owner[1].length)[0..1])) by { close(); }
    have separate(memory(owner[1].data[0..1]), memory((&owner[1].length)[0..1])) by {
        apply(click::separation::separate_restrict(memory(owner[1].data[0..1]), memory(owner[0..2]), memory(owner[1].data[0..1]), memory((&owner[1].length)[0..1])));
    }
    step();
    have separate(statement(0).footprint, memory((&owner[1].length)[0..1])) by {
        close() using { at(statement(0).entry, separate(memory(owner[1].data[0..1]), memory((&owner[1].length)[0..1]))); };
    }
    have owner[1].length == old(owner[1].length) by {
        preserve(memory((&owner[1].length)[0..1]), statement(0));
    }
    step_until(function.exit);
}
```
```expect
pass
```
