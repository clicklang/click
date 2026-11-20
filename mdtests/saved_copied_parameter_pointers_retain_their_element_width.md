# Saved pointer fields of copied parameters retain their element width

The selected call's parameter layout supplies the type of its pointer field.
A resource descriptor observes that type without granting backing authority.

```c filename=saved_field.c
struct bytes { uint8* data; uint64 size; };
uint64 size(struct bytes v) { return v.size; }
uint64 forwarded(struct bytes v) { return size(v); }
```

```click
import click::separation;
verifying "saved_field.c";
uint64 size(struct bytes v) {
    ensures result == v.size;
}
uint64 forwarded(struct bytes v) {
    ensures result == v.size;
} by {
    step_until(call(0).entry);
    step();
    have contains(memory(at(call(0).entry, call(0).parameter(v).data)[0..4]), memory(at(call(0).entry, call(0).parameter(v).data)[0..4])) by {
        apply(click::separation::contains_refl(memory(at(call(0).entry, call(0).parameter(v).data)[0..4])));
    }
    step_until(function.exit);
    solve();
}
```

```expect
pass
```
