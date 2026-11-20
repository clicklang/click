# Address observations retain saved pointer values and named call results

Observing an address consumes the pointer value, including a saved value or a
modular call result. It does not add bounds or permission to dereference it.

```c filename=addresses.c
int32* identity(int32* p) { return p; }
int32* forwarded(int32* p) { return identity(p); }
```

```click
import click::separation;
verifying "addresses.c";
int32* identity(int32* p) {
    ensures result == p;
}
int32* forwarded(int32* p) {
    ensures result == p;
} by {
    step_until(call(0).entry);
    step();
    have address(call(0).result) == address(old(p)) by { known(); }
    have address(at(function.entry, p)) == old(address(p)) by { known(); }
    have contains(memory(at(call(0).exit, call(0).result)[0..1]), memory(at(call(0).exit, call(0).result)[0..1])) by {
        apply(click::separation::contains_refl(memory(at(call(0).exit, call(0).result)[0..1])));
    }
    step_until(function.exit);
    solve();
}
```

```expect
pass
```
