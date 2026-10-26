# A binder named like a type is refused beside `as`

An `as` clause binds a name (a source alias, a loop label, an induction
hypothesis, an introduced variable), and `e as uint32` is a cast, so the
bound name may not be a type name.

```c filename=zero.c
int zero(void) { return 0; }
```

```click
verifying "zero.c" as uint32;
int32 zero() {
    ensures result == 0;
}
```

```expect
fail: `uint32` is a type name, which `as` reads as a cast; bind another name
```
