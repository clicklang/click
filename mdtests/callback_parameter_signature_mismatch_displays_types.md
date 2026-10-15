# A callback parameter mismatch displays both signatures

```c filename=callback.c
int32 apply(int32 (*f)(int32), int32 x) { return f(x); }
```

```click
verifying "callback.c";
int32 apply(uint32 (*f)(uint32), int32 x) {
    ensures result == 0;
}
```

```expect
fail: .click has uint32 (*)(uint32) f, C has int32 (*)(int32) f
```
