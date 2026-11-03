# A selection does not leak between same-statement calls with an exact resource

```c filename=joint.c
int32 invoke(int32 (*callback)(int32), int32 x) {
    return callback(callback(x));
}
```

```click
abstract resource Permit();
contract int32 First(int32 x) { owns Permit(); ensures result == x; }
contract int32 Second(int32 x) { owns Permit(); ensures result == x; }
verifying "joint.c";
int32 invoke(int32 (*callback)(int32), int32 x) {
    requires First(callback);
    requires Second(callback);
    owns Permit();
    ensures result == x;
} by { step(First); }
```

```expect
fail: ambiguous callback resource transition
```
