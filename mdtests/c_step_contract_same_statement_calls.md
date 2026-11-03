# A second call cannot search an ambiguous owner/view bucket for its result alias

The first call returns a value equal to `x`. Its owned and observed `Permit(x)`
entries are not an exact match for the second call's `Permit(result)`. Direct
support selection declines this non-singleton bucket rather than searching it.
The exact-resource sibling fixture separately checks that contract selection
does not leak between calls.

```c filename=joint.c
int32 invoke(int32 (*callback)(int32), int32 x) {
    return callback(callback(x));
}
```

```click
abstract resource Permit(x: int32);
contract int32 First(int32 x) { owns Permit(x); ensures result == x; }
contract int32 Second(int32 x) { owns Permit(x); ensures result == x; }
verifying "joint.c";
int32 invoke(int32 (*callback)(int32), int32 x) {
    requires First(callback);
    requires Second(callback);
    owns Permit(x);
    ensures result == x;
} by { step(First); }
```

```expect
fail: missing resource fact `owns Permit(statement(0).call(callback, 0).result)`
```
