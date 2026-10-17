# Pure numeric results obey the checked return type

Opaque calls and unfolded bodies use the declared machine return conversion.

```click
function narrow(word: uint64) -> int32 { word }
function widen(word: int32) -> int64 { word }
theorem narrowing() {
    ensures narrow(4294967296) == 0 by {
        unfold(narrow(4294967296)); normalize();
    }
}
theorem widening() {
    ensures widen(-1) == -1 by { unfold(widen(-1)); normalize(); }
}
```

```expect
pass
```
