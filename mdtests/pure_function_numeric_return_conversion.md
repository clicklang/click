# Pure numeric results obey the checked return type

Opaque calls and unfolded bodies use the declared machine return conversion.
A narrowing body writes its conversion: `(int32) word` can change the value,
so it is not implicit. A widening body converts implicitly.

```click
function narrow(word: uint64) -> int32 { (int32) word }
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
