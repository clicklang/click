# Pure-function applications use their declared machine argument type

A rewritten wide value and an unsuffixed literal must name the same call.
Unfolding also converts the argument before substituting it into the body.
An `int32` result passed to a `uint64` parameter changes sign, so its
conversion is written.

```click
function is_zero(word: uint64) -> int32 {
    if word == 0 { 1 } else { 0 }
}
function byte_plus_one(word: uint8) -> int32 { word + 1 }
function identity(word: int32) -> int32 { word }

theorem zero_word(word: uint64) {
    requires word == 0;
    ensures is_zero(word) == 1 by {
        rewrite(word == 0);
        unfold(is_zero(0));
        simp();
    }
}
theorem byte_call() {
    ensures byte_plus_one(42) == 43 by {
        unfold(byte_plus_one(42)); simp();
    }
}
theorem nested_call(word: int32) {
    requires word == 0;
    ensures is_zero((uint64) identity(word)) == 1 by {
        unfold(is_zero((uint64) identity(word)));
        unfold(identity(word)); simp();
    }
}
```

```expect
pass
```
