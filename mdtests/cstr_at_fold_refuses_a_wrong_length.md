# A C string cannot be folded at a wrong length

`cstr_at(p, len)` states that byte `len` is the first terminator. The bytes
determine that length, so a fold at any other length must fail. `mk` holds a
viewed string of length `n` and claims to produce `cstr_at(p, n + 1)`: byte
`n` is a terminator, so the body fact that the first `n + 1` bytes are nonzero
cannot be established.

```c filename=cstr_at_fold_refuses_a_wrong_length.c
int32 mk(const uint8 *p, uint64 n) { return 0; }
```

```click
// The resource proposed for `library/cstr.click`, declared here because a
// library module cannot yet export a composite resource: a view of the bytes
// of `p` through its first terminator, with the facts that make them the C
// string of length `len`.
resource cstr_at(p: const uint8*, len: uint64) {
    views p[0..len + 1u64];
    fact len < 18446744073709551615u64;
    fact forall (k: uint64) { 0u64 <= k and k < len implies p[k] != '\0' };
    fact p[len] == '\0';
    fact forall (k: uint64) { 0u64 <= k and k < len + 1u64 implies defined(p[k]) };
}

verifying "cstr_at_fold_refuses_a_wrong_length.c";

int32 mk(const uint8* p, uint64 n) {
    views p[0..n + 2u64];
    requires n < 18446744073709551614u64;
    requires forall (k: uint64) { 0u64 <= k and k < n implies p[k] != '\0' };
    requires p[n] == '\0';
    requires forall (k: uint64) { 0u64 <= k and k < n + 2u64 implies defined(p[k]) };
    produces cstr_at(p, n + 1u64);
} by {
    execute();
    fold(cstr_at(p, n + 1u64));
}
```

```expect
fail: requires an exact body fact
```
