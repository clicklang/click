# A fold takes a constant prefix from an owned range with a symbolic end

`cut` owns `s[0..n]` and folds `one(s)`, whose body owns the single byte
`s[0..1]`. The fold splits the owned range into the byte the composite takes
and the remainder `s[1..n]`, and the kernel checks that the composite's body
and the remainder are exactly the range it replaced. The constant piece and
the remainder meet at `1` although the piece is a 32-bit range and the
remainder a 64-bit one, so the rewrite is accepted. Shortening a C string,
[`cstr_at_consumes_and_produces_a_shorter_string.md`](cstr_at_consumes_and_produces_a_shorter_string.md),
folds the same way.

```c filename=fold_a_constant_prefix_of_a_symbolic_owned_range.c
void cut(uint8 *s, uint64 n) { }
```

```click
resource one(p: const uint8*) {
    owns p[0..1u64];
}

verifying "fold_a_constant_prefix_of_a_symbolic_owned_range.c";

void cut(uint8* s, uint64 n) {
    requires 0u64 < n;
    requires n < 1000u64;
    consumes s[0..n];
    produces one(s);
    produces s[1u64..n];
} by {
    fold(one(s));
    execute();
}
```

```expect
pass
```
