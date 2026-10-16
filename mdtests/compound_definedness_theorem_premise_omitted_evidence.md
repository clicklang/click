# An explicit evidence list cannot import an omitted ambient guard

The whole sum is known defined. Listing only the inner addition does not
provide the theorem with the outer guard.

```c filename=omitted_guard.c
int32 probe(int32 a, int32 b, int32 c) { return 0; }
```

```click
import click::integer;

verifying "omitted_guard.c";
int32 probe(int32 a, int32 b, int32 c) {
    requires defined(a + b + c);
    ensures result == 0;
} by {
    apply(int32_add_to_integer(a + b, c)) using { defined(a + b); };
    execute(); simp();
}
```

```expect
fail: required exact fact for theorem `click::integer::int32_add_to_integer` is unavailable
```
