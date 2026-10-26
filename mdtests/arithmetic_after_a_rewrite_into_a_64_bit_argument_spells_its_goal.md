# Arithmetic after a rewrite into a 64-bit argument spells its goal

A `rewrite` by an observation equality can replace a `uint64` argument of a
specification function, so the goal no longer matches its written template.
`arithmetic` then spells the goal from the checked state, and a word argument
of any 32-, 64- or 128-bit type is spelled as its term, not only an `int32`
one.

```click
import click::integer;

function spec_f(bytes: uint8[], length: uint64, a0: Integer) -> Integer { a0 + to_integer(length) }
function g(x: Integer) -> Integer { x + 1 }

theorem rewritten_word_argument(bytes: uint8[], n: uint64, r: uint64, a: uint32) {
    requires to_integer(n - r) == to_integer(0u64);
    requires g(to_integer(a)) == to_integer(a);
    requires spec_f(bytes, 0u64, to_integer(a)) == to_integer(a);
    ensures g(to_integer(a)) == spec_f(bytes, n - r, to_integer(a)) by {
        rewrite(to_integer(n - r) == to_integer(0u64));
        solve() using {
            g(to_integer(a)) == to_integer(a);
            spec_f(bytes, 0u64, to_integer(a)) == to_integer(a);
        };
    }
}
```

```expect
pass
```
