# A `uint64` range-quantifier variable types as `int32` in a call

Soundness: not soundness. The type checker refuses a well-typed proposition;
nothing is accepted. A `uint64` range quantifier whose body passes its
variable to a pure function cannot be stated at all, in a requirement or an
ensures.

The violated invariant: the variable of `(lo..hi).all(|k| { ... })` has the
type of the range bounds, here `uint64`, everywhere in the body. The
[instantiation reference](../docs/reference/tactics/index.md#universal-instantiation)
lists range quantifiers "over either type" (`int32` or `uint64`). Inside a
call argument, the type checker instead gives `k` the type `int32` and
refuses `g(k)` for `g(a: uint64)`. The same body is accepted elsewhere:

- `forall (k: uint64) { g(k) == k }` (an explicit binder type) verifies with
  the same `instantiate`;
- `(0..n).all(|k| { g(k) == k })` over `int32` with `g(a: int32)` verifies;
- `(0u64..n).all(|k| { k * 2u64 >= k })`, with `k` in arithmetic rather than
  a call, verifies.

```c filename=z.c
void unused() {}
```

```click
verifying "z.c";

function g(a: uint64) -> uint64 { a }

theorem t(n: uint64, u: uint64) {
    requires (0u64..n).all(|k| { g(k) == k });
    requires u < n;
    ensures g(u) == u by {
        instantiate((0u64..n).all(|k| { g(k) == k }), u);
    }
}
```

`click verify` prints:

```text
type error:
  while checking module `z.click`
  function `g` argument 0 expects uint64, got int32 in theorem `t` requirement; a conversion that can change the value is written, as in `(uint64) ...`

  --> z.click:5:1
  5 | theorem t(n: uint64, u: uint64) {
    | ^^^^^^^
```

(The module name in the message is the `.click` file's name.) Writing the
same quantifier as the goal, `ensures (0u64..n).all(|k| { g(k) == k })`, fails
with the same message ending "in theorem `t` ensure".

## Acceptance criteria

- The reproduction verifies.
- `ensures (0u64..n).all(|k| { g(k) == k }) by { intro(); intro(); unfold(g(k)); }`
  passes type checking.
- A range quantifier over `int32` bounds still types its variable `int32`, so
  `g(k)` with `g(a: uint64)` over `(0..n)` is still refused.
- A regression keeps the source pattern: a `uint64` range quantifier whose
  body passes the variable to a `uint64` pure function, in a requirement and
  in an ensures.
