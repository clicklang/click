# Click library

The Click library is the public Surface Click API in the
[`library/`](https://github.com/clicklang/click/tree/master/library) modules.
It isn't the Rust crate's internal `pub` API. This page lists it one module
per section.

## Layers

Each library declaration is in one of three layers, and its layer decides
how far it is trusted:

- **Verifier primitives** are part of the language, not the library. The
  abstract resources `mutex_guard`, `mutex_live`, `mutex_use`, `publisher`,
  `subscriber`, `authority` and `allocation`, and
  `__click_constant_p_unknown`, are given their meaning by the kernel or the
  C front end. Their declarations sit in `library/primitives.click` and
  `library/c/builtins.click`, and are documented under
  [verifier primitives](../language/index.md#verifier-primitives) in the
  language reference, not here.
- **Language library models** state what the C, C++ or Rust library the
  verified code calls does. Each is an assumed `extern` contract, listed in
  [trust](../../concepts/trust.md#the-click-library), and it comes with the
  code that uses it, not with a sidecar import. `click::c::string` is written
  in Click below. The C front end builds in the allocator family
  ([heap allocation](../language/c.md#heap-allocation)) and writes the
  `snprintf` contracts ([formatted output](../language/c.md#formatted-output)),
  and the C++ and Rust importers append the generic contracts of
  `library/cpp/` and `library/rust/core.click`, written out at each called
  instance, and the Rust integer-method contracts of
  `library/rust/integers.click` an import calls. The Rust core-method
  contracts state their results with the `click::rust::` modules below.
- **The specification library** is checked Click: types, pure functions,
  predicates and theorems. A theorem is either proved or a kernel standard
  theorem whose declaration is checked against its kernel builder. The
  `click::rust::vec` and `click::rust::chunks_exact` axioms are trusted, not
  proved.

## Modules

| Module | Seen | Layer |
| --- | --- | --- |
| [`click::nat`](#clicknat) | implicit | specification |
| [`click::list`](#clicklist) | implicit | specification |
| [`click::option`](#clickoption) | implicit | specification |
| [`click::result`](#clickresult) | implicit | specification |
| [`click::integer`](#clickinteger) | `import click::integer;` | specification |
| [`click::permutation`](#clickpermutation) | `import click::permutation;` | specification |
| [`click::bytes`](#clickbytes) | `import click::bytes;`, or with `click::c::string` | specification |
| [`click::cstr`](#clickcstr) | `import click::cstr;`, or with `click::c::string` | specification |
| [`click::format`](#clickformat) | `import click::format;`; named by path in `snprintf` contracts | specification |
| [`click::c::string`](#clickcstring) | when the C declares or calls one of its functions | C library model |
| [C++ standard library models](#c-standard-library-models), `library/cpp/` (not a module) | when a C++ import calls one of its functions | C++ library model |
| [`click::rust::i8` ... `click::rust::usize`](#clickrusti8-through-clickrustusize) | `import click::rust::u32;`; named by path in Rust core-method contracts | specification |
| [`click::rust::vec`](#clickrustvec) | `import click::rust::vec;` | specification, with trusted axioms |
| [`click::rust::slice`](#clickrustslice) | `import click::rust::slice;` | specification |
| [`click::rust::chunks_exact`](#clickrustchunks_exact) | `import click::rust::chunks_exact;` | specification, with trusted axioms |
| [Rust core models](#rust-core-models), `library/rust/core.click` (not a module) | when a Rust import calls one of its methods | Rust library model |
| [`click::separation`](#clickseparation) | `import click::separation;` | specification |

`click::primitives` and `click::c::builtins` are implicit too; they hold the
verifier primitives. Any module not marked implicit needs its
`import click::...;` line; see
[Click library imports](../../concepts/sidecars.md#click-library-imports).

## Checking this page

Every declaration below is copied exactly from the library and checked by the
documentation gate. The same gate compares declaration names bidirectionally,
so adding, removing, or changing a public symbol requires a matching reference
update.
A C++ or Rust library model is named by the path it models,
`std::span<T>::size` or `Vec::push`, and the gate checks that the tests its
**Verified use** cites call it.

A proof inside the library sees only the library theorems declared above
it, in module order. Built-in tactics apply library theorems by name without
a citation, so declaration order is what keeps library proofs acyclic; a
proof that cites a later theorem of its own module is refused with that
reason. Sidecars apply library theorems as declarations and are not limited
this way.

Pure function calls remain symbolic until explicitly unfolded. Predicates
remain opaque until a proof explicitly unfolds them or applies a theorem that
exposes the needed consequence. Theorems can be applied when their stated
requirements are available.

## `click::nat`

Source: `library/nat.click`, implicit.

### Natural numbers

`Nat` is an ordinary recursive logical datatype: `Zero` and `Succ(Nat)`.
Its values are mathematical naturals, with no machine-width bound or wrapping.
Unknown naturals remain symbolic; they are not eagerly built as successor chains.
Addition is a pure recursive definition with checked induction proofs, not a new
kernel arithmetic primitive. Checked `to_integer` and `to_nat` conversions are
available; this slice does not add numeral sugar or implicit conversions to C
integers.

### `Nat`

```click
spec enum Nat {
    Zero,
    Succ(Nat),
}
```

**Verified use:** [`mdtests/stdlib_nat.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_nat.md).

`to_integer(n)` observes a `Nat` as an exact Integer. `to_nat(z)` requires
`z >= 0` and remains symbolic even for large values. These conversions have
checked builtin meanings, and the laws below relate the two domains without
coercions.

### `nat::to_integer_zero`

```click
theorem to_integer_zero() {
    ensures to_integer(Nat::Zero) == 0;
}
```

### `nat::to_integer_succ`

```click
theorem to_integer_succ(n: Nat) {
    ensures to_integer(Nat::Succ(n)) == to_integer(n) + 1;
}
```

### `nat::to_integer_nonnegative`

```click
theorem to_integer_nonnegative(n: Nat) {
    ensures to_integer(n) >= 0;
}
```

### `nat::to_nat_to_integer`

```click
theorem to_nat_to_integer(n: Nat) {
    ensures to_nat(to_integer(n)) == n;
}
```

### `nat::to_integer_to_nat`

```click
theorem to_integer_to_nat(z: Integer) {
    requires z >= 0;
    ensures to_integer(to_nat(z)) == z;
}
```

### `nat::to_nat_zero`

```click
theorem to_nat_zero() {
    ensures to_nat(0) == Nat::Zero;
}
```

### `nat::add`

```click
function add(left: Nat, right: Nat) -> Nat
    decreases left
{
    match left {
        Nat::Zero => right,
        Nat::Succ(previous) => Nat::Succ(nat::add(previous, right)),
    }
}
```

**Verified use:** [`mdtests/stdlib_nat.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_nat.md).

### `nat::add_left_identity`

```click
theorem add_left_identity(n: Nat) {
    ensures nat::add(Nat::Zero, n) == n by {
        unfold(nat::add(Nat::Zero, n));
        normalize();
    }
}
```

**Verified use:** [`mdtests/stdlib_nat.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_nat.md).

### `nat::add_succ_left`

```click
theorem add_succ_left(n: Nat, m: Nat) {
    ensures nat::add(Nat::Succ(n), m) == Nat::Succ(nat::add(n, m)) by {
        unfold(nat::add(Nat::Succ(n), m));
        normalize();
    }
}
```

**Verified use:** [`mdtests/stdlib_nat.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_nat.md).

### `nat::to_integer_add`

The ordinary structural addition agrees with exact Integer addition. Its proof
uses Nat induction and explicit, locally checked linear certificates.

```click
theorem to_integer_add(n: Nat, m: Nat) {
    ensures to_integer(nat::add(n, m)) == to_integer(n) + to_integer(m) by {
        induct(n) as ih {
            Nat::Zero => {
                unfold(nat::add(Nat::Zero, m));
                apply(nat::to_integer_zero());
                arithmetic_certificate {
                    premise 0: to_integer(Nat::Zero) == 0 => to_integer(Nat::Zero) == 0;
                    scale 0 by -1 => to_integer(m) == to_integer(Nat::Zero) + to_integer(m);
                    conclusion 1;
                }
            }
            Nat::Succ(previous) => {
                unfold(nat::add(Nat::Succ(previous), m));
                apply(nat::to_integer_succ(nat::add(previous, m)));
                apply(ih(previous));
                apply(nat::to_integer_succ(previous));
                arithmetic_certificate {
                    premise 0: to_integer(Nat::Succ(nat::add(previous, m))) == to_integer(nat::add(previous, m)) + 1 => to_integer(Nat::Succ(nat::add(previous, m))) == to_integer(nat::add(previous, m)) + 1;
                    premise 1: to_integer(nat::add(previous, m)) == to_integer(previous) + to_integer(m) => to_integer(nat::add(previous, m)) == to_integer(previous) + to_integer(m);
                    premise 2: to_integer(Nat::Succ(previous)) == to_integer(previous) + 1 => to_integer(Nat::Succ(previous)) == to_integer(previous) + 1;
                    add 0, 1 => to_integer(Nat::Succ(nat::add(previous, m))) == to_integer(previous) + to_integer(m) + 1;
                    scale 2 by -1 => to_integer(previous) + 1 == to_integer(Nat::Succ(previous));
                    add 3, 4 => to_integer(Nat::Succ(nat::add(previous, m))) == to_integer(Nat::Succ(previous)) + to_integer(m);
                    conclusion 5;
                }
            }
        }
    }
}
```

### `nat::add_right_identity`

```click
theorem add_right_identity(n: Nat) {
    ensures nat::add(n, Nat::Zero) == n by {
        induct(n) as ih {
            Nat::Zero => {
                unfold(nat::add(Nat::Zero, Nat::Zero));
                normalize();
            }
            Nat::Succ(previous) => {
                apply(ih(previous));
                unfold(nat::add(Nat::Succ(previous), Nat::Zero));
                rewrite(nat::add(previous, Nat::Zero) == previous);
                normalize();
            }
        }
    }
}
```

**Verified use:** [`mdtests/stdlib_nat.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_nat.md).

### `nat::add_succ_right`

```click
theorem add_succ_right(n: Nat, m: Nat) {
    ensures nat::add(n, Nat::Succ(m)) == Nat::Succ(nat::add(n, m)) by {
        induct(n) as ih {
            Nat::Zero => {
                unfold(nat::add(Nat::Zero, Nat::Succ(m)));
                unfold(nat::add(Nat::Zero, m));
                normalize();
            }
            Nat::Succ(previous) => {
                apply(ih(previous));
                unfold(nat::add(Nat::Succ(previous), Nat::Succ(m)));
                unfold(nat::add(Nat::Succ(previous), m));
                rewrite(nat::add(previous, Nat::Succ(m)) == Nat::Succ(nat::add(previous, m)));
                normalize();
            }
        }
    }
}
```

**Verified use:** [`mdtests/stdlib_nat.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_nat.md).

### `nat::add_associative`

```click
theorem add_associative(a: Nat, b: Nat, c: Nat) {
    ensures nat::add(nat::add(a, b), c) == nat::add(a, nat::add(b, c)) by {
        induct(a) as ih {
            Nat::Zero => {
                unfold(nat::add(Nat::Zero, b));
                unfold(nat::add(Nat::Zero, nat::add(b, c)));
                normalize();
            }
            Nat::Succ(previous) => {
                apply(ih(previous));
                apply(nat::add_succ_left(previous, b));
                rewrite(nat::add(Nat::Succ(previous), b) == Nat::Succ(nat::add(previous, b)));
                apply(nat::add_succ_left(nat::add(previous, b), c));
                rewrite(nat::add(Nat::Succ(nat::add(previous, b)), c)
                    == Nat::Succ(nat::add(nat::add(previous, b), c)));
                apply(nat::add_succ_left(previous, nat::add(b, c)));
                rewrite(nat::add(Nat::Succ(previous), nat::add(b, c))
                    == Nat::Succ(nat::add(previous, nat::add(b, c))));
                rewrite(nat::add(nat::add(previous, b), c) == nat::add(previous, nat::add(b, c)));
                normalize();
            }
        }
    }
}
```

**Verified use:** [`mdtests/stdlib_nat.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_nat.md).

### `nat::add_commutative`

```click
theorem add_commutative(a: Nat, b: Nat) {
    ensures nat::add(a, b) == nat::add(b, a) by {
        induct(a) as ih {
            Nat::Zero => {
                unfold(nat::add(Nat::Zero, b));
                apply(nat::add_right_identity(b));
                rewrite(nat::add(b, Nat::Zero) == b);
                normalize();
            }
            Nat::Succ(previous) => {
                apply(ih(previous));
                unfold(nat::add(Nat::Succ(previous), b));
                apply(nat::add_succ_right(b, previous));
                rewrite(nat::add(b, Nat::Succ(previous)) == Nat::Succ(nat::add(b, previous)));
                rewrite(nat::add(previous, b) == nat::add(b, previous));
                normalize();
            }
        }
    }
}
```

**Verified use:** [`mdtests/stdlib_nat.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_nat.md).

## `click::list`

Source: `library/list.click`, implicit. `List` and its constructors keep bare names; functions and theorems are written `list::name`.

### Lists

`List<T>` is an immutable logical value, not a C layout or ownership resource.
It preserves order and multiplicity. Use explicit constructors and the functions
below; `[]`, `++`, and `in` still use the older sequence representation.

### `List`

```click
spec enum List<T> {
    Nil,
    Cons(T, List<T>),
}
```

**Verified use:** [`mdtests/stdlib_list.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_list.md).

### `list::append`

```click
function append<T>(xs: List<T>, ys: List<T>) -> List<T>
    decreases xs
{
    match xs {
        List::Nil => ys,
        List::Cons(head, tail) => List<T>::Cons(head, list::append(tail, ys)),
    }
}
```

**Verified use:** [`mdtests/stdlib_list.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_list.md).

### `list::contains`

```click
function contains<T>(xs: List<T>, value: T) -> Bool
    decreases xs
{
    match xs {
        List::Nil => false,
        List::Cons(head, tail) =>
            if head == value { true } else { list::contains(tail, value) },
    }
}
```

Returns `true` for membership and `false` otherwise, using element
equality. A call written alone is a claim: `ensures list::contains(xs, v);`
means `list::contains(xs, v) == true`.
Its checked laws support C scalar, pointer, and algebraic-valued elements,
including nested lists. Comparisons of unknown algebraic values stay symbolic.

**Verified use:** [`mdtests/stdlib_list.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_list.md).

### `list::append_left_identity`

```click
theorem append_left_identity<T>(xs: List<T>) {
    ensures list::append(List<T>::Nil, xs) == xs by {
        unfold(list::append(List<T>::Nil, xs));
        normalize();
    }
}
```

**Verified use:** [`mdtests/stdlib_list.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_list.md).

### `list::append_right_identity`

```click
theorem append_right_identity<T>(xs: List<T>) {
    ensures list::append(xs, List<T>::Nil) == xs by {
        induct(xs) as ih {
            List::Nil => {
                unfold(list::append(List<T>::Nil, List<T>::Nil));
                normalize();
            }
            List::Cons(head, tail) => {
                apply(ih(tail));
                unfold(list::append(List<T>::Cons(head, tail), List<T>::Nil));
                rewrite(list::append(tail, List<T>::Nil) == tail);
                normalize();
            }
        }
    }
}
```

**Verified use:** [`mdtests/stdlib_list.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_list.md).

### `list::append_cons`

```click
theorem append_cons<T>(head: T, tail: List<T>, ys: List<T>) {
    ensures list::append(List<T>::Cons(head, tail), ys)
        == List<T>::Cons(head, list::append(tail, ys)) by {
        unfold(list::append(List<T>::Cons(head, tail), ys));
        normalize();
    }
}
```

**Verified use:** [`mdtests/stdlib_list.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_list.md).

### `list::append_associative`

```click
theorem append_associative<T>(xs: List<T>, ys: List<T>, zs: List<T>) {
    ensures list::append(list::append(xs, ys), zs)
        == list::append(xs, list::append(ys, zs)) by {
        induct(xs) as ih {
            List::Nil => {
                unfold(list::append(List<T>::Nil, ys));
                unfold(list::append(List<T>::Nil, list::append(ys, zs)));
                solve();
            }
            List::Cons(head, tail) => {
                apply(ih(tail));
                apply(list::append_cons(head, tail, ys));
                rewrite(list::append(List<T>::Cons(head, tail), ys)
                    == List<T>::Cons(head, list::append(tail, ys)));
                apply(list::append_cons(head, list::append(tail, ys), zs));
                rewrite(list::append(List<T>::Cons(head, list::append(tail, ys)), zs)
                    == List<T>::Cons(head, list::append(list::append(tail, ys), zs)));
                apply(list::append_cons(head, tail, list::append(ys, zs)));
                rewrite(list::append(List<T>::Cons(head, tail), list::append(ys, zs))
                    == List<T>::Cons(head, list::append(tail, list::append(ys, zs))));
                rewrite(list::append(list::append(tail, ys), zs)
                    == list::append(tail, list::append(ys, zs)));
                solve();
            }
        }
    }
}
```

**Verified use:** [`mdtests/stdlib_list.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_list.md).

### `list::contains_nil`

```click
theorem contains_nil<T>(value: T) {
    ensures list::contains(List<T>::Nil, value) == false by {
        unfold(list::contains(List<T>::Nil, value));
        normalize();
    }
}
```

**Verified use:** [`mdtests/stdlib_list.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_list.md).

### `list::contains_cons`

```click
theorem contains_cons<T>(head: T, tail: List<T>, value: T) {
    ensures list::contains(List<T>::Cons(head, tail), value)
        == if head == value { true } else { list::contains(tail, value) } by {
        unfold(list::contains(List<T>::Cons(head, tail), value));
        normalize();
    }
}
```

**Verified use:** [`mdtests/stdlib_list.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_list.md).

### `list::contains_append`

```click
theorem contains_append<T>(xs: List<T>, ys: List<T>, value: T) {
    ensures list::contains(list::append(xs, ys), value)
        == if list::contains(xs, value) { true } else { list::contains(ys, value) } by {
        induct(xs) as ih {
            List::Nil => {
                unfold(list::append(List<T>::Nil, ys));
                unfold(list::contains(List<T>::Nil, value));
                solve();
            }
            List::Cons(head, tail) => {
                apply(ih(tail));
                apply(list::append_cons(head, tail, ys));
                rewrite(list::append(List<T>::Cons(head, tail), ys)
                    == List<T>::Cons(head, list::append(tail, ys)));
                if head == value {
                    apply(list::contains_cons(head, list::append(tail, ys), value));
                    rewrite(list::contains(List<T>::Cons(head, list::append(tail, ys)), value)
                        == if head == value { true } else { list::contains(list::append(tail, ys), value) });
                    apply(list::contains_cons(head, tail, value));
                    rewrite(list::contains(List<T>::Cons(head, tail), value)
                        == if head == value { true } else { list::contains(tail, value) });
                    normalize() using { head == value; };
                } else {
                    apply(list::contains_cons(head, list::append(tail, ys), value));
                    rewrite(list::contains(List<T>::Cons(head, list::append(tail, ys)), value)
                        == if head == value { true } else { list::contains(list::append(tail, ys), value) });
                    apply(list::contains_cons(head, tail, value));
                    rewrite(list::contains(List<T>::Cons(head, tail), value)
                        == if head == value { true } else { list::contains(tail, value) });
                    rewrite(list::contains(list::append(tail, ys), value)
                        == if list::contains(tail, value) { true } else { list::contains(ys, value) });
                    normalize() using { not(head == value); };
                }
            }
        }
    }
}
```

Membership through append, proved by structural induction with explicit
conditional reduction in each constructor case.

**Verified use:** [`mdtests/stdlib_list_compositionality.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_list_compositionality.md).

### Natural-valued lengths

`list::length` returns `Nat`, so a length cannot be negative or overflow.
These laws hold for arbitrary element types, including nested lists.

### `list::length`

```click
function length<T>(xs: List<T>) -> Nat
    decreases xs
{
    match xs {
        List::Nil => Nat::Zero,
        List::Cons(head, tail) => Nat::Succ(list::length(tail)),
    }
}
```

**Verified use:** [`mdtests/stdlib_list_length.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_list_length.md).

### `list::length_nil`

```click
theorem length_nil<T>(xs: List<T>) {
    requires xs == List<T>::Nil;
    ensures list::length(xs) == Nat::Zero by {
        rewrite(xs == List<T>::Nil);
        unfold(list::length(List<T>::Nil));
        normalize();
    }
}
```

**Verified use:** [`mdtests/stdlib_list_length.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_list_length.md).

### `list::length_cons`

```click
theorem length_cons<T>(head: T, tail: List<T>) {
    ensures list::length(List<T>::Cons(head, tail)) == Nat::Succ(list::length(tail)) by {
        unfold(list::length(List<T>::Cons(head, tail)));
        normalize();
    }
}
```

**Verified use:** [`mdtests/stdlib_list_length.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_list_length.md).

### `list::length_append`

```click
theorem length_append<T>(xs: List<T>, ys: List<T>) {
    ensures list::length(list::append(xs, ys)) == nat::add(list::length(xs), list::length(ys)) by {
        induct(xs) as ih {
            List::Nil => {
                unfold(list::append(List<T>::Nil, ys));
                unfold(list::length(List<T>::Nil));
                unfold(nat::add(Nat::Zero, list::length(ys)));
                solve();
            }
            List::Cons(head, tail) => {
                apply(ih(tail));
                apply(list::append_cons(head, tail, ys));
                rewrite(list::append(List<T>::Cons(head, tail), ys)
                    == List<T>::Cons(head, list::append(tail, ys)));
                apply(list::length_cons(head, list::append(tail, ys)));
                rewrite(list::length(List<T>::Cons(head, list::append(tail, ys)))
                    == Nat::Succ(list::length(list::append(tail, ys))));
                apply(list::length_cons(head, tail));
                rewrite(list::length(List<T>::Cons(head, tail)) == Nat::Succ(list::length(tail)));
                apply(nat::add_succ_left(list::length(tail), list::length(ys)));
                rewrite(nat::add(Nat::Succ(list::length(tail)), list::length(ys))
                    == Nat::Succ(nat::add(list::length(tail), list::length(ys))));
                rewrite(list::length(list::append(tail, ys)) == nat::add(list::length(tail), list::length(ys)));
                normalize();
            }
        }
    }
}
```

**Verified use:** [`mdtests/stdlib_list_length.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_list_length.md).

## `click::option`

Source: `library/option.click`, implicit.

### `Option`

```click
spec enum Option<T> {
    None,
    Some(T),
}
```

**Meaning:** An optional value. A Rust `Option<u32>` parameter or result is
this value in a contract: `ensures result == Option<u32>::Some(x);`. The
importer lays the Rust value out itself; a contract never reads that layout.

### `option::unwrap_or`

```click
function unwrap_or<T>(o: Option<T>, default: T) -> T {
    match o {
        Option::Some(value) => value,
        Option::None => default,
    }
}
```

**Meaning:** Rust's `Option::unwrap_or`: the payload of `Some`, else
`default`. A call `o.unwrap_or(d)` in imported Rust calls an external function
whose contract is `ensures result == click::option::unwrap_or(o, d);`. The
module is implicit, so a sidecar writes `option::unwrap_or(o, d)` with no
import.

**Verified use:** [`design/charon-trial/option-values`](https://github.com/clicklang/click/blob/master/design/charon-trial/option-values/options.click).

## `click::result`

Source: `library/result.click`, implicit.

### `Result`

```click
spec enum Result<T, E> {
    Ok(T),
    Err(E),
}
```

**Meaning:** A value or an error. A Rust `Result<u32, u8>` parameter or result
is this value in a contract: `ensures result == Result<u32, u8>::Ok(x);`. As
for `Option`, the importer lays the Rust value out itself.

### `result::unwrap_or`

```click
function unwrap_or<T, E>(r: Result<T, E>, default: T) -> T {
    match r {
        Result::Ok(value) => value,
        Result::Err(error) => default,
    }
}
```

**Meaning:** Rust's `Result::unwrap_or`: the payload of `Ok`, else `default`.
A call `r.unwrap_or(d)` in imported Rust calls an external function whose
contract is `ensures result == click::result::unwrap_or(r, d);`. The module is
implicit; a sidecar writes `click::result::unwrap_or(r, d)` with no import.

**Verified use:** [`design/charon-trial/result-values`](https://github.com/clicklang/click/blob/master/design/charon-trial/result-values/results.click).

## `click::integer`

Source: `library/integer.click`, `import click::integer;`. Width-specific order, definedness and `to_integer` lemmas, unsigned wrapping operations, round trips through the `to_*` conversions, and `Integer` truncating-division laws. [Trust](../../concepts/trust.md#the-click-library) says which theorems are kernel standard theorems.

### Order, definedness and conversion lemmas

### `integer::int32_increment_upper_bound`

```click
theorem int32_increment_upper_bound(value: int32, upper: int32) {
    requires value < upper;

    ensures to_integer(value + 1) <= to_integer(upper) by {
        arithmetic_certificate signed_int32 {
            premise 0: (value as int32) < (upper as int32) => (value as int32) < (upper as int32);
            int32_range => to_integer(upper as int32) <= to_integer(2147483647 as int32);
            add 0, 1 => (to_integer(value as int32) + to_integer(upper as int32)) < (to_integer(upper as int32) + to_integer(2147483647 as int32));
            interval_from_affine 2 (value) (-2147483648) (2147483646);
            interval_atom (1) (1) (1);
            interval_add_bounded 3, 4 (-2147483647) (2147483647);
            affine_conclusion 0 5 => ((value + 1) as int32) <= (upper as int32);
            conclusion 6;
        }
    }
}
```

**Meaning:** Given its listed requirements, proves `to_integer(value + 1) <= to_integer(upper)`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `integer::int32_increment_strictly_increases`

```click
theorem int32_increment_strictly_increases(value: int32, upper: int32) {
    requires value < upper;

    ensures to_integer(value) < to_integer(value + 1) by {
        arithmetic_certificate signed_int32 {
            premise 0: (value as int32) < (upper as int32) => (value as int32) < (upper as int32);
            int32_range => to_integer(upper as int32) <= to_integer(2147483647 as int32);
            add 0, 1 => (to_integer(value as int32) + to_integer(upper as int32)) < (to_integer(upper as int32) + to_integer(2147483647 as int32));
            interval_from_affine 2 (value) (-2147483648) (2147483646);
            interval_atom (1) (1) (1);
            interval_add_bounded 3, 4 (-2147483647) (2147483647);
            trivial => 0 <= 0;
            affine_conclusion 6 5 => (value as int32) < ((value + 1) as int32);
            conclusion 7;
        }
    }
}
```

**Meaning:** Given its listed requirements, proves `to_integer(value) < to_integer(value + 1)`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `integer::int32_increment_lower_bound`

```click
theorem int32_increment_lower_bound(value: int32, lower: int32, upper: int32) {
    requires lower <= value;
    requires value < upper;

    ensures to_integer(lower) <= to_integer(value + 1) by {
        arithmetic_certificate signed_int32 {
            premise 0: (lower as int32) <= (value as int32) => (lower as int32) <= (value as int32);
            premise 1: (value as int32) < (upper as int32) => (value as int32) < (upper as int32);
            int32_range => to_integer(-2147483648 as int32) <= to_integer(lower as int32);
            add 0, 2 => (to_integer(lower as int32) + to_integer(-2147483648 as int32)) <= (to_integer(value as int32) + to_integer(lower as int32));
            int32_range => to_integer(upper as int32) <= to_integer(2147483647 as int32);
            add 1, 4 => (to_integer(value as int32) + to_integer(upper as int32)) < (to_integer(upper as int32) + to_integer(2147483647 as int32));
            interval_from_affine 3 (value) (-2147483648) (2147483647);
            interval_from_affine 5 (value) (-2147483648) (2147483646);
            interval_intersect 6, 7 (-2147483648) (2147483646);
            interval_atom (1) (1) (1);
            interval_add_bounded 8, 9 (-2147483647) (2147483647);
            trivial => -1 <= 0;
            add 0, 11 => (to_integer(lower as int32) + -1) <= (to_integer(value as int32) + 0);
            affine_conclusion 12 10 => (lower as int32) <= ((value + 1) as int32);
            conclusion 13;
        }
    }
}
```

**Meaning:** Given its listed requirements, proves `to_integer(lower) <= to_integer(value + 1)`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `integer::int32_positive_is_nonnegative`

```click
theorem int32_positive_is_nonnegative(value: int32) {
    requires 0 < value;

    ensures 0 <= value by {
        arithmetic_certificate {
            premise 0: 0 < value => 0 < value;
            trivial => -1 <= 0;
            add 0, 1 => 0 + -1 < (to_integer(value as int32) + 0);
            conclusion 2;
        }
    }
}
```

**Meaning:** Given its listed requirements, proves `0 <= value`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `integer::int32_increment_below_max_is_defined`

```click
theorem int32_increment_below_max_is_defined(value: int32) {
    requires value < 2147483647;

    ensures defined(value + 1) by {
        arithmetic_certificate rules {
            premise 0: value < 2147483647 => value < 2147483647;
            int32_defined bounds [0] => defined(value + 1);
            conclusion 0;
        }
    }
}
```

**Meaning:** Given its listed requirements, proves `defined(value + 1)`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `integer::int32_nonnegative_add_within_max_is_defined`

```click
theorem int32_nonnegative_add_within_max_is_defined(value: int32, amount: int32) {
    requires 0 <= amount;
    requires to_integer(value) <= to_integer(2147483647 - amount);

    ensures defined(value + amount) by {
        have -2147483648 <= 2147483647 - to_integer(amount) by {
            arithmetic_certificate {
                negated_goal => 2147483647 - to_integer(amount) < -2147483648;
                type_range => to_integer(amount) <= 2147483647;
                add 0, 1 => 2147483647 - to_integer(amount) + to_integer(amount) < -2147483648 + 2147483647;
                conclusion 2;
            }
        }
        have 2147483647 - to_integer(amount) <= 2147483647 by {
            arithmetic_certificate {
                negated_goal => 2147483647 < 2147483647 - to_integer(amount);
                premise 0: 0 <= to_integer(amount) => 0 <= to_integer(amount);
                add 0, 1 => 2147483647 + 0 < 2147483647 - to_integer(amount) + to_integer(amount);
                conclusion 2;
            }
        }
        have to_integer(2147483647 - amount) == 2147483647 - to_integer(amount) by {
            arithmetic_certificate rules {
                premise 0: -2147483648 <= 2147483647 - to_integer(amount) => -2147483648 <= 2147483647 - to_integer(amount);
                premise 1: 2147483647 - to_integer(amount) <= 2147483647 => 2147483647 - to_integer(amount) <= 2147483647;
                integer_operation_identity bounds [0, 1] => to_integer(2147483647 - amount) == 2147483647 - to_integer(amount);
                conclusion 0;
            }
        }
        have -2147483648 <= to_integer(value) + to_integer(amount) by {
            arithmetic_certificate {
                negated_goal => to_integer(value) + to_integer(amount) < -2147483648;
                premise 0: 0 <= to_integer(amount) => 0 <= to_integer(amount);
                type_range => -2147483648 <= to_integer(value);
                add 0, 1 => to_integer(value) + to_integer(amount) + 0 < -2147483648 + to_integer(amount);
                add 3, 2 => to_integer(value) + to_integer(amount) + 0 + -2147483648 < -2147483648 + to_integer(amount) + to_integer(value);
                conclusion 4;
            }
        }
        have to_integer(value) + to_integer(amount) <= 2147483647 by {
            arithmetic_certificate {
                negated_goal => 2147483647 < to_integer(value) + to_integer(amount);
                premise 0: to_integer(2147483647 - amount) == 2147483647 - to_integer(amount) => to_integer(2147483647 - amount) == 2147483647 - to_integer(amount);
                less_equal_from_equal 1 => to_integer(2147483647 - amount) <= 2147483647 - to_integer(amount);
                premise 1: to_integer(value) <= to_integer(2147483647 - amount) => to_integer(value) <= to_integer(2147483647 - amount);
                add 0, 2 => 2147483647 + to_integer(2147483647 - amount) < to_integer(value) + to_integer(amount) + (2147483647 - to_integer(amount));
                add 4, 3 => 2147483647 + to_integer(2147483647 - amount) + to_integer(value) < to_integer(value) + to_integer(amount) + (2147483647 - to_integer(amount)) + to_integer(2147483647 - amount);
                conclusion 5;
            }
        }
        assumption();
    }
}
```

**Meaning:** Given its listed requirements, proves `defined(value + amount)`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `integer::int32_nonnegative_subtract_within_value_is_defined`

```click
theorem int32_nonnegative_subtract_within_value_is_defined(value: int32, amount: int32) {
    requires 0 <= amount;
    requires amount <= value;

    ensures defined(value - amount) by {
        have to_integer(value) <= 2147483647 by {
            arithmetic_certificate {
                type_range => to_integer(value) <= 2147483647;
                conclusion 0;
            }
        }
        have -2147483648 <= to_integer(value) - to_integer(amount) by {
            arithmetic_certificate {
                premise 0: amount <= value => amount <= value;
                trivial => -2147483648 <= 0;
                add 0, 1 => (to_integer(amount as int32) + -2147483648) <= (to_integer(value as int32) + 0);
                conclusion 2;
            }
        }
        have to_integer(value) - to_integer(amount) <= 2147483647 by {
            arithmetic_certificate {
                premise 0: 0 <= amount => 0 <= amount;
                premise 1: to_integer(value) <= 2147483647 => to_integer(value) <= 2147483647;
                add 0, 1 => 0 + to_integer(value) <= (to_integer(amount as int32) + 2147483647);
                conclusion 2;
            }
        }
        assumption();
    }
}
```

**Meaning:** Given its listed requirements, proves `defined(value - amount)`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `integer::int32_add_defined_by_integer_bounds`

```click
theorem int32_add_defined_by_integer_bounds(left: int32, right: int32) {
    requires to_integer(left) + to_integer(right) >= -2147483648;
    requires to_integer(left) + to_integer(right) <= 2147483647;
    ensures defined(left + right) by {
        assumption();
    }
}
```

Bounds on the mathematical sum establish that signed C addition does not overflow.
Both bounds are required, including when the final program result is in range.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `integer::uint32_add_to_integer`

```click
theorem uint32_add_to_integer(left: uint32, right: uint32) {
    requires to_integer(left) + to_integer(right) <= 4294967295;
    ensures to_integer(left + right) == to_integer(left) + to_integer(right) by {
        have 0 <= to_integer(left) + to_integer(right) by {
            arithmetic_certificate {
                negated_goal => to_integer(left) + to_integer(right) < 0;
                type_range => 0 <= to_integer(left);
                type_range => 0 <= to_integer(right);
                add 0, 1 => to_integer(left) + to_integer(right) + 0 < 0 + to_integer(left);
                add 3, 2 => to_integer(left) + to_integer(right) + 0 + 0 < 0 + to_integer(left) + to_integer(right);
                conclusion 4;
            }
        }
        have to_integer(left) + to_integer(right) <= 4294967295 by {
            assumption();
        }
        have to_integer(left + right) == to_integer(left) + to_integer(right) by {
            arithmetic_certificate rules {
                premise 0: 0 <= to_integer(left) + to_integer(right) => 0 <= to_integer(left) + to_integer(right);
                premise 1: to_integer(left) + to_integer(right) <= 4294967295 => to_integer(left) + to_integer(right) <= 4294967295;
                integer_operation_identity bounds [0, 1] => to_integer(left + right) == to_integer(left) + to_integer(right);
                conclusion 0;
            }
        }
        assumption();
    }
}
```

Unsigned machine addition agrees with mathematical addition when the mathematical sum fits `uint32`. Unsigned definedness alone allows wrapping and cannot establish this equality.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `integer::uint32_subtract_to_integer`

```click
theorem uint32_subtract_to_integer(left: uint32, right: uint32) {
    requires right <= left;
    ensures to_integer(left - right) == to_integer(left) - to_integer(right) by {
        have 0 <= to_integer(left) - to_integer(right) by {
            arithmetic_certificate {
                negated_goal => to_integer(left) - to_integer(right) < 0;
                premise 0: to_integer(right) <= to_integer(left) => to_integer(right) <= to_integer(left);
                add 0, 1 => to_integer(left) - to_integer(right) + to_integer(right) < 0 + to_integer(left);
                conclusion 2;
            }
        }
        have to_integer(left) - to_integer(right) <= 4294967295 by {
            arithmetic_certificate {
                negated_goal => 4294967295 < to_integer(left) - to_integer(right);
                type_range => to_integer(left) <= 4294967295;
                type_range => 0 <= to_integer(right);
                add 0, 1 => 4294967295 + to_integer(left) < to_integer(left) - to_integer(right) + 4294967295;
                add 3, 2 => 4294967295 + to_integer(left) + 0 < to_integer(left) - to_integer(right) + 4294967295 + to_integer(right);
                conclusion 4;
            }
        }
        have to_integer(left - right) == to_integer(left) - to_integer(right) by {
            arithmetic_certificate rules {
                premise 0: 0 <= to_integer(left) - to_integer(right) => 0 <= to_integer(left) - to_integer(right);
                premise 1: to_integer(left) - to_integer(right) <= 4294967295 => to_integer(left) - to_integer(right) <= 4294967295;
                integer_operation_identity bounds [0, 1] => to_integer(left - right) == to_integer(left) - to_integer(right);
                conclusion 0;
            }
        }
        assumption();
    }
}
```

Unsigned subtraction agrees with Integer subtraction under the native unsigned no-underflow guard. The rule covers the full `uint32` range. Native definedness alone permits wrapping, so it cannot replace the guard.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `integer::uint32_divide_to_integer`

```click
theorem uint32_divide_to_integer(left: uint32, right: uint32) {
    requires right != 0u32;
    requires to_integer(right) != 0;
    ensures to_integer(left / right) == truncating_quotient(to_integer(left), to_integer(right));
}
```

Unsigned division agrees with Integer truncating division when both evaluation domains exclude zero. No overflow bound on the dividend is required.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `integer::uint32_remainder_to_integer`

```click
theorem uint32_remainder_to_integer(left: uint32, right: uint32) {
    requires right != 0u32;
    requires to_integer(right) != 0;
    ensures to_integer(left % right) == truncating_remainder(to_integer(left), to_integer(right));
}
```

Unsigned remainder agrees with Integer truncating remainder when both evaluation domains exclude zero. A machine comparison is read through its `to_integer` observations, so the native guard `right != 0u32` alone meets both premises.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `integer::uint32_multiply_to_integer`

```click
theorem uint32_multiply_to_integer(left: uint32, right: uint32) {
    requires right == 0u32 or left <= 4294967295u32 / right;
    ensures to_integer(left * right) == to_integer(left) * to_integer(right) by {
        have 0 <= to_integer(left) by {
            normalize();
        }
        have to_integer(left) <= 4294967295 by {
            normalize();
        }
        have 0 <= to_integer(right) by {
            normalize();
        }
        have to_integer(right) <= 4294967295 by {
            normalize();
        }
        have 0 <= to_integer(left) * to_integer(right) by {
            arithmetic_certificate rules {
                premise 0: 0 <= to_integer(left) => 0 <= to_integer(left);
                premise 1: to_integer(left) <= 4294967295 => to_integer(left) <= 4294967295;
                premise 2: 0 <= to_integer(right) => 0 <= to_integer(right);
                premise 3: to_integer(right) <= 4294967295 => to_integer(right) <= 4294967295;
                integer_product_bounds bounds [0, 1, 2, 3] => 0 <= to_integer(left) * to_integer(right);
                conclusion 0;
            }
        }
        if right == 0u32 {
            have to_integer(right) <= 0 by {
                normalize() using { right == 0u32; };
            }
            have to_integer(left) * to_integer(right) <= 0 by {
                arithmetic_certificate rules {
                    premise 0: 0 <= to_integer(left) => 0 <= to_integer(left);
                    premise 1: to_integer(left) <= 4294967295 => to_integer(left) <= 4294967295;
                    premise 2: 0 <= to_integer(right) => 0 <= to_integer(right);
                    premise 3: to_integer(right) <= 0 => to_integer(right) <= 0;
                    integer_product_bounds bounds [0, 1, 2, 3] => to_integer(left) * to_integer(right) <= 0;
                    conclusion 0;
                }
            }
            have to_integer(left) * to_integer(right) <= 4294967295 by {
                arithmetic_certificate {
                    premise 0: to_integer(left) * to_integer(right) <= 0 => to_integer(left) * to_integer(right) <= 0;
                    trivial => -4294967295 <= 0;
                    add 0, 1 => to_integer(left) * to_integer(right) + -4294967295 <= 0 + 0;
                    conclusion 2;
                }
            }
            arithmetic_certificate rules {
                premise 0: 0 <= to_integer(left) * to_integer(right) => 0 <= to_integer(left) * to_integer(right);
                premise 1: to_integer(left) * to_integer(right) <= 4294967295 => to_integer(left) * to_integer(right) <= 4294967295;
                integer_operation_identity bounds [0, 1] => to_integer(left * right) == to_integer(left) * to_integer(right);
                conclusion 0;
            }
        } else {
            have left <= 4294967295u32 / right by {
                cases {
                    right == 0u32 => {
                        contradiction(right == 0u32);
                    }
                    left <= 4294967295u32 / right => {
                        assumption();
                    }
                }
            }
            have right != 0u32 by {
                normalize() using { not right == 0u32; };
            }
            have 1 <= to_integer(right) by {
                arithmetic_certificate {
                    excluded_bound 0: to_integer(right) != 0 => 1 <= to_integer(right);
                    conclusion 0;
                }
            }
            apply(integer::uint32_divide_to_integer(4294967295u32, right)) using {
                right != 0u32;
                to_integer(right) != 0;
            };
            apply(integer::truncation_identity(4294967295, to_integer(right))) using {
                to_integer(right) != 0;
            };
            apply(integer::nonnegative_dividend_remainder(4294967295, to_integer(right))) using {
                to_integer(right) != 0;
            };
            have 0 <= truncating_quotient(4294967295, to_integer(right)) - to_integer(left) by {
                arithmetic_certificate {
                    negated_goal => truncating_quotient(4294967295, to_integer(right)) - to_integer(left) < 0;
                    premise 0: to_integer(left) <= to_integer(4294967295u32 / right) => to_integer(left) <= to_integer(4294967295u32 / right);
                    premise 1: to_integer(4294967295u32 / right) == truncating_quotient(4294967295, to_integer(right)) => to_integer(4294967295u32 / right) == truncating_quotient(4294967295, to_integer(right));
                    less_equal_from_equal 2 => to_integer(4294967295u32 / right) <= truncating_quotient(4294967295, to_integer(right));
                    add 0, 1 => truncating_quotient(4294967295, to_integer(right)) - to_integer(left) + to_integer(left) < 0 + to_integer(4294967295u32 / right);
                    add 4, 3 => truncating_quotient(4294967295, to_integer(right)) - to_integer(left) + to_integer(left) + to_integer(4294967295u32 / right) < 0 + to_integer(4294967295u32 / right) + truncating_quotient(4294967295, to_integer(right));
                    conclusion 5;
                }
            }
            have truncating_quotient(4294967295, to_integer(right)) - to_integer(left) <= 4294967295 by {
                arithmetic_certificate {
                    negated_goal => 4294967295 < truncating_quotient(4294967295, to_integer(right)) - to_integer(left);
                    premise 0: to_integer(4294967295u32 / right) == truncating_quotient(4294967295, to_integer(right)) => to_integer(4294967295u32 / right) == truncating_quotient(4294967295, to_integer(right));
                    less_equal_from_equal 1 reverse => truncating_quotient(4294967295, to_integer(right)) <= to_integer(4294967295u32 / right);
                    type_range => to_integer(4294967295u32 / right) <= 4294967295;
                    type_range => 0 <= to_integer(left);
                    add 0, 2 => 4294967295 + truncating_quotient(4294967295, to_integer(right)) < truncating_quotient(4294967295, to_integer(right)) - to_integer(left) + to_integer(4294967295u32 / right);
                    add 5, 3 => 4294967295 + truncating_quotient(4294967295, to_integer(right)) + to_integer(4294967295u32 / right) < truncating_quotient(4294967295, to_integer(right)) - to_integer(left) + to_integer(4294967295u32 / right) + 4294967295;
                    add 6, 4 => 4294967295 + truncating_quotient(4294967295, to_integer(right)) + to_integer(4294967295u32 / right) + 0 < truncating_quotient(4294967295, to_integer(right)) - to_integer(left) + to_integer(4294967295u32 / right) + 4294967295 + to_integer(left);
                    conclusion 7;
                }
            }
            have 0 <= (truncating_quotient(4294967295, to_integer(right)) - to_integer(left)) * to_integer(right) by {
                arithmetic_certificate rules {
                    premise 0: 0 <= truncating_quotient(4294967295, to_integer(right)) - to_integer(left) => 0 <= truncating_quotient(4294967295, to_integer(right)) - to_integer(left);
                    premise 1: truncating_quotient(4294967295, to_integer(right)) - to_integer(left) <= 4294967295 => truncating_quotient(4294967295, to_integer(right)) - to_integer(left) <= 4294967295;
                    premise 2: 0 <= to_integer(right) => 0 <= to_integer(right);
                    premise 3: to_integer(right) <= 4294967295 => to_integer(right) <= 4294967295;
                    integer_product_bounds bounds [0, 1, 2, 3] => 0 <= (truncating_quotient(4294967295, to_integer(right)) - to_integer(left)) * to_integer(right);
                    conclusion 0;
                }
            }
            have (truncating_quotient(4294967295, to_integer(right)) - to_integer(left)) * to_integer(right) == truncating_quotient(4294967295, to_integer(right)) * to_integer(right) - to_integer(left) * to_integer(right) by {
                arithmetic_certificate rules {
                    integer_polynomial_identity bounds [] => (truncating_quotient(4294967295, to_integer(right)) - to_integer(left)) * to_integer(right) == truncating_quotient(4294967295, to_integer(right)) * to_integer(right) - to_integer(left) * to_integer(right);
                    conclusion 0;
                }
            }
            have to_integer(left) * to_integer(right) <= 4294967295 by {
                arithmetic_certificate {
                    negated_goal => 4294967295 < to_integer(left) * to_integer(right);
                    premise 0: 0 <= truncating_remainder(4294967295, to_integer(right)) => 0 <= truncating_remainder(4294967295, to_integer(right));
                    premise 1: 0 <= (truncating_quotient(4294967295, to_integer(right)) - to_integer(left)) * to_integer(right) => 0 <= (truncating_quotient(4294967295, to_integer(right)) - to_integer(left)) * to_integer(right);
                    premise 2: 4294967295 == truncating_quotient(4294967295, to_integer(right)) * to_integer(right) + truncating_remainder(4294967295, to_integer(right)) => 4294967295 == truncating_quotient(4294967295, to_integer(right)) * to_integer(right) + truncating_remainder(4294967295, to_integer(right));
                    less_equal_from_equal 3 reverse => truncating_quotient(4294967295, to_integer(right)) * to_integer(right) + truncating_remainder(4294967295, to_integer(right)) <= 4294967295;
                    premise 3: (truncating_quotient(4294967295, to_integer(right)) - to_integer(left)) * to_integer(right) == truncating_quotient(4294967295, to_integer(right)) * to_integer(right) - to_integer(left) * to_integer(right) => (truncating_quotient(4294967295, to_integer(right)) - to_integer(left)) * to_integer(right) == truncating_quotient(4294967295, to_integer(right)) * to_integer(right) - to_integer(left) * to_integer(right);
                    less_equal_from_equal 5 => (truncating_quotient(4294967295, to_integer(right)) - to_integer(left)) * to_integer(right) <= truncating_quotient(4294967295, to_integer(right)) * to_integer(right) - to_integer(left) * to_integer(right);
                    add 0, 1 => 4294967295 + 0 < to_integer(left) * to_integer(right) + truncating_remainder(4294967295, to_integer(right));
                    add 7, 2 => 4294967295 + 0 + 0 < to_integer(left) * to_integer(right) + truncating_remainder(4294967295, to_integer(right)) + (truncating_quotient(4294967295, to_integer(right)) - to_integer(left)) * to_integer(right);
                    add 8, 4 => 4294967295 + 0 + 0 + truncating_quotient(4294967295, to_integer(right)) * to_integer(right) + truncating_remainder(4294967295, to_integer(right)) < to_integer(left) * to_integer(right) + truncating_remainder(4294967295, to_integer(right)) + (truncating_quotient(4294967295, to_integer(right)) - to_integer(left)) * to_integer(right) + 4294967295;
                    add 9, 6 => 4294967295 + 0 + 0 + truncating_quotient(4294967295, to_integer(right)) * to_integer(right) + truncating_remainder(4294967295, to_integer(right)) + (truncating_quotient(4294967295, to_integer(right)) - to_integer(left)) * to_integer(right) < to_integer(left) * to_integer(right) + truncating_remainder(4294967295, to_integer(right)) + (truncating_quotient(4294967295, to_integer(right)) - to_integer(left)) * to_integer(right) + 4294967295 + truncating_quotient(4294967295, to_integer(right)) * to_integer(right) - to_integer(left) * to_integer(right);
                    conclusion 10;
                }
            }
            arithmetic_certificate rules {
                premise 0: 0 <= to_integer(left) * to_integer(right) => 0 <= to_integer(left) * to_integer(right);
                premise 1: to_integer(left) * to_integer(right) <= 4294967295 => to_integer(left) * to_integer(right) <= 4294967295;
                integer_operation_identity bounds [0, 1] => to_integer(left * right) == to_integer(left) * to_integer(right);
                conclusion 0;
            }
        }
    }
}
```

Unsigned multiplication agrees with Integer multiplication under the native no-overflow guard. A zero right operand satisfies the guard without division; other operands must fit the unsigned quotient ceiling. Native unsigned definedness alone permits wrapping.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `integer::uint32_multiply_guard_by_integer_bound`

```click
theorem uint32_multiply_guard_by_integer_bound(left: uint32, right: uint32) {
    requires to_integer(left) * to_integer(right) <= 4294967295;
    ensures right == 0u32 or left <= 4294967295u32 / right by {
        if right == 0u32 {
            assumption();
        } else {
            have right != 0u32 by {
                normalize() using { not right == 0u32; };
            }
            have 1 <= to_integer(right) by {
                arithmetic_certificate {
                    excluded_bound 0: to_integer(right) != 0 => 1 <= to_integer(right);
                    conclusion 0;
                }
            }
            apply(integer::positive_divisor_quotient_lower(4294967295, to_integer(right), to_integer(left))) using {
                to_integer(right) != 0;
                1 <= to_integer(right);
                to_integer(left) * to_integer(right) <= 4294967295;
            };
            apply(integer::uint32_divide_to_integer(4294967295u32, right)) using {
                right != 0u32;
                to_integer(right) != 0;
            };
            have to_integer(left) <= to_integer(4294967295u32 / right) by {
                assumption();
            }
            have left <= 4294967295u32 / right by {
                normalize() using { to_integer(left) <= to_integer(4294967295u32 / right); };
            }
            assumption();
        }
    }
}
```

A mathematical product bound establishes the native checked-multiplication guard used by Rust. The zero right operand needs no division. Combine this rule with `integer::uint32_multiply_to_integer` to prove an exact product from Integer bounds; bounding the already wrapped machine product is insufficient.

**Verified use:** [`mdtests/integer_uint32_product_bound_guard.md`](https://github.com/clicklang/click/blob/master/mdtests/integer_uint32_product_bound_guard.md).

### `integer::uint64_add_to_integer`

```click
theorem uint64_add_to_integer(left: uint64, right: uint64) {
    requires to_integer(left) + to_integer(right) <= 18446744073709551615;
    ensures to_integer(left + right) == to_integer(left) + to_integer(right) by {
        have 0 <= to_integer(left) + to_integer(right) by {
            arithmetic_certificate {
                negated_goal => to_integer(left) + to_integer(right) < 0;
                type_range => 0 <= to_integer(left);
                type_range => 0 <= to_integer(right);
                add 0, 1 => to_integer(left) + to_integer(right) + 0 < 0 + to_integer(left);
                add 3, 2 => to_integer(left) + to_integer(right) + 0 + 0 < 0 + to_integer(left) + to_integer(right);
                conclusion 4;
            }
        }
        have to_integer(left) + to_integer(right) <= 18446744073709551615 by {
            assumption();
        }
        have to_integer(left + right) == to_integer(left) + to_integer(right) by {
            arithmetic_certificate rules {
                premise 0: 0 <= to_integer(left) + to_integer(right) => 0 <= to_integer(left) + to_integer(right);
                premise 1: to_integer(left) + to_integer(right) <= 18446744073709551615 => to_integer(left) + to_integer(right) <= 18446744073709551615;
                integer_operation_identity bounds [0, 1] => to_integer(left + right) == to_integer(left) + to_integer(right);
                conclusion 0;
            }
        }
        assumption();
    }
}
```

Unsigned addition agrees with Integer addition when the sum fits uint64. Native unsigned definedness alone permits wrapping.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `integer::uint64_multiply_to_integer`

```click
theorem uint64_multiply_to_integer(left: uint64, right: uint64) {
    requires to_integer(left) * to_integer(right) <= 18446744073709551615;
    ensures to_integer(left * right) == to_integer(left) * to_integer(right) by {
        have 0 <= to_integer(left) by {
            arithmetic_certificate {
                type_range => 0 <= to_integer(left);
                conclusion 0;
            }
        }
        have to_integer(left) <= 18446744073709551615 by {
            arithmetic_certificate {
                type_range => to_integer(left) <= 18446744073709551615;
                conclusion 0;
            }
        }
        have 0 <= to_integer(right) by {
            arithmetic_certificate {
                type_range => 0 <= to_integer(right);
                conclusion 0;
            }
        }
        have to_integer(right) <= 18446744073709551615 by {
            arithmetic_certificate {
                type_range => to_integer(right) <= 18446744073709551615;
                conclusion 0;
            }
        }
        have 0 <= to_integer(left) * to_integer(right) by {
            arithmetic_certificate rules {
                premise 0: 0 <= to_integer(left) => 0 <= to_integer(left);
                premise 1: to_integer(left) <= 18446744073709551615 => to_integer(left) <= 18446744073709551615;
                premise 2: 0 <= to_integer(right) => 0 <= to_integer(right);
                premise 3: to_integer(right) <= 18446744073709551615 => to_integer(right) <= 18446744073709551615;
                integer_product_bounds bounds [0, 1, 2, 3] => 0 <= to_integer(left) * to_integer(right);
                conclusion 0;
            }
        }
        arithmetic_certificate rules {
            premise 0: 0 <= to_integer(left) * to_integer(right) => 0 <= to_integer(left) * to_integer(right);
            premise 1: to_integer(left) * to_integer(right) <= 18446744073709551615 => to_integer(left) * to_integer(right) <= 18446744073709551615;
            integer_operation_identity bounds [0, 1] => to_integer(left * right) == to_integer(left) * to_integer(right);
            conclusion 0;
        }
    }
}
```

Unsigned multiplication agrees with the Integer product when it fits uint64. The explicit product bound excludes wrap.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `integer::uint64_product_bound_from_division`

```click
theorem uint64_product_bound_from_division(x: uint64, y: uint64) {
    requires y != 0u64;
    requires x <= 18446744073709551615u64 / y;
    ensures to_integer(x) * to_integer(y) <= to_integer(18446744073709551615u64) by {
        have to_integer(y) != 0;
        have 0 <= to_integer(y);
        have 0 <= to_integer(18446744073709551615u64) by normalize();
        apply(integer::uint64_divide_to_integer(18446744073709551615u64, y)) using {
            y != 0u64;
            to_integer(y) != 0;
        };
        have to_integer(x) <= to_integer(18446744073709551615u64 / y);
        apply(integer::multiply_order_nonnegative(to_integer(x), to_integer(18446744073709551615u64 / y), to_integer(y))) using {
            to_integer(x) <= to_integer(18446744073709551615u64 / y);
            0 <= to_integer(y);
            y != 0u64;
        };
        apply(integer::truncation_identity(to_integer(18446744073709551615u64), to_integer(y))) using { to_integer(y) != 0; };
        apply(integer::nonnegative_dividend_remainder(to_integer(18446744073709551615u64), to_integer(y))) using {
            to_integer(y) != 0;
            0 <= to_integer(18446744073709551615u64);
        };
        have to_integer(18446744073709551615u64 / y) * to_integer(y) == truncating_quotient(to_integer(18446744073709551615u64), to_integer(y)) * to_integer(y) by {
            rewrite(to_integer(18446744073709551615u64 / y) == truncating_quotient(to_integer(18446744073709551615u64), to_integer(y)));
            normalize();
        }
        solve() using {
            to_integer(x) * to_integer(y) <= to_integer(18446744073709551615u64 / y) * to_integer(y);
            to_integer(18446744073709551615u64 / y) * to_integer(y) == truncating_quotient(to_integer(18446744073709551615u64), to_integer(y)) * to_integer(y);
            to_integer(18446744073709551615u64) == truncating_quotient(to_integer(18446744073709551615u64), to_integer(y)) * to_integer(y) + truncating_remainder(to_integer(18446744073709551615u64), to_integer(y));
            0 <= truncating_remainder(to_integer(18446744073709551615u64), to_integer(y));
        };
    }
}
```

A nonzero native divisor and `x <= 18446744073709551615u64 / y` bound the
exact Integer product. Use this before `integer::uint64_multiply_to_integer` when the
program exposes a division-based overflow guard.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `integer::uint64_subtract_to_integer`

```click
theorem uint64_subtract_to_integer(left: uint64, right: uint64) {
    requires to_integer(right) <= to_integer(left);
    ensures to_integer(left - right) == to_integer(left) - to_integer(right) by {
        have 0 <= to_integer(left) - to_integer(right) by {
            arithmetic_certificate {
                negated_goal => to_integer(left) - to_integer(right) < 0;
                premise 0: to_integer(right) <= to_integer(left) => to_integer(right) <= to_integer(left);
                add 0, 1 => to_integer(left) - to_integer(right) + to_integer(right) < 0 + to_integer(left);
                conclusion 2;
            }
        }
        have to_integer(left) - to_integer(right) <= 18446744073709551615 by {
            arithmetic_certificate {
                negated_goal => 18446744073709551615 < to_integer(left) - to_integer(right);
                type_range => to_integer(left) <= 18446744073709551615;
                type_range => 0 <= to_integer(right);
                add 0, 1 => 18446744073709551615 + to_integer(left) < to_integer(left) - to_integer(right) + 18446744073709551615;
                add 3, 2 => 18446744073709551615 + to_integer(left) + 0 < to_integer(left) - to_integer(right) + 18446744073709551615 + to_integer(right);
                conclusion 4;
            }
        }
        have to_integer(left - right) == to_integer(left) - to_integer(right) by {
            arithmetic_certificate rules {
                premise 0: 0 <= to_integer(left) - to_integer(right) => 0 <= to_integer(left) - to_integer(right);
                premise 1: to_integer(left) - to_integer(right) <= 18446744073709551615 => to_integer(left) - to_integer(right) <= 18446744073709551615;
                integer_operation_identity bounds [0, 1] => to_integer(left - right) == to_integer(left) - to_integer(right);
                conclusion 0;
            }
        }
        assumption();
    }
}
```

Unsigned subtraction agrees with Integer subtraction when the subtrahend is at most the minuend, excluding underflow.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `integer::uint64_divide_to_integer`

```click
theorem uint64_divide_to_integer(left: uint64, right: uint64) {
    requires right != 0u64;
    requires to_integer(right) != 0;
    ensures to_integer(left / right) == truncating_quotient(to_integer(left), to_integer(right));
}
```

Unsigned division agrees with the truncating Integer quotient. Both native and observed nonzero divisor premises are required.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `integer::uint64_remainder_to_integer`

```click
theorem uint64_remainder_to_integer(left: uint64, right: uint64) {
    requires right != 0u64;
    requires to_integer(right) != 0;
    ensures to_integer(left % right) == truncating_remainder(to_integer(left), to_integer(right));
}
```

Unsigned remainder agrees with the truncating Integer remainder. Both native and observed nonzero divisor premises are required.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `integer::uint64_to_integer_less_equal_implies_less_equal`

```click
theorem uint64_to_integer_less_equal_implies_less_equal(left: uint64, right: uint64) {
    requires to_integer(left) <= to_integer(right);
    ensures left <= right by assumption();
}
```

Exact Integer observation order implies native uint64 non-strict order. The mathematical order premise is required.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `integer::uint32_pack_uint16_to_integer`

```click
theorem uint32_pack_uint16_to_integer(low: uint32, high: uint32) {
    requires low <= 65535u32;
    requires high <= 65535u32;
    ensures to_integer(low | (high << 16)) == to_integer(low) + 65536 * to_integer(high);
}
```

Two unsigned 16-bit fields have this exact packed Integer value when both native bounds hold.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `integer::uint32_pack_uint16_high_first_to_integer`

```click
theorem uint32_pack_uint16_high_first_to_integer(low: uint32, high: uint32) {
    requires low <= 65535u32;
    requires high <= 65535u32;
    ensures to_integer((high << 16) | low) == to_integer(low) + 65536 * to_integer(high);
}
```

Two unsigned 16-bit fields have this exact packed Integer value with the shifted high field written first. Both native bounds are required.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `integer::uint32_unpack_uint16_low`

```click
theorem uint32_unpack_uint16_low(low: uint32, high: uint32) {
    requires low <= 65535u32;
    requires high <= 65535u32;
    ensures (((high << 16) | low) & 65535u32) == low;
}
```

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `integer::uint32_unpack_uint16_high`

```click
theorem uint32_unpack_uint16_high(low: uint32, high: uint32) {
    requires low <= 65535u32;
    requires high <= 65535u32;
    ensures ((((high << 16) | low) >> 16) & 65535u32) == high;
}
```

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

These exact word identities require both fields to fit in 16 bits. The high
word uses a logical right shift, so the identity also holds when the packed
word's top bit is set. Their bounds are checked premises of the kernel rules.

### `integer::uint64_pack_uint16_to_integer`

```click
theorem uint64_pack_uint16_to_integer(low: uint64, high: uint64) {
    requires low <= 65535u64;
    requires high <= 65535u64;
    ensures to_integer(low | (high << 16)) == to_integer(low) + 65536 * to_integer(high);
}
```

Two unsigned 16-bit fields have this exact packed Integer value when both native bounds hold.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `integer::uint64_unpack_uint16_low`

```click
theorem uint64_unpack_uint16_low(low: uint64, high: uint64) {
    requires low <= 65535u64;
    requires high <= 65535u64;
    ensures ((low | (high << 16)) & 65535u64) == low;
}
```

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `integer::uint64_unpack_uint16_high`

```click
theorem uint64_unpack_uint16_high(low: uint64, high: uint64) {
    requires low <= 65535u64;
    requires high <= 65535u64;
    ensures (((low | (high << 16)) >> 16) & 65535u64) == high;
}
```

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

The kernel issues these exact LP64 word identities only with both 16-bit field
bounds. They retain all packed bits, including bit 31; the high field uses a
logical right shift.

### `integer::uint64_less_than_implies_not_greater_equal`

```click
theorem uint64_less_than_implies_not_greater_equal(left: uint64, right: uint64) {
    requires left < right;
    ensures not (left >= right) by assumption();
}
```

A strict unsigned order excludes the opposite greater-or-equal branch.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `integer::uint32_less_equal_to_integer`

```click
theorem uint32_less_equal_to_integer(left: uint32, right: uint32) {
    requires left <= right;
    ensures to_integer(left) <= to_integer(right) by assumption();
}
```

Preserves native unsigned order in exact Integer observations, including values above the sign bit. The native order premise is required.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `integer::uint32_to_integer_less_equal_implies_less_equal`

```click
theorem uint32_to_integer_less_equal_implies_less_equal(left: uint32, right: uint32) {
    requires to_integer(left) <= to_integer(right);
    ensures left <= right by assumption();
}
```

Reflects exact Integer observation order into native unsigned order. The mathematical order premise is required.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `integer::uint32_to_integer_equal_implies_equal`

```click
theorem uint32_to_integer_equal_implies_equal(left: uint32, right: uint32) {
    requires to_integer(left) == to_integer(right);
    ensures left == right by assumption();
}
```

Reflects equal exact Integer observations into native unsigned equality. Every
32-bit pattern, including those above the signed sign bit, has one unsigned
Integer value, so the observation is injective.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `integer::uint32_remainder_less_than_divisor`

```click
theorem uint32_remainder_less_than_divisor(value: uint32, divisor: uint32) {
    requires divisor != 0u32;
    ensures value % divisor < divisor by {
        have 1 <= to_integer(divisor) by {
            arithmetic_certificate {
                excluded_bound 0: to_integer(divisor) != 0 => 1 <= to_integer(divisor);
                conclusion 0;
            }
        }
        have to_integer(divisor) != 0 by {
            arithmetic_certificate rules {
                premise 0: 1 <= to_integer(divisor) => 1 <= to_integer(divisor);
                integer_bound_exclusion bounds [0] => to_integer(divisor) != 0;
                conclusion 0;
            }
        }
        have 0 < to_integer(divisor) by {
            arithmetic_certificate {
                premise 0: 1 <= to_integer(divisor) => 1 <= to_integer(divisor);
                conclusion 0;
            }
        }
        apply(integer::uint32_remainder_to_integer(value, divisor)) using {
            divisor != 0u32;
            to_integer(divisor) != 0;
        };
        apply(integer::positive_divisor_remainder_upper(to_integer(value), to_integer(divisor))) using {
            to_integer(divisor) != 0;
            0 < to_integer(divisor);
        };
        arithmetic_certificate {
            negated_goal => to_integer(divisor) <= to_integer(value % divisor);
            premise 0: to_integer(value % divisor) == truncating_remainder(to_integer(value), to_integer(divisor)) => to_integer(value % divisor) == truncating_remainder(to_integer(value), to_integer(divisor));
            premise 1: truncating_remainder(to_integer(value), to_integer(divisor)) <= to_integer(divisor) - 1 => truncating_remainder(to_integer(value), to_integer(divisor)) <= to_integer(divisor) - 1;
            less_equal_from_equal 1 => to_integer(value % divisor) <= truncating_remainder(to_integer(value), to_integer(divisor));
            add 0, 3 => to_integer(divisor) + to_integer(value % divisor) <= to_integer(value % divisor) + truncating_remainder(to_integer(value), to_integer(divisor));
            add 4, 2 => to_integer(divisor) + to_integer(value % divisor) + truncating_remainder(to_integer(value), to_integer(divisor)) <= to_integer(value % divisor) + truncating_remainder(to_integer(value), to_integer(divisor)) + to_integer(divisor) - 1;
            conclusion 5;
        }
    }
}
```

The unsigned remainder is below its divisor for any dividend. The nonzero divisor premise is essential.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `integer::uint32_less_than_divisor_implies_remainder_is_value`

```click
theorem uint32_less_than_divisor_implies_remainder_is_value(value: uint32, divisor: uint32) {
    requires value < divisor;
    ensures value % divisor == value by {
        have to_integer(value) < to_integer(divisor) by {
            normalize() using { value < divisor; };
        }
        have 0 <= to_integer(value) by {
            normalize();
        }
        have 1 <= to_integer(divisor) by {
            arithmetic_certificate {
                premise 0: to_integer(value) < to_integer(divisor) => to_integer(value) < to_integer(divisor);
                type_range => 0 <= to_integer(value);
                add 0, 1 => to_integer(value) + 0 < to_integer(divisor) + to_integer(value);
                conclusion 2;
            }
        }
        have to_integer(divisor) != 0 by {
            normalize() using { 1 <= to_integer(divisor); };
        }
        have divisor != 0u32 by {
            normalize() using { to_integer(divisor) != 0; };
        }
        apply(integer::uint32_remainder_to_integer(value, divisor)) using {
            divisor != 0u32;
            to_integer(divisor) != 0;
        };
        have 0 * to_integer(divisor) <= to_integer(value) by {
            arithmetic_certificate {
                premise 0: 0 <= to_integer(value) => 0 <= to_integer(value);
                conclusion 0;
            }
        }
        apply(integer::positive_divisor_quotient_lower(to_integer(value), to_integer(divisor), 0)) using {
            to_integer(divisor) != 0;
            1 <= to_integer(divisor);
            0 * to_integer(divisor) <= to_integer(value);
        };
        have to_integer(value) < 1 * to_integer(divisor) by {
            arithmetic_certificate {
                premise 0: to_integer(value) < to_integer(divisor) => to_integer(value) < to_integer(divisor);
                conclusion 0;
            }
        }
        have 0 < 1 by {
            normalize();
        }
        apply(integer::positive_divisor_quotient_strict_upper(to_integer(value), to_integer(divisor), 1)) using {
            to_integer(divisor) != 0;
            1 <= to_integer(divisor);
            0 < 1;
            to_integer(value) < 1 * to_integer(divisor);
        };
        have truncating_quotient(to_integer(value), to_integer(divisor)) == 0 by {
            arithmetic_certificate {
                premise 0: truncating_quotient(to_integer(value), to_integer(divisor)) < 1 => truncating_quotient(to_integer(value), to_integer(divisor)) <= 0;
                premise 1: 0 <= truncating_quotient(to_integer(value), to_integer(divisor)) => 0 <= truncating_quotient(to_integer(value), to_integer(divisor));
                equal_from_bounds 0, 1 => truncating_quotient(to_integer(value), to_integer(divisor)) == 0;
                conclusion 2;
            }
        }
        apply(integer::truncation_identity(to_integer(value), to_integer(divisor))) using {
            to_integer(divisor) != 0;
        };
        have truncating_quotient(to_integer(value), to_integer(divisor)) * to_integer(divisor) == 0 by {
            rewrite(truncating_quotient(to_integer(value), to_integer(divisor)) == 0);
            normalize();
        }
        have to_integer(value % divisor) == to_integer(value) by {
            arithmetic_certificate {
                premise 0: to_integer(value % divisor) == truncating_remainder(to_integer(value), to_integer(divisor)) => to_integer(value % divisor) == truncating_remainder(to_integer(value), to_integer(divisor));
                premise 1: to_integer(value) == truncating_quotient(to_integer(value), to_integer(divisor)) * to_integer(divisor) + truncating_remainder(to_integer(value), to_integer(divisor)) => to_integer(value) == truncating_quotient(to_integer(value), to_integer(divisor)) * to_integer(divisor) + truncating_remainder(to_integer(value), to_integer(divisor));
                premise 2: truncating_quotient(to_integer(value), to_integer(divisor)) * to_integer(divisor) == 0 => truncating_quotient(to_integer(value), to_integer(divisor)) * to_integer(divisor) == 0;
                scale 1 by -1 => -1 * to_integer(value) == -1 * (truncating_quotient(to_integer(value), to_integer(divisor)) * to_integer(divisor) + truncating_remainder(to_integer(value), to_integer(divisor)));
                add 0, 3 => to_integer(value % divisor) + -1 * to_integer(value) == truncating_remainder(to_integer(value), to_integer(divisor)) + -1 * (truncating_quotient(to_integer(value), to_integer(divisor)) * to_integer(divisor) + truncating_remainder(to_integer(value), to_integer(divisor)));
                scale 2 by -1 => -1 * (truncating_quotient(to_integer(value), to_integer(divisor)) * to_integer(divisor)) == -1 * 0;
                add 4, 5 => to_integer(value % divisor) + -1 * to_integer(value) + -1 * (truncating_quotient(to_integer(value), to_integer(divisor)) * to_integer(divisor)) == truncating_remainder(to_integer(value), to_integer(divisor)) + -1 * (truncating_quotient(to_integer(value), to_integer(divisor)) * to_integer(divisor) + truncating_remainder(to_integer(value), to_integer(divisor))) + -1 * 0;
                conclusion 6;
            }
        }
        assumption();
    }
}
```

A dividend below its unsigned divisor is unchanged by reduction. The strict
unsigned premise excludes a zero divisor; a nonzero divisor or a non-strict
bound alone is insufficient. Values above the signed sign bit retain their
unsigned meaning.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `integer::uint32_to_integer_bounds`

```click
theorem uint32_to_integer_bounds(value: uint32) {
    ensures 0 <= to_integer(value) by {
        have 0u32 <= value;
        apply(integer::uint32_less_equal_to_integer(0u32, value)) using { 0u32 <= value; };
    }
    ensures to_integer(value) <= 4294967295 by {
        have value <= 4294967295u32;
        apply(integer::uint32_less_equal_to_integer(value, 4294967295u32)) using { value <= 4294967295u32; };
    }
}
```

Proves the full unsigned observation range from native order. This theorem does not distribute observations over wrapping operations.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `integer::int32_add_to_integer`

```click
theorem int32_add_to_integer(left: int32, right: int32) {
    requires defined(left + right);
    ensures to_integer(left + right) == to_integer(left) + to_integer(right) by {
        have -2147483648 <= to_integer(left) + to_integer(right) by {
            assumption();
        }
        have to_integer(left) + to_integer(right) <= 2147483647 by {
            assumption();
        }
        have to_integer(left + right) == to_integer(left) + to_integer(right) by {
            arithmetic_certificate rules {
                premise 0: -2147483648 <= to_integer(left) + to_integer(right) => -2147483648 <= to_integer(left) + to_integer(right);
                premise 1: to_integer(left) + to_integer(right) <= 2147483647 => to_integer(left) + to_integer(right) <= 2147483647;
                integer_operation_identity bounds [0, 1] => to_integer(left + right) == to_integer(left) + to_integer(right);
                conclusion 0;
            }
        }
        assumption();
    }
}
```

A defined signed C addition has the same value as mathematical Integer addition.
The definedness premise excludes overflow; the equality is not unconditional.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `integer::int64_subtract_to_integer`

```click
theorem int64_subtract_to_integer(left: int64, right: int64) {
    requires defined(left - right);
    ensures to_integer(left - right) == to_integer(left) - to_integer(right) by {
        have -9223372036854775808 <= to_integer(left) - to_integer(right) by {
            assumption();
        }
        have to_integer(left) - to_integer(right) <= 9223372036854775807 by {
            assumption();
        }
        have to_integer(left - right) == to_integer(left) - to_integer(right) by {
            arithmetic_certificate rules {
                premise 0: -9223372036854775808 <= to_integer(left) - to_integer(right) => -9223372036854775808 <= to_integer(left) - to_integer(right);
                premise 1: to_integer(left) - to_integer(right) <= 9223372036854775807 => to_integer(left) - to_integer(right) <= 9223372036854775807;
                integer_operation_identity bounds [0, 1] => to_integer(left - right) == to_integer(left) - to_integer(right);
                conclusion 0;
            }
        }
        assumption();
    }
}
```

A defined signed 64-bit operation has its exact mathematical Integer value.
The native definedness premise excludes overflow; this law does not establish
that premise or infer any operand range.

**Verified use:** [`mdtests/int64_integer_operation_bridges.md`](https://github.com/clicklang/click/blob/master/mdtests/int64_integer_operation_bridges.md).

### `integer::int32_subtract_to_integer`

```click
theorem int32_subtract_to_integer(left: int32, right: int32) {
    requires defined(left - right);
    ensures to_integer(left - right) == to_integer(left) - to_integer(right) by {
        have -2147483648 <= to_integer(left) - to_integer(right) by {
            assumption();
        }
        have to_integer(left) - to_integer(right) <= 2147483647 by {
            assumption();
        }
        have to_integer(left - right) == to_integer(left) - to_integer(right) by {
            arithmetic_certificate rules {
                premise 0: -2147483648 <= to_integer(left) - to_integer(right) => -2147483648 <= to_integer(left) - to_integer(right);
                premise 1: to_integer(left) - to_integer(right) <= 2147483647 => to_integer(left) - to_integer(right) <= 2147483647;
                integer_operation_identity bounds [0, 1] => to_integer(left - right) == to_integer(left) - to_integer(right);
                conclusion 0;
            }
        }
        assumption();
    }
}
```

A defined signed C subtraction has the same value as mathematical Integer subtraction.
The definedness premise excludes overflow; the equality is not unconditional.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `integer::int32_less_equal_to_integer`

```click
theorem int32_less_equal_to_integer(left: int32, right: int32) {
    requires left <= right;
    ensures to_integer(left) <= to_integer(right) by assumption();
}
```

A signed C order fact transfers to the exact mathematical observations of the
two operands. The C order premise is required; the bridge does not assume an
order between unrelated machine values.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `integer::int32_to_integer_less_equal_implies_less_equal`

```click
theorem int32_to_integer_less_equal_implies_less_equal(left: int32, right: int32) {
    requires to_integer(left) <= to_integer(right);
    ensures left <= right by assumption();
}
```

A proved non-strict order between exact signed observations establishes the native order. The named requirement is necessary; no ambient machine range or overflow fact is inferred.

**Verified use:** [`mdtests/signed_integer_order_bridges.md`](https://github.com/clicklang/click/blob/master/mdtests/signed_integer_order_bridges.md).

### `integer::int64_to_integer_less_equal_implies_less_equal`

```click
theorem int64_to_integer_less_equal_implies_less_equal(left: int64, right: int64) {
    requires to_integer(left) <= to_integer(right);
    ensures left <= right by assumption();
}
```

A proved non-strict order between exact signed observations establishes the native order. The named requirement is necessary; no ambient machine range or overflow fact is inferred.

**Verified use:** [`mdtests/signed_integer_order_bridges.md`](https://github.com/clicklang/click/blob/master/mdtests/signed_integer_order_bridges.md).

### `integer::int32_positive_predecessor_is_nonnegative`

```click
theorem int32_positive_predecessor_is_nonnegative(value: int32) {
    requires 0 < value;

    ensures 0 <= to_integer(value - 1) by {
        arithmetic_certificate signed_int32 {
            premise 0: (0 as int32) < (value as int32) => (0 as int32) < (value as int32);
            interval_from_affine 0 (value) (1) (2147483647);
            interval_atom (1) (1) (1);
            interval_subtract 1, 2 1 (0) (2147483646);
            affine_conclusion 0 3 => (0 as int32) <= ((value - 1) as int32);
            conclusion 4;
        }
    }
}
```

**Meaning:** Given its listed requirements, proves `0 <= to_integer(value - 1)`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `integer::int32_positive_predecessor_strictly_decreases`

```click
theorem int32_positive_predecessor_strictly_decreases(value: int32) {
    requires 0 < value;

    ensures to_integer(value - 1) < to_integer(value) by {
        arithmetic_certificate signed_int32 {
            premise 0: (0 as int32) < (value as int32) => (0 as int32) < (value as int32);
            interval_from_affine 0 (value) (1) (2147483647);
            interval_atom (1) (1) (1);
            interval_subtract 1, 2 1 (0) (2147483646);
            trivial => 0 <= 0;
            affine_conclusion 4 3 => ((value - 1) as int32) < (value as int32);
            conclusion 5;
        }
    }
}
```

**Meaning:** Given its listed requirements, proves `to_integer(value - 1) < to_integer(value)`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `integer::uint32_positive_predecessor_strictly_decreases`

```click
theorem uint32_positive_predecessor_strictly_decreases(value: uint32) {
    requires 0u32 < value;

    ensures to_integer(value - 1u32) < to_integer(value) by {
        have 0 < to_integer(value) by {
            assumption();
        }
        have 0 <= to_integer(value) - 1 by {
            arithmetic_certificate {
                negated_goal => to_integer(value) - 1 < 0;
                premise 0: 0 < to_integer(value) => 0 < to_integer(value);
                add 0, 1 => to_integer(value) - 1 + 1 + (0 + 1) <= 0 + to_integer(value);
                conclusion 2;
            }
        }
        have to_integer(value) - 1 <= 4294967295 by {
            arithmetic_certificate {
                negated_goal => 4294967295 < to_integer(value) - 1;
                type_range => to_integer(value) <= 4294967295;
                add 0, 1 => 4294967295 + to_integer(value) < to_integer(value) - 1 + 4294967295;
                conclusion 2;
            }
        }
        have to_integer(value - 1u32) == to_integer(value) - 1 by {
            arithmetic_certificate rules {
                premise 0: 0 <= to_integer(value) - 1 => 0 <= to_integer(value) - 1;
                premise 1: to_integer(value) - 1 <= 4294967295 => to_integer(value) - 1 <= 4294967295;
                integer_operation_identity bounds [0, 1] => to_integer(value - 1u32) == to_integer(value) - 1;
                conclusion 0;
            }
        }
        arithmetic_certificate {
            premise 0: to_integer(value - 1u32) == to_integer(value) - 1 => to_integer(value - 1u32) == to_integer(value) - 1;
            less_equal_from_equal 0 => to_integer(value - 1u32) <= to_integer(value) - 1;
            conclusion 1;
        }
    }
}
```

**Meaning:** Given its listed requirements, proves `to_integer(value - 1u32) < to_integer(value)`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `integer::uint32_increment_upper_bound`

```click
theorem uint32_increment_upper_bound(value: uint32, upper: uint32) {
    requires value < upper;

    ensures to_integer(value + 1u32) <= to_integer(upper) by {
        have to_integer(value) < to_integer(upper) by {
            assumption();
        }
        have 0 <= to_integer(value) + 1 by {
            arithmetic_certificate {
                negated_goal => to_integer(value) + 1 < 0;
                type_range => 0 <= to_integer(value);
                add 0, 1 => to_integer(value) + 1 + 0 < 0 + to_integer(value);
                conclusion 2;
            }
        }
        have to_integer(value) + 1 <= 4294967295 by {
            arithmetic_certificate {
                negated_goal => 4294967295 < to_integer(value) + 1;
                premise 0: to_integer(value) < to_integer(upper) => to_integer(value) < to_integer(upper);
                type_range => to_integer(upper) <= 4294967295;
                add 0, 1 => 4294967295 + 1 + (to_integer(value) + 1) <= to_integer(value) + 1 + to_integer(upper);
                add 3, 2 => 4294967295 + 1 + (to_integer(value) + 1) + to_integer(upper) <= to_integer(value) + 1 + to_integer(upper) + 4294967295;
                conclusion 4;
            }
        }
        have to_integer(value + 1u32) == to_integer(value) + 1 by {
            arithmetic_certificate rules {
                premise 0: 0 <= to_integer(value) + 1 => 0 <= to_integer(value) + 1;
                premise 1: to_integer(value) + 1 <= 4294967295 => to_integer(value) + 1 <= 4294967295;
                integer_operation_identity bounds [0, 1] => to_integer(value + 1u32) == to_integer(value) + 1;
                conclusion 0;
            }
        }
        arithmetic_certificate {
            premise 0: to_integer(value + 1u32) == to_integer(value) + 1 => to_integer(value + 1u32) == to_integer(value) + 1;
            less_equal_from_equal 0 => to_integer(value + 1u32) <= to_integer(value) + 1;
            premise 1: to_integer(value) < to_integer(upper) => to_integer(value) < to_integer(upper);
            add 1, 2 => to_integer(value + 1u32) + to_integer(value) < to_integer(value) + 1 + to_integer(upper);
            conclusion 3;
        }
    }
}
```

**Meaning:** Given its listed requirements, proves `to_integer(value + 1u32) <= to_integer(upper)`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `integer::uint32_less_than_implies_positive_difference`

```click
theorem uint32_less_than_implies_positive_difference(value: uint32, upper: uint32) {
    requires value < upper;

    ensures 0 < to_integer(upper - value) by {
        have 0 <= to_integer(upper) - to_integer(value) by {
            arithmetic_certificate {
                negated_goal => to_integer(upper) - to_integer(value) < 0;
                premise 0: to_integer(value) < to_integer(upper) => to_integer(value) < to_integer(upper);
                add 0, 1 => to_integer(upper) - to_integer(value) + 1 + (to_integer(value) + 1) <= 0 + to_integer(upper);
                conclusion 2;
            }
        }
        have to_integer(upper) - to_integer(value) <= 4294967295 by {
            arithmetic_certificate {
                negated_goal => 4294967295 < to_integer(upper) - to_integer(value);
                type_range => to_integer(upper) <= 4294967295;
                type_range => 0 <= to_integer(value);
                add 0, 1 => 4294967295 + to_integer(upper) < to_integer(upper) - to_integer(value) + 4294967295;
                add 3, 2 => 4294967295 + to_integer(upper) + 0 < to_integer(upper) - to_integer(value) + 4294967295 + to_integer(value);
                conclusion 4;
            }
        }
        have to_integer(upper - value) == to_integer(upper) - to_integer(value) by {
            arithmetic_certificate rules {
                premise 0: 0 <= to_integer(upper) - to_integer(value) => 0 <= to_integer(upper) - to_integer(value);
                premise 1: to_integer(upper) - to_integer(value) <= 4294967295 => to_integer(upper) - to_integer(value) <= 4294967295;
                integer_operation_identity bounds [0, 1] => to_integer(upper - value) == to_integer(upper) - to_integer(value);
                conclusion 0;
            }
        }
        arithmetic_certificate {
            negated_goal => to_integer(upper - value) <= 0;
            premise 0: to_integer(upper - value) == to_integer(upper) - to_integer(value) => to_integer(upper - value) == to_integer(upper) - to_integer(value);
            less_equal_from_equal 1 reverse => to_integer(upper) - to_integer(value) <= to_integer(upper - value);
            premise 1: to_integer(value) < to_integer(upper) => to_integer(value) < to_integer(upper);
            add 0, 2 => to_integer(upper - value) + (to_integer(upper) - to_integer(value)) <= 0 + to_integer(upper - value);
            add 4, 3 => to_integer(upper - value) + (to_integer(upper) - to_integer(value)) + to_integer(value) < 0 + to_integer(upper - value) + to_integer(upper);
            conclusion 5;
        }
    }
}
```

**Meaning:** Given its listed requirements, proves `0 < to_integer(upper - value)`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `integer::uint32_difference_decreases_after_increment`

```click
axiom uint32_difference_decreases_after_increment(value: uint32, bound: uint32) {
    requires value < bound;
    ensures to_integer((0u32 - value) + (bound - 1u32)) < to_integer((0u32 - value) + bound);
}
```

**Axiom:** trusted, not proved. Under `value < bound` neither `bound - value` nor `(bound - 1) - value` wraps, so the left side is one less than the right.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `integer::uint64_less_than_less_equal_transitive`

```click
theorem uint64_less_than_less_equal_transitive(first: uint64, middle: uint64, last: uint64) {
    requires first < middle;
    requires middle <= last;

    ensures first < last by {
        arithmetic_certificate {
            premise 0: first < middle => first < middle;
            premise 1: middle <= last => middle <= last;
            add 0, 1 => to_integer(first) + to_integer(middle) < to_integer(middle) + to_integer(last);
            conclusion 2;
        }
    }
}
```

Transitivity of unsigned 64-bit order: `first < middle` and `middle <= last` give `first < last`.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `integer::uint64_less_equal_transitive`

```click
theorem uint64_less_equal_transitive(first: uint64, middle: uint64, last: uint64) {
    requires first <= middle;
    requires middle <= last;

    ensures first <= last by {
        arithmetic_certificate {
            premise 0: first <= middle => first <= middle;
            premise 1: middle <= last => middle <= last;
            add 0, 1 => to_integer(first) + to_integer(middle) <= to_integer(middle) + to_integer(last);
            conclusion 2;
        }
    }
}
```

Transitivity of unsigned 64-bit order: `first <= middle` and `middle <= last` give `first <= last`.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `integer::int32_nonnegative_predecessor_upper_bound`

```click
theorem int32_nonnegative_predecessor_upper_bound(value: int32, bound: int32) {
    requires 0 <= value;
    requires value <= bound;

    ensures to_integer(value - 1) <= to_integer(bound) by {
        arithmetic_certificate signed_int32 {
            premise 0: (0 as int32) <= (value as int32) => (0 as int32) <= (value as int32);
            premise 1: (value as int32) <= (bound as int32) => (value as int32) <= (bound as int32);
            interval_from_affine 0 (value) (0) (2147483647);
            interval_atom (1) (1) (1);
            interval_subtract 2, 3 2 (-1) (2147483646);
            trivial => -1 <= 0;
            add 1, 5 => (to_integer(value as int32) + -1) <= (to_integer(bound as int32) + 0);
            affine_conclusion 6 4 => ((value - 1) as int32) <= (bound as int32);
            conclusion 7;
        }
    }
}
```

**Meaning:** Given its listed requirements, proves `to_integer(value - 1) <= to_integer(bound)`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `integer::int32_less_equal_less_than_transitive`

```click
theorem int32_less_equal_less_than_transitive(first: int32, middle: int32, last: int32) {
    requires first <= middle;
    requires middle < last;

    ensures first < last by {
        arithmetic_certificate {
            premise 0: first <= middle => first <= middle;
            premise 1: middle < last => middle < last;
            add 0, 1 => (to_integer(first as int32) + to_integer(middle as int32)) < (to_integer(middle as int32) + to_integer(last as int32));
            conclusion 2;
        }
    }
}
```

**Meaning:** Given its listed requirements, proves `first < last`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `integer::int32_less_equal_transitive`

```click
theorem int32_less_equal_transitive(first: int32, middle: int32, last: int32) {
    requires first <= middle;
    requires middle <= last;

    ensures first <= last by {
        arithmetic_certificate {
            premise 0: first <= middle => first <= middle;
            premise 1: middle <= last => middle <= last;
            add 0, 1 => (to_integer(first as int32) + to_integer(middle as int32)) <= (to_integer(middle as int32) + to_integer(last as int32));
            conclusion 2;
        }
    }
}
```

**Meaning:** Given its listed requirements, proves `first <= last`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `integer::int32_less_equal_and_not_less_than_implies_equal`

```click
theorem int32_less_equal_and_not_less_than_implies_equal(left: int32, right: int32) {
    requires left <= right;
    requires not (left < right);

    ensures left == right by {
        arithmetic_certificate {
            premise 0: left <= right => left <= right;
            premise 1: not left < right => not left < right;
            equal_from_bounds 0, 1 => left == right;
            conclusion 2;
        }
    }
}
```

**Meaning:** Given its listed requirements, proves `left == right`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `integer::int32_less_equal_and_not_equal_implies_less_than`

```click
theorem int32_less_equal_and_not_equal_implies_less_than(left: int32, right: int32) {
    requires left <= right;
    requires left != right;

    ensures left < right by {
        arithmetic_certificate signed_int32 {
            premise 0: (left as int32) <= (right as int32) => (left as int32) <= (right as int32);
            premise 1: (left as int32) != (right as int32) => (left as int32) != (right as int32);
            less_than_from_not_equal 0, 1 => to_integer(left as int32) < to_integer(right as int32);
            conclusion 2;
        }
    }
}
```

**Meaning:** Given its listed requirements, proves `left < right`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### Unsigned wrapping arithmetic

`import click::integer;` provides the C operations on unsigned
values, which wrap modulo `2^32` or `2^64`, as functions. A
specification's `+`, `-` and `*` compare exact
Integers, so a claim about C's modular result names these instead; a
comparison between machine values with no Integer arithmetic keeps its C
meaning (`mdtests/wrapping_arithmetic_keeps_its_c_meaning_under_integer_arithmetic.md`).

### `integer::uint32_wrapping_add`

```click
function uint32_wrapping_add(left: uint32, right: uint32) -> uint32 {
    left + right
}
```

**Meaning:** The C uint32 sum `left + right`, reduced modulo 2^32.

**Kind:** function. Parameter types and the result type are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `integer::uint32_wrapping_sub`

```click
function uint32_wrapping_sub(left: uint32, right: uint32) -> uint32 {
    left - right
}
```

**Meaning:** The C uint32 difference `left - right`, reduced modulo 2^32.

**Kind:** function. Parameter types and the result type are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `integer::uint32_wrapping_mul`

```click
function uint32_wrapping_mul(left: uint32, right: uint32) -> uint32 {
    left * right
}
```

**Meaning:** The C uint32 product `left * right`, reduced modulo 2^32.

**Kind:** function. Parameter types and the result type are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `integer::uint64_wrapping_add`

```click
function uint64_wrapping_add(left: uint64, right: uint64) -> uint64 {
    left + right
}
```

**Meaning:** The C uint64 sum `left + right`, reduced modulo 2^64.

**Kind:** function. Parameter types and the result type are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `integer::uint64_wrapping_sub`

```click
function uint64_wrapping_sub(left: uint64, right: uint64) -> uint64 {
    left - right
}
```

**Meaning:** The C uint64 difference `left - right`, reduced modulo 2^64.

**Kind:** function. Parameter types and the result type are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `integer::uint64_wrapping_mul`

```click
function uint64_wrapping_mul(left: uint64, right: uint64) -> uint64 {
    left * right
}
```

**Meaning:** The C uint64 product `left * right`, reduced modulo 2^64.

**Kind:** function. Parameter types and the result type are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### Integer round trips

### `integer::to_int8_round_trip`

```click
theorem to_int8_round_trip(z: Integer) {
    requires z >= -128;
    requires z <= 127;
    ensures to_integer(to_int8(z)) == z by {
        have -128 <= z by {
            assumption();
        }
        have z <= 127 by {
            assumption();
        }
        arithmetic_certificate rules {
            premise 0: -128 <= z => -128 <= z;
            premise 1: z <= 127 => z <= 127;
            integer_cast_identity bounds [0, 1] => to_integer(to_int8(z)) == z;
            conclusion 0;
        }
    }
}
```

An Integer within the exact `int8` range retains its value after conversion
to that machine type and back. Both bounds are required. The proof is the
`integer_cast_identity` certificate that the omitted proof plans and
`click expand` writes; it is no kernel standard theorem.


### `integer::to_int16_round_trip`

```click
theorem to_int16_round_trip(z: Integer) {
    requires z >= -32768;
    requires z <= 32767;
    ensures to_integer(to_int16(z)) == z by {
        have -32768 <= z by {
            assumption();
        }
        have z <= 32767 by {
            assumption();
        }
        arithmetic_certificate rules {
            premise 0: -32768 <= z => -32768 <= z;
            premise 1: z <= 32767 => z <= 32767;
            integer_cast_identity bounds [0, 1] => to_integer(to_int16(z)) == z;
            conclusion 0;
        }
    }
}
```

An Integer within the exact `int16` range retains its value after conversion
to that machine type and back. Both bounds are required. The proof is the
`integer_cast_identity` certificate that the omitted proof plans and
`click expand` writes; it is no kernel standard theorem.

### `integer::to_int32_round_trip`

```click
theorem to_int32_round_trip(z: Integer) {
    requires z >= -2147483648;
    requires z <= 2147483647;
    ensures to_integer(to_int32(z)) == z by {
        have -2147483648 <= z by {
            assumption();
        }
        have z <= 2147483647 by {
            assumption();
        }
        arithmetic_certificate rules {
            premise 0: -2147483648 <= z => -2147483648 <= z;
            premise 1: z <= 2147483647 => z <= 2147483647;
            integer_cast_identity bounds [0, 1] => to_integer(to_int32(z)) == z;
            conclusion 0;
        }
    }
}
```

An Integer within the exact `int32` range retains its value after conversion
to that machine type and back. Both bounds are required. The proof is the
`integer_cast_identity` certificate that the omitted proof plans and
`click expand` writes; it is no kernel standard theorem.

### `integer::to_uint8_round_trip`

```click
theorem to_uint8_round_trip(z: Integer) {
    requires z >= 0;
    requires z <= 255;
    ensures to_integer(to_uint8(z)) == z by {
        have 0 <= z by {
            assumption();
        }
        have z <= 255 by {
            assumption();
        }
        arithmetic_certificate rules {
            premise 0: 0 <= z => 0 <= z;
            premise 1: z <= 255 => z <= 255;
            integer_cast_identity bounds [0, 1] => to_integer(to_uint8(z)) == z;
            conclusion 0;
        }
    }
}
```

An Integer within the exact `uint8` range retains its value after conversion
to that machine type and back. Both bounds are required. The proof is the
`integer_cast_identity` certificate that the omitted proof plans and
`click expand` writes; it is no kernel standard theorem.

### `integer::to_uint16_round_trip`

```click
theorem to_uint16_round_trip(z: Integer) {
    requires z >= 0;
    requires z <= 65535;
    ensures to_integer(to_uint16(z)) == z by {
        have 0 <= z by {
            assumption();
        }
        have z <= 65535 by {
            assumption();
        }
        arithmetic_certificate rules {
            premise 0: 0 <= z => 0 <= z;
            premise 1: z <= 65535 => z <= 65535;
            integer_cast_identity bounds [0, 1] => to_integer(to_uint16(z)) == z;
            conclusion 0;
        }
    }
}
```

An Integer within the exact `uint16` range retains its value after conversion
to that machine type and back. Both bounds are required. The proof is the
`integer_cast_identity` certificate that the omitted proof plans and
`click expand` writes; it is no kernel standard theorem.

### `integer::to_uint32_round_trip`

```click
theorem to_uint32_round_trip(z: Integer) {
    requires z >= 0;
    requires z <= 4294967295;
    ensures to_integer(to_uint32(z)) == z by {
        have 0 <= z by {
            assumption();
        }
        have z <= 4294967295 by {
            assumption();
        }
        arithmetic_certificate rules {
            premise 0: 0 <= z => 0 <= z;
            premise 1: z <= 4294967295 => z <= 4294967295;
            integer_cast_identity bounds [0, 1] => to_integer(to_uint32(z)) == z;
            conclusion 0;
        }
    }
}
```

An Integer within the exact `uint32` range retains its value after conversion
to that machine type and back. Both bounds are required. The proof is the
`integer_cast_identity` certificate that the omitted proof plans and
`click expand` writes; it is no kernel standard theorem.

### `integer::to_int64_round_trip`

```click
theorem to_int64_round_trip(z: Integer) {
    requires z >= -9223372036854775808;
    requires z <= 9223372036854775807;
    ensures to_integer(to_int64(z)) == z by {
        have -9223372036854775808 <= z by {
            assumption();
        }
        have z <= 9223372036854775807 by {
            assumption();
        }
        arithmetic_certificate rules {
            premise 0: -9223372036854775808 <= z => -9223372036854775808 <= z;
            premise 1: z <= 9223372036854775807 => z <= 9223372036854775807;
            integer_cast_identity bounds [0, 1] => to_integer(to_int64(z)) == z;
            conclusion 0;
        }
    }
}
```

An Integer within the exact `int64` range retains its value after conversion
to that machine type and back. Both bounds are required. The proof is the
`integer_cast_identity` certificate that the omitted proof plans and
`click expand` writes; it is no kernel standard theorem.

### `integer::to_uint64_round_trip`

```click
theorem to_uint64_round_trip(z: Integer) {
    requires z >= 0;
    requires z <= 18446744073709551615;
    ensures to_integer(to_uint64(z)) == z by {
        have 0 <= z by {
            assumption();
        }
        have z <= 18446744073709551615 by {
            assumption();
        }
        arithmetic_certificate rules {
            premise 0: 0 <= z => 0 <= z;
            premise 1: z <= 18446744073709551615 => z <= 18446744073709551615;
            integer_cast_identity bounds [0, 1] => to_integer(to_uint64(z)) == z;
            conclusion 0;
        }
    }
}
```

An Integer within the exact `uint64` range retains its value after conversion
to that machine type and back. Both bounds are required. The proof is the
`integer_cast_identity` certificate that the omitted proof plans and
`click expand` writes; it is no kernel standard theorem.

### Mathematical truncating division

These Integer laws use truncation toward zero, independently of native machine
widths and of the planned Euclidean `/` and `%` operators. They do not establish
native division or narrowing safety.

### `integer::truncation_identity`

```click
theorem truncation_identity(n: Integer, d: Integer) {
    requires d != 0;
    ensures n == truncating_quotient(n, d) * d + truncating_remainder(n, d);
}
```

### `integer::positive_divisor_remainder_lower`

```click
theorem positive_divisor_remainder_lower(n: Integer, d: Integer) {
    requires d != 0;
    requires 0 < d;
    ensures 1 - d <= truncating_remainder(n, d);
}
```

### `integer::positive_divisor_remainder_upper`

```click
theorem positive_divisor_remainder_upper(n: Integer, d: Integer) {
    requires d != 0;
    requires 0 < d;
    ensures truncating_remainder(n, d) <= d - 1;
}
```

### `integer::nonnegative_dividend_remainder`

```click
theorem nonnegative_dividend_remainder(n: Integer, d: Integer) {
    requires d != 0;
    requires 0 <= n;
    ensures 0 <= truncating_remainder(n, d);
}
```

### `integer::nonpositive_dividend_remainder`

```click
theorem nonpositive_dividend_remainder(n: Integer, d: Integer) {
    requires d != 0;
    requires n <= 0;
    ensures truncating_remainder(n, d) <= 0;
}
```


### `integer::multiply_add`

```click
theorem multiply_add(a: Integer, b: Integer, c: Integer) {
    ensures (a + b) * c == a * c + b * c by {
        arithmetic_certificate rules {
            integer_polynomial_identity bounds [] => (a + b) * c == a * c + b * c;
            conclusion 0;
        }
    }
}
```


### `integer::floor_from_remainder`

```click
theorem floor_from_remainder(n: Integer, d: Integer, q: Integer, r: Integer, value: Integer) {
    requires 0 < d;
    requires n == q * d + r;
    requires 1 - d <= r;
    requires r <= d - 1;
    requires r < 0 implies value == q + -1;
    requires 0 <= r implies value == q;
    ensures value * d <= n by {
        if r < 0 {
            have value == q + -1;
            apply(integer::multiply_add(q, -1, d));
            rewrite(value == q + -1);
            rewrite((q + -1) * d == q * d + -1 * d);
            solve() using { n == q * d + r; 1 - d <= r; };
        } else {
            have 0 <= r by { solve() using { not (r < 0); }; }
            have value == q;
            rewrite(value == q);
            solve() using { n == q * d + r; 0 <= r; };
        }
    }
    ensures n < (value + 1) * d by {
        if r < 0 {
            have value == q + -1;
            have value + 1 == q by { solve() using { value == q + -1; }; }
            rewrite(value + 1 == q);
            solve() using { n == q * d + r; r < 0; };
        } else {
            have 0 <= r by { solve() using { not (r < 0); }; }
            have value == q;
            apply(integer::multiply_add(q, 1, d));
            rewrite(value == q);
            rewrite((q + 1) * d == q * d + 1 * d);
            solve() using { n == q * d + r; r <= d - 1; };
        }
    }
}
```


### `integer::ceiling_from_remainder`

```click
theorem ceiling_from_remainder(n: Integer, d: Integer, q: Integer, r: Integer, value: Integer) {
    requires 0 < d;
    requires n == q * d + r;
    requires 1 - d <= r;
    requires r <= d - 1;
    requires 0 < r implies value == q + 1;
    requires r <= 0 implies value == q;
    ensures n <= value * d by {
        if 0 < r {
            have value == q + 1;
            apply(integer::multiply_add(q, 1, d));
            rewrite(value == q + 1);
            rewrite((q + 1) * d == q * d + 1 * d);
            solve() using { n == q * d + r; r <= d - 1; };
        } else {
            have r <= 0 by { solve() using { not (0 < r); }; }
            have value == q;
            rewrite(value == q);
            solve() using { n == q * d + r; r <= 0; };
        }
    }
    ensures (value + -1) * d < n by {
        if 0 < r {
            have value == q + 1;
            have value + -1 == q by { solve() using { value == q + 1; }; }
            rewrite(value + -1 == q);
            solve() using { n == q * d + r; 0 < r; };
        } else {
            have r <= 0 by { solve() using { not (0 < r); }; }
            have value == q;
            apply(integer::multiply_add(q, -1, d));
            rewrite(value == q);
            rewrite((q + -1) * d == q * d + -1 * d);
            solve() using { n == q * d + r; 1 - d <= r; };
        }
    }
}
```


### `integer::positive_divisor_quotient_lower`

```click
theorem positive_divisor_quotient_lower(n: Integer, d: Integer, bound: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires bound * d <= n;
    ensures bound <= truncating_quotient(n, d) by {
        arithmetic_certificate rules {
            premise 0: bound * d <= n => bound * d <= n;
            premise 1: 1 <= d => 1 <= d;
            integer_quotient_bound bounds [0, 1] => bound <= truncating_quotient(n, d);
            conclusion 0;
        }
    }
}
```


### `integer::positive_divisor_quotient_upper`

```click
theorem positive_divisor_quotient_upper(n: Integer, d: Integer, bound: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires n <= bound * d;
    ensures truncating_quotient(n, d) <= bound by {
        arithmetic_certificate rules {
            premise 0: n <= bound * d => n <= bound * d;
            premise 1: 1 <= d => 1 <= d;
            integer_quotient_bound bounds [0, 1] => truncating_quotient(n, d) <= bound;
            conclusion 0;
        }
    }
}
```


### `integer::positive_divisor_quotient_strict_lower`

```click
theorem positive_divisor_quotient_strict_lower(n: Integer, d: Integer, bound: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires bound < 0;
    requires bound * d < n;
    ensures bound < truncating_quotient(n, d) by {
        have bound * d <= n by { solve() using { bound * d < n; }; }
        apply(integer::positive_divisor_quotient_lower(n, d, bound));
        if bound < truncating_quotient(n, d) {
            assumption();
        } else {
            have truncating_quotient(n, d) == bound by { solve() using {
                bound <= truncating_quotient(n, d); not (bound < truncating_quotient(n, d));
            }; }
            if n <= 0 {
                have 0 < d by { solve() using { 1 <= d; }; }
                apply(integer::nonpositive_dividend_remainder(n, d));
                apply(integer::truncation_identity(n, d));
                have n == bound * d + truncating_remainder(n, d) by {
                    rewrite(bound == truncating_quotient(n, d));
                    assumption();
                }
                have not (bound * d < n) by { solve() using {
                    n == bound * d + truncating_remainder(n, d); truncating_remainder(n, d) <= 0;
                }; }
                contradiction(bound * d < n);
            } else {
                have 0 <= n by { solve() using { not (n <= 0); }; }
                have 0 * d <= n by { solve() using { 0 <= n; }; }
                apply(integer::positive_divisor_quotient_lower(n, d, 0));
                have not (bound < 0) by { solve() using {
                    0 <= truncating_quotient(n, d); truncating_quotient(n, d) == bound;
                }; }
                contradiction(bound < 0);
            }
        }
    }
}
```

### `integer::positive_divisor_quotient_strict_upper`

```click
theorem positive_divisor_quotient_strict_upper(n: Integer, d: Integer, bound: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires 0 < bound;
    requires n < bound * d;
    ensures truncating_quotient(n, d) < bound by {
        have n <= bound * d by { solve() using { n < bound * d; }; }
        apply(integer::positive_divisor_quotient_upper(n, d, bound));
        if truncating_quotient(n, d) < bound {
            assumption();
        } else {
            have truncating_quotient(n, d) == bound by { solve() using {
                truncating_quotient(n, d) <= bound; not (truncating_quotient(n, d) < bound);
            }; }
            if 0 <= n {
                have 0 < d by { solve() using { 1 <= d; }; }
                apply(integer::nonnegative_dividend_remainder(n, d));
                apply(integer::truncation_identity(n, d));
                have n == bound * d + truncating_remainder(n, d) by {
                    rewrite(bound == truncating_quotient(n, d));
                    assumption();
                }
                have not (n < bound * d) by { solve() using {
                    n == bound * d + truncating_remainder(n, d); 0 <= truncating_remainder(n, d);
                }; }
                contradiction(n < bound * d);
            } else {
                have n <= 0 by { solve() using { not (0 <= n); }; }
                have n <= 0 * d by { solve() using { n <= 0; }; }
                apply(integer::positive_divisor_quotient_upper(n, d, 0));
                have not (0 < bound) by { solve() using {
                    truncating_quotient(n, d) <= 0; truncating_quotient(n, d) == bound;
                }; }
                contradiction(0 < bound);
            }
        }
    }
}
```

### `integer::lower_correction_bound`

```click
theorem lower_correction_bound(n: Integer, d: Integer, q: Integer, r: Integer, lower: Integer) {
    requires lower <= q;
    requires lower * d <= n;
    requires n == q * d + r;
    requires r < 0;
    ensures lower + 1 <= q by {
        if lower + 1 <= q {
            assumption();
        } else {
            have q == lower by { solve() using { lower <= q; not (lower + 1 <= q); }; }
            have n == lower * d + r by {
                rewrite(lower == q);
                assumption();
            }
            have not (r < 0) by { solve() using { lower * d <= n; n == lower * d + r; }; }
            contradiction(r < 0);
        }
    }
}
```


### `integer::upper_correction_bound`

```click
theorem upper_correction_bound(n: Integer, d: Integer, q: Integer, r: Integer, upper: Integer) {
    requires q <= upper;
    requires n <= upper * d;
    requires n == q * d + r;
    requires 0 < r;
    ensures q <= upper + -1 by {
        if q <= upper + -1 {
            assumption();
        } else {
            have q == upper by { solve() using { q <= upper; not (q <= upper + -1); }; }
            have n == upper * d + r by {
                rewrite(upper == q);
                assumption();
            }
            have not (0 < r) by { solve() using { n <= upper * d; n == upper * d + r; }; }
            contradiction(0 < r);
        }
    }
}
```

### `integer::multiply_order_nonnegative`

```click
theorem multiply_order_nonnegative(a: Integer, b: Integer, factor: Integer) {
    requires a <= b;
    requires 0 <= factor;
    ensures a * factor <= b * factor by {
        arithmetic_certificate rules {
            premise 0: a <= b => a <= b;
            premise 1: 0 <= factor => 0 <= factor;
            integer_multiply_order bounds [0, 1] => a * factor <= b * factor;
            conclusion 0;
        }
    }
}
```

### `integer::multiply_order_nonpositive`

```click
theorem multiply_order_nonpositive(a: Integer, b: Integer, factor: Integer) {
    requires a <= b;
    requires factor <= 0;
    ensures b * factor <= a * factor by {
        arithmetic_certificate rules {
            premise 0: a <= b => a <= b;
            premise 1: factor <= 0 => factor <= 0;
            integer_multiply_order bounds [0, 1] => b * factor <= a * factor;
            conclusion 0;
        }
    }
}
```

### `integer::scaled_product_bounds`

```click
theorem scaled_product_bounds(value: Integer, amount: Integer, size: Integer, lower: Integer, upper: Integer) {
    requires lower <= value;
    requires value <= upper;
    requires lower <= 0;
    requires 0 <= upper;
    requires 0 <= amount;
    requires amount <= size;
    ensures lower * size <= value * amount by {
        apply(integer::multiply_order_nonnegative(lower, value, amount));
        have lower * size <= lower * amount by {
            arithmetic_certificate rules {
                premise 0: amount <= size => amount <= size;
                premise 1: lower <= 0 => lower <= 0;
                integer_multiply_order bounds [0, 1] => lower * size <= lower * amount;
                conclusion 0;
            }
        }
        solve() using { lower * size <= lower * amount; lower * amount <= value * amount; };
    }
    ensures value * amount <= upper * size by {
        apply(integer::multiply_order_nonnegative(value, upper, amount));
        have upper * amount <= upper * size by {
            arithmetic_certificate rules {
                premise 0: amount <= size => amount <= size;
                premise 1: 0 <= upper => 0 <= upper;
                integer_multiply_order bounds [0, 1] => upper * amount <= upper * size;
                conclusion 0;
            }
        }
        solve() using { value * amount <= upper * amount; upper * amount <= upper * size; };
    }
}
```

### `integer::int32_remainder_to_integer`

```click
theorem int32_remainder_to_integer(left: int32, right: int32) {
    requires defined(left % right);
    requires to_integer(right) != 0;
    ensures to_integer(left % right) == truncating_remainder(to_integer(left), to_integer(right));
}
```

Connects a defined signed machine remainder to mathematical truncation. Native definedness excludes both a zero divisor and `INT32_MIN % -1`; a nonzero mathematical divisor alone does not establish that the C operation is defined.

### `integer::uint32_from_le_bytes`

```click
theorem uint32_from_le_bytes(p: uint32*) {
    requires little_endian();
    views p[0..1];
    requires defined(p[0]);
    ensures p[0] ==
        (((p as (uint8 *))[0] as uint32) |
         ((p as (uint8 *))[1] as uint32) << 8u32 |
         ((p as (uint8 *))[2] as uint32) << 16u32 |
         ((p as (uint8 *))[3] as uint32) << 24u32);
}
```

Relates one readable unsigned 32-bit object to its four character representation
bytes at the same program point. `little_endian()` is a built-in target fact;
C proofs receive it only from a little-endian execution environment. Pure
theorems must state it as a premise. The rule does not grant read permission,
initialize memory, or reinterpret pointer representations. Its kernel
constructor constructs five reads and a fixed packing expression without
searching memory history. Applications retain the named lemma in expansion.

Checked use: [`integer_uint32_from_le_bytes_initialization.md`](https://github.com/clicklang/click/blob/master/mdtests/integer_uint32_from_le_bytes_initialization.md).

## `click::permutation`

Source: `library/permutation.click`, `import click::permutation;`.

### `permutation::count`

```click
function count<T>(p: T*, lo: int32, hi: int32, x: T) -> int32 {
    (lo..hi).fold(0, |acc, k| {
        acc + if p[k] == x { 1 } else { 0 }
    })
}
```

**Meaning:** Returns the number of elements equal to `x` in the half-open range `lo..hi` of the array reference `p`. It is generic over the element type: `T` is inferred from `p`, an `int32[]` or `uint8[]` array ref (a pure-function `T*` parameter is an array ref), and `x` must have that same type.

**Kind:** generic function. Parameter types, requirements, and guarantees are normative in the declaration above. The bounds stay `int32`, as `bytes::count`'s do.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate. [`mdtests/stdlib_permutation_count_over_bytes.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_permutation_count_over_bytes.md) counts a `uint8` buffer, [`mdtests/stdlib_permutation_count_over_bytes_rejects_overwrite.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_permutation_count_over_bytes_rejects_overwrite.md) refuses an overwrite as a byte permutation, and [`mdtests/stdlib_permutation_count_rejects_mixed_element_types.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_permutation_count_rejects_mixed_element_types.md) refuses an `int32` value counted in a `uint8` buffer.

### `permutation::permutation`

```click
predicate permutation(a: int32[], b: int32[], lo: int32, hi: int32) {
    forall (x: int32) {
        permutation::count(a, lo, hi, x) == permutation::count(b, lo, hi, x)
    }
}
```

**Meaning:** States that `a` and `b` contain every `int32` value the same number of times in `lo..hi`. Unfolding exposes equality of two `count` calls under a universal quantifier.

**Limit:** the predicate is stated over `int32[]` only. A generic form would quantify over its element type, `forall (x: T)`, and a quantifier's type must be a concrete C, `Integer` or algebraic type; the parser refuses a type parameter there. A permutation over another element type is a file predicate over the generic `permutation::count`, as `byte_permutation` in [`mdtests/stdlib_permutation_count_over_bytes.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_permutation_count_over_bytes.md) is.

**Kind:** predicate. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate. Use `unfold(permutation::permutation)` when a proof needs the predicate body.

## `click::bytes`

Source: `library/bytes.click`, `import click::bytes;`, or brought by `click::c::string`, in which case a sidecar without the import writes the full `click::bytes::` path.

### `bytes::count`

```click
function count(bytes: uint8[], lo: int32, hi: int32, value: uint8) -> int32 {
    (lo..hi).fold(0, |acc, k| {
        acc + if bytes[k] == value { 1 } else { 0 }
    })
}
```

**Meaning:** Returns the number of bytes equal to `value` in the half-open range `lo..hi`.

**Kind:** function. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `bytes::equal`

```click
predicate equal(left: uint8[], left_lo: uint64, right: uint8[], right_lo: uint64, len: uint64) {
    (0u64..len).all(|k| {
        left[left_lo + k] == right[right_lo + k]
    })
}
```

**Meaning:** States that the `len` bytes starting at `left_lo` and `right_lo` are pairwise equal. Offsets and lengths are `size_t` values.

**Kind:** predicate. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate. Use `unfold(bytes::equal)` when a proof needs the predicate body.

### `bytes::equal_range`

```click
predicate equal_range(left: uint8[], right: uint8[], lo: uint64, hi: uint64) {
    (lo..hi).all(|k| {
        left[k] == right[k]
    })
}
```

**Meaning:** States that `left` and `right` are pairwise equal throughout the same half-open range `lo..hi`.

**Kind:** predicate. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate. Use `unfold(bytes::equal_range)` when a proof needs the predicate body.

### `bytes::all_equal`

```click
predicate all_equal(bytes: uint8[], lo: uint64, hi: uint64, value: uint8) {
    (lo..hi).all(|k| {
        bytes[k] == value
    })
}
```

**Meaning:** States that every byte in `lo..hi` equals `value`.

**Kind:** predicate. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate. Use `unfold(bytes::all_equal)` when a proof needs the predicate body.

### `bytes::contains`

```click
predicate contains(bytes: uint8[], lo: uint64, hi: uint64, value: uint8) {
    (lo..hi).any(|k| {
        bytes[k] == value
    })
}
```

**Meaning:** States that at least one byte in `lo..hi` equals `value`.

**Kind:** predicate. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate. Use `unfold(bytes::contains)` when a proof needs the predicate body.

### `bytes::all_not_equal`

```click
predicate all_not_equal(bytes: uint8[], lo: uint64, hi: uint64, value: uint8) {
    (lo..hi).all(|k| {
        bytes[k] != value
    })
}
```

**Meaning:** States that every byte in `lo..hi` differs from `value`.

**Kind:** predicate. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate. Use `unfold(bytes::all_not_equal)` when a proof needs the predicate body.

## `click::cstr`

Source: `library/cstr.click`, `import click::cstr;`, or brought by `click::c::string`.

### `cstr::prefix`

```click
predicate prefix(bytes: uint8[], len: uint64) {
    forall (k: uint64) { k < len implies bytes[k] != '\0' }
}
```

**Meaning:** States that the first `len` bytes contain no null terminator.

**Kind:** predicate. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate. Use `unfold(cstr::prefix)` when a proof needs the predicate body.

### `cstr::len`

```click
predicate len(bytes: uint8[], len: uint64) {
    len < 18446744073709551615u64 and
        viewable(bytes[0..len + 1u64]) and
        cstr::prefix(bytes, len) and
        bytes[len] == '\0'
}
```

**Meaning:** States that `len` is a `size_t` length below `SIZE_MAX`, the
complete prefix through its terminator is readable, the preceding bytes contain
no null terminator, and byte `len` is a null terminator.

**Kind:** predicate. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate. Use `unfold(cstr::len)` when a proof needs the predicate body.

### `cstr::cstr`

```click
predicate cstr(bytes: uint8[]) {
    exists (len: uint64) {
        cstr::len(bytes, len)
    }
}
```

**Meaning:** States that the byte array has some exact specification-level C-string length.

**Kind:** predicate. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate. Use `unfold(cstr::cstr)` when a proof needs the predicate body.

### `cstr::readable_len`

```click
predicate readable_len(bytes: uint8[], len: uint64) {
    len < 18446744073709551615u64 and
        viewable(bytes[0..len + 1u64]) and
        forall (k: uint64) { k < len implies bytes[k] != '\0' } and
        bytes[len] == '\0' and
        forall (k: uint64) { to_integer(k) < to_integer(len + 1u64) implies defined(bytes[k]) }
}
```

**Meaning:** States that `len` is a `size_t` C-string length below
`SIZE_MAX`, the complete prefix through its terminator is dynamically viewable,
the prefix has no embedded terminator, and every byte through the null
terminator is defined.

**Kind:** predicate. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate. Use `unfold(cstr::readable_len)` when a proof needs the predicate body.

### `cstr::readable_len_unique`

```click
theorem readable_len_unique(bytes: uint8[], left: uint64, right: uint64) {
    requires forall (k: uint64) { k < left implies bytes[k] != '\0' };
    requires bytes[left] == '\0';
    requires forall (k: uint64) { k < right implies bytes[k] != '\0' };
    requires bytes[right] == '\0';

    ensures left == right by {
        have left < right or not (left < right) by {
            if left < right {
                assumption();
            } else {
                assumption();
            }
        }
        cases {
            left < right => {
                instantiate(forall (k: uint64) { k < right implies bytes[k] != '\0' }, left)
                    using { left < right; };
                contradiction(bytes[left] == '\0');
            }
            not (left < right) => {
                have right < left or not (right < left) by {
                    if right < left {
                        assumption();
                    } else {
                        assumption();
                    }
                }
                cases {
                    right < left => {
                        instantiate(forall (k: uint64) { k < left implies bytes[k] != '\0' }, right)
                            using { right < left; };
                        contradiction(bytes[right] == '\0');
                    }
                    not (right < left) => {
                        have left <= right by {
                            solve();
                        }
                        solve();
                    }
                }
            }
        }
    }
}
```

**Meaning:** Proves that two `size_t` lengths with the same null-free prefix
condition and null terminator for one byte array are equal. It is a pure
content theorem; it does not grant viewability or read/write permission.

**Kind:** theorem. The proof is checked as part of the standard-library
definition and its requirements and guarantee are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `cstr::readable`

```click
predicate readable(bytes: uint8[]) {
    exists (len: uint64) {
        len < 18446744073709551615u64 and
            viewable(bytes[0..len + 1u64]) and
            forall (k: uint64) { k < len implies bytes[k] != '\0' } and
            bytes[len] == '\0' and
            forall (k: uint64) { to_integer(k) < to_integer(len + 1u64) implies defined(bytes[k]) }
    }
}
```

**Meaning:** States that the byte array has some dynamically viewable,
null-terminated C-string prefix. The length remains existential; unfold the
predicate when a proof needs to expose that witness. A caller can pass the same
unchanged plain-`char` or signed-character pointer to a callee requiring this predicate:
contract expansion retains the predicate's unsigned byte reads. The caller
must supply the requirement; it does not cover an offset pointer or survive
an arbitrary write to the string. See
[`cstr_plain_char_caller_requirement_reaches_callee.md`](https://github.com/clicklang/click/blob/master/mdtests/cstr_plain_char_caller_requirement_reaches_callee.md).

**Kind:** predicate. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate. Use `unfold(cstr::readable)` when a proof needs the predicate body.

### `cstr_at`

```click
resource cstr_at(p: const uint8*, len: uint64) {
    owns p[0..len + 1u64];
    fact len < 18446744073709551615u64;
    fact forall (k: uint64) { 0u64 <= k and k < len implies p[k] != '\0' };
    fact p[len] == '\0';
    fact forall (k: uint64) { 0u64 <= k and to_integer(k) < to_integer(len + 1u64) implies defined(p[k]) };
}
```

**Meaning:** A C string: the `len + 1` bytes of `p` through its first
terminator, with the facts that make them the C string of length `len`. The
body owns the bytes, and a contract chooses how it holds them. `views
cstr_at(p, len);` borrows the string read-only: the callee cannot write it,
and an opened view exposes the bytes as views. `owns cstr_at(p, len);` holds
it exclusively and returns the same instance, so `len` is unchanged at exit.
A function that changes the length, such as one that writes an earlier
terminator, states `consumes cstr_at(p, len);` and `produces` the new
instance with the bytes it no longer covers. The bytes determine `len`, so
`fold(cstr_at(p, m))` at any other length fails. An owner lends its instance
to a callee that views it, and a caller that owns the bytes and holds the
facts but no instance has the call assemble the view; the caller keeps its
bytes. `open(cstr_at(p, len)) { ... }` exposes the body and the facts. A
`char`, `signed char`, or `unsigned char` pointer may be passed for `p`, as
for the C-string predicates; a signed character pointer is read through its
byte view `p as (uint8 *)`.

**Kind:** composite resource. Parameter types, memory clause, and facts are normative in the declaration above.

**Verified use:** [`cstr_at_view_passes_through_a_call.md`](https://github.com/clicklang/click/blob/master/mdtests/cstr_at_view_passes_through_a_call.md),
[`cstr_at_opens_and_lends_a_prefix_to_a_copy.md`](https://github.com/clicklang/click/blob/master/mdtests/cstr_at_opens_and_lends_a_prefix_to_a_copy.md),
[`cstr_at_fold_refuses_a_wrong_length.md`](https://github.com/clicklang/click/blob/master/mdtests/cstr_at_fold_refuses_a_wrong_length.md),
[`cstr_at_viewed_string_cannot_be_written.md`](https://github.com/clicklang/click/blob/master/mdtests/cstr_at_viewed_string_cannot_be_written.md),
[`cstr_at_owner_rewrites_a_byte_and_refolds_the_same_length.md`](https://github.com/clicklang/click/blob/master/mdtests/cstr_at_owner_rewrites_a_byte_and_refolds_the_same_length.md),
[`cstr_at_owns_clause_cannot_shorten_the_string.md`](https://github.com/clicklang/click/blob/master/mdtests/cstr_at_owns_clause_cannot_shorten_the_string.md),
[`cstr_at_consumes_and_produces_a_shorter_string.md`](https://github.com/clicklang/click/blob/master/mdtests/cstr_at_consumes_and_produces_a_shorter_string.md),
[`cstr_at_owner_lends_its_string_to_a_viewing_callee.md`](https://github.com/clicklang/click/blob/master/mdtests/cstr_at_owner_lends_its_string_to_a_viewing_callee.md),
[`cstr_at_call_assembles_a_view_from_owned_bytes.md`](https://github.com/clicklang/click/blob/master/mdtests/cstr_at_call_assembles_a_view_from_owned_bytes.md),
and, through character pointers,
[`cstr_at_borrows_a_char_string_from_the_library.md`](https://github.com/clicklang/click/blob/master/mdtests/cstr_at_borrows_a_char_string_from_the_library.md).

### `cstr::bounded`

```click
predicate bounded(bytes: uint8[], max: uint64) {
    exists (k: uint64) { k < max and bytes[k] == '\0' }
}
```

**Meaning:** States that a null terminator occurs before the exclusive bound `max`.

**Kind:** predicate. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate. Use `unfold(cstr::bounded)` when a proof needs the predicate body.

### `cstr::len_is_viewable`

```click
theorem len_is_viewable(bytes: uint8[], len: uint64) {
    requires cstr::len(bytes, len);

    ensures viewable(bytes[0..len + 1u64]) by {
        unfold(cstr::len);
        solve();
    }
}
```

**Meaning:** Given an exact C-string length, exposes the viewability of the
prefix and its terminator as a separate fact for a subsequent proof step.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/cstr_viewable_witness.md`](https://github.com/clicklang/click/blob/master/mdtests/cstr_viewable_witness.md) checks this witness projection.

### `cstr::len_has_prefix`

```click
theorem len_has_prefix(bytes: uint8[], len: uint64) {
    requires cstr::len(bytes, len);

    ensures cstr::prefix(bytes, len) by {
        unfold(cstr::len);
        solve();
    }
}
```

**Meaning:** Given its listed requirements, proves `cstr::prefix(bytes, len)`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `cstr::len_has_terminator`

```click
theorem len_has_terminator(bytes: uint8[], len: uint64) {
    requires cstr::len(bytes, len);

    ensures bytes[len] == '\0' by {
        unfold(cstr::len);
        solve();
    }
}
```

**Meaning:** Given its listed requirements, proves `bytes[len] == '\0'`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

## `click::format`

Source: `library/format.click`, `import click::format;`. The C front end's `snprintf` contracts name it by path.

### Decimal formatting

`click::format` states the characters C's `printf` family writes for an
integer. The C front end writes the contract of each `snprintf` call with a
string-literal format with these functions
([formatted output](../language/c.md#formatted-output)). The theorems
`format::decimal_length_n` and `format::pow10_e` evaluate them for the
32-bit values `%u` and `%d` convert.

### `format::pow10`

```click
function pow10(e: uint64) -> uint64 {
    (if e == 0u64 { 1u64 } else { 0u64 }) + (if e == 1u64 { 10u64 } else { 0u64 }) + (if e == 2u64 { 100u64 } else { 0u64 }) + (if e == 3u64 { 1000u64 } else { 0u64 }) + (if e == 4u64 { 10000u64 } else { 0u64 }) + (if e == 5u64 { 100000u64 } else { 0u64 }) + (if e == 6u64 { 1000000u64 } else { 0u64 }) + (if e == 7u64 { 10000000u64 } else { 0u64 }) + (if e == 8u64 { 100000000u64 } else { 0u64 }) + (if e == 9u64 { 1000000000u64 } else { 0u64 }) + (if e == 10u64 { 10000000000u64 } else { 0u64 }) + (if e == 11u64 { 100000000000u64 } else { 0u64 }) + (if e == 12u64 { 1000000000000u64 } else { 0u64 }) + (if e == 13u64 { 10000000000000u64 } else { 0u64 }) + (if e == 14u64 { 100000000000000u64 } else { 0u64 }) + (if e == 15u64 { 1000000000000000u64 } else { 0u64 }) + (if e == 16u64 { 10000000000000000u64 } else { 0u64 }) + (if e == 17u64 { 100000000000000000u64 } else { 0u64 }) + (if e == 18u64 { 1000000000000000000u64 } else { 0u64 }) + (if e == 19u64 { 10000000000000000000u64 } else { 0u64 })
}
```

**Meaning:** `10` to the power `e` for `e < 20`, the exponents a 64-bit value's digits use.

**Kind:** function. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate. Use `unfold(format::pow10)` when a proof needs the function body.

### `format::decimal_length`

```click
function decimal_length(v: uint64) -> uint64 {
    1u64 + (if v < 10u64 { 0u64 } else { 1u64 }) + (if v < 100u64 { 0u64 } else { 1u64 }) + (if v < 1000u64 { 0u64 } else { 1u64 }) + (if v < 10000u64 { 0u64 } else { 1u64 }) + (if v < 100000u64 { 0u64 } else { 1u64 }) + (if v < 1000000u64 { 0u64 } else { 1u64 }) + (if v < 10000000u64 { 0u64 } else { 1u64 }) + (if v < 100000000u64 { 0u64 } else { 1u64 }) + (if v < 1000000000u64 { 0u64 } else { 1u64 }) + (if v < 10000000000u64 { 0u64 } else { 1u64 }) + (if v < 100000000000u64 { 0u64 } else { 1u64 }) + (if v < 1000000000000u64 { 0u64 } else { 1u64 }) + (if v < 10000000000000u64 { 0u64 } else { 1u64 }) + (if v < 100000000000000u64 { 0u64 } else { 1u64 }) + (if v < 1000000000000000u64 { 0u64 } else { 1u64 }) + (if v < 10000000000000000u64 { 0u64 } else { 1u64 }) + (if v < 100000000000000000u64 { 0u64 } else { 1u64 }) + (if v < 1000000000000000000u64 { 0u64 } else { 1u64 }) + (if v < 10000000000000000000u64 { 0u64 } else { 1u64 })
}
```

**Meaning:** The number of decimal digits `printf` writes for `v`: one for `v < 10`, so zero has one digit.

**Kind:** function. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate. Use `unfold(format::decimal_length)` when a proof needs the function body.

### `format::decimal_digit`

```click
function decimal_digit(v: uint64, k: uint64) -> uint8 {
    if k < format::decimal_length(v) {
        (48u64 + v / format::pow10(format::decimal_length(v) - 1u64 - k) % 10u64) as uint8
    } else {
        48u8
    }
}
```

**Meaning:** The ASCII character of `v`'s `k`th decimal digit, counting from the most significant. Past the last digit, at `k >= format::decimal_length(v)`, it is `'0'` (`48u8`), so the function is total. Unfolding it owes nothing: specification `/` and `%` are total, so the digit's division by `format::pow10(...)` needs no nonzero premise.

**Kind:** function. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate. Use `unfold(format::decimal_digit)` when a proof needs the function body.

### `format::padded_length`

```click
function padded_length(v: uint64, width: uint64) -> uint64 {
    if format::decimal_length(v) < width { width } else { format::decimal_length(v) }
}
```

**Meaning:** The characters `%Nu` writes for `v` in a field of width `N`: the field width, or `v`'s digits when they are wider.

**Kind:** function. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate. Use `unfold(format::padded_length)` when a proof needs the function body.

### `format::padded_digit`

```click
function padded_digit(v: uint64, width: uint64, pad: uint8, k: uint64) -> uint8 {
    if to_integer(k) < to_integer(format::padded_length(v, width) - format::decimal_length(v)) {
        pad
    } else {
        format::decimal_digit(v, k - (format::padded_length(v, width) - format::decimal_length(v)))
    }
}
```

**Meaning:** The `k`th character of `v` in a field of `width`: `pad` (`'0'` for a `0` flag, `' '` otherwise) before the digits.

**Kind:** function. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate. Use `unfold(format::padded_digit)` when a proof needs the function body.

### `format::magnitude`

```click
function magnitude(v: int32) -> uint64 {
    if v < 0 { (0i64 - v as int64) as uint64 } else { v as uint64 }
}
```

**Meaning:** The magnitude of an `int`, exact even for `INT_MIN`.

**Kind:** function. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate. Use `unfold(format::magnitude)` when a proof needs the function body.

### `format::signed_length`

```click
function signed_length(v: int32) -> uint64 {
    if v < 0 { 1u64 + format::decimal_length(format::magnitude(v)) } else { format::decimal_length(format::magnitude(v)) }
}
```

**Meaning:** The number of characters `%d` writes for `v`: its digits, after a `-` when it is negative.

**Kind:** function. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate. Use `unfold(format::signed_length)` when a proof needs the function body.

### `format::signed_digit`

```click
function signed_digit(v: int32, k: uint64) -> uint8 {
    if v < 0 {
        if k == 0u64 { 45u8 } else { format::decimal_digit(format::magnitude(v), k - 1u64) }
    } else {
        format::decimal_digit(format::magnitude(v), k)
    }
}
```

**Meaning:** The `k`th character `%d` writes for `v`: a `-` first when it is negative, then the digits of its magnitude.

**Kind:** function. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate. Use `unfold(format::signed_digit)` when a proof needs the function body.

### `format::pow10_0`

```click
theorem pow10_0() {
    ensures format::pow10(0u64) == 1u64 by {
        unfold(format::pow10(0u64));
        solve();
    }
}
```

**Meaning:** Evaluates `format::pow10` at `0`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `format::pow10_1`

```click
theorem pow10_1() {
    ensures format::pow10(1u64) == 10u64 by {
        unfold(format::pow10(1u64));
        solve();
    }
}
```

**Meaning:** Evaluates `format::pow10` at `1`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `format::pow10_2`

```click
theorem pow10_2() {
    ensures format::pow10(2u64) == 100u64 by {
        unfold(format::pow10(2u64));
        solve();
    }
}
```

**Meaning:** Evaluates `format::pow10` at `2`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `format::pow10_3`

```click
theorem pow10_3() {
    ensures format::pow10(3u64) == 1000u64 by {
        unfold(format::pow10(3u64));
        solve();
    }
}
```

**Meaning:** Evaluates `format::pow10` at `3`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `format::pow10_4`

```click
theorem pow10_4() {
    ensures format::pow10(4u64) == 10000u64 by {
        unfold(format::pow10(4u64));
        solve();
    }
}
```

**Meaning:** Evaluates `format::pow10` at `4`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `format::pow10_5`

```click
theorem pow10_5() {
    ensures format::pow10(5u64) == 100000u64 by {
        unfold(format::pow10(5u64));
        solve();
    }
}
```

**Meaning:** Evaluates `format::pow10` at `5`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `format::pow10_6`

```click
theorem pow10_6() {
    ensures format::pow10(6u64) == 1000000u64 by {
        unfold(format::pow10(6u64));
        solve();
    }
}
```

**Meaning:** Evaluates `format::pow10` at `6`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `format::pow10_7`

```click
theorem pow10_7() {
    ensures format::pow10(7u64) == 10000000u64 by {
        unfold(format::pow10(7u64));
        solve();
    }
}
```

**Meaning:** Evaluates `format::pow10` at `7`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `format::pow10_8`

```click
theorem pow10_8() {
    ensures format::pow10(8u64) == 100000000u64 by {
        unfold(format::pow10(8u64));
        solve();
    }
}
```

**Meaning:** Evaluates `format::pow10` at `8`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `format::pow10_9`

```click
theorem pow10_9() {
    ensures format::pow10(9u64) == 1000000000u64 by {
        unfold(format::pow10(9u64));
        solve();
    }
}
```

**Meaning:** Evaluates `format::pow10` at `9`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `format::pow10_nonzero`

```click
theorem pow10_nonzero(e: uint64) {
    requires e < 20u64;
    ensures format::pow10(e) != 0u64 by {
        unfold(format::pow10(e));
        if e == 19u64 {
            normalize() using { e == 19u64; };
        } else {
            have e < 19u64 by { solve() using { e < 20u64; not (e == 19u64); }; }
            if e == 18u64 {
                normalize() using { e == 18u64; };
            } else {
                have e < 18u64 by { solve() using { e < 19u64; not (e == 18u64); }; }
                if e == 17u64 {
                    normalize() using { e == 17u64; };
                } else {
                    have e < 17u64 by { solve() using { e < 18u64; not (e == 17u64); }; }
                    if e == 16u64 {
                        normalize() using { e == 16u64; };
                    } else {
                        have e < 16u64 by { solve() using { e < 17u64; not (e == 16u64); }; }
                        if e == 15u64 {
                            normalize() using { e == 15u64; };
                        } else {
                            have e < 15u64 by { solve() using { e < 16u64; not (e == 15u64); }; }
                            if e == 14u64 {
                                normalize() using { e == 14u64; };
                            } else {
                                have e < 14u64 by { solve() using { e < 15u64; not (e == 14u64); }; }
                                if e == 13u64 {
                                    normalize() using { e == 13u64; };
                                } else {
                                    have e < 13u64 by { solve() using { e < 14u64; not (e == 13u64); }; }
                                    if e == 12u64 {
                                        normalize() using { e == 12u64; };
                                    } else {
                                        have e < 12u64 by { solve() using { e < 13u64; not (e == 12u64); }; }
                                        if e == 11u64 {
                                            normalize() using { e == 11u64; };
                                        } else {
                                            have e < 11u64 by { solve() using { e < 12u64; not (e == 11u64); }; }
                                            if e == 10u64 {
                                                normalize() using { e == 10u64; };
                                            } else {
                                                have e < 10u64 by { solve() using { e < 11u64; not (e == 10u64); }; }
                                                if e == 9u64 {
                                                    normalize() using { e == 9u64; };
                                                } else {
                                                    have e < 9u64 by { solve() using { e < 10u64; not (e == 9u64); }; }
                                                    if e == 8u64 {
                                                        normalize() using { e == 8u64; };
                                                    } else {
                                                        have e < 8u64 by { solve() using { e < 9u64; not (e == 8u64); }; }
                                                        if e == 7u64 {
                                                            normalize() using { e == 7u64; };
                                                        } else {
                                                            have e < 7u64 by { solve() using { e < 8u64; not (e == 7u64); }; }
                                                            if e == 6u64 {
                                                                normalize() using { e == 6u64; };
                                                            } else {
                                                                have e < 6u64 by { solve() using { e < 7u64; not (e == 6u64); }; }
                                                                if e == 5u64 {
                                                                    normalize() using { e == 5u64; };
                                                                } else {
                                                                    have e < 5u64 by { solve() using { e < 6u64; not (e == 5u64); }; }
                                                                    if e == 4u64 {
                                                                        normalize() using { e == 4u64; };
                                                                    } else {
                                                                        have e < 4u64 by { solve() using { e < 5u64; not (e == 4u64); }; }
                                                                        if e == 3u64 {
                                                                            normalize() using { e == 3u64; };
                                                                        } else {
                                                                            have e < 3u64 by { solve() using { e < 4u64; not (e == 3u64); }; }
                                                                            if e == 2u64 {
                                                                                normalize() using { e == 2u64; };
                                                                            } else {
                                                                                have e < 2u64 by { solve() using { e < 3u64; not (e == 2u64); }; }
                                                                                if e == 1u64 {
                                                                                    normalize() using { e == 1u64; };
                                                                                } else {
                                                                                    have e < 1u64 by { solve() using { e < 2u64; not (e == 1u64); }; }
                                                                                    have e == 0u64 by { solve() using { e < 1u64; }; }
                                                                                    normalize() using { e == 0u64; };
                                                                                }
                                                                            }
                                                                        }
                                                                    }
                                                                }
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}
```

**Meaning:** Every exponent below 20, the exponents of a 64-bit value's digits, has a nonzero power of ten.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `format::decimal_length_1`

```click
theorem decimal_length_1(v: uint64) {
    requires v < 10u64;
    ensures format::decimal_length(v) == 1u64 by {
        have v < 10u64 by { solve(); }
        have v < 100u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10u64, 100u64)); }
        have v < 1000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10u64, 1000u64)); }
        have v < 10000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10u64, 10000u64)); }
        have v < 100000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10u64, 100000u64)); }
        have v < 1000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10u64, 1000000u64)); }
        have v < 10000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10u64, 10000000u64)); }
        have v < 100000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10u64, 100000000u64)); }
        have v < 1000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10u64, 1000000000u64)); }
        have v < 10000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10u64, 10000000000u64)); }
        have v < 100000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10u64, 100000000000u64)); }
        have v < 1000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10u64, 1000000000000u64)); }
        have v < 10000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10u64, 10000000000000u64)); }
        have v < 100000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10u64, 100000000000000u64)); }
        have v < 1000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10u64, 1000000000000000u64)); }
        have v < 10000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10u64, 10000000000000000u64)); }
        have v < 100000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10u64, 100000000000000000u64)); }
        have v < 1000000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10u64, 1000000000000000000u64)); }
        have v < 10000000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10u64, 10000000000000000000u64)); }
        unfold(format::decimal_length(v));
        have (if v < 10u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 10u64; }; }
        rewrite((if v < 10u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 100u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 100u64; }; }
        rewrite((if v < 100u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 1000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 1000u64; }; }
        rewrite((if v < 1000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 10000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 10000u64; }; }
        rewrite((if v < 10000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 100000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 100000u64; }; }
        rewrite((if v < 100000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 1000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 1000000u64; }; }
        rewrite((if v < 1000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 10000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 10000000u64; }; }
        rewrite((if v < 10000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 100000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 100000000u64; }; }
        rewrite((if v < 100000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 1000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 1000000000u64; }; }
        rewrite((if v < 1000000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 10000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 10000000000u64; }; }
        rewrite((if v < 10000000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 100000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 100000000000u64; }; }
        rewrite((if v < 100000000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 1000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 1000000000000u64; }; }
        rewrite((if v < 1000000000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 10000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 10000000000000u64; }; }
        rewrite((if v < 10000000000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 100000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 100000000000000u64; }; }
        rewrite((if v < 100000000000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 1000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 1000000000000000u64; }; }
        rewrite((if v < 1000000000000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 10000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 10000000000000000u64; }; }
        rewrite((if v < 10000000000000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 100000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 100000000000000000u64; }; }
        rewrite((if v < 100000000000000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 1000000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 1000000000000000000u64; }; }
        rewrite((if v < 1000000000000000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 10000000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 10000000000000000000u64; }; }
        rewrite((if v < 10000000000000000000u64 { 0u64 } else { 1u64 }) == 0u64);
        normalize();
    }
}
```

**Meaning:** A value with 1 decimal digit has `format::decimal_length` 1.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `format::decimal_length_2`

```click
theorem decimal_length_2(v: uint64) {
    requires 10u64 <= v;
    requires v < 100u64;
    ensures format::decimal_length(v) == 2u64 by {
        have not (v < 10u64) by { solve(); }
        have v < 100u64 by { solve(); }
        have v < 1000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100u64, 1000u64)); }
        have v < 10000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100u64, 10000u64)); }
        have v < 100000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100u64, 100000u64)); }
        have v < 1000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100u64, 1000000u64)); }
        have v < 10000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100u64, 10000000u64)); }
        have v < 100000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100u64, 100000000u64)); }
        have v < 1000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100u64, 1000000000u64)); }
        have v < 10000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100u64, 10000000000u64)); }
        have v < 100000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100u64, 100000000000u64)); }
        have v < 1000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100u64, 1000000000000u64)); }
        have v < 10000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100u64, 10000000000000u64)); }
        have v < 100000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100u64, 100000000000000u64)); }
        have v < 1000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100u64, 1000000000000000u64)); }
        have v < 10000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100u64, 10000000000000000u64)); }
        have v < 100000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100u64, 100000000000000000u64)); }
        have v < 1000000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100u64, 1000000000000000000u64)); }
        have v < 10000000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100u64, 10000000000000000000u64)); }
        unfold(format::decimal_length(v));
        have (if v < 10u64 { 0u64 } else { 1u64 }) == 1u64 by { solve() using { not (v < 10u64); }; }
        rewrite((if v < 10u64 { 0u64 } else { 1u64 }) == 1u64);
        have (if v < 100u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 100u64; }; }
        rewrite((if v < 100u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 1000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 1000u64; }; }
        rewrite((if v < 1000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 10000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 10000u64; }; }
        rewrite((if v < 10000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 100000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 100000u64; }; }
        rewrite((if v < 100000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 1000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 1000000u64; }; }
        rewrite((if v < 1000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 10000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 10000000u64; }; }
        rewrite((if v < 10000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 100000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 100000000u64; }; }
        rewrite((if v < 100000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 1000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 1000000000u64; }; }
        rewrite((if v < 1000000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 10000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 10000000000u64; }; }
        rewrite((if v < 10000000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 100000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 100000000000u64; }; }
        rewrite((if v < 100000000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 1000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 1000000000000u64; }; }
        rewrite((if v < 1000000000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 10000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 10000000000000u64; }; }
        rewrite((if v < 10000000000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 100000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 100000000000000u64; }; }
        rewrite((if v < 100000000000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 1000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 1000000000000000u64; }; }
        rewrite((if v < 1000000000000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 10000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 10000000000000000u64; }; }
        rewrite((if v < 10000000000000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 100000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 100000000000000000u64; }; }
        rewrite((if v < 100000000000000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 1000000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 1000000000000000000u64; }; }
        rewrite((if v < 1000000000000000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 10000000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 10000000000000000000u64; }; }
        rewrite((if v < 10000000000000000000u64 { 0u64 } else { 1u64 }) == 0u64);
        normalize();
    }
}
```

**Meaning:** A value with 2 decimal digits has `format::decimal_length` 2.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `format::decimal_length_3`

```click
theorem decimal_length_3(v: uint64) {
    requires 100u64 <= v;
    requires v < 1000u64;
    ensures format::decimal_length(v) == 3u64 by {
        have not (v < 10u64) by { apply(integer::uint64_less_equal_transitive(10u64, 100u64, v)); }
        have not (v < 100u64) by { solve(); }
        have v < 1000u64 by { solve(); }
        have v < 10000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000u64, 10000u64)); }
        have v < 100000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000u64, 100000u64)); }
        have v < 1000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000u64, 1000000u64)); }
        have v < 10000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000u64, 10000000u64)); }
        have v < 100000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000u64, 100000000u64)); }
        have v < 1000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000u64, 1000000000u64)); }
        have v < 10000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000u64, 10000000000u64)); }
        have v < 100000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000u64, 100000000000u64)); }
        have v < 1000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000u64, 1000000000000u64)); }
        have v < 10000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000u64, 10000000000000u64)); }
        have v < 100000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000u64, 100000000000000u64)); }
        have v < 1000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000u64, 1000000000000000u64)); }
        have v < 10000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000u64, 10000000000000000u64)); }
        have v < 100000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000u64, 100000000000000000u64)); }
        have v < 1000000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000u64, 1000000000000000000u64)); }
        have v < 10000000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000u64, 10000000000000000000u64)); }
        unfold(format::decimal_length(v));
        have (if v < 10u64 { 0u64 } else { 1u64 }) == 1u64 by { solve() using { not (v < 10u64); }; }
        rewrite((if v < 10u64 { 0u64 } else { 1u64 }) == 1u64);
        have (if v < 100u64 { 0u64 } else { 1u64 }) == 1u64 by { solve() using { not (v < 100u64); }; }
        rewrite((if v < 100u64 { 0u64 } else { 1u64 }) == 1u64);
        have (if v < 1000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 1000u64; }; }
        rewrite((if v < 1000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 10000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 10000u64; }; }
        rewrite((if v < 10000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 100000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 100000u64; }; }
        rewrite((if v < 100000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 1000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 1000000u64; }; }
        rewrite((if v < 1000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 10000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 10000000u64; }; }
        rewrite((if v < 10000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 100000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 100000000u64; }; }
        rewrite((if v < 100000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 1000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 1000000000u64; }; }
        rewrite((if v < 1000000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 10000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 10000000000u64; }; }
        rewrite((if v < 10000000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 100000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 100000000000u64; }; }
        rewrite((if v < 100000000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 1000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 1000000000000u64; }; }
        rewrite((if v < 1000000000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 10000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 10000000000000u64; }; }
        rewrite((if v < 10000000000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 100000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 100000000000000u64; }; }
        rewrite((if v < 100000000000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 1000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 1000000000000000u64; }; }
        rewrite((if v < 1000000000000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 10000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 10000000000000000u64; }; }
        rewrite((if v < 10000000000000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 100000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 100000000000000000u64; }; }
        rewrite((if v < 100000000000000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 1000000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 1000000000000000000u64; }; }
        rewrite((if v < 1000000000000000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 10000000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 10000000000000000000u64; }; }
        rewrite((if v < 10000000000000000000u64 { 0u64 } else { 1u64 }) == 0u64);
        normalize();
    }
}
```

**Meaning:** A value with 3 decimal digits has `format::decimal_length` 3.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `format::decimal_length_4`

```click
theorem decimal_length_4(v: uint64) {
    requires 1000u64 <= v;
    requires v < 10000u64;
    ensures format::decimal_length(v) == 4u64 by {
        have not (v < 10u64) by { apply(integer::uint64_less_equal_transitive(10u64, 1000u64, v)); }
        have not (v < 100u64) by { apply(integer::uint64_less_equal_transitive(100u64, 1000u64, v)); }
        have not (v < 1000u64) by { solve(); }
        have v < 10000u64 by { solve(); }
        have v < 100000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10000u64, 100000u64)); }
        have v < 1000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10000u64, 1000000u64)); }
        have v < 10000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10000u64, 10000000u64)); }
        have v < 100000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10000u64, 100000000u64)); }
        have v < 1000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10000u64, 1000000000u64)); }
        have v < 10000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10000u64, 10000000000u64)); }
        have v < 100000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10000u64, 100000000000u64)); }
        have v < 1000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10000u64, 1000000000000u64)); }
        have v < 10000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10000u64, 10000000000000u64)); }
        have v < 100000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10000u64, 100000000000000u64)); }
        have v < 1000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10000u64, 1000000000000000u64)); }
        have v < 10000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10000u64, 10000000000000000u64)); }
        have v < 100000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10000u64, 100000000000000000u64)); }
        have v < 1000000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10000u64, 1000000000000000000u64)); }
        have v < 10000000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10000u64, 10000000000000000000u64)); }
        unfold(format::decimal_length(v));
        have (if v < 10u64 { 0u64 } else { 1u64 }) == 1u64 by { solve() using { not (v < 10u64); }; }
        rewrite((if v < 10u64 { 0u64 } else { 1u64 }) == 1u64);
        have (if v < 100u64 { 0u64 } else { 1u64 }) == 1u64 by { solve() using { not (v < 100u64); }; }
        rewrite((if v < 100u64 { 0u64 } else { 1u64 }) == 1u64);
        have (if v < 1000u64 { 0u64 } else { 1u64 }) == 1u64 by { solve() using { not (v < 1000u64); }; }
        rewrite((if v < 1000u64 { 0u64 } else { 1u64 }) == 1u64);
        have (if v < 10000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 10000u64; }; }
        rewrite((if v < 10000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 100000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 100000u64; }; }
        rewrite((if v < 100000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 1000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 1000000u64; }; }
        rewrite((if v < 1000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 10000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 10000000u64; }; }
        rewrite((if v < 10000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 100000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 100000000u64; }; }
        rewrite((if v < 100000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 1000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 1000000000u64; }; }
        rewrite((if v < 1000000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 10000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 10000000000u64; }; }
        rewrite((if v < 10000000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 100000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 100000000000u64; }; }
        rewrite((if v < 100000000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 1000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 1000000000000u64; }; }
        rewrite((if v < 1000000000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 10000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 10000000000000u64; }; }
        rewrite((if v < 10000000000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 100000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 100000000000000u64; }; }
        rewrite((if v < 100000000000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 1000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 1000000000000000u64; }; }
        rewrite((if v < 1000000000000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 10000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 10000000000000000u64; }; }
        rewrite((if v < 10000000000000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 100000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 100000000000000000u64; }; }
        rewrite((if v < 100000000000000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 1000000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 1000000000000000000u64; }; }
        rewrite((if v < 1000000000000000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 10000000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 10000000000000000000u64; }; }
        rewrite((if v < 10000000000000000000u64 { 0u64 } else { 1u64 }) == 0u64);
        normalize();
    }
}
```

**Meaning:** A value with 4 decimal digits has `format::decimal_length` 4.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `format::decimal_length_5`

```click
theorem decimal_length_5(v: uint64) {
    requires 10000u64 <= v;
    requires v < 100000u64;
    ensures format::decimal_length(v) == 5u64 by {
        have not (v < 10u64) by { apply(integer::uint64_less_equal_transitive(10u64, 10000u64, v)); }
        have not (v < 100u64) by { apply(integer::uint64_less_equal_transitive(100u64, 10000u64, v)); }
        have not (v < 1000u64) by { apply(integer::uint64_less_equal_transitive(1000u64, 10000u64, v)); }
        have not (v < 10000u64) by { solve(); }
        have v < 100000u64 by { solve(); }
        have v < 1000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100000u64, 1000000u64)); }
        have v < 10000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100000u64, 10000000u64)); }
        have v < 100000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100000u64, 100000000u64)); }
        have v < 1000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100000u64, 1000000000u64)); }
        have v < 10000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100000u64, 10000000000u64)); }
        have v < 100000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100000u64, 100000000000u64)); }
        have v < 1000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100000u64, 1000000000000u64)); }
        have v < 10000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100000u64, 10000000000000u64)); }
        have v < 100000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100000u64, 100000000000000u64)); }
        have v < 1000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100000u64, 1000000000000000u64)); }
        have v < 10000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100000u64, 10000000000000000u64)); }
        have v < 100000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100000u64, 100000000000000000u64)); }
        have v < 1000000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100000u64, 1000000000000000000u64)); }
        have v < 10000000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100000u64, 10000000000000000000u64)); }
        unfold(format::decimal_length(v));
        have (if v < 10u64 { 0u64 } else { 1u64 }) == 1u64 by { solve() using { not (v < 10u64); }; }
        rewrite((if v < 10u64 { 0u64 } else { 1u64 }) == 1u64);
        have (if v < 100u64 { 0u64 } else { 1u64 }) == 1u64 by { solve() using { not (v < 100u64); }; }
        rewrite((if v < 100u64 { 0u64 } else { 1u64 }) == 1u64);
        have (if v < 1000u64 { 0u64 } else { 1u64 }) == 1u64 by { solve() using { not (v < 1000u64); }; }
        rewrite((if v < 1000u64 { 0u64 } else { 1u64 }) == 1u64);
        have (if v < 10000u64 { 0u64 } else { 1u64 }) == 1u64 by { solve() using { not (v < 10000u64); }; }
        rewrite((if v < 10000u64 { 0u64 } else { 1u64 }) == 1u64);
        have (if v < 100000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 100000u64; }; }
        rewrite((if v < 100000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 1000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 1000000u64; }; }
        rewrite((if v < 1000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 10000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 10000000u64; }; }
        rewrite((if v < 10000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 100000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 100000000u64; }; }
        rewrite((if v < 100000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 1000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 1000000000u64; }; }
        rewrite((if v < 1000000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 10000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 10000000000u64; }; }
        rewrite((if v < 10000000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 100000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 100000000000u64; }; }
        rewrite((if v < 100000000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 1000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 1000000000000u64; }; }
        rewrite((if v < 1000000000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 10000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 10000000000000u64; }; }
        rewrite((if v < 10000000000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 100000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 100000000000000u64; }; }
        rewrite((if v < 100000000000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 1000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 1000000000000000u64; }; }
        rewrite((if v < 1000000000000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 10000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 10000000000000000u64; }; }
        rewrite((if v < 10000000000000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 100000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 100000000000000000u64; }; }
        rewrite((if v < 100000000000000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 1000000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 1000000000000000000u64; }; }
        rewrite((if v < 1000000000000000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 10000000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 10000000000000000000u64; }; }
        rewrite((if v < 10000000000000000000u64 { 0u64 } else { 1u64 }) == 0u64);
        normalize();
    }
}
```

**Meaning:** A value with 5 decimal digits has `format::decimal_length` 5.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `format::decimal_length_6`

```click
theorem decimal_length_6(v: uint64) {
    requires 100000u64 <= v;
    requires v < 1000000u64;
    ensures format::decimal_length(v) == 6u64 by {
        have not (v < 10u64) by { apply(integer::uint64_less_equal_transitive(10u64, 100000u64, v)); }
        have not (v < 100u64) by { apply(integer::uint64_less_equal_transitive(100u64, 100000u64, v)); }
        have not (v < 1000u64) by { apply(integer::uint64_less_equal_transitive(1000u64, 100000u64, v)); }
        have not (v < 10000u64) by { apply(integer::uint64_less_equal_transitive(10000u64, 100000u64, v)); }
        have not (v < 100000u64) by { solve(); }
        have v < 1000000u64 by { solve(); }
        have v < 10000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000000u64, 10000000u64)); }
        have v < 100000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000000u64, 100000000u64)); }
        have v < 1000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000000u64, 1000000000u64)); }
        have v < 10000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000000u64, 10000000000u64)); }
        have v < 100000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000000u64, 100000000000u64)); }
        have v < 1000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000000u64, 1000000000000u64)); }
        have v < 10000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000000u64, 10000000000000u64)); }
        have v < 100000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000000u64, 100000000000000u64)); }
        have v < 1000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000000u64, 1000000000000000u64)); }
        have v < 10000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000000u64, 10000000000000000u64)); }
        have v < 100000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000000u64, 100000000000000000u64)); }
        have v < 1000000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000000u64, 1000000000000000000u64)); }
        have v < 10000000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000000u64, 10000000000000000000u64)); }
        unfold(format::decimal_length(v));
        have (if v < 10u64 { 0u64 } else { 1u64 }) == 1u64 by { solve() using { not (v < 10u64); }; }
        rewrite((if v < 10u64 { 0u64 } else { 1u64 }) == 1u64);
        have (if v < 100u64 { 0u64 } else { 1u64 }) == 1u64 by { solve() using { not (v < 100u64); }; }
        rewrite((if v < 100u64 { 0u64 } else { 1u64 }) == 1u64);
        have (if v < 1000u64 { 0u64 } else { 1u64 }) == 1u64 by { solve() using { not (v < 1000u64); }; }
        rewrite((if v < 1000u64 { 0u64 } else { 1u64 }) == 1u64);
        have (if v < 10000u64 { 0u64 } else { 1u64 }) == 1u64 by { solve() using { not (v < 10000u64); }; }
        rewrite((if v < 10000u64 { 0u64 } else { 1u64 }) == 1u64);
        have (if v < 100000u64 { 0u64 } else { 1u64 }) == 1u64 by { solve() using { not (v < 100000u64); }; }
        rewrite((if v < 100000u64 { 0u64 } else { 1u64 }) == 1u64);
        have (if v < 1000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 1000000u64; }; }
        rewrite((if v < 1000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 10000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 10000000u64; }; }
        rewrite((if v < 10000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 100000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 100000000u64; }; }
        rewrite((if v < 100000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 1000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 1000000000u64; }; }
        rewrite((if v < 1000000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 10000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 10000000000u64; }; }
        rewrite((if v < 10000000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 100000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 100000000000u64; }; }
        rewrite((if v < 100000000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 1000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 1000000000000u64; }; }
        rewrite((if v < 1000000000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 10000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 10000000000000u64; }; }
        rewrite((if v < 10000000000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 100000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 100000000000000u64; }; }
        rewrite((if v < 100000000000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 1000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 1000000000000000u64; }; }
        rewrite((if v < 1000000000000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 10000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 10000000000000000u64; }; }
        rewrite((if v < 10000000000000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 100000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 100000000000000000u64; }; }
        rewrite((if v < 100000000000000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 1000000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 1000000000000000000u64; }; }
        rewrite((if v < 1000000000000000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 10000000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 10000000000000000000u64; }; }
        rewrite((if v < 10000000000000000000u64 { 0u64 } else { 1u64 }) == 0u64);
        normalize();
    }
}
```

**Meaning:** A value with 6 decimal digits has `format::decimal_length` 6.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `format::decimal_length_7`

```click
theorem decimal_length_7(v: uint64) {
    requires 1000000u64 <= v;
    requires v < 10000000u64;
    ensures format::decimal_length(v) == 7u64 by {
        have not (v < 10u64) by { apply(integer::uint64_less_equal_transitive(10u64, 1000000u64, v)); }
        have not (v < 100u64) by { apply(integer::uint64_less_equal_transitive(100u64, 1000000u64, v)); }
        have not (v < 1000u64) by { apply(integer::uint64_less_equal_transitive(1000u64, 1000000u64, v)); }
        have not (v < 10000u64) by { apply(integer::uint64_less_equal_transitive(10000u64, 1000000u64, v)); }
        have not (v < 100000u64) by { apply(integer::uint64_less_equal_transitive(100000u64, 1000000u64, v)); }
        have not (v < 1000000u64) by { solve(); }
        have v < 10000000u64 by { solve(); }
        have v < 100000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10000000u64, 100000000u64)); }
        have v < 1000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10000000u64, 1000000000u64)); }
        have v < 10000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10000000u64, 10000000000u64)); }
        have v < 100000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10000000u64, 100000000000u64)); }
        have v < 1000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10000000u64, 1000000000000u64)); }
        have v < 10000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10000000u64, 10000000000000u64)); }
        have v < 100000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10000000u64, 100000000000000u64)); }
        have v < 1000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10000000u64, 1000000000000000u64)); }
        have v < 10000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10000000u64, 10000000000000000u64)); }
        have v < 100000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10000000u64, 100000000000000000u64)); }
        have v < 1000000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10000000u64, 1000000000000000000u64)); }
        have v < 10000000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10000000u64, 10000000000000000000u64)); }
        unfold(format::decimal_length(v));
        have (if v < 10u64 { 0u64 } else { 1u64 }) == 1u64 by { solve() using { not (v < 10u64); }; }
        rewrite((if v < 10u64 { 0u64 } else { 1u64 }) == 1u64);
        have (if v < 100u64 { 0u64 } else { 1u64 }) == 1u64 by { solve() using { not (v < 100u64); }; }
        rewrite((if v < 100u64 { 0u64 } else { 1u64 }) == 1u64);
        have (if v < 1000u64 { 0u64 } else { 1u64 }) == 1u64 by { solve() using { not (v < 1000u64); }; }
        rewrite((if v < 1000u64 { 0u64 } else { 1u64 }) == 1u64);
        have (if v < 10000u64 { 0u64 } else { 1u64 }) == 1u64 by { solve() using { not (v < 10000u64); }; }
        rewrite((if v < 10000u64 { 0u64 } else { 1u64 }) == 1u64);
        have (if v < 100000u64 { 0u64 } else { 1u64 }) == 1u64 by { solve() using { not (v < 100000u64); }; }
        rewrite((if v < 100000u64 { 0u64 } else { 1u64 }) == 1u64);
        have (if v < 1000000u64 { 0u64 } else { 1u64 }) == 1u64 by { solve() using { not (v < 1000000u64); }; }
        rewrite((if v < 1000000u64 { 0u64 } else { 1u64 }) == 1u64);
        have (if v < 10000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 10000000u64; }; }
        rewrite((if v < 10000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 100000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 100000000u64; }; }
        rewrite((if v < 100000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 1000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 1000000000u64; }; }
        rewrite((if v < 1000000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 10000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 10000000000u64; }; }
        rewrite((if v < 10000000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 100000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 100000000000u64; }; }
        rewrite((if v < 100000000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 1000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 1000000000000u64; }; }
        rewrite((if v < 1000000000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 10000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 10000000000000u64; }; }
        rewrite((if v < 10000000000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 100000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 100000000000000u64; }; }
        rewrite((if v < 100000000000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 1000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 1000000000000000u64; }; }
        rewrite((if v < 1000000000000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 10000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 10000000000000000u64; }; }
        rewrite((if v < 10000000000000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 100000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 100000000000000000u64; }; }
        rewrite((if v < 100000000000000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 1000000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 1000000000000000000u64; }; }
        rewrite((if v < 1000000000000000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 10000000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 10000000000000000000u64; }; }
        rewrite((if v < 10000000000000000000u64 { 0u64 } else { 1u64 }) == 0u64);
        normalize();
    }
}
```

**Meaning:** A value with 7 decimal digits has `format::decimal_length` 7.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `format::decimal_length_8`

```click
theorem decimal_length_8(v: uint64) {
    requires 10000000u64 <= v;
    requires v < 100000000u64;
    ensures format::decimal_length(v) == 8u64 by {
        have not (v < 10u64) by { apply(integer::uint64_less_equal_transitive(10u64, 10000000u64, v)); }
        have not (v < 100u64) by { apply(integer::uint64_less_equal_transitive(100u64, 10000000u64, v)); }
        have not (v < 1000u64) by { apply(integer::uint64_less_equal_transitive(1000u64, 10000000u64, v)); }
        have not (v < 10000u64) by { apply(integer::uint64_less_equal_transitive(10000u64, 10000000u64, v)); }
        have not (v < 100000u64) by { apply(integer::uint64_less_equal_transitive(100000u64, 10000000u64, v)); }
        have not (v < 1000000u64) by { apply(integer::uint64_less_equal_transitive(1000000u64, 10000000u64, v)); }
        have not (v < 10000000u64) by { solve(); }
        have v < 100000000u64 by { solve(); }
        have v < 1000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100000000u64, 1000000000u64)); }
        have v < 10000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100000000u64, 10000000000u64)); }
        have v < 100000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100000000u64, 100000000000u64)); }
        have v < 1000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100000000u64, 1000000000000u64)); }
        have v < 10000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100000000u64, 10000000000000u64)); }
        have v < 100000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100000000u64, 100000000000000u64)); }
        have v < 1000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100000000u64, 1000000000000000u64)); }
        have v < 10000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100000000u64, 10000000000000000u64)); }
        have v < 100000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100000000u64, 100000000000000000u64)); }
        have v < 1000000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100000000u64, 1000000000000000000u64)); }
        have v < 10000000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 100000000u64, 10000000000000000000u64)); }
        unfold(format::decimal_length(v));
        have (if v < 10u64 { 0u64 } else { 1u64 }) == 1u64 by { solve() using { not (v < 10u64); }; }
        rewrite((if v < 10u64 { 0u64 } else { 1u64 }) == 1u64);
        have (if v < 100u64 { 0u64 } else { 1u64 }) == 1u64 by { solve() using { not (v < 100u64); }; }
        rewrite((if v < 100u64 { 0u64 } else { 1u64 }) == 1u64);
        have (if v < 1000u64 { 0u64 } else { 1u64 }) == 1u64 by { solve() using { not (v < 1000u64); }; }
        rewrite((if v < 1000u64 { 0u64 } else { 1u64 }) == 1u64);
        have (if v < 10000u64 { 0u64 } else { 1u64 }) == 1u64 by { solve() using { not (v < 10000u64); }; }
        rewrite((if v < 10000u64 { 0u64 } else { 1u64 }) == 1u64);
        have (if v < 100000u64 { 0u64 } else { 1u64 }) == 1u64 by { solve() using { not (v < 100000u64); }; }
        rewrite((if v < 100000u64 { 0u64 } else { 1u64 }) == 1u64);
        have (if v < 1000000u64 { 0u64 } else { 1u64 }) == 1u64 by { solve() using { not (v < 1000000u64); }; }
        rewrite((if v < 1000000u64 { 0u64 } else { 1u64 }) == 1u64);
        have (if v < 10000000u64 { 0u64 } else { 1u64 }) == 1u64 by { solve() using { not (v < 10000000u64); }; }
        rewrite((if v < 10000000u64 { 0u64 } else { 1u64 }) == 1u64);
        have (if v < 100000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 100000000u64; }; }
        rewrite((if v < 100000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 1000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 1000000000u64; }; }
        rewrite((if v < 1000000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 10000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 10000000000u64; }; }
        rewrite((if v < 10000000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 100000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 100000000000u64; }; }
        rewrite((if v < 100000000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 1000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 1000000000000u64; }; }
        rewrite((if v < 1000000000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 10000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 10000000000000u64; }; }
        rewrite((if v < 10000000000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 100000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 100000000000000u64; }; }
        rewrite((if v < 100000000000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 1000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 1000000000000000u64; }; }
        rewrite((if v < 1000000000000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 10000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 10000000000000000u64; }; }
        rewrite((if v < 10000000000000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 100000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 100000000000000000u64; }; }
        rewrite((if v < 100000000000000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 1000000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 1000000000000000000u64; }; }
        rewrite((if v < 1000000000000000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 10000000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 10000000000000000000u64; }; }
        rewrite((if v < 10000000000000000000u64 { 0u64 } else { 1u64 }) == 0u64);
        normalize();
    }
}
```

**Meaning:** A value with 8 decimal digits has `format::decimal_length` 8.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `format::decimal_length_9`

```click
theorem decimal_length_9(v: uint64) {
    requires 100000000u64 <= v;
    requires v < 1000000000u64;
    ensures format::decimal_length(v) == 9u64 by {
        have not (v < 10u64) by { apply(integer::uint64_less_equal_transitive(10u64, 100000000u64, v)); }
        have not (v < 100u64) by { apply(integer::uint64_less_equal_transitive(100u64, 100000000u64, v)); }
        have not (v < 1000u64) by { apply(integer::uint64_less_equal_transitive(1000u64, 100000000u64, v)); }
        have not (v < 10000u64) by { apply(integer::uint64_less_equal_transitive(10000u64, 100000000u64, v)); }
        have not (v < 100000u64) by { apply(integer::uint64_less_equal_transitive(100000u64, 100000000u64, v)); }
        have not (v < 1000000u64) by { apply(integer::uint64_less_equal_transitive(1000000u64, 100000000u64, v)); }
        have not (v < 10000000u64) by { apply(integer::uint64_less_equal_transitive(10000000u64, 100000000u64, v)); }
        have not (v < 100000000u64) by { solve(); }
        have v < 1000000000u64 by { solve(); }
        have v < 10000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000000000u64, 10000000000u64)); }
        have v < 100000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000000000u64, 100000000000u64)); }
        have v < 1000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000000000u64, 1000000000000u64)); }
        have v < 10000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000000000u64, 10000000000000u64)); }
        have v < 100000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000000000u64, 100000000000000u64)); }
        have v < 1000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000000000u64, 1000000000000000u64)); }
        have v < 10000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000000000u64, 10000000000000000u64)); }
        have v < 100000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000000000u64, 100000000000000000u64)); }
        have v < 1000000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000000000u64, 1000000000000000000u64)); }
        have v < 10000000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 1000000000u64, 10000000000000000000u64)); }
        unfold(format::decimal_length(v));
        have (if v < 10u64 { 0u64 } else { 1u64 }) == 1u64 by { solve() using { not (v < 10u64); }; }
        rewrite((if v < 10u64 { 0u64 } else { 1u64 }) == 1u64);
        have (if v < 100u64 { 0u64 } else { 1u64 }) == 1u64 by { solve() using { not (v < 100u64); }; }
        rewrite((if v < 100u64 { 0u64 } else { 1u64 }) == 1u64);
        have (if v < 1000u64 { 0u64 } else { 1u64 }) == 1u64 by { solve() using { not (v < 1000u64); }; }
        rewrite((if v < 1000u64 { 0u64 } else { 1u64 }) == 1u64);
        have (if v < 10000u64 { 0u64 } else { 1u64 }) == 1u64 by { solve() using { not (v < 10000u64); }; }
        rewrite((if v < 10000u64 { 0u64 } else { 1u64 }) == 1u64);
        have (if v < 100000u64 { 0u64 } else { 1u64 }) == 1u64 by { solve() using { not (v < 100000u64); }; }
        rewrite((if v < 100000u64 { 0u64 } else { 1u64 }) == 1u64);
        have (if v < 1000000u64 { 0u64 } else { 1u64 }) == 1u64 by { solve() using { not (v < 1000000u64); }; }
        rewrite((if v < 1000000u64 { 0u64 } else { 1u64 }) == 1u64);
        have (if v < 10000000u64 { 0u64 } else { 1u64 }) == 1u64 by { solve() using { not (v < 10000000u64); }; }
        rewrite((if v < 10000000u64 { 0u64 } else { 1u64 }) == 1u64);
        have (if v < 100000000u64 { 0u64 } else { 1u64 }) == 1u64 by { solve() using { not (v < 100000000u64); }; }
        rewrite((if v < 100000000u64 { 0u64 } else { 1u64 }) == 1u64);
        have (if v < 1000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 1000000000u64; }; }
        rewrite((if v < 1000000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 10000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 10000000000u64; }; }
        rewrite((if v < 10000000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 100000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 100000000000u64; }; }
        rewrite((if v < 100000000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 1000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 1000000000000u64; }; }
        rewrite((if v < 1000000000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 10000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 10000000000000u64; }; }
        rewrite((if v < 10000000000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 100000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 100000000000000u64; }; }
        rewrite((if v < 100000000000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 1000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 1000000000000000u64; }; }
        rewrite((if v < 1000000000000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 10000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 10000000000000000u64; }; }
        rewrite((if v < 10000000000000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 100000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 100000000000000000u64; }; }
        rewrite((if v < 100000000000000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 1000000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 1000000000000000000u64; }; }
        rewrite((if v < 1000000000000000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 10000000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 10000000000000000000u64; }; }
        rewrite((if v < 10000000000000000000u64 { 0u64 } else { 1u64 }) == 0u64);
        normalize();
    }
}
```

**Meaning:** A value with 9 decimal digits has `format::decimal_length` 9.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `format::decimal_length_10`

```click
theorem decimal_length_10(v: uint64) {
    requires 1000000000u64 <= v;
    requires v < 10000000000u64;
    ensures format::decimal_length(v) == 10u64 by {
        have not (v < 10u64) by { apply(integer::uint64_less_equal_transitive(10u64, 1000000000u64, v)); }
        have not (v < 100u64) by { apply(integer::uint64_less_equal_transitive(100u64, 1000000000u64, v)); }
        have not (v < 1000u64) by { apply(integer::uint64_less_equal_transitive(1000u64, 1000000000u64, v)); }
        have not (v < 10000u64) by { apply(integer::uint64_less_equal_transitive(10000u64, 1000000000u64, v)); }
        have not (v < 100000u64) by { apply(integer::uint64_less_equal_transitive(100000u64, 1000000000u64, v)); }
        have not (v < 1000000u64) by { apply(integer::uint64_less_equal_transitive(1000000u64, 1000000000u64, v)); }
        have not (v < 10000000u64) by { apply(integer::uint64_less_equal_transitive(10000000u64, 1000000000u64, v)); }
        have not (v < 100000000u64) by { apply(integer::uint64_less_equal_transitive(100000000u64, 1000000000u64, v)); }
        have not (v < 1000000000u64) by { solve(); }
        have v < 10000000000u64 by { solve(); }
        have v < 100000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10000000000u64, 100000000000u64)); }
        have v < 1000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10000000000u64, 1000000000000u64)); }
        have v < 10000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10000000000u64, 10000000000000u64)); }
        have v < 100000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10000000000u64, 100000000000000u64)); }
        have v < 1000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10000000000u64, 1000000000000000u64)); }
        have v < 10000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10000000000u64, 10000000000000000u64)); }
        have v < 100000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10000000000u64, 100000000000000000u64)); }
        have v < 1000000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10000000000u64, 1000000000000000000u64)); }
        have v < 10000000000000000000u64 by { apply(integer::uint64_less_than_less_equal_transitive(v, 10000000000u64, 10000000000000000000u64)); }
        unfold(format::decimal_length(v));
        have (if v < 10u64 { 0u64 } else { 1u64 }) == 1u64 by { solve() using { not (v < 10u64); }; }
        rewrite((if v < 10u64 { 0u64 } else { 1u64 }) == 1u64);
        have (if v < 100u64 { 0u64 } else { 1u64 }) == 1u64 by { solve() using { not (v < 100u64); }; }
        rewrite((if v < 100u64 { 0u64 } else { 1u64 }) == 1u64);
        have (if v < 1000u64 { 0u64 } else { 1u64 }) == 1u64 by { solve() using { not (v < 1000u64); }; }
        rewrite((if v < 1000u64 { 0u64 } else { 1u64 }) == 1u64);
        have (if v < 10000u64 { 0u64 } else { 1u64 }) == 1u64 by { solve() using { not (v < 10000u64); }; }
        rewrite((if v < 10000u64 { 0u64 } else { 1u64 }) == 1u64);
        have (if v < 100000u64 { 0u64 } else { 1u64 }) == 1u64 by { solve() using { not (v < 100000u64); }; }
        rewrite((if v < 100000u64 { 0u64 } else { 1u64 }) == 1u64);
        have (if v < 1000000u64 { 0u64 } else { 1u64 }) == 1u64 by { solve() using { not (v < 1000000u64); }; }
        rewrite((if v < 1000000u64 { 0u64 } else { 1u64 }) == 1u64);
        have (if v < 10000000u64 { 0u64 } else { 1u64 }) == 1u64 by { solve() using { not (v < 10000000u64); }; }
        rewrite((if v < 10000000u64 { 0u64 } else { 1u64 }) == 1u64);
        have (if v < 100000000u64 { 0u64 } else { 1u64 }) == 1u64 by { solve() using { not (v < 100000000u64); }; }
        rewrite((if v < 100000000u64 { 0u64 } else { 1u64 }) == 1u64);
        have (if v < 1000000000u64 { 0u64 } else { 1u64 }) == 1u64 by { solve() using { not (v < 1000000000u64); }; }
        rewrite((if v < 1000000000u64 { 0u64 } else { 1u64 }) == 1u64);
        have (if v < 10000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 10000000000u64; }; }
        rewrite((if v < 10000000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 100000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 100000000000u64; }; }
        rewrite((if v < 100000000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 1000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 1000000000000u64; }; }
        rewrite((if v < 1000000000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 10000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 10000000000000u64; }; }
        rewrite((if v < 10000000000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 100000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 100000000000000u64; }; }
        rewrite((if v < 100000000000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 1000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 1000000000000000u64; }; }
        rewrite((if v < 1000000000000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 10000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 10000000000000000u64; }; }
        rewrite((if v < 10000000000000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 100000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 100000000000000000u64; }; }
        rewrite((if v < 100000000000000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 1000000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 1000000000000000000u64; }; }
        rewrite((if v < 1000000000000000000u64 { 0u64 } else { 1u64 }) == 0u64);
        have (if v < 10000000000000000000u64 { 0u64 } else { 1u64 }) == 0u64 by { solve() using { v < 10000000000000000000u64; }; }
        rewrite((if v < 10000000000000000000u64 { 0u64 } else { 1u64 }) == 0u64);
        normalize();
    }
}
```

**Meaning:** A value with 10 decimal digits has `format::decimal_length` 10.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `format::decimal_digit_power_nonzero`

```click
theorem decimal_digit_power_nonzero(v: uint64, k: uint64) {
    requires k < format::decimal_length(v);
    ensures format::pow10(format::decimal_length(v) - 1u64 - k) != 0u64 by {
        have format::decimal_length(v) <= 20u64 by {
            unfold(format::decimal_length(v));
            solve();
        }
        have (format::decimal_length(v) - 1u64 - k) as uint64 < 20u64 by { solve(); }
        apply(format::pow10_nonzero(format::decimal_length(v) - 1u64 - k));
    }
}
```

**Meaning:** Where `k` names one of `v`'s digits, the power of ten that selects it is nonzero, so the digit's division by it is an ordinary quotient rather than the opaque quotient by zero.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `format::decimal_digit_of_length`

```click
theorem decimal_digit_of_length(v: uint64, n: uint64, k: uint64) {
    requires format::decimal_length(v) == n;
    requires k < n;
    ensures format::decimal_digit(v, k) == (48u64 + v / format::pow10(n - 1u64 - k) % 10u64) as uint8 by {
        unfold(format::decimal_digit(v, k));
        rewrite(format::decimal_length(v) == n);
        normalize() using { k < n; };
    }
}
```

**Meaning:** Rewrites digit `k < n` of a value whose length is known to be `n` to `48 + v / 10^(n-1-k) % 10`. For known `n` and `k`, `format::pow10_e` gives the value of the power `format::pow10(n - 1u64 - k)` it divides by.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `format::decimal_digit_lower_bound`

```click
theorem decimal_digit_lower_bound(v: uint64, k: uint64) {
    ensures 48u8 <= format::decimal_digit(v, k) by {
        if k < format::decimal_length(v) {
            apply(format::decimal_digit_power_nonzero(v, k));
            unfold(format::decimal_digit(v, k));
            have 48u8 <= (48u64 + v / format::pow10(format::decimal_length(v) - 1u64 - k) % 10u64) as uint8;
            normalize() using { k < format::decimal_length(v); };
            assumption();
        } else {
            unfold(format::decimal_digit(v, k));
            normalize() using { not (k < format::decimal_length(v)); };
        }
    }
}```

**Meaning:** Every decimal digit is a character from `'0'` up, so none is the terminator `0`.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

### `format::padded_digit_lower_bound`

```click
theorem padded_digit_lower_bound(v: uint64, width: uint64, k: uint64) {
    ensures 48u8 <= format::padded_digit(v, width, 48u8, k) by {
        unfold(format::padded_digit(v, width, 48u8, k));
        if to_integer(k) < to_integer(format::padded_length(v, width) - format::decimal_length(v)) {
            normalize() using { to_integer(k) < to_integer(format::padded_length(v, width) - format::decimal_length(v)); };
        } else {
            apply(format::decimal_digit_lower_bound(v, k - (format::padded_length(v, width) - format::decimal_length(v))));
            solve() using { not (to_integer(k) < to_integer(format::padded_length(v, width) - format::decimal_length(v))); 48u8 <= format::decimal_digit(v, k - (format::padded_length(v, width) - format::decimal_length(v))); };
        }
    }
}```

**Meaning:** Every character of a `0`-padded field is a digit or the `'0'` pad, so none is the terminator; this is what a `%s` of a `%03u` fraction needs.

**Kind:** theorem. Parameter types, requirements, and guarantees are normative in the declaration above.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md) exercises this symbol and is checked by the ordinary mdtest gate.

## `click::c::string`

Source: `library/c/string.click`, a C library model: it comes with a C declaration of, or call to, one of its functions, not with an import.

### External C contracts

These declarations cover the narrow byte-oriented libc slice supported by Click.
They are body-less assumptions: callers must satisfy their requirements, and
Click does not verify an implementation of the external function.

### `memcpy`

```click
extern uint8* memcpy(uint8 destination[], const uint8 source[], uint64 bytes) {
    views source[0..bytes];
    owns uninitialized(destination[0..bytes]);
    ensures result == destination;
    ensures bytes::equal(destination, 0u64, old(source), 0u64, bytes);
}
```

**Meaning:** Copies `bytes` bytes, a `size_t` count as in C, from a viewed source to
an owned destination and returns the destination pointer. The caller lends
the source for the call from bytes it views or owns. The `owns` and `views`
clauses of one contract are disjoint, so a call whose source overlaps its
destination is refused
([`mdtests/byte_representation_overlapping_copy_rejected.md`](https://github.com/clicklang/click/blob/master/mdtests/byte_representation_overlapping_copy_rejected.md)),
and `viewable` alone, which grants no read authority, does not lend the
source
([`mdtests/memcpy_source_needs_a_covering_resource.md`](https://github.com/clicklang/click/blob/master/mdtests/memcpy_source_needs_a_covering_resource.md)). This exact
standard-library declaration also carries the checked representation-copy
effect: after the call, each initialized typed cell whose complete byte
representation lies in the copied range is established at the mapped
destination offset. A source cell the copy would split, a symbolic range, an
unaligned destination, and an untyped source establish no typed value. The
effect is bound to this declaration, not to the name `memcpy`.

**Kind:** external C contract. The declaration is an explicit verification assumption.

**Verified use:** [`mdtests/byte_representation_scalar_copy.md`](https://github.com/clicklang/click/blob/master/mdtests/byte_representation_scalar_copy.md) checks its typed-copy effect, and [`mdtests/memcpy_reads_a_viewed_or_borrowed_source.md`](https://github.com/clicklang/click/blob/master/mdtests/memcpy_reads_a_viewed_or_borrowed_source.md) copies from a viewed source and from an owned one lent for the call.

### `memcmp`

```click
extern int32 memcmp(const uint8 left[], const uint8 right[], uint64 bytes) {
    views left[0..bytes];
    views right[0..bytes];
    requires forall (k: uint64) { k < bytes implies defined(left[k]) and defined(right[k]) };
    ensures result == 0 implies bytes::equal(left, 0u64, right, 0u64, bytes);
    ensures result != 0 implies not bytes::equal(left, 0u64, right, 0u64, bytes);
}
```

**Meaning:** Reads both `bytes`-long byte ranges (a `size_t` count, as in C) under views, without mutation, and distinguishes equal
from unequal prefixes by whether the result is zero. Views are shared, so
one viewed or owned range can be both operands.

**Kind:** external C contract. The declaration is an explicit verification assumption.

**Verified use:** [`mdtests/strlen_of_an_empty_string_and_memcmp_use_the_catalog_contracts.md`](https://github.com/clicklang/click/blob/master/mdtests/strlen_of_an_empty_string_and_memcmp_use_the_catalog_contracts.md) checks its range and definedness preconditions at a call, and [`mdtests/memcmp_reads_two_viewed_buffers.md`](https://github.com/clicklang/click/blob/master/mdtests/memcmp_reads_two_viewed_buffers.md) compares two viewed buffers and one buffer with itself.

### `memset`

```click
extern uint8* memset(uint8 destination[], int32 value, uint64 bytes) {
    requires 0 <= value;
    requires value <= 255;
    owns uninitialized(destination[0..bytes]);
    ensures result == destination;
    ensures (0u64..bytes).all(|k| {
        defined(destination[k]) and destination[k] == value
    });
}
```

**Meaning:** Fills `bytes` bytes (a `size_t` count, as in C) of an owned
destination with a value Click can represent as `unsigned char`, and returns the
destination pointer. C converts any `int` fill value to `unsigned char`; Click
models that narrowing only for a representable value, so the contract requires
one.

**Kind:** external C contract. The declaration is an explicit verification assumption.

**Verified use:** [`mdtests/c_builtin_memset_header_checks_its_contract.md`](https://github.com/clicklang/click/blob/master/mdtests/c_builtin_memset_header_checks_its_contract.md) refuses a call whose fill value is outside its precondition's range.

### `strlen`

```click
extern uint64 strlen(const uint8* bytes) {
    let n: uint64;
    views cstr_at(bytes, n);
    ensures result == n;
}
```

**Meaning:** Returns the `size_t` length of the C string `cstr_at(bytes, n)`
the caller holds, without mutation, as C's `strlen` does. The value
parameter `n` is the length, which the C signature does not carry. A call
takes it from the one held `cstr_at` at `bytes` (`views`, `owns`, or an
owner lending it), or from a call map, `{ n: k }`, whose string the call
assembles from owned bytes and the string's facts when the caller holds
none. The string's facts (the length is
below `SIZE_MAX`, no earlier terminator, the terminator at `len`, every byte
defined) come with the instance, so the result points at its terminator.
`cstr::readable` alone grants no resource and does not satisfy the call.

**Kind:** external C contract. The declaration is an explicit verification assumption.

**Verified use:** [`mdtests/strlen_of_an_empty_string_and_memcmp_use_the_catalog_contracts.md`](https://github.com/clicklang/click/blob/master/mdtests/strlen_of_an_empty_string_and_memcmp_use_the_catalog_contracts.md) returns zero for `cstr_at(text, 0u64)`;
[`mdtests/cstr_readable_witness_stated_before_call.md`](https://github.com/clicklang/click/blob/master/mdtests/cstr_readable_witness_stated_before_call.md)
names the string a call assembles; and
[`mdtests/cstr_dynamic_indexed_read_requires_permission.md`](https://github.com/clicklang/click/blob/master/mdtests/cstr_dynamic_indexed_read_requires_permission.md)
refuses a caller that holds only `cstr::readable`.

## C++ standard library models

Source: `library/cpp/span.click`, `library/cpp/array.click` and
`library/cpp/as_writable_bytes.click`. These files are not modules: the C++
importer appends the ones an import calls to its sidecar and writes each
`template<...> extern` block out at each element type and extent a call
names, `std::span<int>::size`. Its name table,
`src/languages/cpp/standard_library.rs`, lists the functions and element
types it maps to them. The model accessors `std_span_data`,
`std_span_size` and `std_array_data` name a span's or array's state.

### `std::span<T>`

```click
template<class T> extern unsigned long std::span<T>::size() const {
    views std_span_size(this);
    ensures result == std_span_size(this);
}
template<class T> extern unsigned long std::span<T>::size_bytes() const {
    views std_span_size(this);
    ensures result == std_span_size(this) * sizeof(T);
}
template<class T> extern T* std::span<T>::data() const {
    views std_span_data(this);
    ensures result == std_span_data(this);
}
template<class T> extern T& std::span<T>::front() const {
    views std_span_data(this);
    views std_span_size(this);
    requires 1u64 <= std_span_size(this);
    ensures &result == std_span_data(this);
}
template<class T> extern T& std::span<T>::back() const {
    views std_span_data(this);
    views std_span_size(this);
    requires 1u64 <= std_span_size(this);
    ensures &result == std_span_data(this) + (std_span_size(this) - 1u64);
}
template<class T> extern T& std::span<T>::operator[](unsigned long index) const {
    views std_span_data(this);
    views std_span_size(this);
    requires index < std_span_size(this);
    ensures &result == std_span_data(this) + index;
}
template<class T> extern std::span<T> std::span<T>::first(unsigned long count) const {
    views std_span_data(this);
    views std_span_size(this);
    requires count <= std_span_size(this);
    ensures std_span_data(result) == std_span_data(this);
    ensures std_span_size(result) == count;
}
template<class T> extern std::span<T> std::span<T>::last(unsigned long count) const {
    views std_span_data(this);
    views std_span_size(this);
    requires count <= std_span_size(this);
    ensures std_span_data(result) == std_span_data(this) + (std_span_size(this) - count);
    ensures std_span_size(result) == count;
}
template<class T> extern std::span<T> std::span<T>::subspan(unsigned long offset, unsigned long count) const {
    views std_span_data(this);
    views std_span_size(this);
    requires offset <= std_span_size(this);
    requires count != 18446744073709551615u64 implies count <= std_span_size(this) - offset;
    ensures std_span_data(result) == std_span_data(this) + offset;
    ensures count == 18446744073709551615u64 implies std_span_size(result) == std_span_size(this) - offset;
    ensures count != 18446744073709551615u64 implies std_span_size(result) == count;
}
```

**Meaning:** A dynamic-extent span is a view of `[data, data + size)`. The
element accessors require an index inside the view and form an address
without reading it; the subviews require the subview to lie inside the view
and keep the backing storage. `subspan`'s count `std::dynamic_extent`,
`18446744073709551615u64`, means "to the end".

**Kind:** C++ standard library model. Each declaration is an explicit verification assumption, reported as `C++ std`.

**Verified use:** [`tests/bitcoin_core_money_range.rs`](https://github.com/clicklang/click/blob/master/tests/bitcoin_core_money_range.rs) calls each through `axiomatic_span_*` probes, and refuses each requirement it drops (nightly).

### `std::span<T, N>`

```click
template<class T, std::size_t N> extern unsigned long std::span<T, N>::size() const {
    ensures result == N;
}
template<class T, std::size_t N> extern unsigned long std::span<T, N>::size_bytes() const {
    ensures result == N * sizeof(T);
}
template<class T, std::size_t N> extern T* std::span<T, N>::data() const {
    views std_span_data(this);
    ensures result == std_span_data(this);
}
template<class T, std::size_t N> extern T& std::span<T, N>::front() const {
    views std_span_data(this);
    requires 1u64 <= N;
    ensures &result == std_span_data(this);
}
template<class T, std::size_t N> extern T& std::span<T, N>::back() const {
    views std_span_data(this);
    requires 1u64 <= N;
    ensures &result == std_span_data(this) + (N - 1u64);
}
template<class T, std::size_t N> extern T& std::span<T, N>::operator[](unsigned long index) const {
    views std_span_data(this);
    requires index < N;
    ensures &result == std_span_data(this) + index;
}
template<class T, std::size_t N> extern std::span<T> std::span<T, N>::first(unsigned long count) const {
    views std_span_data(this);
    requires count <= N;
    ensures std_span_data(result) == std_span_data(this);
    ensures std_span_size(result) == count;
}
template<class T, std::size_t N> extern std::span<T> std::span<T, N>::last(unsigned long count) const {
    views std_span_data(this);
    requires count <= N;
    ensures std_span_data(result) == std_span_data(this) + (N - count);
    ensures std_span_size(result) == count;
}
template<class T, std::size_t N> extern std::span<T> std::span<T, N>::subspan(unsigned long offset, unsigned long count) const {
    views std_span_data(this);
    requires offset <= N;
    requires count != 18446744073709551615u64 implies count <= N - offset;
    ensures std_span_data(result) == std_span_data(this) + offset;
    ensures count == 18446744073709551615u64 implies std_span_size(result) == N - offset;
    ensures count != 18446744073709551615u64 implies std_span_size(result) == count;
}
```

**Meaning:** A static-extent span is a view of `[data, data + N)`. `N` is
the template argument, written at an instance as a literal, `4u64`; only the
data pointer is state. The subviews taking a runtime count are
dynamic-extent spans.

**Kind:** C++ standard library model. Each declaration is an explicit verification assumption, reported as `C++ std`.

**Verified use:** [`tests/bitcoin_core_money_range.rs`](https://github.com/clicklang/click/blob/master/tests/bitcoin_core_money_range.rs) reads, measures and subviews `std::span<int, 4>` and `std::span<const unsigned char, 32>` in `axiomatic_static_extent_*` (nightly).

### `std::array<T, N>`

```click
template<class T, std::size_t N> extern unsigned long std::array<T, N>::size() const {
    ensures result == N;
}
template<class T, std::size_t N> extern T* std::array<T, N>::data() {
    ensures result == &std_array_data(this)[0];
}
template<class T, std::size_t N> extern const T* std::array<T, N>::data() const {
    ensures result == &std_array_data(this)[0];
}
template<class T, std::size_t N> extern T& std::array<T, N>::operator[](unsigned long index) {
    requires index < N;
    ensures &result == &std_array_data(this)[index];
}
template<class T, std::size_t N> extern const T& std::array<T, N>::operator[](unsigned long index) const {
    requires index < N;
    ensures &result == &std_array_data(this)[index];
}
template<class T, std::size_t N> extern T& std::array<T, N>::front() {
    requires 1u64 <= N;
    ensures &result == &std_array_data(this)[0];
}
template<class T, std::size_t N> extern const T& std::array<T, N>::front() const {
    requires 1u64 <= N;
    ensures &result == &std_array_data(this)[0];
}
template<class T, std::size_t N> extern T& std::array<T, N>::back() {
    requires 1u64 <= N;
    ensures &result == &std_array_data(this)[N - 1u64];
}
template<class T, std::size_t N> extern const T& std::array<T, N>::back() const {
    requires 1u64 <= N;
    ensures &result == &std_array_data(this)[N - 1u64];
}
```

**Meaning:** A `std::array<T, N>` holds `N` elements in the object, named by
`std_array_data(a)`. Each accessor has a `const` and a mutable overload,
written as its own template; an instance is written from the overload whose
receiver constness it has. The element accessors require an index inside
the array and form an address without reading it.

**Kind:** C++ standard library model. Each declaration is an explicit verification assumption, reported as `C++ std`.

**Verified use:** [`tests/bitcoin_core_money_range.rs`](https://github.com/clicklang/click/blob/master/tests/bitcoin_core_money_range.rs) reads and writes elements in `axiomatic_std_array_reference_element_resources_verify`, and calls `size`, `data` and `back` in the nightly `axiomatic_std_array_*` tests.

### `std::as_writable_bytes<T, N>`

```click
template<class T, std::size_t N> extern std::span<std::byte> std::as_writable_bytes<T, N>(std::span<T> s) {
    ensures std_span_data(result) == old(std_span_data(s) as (uint8 *));
    ensures std_span_size(result) == old(std_span_size(s)) * sizeof(T);
}
```

**Meaning:** The same storage as a span of bytes: the backing address as
`uint8 *` and `sizeof(T)` bytes per element. It reads and grants nothing.
The argument is a span passed by value, so the result is stated from it as
it was on entry.

**Kind:** C++ standard library model. Each declaration is an explicit verification assumption, reported as `C++ std`.

**Verified use:** [`tests/bitcoin_core_money_range.rs`](https://github.com/clicklang/click/blob/master/tests/bitcoin_core_money_range.rs) views an `std::span<int>` as bytes in `pinned_writable_byte_span_*` (nightly).

## `click::rust::i8` through `click::rust::usize`

Source: `library/rust/i8.click` through `library/rust/usize.click`, one module per Rust integer type, imported as `import click::rust::u32;`. The Rust integer-method contracts of `library/rust/integers.click` name them by path.

### Rust core methods

`click::rust::i8` through `click::rust::usize` define, for each Rust integer
type, the core methods the Rust importer specifies: `min`, `max`,
`wrapping_add`, `wrapping_sub`, `wrapping_mul`, `saturating_add`,
`saturating_sub`, `checked_add`, `checked_sub`, `abs_diff`, and, for a signed
type, `unsigned_abs`. A call of one of these methods in imported Rust calls an
external function whose contract is the library's
([Rust integer methods](#rust-integer-methods)), `ensures result ==
click::rust::u32::min(a, b);`, so a sidecar states and proves claims about it
with the same function after `import click::rust::u32;`. Each is opaque until
`unfold` gives its definition. A signed type's wrapping arithmetic, `abs_diff`
and `unsigned_abs` go through the unsigned type of its width, whose casts are
modular; an 8- or 16-bit result is cast back from C's promoted `int`.

### Rust names for library lemmas

A Rust proof applies the library lemmas it needs by Rust names, in the
module of the operand type: `u32::multiply_to_integer`,
`usize::multiply_to_integer` and `usize::product_bound_from_division`. Each
restates a width-named lemma of [`click::integer`](#clickinteger) and is
proved by applying it, so it adds no trust. These modules import
`click::integer` for those proofs; a sidecar that applies a Rust name needs
only `import click::rust::u32;` or `import click::rust::usize;`.

### `i8::min`

```click
function min(a: int8, b: int8) -> int8 {
    if a <= b { a } else { b }
}
```

### `i8::max`

```click
function max(a: int8, b: int8) -> int8 {
    if a <= b { b } else { a }
}
```

### `i8::wrapping_add`

```click
function wrapping_add(a: int8, b: int8) -> int8 {
    a + b
}
```

### `i8::wrapping_sub`

```click
function wrapping_sub(a: int8, b: int8) -> int8 {
    a - b
}
```

### `i8::wrapping_mul`

```click
function wrapping_mul(a: int8, b: int8) -> int8 {
    a * b
}
```

### `i8::saturating_add`

```click
function saturating_add(a: int8, b: int8) -> int8 {
    if to_integer(a) + to_integer(b) > 127 {
        (127i64 as int8)
    } else {
        if to_integer(a) + to_integer(b) < -128 {
            (-128i64 as int8)
        } else {
            ((a as uint8) + (b as uint8)) as int8
        }
    }
}
```

### `i8::saturating_sub`

```click
function saturating_sub(a: int8, b: int8) -> int8 {
    if to_integer(a) - to_integer(b) > 127 {
        (127i64 as int8)
    } else {
        if to_integer(a) - to_integer(b) < -128 {
            (-128i64 as int8)
        } else {
            ((a as uint8) - (b as uint8)) as int8
        }
    }
}
```

### `i8::checked_add`

```click
function checked_add(a: int8, b: int8) -> Option<int8> {
    if -128 <= to_integer(a) + to_integer(b) and to_integer(a) + to_integer(b) <= 127 {
        Option<int8>::Some(((a as uint8) + (b as uint8)) as int8)
    } else {
        Option<int8>::None
    }
}
```

### `i8::checked_sub`

```click
function checked_sub(a: int8, b: int8) -> Option<int8> {
    if -128 <= to_integer(a) - to_integer(b) and to_integer(a) - to_integer(b) <= 127 {
        Option<int8>::Some(((a as uint8) - (b as uint8)) as int8)
    } else {
        Option<int8>::None
    }
}
```

### `i8::abs_diff`

```click
function abs_diff(a: int8, b: int8) -> uint8 {
    if b <= a { ((a as uint8) - (b as uint8)) as uint8 } else { ((b as uint8) - (a as uint8)) as uint8 }
}
```

### `i8::unsigned_abs`

```click
function unsigned_abs(a: int8) -> uint8 {
    if a < (0i64 as int8) { ((0u32 as uint8) - (a as uint8)) as uint8 } else { a as uint8 }
}
```

### `i16::min`

```click
function min(a: int16, b: int16) -> int16 {
    if a <= b { a } else { b }
}
```

### `i16::max`

```click
function max(a: int16, b: int16) -> int16 {
    if a <= b { b } else { a }
}
```

### `i16::wrapping_add`

```click
function wrapping_add(a: int16, b: int16) -> int16 {
    a + b
}
```

### `i16::wrapping_sub`

```click
function wrapping_sub(a: int16, b: int16) -> int16 {
    a - b
}
```

### `i16::wrapping_mul`

```click
function wrapping_mul(a: int16, b: int16) -> int16 {
    a * b
}
```

### `i16::saturating_add`

```click
function saturating_add(a: int16, b: int16) -> int16 {
    if to_integer(a) + to_integer(b) > 32767 {
        (32767i64 as int16)
    } else {
        if to_integer(a) + to_integer(b) < -32768 {
            (-32768i64 as int16)
        } else {
            ((a as uint16) + (b as uint16)) as int16
        }
    }
}
```

### `i16::saturating_sub`

```click
function saturating_sub(a: int16, b: int16) -> int16 {
    if to_integer(a) - to_integer(b) > 32767 {
        (32767i64 as int16)
    } else {
        if to_integer(a) - to_integer(b) < -32768 {
            (-32768i64 as int16)
        } else {
            ((a as uint16) - (b as uint16)) as int16
        }
    }
}
```

### `i16::checked_add`

```click
function checked_add(a: int16, b: int16) -> Option<int16> {
    if -32768 <= to_integer(a) + to_integer(b) and to_integer(a) + to_integer(b) <= 32767 {
        Option<int16>::Some(((a as uint16) + (b as uint16)) as int16)
    } else {
        Option<int16>::None
    }
}
```

### `i16::checked_sub`

```click
function checked_sub(a: int16, b: int16) -> Option<int16> {
    if -32768 <= to_integer(a) - to_integer(b) and to_integer(a) - to_integer(b) <= 32767 {
        Option<int16>::Some(((a as uint16) - (b as uint16)) as int16)
    } else {
        Option<int16>::None
    }
}
```

### `i16::abs_diff`

```click
function abs_diff(a: int16, b: int16) -> uint16 {
    if b <= a { ((a as uint16) - (b as uint16)) as uint16 } else { ((b as uint16) - (a as uint16)) as uint16 }
}
```

### `i16::unsigned_abs`

```click
function unsigned_abs(a: int16) -> uint16 {
    if a < (0i64 as int16) { ((0u32 as uint16) - (a as uint16)) as uint16 } else { a as uint16 }
}
```

### `i32::min`

```click
function min(a: int32, b: int32) -> int32 {
    if a <= b { a } else { b }
}
```

### `i32::max`

```click
function max(a: int32, b: int32) -> int32 {
    if a <= b { b } else { a }
}
```

### `i32::wrapping_add`

```click
function wrapping_add(a: int32, b: int32) -> int32 {
    ((a as uint32) + (b as uint32)) as int32
}
```

### `i32::wrapping_sub`

```click
function wrapping_sub(a: int32, b: int32) -> int32 {
    ((a as uint32) - (b as uint32)) as int32
}
```

### `i32::wrapping_mul`

```click
function wrapping_mul(a: int32, b: int32) -> int32 {
    ((a as uint32) * (b as uint32)) as int32
}
```

### `i32::saturating_add`

```click
function saturating_add(a: int32, b: int32) -> int32 {
    if to_integer(a) + to_integer(b) > 2147483647 {
        (2147483647i64 as int32)
    } else {
        if to_integer(a) + to_integer(b) < -2147483648 {
            (-2147483648i64 as int32)
        } else {
            ((a as uint32) + (b as uint32)) as int32
        }
    }
}
```

### `i32::saturating_sub`

```click
function saturating_sub(a: int32, b: int32) -> int32 {
    if to_integer(a) - to_integer(b) > 2147483647 {
        (2147483647i64 as int32)
    } else {
        if to_integer(a) - to_integer(b) < -2147483648 {
            (-2147483648i64 as int32)
        } else {
            ((a as uint32) - (b as uint32)) as int32
        }
    }
}
```

### `i32::checked_add`

```click
function checked_add(a: int32, b: int32) -> Option<int32> {
    if -2147483648 <= to_integer(a) + to_integer(b) and to_integer(a) + to_integer(b) <= 2147483647 {
        Option<int32>::Some(((a as uint32) + (b as uint32)) as int32)
    } else {
        Option<int32>::None
    }
}
```

### `i32::checked_sub`

```click
function checked_sub(a: int32, b: int32) -> Option<int32> {
    if -2147483648 <= to_integer(a) - to_integer(b) and to_integer(a) - to_integer(b) <= 2147483647 {
        Option<int32>::Some(((a as uint32) - (b as uint32)) as int32)
    } else {
        Option<int32>::None
    }
}
```

### `i32::abs_diff`

```click
function abs_diff(a: int32, b: int32) -> uint32 {
    if b <= a { (a as uint32) - (b as uint32) } else { (b as uint32) - (a as uint32) }
}
```

### `i32::unsigned_abs`

```click
function unsigned_abs(a: int32) -> uint32 {
    if a < (0i64 as int32) { 0u32 - (a as uint32) } else { a as uint32 }
}
```

### `i64::min`

```click
function min(a: int64, b: int64) -> int64 {
    if a <= b { a } else { b }
}
```

### `i64::max`

```click
function max(a: int64, b: int64) -> int64 {
    if a <= b { b } else { a }
}
```

### `i64::wrapping_add`

```click
function wrapping_add(a: int64, b: int64) -> int64 {
    ((a as uint64) + (b as uint64)) as int64
}
```

### `i64::wrapping_sub`

```click
function wrapping_sub(a: int64, b: int64) -> int64 {
    ((a as uint64) - (b as uint64)) as int64
}
```

### `i64::wrapping_mul`

```click
function wrapping_mul(a: int64, b: int64) -> int64 {
    ((a as uint64) * (b as uint64)) as int64
}
```

### `i64::saturating_add`

```click
function saturating_add(a: int64, b: int64) -> int64 {
    if to_integer(a) + to_integer(b) > 9223372036854775807 {
        9223372036854775807i64
    } else {
        if to_integer(a) + to_integer(b) < -9223372036854775808 {
            -9223372036854775808i64
        } else {
            ((a as uint64) + (b as uint64)) as int64
        }
    }
}
```

### `i64::saturating_sub`

```click
function saturating_sub(a: int64, b: int64) -> int64 {
    if to_integer(a) - to_integer(b) > 9223372036854775807 {
        9223372036854775807i64
    } else {
        if to_integer(a) - to_integer(b) < -9223372036854775808 {
            -9223372036854775808i64
        } else {
            ((a as uint64) - (b as uint64)) as int64
        }
    }
}
```

### `i64::checked_add`

```click
function checked_add(a: int64, b: int64) -> Option<int64> {
    if -9223372036854775808 <= to_integer(a) + to_integer(b) and to_integer(a) + to_integer(b) <= 9223372036854775807 {
        Option<int64>::Some(((a as uint64) + (b as uint64)) as int64)
    } else {
        Option<int64>::None
    }
}
```

### `i64::checked_sub`

```click
function checked_sub(a: int64, b: int64) -> Option<int64> {
    if -9223372036854775808 <= to_integer(a) - to_integer(b) and to_integer(a) - to_integer(b) <= 9223372036854775807 {
        Option<int64>::Some(((a as uint64) - (b as uint64)) as int64)
    } else {
        Option<int64>::None
    }
}
```

### `i64::abs_diff`

```click
function abs_diff(a: int64, b: int64) -> uint64 {
    if b <= a { (a as uint64) - (b as uint64) } else { (b as uint64) - (a as uint64) }
}
```

### `i64::unsigned_abs`

```click
function unsigned_abs(a: int64) -> uint64 {
    if a < 0i64 { 0u64 - (a as uint64) } else { a as uint64 }
}
```

### `isize::min`

```click
function min(a: int64, b: int64) -> int64 {
    if a <= b { a } else { b }
}
```

### `isize::max`

```click
function max(a: int64, b: int64) -> int64 {
    if a <= b { b } else { a }
}
```

### `isize::wrapping_add`

```click
function wrapping_add(a: int64, b: int64) -> int64 {
    ((a as uint64) + (b as uint64)) as int64
}
```

### `isize::wrapping_sub`

```click
function wrapping_sub(a: int64, b: int64) -> int64 {
    ((a as uint64) - (b as uint64)) as int64
}
```

### `isize::wrapping_mul`

```click
function wrapping_mul(a: int64, b: int64) -> int64 {
    ((a as uint64) * (b as uint64)) as int64
}
```

### `isize::saturating_add`

```click
function saturating_add(a: int64, b: int64) -> int64 {
    if to_integer(a) + to_integer(b) > 9223372036854775807 {
        9223372036854775807i64
    } else {
        if to_integer(a) + to_integer(b) < -9223372036854775808 {
            -9223372036854775808i64
        } else {
            ((a as uint64) + (b as uint64)) as int64
        }
    }
}
```

### `isize::saturating_sub`

```click
function saturating_sub(a: int64, b: int64) -> int64 {
    if to_integer(a) - to_integer(b) > 9223372036854775807 {
        9223372036854775807i64
    } else {
        if to_integer(a) - to_integer(b) < -9223372036854775808 {
            -9223372036854775808i64
        } else {
            ((a as uint64) - (b as uint64)) as int64
        }
    }
}
```

### `isize::checked_add`

```click
function checked_add(a: int64, b: int64) -> Option<int64> {
    if -9223372036854775808 <= to_integer(a) + to_integer(b) and to_integer(a) + to_integer(b) <= 9223372036854775807 {
        Option<int64>::Some(((a as uint64) + (b as uint64)) as int64)
    } else {
        Option<int64>::None
    }
}
```

### `isize::checked_sub`

```click
function checked_sub(a: int64, b: int64) -> Option<int64> {
    if -9223372036854775808 <= to_integer(a) - to_integer(b) and to_integer(a) - to_integer(b) <= 9223372036854775807 {
        Option<int64>::Some(((a as uint64) - (b as uint64)) as int64)
    } else {
        Option<int64>::None
    }
}
```

### `isize::abs_diff`

```click
function abs_diff(a: int64, b: int64) -> uint64 {
    if b <= a { (a as uint64) - (b as uint64) } else { (b as uint64) - (a as uint64) }
}
```

### `isize::unsigned_abs`

```click
function unsigned_abs(a: int64) -> uint64 {
    if a < 0i64 { 0u64 - (a as uint64) } else { a as uint64 }
}
```

### `u8::min`

```click
function min(a: uint8, b: uint8) -> uint8 {
    if a <= b { a } else { b }
}
```

### `u8::max`

```click
function max(a: uint8, b: uint8) -> uint8 {
    if a <= b { b } else { a }
}
```

### `u8::wrapping_add`

```click
function wrapping_add(a: uint8, b: uint8) -> uint8 {
    a + b
}
```

### `u8::wrapping_sub`

```click
function wrapping_sub(a: uint8, b: uint8) -> uint8 {
    a - b
}
```

### `u8::wrapping_mul`

```click
function wrapping_mul(a: uint8, b: uint8) -> uint8 {
    a * b
}
```

### `u8::saturating_add`

```click
function saturating_add(a: uint8, b: uint8) -> uint8 {
    if to_integer(a) + to_integer(b) <= 255 { (a + b) as uint8 } else { (255u32 as uint8) }
}
```

### `u8::saturating_sub`

```click
function saturating_sub(a: uint8, b: uint8) -> uint8 {
    if b <= a { (a - b) as uint8 } else { (0u32 as uint8) }
}
```

### `u8::checked_add`

```click
function checked_add(a: uint8, b: uint8) -> Option<uint8> {
    if to_integer(a) + to_integer(b) <= 255 {
        Option<uint8>::Some((a + b) as uint8)
    } else {
        Option<uint8>::None
    }
}
```

### `u8::checked_sub`

```click
function checked_sub(a: uint8, b: uint8) -> Option<uint8> {
    if b <= a { Option<uint8>::Some((a - b) as uint8) } else { Option<uint8>::None }
}
```

### `u8::abs_diff`

```click
function abs_diff(a: uint8, b: uint8) -> uint8 {
    if b <= a { (a - b) as uint8 } else { (b - a) as uint8 }
}
```

### `u16::min`

```click
function min(a: uint16, b: uint16) -> uint16 {
    if a <= b { a } else { b }
}
```

### `u16::max`

```click
function max(a: uint16, b: uint16) -> uint16 {
    if a <= b { b } else { a }
}
```

### `u16::wrapping_add`

```click
function wrapping_add(a: uint16, b: uint16) -> uint16 {
    a + b
}
```

### `u16::wrapping_sub`

```click
function wrapping_sub(a: uint16, b: uint16) -> uint16 {
    a - b
}
```

### `u16::wrapping_mul`

```click
function wrapping_mul(a: uint16, b: uint16) -> uint16 {
    a * b
}
```

### `u16::saturating_add`

```click
function saturating_add(a: uint16, b: uint16) -> uint16 {
    if to_integer(a) + to_integer(b) <= 65535 { (a + b) as uint16 } else { (65535u32 as uint16) }
}
```

### `u16::saturating_sub`

```click
function saturating_sub(a: uint16, b: uint16) -> uint16 {
    if b <= a { (a - b) as uint16 } else { (0u32 as uint16) }
}
```

### `u16::checked_add`

```click
function checked_add(a: uint16, b: uint16) -> Option<uint16> {
    if to_integer(a) + to_integer(b) <= 65535 {
        Option<uint16>::Some((a + b) as uint16)
    } else {
        Option<uint16>::None
    }
}
```

### `u16::checked_sub`

```click
function checked_sub(a: uint16, b: uint16) -> Option<uint16> {
    if b <= a { Option<uint16>::Some((a - b) as uint16) } else { Option<uint16>::None }
}
```

### `u16::abs_diff`

```click
function abs_diff(a: uint16, b: uint16) -> uint16 {
    if b <= a { (a - b) as uint16 } else { (b - a) as uint16 }
}
```

### `u32::min`

```click
function min(a: uint32, b: uint32) -> uint32 {
    if a <= b { a } else { b }
}
```

### `u32::max`

```click
function max(a: uint32, b: uint32) -> uint32 {
    if a <= b { b } else { a }
}
```

### `u32::wrapping_add`

```click
function wrapping_add(a: uint32, b: uint32) -> uint32 {
    a + b
}
```

### `u32::wrapping_sub`

```click
function wrapping_sub(a: uint32, b: uint32) -> uint32 {
    a - b
}
```

### `u32::wrapping_mul`

```click
function wrapping_mul(a: uint32, b: uint32) -> uint32 {
    a * b
}
```

### `u32::saturating_add`

```click
function saturating_add(a: uint32, b: uint32) -> uint32 {
    if to_integer(a) + to_integer(b) <= 4294967295 { a + b } else { 4294967295u32 }
}
```

### `u32::saturating_sub`

```click
function saturating_sub(a: uint32, b: uint32) -> uint32 {
    if b <= a { a - b } else { 0u32 }
}
```

### `u32::checked_add`

```click
function checked_add(a: uint32, b: uint32) -> Option<uint32> {
    if to_integer(a) + to_integer(b) <= 4294967295 {
        Option<uint32>::Some(a + b)
    } else {
        Option<uint32>::None
    }
}
```

### `u32::checked_sub`

```click
function checked_sub(a: uint32, b: uint32) -> Option<uint32> {
    if b <= a { Option<uint32>::Some(a - b) } else { Option<uint32>::None }
}
```

### `u32::abs_diff`

```click
function abs_diff(a: uint32, b: uint32) -> uint32 {
    if b <= a { a - b } else { b - a }
}
```

### `u32::multiply_to_integer`

```click
theorem multiply_to_integer(left: uint32, right: uint32) {
    requires right == 0u32 or left <= 4294967295u32 / right;
    ensures to_integer(left * right) == to_integer(left) * to_integer(right) by apply(integer::uint32_multiply_to_integer(left, right));
}
```

An in-range `u32` product is the Integer product: the Rust name of
[`integer::uint32_multiply_to_integer`](#integeruint32_multiply_to_integer),
proved by applying it.

**Verified use:** [`examples/rust-unsigned/arithmetic.click`](https://github.com/clicklang/click/blob/master/examples/rust-unsigned/arithmetic.click), [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md).

### `u64::min`

```click
function min(a: uint64, b: uint64) -> uint64 {
    if a <= b { a } else { b }
}
```

### `u64::max`

```click
function max(a: uint64, b: uint64) -> uint64 {
    if a <= b { b } else { a }
}
```

### `u64::wrapping_add`

```click
function wrapping_add(a: uint64, b: uint64) -> uint64 {
    a + b
}
```

### `u64::wrapping_sub`

```click
function wrapping_sub(a: uint64, b: uint64) -> uint64 {
    a - b
}
```

### `u64::wrapping_mul`

```click
function wrapping_mul(a: uint64, b: uint64) -> uint64 {
    a * b
}
```

### `u64::saturating_add`

```click
function saturating_add(a: uint64, b: uint64) -> uint64 {
    if to_integer(a) + to_integer(b) <= 18446744073709551615 { a + b } else { 18446744073709551615u64 }
}
```

### `u64::saturating_sub`

```click
function saturating_sub(a: uint64, b: uint64) -> uint64 {
    if b <= a { a - b } else { 0u64 }
}
```

### `u64::checked_add`

```click
function checked_add(a: uint64, b: uint64) -> Option<uint64> {
    if to_integer(a) + to_integer(b) <= 18446744073709551615 {
        Option<uint64>::Some(a + b)
    } else {
        Option<uint64>::None
    }
}
```

### `u64::checked_sub`

```click
function checked_sub(a: uint64, b: uint64) -> Option<uint64> {
    if b <= a { Option<uint64>::Some(a - b) } else { Option<uint64>::None }
}
```

### `u64::abs_diff`

```click
function abs_diff(a: uint64, b: uint64) -> uint64 {
    if b <= a { a - b } else { b - a }
}
```

### `usize::min`

```click
function min(a: uint64, b: uint64) -> uint64 {
    if a <= b { a } else { b }
}
```

### `usize::max`

```click
function max(a: uint64, b: uint64) -> uint64 {
    if a <= b { b } else { a }
}
```

### `usize::wrapping_add`

```click
function wrapping_add(a: uint64, b: uint64) -> uint64 {
    a + b
}
```

### `usize::wrapping_sub`

```click
function wrapping_sub(a: uint64, b: uint64) -> uint64 {
    a - b
}
```

### `usize::wrapping_mul`

```click
function wrapping_mul(a: uint64, b: uint64) -> uint64 {
    a * b
}
```

### `usize::saturating_add`

```click
function saturating_add(a: uint64, b: uint64) -> uint64 {
    if to_integer(a) + to_integer(b) <= 18446744073709551615 { a + b } else { 18446744073709551615u64 }
}
```

### `usize::saturating_sub`

```click
function saturating_sub(a: uint64, b: uint64) -> uint64 {
    if b <= a { a - b } else { 0u64 }
}
```

### `usize::checked_add`

```click
function checked_add(a: uint64, b: uint64) -> Option<uint64> {
    if to_integer(a) + to_integer(b) <= 18446744073709551615 {
        Option<uint64>::Some(a + b)
    } else {
        Option<uint64>::None
    }
}
```

### `usize::checked_sub`

```click
function checked_sub(a: uint64, b: uint64) -> Option<uint64> {
    if b <= a { Option<uint64>::Some(a - b) } else { Option<uint64>::None }
}
```

### `usize::abs_diff`

```click
function abs_diff(a: uint64, b: uint64) -> uint64 {
    if b <= a { a - b } else { b - a }
}
```

### `usize::product_bound_from_division`

```click
theorem product_bound_from_division(x: uint64, y: uint64) {
    requires y != 0u64;
    requires x <= 18446744073709551615u64 / y;
    ensures to_integer(x) * to_integer(y) <= to_integer(18446744073709551615u64) by apply(integer::uint64_product_bound_from_division(x, y));
}
```

A product bounded by division does not exceed `usize::MAX`: the Rust name of
[`integer::uint64_product_bound_from_division`](#integeruint64_product_bound_from_division),
proved by applying it.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md); `tests/rust_import.rs` applies it to imported Rust (`rust_usize_arithmetic_casts_and_expansion_verify`).

### `usize::multiply_to_integer`

```click
theorem multiply_to_integer(left: uint64, right: uint64) {
    requires to_integer(left) * to_integer(right) <= 18446744073709551615;
    ensures to_integer(left * right) == to_integer(left) * to_integer(right) by apply(integer::uint64_multiply_to_integer(left, right));
}
```

An in-range `usize` product is the Integer product: the Rust name of
[`integer::uint64_multiply_to_integer`](#integeruint64_multiply_to_integer),
proved by applying it.

**Verified use:** [`mdtests/stdlib_every_symbol.md`](https://github.com/clicklang/click/blob/master/mdtests/stdlib_every_symbol.md); `tests/rust_import.rs` applies it to imported Rust (`rust_usize_arithmetic_casts_and_expansion_verify`).

## `click::rust::vec`

Source: `library/rust/vec.click`, `import click::rust::vec;`.

### Rust vectors

`click::rust::vec` declares `Vec<T>`, the values a Rust vector holds, as a
primitive library type, with four operations and the axioms that relate them.
A sidecar reads them after `import click::rust::vec;` and proves claims about
vectors by citing the axioms, `apply(vec::len_push(v, x));`. The `type`, the
bodyless `function`s and the `axiom`s are forms only the built-in library
modules may declare; each axiom is trusted, not proved
([trust](../../concepts/trust.md#the-click-library)). Capacity and allocation
are outside the model.
A Rust `Vec<u32>` an import reads is this type at `uint32`, and its methods'
contracts are stated with these operations
([Vec values](../rust.md#vec-values)).

### `Vec`

```click
type Vec<T>;
```

A Rust vector's values: a finite sequence of fewer than 2^64 values of `T`. It is a primitive type, like `uint32`: it has no constructors, so a `match`, a proof `match` and `induct` refuse it, and the kernel reads each instance, `Vec<uint32>`, as a rigid type of its own. Its meaning is the four operations below and the axioms that relate them; two vectors that hold the same values are equal by `vec::extensionality`. A `spec enum` field cannot hold a `Vec` yet.

### `vec::len`

```click
function len<T>(v: Vec<T>) -> uint64;
```

The number of values in `v`. Opaque: `unfold` refuses it, since it has no definition.

### `vec::get`

```click
function get<T>(v: Vec<T>, i: uint64) -> T;
```

The value at index `i`. The axioms describe it only below `vec::len(v)`; past the end it names a value nothing constrains.

### `vec::push`

```click
function push<T>(v: Vec<T>, x: T) -> Vec<T>;
```

`v` with `x` appended.

### `vec::set`

```click
function set<T>(v: Vec<T>, i: uint64, x: T) -> Vec<T>;
```

`v` with the value at index `i` replaced by `x`. The axioms describe it only for `i` below `vec::len(v)`.

### `vec::len_push`

```click
axiom len_push<T>(v: Vec<T>, x: T) {
    requires vec::len(v) < 18446744073709551615u64;
    ensures vec::len(vec::push(v, x)) == vec::len(v) + 1;
}
```

**Axiom:** trusted, not proved.

### `vec::get_push_last`

```click
axiom get_push_last<T>(v: Vec<T>, x: T) {
    requires vec::len(v) < 18446744073709551615u64;
    ensures vec::get(vec::push(v, x), vec::len(v)) == x;
}
```

**Axiom:** trusted, not proved.

### `vec::get_push_kept`

```click
axiom get_push_kept<T>(v: Vec<T>, x: T, i: uint64) {
    requires i < vec::len(v);
    ensures vec::get(vec::push(v, x), i) == vec::get(v, i);
}
```

**Axiom:** trusted, not proved.

### `vec::len_set`

```click
axiom len_set<T>(v: Vec<T>, i: uint64, x: T) {
    requires i < vec::len(v);
    ensures vec::len(vec::set(v, i, x)) == vec::len(v);
}
```

**Axiom:** trusted, not proved.

### `vec::get_set_same`

```click
axiom get_set_same<T>(v: Vec<T>, i: uint64, x: T) {
    requires i < vec::len(v);
    ensures vec::get(vec::set(v, i, x), i) == x;
}
```

**Axiom:** trusted, not proved.

### `vec::get_set_other`

```click
axiom get_set_other<T>(v: Vec<T>, i: uint64, j: uint64, x: T) {
    requires i < vec::len(v);
    requires j < vec::len(v);
    requires i != j;
    ensures vec::get(vec::set(v, i, x), j) == vec::get(v, j);
}
```

**Axiom:** trusted, not proved.

### `vec::extensionality`

```click
axiom extensionality<T>(v: Vec<T>, w: Vec<T>) {
    requires vec::len(v) == vec::len(w);
    requires forall (i: uint64) { i < vec::len(v) implies vec::get(v, i) == vec::get(w, i) };
    ensures v == w;
}
```

**Axiom:** trusted, not proved.

## `click::rust::slice`

Source: `library/rust/slice.click`, `import click::rust::slice;`.

### Rust slices

`click::rust::slice` declares `Slice<T>`, a Rust slice as one value: its data
pointer and its length. `==` on slices is identity, the same pointer and the
same length. A slice value grants no access: reading `s[i]` reads memory
through its pointer under the caller's `views` or `owns`. A sidecar names
these operations after `import click::rust::slice;`. A Rust sidecar writes a
slice with Rust's spellings, and each slice is one argument of a pure-function
call, so a pointer and a length are passed as `slice::from_raw_parts(p, n)`
([pure functions](../rust.md)). A slice parameter is lowered as its pointer
and its length; both spellings are the same slice.

### `Slice`

```click
spec enum Slice<T> {
    Slice(T*, uint64),
}
```

A slice of `T`: a pointer to its first element and its number of elements.
Two slices are equal exactly when their pointers and lengths are.

### `slice::len`

```click
function len<T>(s: Slice<T>) -> uint64 {
    match s {
        Slice::Slice(_, n) => n,
    }
}
```

The number of elements, Rust's `s.len()`.

### `slice::as_ptr`

```click
function as_ptr<T>(s: Slice<T>) -> T* {
    match s {
        Slice::Slice(p, _) => p,
    }
}
```

The data pointer, Rust's `s.as_ptr()`.

### `slice::from_raw_parts`

```click
function from_raw_parts<T>(p: T*, n: uint64) -> Slice<T> {
    Slice::Slice(p, n)
}
```

The slice with data `p` and length `n`, Rust's
`core::slice::from_raw_parts(p, n)`.

### `slice::subslice_len`

```click
function subslice_len(start: uint64, end: uint64, len: uint64) -> uint64 {
    end - start
}
```

The length of the subslice `s[start..end]` of a slice of length `len`. A
call owes `start <= end` and `end <= len` where it is evaluated, guarded as
every evaluation condition is, where Rust panics otherwise. A Rust sidecar's
subslice `s[a..b]` is `Slice::Slice(s.as_ptr() + a, slice::subslice_len(a,
b, s.len()))`, and prints as `s[a..b]`.

## `click::rust::chunks_exact`

Source: `library/rust/chunks_exact.click`, `import click::rust::chunks_exact;`.

### Rust chunk iterators

`click::rust::chunks_exact` declares `ChunksExact<T>`, the iterator Rust's
`s.chunks_exact(n)` returns, as a primitive type like `Vec<T>`. An iterator
value stands for the finite sequence of chunks it will still yield:
`chunks_exact::len(it)` of them, the `k`-th being `chunks_exact::nth(it, k)`,
a slice. `nth` is an observation that consumes nothing, not Rust's consuming
`Iterator::nth`. The axioms say what `chunks_exact` builds and what one
`next()` leaves; they are trusted, not proved. A value reads with its
methods, `s.chunks_exact(4u64).nth(k).len()`
([methods](../language/index.md#methods)). A Rust unit imports its `chunks_exact` iterators as values of this type
([Rust](../rust.md#exact-chunk-iterators-and-remainder)); see
`design/rust-iterators.md`.

### `ChunksExact`

```click
type ChunksExact<T>;
```

Rust's `core::slice::ChunksExact<T>`, the iterator `s.chunks_exact(n)` returns, as a primitive type of the Click library. An iterator value stands for the finite sequence of items it will still yield: `len(it)` items, the `k`-th of them `nth(it, k)`. Its meaning is the functions below and the axioms that relate them (`design/rust-iterators.md`).  Each axiom is trusted, not proved. Rust's own `ChunksExact` satisfies all of them together, so they are consistent. `nth` here is an observation that consumes nothing, not Rust's consuming `Iterator::nth`.

### `chunks_exact::chunks_exact`

```click
function chunks_exact<T>(s: Slice<T>, n: uint64) -> ChunksExact<T>;
```

The iterator `s.chunks_exact(n)`, for a chunk size `n` that is not zero, where Rust panics.

### `chunks_exact::len`

```click
function len<T>(it: ChunksExact<T>) -> uint64;
```

The number of chunks `it` will still yield, Rust's `it.len()`.

### `chunks_exact::nth`

```click
function nth<T>(it: ChunksExact<T>, k: uint64) -> Slice<T>;
```

The chunk the `k`-th following `next()` returns, for a `k` below `len(it)`. At any other index it names some slice the axioms say nothing about.

### `chunks_exact::remainder`

```click
function remainder<T>(it: ChunksExact<T>) -> Slice<T>;
```

The elements the chunks leave over, Rust's `it.remainder()`.

### `chunks_exact::after_next`

```click
function after_next<T>(it: ChunksExact<T>) -> ChunksExact<T>;
```

`it` after one `next()` that returned a chunk, for an `it` with `0 < len(it)`.

### `chunks_exact::after`

```click
function after<T>(it: ChunksExact<T>, k: Integer) -> ChunksExact<T>;
```

`it` after `k` calls of `next()` that each returned a chunk, for a `k` from zero to `len(it)`. The count is a mathematical integer, so a loop states where its iterator stands by its pass count: `iter == start.after(iterations)`.

### `chunks_exact::len_chunks_exact`

```click
axiom len_chunks_exact<T>(s: Slice<T>, n: uint64) {
    requires n != 0u64;
    ensures chunks_exact::len(chunks_exact::chunks_exact(s, n)) == slice::len(s) / n;
}
```

**Axiom:** trusted, not proved.

### `chunks_exact::nth_chunks_exact`

```click
axiom nth_chunks_exact(s: Slice<uint8>, n: uint64, k: uint64) {
    requires n != 0u64;
    requires k < slice::len(s) / n;
    ensures slice::as_ptr(chunks_exact::nth(chunks_exact::chunks_exact(s, n), k))
        == slice::as_ptr(s) + k * n;
    ensures slice::len(chunks_exact::nth(chunks_exact::chunks_exact(s, n), k)) == n;
}
```

Chunk `k` is the `n` elements from element `k * n`. Stated for bytes: an offset from a `T*` needs `T`'s size, which a generic axiom does not have. **Axiom:** trusted, not proved.

### `chunks_exact::remainder_chunks_exact`

```click
axiom remainder_chunks_exact(s: Slice<uint8>, n: uint64) {
    requires n != 0u64;
    ensures slice::as_ptr(chunks_exact::remainder(chunks_exact::chunks_exact(s, n)))
        == slice::as_ptr(s) + (slice::len(s) - slice::len(s) % n);
    ensures slice::len(chunks_exact::remainder(chunks_exact::chunks_exact(s, n)))
        == slice::len(s) % n;
}
```

The remainder is the last `len(s) % n` elements. Stated for bytes, as `nth_chunks_exact` is. **Axiom:** trusted, not proved.

### `chunks_exact::len_after_next`

```click
axiom len_after_next<T>(it: ChunksExact<T>) {
    requires 0u64 < chunks_exact::len(it);
    ensures chunks_exact::len(chunks_exact::after_next(it)) == chunks_exact::len(it) - 1u64;
}
```

**Axiom:** trusted, not proved.

### `chunks_exact::nth_after_next`

```click
axiom nth_after_next<T>(it: ChunksExact<T>, k: uint64) {
    requires 0u64 < chunks_exact::len(it);
    requires k < chunks_exact::len(it) - 1u64;
    ensures chunks_exact::nth(chunks_exact::after_next(it), k)
        == chunks_exact::nth(it, k + 1u64);
}
```

**Axiom:** trusted, not proved.

### `chunks_exact::remainder_after_next`

```click
axiom remainder_after_next<T>(it: ChunksExact<T>) {
    requires 0u64 < chunks_exact::len(it);
    ensures chunks_exact::remainder(chunks_exact::after_next(it)) == chunks_exact::remainder(it);
}
```

`next()` leaves the remainder as it was. **Axiom:** trusted, not proved.

### `chunks_exact::after_zero`

```click
axiom after_zero<T>(it: ChunksExact<T>) {
    ensures chunks_exact::after(it, 0) == it;
}
```

No call leaves the iterator as it was. **Axiom:** trusted, not proved.

### `chunks_exact::after_next_after`

```click
axiom after_next_after<T>(it: ChunksExact<T>, k: Integer) {
    requires 0 <= k;
    requires k < to_integer(chunks_exact::len(it));
    ensures chunks_exact::after_next(chunks_exact::after(it, k)) == chunks_exact::after(it, k + 1);
}
```

One more `next()` is one more call. **Axiom:** trusted, not proved.

### `chunks_exact::len_after`

```click
axiom len_after<T>(it: ChunksExact<T>, k: Integer) {
    requires 0 <= k;
    requires k <= to_integer(chunks_exact::len(it));
    ensures to_integer(chunks_exact::len(chunks_exact::after(it, k)))
        == to_integer(chunks_exact::len(it)) - k;
}
```

**Axiom:** trusted, not proved.

### `chunks_exact::nth_after`

```click
axiom nth_after<T>(it: ChunksExact<T>, k: Integer, j: uint64, m: uint64) {
    requires 0 <= k;
    requires to_integer(m) == k + to_integer(j);
    requires m < chunks_exact::len(it);
    ensures chunks_exact::nth(chunks_exact::after(it, k), j) == chunks_exact::nth(it, m);
}
```

The chunks still to come are the ones `it` would have yielded from `k` on: chunk `j` of them is chunk `m` of `it`, where `m` is `k + j`. **Axiom:** trusted, not proved.

### `chunks_exact::remainder_after`

```click
axiom remainder_after<T>(it: ChunksExact<T>, k: Integer) {
    requires 0 <= k;
    requires k <= to_integer(chunks_exact::len(it));
    ensures chunks_exact::remainder(chunks_exact::after(it, k)) == chunks_exact::remainder(it);
}
```

**Axiom:** trusted, not proved.

## `click::rust::slice_iter`

Source: `library/rust/slice_iter.click`, `import click::rust::slice_iter;`.

### Rust slice iterators

`click::rust::slice_iter` declares `SliceIter<T>`, the iterator Rust's
`s.iter()` returns, as a primitive type like `Vec<T>`. An iterator value
stands for the elements it will still yield, which are a slice:
`slice_iter::as_slice(it)`, with `slice_iter::len(it)` elements. A value
reads with its methods, `iter.as_slice().as_ptr()` and `iter.len()`
([methods](../language/index.md#methods)). The two axioms are generic and
trusted. What one `next()` leaves is stated by the contract of the call that
makes it, at the element type it is made at, because an offset from a `T*`
needs `T`'s size. A Rust unit with `"iterators": "library"` imports its slice
iterators as values of this type ([Rust](../rust.md#slice-iterators-as-library-values));
see `design/rust-iterators.md`.

### `SliceIter`

```click
type SliceIter<T>;
```

Rust's `core::slice::Iter<T>`, the iterator `s.iter()` returns, as a primitive type of the Click library. An iterator value stands for the elements it will still yield, which are a slice: `as_slice(it)`, Rust's `it.as_slice()`.

### `slice_iter::iter`

```click
function iter<T>(s: Slice<T>) -> SliceIter<T>;
```

The iterator `s.iter()`.

### `slice_iter::as_slice`

```click
function as_slice<T>(it: SliceIter<T>) -> Slice<T>;
```

The elements `it` will still yield, Rust's `it.as_slice()`. The next `next()` returns a reference to its first element.

### `slice_iter::len`

```click
function len<T>(it: SliceIter<T>) -> uint64;
```

The number of elements `it` will still yield, Rust's `it.len()`.

### `slice_iter::after_next`

```click
function after_next<T>(it: SliceIter<T>) -> SliceIter<T>;
```

`it` after one `next()` that returned an element, for an `it` with `0 < len(it)`.

### `slice_iter::as_slice_iter`

```click
axiom as_slice_iter<T>(s: Slice<T>) {
    ensures slice_iter::as_slice(slice_iter::iter(s)) == s;
}
```

**Axiom:** trusted, not proved. A new iterator will yield the whole slice.

### `slice_iter::len_as_slice`

```click
axiom len_as_slice<T>(it: SliceIter<T>) {
    ensures slice_iter::len(it) == slice::len(slice_iter::as_slice(it));
}
```

**Axiom:** trusted, not proved. The count is the length of what is left.

## Rust core models

Source: `library/rust/core.click`. This file is not a module: the Rust
importer appends it to a sidecar when an import calls one of its methods,
and writes each generic `extern fn` block out at each element type a call
names, `Vec::push<u32>`. A block no call names is dropped. The integer
core-method contracts are in [Rust integer methods](#rust-integer-methods).

### `Vec<T>` methods

```click
extern fn Vec::new<T>() -> Vec<T> {
    ensures click::rust::vec::len(result) == 0u64;
}
extern fn Vec::with_capacity<T>(capacity: usize) -> Vec<T> {
    ensures click::rust::vec::len(result) == 0u64;
}
extern fn Vec::push<T>(v: &mut Vec<T>, x: T) {
    owns *v;
    requires click::rust::vec::len(*v) < 18446744073709551615u64;
    ensures *v == click::rust::vec::push(old(*v), x);
    ensures click::rust::vec::len(*v) == click::rust::vec::len(old(*v)) + 1;
    ensures click::rust::vec::get(*v, click::rust::vec::len(old(*v))) == x;
    ensures forall (k: usize) { k < click::rust::vec::len(old(*v)) implies click::rust::vec::get(*v, k) == click::rust::vec::get(old(*v), k) };
}
extern fn Vec::len<T>(v: &Vec<T>) -> usize {
    views *v;
    ensures result == click::rust::vec::len(old(*v));
}
extern fn Vec::index<T>(v: &Vec<T>, i: usize) -> T {
    views *v;
    requires i < click::rust::vec::len(*v);
    ensures result == click::rust::vec::get(old(*v), i);
}
```

**Meaning:** Each call's effect on the library's `Vec<T>` value
([`click::rust::vec`](#clickrustvec)). The capacity is outside the model.
`v[i]` requires `i` in bounds, as Rust panics otherwise. A vector holds at
most `u64::MAX` elements, and `push` requires room below it; Rust's own
allocation limit is smaller and aborts rather than returns.

**Kind:** Rust core model. Each declaration is an explicit verification assumption, reported as `Rust core`.

**Verified use:** [`tests/rust_import.rs`](https://github.com/clicklang/click/blob/master/tests/rust_import.rs) verifies [`design/charon-trial/vec-values/vecs.rs`](https://github.com/clicklang/click/blob/master/design/charon-trial/vec-values/vecs.rs) in `charon_vec_values_read_as_the_library_vec`, and refuses each claim mutated false and an index not shown in bounds.

### `slice::swap<T>`

```click
extern fn slice::swap<T>(s: &mut [T], a: usize, b: usize) {
    owns *s;
    requires a < s.len();
    requires b < s.len();
    ensures s[a] == old(s[b]);
    ensures s[b] == old(s[a]);
    ensures forall (k: usize) { k < s.len() and k != a and k != b implies s[k] == old(s[k]) };
}
```

**Meaning:** `<[T]>::swap(s, a, b)` owns the slice, requires both indices in
bounds, as Rust panics otherwise, and exchanges the two elements, leaving
every other element unchanged.

**Kind:** Rust core model. Each declaration is an explicit verification assumption, reported as `Rust core`.

**Verified use:** [`tests/rust_import/core_methods.rs`](https://github.com/clicklang/click/blob/master/tests/rust_import/core_methods.rs) verifies `exchange`, `swap_bytes` and `reverse_three` in [`design/charon-trial/core-methods/methods.rs`](https://github.com/clicklang/click/blob/master/design/charon-trial/core-methods/methods.rs), and refuses a `swap` index not shown in bounds.

### `Option<T>` and `Result<T, E>` unwrapping

```click
extern fn Option::unwrap<T>(o: Option<T>) -> T {
    requires o != Option<T>::None;
    ensures o == Option<T>::Some(result);
}
extern fn Option::expect<T>(o: Option<T>) -> T {
    requires o != Option<T>::None;
    ensures o == Option<T>::Some(result);
}
extern fn Option::unwrap_or<T>(o: Option<T>, d: T) -> T {
    ensures result == click::option::unwrap_or(o, d);
}
extern fn Result::unwrap<T, E>(r: Result<T, E>) -> T {
    requires exists (value: T) { r == Result<T, E>::Ok(value) };
    ensures r == Result<T, E>::Ok(result);
}
extern fn Result::expect<T, E>(r: Result<T, E>) -> T {
    requires exists (value: T) { r == Result<T, E>::Ok(value) };
    ensures r == Result<T, E>::Ok(result);
}
extern fn Result::unwrap_or<T, E>(r: Result<T, E>, d: T) -> T {
    ensures result == click::result::unwrap_or(r, d);
}
```

**Meaning:** `unwrap` and `expect` require `Some` or `Ok`, as Rust panics
otherwise, and return its payload; `expect`'s message serves the panic alone
and is not passed. `unwrap_or` is the library's `option::unwrap_or` or
`result::unwrap_or`. The importer declares them at a scalar payload.

**Kind:** Rust core model. Each declaration is an explicit verification assumption, reported as `Rust core`.

**Verified use:** [`tests/rust_import/panics.rs`](https://github.com/clicklang/click/blob/master/tests/rust_import/panics.rs) verifies `unwrapped` and `expected` in [`design/charon-trial/panics/panics.rs`](https://github.com/clicklang/click/blob/master/design/charon-trial/panics/panics.rs) and refuses an unwrap not shown `Some`; [`tests/rust_import.rs`](https://github.com/clicklang/click/blob/master/tests/rust_import.rs) verifies `Result` `unwrap`, `expect` and `unwrap_or` in [`design/charon-trial/result-values/results.rs`](https://github.com/clicklang/click/blob/master/design/charon-trial/result-values/results.rs) in `charon_result_values_read_as_click_results`; [`tests/rust_import/core_methods.rs`](https://github.com/clicklang/click/blob/master/tests/rust_import/core_methods.rs) verifies `Option::unwrap_or` in [`design/charon-trial/core-methods/methods.rs`](https://github.com/clicklang/click/blob/master/design/charon-trial/core-methods/methods.rs).

### Slice value methods

```click
extern fn slice::as_ptr<T>(s: Slice<T>) -> &T {
    ensures result == click::rust::slice::as_ptr(s);
}
extern fn slice::len<T>(s: Slice<T>) -> usize {
    ensures result == click::rust::slice::len(s);
}
```

**Meaning:** A slice the library-iterator model returns, a `chunks_exact`
chunk or remainder, is one value of the library's
[`Slice<T>`](#clickrustslice), and the body reads its data and length
through Rust's `<[T]>::as_ptr` and `<[T]>::len`. The importer declares them
at `u8`.

**Kind:** Rust core model. Each declaration is an explicit verification assumption, reported as `Rust core`.

**Verified use:** [`tests/rust_import.rs`](https://github.com/clicklang/click/blob/master/tests/rust_import.rs) verifies the `chunks_exact` loops of [`design/charon-trial/chunks/chunks.rs`](https://github.com/clicklang/click/blob/master/design/charon-trial/chunks/chunks.rs) in `charon_chunks_check_boundaries_authority_and_false_claims` (nightly), whose sidecar [`design/charon-trial/chunks/chunks.click`](https://github.com/clicklang/click/blob/master/design/charon-trial/chunks/chunks.click) reads each chunk through `as_ptr` and `len`.

### `SliceIter<T>` methods

```click
extern fn SliceIter::iter<T>(p: &T, n: usize) -> SliceIter<T> {
    ensures result == click::rust::slice_iter::iter(Slice<T>::Slice(p, n));
    ensures click::rust::slice::as_ptr(click::rust::slice_iter::as_slice(result)) == p;
    ensures click::rust::slice::len(click::rust::slice_iter::as_slice(result)) == n;
    ensures click::rust::slice_iter::len(result) == n;
}
extern fn SliceIter::next<T>(it: &mut SliceIter<T>) -> Option<&T> {
    owns *it;
    ensures click::rust::slice_iter::len(old(*it)) == 0u64 implies result == Option<&T>::None;
    ensures click::rust::slice_iter::len(old(*it)) == 0u64 implies *it == old(*it);
    ensures 0u64 < click::rust::slice_iter::len(old(*it)) implies result == Option<&T>::Some(click::rust::slice::as_ptr(click::rust::slice_iter::as_slice(old(*it))));
    ensures 0u64 < click::rust::slice_iter::len(old(*it)) implies *it == click::rust::slice_iter::after_next(old(*it));
    ensures 0u64 < click::rust::slice_iter::len(old(*it)) implies click::rust::slice::as_ptr(click::rust::slice_iter::as_slice(*it)) == click::rust::slice::as_ptr(click::rust::slice_iter::as_slice(old(*it))) + 1u64;
    ensures 0u64 < click::rust::slice_iter::len(old(*it)) implies click::rust::slice::len(click::rust::slice_iter::as_slice(*it)) == click::rust::slice::len(click::rust::slice_iter::as_slice(old(*it))) - 1u64;
    ensures 0u64 < click::rust::slice_iter::len(old(*it)) implies click::rust::slice_iter::len(*it) == click::rust::slice_iter::len(old(*it)) - 1u64;
}
```

**Meaning:** `<[T]>::iter` builds the library's
[`SliceIter<T>`](#clickrustslice_iter) of the slice, and `Iterator::next`
returns `None` with the iterator unchanged when nothing is left, and
otherwise a reference to the first remaining element, leaving the
iterator one element later and one shorter. The offset needs the element's
size, so it is stated here, at each element type, rather than as an axiom.

**Kind:** Rust core model. Each declaration is an explicit verification assumption, reported as `Rust core`.

**Verified use:** [`tests/rust_import.rs`](https://github.com/clicklang/click/blob/master/tests/rust_import.rs) verifies the loop over `bytes.iter()` in [`design/charon-trial/slice-iter/sum.rs`](https://github.com/clicklang/click/blob/master/design/charon-trial/slice-iter/sum.rs) in `charon_slice_iter_sums_bytes_by_its_library_contract` (nightly), and `rust_empty_slice_iterator_needs_no_read_authority`.

### `ChunksExact<T>` methods

```click
extern fn ChunksExact::new<T>(s: &[T], n: usize) -> ChunksExact<T> {
    requires n != 0u64;
    ensures result == click::rust::chunks_exact::chunks_exact(Slice<T>::Slice(s, s.len()), n);
}
extern fn ChunksExact::next<T>(it: &mut ChunksExact<T>) -> Option<&[T]> {
    owns *it;
    ensures click::rust::chunks_exact::len(old(*it)) == 0u64 implies result == Option<&[T]>::None;
    ensures click::rust::chunks_exact::len(old(*it)) == 0u64 implies *it == old(*it);
    ensures 0u64 < click::rust::chunks_exact::len(old(*it)) implies result == Option<&[T]>::Some(click::rust::chunks_exact::nth(old(*it), 0u64));
    ensures 0u64 < click::rust::chunks_exact::len(old(*it)) implies *it == click::rust::chunks_exact::after_next(old(*it));
}
extern fn ChunksExact::remainder<T>(it: &ChunksExact<T>) -> Slice<T> {
    views *it;
    ensures result == click::rust::chunks_exact::remainder(old(*it));
}
extern fn ChunksExact::remainder_ptr<T>(it: ChunksExact<T>) -> &T {
    ensures result == click::rust::slice::as_ptr(click::rust::chunks_exact::remainder(it));
}
extern fn ChunksExact::remainder_len<T>(it: ChunksExact<T>) -> usize {
    ensures result == click::rust::slice::len(click::rust::chunks_exact::remainder(it));
}
extern fn ChunksExact::len<T>(it: ChunksExact<T>) -> usize {
    ensures result == click::rust::chunks_exact::len(it);
}
extern fn ChunksExact::item_ptr<T>(it: ChunksExact<T>) -> &T {
    requires 0u64 < click::rust::chunks_exact::len(it);
    ensures result == click::rust::slice::as_ptr(click::rust::chunks_exact::nth(it, 0u64));
}
extern fn ChunksExact::item_len<T>(it: ChunksExact<T>) -> usize {
    requires 0u64 < click::rust::chunks_exact::len(it);
    ensures result == click::rust::slice::len(click::rust::chunks_exact::nth(it, 0u64));
}
extern fn ChunksExact::after_next<T>(it: ChunksExact<T>) -> ChunksExact<T> {
    requires 0u64 < click::rust::chunks_exact::len(it);
    ensures result == click::rust::chunks_exact::after_next(it);
}
```

**Meaning:** `<[T]>::chunks_exact(n)` requires `n != 0`, as Rust panics
otherwise, and builds the library's
[`ChunksExact<T>`](#clickrustchunks_exact) of the slice. With the
library-iterator model, `next` and `remainder` are Rust's own methods over
that value. Without it, a loop and `remainder()` lower to the pointer and
length operations `remainder_ptr` through `after_next`, each stated with the
same library functions. The importer declares them at `u8`, the element
type of the library's chunk axioms.

**Kind:** Rust core model. Each declaration is an explicit verification assumption, reported as `Rust core`.

**Verified use:** [`tests/rust_import.rs`](https://github.com/clicklang/click/blob/master/tests/rust_import.rs) verifies `chunks_exact` loops and `remainder()` with the library-iterator model in `chunks_exact_is_proved_by_its_library_contract` and `charon_chunks_check_boundaries_authority_and_false_claims` (nightly, [`design/charon-trial/chunks/chunks.rs`](https://github.com/clicklang/click/blob/master/design/charon-trial/chunks/chunks.rs)), and without it in `rust_chunks_exact_remainder_metadata_and_bytes` and `rust_chunks_exact_loops_cover_input_and_preserve_bytes` (nightly), which refuse a zero chunk size not ruled out.

## Rust integer methods

Source: `library/rust/integers.click`, one `extern fn` per Rust integer core
method and type, each on one line. This file is not a module: the Rust
importer appends to a sidecar the line of each method an import calls, and
only those, so a contract at a type no call names, `Option<i8>`, is never
read. Each states its result with the specification function of the same
path in [`click::rust::i8` through `click::rust::usize`](#clickrusti8-through-clickrustusize);
the `extern`'s own path, `u32::min`, names the program's function, never the
library function ([core library methods](../rust.md#core-library-methods)).

### Integer `min` and `max`

```click
extern fn i8::min(a: i8, b: i8) -> i8 { ensures result == click::rust::i8::min(a, b); }
extern fn i8::max(a: i8, b: i8) -> i8 { ensures result == click::rust::i8::max(a, b); }
extern fn i16::min(a: i16, b: i16) -> i16 { ensures result == click::rust::i16::min(a, b); }
extern fn i16::max(a: i16, b: i16) -> i16 { ensures result == click::rust::i16::max(a, b); }
extern fn i32::min(a: i32, b: i32) -> i32 { ensures result == click::rust::i32::min(a, b); }
extern fn i32::max(a: i32, b: i32) -> i32 { ensures result == click::rust::i32::max(a, b); }
extern fn i64::min(a: i64, b: i64) -> i64 { ensures result == click::rust::i64::min(a, b); }
extern fn i64::max(a: i64, b: i64) -> i64 { ensures result == click::rust::i64::max(a, b); }
extern fn isize::min(a: isize, b: isize) -> isize { ensures result == click::rust::isize::min(a, b); }
extern fn isize::max(a: isize, b: isize) -> isize { ensures result == click::rust::isize::max(a, b); }
extern fn u8::min(a: u8, b: u8) -> u8 { ensures result == click::rust::u8::min(a, b); }
extern fn u8::max(a: u8, b: u8) -> u8 { ensures result == click::rust::u8::max(a, b); }
extern fn u16::min(a: u16, b: u16) -> u16 { ensures result == click::rust::u16::min(a, b); }
extern fn u16::max(a: u16, b: u16) -> u16 { ensures result == click::rust::u16::max(a, b); }
extern fn u32::min(a: u32, b: u32) -> u32 { ensures result == click::rust::u32::min(a, b); }
extern fn u32::max(a: u32, b: u32) -> u32 { ensures result == click::rust::u32::max(a, b); }
extern fn u64::min(a: u64, b: u64) -> u64 { ensures result == click::rust::u64::min(a, b); }
extern fn u64::max(a: u64, b: u64) -> u64 { ensures result == click::rust::u64::max(a, b); }
extern fn usize::min(a: usize, b: usize) -> usize { ensures result == click::rust::usize::min(a, b); }
extern fn usize::max(a: usize, b: usize) -> usize { ensures result == click::rust::usize::max(a, b); }
```

**Meaning:** `a.min(b)` and `a.max(b)`, of `Ord` at an integer type, are the library's
`min` and `max` of that type.

**Kind:** Rust core model. Each declaration is an explicit verification assumption, reported as `Rust core`.

**Verified use:** [`tests/rust_import/core_methods.rs`](https://github.com/clicklang/click/blob/master/tests/rust_import/core_methods.rs) verifies `smaller`, `larger` and `fewer` in [`design/charon-trial/core-methods/methods.rs`](https://github.com/clicklang/click/blob/master/design/charon-trial/core-methods/methods.rs), and refuses a wrong claim about `smaller(1, 2)`.

### Integer wrapping arithmetic

```click
extern fn i8::wrapping_add(a: i8, b: i8) -> i8 { ensures result == click::rust::i8::wrapping_add(a, b); }
extern fn i8::wrapping_sub(a: i8, b: i8) -> i8 { ensures result == click::rust::i8::wrapping_sub(a, b); }
extern fn i8::wrapping_mul(a: i8, b: i8) -> i8 { ensures result == click::rust::i8::wrapping_mul(a, b); }
extern fn i16::wrapping_add(a: i16, b: i16) -> i16 { ensures result == click::rust::i16::wrapping_add(a, b); }
extern fn i16::wrapping_sub(a: i16, b: i16) -> i16 { ensures result == click::rust::i16::wrapping_sub(a, b); }
extern fn i16::wrapping_mul(a: i16, b: i16) -> i16 { ensures result == click::rust::i16::wrapping_mul(a, b); }
extern fn i32::wrapping_add(a: i32, b: i32) -> i32 { ensures result == click::rust::i32::wrapping_add(a, b); }
extern fn i32::wrapping_sub(a: i32, b: i32) -> i32 { ensures result == click::rust::i32::wrapping_sub(a, b); }
extern fn i32::wrapping_mul(a: i32, b: i32) -> i32 { ensures result == click::rust::i32::wrapping_mul(a, b); }
extern fn i64::wrapping_add(a: i64, b: i64) -> i64 { ensures result == click::rust::i64::wrapping_add(a, b); }
extern fn i64::wrapping_sub(a: i64, b: i64) -> i64 { ensures result == click::rust::i64::wrapping_sub(a, b); }
extern fn i64::wrapping_mul(a: i64, b: i64) -> i64 { ensures result == click::rust::i64::wrapping_mul(a, b); }
extern fn isize::wrapping_add(a: isize, b: isize) -> isize { ensures result == click::rust::isize::wrapping_add(a, b); }
extern fn isize::wrapping_sub(a: isize, b: isize) -> isize { ensures result == click::rust::isize::wrapping_sub(a, b); }
extern fn isize::wrapping_mul(a: isize, b: isize) -> isize { ensures result == click::rust::isize::wrapping_mul(a, b); }
extern fn u8::wrapping_add(a: u8, b: u8) -> u8 { ensures result == click::rust::u8::wrapping_add(a, b); }
extern fn u8::wrapping_sub(a: u8, b: u8) -> u8 { ensures result == click::rust::u8::wrapping_sub(a, b); }
extern fn u8::wrapping_mul(a: u8, b: u8) -> u8 { ensures result == click::rust::u8::wrapping_mul(a, b); }
extern fn u16::wrapping_add(a: u16, b: u16) -> u16 { ensures result == click::rust::u16::wrapping_add(a, b); }
extern fn u16::wrapping_sub(a: u16, b: u16) -> u16 { ensures result == click::rust::u16::wrapping_sub(a, b); }
extern fn u16::wrapping_mul(a: u16, b: u16) -> u16 { ensures result == click::rust::u16::wrapping_mul(a, b); }
extern fn u32::wrapping_add(a: u32, b: u32) -> u32 { ensures result == click::rust::u32::wrapping_add(a, b); }
extern fn u32::wrapping_sub(a: u32, b: u32) -> u32 { ensures result == click::rust::u32::wrapping_sub(a, b); }
extern fn u32::wrapping_mul(a: u32, b: u32) -> u32 { ensures result == click::rust::u32::wrapping_mul(a, b); }
extern fn u64::wrapping_add(a: u64, b: u64) -> u64 { ensures result == click::rust::u64::wrapping_add(a, b); }
extern fn u64::wrapping_sub(a: u64, b: u64) -> u64 { ensures result == click::rust::u64::wrapping_sub(a, b); }
extern fn u64::wrapping_mul(a: u64, b: u64) -> u64 { ensures result == click::rust::u64::wrapping_mul(a, b); }
extern fn usize::wrapping_add(a: usize, b: usize) -> usize { ensures result == click::rust::usize::wrapping_add(a, b); }
extern fn usize::wrapping_sub(a: usize, b: usize) -> usize { ensures result == click::rust::usize::wrapping_sub(a, b); }
extern fn usize::wrapping_mul(a: usize, b: usize) -> usize { ensures result == click::rust::usize::wrapping_mul(a, b); }
```

**Meaning:** `wrapping_add`, `wrapping_sub` and `wrapping_mul` are the library's
modular sums, differences and products of each type.

**Kind:** Rust core model. Each declaration is an explicit verification assumption, reported as `Rust core`.

**Verified use:** [`tests/rust_import/core_methods.rs`](https://github.com/clicklang/click/blob/master/tests/rust_import/core_methods.rs) verifies `byte_ring` in [`design/charon-trial/core-methods/methods.rs`](https://github.com/clicklang/click/blob/master/design/charon-trial/core-methods/methods.rs); [`tests/examples.rs`](https://github.com/clicklang/click/blob/master/tests/examples.rs) verifies `wrapping_add_u32`, `wrapping_sub_u32` and `wrapping_mul_u32` in [`examples/integer-languages/rust/integers.rs`](https://github.com/clicklang/click/blob/master/examples/integer-languages/rust/integers.rs) in `example_projects`.

### Integer saturating arithmetic

```click
extern fn i8::saturating_add(a: i8, b: i8) -> i8 { ensures result == click::rust::i8::saturating_add(a, b); }
extern fn i8::saturating_sub(a: i8, b: i8) -> i8 { ensures result == click::rust::i8::saturating_sub(a, b); }
extern fn i16::saturating_add(a: i16, b: i16) -> i16 { ensures result == click::rust::i16::saturating_add(a, b); }
extern fn i16::saturating_sub(a: i16, b: i16) -> i16 { ensures result == click::rust::i16::saturating_sub(a, b); }
extern fn i32::saturating_add(a: i32, b: i32) -> i32 { ensures result == click::rust::i32::saturating_add(a, b); }
extern fn i32::saturating_sub(a: i32, b: i32) -> i32 { ensures result == click::rust::i32::saturating_sub(a, b); }
extern fn i64::saturating_add(a: i64, b: i64) -> i64 { ensures result == click::rust::i64::saturating_add(a, b); }
extern fn i64::saturating_sub(a: i64, b: i64) -> i64 { ensures result == click::rust::i64::saturating_sub(a, b); }
extern fn isize::saturating_add(a: isize, b: isize) -> isize { ensures result == click::rust::isize::saturating_add(a, b); }
extern fn isize::saturating_sub(a: isize, b: isize) -> isize { ensures result == click::rust::isize::saturating_sub(a, b); }
extern fn u8::saturating_add(a: u8, b: u8) -> u8 { ensures result == click::rust::u8::saturating_add(a, b); }
extern fn u8::saturating_sub(a: u8, b: u8) -> u8 { ensures result == click::rust::u8::saturating_sub(a, b); }
extern fn u16::saturating_add(a: u16, b: u16) -> u16 { ensures result == click::rust::u16::saturating_add(a, b); }
extern fn u16::saturating_sub(a: u16, b: u16) -> u16 { ensures result == click::rust::u16::saturating_sub(a, b); }
extern fn u32::saturating_add(a: u32, b: u32) -> u32 { ensures result == click::rust::u32::saturating_add(a, b); }
extern fn u32::saturating_sub(a: u32, b: u32) -> u32 { ensures result == click::rust::u32::saturating_sub(a, b); }
extern fn u64::saturating_add(a: u64, b: u64) -> u64 { ensures result == click::rust::u64::saturating_add(a, b); }
extern fn u64::saturating_sub(a: u64, b: u64) -> u64 { ensures result == click::rust::u64::saturating_sub(a, b); }
extern fn usize::saturating_add(a: usize, b: usize) -> usize { ensures result == click::rust::usize::saturating_add(a, b); }
extern fn usize::saturating_sub(a: usize, b: usize) -> usize { ensures result == click::rust::usize::saturating_sub(a, b); }
```

**Meaning:** `saturating_add` and `saturating_sub` are the library's sums and
differences clamped to the type's range.

**Kind:** Rust core model. Each declaration is an explicit verification assumption, reported as `Rust core`.

**Verified use:** [`tests/rust_import/core_methods.rs`](https://github.com/clicklang/click/blob/master/tests/rust_import/core_methods.rs) verifies `shortfall` and `sample_sum` in [`design/charon-trial/core-methods/methods.rs`](https://github.com/clicklang/click/blob/master/design/charon-trial/core-methods/methods.rs).

### Integer checked arithmetic

```click
extern fn i8::checked_add(a: i8, b: i8) -> Option<i8> { ensures result == click::rust::i8::checked_add(a, b); }
extern fn i8::checked_sub(a: i8, b: i8) -> Option<i8> { ensures result == click::rust::i8::checked_sub(a, b); }
extern fn i16::checked_add(a: i16, b: i16) -> Option<i16> { ensures result == click::rust::i16::checked_add(a, b); }
extern fn i16::checked_sub(a: i16, b: i16) -> Option<i16> { ensures result == click::rust::i16::checked_sub(a, b); }
extern fn i32::checked_add(a: i32, b: i32) -> Option<i32> { ensures result == click::rust::i32::checked_add(a, b); }
extern fn i32::checked_sub(a: i32, b: i32) -> Option<i32> { ensures result == click::rust::i32::checked_sub(a, b); }
extern fn i64::checked_add(a: i64, b: i64) -> Option<i64> { ensures result == click::rust::i64::checked_add(a, b); }
extern fn i64::checked_sub(a: i64, b: i64) -> Option<i64> { ensures result == click::rust::i64::checked_sub(a, b); }
extern fn isize::checked_add(a: isize, b: isize) -> Option<isize> { ensures result == click::rust::isize::checked_add(a, b); }
extern fn isize::checked_sub(a: isize, b: isize) -> Option<isize> { ensures result == click::rust::isize::checked_sub(a, b); }
extern fn u8::checked_add(a: u8, b: u8) -> Option<u8> { ensures result == click::rust::u8::checked_add(a, b); }
extern fn u8::checked_sub(a: u8, b: u8) -> Option<u8> { ensures result == click::rust::u8::checked_sub(a, b); }
extern fn u16::checked_add(a: u16, b: u16) -> Option<u16> { ensures result == click::rust::u16::checked_add(a, b); }
extern fn u16::checked_sub(a: u16, b: u16) -> Option<u16> { ensures result == click::rust::u16::checked_sub(a, b); }
extern fn u32::checked_add(a: u32, b: u32) -> Option<u32> { ensures result == click::rust::u32::checked_add(a, b); }
extern fn u32::checked_sub(a: u32, b: u32) -> Option<u32> { ensures result == click::rust::u32::checked_sub(a, b); }
extern fn u64::checked_add(a: u64, b: u64) -> Option<u64> { ensures result == click::rust::u64::checked_add(a, b); }
extern fn u64::checked_sub(a: u64, b: u64) -> Option<u64> { ensures result == click::rust::u64::checked_sub(a, b); }
extern fn usize::checked_add(a: usize, b: usize) -> Option<usize> { ensures result == click::rust::usize::checked_add(a, b); }
extern fn usize::checked_sub(a: usize, b: usize) -> Option<usize> { ensures result == click::rust::usize::checked_sub(a, b); }
```

**Meaning:** `checked_add` and `checked_sub` return the library's `Option` of the
type: `Some` of the sum or difference when it is in range, `None`
otherwise.

**Kind:** Rust core model. Each declaration is an explicit verification assumption, reported as `Rust core`.

**Verified use:** [`tests/rust_import/core_methods.rs`](https://github.com/clicklang/click/blob/master/tests/rust_import/core_methods.rs) verifies `clamp_add` and `spend` in [`design/charon-trial/core-methods/methods.rs`](https://github.com/clicklang/click/blob/master/design/charon-trial/core-methods/methods.rs), and refuses a fitting sum claimed `None`.

### Integer `abs_diff` and `unsigned_abs`

```click
extern fn i8::abs_diff(a: i8, b: i8) -> u8 { ensures result == click::rust::i8::abs_diff(a, b); }
extern fn i8::unsigned_abs(a: i8) -> u8 { ensures result == click::rust::i8::unsigned_abs(a); }
extern fn i16::abs_diff(a: i16, b: i16) -> u16 { ensures result == click::rust::i16::abs_diff(a, b); }
extern fn i16::unsigned_abs(a: i16) -> u16 { ensures result == click::rust::i16::unsigned_abs(a); }
extern fn i32::abs_diff(a: i32, b: i32) -> u32 { ensures result == click::rust::i32::abs_diff(a, b); }
extern fn i32::unsigned_abs(a: i32) -> u32 { ensures result == click::rust::i32::unsigned_abs(a); }
extern fn i64::abs_diff(a: i64, b: i64) -> u64 { ensures result == click::rust::i64::abs_diff(a, b); }
extern fn i64::unsigned_abs(a: i64) -> u64 { ensures result == click::rust::i64::unsigned_abs(a); }
extern fn isize::abs_diff(a: isize, b: isize) -> usize { ensures result == click::rust::isize::abs_diff(a, b); }
extern fn isize::unsigned_abs(a: isize) -> usize { ensures result == click::rust::isize::unsigned_abs(a); }
extern fn u8::abs_diff(a: u8, b: u8) -> u8 { ensures result == click::rust::u8::abs_diff(a, b); }
extern fn u16::abs_diff(a: u16, b: u16) -> u16 { ensures result == click::rust::u16::abs_diff(a, b); }
extern fn u32::abs_diff(a: u32, b: u32) -> u32 { ensures result == click::rust::u32::abs_diff(a, b); }
extern fn u64::abs_diff(a: u64, b: u64) -> u64 { ensures result == click::rust::u64::abs_diff(a, b); }
extern fn usize::abs_diff(a: usize, b: usize) -> usize { ensures result == click::rust::usize::abs_diff(a, b); }
```

**Meaning:** `abs_diff` is the distance between its operands and `unsigned_abs` the
magnitude of a signed value, each in the unsigned type of the operand's
width.

**Kind:** Rust core model. Each declaration is an explicit verification assumption, reported as `Rust core`.

**Verified use:** [`tests/rust_import/core_methods.rs`](https://github.com/clicklang/click/blob/master/tests/rust_import/core_methods.rs) verifies `distance` and `magnitude` in [`design/charon-trial/core-methods/methods.rs`](https://github.com/clicklang/click/blob/master/design/charon-trial/core-methods/methods.rs).

## `click::separation`

Source: `library/separation.click`, `import click::separation;`.

### `separation::restrict`

```click
theorem restrict(A: Resource, B: Resource, a: Resource, b: Resource) {
    requires separate(A, B);
    requires contains(A, a);
    requires contains(B, b);
    ensures separate(a, b);
}
```

**Meaning:** Contained parts of separate parents are separate. Import
`click::separation` and apply the theorem with the three explicit premises.
`Resource` arguments are descriptors and grant no ownership. This named axiom
is backed by a trusted kernel constructor; application does not search memory
history or discover containment facts.

**Verified use:** [`mdtests/resource_theorem_parameters.md`](https://github.com/clicklang/click/blob/master/mdtests/resource_theorem_parameters.md).

### `separation::viewable_restrict`

```click
theorem viewable_restrict(A: Resource, B: Resource) {
    requires viewable(A);
    requires contains(A, B);
    ensures viewable(B);
}
```

**Meaning:** A contained part of a viewable resource is viewable at the same
snapshot. This applies to arbitrary resource descriptors, including named
resources and separating conjunctions. For memory,
`viewable(memory(p[a..b]))` is the same fact as `viewable(p[a..b])`.
The axiom grants no ownership and discovers neither containment nor history
paths; both premises are explicit.

**Verified use:** `mdtests/viewable_restrict_memory.md` and
`mdtests/viewable_restrict_resources.md`.

### Separating conjunction laws

`A * B` is a resource descriptor for separating conjunction; `separation::emp`
is the empty descriptor. Neither grants ownership. The following named axioms
construct their conclusions from exactly the written premises, without opening
resource definitions or discovering containment paths.

| Theorem | Required premises | Conclusion |
| --- | --- | --- |
| `contains_refl(A)` | none | `contains(A, A)` |
| `contains_trans(A, B, C)` | `contains(A, B)`; `contains(B, C)` | `contains(A, C)` |
| `contains_left(A, B)` | none | `contains(A * B, A)` |
| `contains_right(A, B)` | none | `contains(A * B, B)` |
| `separate_symm(A, B)` | `separate(A, B)` | `separate(B, A)` |
| `separate_star(A, B, C)` | `separate(A, C)`; `separate(B, C)` | `separate(A * B, C)` |
| `separate_emp(A)` | none | `separate(separation::emp, A)` |

Import `click::separation`; each theorem above is in the `separation::`
namespace. All parameters have type `Resource`. There is no rule deriving
separation between the two operands merely from writing their conjunction.
For example, `A * A` retains two occurrences and is not identified with `A`.
Use `restrict` to pass separation from a containing resource to a selected part.

**Checked examples:** `mdtests/separation_conjunction.md` and
`mdtests/separation_conjunction_missing_premise.md`.

### `separation::contains_refl`

```click
theorem contains_refl(A: Resource) { ensures contains(A, A); }
```

### `separation::contains_trans`

```click
theorem contains_trans(A: Resource, B: Resource, C: Resource) {
    requires contains(A, B);
    requires contains(B, C);
    ensures contains(A, C);
}
```

### `separation::contains_left`

```click
theorem contains_left(A: Resource, B: Resource) { ensures contains(A * B, A); }
```

### `separation::contains_right`

```click
theorem contains_right(A: Resource, B: Resource) { ensures contains(A * B, B); }
```

### `separation::separate_symm`

```click
theorem separate_symm(A: Resource, B: Resource) {
    requires separate(A, B);
    ensures separate(B, A);
}
```

### `separation::separate_star`

```click
theorem separate_star(A: Resource, B: Resource, C: Resource) {
    requires separate(A, C);
    requires separate(B, C);
    ensures separate(A * B, C);
}
```

### `separation::separate_emp`

```click
theorem separate_emp(A: Resource) { ensures separate(separation::emp, A); }
```

### `separation::elements`

```click
theorem elements<T, I>(p: T*, i: I, j: I) {
    requires i != j;
    ensures separate(memory(p[i]), memory(p[j]));
}
```

**Meaning:** Unequal indices of one typed array describe separate complete
elements. Both indices have the same inferred type `I`: `int32`, `int64`, or
`uint64`. Signed indices retain signed offsets, including negative offsets;
no unsigned conversion is inserted. The inferred `T` supplies the physical
storage width, including struct padding. Apply with the explicit disequality
premise. The law constructs two element descriptors directly, without enumerating
an interval or inspecting memory history. These are logical resource descriptors;
the law grants no ownership or permission to read or write either element.
Executable pointer arithmetic and accesses retain their normal definedness checks.

The premise is the disequality of the index values at type `I`. For an
`int32` index `m - 1` that is `((m - 1) as int32) != 0`, not the
mathematical Integer fact `m - 1 != 0`, which `apply ... using` refuses as a
different fact. State the word fact with `have ((m - 1) as int32) != 0 by
solve();`, which `solve` proves from the Integer fact where the facts keep
`m - 1` in range, and cite `defined(m - 1)` for the argument expression
([`separation_elements_index_word_from_an_integer_fact.md`](https://github.com/clicklang/click/blob/master/mdtests/separation_elements_index_word_from_an_integer_fact.md)).

**Verified use:** [`mdtests/separation_elements.md`](https://github.com/clicklang/click/blob/master/mdtests/separation_elements.md) and [`mdtests/separation_elements_types.md`](https://github.com/clicklang/click/blob/master/mdtests/separation_elements_types.md). Signed indices and preservation are checked by [`mdtests/separation_elements_signed.md`](https://github.com/clicklang/click/blob/master/mdtests/separation_elements_signed.md) and [`mdtests/separation_elements_signed_store.md`](https://github.com/clicklang/click/blob/master/mdtests/separation_elements_signed_store.md).


### `separation::distinct_elements`

```click
theorem distinct_elements<T, I>(p: T*, i: I, j: I) {
    requires i != j;
    ensures &p[i] != &p[j];
}
```

**Meaning:** Unequal indices of one typed array give unequal element
addresses. Like `separation::elements`, both indices have the same inferred
type `I` (`int32`, `int64`, or `uint64`), the addresses are the exact scaled
offsets `p + i * sizeof(T)` and `p + j * sizeof(T)`, and the premise is the
disequality of the index values at type `I`, such as
`((m - 1) as int32) != 0` or `j != 0u64`. The law states only the address
disequality; it grants no ownership and checks no pointer arithmetic.
`solve` applies it to a goal `&q[j] != &q[0]` after proving the index
disequality, and its expansion writes the `apply` with an explicit `using`
([tactics](../tactics/index.md#arithmetic-with-selected-premises)).

**Verified use:** [`mdtests/solve_proves_element_addresses_distinct_from_their_indices.md`](https://github.com/clicklang/click/blob/master/mdtests/solve_proves_element_addresses_distinct_from_their_indices.md) applies it explicitly and through `solve`, and [`mdtests/solve_proves_element_addresses_distinct_at_each_index_type.md`](https://github.com/clicklang/click/blob/master/mdtests/solve_proves_element_addresses_distinct_at_each_index_type.md) at `uint64` and `int64` indices; [`mdtests/solve_does_not_prove_element_addresses_distinct_when_the_indices_may_be_equal.md`](https://github.com/clicklang/click/blob/master/mdtests/solve_does_not_prove_element_addresses_distinct_when_the_indices_may_be_equal.md) refuses equal-possible indices.
### `separation::subrange`

```click
theorem subrange<T, I>(p: T*, lo: I, hi: I, inner_lo: I, inner_hi: I) {
    requires lo <= inner_lo;
    requires inner_lo <= inner_hi;
    requires inner_hi <= hi;
    ensures contains(memory(p[lo..hi]), memory(p[inner_lo..inner_hi]));
}
```

**Meaning:** Nested element intervals describe contained resources. Index type
`I` is `int32` or `uint64`; all four bounds have that same type. Bounds are in
elements of the inferred type `T`, not bytes. Both descriptors retain the
same pointer origin and element width. The law grants no ownership or read
permission. It constructs the containment implication directly, without
searching facts, enumerating elements, or traversing memory history.
Applications supply all three bound premises explicitly. Empty inner intervals
are permitted. Memory access and separation still require their usual validity
conditions.

**Verified use:** [`mdtests/generic_pointer_theorem_parameters.md`](https://github.com/clicklang/click/blob/master/mdtests/generic_pointer_theorem_parameters.md) and [`mdtests/generic_pointer_struct_parameters.md`](https://github.com/clicklang/click/blob/master/mdtests/generic_pointer_struct_parameters.md), including padded structs and struct-pointer elements. [`mdtests/separation_subrange_supports_wide_bounds.md`](https://github.com/clicklang/click/blob/master/mdtests/separation_subrange_supports_wide_bounds.md) covers unsigned 64-bit bounds.

### `separation::contains_element`

```click
theorem contains_element<T, I>(p: T*, lo: I, hi: I, i: I) {
    requires lo <= i;
    requires i < hi;
    ensures contains(memory(p[lo..hi]), memory(p[i]));
}
```

**Meaning:** An explicitly bounded index denotes a complete element inside its
interval. `I` is `int32` or `uint64`. The upper endpoint is exclusive. The rule
constructs the selected element address directly, preserving the pointer's
carrier and the inferred element width; it does not form a wrapping `i + 1`
endpoint, inspect memory, or search facts. It grants no ownership.

**Verified use:** [`mdtests/separation_element_contains_the_selected_cell.md`](https://github.com/clicklang/click/blob/master/mdtests/separation_element_contains_the_selected_cell.md).

## Namespace and extension rules

Library functions, predicates and theorems have qualified names, such as
`click::integer::multiply_add`, so a user declaration may share a library
declaration's bare name; the file then writes the library's by its path. A
selective import of a name the file also declares is refused. Library types,
constructors and resources keep bare names, which a user definition can't
redefine. A C function contract can have the same name as a library pure
function when no user Click definition creates a conflict.

To add a public symbol:

1. Add its declaration to the `library/` module for its topic.
2. Add a focused mdtest that uses it from an ordinary sidecar.
3. Add its semantic entry here; the inventory and exact-declaration checks fail
   until this page agrees with the source.
4. Add general prover or kernel support only when the definition exposes a
   reusable reasoning gap. Don't hard-code a domain-specific library name into
   the kernel merely because it is useful.
