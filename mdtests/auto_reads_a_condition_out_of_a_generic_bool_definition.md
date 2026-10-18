# `auto` reads a condition out of a generic `bool` definition

The definition reading of
[`auto_reads_a_condition_out_of_a_definition.md`](auto_reads_a_condition_out_of_a_definition.md)
also applies to a generic function, to a `bool` result, and through an end
that applies a function its arguments decide. `list::contains` is generic and
returns `bool`; at `Cons(v, Nil)` its `else` end is `list::contains(Nil, x)`,
which `auto` follows into the definition to `false`. So the fact
`list::contains(Cons(v, Nil), x)` forces `v == x`. The proof `auto` writes is
the one written by hand: `if v == x`, `assumption`; otherwise
`have not list::contains(..)` by unfolding both applications and normalizing
with `not (v == x)`, then `contradiction`.

The fact may name the list through a connected equation, and the goal may be
a postcondition spelled over `result`.

```c filename=pick.c
int pick(int *p, int v, int x) {
    return v;
}
```

```click
verifying "pick.c";
import click::list;

theorem only_element(v: int32, x: int32) {
    requires list::contains(List<int32>::Cons(v, List<int32>::Nil), x);
    ensures v == x by auto();
}

theorem through_a_constructor_equation(items: List<int32>, v: int32, x: int32) {
    requires items == List<int32>::Cons(v, List<int32>::Nil);
    requires list::contains(items, x);
    ensures v == x by auto();
}

abstract resource holder(p: int32*) { field items: List<int32>; }

int pick(int32* p, int32 v, int32 x) {
    owns h: holder(p);
    requires h.items == List<int32>::Cons(v, List<int32>::Nil);
    requires list::contains(h.items, x);
    ensures result == x;
} by auto();
```

```expect
pass
```
