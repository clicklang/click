# `auto` does not read an unforced condition out of a generic definition

Following an end into its definition
([`auto_reads_a_condition_out_of_a_generic_bool_definition.md`](auto_reads_a_condition_out_of_a_generic_bool_definition.md))
reads a condition only when every way that fails it ends in a constant other
than the fact's. At `Cons(v, Cons(w, Nil))`, `list::contains(.., x)` is also
`true` when `w == x`, so the fact does not force `v == x`, and `auto` fails
promptly.

```click
import click::list;

theorem not_forced(v: int32, w: int32, x: int32) {
    requires list::contains(
        List<int32>::Cons(v, List<int32>::Cons(w, List<int32>::Nil)), x);
    ensures v == x by auto();
}
```

```expect
fail: could not establish `v == x`
```
