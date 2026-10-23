# a file theorem may share a library theorem's name

Library theorems have qualified identities, so a file may declare a theorem
with a library theorem's bare name. A bare citation names the file's own
theorem, a path names the library's, and built-in tactics are unaffected by
the file's theorem.

```click
import click::integer;

theorem multiply_add(a: uint32) {
    ensures a == a by simp();
}

theorem own_by_bare_name(a: uint32) {
    ensures a == a by apply(multiply_add(a));
}

theorem library_by_path(a: Integer, b: Integer, c: Integer) {
    ensures (a + b) * c == a * c + b * c by apply(integer::multiply_add(a, b, c));
}

theorem library_through_a_tactic(a: uint32, b: uint32, c: uint32) {
    requires a < b;
    requires b < c;
    ensures a < c by simp();
}
```

```expect
pass
```
