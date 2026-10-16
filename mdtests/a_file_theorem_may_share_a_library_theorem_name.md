# a file theorem may share a library theorem's name

Library theorems have qualified identities, so a file may declare a theorem
with a library theorem's bare name. A bare citation names the file's own
theorem, a path names the library's, and built-in tactics keep using the
library's.

```click
import click::machine_integer;

theorem uint32_less_than_transitive(a: uint32) {
    ensures a == a by simp();
}

theorem own_by_bare_name(a: uint32) {
    ensures a == a by apply(uint32_less_than_transitive(a));
}

theorem library_by_path(a: uint32, b: uint32, c: uint32) {
    requires a < b;
    requires b < c;
    ensures a < c by apply(machine_integer::uint32_less_than_transitive(a, b, c));
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
