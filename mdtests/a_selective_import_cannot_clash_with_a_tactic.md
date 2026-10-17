# A selectively imported name cannot clash with a file's tactic

Like [`a_selective_import_cannot_clash_with_a_file_declaration.md`](a_selective_import_cannot_clash_with_a_file_declaration.md),
for a `tactic`. Before, the declaration and its call were both renamed to the
library's `append` and the proof verified.

```c filename=t.c
int f(int x) { return x; }
```

```click
verifying "t.c";
import click::list::{append};

tactic append(x: int32) {
    requires x == 1;
    ensures x + 1 == 2;
} by { have x + 1 == 2; }

int f(int x) {
    requires x == 1;
    ensures result + 1 == 2;
} by { append(x); execute(); simp(); }
```

```expect
fail: `append` is imported from `click::list` and also declared in this file
```
