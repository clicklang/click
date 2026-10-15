# a selectively imported name cannot clash with a file declaration

The negative twin of
[`a_selective_import_brings_bare_library_names.md`](a_selective_import_brings_bare_library_names.md).
As with Rust's explicit `use`, importing `append` while the file declares its
own `append` is an error rather than a choice between them.

```click
import click::list::{append};

function append(x: int32) -> int32 {
    x + 1
}
```

```expect
fail: `append` is imported from `click::list` and also declared in this file
```
