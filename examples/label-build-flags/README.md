# Label build flags

A synthetic two-file C library with an ordinary `Makefile`: the worked example
of [Verify a function in your own project](../../docs/concepts/own-project.md).
The C is written as a C programmer would write it and is not adapted to Click.

| File | Role |
| --- | --- |
| `Makefile` | The real build: `-Iinclude -DLABEL_CAPACITY=32` |
| `include/label_config.h` | `LABEL_CAPACITY`, default 16, overridden by `-D` |
| `label.h` | Public prototypes, beside the sources |
| `label_fit.c` | `label_fit`, which uses the configured capacity |
| `label_copy.c` | `label_measure` and `label_copy`, which call `strlen`, `memcpy`, and `label_fit` |
| `label.click` | One sidecar for both files |
| `click.project.json` | The project: one C unit for both files, with the build's flags |
| `click.project.lock.json`, `.click/label/` | The lock and preprocessed sources `click import lock` wrote |

`label.click` proves that `label_fit`'s result is below the build's capacity
of 32 and never exceeds the input length, and that `label_measure` returns
less than 32 for any readable C string. The unit passes the `Makefile`'s
`-Iinclude -DLABEL_CAPACITY=32` for both files; `<string.h>` in
`label_copy.c` resolves to Click's modeled header, so the `strlen` call is
checked against Click's library contract. The call to `label_fit` applies
`label_fit`'s verified contract.

`label_copy` also verifies: for a readable source string and a separate
32-byte destination buffer, it copies the bounded prefix, appends a terminator,
and returns an index below 32. The standard library model accepts its
`const char *` source without changing the C.

From this directory:

```sh
click import lock
click verify label.click
```

`make` builds `liblabel.a` with a host compiler; Click does not use the
`Makefile`. The lock and the preprocessed sources are committed, so
verification needs no compiler; `click import lock` refreshes them.
