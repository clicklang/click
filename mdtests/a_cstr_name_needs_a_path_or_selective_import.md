# a cstr name needs a path or a selective import

After `import click::cstr;` a sidecar writes `cstr::readable`; the bare
`readable` is not in scope.

```click
import click::cstr;

theorem readable_by_bare_name(text: uint8[]) {
    requires readable(text);
    ensures 1 == 1;
}
```

```expect
fail: readable
```
