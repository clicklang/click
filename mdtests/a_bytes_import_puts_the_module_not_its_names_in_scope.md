# a bytes import puts the module, not its names, in scope

After `import click::bytes;` a sidecar writes `bytes::all_equal`; the bare
`all_equal` needs a selective import.

```click
import click::bytes;

theorem zeroed(d: uint8[]) {
    requires all_equal(d, 0u64, 1u64, 0u8);
    ensures d[0u64] == 0u8;
}
```

```expect
fail: all_equal
```
