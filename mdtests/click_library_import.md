# a Click library module is imported by its `click::` path

`import click::cstr;` names `library/cstr.click`. Every library module is
still loaded implicitly, so the import checks that its module exists and the
proof uses the module's theorem as before. Importing a module twice, or a
nested module such as `click::c::string`, is accepted.

```click
import click::cstr;
import click::c::string;
import click::cstr;

theorem imported_cstr_len_is_viewable(bytes: uint8[], len: uint64) {
    requires cstr_len(bytes, len);

    ensures viewable(bytes[0..len + 1u64]) by {
        apply(cstr_len_is_viewable(bytes, len));
    }
}
```

```expect
pass
```
