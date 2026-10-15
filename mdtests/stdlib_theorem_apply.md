# standard-library theorem application

This checks that pure theorem proofs can apply theorem declarations from the
standard library.

```click
import click::cstr;

theorem user_reuses_cstr_len_has_prefix(bytes: uint8[], len: uint64) {
    requires cstr::len(bytes, len);

    ensures cstr::prefix(bytes, len) by {
        apply(cstr::len_has_prefix(bytes, len));
        simp();
    }
}
```

```expect
pass
```
