# Library field accessors unfold after a constructor rewrite

A library accessor stays a pure-function call when a rewrite replaces its
symbolic argument with a constructor. The same explicit `unfold` works before
or after that rewrite, for both the slice length and its pointer field.
Previously lowering reduced a library accessor on a constructor to its field,
but rewriting retained the call; the subsequent `unfold` only added `true`.

```click
import click::rust::slice;

theorem slice_fields_after_rewrite(s: Slice<uint8>, p: uint8*, n: uint64) {
    requires s == Slice<uint8>::Slice(p, n);
    ensures slice::len(s) == n by {
        rewrite(s == Slice<uint8>::Slice(p, n));
        unfold(slice::len(Slice<uint8>::Slice(p, n)));
        normalize();
    }
    ensures slice::as_ptr(s) == p by {
        rewrite(s == Slice<uint8>::Slice(p, n));
        unfold(slice::as_ptr(Slice<uint8>::Slice(p, n)));
        normalize();
    }
    ensures slice::len(s) == n by {
        unfold(slice::len(s));
        rewrite(s == Slice<uint8>::Slice(p, n));
        normalize();
    }
}

theorem direct_slice_fields(p: uint8*, n: uint64) {
    ensures slice::len(Slice<uint8>::Slice(p, n)) == n by {
        unfold(slice::len(Slice<uint8>::Slice(p, n)));
        normalize();
    }
    ensures slice::as_ptr(Slice<uint8>::Slice(p, n)) == p by {
        unfold(slice::as_ptr(Slice<uint8>::Slice(p, n)));
        normalize();
    }
}
```

```expect
pass
```
