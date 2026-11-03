# library vec axioms

A `Vec<T>` is a primitive library type: a proof reaches its meaning by citing
the library's axioms about `vec::len`, `vec::get`, `vec::push` and `vec::set`.

```click
import click::rust::vec;

theorem push_then_read(v: Vec<uint32>, x: uint32, i: uint64) {
    requires vec::len(v) < 10u64;
    requires i < vec::len(v);
    ensures vec::len(vec::push(v, x)) == vec::len(v) + 1 by {
        have vec::len(v) < 18446744073709551615u64 by { solve(); }
        apply(vec::len_push(v, x));
    }
    ensures vec::get(vec::push(v, x), vec::len(v)) == x by {
        have vec::len(v) < 18446744073709551615u64 by { solve(); }
        apply(vec::get_push_last(v, x));
    }
    ensures vec::get(vec::push(v, x), i) == vec::get(v, i) by {
        apply(vec::get_push_kept(v, x, i));
    }
}

theorem set_then_read<T>(v: Vec<T>, i: uint64, j: uint64, x: T) {
    requires i < vec::len(v);
    requires j < vec::len(v);
    requires i != j;
    ensures vec::len(vec::set(v, i, x)) == vec::len(v) by {
        apply(vec::len_set(v, i, x));
    }
    ensures vec::get(vec::set(v, i, x), i) == x by {
        apply(vec::get_set_same(v, i, x));
    }
    ensures vec::get(vec::set(v, i, x), j) == vec::get(v, j) by {
        apply(vec::get_set_other(v, i, j, x));
    }
}

theorem same_values_same_vector(v: Vec<int32>, w: Vec<int32>) {
    requires vec::len(v) == vec::len(w);
    requires forall (i: uint64) { i < vec::len(v) implies vec::get(v, i) == vec::get(w, i) };
    ensures v == w by {
        apply(vec::extensionality(v, w));
    }
}
```

```expect
pass
```
