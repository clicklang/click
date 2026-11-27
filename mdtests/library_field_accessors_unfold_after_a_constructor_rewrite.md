# Library field accessors unfold after a constructor rewrite

A library accessor stays a pure-function call when a rewrite replaces its
symbolic argument with a constructor. The same explicit `unfold` works before
or after that rewrite. Previously lowering reduced a library accessor on a
constructor to its field, but rewriting retained the call; the subsequent
`unfold` only added `true`.

```click
import click::rust::option;

theorem payload_after_rewrite(o: Option<uint64>, m: uint64, d: uint64) {
    requires o == Option<uint64>::Some(m);
    ensures option::unwrap_or(o, d) == m by {
        rewrite(o, Option<uint64>::Some(m));
        unfold(option::unwrap_or(Option<uint64>::Some(m), d));
        close();
    }
    ensures option::unwrap_or(o, d) == m by {
        unfold(option::unwrap_or(o, d));
        rewrite(o, Option<uint64>::Some(m));
        close();
    }
}

theorem direct_payload(m: uint64, d: uint64) {
    ensures option::unwrap_or(Option<uint64>::Some(m), d) == m by {
        unfold(option::unwrap_or(Option<uint64>::Some(m), d));
        close();
    }
    ensures option::unwrap_or(Option<uint64>::None, d) == d by {
        unfold(option::unwrap_or(Option<uint64>::None, d));
        close();
    }
}
```

```expect
pass
```
