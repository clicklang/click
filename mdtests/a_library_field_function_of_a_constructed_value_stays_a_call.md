# A library field function of a constructed value stays a call

A library function whose body is `match o { V(.., x, ..) => x, ... }`, as
`option::unwrap_or` is, lowers as the call that was written, like any other
function: `option::unwrap_or(Option<uint64>::Some(m), d)` is a call, not `m`.
`unfold` opens it to the constructor's field. The goal is therefore the same
term whether the constructed value is written at the call or arrives by
`rewrite`, and the same `unfold` opens it in both.

```click
import click::rust::option;

spec enum Pair {
    Pair(uint64, uint64),
}

function second(p: Pair) -> uint64 {
    match p {
        Pair::Pair(_, b) => b,
    }
}

theorem a_program_function_stays_a_call(a: uint64) {
    ensures second(Pair::Pair(a, 7u64)) == 7u64 by {
        unfold(second(Pair::Pair(a, 7u64)));
        close();
    }
}

theorem from_its_parts(m: uint64, d: uint64) {
    ensures option::unwrap_or(Option<uint64>::Some(m), d) == m by {
        unfold(option::unwrap_or(Option<uint64>::Some(m), d));
        close();
    }
}

theorem after_a_rewrite(o: Option<uint64>, m: uint64, d: uint64) {
    requires o == Option<uint64>::Some(m);
    ensures option::unwrap_or(o, d) == m by {
        rewrite(o, Option<uint64>::Some(m));
        unfold(option::unwrap_or(Option<uint64>::Some(m), d));
        close();
    }
}

theorem an_opaque_option(o: Option<uint64>, d: uint64) {
    requires o == Option<uint64>::Some(3u64);
    ensures option::unwrap_or(o, d) == 3u64 by {
        unfold(option::unwrap_or(o, d));
        close();
    }
}
```

```expect
pass
```
