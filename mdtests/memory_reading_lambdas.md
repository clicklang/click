# Memory-reading lambdas use the application state

Capturing a pointer preserves its value, while each application reads the
selected memory state. Guarded range bodies use the same read obligations
as the unannotated range shorthands.

```c filename=memory_lambdas.c
void write(int32* p) { p[0] = 5; }
int32 first(int32* p, int32* q) { return p[0]; }
int32 unchanged(int32* p, int32 lo, int32 hi) { return 0; }
```

```click
verifying "memory_lambdas.c";

function captured_pointer(p: int32*, q: int32*) -> int32 {
    let read = |i: int32| -> int32 { p[i] };
    let p = q;
    read(0)
}

function read_helper(p: int32*, i: int32) -> int32 { p[i] }
predicate is_zero(p: int32*, i: int32) { p[i] == 0 }

function typed_sum(p: int32*, lo: int32, hi: int32) -> Integer {
    let add = |acc: Integer, i: int32| -> Integer { acc + to_integer(p[i]) };
    (lo..hi).fold(0, add)
}

function shorthand_sum(p: int32*, lo: int32, hi: int32) -> Integer {
    (lo..hi).fold(0, |acc, i| { acc + to_integer(p[i]) })
}

void write(int32* p) {
    let read = |i: int32| -> int32 { p[i] };
    let five = |i: int32| -> Prop { p[i] == 5 };
    let wide = |i: int32| -> Integer { to_integer(p[i]) };
    let frozen: Integer = to_integer(old(p[0]));
    let saved = || -> Integer { frozen };
    owns p[0..1];
    requires read(0) == 0;
    ensures read(0) == 5;
    ensures five(0);
    ensures wide(0) == 5;
    ensures old(read(0)) == 0;
    ensures saved() == 0;
}

int32 first(int32* p, int32* q) {
    views p[0..1];
    ensures result == captured_pointer(p, q) by {
        step_until(function.exit);
        unfold(captured_pointer(p, q));
        solve();
    }
    ensures result == (|i: int32| -> int32 { read_helper(p, i) })(0) by {
        step_until(function.exit);
        unfold(read_helper(p, 0));
        solve();
    }
}

int32 unchanged(int32* p, int32 lo, int32 hi) {
    let zero = |i: int32| -> Prop { p[i] == 0 };
    requires 0 <= lo and lo < hi;
    views p[lo..hi];
    requires (lo..hi).all(zero);
    ensures (lo..hi).all(zero);
    ensures (lo..hi).any(zero) by {
        step_until(function.exit);
        have p[lo] == 0 by {
            instantiate((lo..hi).all(|i: int32| -> Prop { p[i] == 0 }), lo);
            solve();
        }
        witness(lo);
        solve();
    }
    ensures (|i: int32| -> Prop { is_zero(p, i) })(lo) by {
        step_until(function.exit);
        have is_zero(p, lo) by {
            unfold(is_zero(p, lo));
            instantiate((lo..hi).all(|i: int32| -> Prop { p[i] == 0 }), lo);
            solve();
        }
        solve();
    }
    ensures typed_sum(p, lo, hi) == shorthand_sum(p, lo, hi) by {
        step_until(function.exit);
        unfold(typed_sum(p, lo, hi));
        unfold(shorthand_sum(p, lo, hi));
        solve();
    }
}

theorem application_read_validity(p: int32*) {
    let read = |i: int32| -> int32 { p[i] };
    requires defined(p[1]);
    ensures defined(read(1)) by solve();
}

theorem unused_read_needs_no_view(p: int32*) {
    let unused = |i: int32| -> Prop { p[i] == 0 };
    ensures true by solve();
}
```

```expect
pass
```
