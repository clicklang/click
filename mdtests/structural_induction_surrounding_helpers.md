# Structural induction retains surrounding helpers and match continuations

A declaration introduces the hypothesis at its written position. Helper facts
before and after it survive the ordinary match, whose arms can continue into
shared proof steps. A helper named `ih` before the local declaration remains
an ordinary theorem application.

```click
spec enum Chain { Nil, Link(Chain) }
function copy_chain(xs: Chain) -> Chain decreases xs {
    match xs {
        Chain::Nil => Chain::Nil,
        Chain::Link(tail) => Chain::Link(copy_chain(tail)),
    }
}
theorem ih(n: int32) { ensures n == n by known(); }

theorem surrounding(xs: Chain, n: int32) {
    requires n >= 0;
    ensures copy_chain(xs) == xs by {
        have before: n >= 0 by known();
        apply(ih(n));
        let ih = induct(xs);
        have between: n >= 0 by solve() using { before; };
        match xs {
            Chain::Nil => { unfold(copy_chain(Chain::Nil)); }
            Chain::Link(tail) => {
                apply(ih(tail));
                unfold(copy_chain(Chain::Link(tail)));
            }
        }
        known();
    }
}

theorem match_in_helper(xs: Chain) {
    ensures copy_chain(xs) == xs by {
        have before: xs == xs by known();
        let ih = induct(xs);
        have answer: copy_chain(xs) == xs by {
            match xs {
                Chain::Nil => { unfold(copy_chain(Chain::Nil)); known(); }
                Chain::Link(tail) => {
                    apply(ih(tail));
                    unfold(copy_chain(Chain::Link(tail)));
                    known();
                }
            }
        }
        known();
    }
}

theorem branch_before_declaration(xs: Chain, n: int32) {
    requires n >= 0;
    ensures copy_chain(xs) == xs by {
        if n == 0 { have n >= 0 by known(); }
        else { have n >= 0 by known(); }
        let ih = induct(xs);
        match xs {
            Chain::Nil => { unfold(copy_chain(Chain::Nil)); }
            Chain::Link(tail) => {
                apply(ih(tail));
                unfold(copy_chain(Chain::Link(tail)));
            }
        }
        known();
    }
}

theorem branch_after_declaration(xs: Chain, n: int32) {
    requires n >= 0;
    ensures copy_chain(xs) == xs by {
        let ih = induct(xs);
        if n == 0 { have n >= 0 by known(); }
        else { have n >= 0 by known(); }
        match xs {
            Chain::Nil => { unfold(copy_chain(Chain::Nil)); }
            Chain::Link(tail) => {
                apply(ih(tail));
                unfold(copy_chain(Chain::Link(tail)));
            }
        }
        known();
    }
}

```

```expect
pass
```
