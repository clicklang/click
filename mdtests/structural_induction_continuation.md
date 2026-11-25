# A structural match can continue with proof steps

```click
spec enum Chain { Nil, Link(Chain) }
function copy_chain(xs: Chain) -> Chain decreases xs {
    match xs {
        Chain::Nil => Chain::Nil,
        Chain::Link(tail) => Chain::Link(copy_chain(tail)),
    }
}

theorem continuation(xs: Chain) {
    ensures copy_chain(xs) == xs by {
        let ih = induct(xs);
        match xs {
            Chain::Nil => {
                have copy_chain(xs) == xs by {
                    rewrite(xs, Chain::Nil);
                    unfold(copy_chain(Chain::Nil));
                    close();
                }
            }
            Chain::Link(tail) => {
                apply(ih(tail));
                have copy_chain(xs) == xs by {
                    rewrite(xs, Chain::Link(tail));
                    unfold(copy_chain(Chain::Link(tail)));
                    rewrite(copy_chain(tail), tail);
                    close();
                }
            }
        }
        have xs == xs by close();
        close();
    }
}
```

```expect
pass
```
