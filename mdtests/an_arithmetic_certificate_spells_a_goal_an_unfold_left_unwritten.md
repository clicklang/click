# An arithmetic certificate spells a goal an unfold left unwritten

The first `unfold` spells `wrap`'s `int32` argument as `(v as int32)` in the
goal it rewrites, so the second, written with `v`, no longer finds its call in
that spelling and the goal keeps only its checked form. The goal mentions an
Integer spec call on the match arm's algebraic binder (`chain_size(rest)`) and
a constructor holding its pointer binder (`at`). Arithmetic spells that goal
from the checked state and the proof's locals to print its certificate. It
once reported the plan it found as "cannot be printed in source form".

```c filename=unwritten_goal.c
void f(int32 *q) {
    return;
}
```

```click
verifying "unwritten_goal.c";
spec enum Chain { Leaf, Link(int32*, int32, Chain) }
function chain_size(c: Chain) -> Integer
    decreases c
{
    match c {
        Chain::Leaf => 0,
        Chain::Link(at, v, rest) => 1 + chain_size(rest),
    }
}
function wrap(at: int32*, v: int32, c: Chain) -> Chain {
    Chain::Link(at, v, c)
}
function weight(c: Chain) -> Integer {
    chain_size(c) + 1
}
resource holder(p: int32*) {
    field model: Chain;
    owns *p;
}
void f(int32* q) {
    owns h: holder(q);
    ensures true;
} by {
    match h.model {
        Chain::Leaf => { step_until(function.exit); },
        Chain::Link(at, v, rest) => {
            have chain_size(Chain::Link(at, v, rest)) == 1 + chain_size(rest) by {
                unfold(chain_size(Chain::Link(at, v, rest)));
                normalize();
            }
            have weight(wrap(at, v, rest)) == chain_size(rest) + 2 by {
                unfold(wrap(at, v, rest));
                unfold(weight(Chain::Link(at, v, rest)));
                solve() using {
                    chain_size(Chain::Link(at, v, rest)) == 1 + chain_size(rest);
                };
            }
            step_until(function.exit);
        },
    }
}
```

```expect
pass
```
