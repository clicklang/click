# an Integer field bound by a proof `match` is an Integer

`match c.model { Walk::At(wd, rest) => ... }` binds `wd` to the model's
`Integer` field. The arm recorded the binding as an Integer, but stating a fact
about it in a C function's proof lowered the proposition without the arm's
Integer bindings. `have depth(c.model) == wd` was refused because Integer
expressions cannot be compared with C values, and `unfold(depth(..wd..))`
because `wd` was not an Integer binding. Both now read the arm's Integer
bindings, as they already read its algebraic ones, and the field takes part in
`arithmetic` like any other Integer.

```c filename=an_integer_field_bound_by_a_proof_match_is_an_integer.c
void touch(int32 n) {
}
```

```click
verifying "an_integer_field_bound_by_a_proof_match_is_an_integer.c";

spec enum Walk { At(Integer, Walk), Done }

function depth(w: Walk) -> Integer {
    match w { Walk::At(wd, rest) => wd, Walk::Done => 0 }
}

resource token(k: int32) {
    field model: Walk;
}

void touch(int32 n) {
    owns c: token(n);
    requires depth(c.model) == 3;
    ensures 1 == 1;
} by {
    match c.model {
        Walk::At(wd, rest) => {
            have depth(c.model) == wd by {
                rewrite(c.model == Walk::At(wd, rest));
                unfold(depth(Walk::At(wd, rest)));
                normalize();
            }
            have wd == 3 by {
                arithmetic() using { depth(c.model) == wd; depth(c.model) == 3; }
            }
            step();
            step();
            simp();
        },
        Walk::Done => {
            step();
            step();
            simp();
        },
    }
}
```

```expect
pass
```
