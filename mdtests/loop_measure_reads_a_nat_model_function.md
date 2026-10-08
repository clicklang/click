# a loop measure over a model can be a `Nat`

`decreases chain_nat(c.model);` ranks the loop by a structural natural number
computed from the binder's model. A `Nat` has no order of its own that a
ranking member can compare, so the measure ranks by its Integer image
`to_integer(chain_nat(c.model))`. The checked conversion law
`nat_integer_nonnegative` already states that image's nonnegativity, so the
bundle's nonnegativity member is closed by construction. Only the decrease is
owed, and `nat_integer_succ` turns the arm's `Nat::Succ` into the `+ 1` that
`arithmetic` compares. The `Integer` form of the same loop is
`loop_measure_reads_a_model_function.md`.

```c filename=loop_measure_reads_a_nat_model_function.c
void countdown(int32 n) {
    while (n > 0) {
        n = n - 1;
    }
}
```

```click
verifying "loop_measure_reads_a_nat_model_function.c";

spec enum Chain { Nil, Link(Chain) }

function chain_nat(m: Chain) -> Nat
    decreases m
{
    match m {
        Chain::Nil => Nat::Zero,
        Chain::Link(rest) => Nat::Succ(chain_nat(rest)),
    }
}

resource chain(k: int32) {
    field model: Chain;
    match model {
        Chain::Nil => { fact k == 0; },
        Chain::Link(rest_model) => {
            owns rest: chain(k - 1);
            fact k > 0;
            fact k - 1 >= 0;
            fact rest.model == rest_model;
        },
    }
}

void countdown(int32 n) {
    requires n >= 0;
    consumes c: chain(n);
    ensures 1 == 1;
} by {
    loop {
        owns c: chain(n);
        decreases chain_nat(c.model);
        invariant n >= 0;

        initialize by simp;
        preserve by {
            match c.model {
                Chain::Nil => { contradiction(c.model == Chain::Nil); },
                Chain::Link(rest_model) => {
                    have chain_nat(c.model) == Nat::Succ(chain_nat(rest_model)) by {
                        rewrite(c.model == Chain::Link(rest_model));
                        unfold(chain_nat(Chain::Link(rest_model)));
                        normalize();
                    }
                    apply(nat_integer_succ(chain_nat(rest_model)));
                    have to_integer(chain_nat(c.model)) == to_integer(chain_nat(rest_model)) + 1 by {
                        rewrite(chain_nat(c.model) == Nat::Succ(chain_nat(rest_model)));
                        assumption();
                    }
                    have to_integer(chain_nat(rest_model)) < to_integer(chain_nat(c.model)) by {
                        arithmetic() using {
                            to_integer(chain_nat(c.model)) == to_integer(chain_nat(rest_model)) + 1;
                        }
                    }
                    let { rest: r } = unfold(c);
                    step();
                    close_invariants();
                },
            }
        }
    }
    have n == 0;
    unfold(c);
    step();
    simp();
}
```

```expect
pass
```
