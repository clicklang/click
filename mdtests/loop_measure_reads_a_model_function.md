# a loop measure can be a function of a binder's model

`decreases chain_len(c.model);` ranks the loop by an `Integer` computed from
the loop binder's model, not by a C value and not by structural containment.
A structural measure needs the rebound instance to sit inside the one the
iteration started with; a measure over the model asks only that a number
computed from the models drops. That is what a loop needs when each step
re-folds its resource into a new instance rather than walking into a child.

At each continuing back edge the bundle owes the two ranking members an Integer
measure always owes: the value at the next head is at least zero, and it is
less than the value at this head. Both are ordinary goals, stated here with
`have` before `close_invariants()`. The head value is nameable because the arm
of `match c.model` the proof is in names the model's parts, and
`chain_len_is_nonnegative` is proved once by structural induction and applied
to the rebound model. A measure that also reads a C local, one that does not
decrease, one that can go negative, and one of a type with no order are each
refused (`loop_decreases_model_function_*.md`,
`loop_decreases_rejects_an_unordered_model.md`).

The C file is the strict-descendant countdown, which takes one or two links per
iteration, so the same measure has to decrease by one on one path and by two on
the other.

```c filename=loop_measure_reads_a_model_function.c
void countdown(int32 n) {
    while (n > 0) {
        n = n - 1;
        if (n > 0) {
            n = n - 1;
        }
    }
}
```

```click
verifying "loop_measure_reads_a_model_function.c";

spec enum Chain { Nil, Link(Chain) }

function chain_len(m: Chain) -> Integer
    decreases m
{
    match m {
        Chain::Nil => 0,
        Chain::Link(rest) => chain_len(rest) + 1,
    }
}

theorem chain_len_is_nonnegative(m: Chain) {
    ensures 0 <= chain_len(m) by {
        induct(m) as ih {
            Chain::Nil => {
                unfold(chain_len(Chain::Nil));
                normalize();
            }
            Chain::Link(rest) => {
                apply(ih(rest));
                unfold(chain_len(Chain::Link(rest)));
                arithmetic() using { 0 <= chain_len(rest); }
            }
        }
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
        decreases chain_len(c.model);
        invariant n >= 0;

        initialize by simp;
        preserve by {
            match c.model {
                Chain::Nil => { contradiction(c.model == Chain::Nil); },
                Chain::Link(rest_model) => {
                    have chain_len(c.model) == chain_len(rest_model) + 1 by {
                        rewrite(c.model == Chain::Link(rest_model));
                        unfold(chain_len(Chain::Link(rest_model)));
                        normalize();
                    }
                    match rest_model {
                        Chain::Nil => {
                            apply(chain_len_is_nonnegative(Chain::Nil));
                            have chain_len(c.model) == chain_len(Chain::Nil) + 1 by {
                                rewrite(c.model == Chain::Link(rest_model));
                                rewrite(rest_model == Chain::Nil);
                                unfold(chain_len(Chain::Link(Chain::Nil)));
                                normalize();
                            }
                            have chain_len(Chain::Nil) < chain_len(c.model) by {
                                arithmetic() using {
                                    chain_len(c.model) == chain_len(Chain::Nil) + 1;
                                }
                            }
                            let { rest: r } = unfold(c);
                            unfold(r);
                            step();
                            step();
                            step();
                            let c = fold(chain(n), { model: Chain::Nil });
                            close_invariants();
                        },
                        Chain::Link(rest2_model) => {
                            apply(chain_len_is_nonnegative(rest2_model));
                            have chain_len(rest_model) == chain_len(rest2_model) + 1 by {
                                rewrite(rest_model == Chain::Link(rest2_model));
                                unfold(chain_len(Chain::Link(rest2_model)));
                                normalize();
                            }
                            have chain_len(rest2_model) < chain_len(c.model) by {
                                arithmetic() using {
                                    chain_len(c.model) == chain_len(rest_model) + 1;
                                    chain_len(rest_model) == chain_len(rest2_model) + 1;
                                }
                            }
                            let { rest: r } = unfold(c);
                            let { rest: r2 } = unfold(r);
                            step();
                            step();
                            step();
                            close_invariants();
                        },
                    }
                },
            }
        }
    }
    have n == 0 by { simp(); }
    unfold(c);
    step();
    simp();
}
```

```expect
pass
```
