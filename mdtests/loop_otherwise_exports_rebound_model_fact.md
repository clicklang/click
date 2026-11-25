# An otherwise proof exports its fact about the rebound model

The guard-false path proves `pending(w.model) == 0` by eliminating the other
case of the invariant. The `break` path proves the same fact for the resource
it folds. The fact survives the join under the successor's model binding.

```c filename=loop_pointer_exit.c
void finish(int *p, int *stop) {
    while (p != stop)
        break;
}
```

```click
verifying "loop_pointer_exit.c";

spec enum Walk { Active, Done }

function pending(walk: Walk) -> int32 {
    match walk { Walk::Active => 1, Walk::Done => 0 }
}

resource walk_at() { field model: Walk; }

void finish(int32* p, int32* stop) {
    owns w: walk_at();
    requires address(p) != address(stop) or pending(w.model) == 0;
    ensures pending(w.model) == 0;
} by {
    loop {
        owns w: walk_at();
        decreases 0;
        invariant address(p) != address(stop) or pending(w.model) == 0;
        initialize by close();
        maintain by {
            unfold(w);
            let w = fold(walk_at(), { model: Walk::Done });
            have pending(w.model) == 0 by {
                rewrite(w.model, Walk::Done);
                unfold(pending(Walk::Done));
                close();
            }
            step();
        }
        otherwise {
            have pending(w.model) == 0 by {
                cases {
                    address(p) != address(stop) => { contradiction(address(p) != address(stop)); }
                    pending(w.model) == 0 => { close(); }
                }
            }
        }
    }
    have pending(w.model) == 0 by { close(); }
}
```

```expect
pass
```
