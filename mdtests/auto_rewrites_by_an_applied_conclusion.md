# `auto` rewrites by an applied theorem's conclusion

`apply(append_nil(xs));` adds `append(xs, IntList::Nil) == xs` as a fact.
When the application closes no goal, that fact stays in the proof for later
steps. A step that needs exactly that fact finds it without a spelling, so
`have ys == xs by auto()` beside `ys == append(xs, IntList::Nil)` already
worked. Using it any other way, such as the reversed equality
`xs == append(xs, IntList::Nil)`, takes a `rewrite` step that cites the fact,
and `auto` can only write a `rewrite` for a fact with a source spelling. An
`apply` that closed a goal was spelled; one partway through a proof was not,
so its author restated the conclusion as a `have`. Each conclusion of such
an application is now spelled the way the caller would write it: the
theorem's `ensures` with the application's arguments substituted. The last
theorem is the rbtree model's shape: the application inside an `induct` arm.

`auto` cannot prove `append(xs, IntList::Nil) == xs` itself, since it needs
induction; it can only use the applied lemma.

```click
spec enum IntList {
    Nil,
    Cons(int, IntList),
}

function append(xs: IntList, ys: IntList) -> IntList
    decreases xs
{
    match xs {
        IntList::Nil => ys,
        IntList::Cons(head, tail) => IntList::Cons(head, append(tail, ys)),
    }
}

theorem append_nil(xs: IntList) {
    ensures append(xs, IntList::Nil) == xs by {
        induct(xs) as ih {
            IntList::Nil => {
                unfold(append(IntList::Nil, IntList::Nil));
                simp();
            }
            IntList::Cons(head, tail) => {
                apply(ih(tail));
                unfold(append(IntList::Cons(head, tail), IntList::Nil));
                rewrite(append(tail, IntList::Nil) == tail);
                normalize();
            }
        }
    }
}

theorem rewrite_by_the_applied_lemma(xs: IntList, ys: IntList) {
    requires ys == append(xs, IntList::Nil);
    ensures ys == xs by {
        apply(append_nil(xs));
        have ys == xs by auto();
        assumption();
    }
}
theorem reversed(xs: IntList) {
    ensures xs == append(xs, IntList::Nil) by {
        apply(append_nil(xs));
        have xs == append(xs, IntList::Nil) by auto();
        assumption();
    }
}

spec enum Flag { On, Off }

theorem reversed_in_an_induction_arm(flag: Flag, xs: IntList) {
    ensures xs == append(xs, IntList::Nil) by {
        induct(flag) as ih {
            Flag::On => {
                apply(append_nil(xs));
                have xs == append(xs, IntList::Nil) by auto();
                assumption();
            }
            Flag::Off => {
                apply(append_nil(xs));
                have xs == append(xs, IntList::Nil) by auto();
                assumption();
            }
        }
    }
}
```

```expect
pass
```
