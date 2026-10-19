# Closing a refuted `implies` after execution searches for seconds

Soundness: not soundness. The claim verifies; only the time to close it is
wrong.

A postcondition `ensures old(m) == List<int32>::Nil implies P` on a path whose
proof matched `m` as `List::Cons(...)` holds because its antecedent is
false. After execution, the closing `simp` takes seconds to find that,
spending its time in "simp closure: premise spelling" (about 1M work units a
call in the C++ form). Stating the same fact before execution,
`have old(before.items) != List<int32>::Nil by simp();` at the top of the
`Cons` arm, makes the whole proof as fast as without the clause. The
proof-failure triage rules expect a smart search to miss or succeed promptly;
this one is slow when it succeeds.

Measured on master `6ac2083ad` (the merge of #1574) with the C++ `new`/`delete`
change on top, debug build:

| `pop` proof | time |
| --- | --- |
| without the `== Nil implies` clause | 2.2 s |
| with it | 7.5 s |
| with it and the early `have` | 2.2 s |
| the same clause in the C++ `Stack<int>::pop` of `issues/generic-stack.md` | 28 s (2.4 s with the early `have`) |

Each of the three `== Nil implies` clauses of that C++ `pop` costs 20 to 30
seconds; the matching `!= Nil implies` clauses close in about a second.

Reproduction, `pop.c`:

```c
struct node { int value; struct node *next; };
struct stack { struct node *head; unsigned long count; };
_Bool pop(struct stack *s, int *out) {
    if (s->head == 0) {
        return 0;
    }
    struct node *node = s->head;
    *out = node->value;
    s->head = node->next;
    free(node);
    s->count = s->count - 1;
    return 1;
}
```

`pop.click`:

```click
import click::integer;
verifying "pop.c";

resource nodes(p: struct node*) {
    field items: List<int32>;
    match items {
        List::Nil => { fact p == 0; },
        List::Cons(value, rest) => {
            owns allocation(p, sizeof(struct node));
            owns *p;
            owns tail: nodes(p->next);
            fact p != 0;
            fact aligned(p, 8);
            fact p->value == value;
            fact tail.items == rest;
        },
    }
}

function length(xs: List<int32>) -> Integer
    decreases xs
{
    match xs {
        List::Nil => 0,
        List::Cons(value, rest) => length(rest) + 1,
    }
}

theorem length_nonnegative(xs: List<int32>) {
    ensures length(xs) >= 0 by {
        induct(xs) as ih {
            List::Nil => {
                unfold(length(List<int32>::Nil));
                simp();
            }
            List::Cons(value, rest) => {
                apply(ih(rest));
                unfold(length(List<int32>::Cons(value, rest)));
                arithmetic() using { length(rest) >= 0; };
            }
        }
    }
}

function first(xs: List<int32>) -> int32 {
    match xs {
        List::Nil => 0,
        List::Cons(value, rest) => value,
    }
}

function rest(xs: List<int32>) -> List<int32> {
    match xs {
        List::Nil => List<int32>::Nil,
        List::Cons(value, tail) => tail,
    }
}

bool pop(struct stack* s, int32* out) {
    owns *s;
    owns *out;
    consumes before: nodes(s->head);
    produces after: nodes(s->head);
    requires to_integer(s->count) == length(before.items);
    ensures old(before.items) == List<int32>::Nil implies result == false;
    ensures to_integer(s->count) == length(after.items);
} by {
    match before.items {
        List::Nil => {
            unfold(before);
            execute();
            let after = fold(nodes(s->head), { items: List<int32>::Nil });
            unfold(length(List<int32>::Nil));
        },
        List::Cons(value, tail_items) => {
            let { tail: tail } = unfold(before);
            unfold(length(List::Cons(value, tail_items)));
            apply(length_nonnegative(tail_items));
            execute();
            unfold(first(List::Cons(value, tail_items)));
            unfold(rest(List::Cons(value, tail_items)));
            match tail_items {
                List::Nil => {
                    unfold(tail);
                    let after = fold(nodes(s->head), { items: List<int32>::Nil });
                    unfold(length(List<int32>::Nil));
                    have length(tail_items) == 0 by simp();
                    have to_integer(old(s->count)) == 1 by arithmetic() using {
                        to_integer(old(s->count)) == length(List::Cons(value, tail_items));
                        length(List::Cons(value, tail_items)) == length(tail_items) + 1;
                        length(tail_items) == 0;
                    };
                    simp();
                },
                List::Cons(next_value, next_items) => {
                    let { tail: next } = unfold(tail);
                    let after = fold(nodes(s->head), { items: List::Cons(next_value, next_items) }, { tail: next });
                    have to_integer(old(s->count)) == length(tail_items) + 1 by arithmetic() using {
                        to_integer(old(s->count)) == length(List::Cons(value, tail_items));
                        length(List::Cons(value, tail_items)) == length(tail_items) + 1;
                    };
                    apply(uint64_subtract_to_integer(old(s->count), 1u64));
                    have to_integer(old(s->count) - 1u64) == length(tail_items) by arithmetic() using {
                        to_integer(old(s->count) - 1u64) == to_integer(old(s->count)) - to_integer(1u64);
                        to_integer(old(s->count)) == length(tail_items) + 1;
                    };
                    simp();
                },
            }
        },
    }
}
```

`click profile pop.click` shows the time under "post-execution claim tactics"
and "simp closure: premise spelling".

Acceptance criteria:

- The reproduction verifies within a second of the version without the
  clause, without the early `have`.
- A focused trace of the closing search shows where the time goes, and the
  fix removes that cost rather than lowering a search limit.
- A regression keeps the `pop` proof above and bounds its work.
