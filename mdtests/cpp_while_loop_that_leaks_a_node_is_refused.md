# A C++ while loop that drops a node without deleting it is refused

The loop of `cpp_while_loop_deletes_a_list.md` without its `delete`: each
iteration moves past a node it still owns, which the loop's resource no longer
describes, so the iteration does not return to the loop-head state.

```cpp filename=destroy.cpp function=destroy profile=normal_only
struct Node {
    int value;
    Node* next;
};

void destroy(Node* p) noexcept {
    while (p != nullptr) {
        Node* next = p->next;
        p = next;
    }
}
```

```click
import click::integer;
verifying "destroy.cpp";

resource nodes(p: Node*) {
    field items: List<int32>;
    match items {
        List::Nil => { fact p == 0; },
        List::Cons(value, rest) => {
            owns allocation(p, sizeof(Node));
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

void destroy(Node* p) {
    consumes list: nodes(p);
} by {
    loop {
        owns list: nodes(p);
        decreases length(list.items);

        initialize by simp();
        preserve by {
            match list.items {
                List::Nil => { contradiction(list.items == List<int32>::Nil); },
                List::Cons(value, rest) => {
                    let { tail: tail } = unfold(list);
                    unfold(length(List::Cons(value, rest)));
                    apply(length_nonnegative(rest));
                    have 0 <= length(tail.items) by simp();
                    have length(tail.items) < length(List::Cons(value, rest)) by arithmetic() using {
                        length(List::Cons(value, rest)) == length(rest) + 1;
                        tail.items == rest;
                    };
                    step();
                    step();
                    close_invariants();
                },
            }
        }
    }
    unfold(list);
    simp();
}
```

```expect
fail: loop state join changes resource ownership
```
