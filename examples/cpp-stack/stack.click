import click::integer;
verifying "stack.cpp";

resource nodes(p: Node<int>*) {
    field items: List<int32>;
    match items {
        List::Nil => { fact p == 0; },
        List::Cons(value, rest) => {
            owns allocation(p, sizeof(Node<int>));
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
                solve();
            }
            List::Cons(value, rest) => {
                apply(ih(rest));
                unfold(length(List<int32>::Cons(value, rest)));
                solve() using { length(rest) >= 0; };
            }
        }
    }
}

function first_or(xs: List<int32>, fallback: int32) -> int32 {
    match xs {
        List::Nil => fallback,
        List::Cons(value, rest) => value,
    }
}

function is_cons(xs: List<int32>) -> bool {
    match xs {
        List::Nil => false,
        List::Cons(value, rest) => true,
    }
}

function rest(xs: List<int32>) -> List<int32> {
    match xs {
        List::Nil => List<int32>::Nil,
        List::Cons(value, tail) => tail,
    }
}

void Stack<int>::push(int value) {
    owns *this;
    consumes before: nodes(this->head);
    produces after: nodes(this->head);
    requires length(before.items) < 1000000;
    requires to_integer(this->count) == length(before.items);
    ensures after.items == List::Cons(value, old(before.items));
    ensures to_integer(this->count) == length(after.items);
} by {
    step_until(function.exit);
    let after = fold(nodes(this->head), { items: List::Cons(value, old(before.items)) }, { tail: before });
    unfold(length(List::Cons(value, old(before.items))));
    have to_integer(old(this->count) + 1u64) == to_integer(old(this->count)) + to_integer(1u64);
    have to_integer(old(this->count) + 1u64) == length(List::Cons(value, old(before.items))) by solve() using {
        to_integer(old(this->count) + 1u64) == to_integer(old(this->count)) + to_integer(1u64);
        to_integer(old(this->count)) == length(old(before.items));
        length(List::Cons(value, old(before.items))) == length(old(before.items)) + 1;
    };
    solve();
}

bool Stack<int>::pop(int& out) {
    owns *this;
    owns out;
    consumes before: nodes(this->head);
    produces after: nodes(this->head);
    requires to_integer(this->count) == length(before.items);
    ensures result == is_cons(old(before.items));
    ensures out == first_or(old(before.items), old(out));
    ensures after.items == rest(old(before.items));
    ensures to_integer(this->count) == length(after.items);
} by {
    match before.items {
        List::Nil => {
            unfold(before);
            step_until(function.exit);
            let after = fold(nodes(this->head), { items: List<int32>::Nil });
            unfold(length(List<int32>::Nil));
            unfold(is_cons(List<int32>::Nil));
            unfold(first_or(List<int32>::Nil, old(out)));
            unfold(rest(List<int32>::Nil));
        },
        List::Cons(value, tail_items) => {
            let { tail: tail } = unfold(before);
            unfold(length(List::Cons(value, tail_items)));
            apply(length_nonnegative(tail_items));
            step_until(function.exit);
            unfold(is_cons(List::Cons(value, tail_items)));
            unfold(first_or(List::Cons(value, tail_items), old(out)));
            unfold(rest(List::Cons(value, tail_items)));
            match tail_items {
                List::Nil => {
                    unfold(tail);
                    let after = fold(nodes(this->head), { items: List<int32>::Nil });
                    unfold(length(List<int32>::Nil));
                    have length(tail_items) == 0 by solve();
                    have to_integer(old(this->count)) == 1 by solve() using {
                        to_integer(old(this->count)) == length(List::Cons(value, tail_items));
                        length(List::Cons(value, tail_items)) == length(tail_items) + 1;
                        length(tail_items) == 0;
                    };
                    solve();
                },
                List::Cons(next_value, next_items) => {
                    let { tail: next } = unfold(tail);
                    let after = fold(nodes(this->head), { items: List::Cons(next_value, next_items) }, { tail: next });
                    have to_integer(old(this->count)) == length(tail_items) + 1 by solve() using {
                        to_integer(old(this->count)) == length(List::Cons(value, tail_items));
                        length(List::Cons(value, tail_items)) == length(tail_items) + 1;
                    };
                    have to_integer(old(this->count) - 1u64) == to_integer(old(this->count)) - to_integer(1u64);
                    have to_integer(old(this->count) - 1u64) == length(tail_items) by solve() using {
                        to_integer(old(this->count) - 1u64) == to_integer(old(this->count)) - to_integer(1u64);
                        to_integer(old(this->count)) == length(tail_items) + 1;
                    };
                    solve();
                },
            }
        },
    }
}

unsigned long Stack<int>::size() const {
    views *this;
    ensures result == this->count;
}

Stack<int>::~Stack() {
    owns *this;
    consumes list: nodes(this->head);
} by {
    loop {
        owns *this;
        owns list: nodes(this->head);
        decreases length(list.items);

        initialize by solve();
        preserve by {
            match list.items {
                List::Nil => { contradiction(list.items == List<int32>::Nil); },
                List::Cons(value, rest) => {
                    let { tail: tail } = unfold(list);
                    unfold(length(List::Cons(value, rest)));
                    apply(length_nonnegative(rest));
                    have 0 <= length(tail.items) by solve();
                    have length(tail.items) < length(List::Cons(value, rest)) by solve() using {
                        length(List::Cons(value, rest)) == length(rest) + 1;
                        tail.items == rest;
                    };
                    step();
                    step();
                    step();
                    close_invariants();
                },
            }
        }
    }
    unfold(list);
    solve();
}

int round_trip(int x) {
    ensures result == x;
} by {
    step_until(region(2));
    let empty = fold(nodes(stack.head), { items: List<int32>::Nil });
    unfold(length(List<int32>::Nil));
    have length(List<int32>::Nil) < 1000000 by solve() using { length(List<int32>::Nil) == 0; };
    step_until(function.exit);
    unfold(length(List<int32>::Cons(x, List<int32>::Nil)));
    unfold(first_or(List<int32>::Cons(x, List<int32>::Nil), 0));
    solve();
}

unsigned long pushed_size(int x) {
    ensures to_integer(result) == 2;
} by {
    step_until(region(2));
    let empty = fold(nodes(stack.head), { items: List<int32>::Nil });
    unfold(length(List<int32>::Nil));
    have length(List<int32>::Nil) < 1000000 by solve() using { length(List<int32>::Nil) == 0; };
    step_until(region(3));
    unfold(length(List<int32>::Cons(x, List<int32>::Nil)));
    have length(List<int32>::Cons(x, List<int32>::Nil)) < 1000000 by solve() using {
        length(List<int32>::Cons(x, List<int32>::Nil)) == length(List<int32>::Nil) + 1;
        length(List<int32>::Nil) == 0;
    };
    step_until(function.exit);
    unfold(length(List<int32>::Cons(x, List<int32>::Cons(x, List<int32>::Nil))));
    have length(List<int32>::Cons(x, List<int32>::Cons(x, List<int32>::Nil))) == 2 by solve() using {
        length(List<int32>::Cons(x, List<int32>::Cons(x, List<int32>::Nil))) == length(List<int32>::Cons(x, List<int32>::Nil)) + 1;
        length(List<int32>::Cons(x, List<int32>::Nil)) == length(List<int32>::Nil) + 1;
        length(List<int32>::Nil) == 0;
    };
    solve();
}
