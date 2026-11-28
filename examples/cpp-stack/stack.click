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
        let ih = induct(xs);
        match xs {
            List::Nil => {
                unfold(length(List<int32>::Nil));
                close();
            }
            List::Cons(value, rest) => {
                apply(ih(rest));
                unfold(length(List<int32>::Cons(value, rest)));
                close() using { length(rest) >= 0; };
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

function is_cons(xs: List<int32>) -> Bool {
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
    let after = fold(nodes(this->head), { items: List::Cons(value, old(before.items)), tail: before });
    unfold(length(List::Cons(value, old(before.items))));
    have to_integer(old(this->count) + 1u64) == to_integer(old(this->count)) + to_integer(1u64);
    have to_integer(old(this->count) + 1u64) == length(List::Cons(value, old(before.items))) by {
        rewrite(to_integer(old(this->count) + 1u64), to_integer(old(this->count)) + to_integer(1u64));
        rewrite(to_integer(old(this->count)), length(old(before.items)));
        rewrite(length(List::Cons(value, old(before.items))), length(old(before.items)) + 1);
        close();
    }
    close();
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
                    have length(tail_items) == 0 by close();
                    have to_integer(old(this->count)) == 1 by close() using {
                        to_integer(old(this->count)) == length(List::Cons(value, tail_items));
                        length(List::Cons(value, tail_items)) == length(tail_items) + 1;
                        length(tail_items) == 0;
                    };
                    close();
                },
                List::Cons(next_value, next_items) => {
                    let { tail: next } = unfold(tail);
                    let after = fold(nodes(this->head), { items: List::Cons(next_value, next_items), tail: next });
                    have to_integer(old(this->count)) == length(tail_items) + 1 by {
                        rewrite(to_integer(old(this->count)), length(List::Cons(value, tail_items)));
                        close();
                    }
                    have to_integer(old(this->count) - 1u64) == to_integer(old(this->count)) - to_integer(1u64);
                    have to_integer(old(this->count) - 1u64) == length(tail_items) by close() using {
                        to_integer(old(this->count) - 1u64) == to_integer(old(this->count)) - to_integer(1u64);
                        to_integer(old(this->count)) == length(tail_items) + 1;
                    };
                    close();
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

        initialize by close();
        maintain by {
            match list.items {
                List::Nil => { close(); },
                List::Cons(value, rest) => {
                    let { tail: tail } = unfold(list);
                    unfold(length(List::Cons(value, rest)));
                    apply(length_nonnegative(rest));
                    have 0 <= length(tail.items) by close();
                    have length(tail.items) < length(List::Cons(value, rest)) by close() using {
                        length(List::Cons(value, rest)) == length(rest) + 1;
                        tail.items == rest;
                    };
                    mark before_node;
                    step();
                    have separate(region(1).footprint, memory(this->head)) by { close() using {}; }
                    have this->head == at(before_node, this->head) by {
                        preserve(memory(this->head), region(1));
                    }
                    have separate(region(1).footprint, memory(this->head->next)) by { close() using {}; }
                    have this->head->next == at(before_node, this->head->next) by {
                        preserve(memory(this->head->next), region(1));
                    }
                    have node == this->head by { close(); }
                    step();
                    have this->head == at(before_node, this->head->next) by { close(); }
                    // Delete affects the whole typed node, not just its first scalar cell.
                    have at(region(1).exit, separate(memory(*this->head), memory(this->head))) by { close(); }
                    mark before_delete;
                    step();
                    have separate(region(3).footprint, memory(this->head)) by {
                        close() using { at(region(1).exit, separate(memory(*this->head), memory(this->head))); };
                    }
                    have this->head == at(before_delete, this->head) by {
                        preserve(memory(this->head), region(3));
                    }
                    have this->head == at(before_node, this->head->next) by { close(); }
                },
            }
        }
    }
    unfold(list);
    step();
    close();
}

int round_trip(int x) {
    ensures result == x;
} by {
    step_until(region(3).entry);
    let empty = fold(nodes(stack.head), { items: List<int32>::Nil });
    unfold(length(List<int32>::Nil));
    have length(List<int32>::Nil) < 1000000 by close() using { length(List<int32>::Nil) == 0; };
    let { after: pushed } = step(Stack<int>::push, { before: empty }) {
        requires length(empty.items) < 1000000 by close();
        requires to_integer(stack.count) == length(empty.items) by close();
        requires aligned(&stack, 8) by close();
    }
    step();
    let { after: remaining } = step(Stack<int>::pop, { before: pushed }) {
        requires to_integer(stack.count) == length(pushed.items) by close();
        requires aligned(&stack, 8) by close();
    }
    step_until(function.exit);
    unfold(length(List<int32>::Cons(x, List<int32>::Nil)));
    unfold(first_or(List<int32>::Cons(x, List<int32>::Nil), 0));
    close();
}

unsigned long pushed_size(int x) {
    ensures to_integer(result) == 2;
} by {
    step_until(region(2).entry);
    let empty = fold(nodes(stack.head), { items: List<int32>::Nil });
    unfold(length(List<int32>::Nil));
    have length(List<int32>::Nil) < 1000000 by close() using { length(List<int32>::Nil) == 0; };
    step_until(region(3).entry);
    unfold(length(List<int32>::Cons(x, List<int32>::Nil)));
    have length(List<int32>::Cons(x, List<int32>::Nil)) < 1000000 by close() using {
        length(List<int32>::Cons(x, List<int32>::Nil)) == length(List<int32>::Nil) + 1;
        length(List<int32>::Nil) == 0;
    };
    let { after: one } = step(Stack<int>::push, { before: empty }) {
        requires length(empty.items) < 1000000 by close();
        requires to_integer(stack.count) == length(empty.items) by close();
        requires aligned(&stack, 8) by close();
    }
    let { after: pushed } = step(Stack<int>::push, { before: one }) {
        requires length(one.items) < 1000000 by close();
        requires to_integer(stack.count) == length(one.items) by close();
        requires aligned(&stack, 8) by close();
    }
    step();
    have separate(region(15).footprint, memory(stack.head)) by { close() using {}; }
    have stack.head == at(region(15).entry, stack.head) by {
        preserve(memory(stack.head), region(15));
    }
    step();
    have separate(region(16).footprint, memory(stack.head)) by { close() using {}; }
    have stack.head == at(region(16).entry, stack.head) by {
        preserve(memory(stack.head), region(16));
    }
    step(Stack<int>::~Stack, { list: pushed });
    step_until(function.exit);
    unfold(length(List<int32>::Cons(x, List<int32>::Cons(x, List<int32>::Nil))));
    have length(List<int32>::Cons(x, List<int32>::Cons(x, List<int32>::Nil))) == 2 by close() using {
        length(List<int32>::Cons(x, List<int32>::Cons(x, List<int32>::Nil))) == length(List<int32>::Cons(x, List<int32>::Nil)) + 1;
        length(List<int32>::Cons(x, List<int32>::Nil)) == length(List<int32>::Nil) + 1;
        length(List<int32>::Nil) == 0;
    };
    close();
}
