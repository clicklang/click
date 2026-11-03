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
                    mark before_node;
                    step();
                    have separate(region(1).footprint, memory(this->head)) by { normalize() using {}; }
                    have this->head == at(before_node, this->head) by {
                        transport_certificate {
                            premise 0: separate(region(1).footprint, memory(this->head))
                                => separate(region(1).footprint, memory(this->head));
                            preserve 0 => this->head == at(before_node, this->head);
                            conclusion 1;
                        }
                    }
                    have separate(region(1).footprint, memory(this->head->next)) by { normalize() using {}; }
                    have this->head->next == at(before_node, this->head->next) by {
                        transport_certificate {
                            premise 0: separate(region(1).footprint, memory(this->head->next))
                                => separate(region(1).footprint, memory(this->head->next));
                            preserve 0 => this->head->next == at(before_node, this->head->next);
                            conclusion 1;
                        }
                    }
                    have node == this->head by { assumption(); }
                    step();
                    have this->head == at(before_node, this->head->next) by { assumption(); }
                    // Delete affects the whole typed node, not just its first scalar cell.
                    have at(region(1).exit, separate(memory(*this->head), memory(this->head))) by { assumption(); }
                    mark before_delete;
                    step();
                    have separate(region(3).footprint, memory(this->head)) by {
                        normalize() using { at(region(1).exit, separate(memory(*this->head), memory(this->head))); };
                    }
                    have this->head == at(before_delete, this->head) by {
                        transport_certificate {
                            premise 0: separate(region(3).footprint, memory(this->head))
                                => separate(region(3).footprint, memory(this->head));
                            preserve 0 => this->head == at(before_delete, this->head);
                            conclusion 1;
                        }
                    }
                    have this->head == at(before_node, this->head->next) by { assumption(); }
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
    let { after: one } = step(__cpp_q_X10_537461636b3c696e743e_I4_push, { before: empty });
    let { after: pushed } = step(__cpp_q_X10_537461636b3c696e743e_I4_push, { before: one });
    step();
    have separate(region(13).footprint, memory(stack.head)) by { normalize() using {}; }
    have stack.head == at(region(13).entry, stack.head) by {
        transport_certificate {
            premise 0: separate(region(13).footprint, memory(stack.head)) => separate(region(13).footprint, memory(stack.head));
            preserve 0 => stack.head == at(region(13).entry, stack.head);
            conclusion 1;
        }
    }
    step();
    have separate(region(14).footprint, memory(stack.head)) by { normalize() using {}; }
    have stack.head == at(region(14).entry, stack.head) by {
        transport_certificate {
            premise 0: separate(region(14).footprint, memory(stack.head)) => separate(region(14).footprint, memory(stack.head));
            preserve 0 => stack.head == at(region(14).entry, stack.head);
            conclusion 1;
        }
    }
    mark before_size;
    let { tail: first_tail } = unfold(pushed);
    let { tail: empty_tail } = unfold(first_tail);
    unfold(empty_tail);
    step();
    have separate(region(15).footprint, memory(stack.head)) by { normalize() using {}; }
    have stack.head == at(region(15).entry, stack.head) by {
        transport_certificate {
            premise 0: separate(region(15).footprint, memory(stack.head)) => separate(region(15).footprint, memory(stack.head));
            preserve 0 => stack.head == at(region(15).entry, stack.head);
            conclusion 1;
        }
    }
    have separate(region(15).footprint, memory(stack.head->next)) by { normalize() using {}; }
    have stack.head->next == at(region(15).entry, stack.head->next) by {
        transport_certificate {
            premise 0: separate(region(15).footprint, memory(stack.head->next)) => separate(region(15).footprint, memory(stack.head->next));
            preserve 0 => stack.head->next == at(region(15).entry, stack.head->next);
            conclusion 1;
        }
    }
    have separate(region(15).footprint, memory(stack.head->next->next)) by { normalize() using {}; }
    have stack.head->next->next == at(region(15).entry, stack.head->next->next) by {
        transport_certificate {
            premise 0: separate(region(15).footprint, memory(stack.head->next->next)) => separate(region(15).footprint, memory(stack.head->next->next));
            preserve 0 => stack.head->next->next == at(region(15).entry, stack.head->next->next);
            conclusion 1;
        }
    }
    step();
    have separate(region(16).footprint, memory(stack.head)) by { normalize() using {}; }
    have stack.head == at(region(16).entry, stack.head) by {
        transport_certificate {
            premise 0: separate(region(16).footprint, memory(stack.head)) => separate(region(16).footprint, memory(stack.head));
            preserve 0 => stack.head == at(region(16).entry, stack.head);
            conclusion 1;
        }
    }
    have separate(region(16).footprint, memory(stack.head->next)) by { normalize() using {}; }
    have stack.head->next == at(region(16).entry, stack.head->next) by {
        transport_certificate {
            premise 0: separate(region(16).footprint, memory(stack.head->next)) => separate(region(16).footprint, memory(stack.head->next));
            preserve 0 => stack.head->next == at(region(16).entry, stack.head->next);
            conclusion 1;
        }
    }
    have separate(region(16).footprint, memory(stack.head->next->next)) by { normalize() using {}; }
    have stack.head->next->next == at(region(16).entry, stack.head->next->next) by {
        transport_certificate {
            premise 0: separate(region(16).footprint, memory(stack.head->next->next)) => separate(region(16).footprint, memory(stack.head->next->next));
            preserve 0 => stack.head->next->next == at(region(16).entry, stack.head->next->next);
            conclusion 1;
        }
    }
    let empty_tail = fold(nodes(stack.head->next->next), { items: List<int32>::Nil });
    let first_tail = fold(nodes(stack.head->next), { items: List::Cons(x, List<int32>::Nil) }, { tail: empty_tail });
    let pushed = fold(nodes(stack.head), { items: List::Cons(x, List::Cons(x, List<int32>::Nil)) }, { tail: first_tail });
    step_until(function.exit);
    unfold(length(List<int32>::Cons(x, List<int32>::Cons(x, List<int32>::Nil))));
    have length(List<int32>::Cons(x, List<int32>::Cons(x, List<int32>::Nil))) == 2 by solve() using {
        length(List<int32>::Cons(x, List<int32>::Cons(x, List<int32>::Nil))) == length(List<int32>::Cons(x, List<int32>::Nil)) + 1;
        length(List<int32>::Cons(x, List<int32>::Nil)) == length(List<int32>::Nil) + 1;
        length(List<int32>::Nil) == 0;
    };
    solve();
}
