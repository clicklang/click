# A C++ class template's generic resource is checked once for every type

`Stack<T>` holds a linked list of `Node<T>`. The sidecar describes the list
once for every type with a resource of its own type parameter, `nodes<T>`,
whose field is a `List<T>` and whose nodes are `new` allocations of
`sizeof(Node<T>)`, the size each instance's `new` allocates. `Stack<T>::push`,
`pop` and `size` are proved once with `T` abstract, against the generic spec
functions `length<T>`, `first_or<T>`, `is_cons<T>` and `rest<T>`.

`pop` reads the top node's `T` value into `out`, after the unfold of `before`
stated that value at an earlier memory state, and folds the next node into
`after` after reading its value at a later one. Both reads are of an abstract
value no C store touched in between, so each is the value the resource
recorded.

Each instance is written out at its type: the clients `round_trip` and
`pushed_size` fold `nodes<int>` and call `Stack<int>::push`, `pop` and
`size`, whose contracts are the generic ones at `int`.

```cpp filename=stack.cpp function=round_trip;pushed_size profile=normal_only templates=Stack<T>
template<class T> struct Node {
    T value;
    Node* next;
};

template<class T> class Stack {
    Node<T>* head = nullptr;
    unsigned long count = 0;

public:
    void push(T value) noexcept {
        head = new Node<T>{value, head};
        count = count + 1;
    }

    bool pop(T& out) noexcept {
        if (head == nullptr) {
            return false;
        }
        Node<T>* node = head;
        out = node->value;
        head = node->next;
        delete node;
        count = count - 1;
        return true;
    }

    unsigned long size() const noexcept { return count; }
};

int round_trip(int x) noexcept {
    Stack<int> stack;
    stack.push(x);
    int out = 0;
    stack.pop(out);
    return out;
}

unsigned long pushed_size(int x) noexcept {
    Stack<int> stack;
    stack.push(x);
    stack.push(x);
    return stack.size();
}
```

```click
import click::integer;
verifying "stack.cpp";

resource nodes<T>(p: Node<T>*) {
    field items: List<T>;
    match items {
        List::Nil => { fact p == 0; },
        List::Cons(value, rest) => {
            owns allocation(p, sizeof(Node<T>));
            owns *p;
            owns tail: nodes<T>(p->next);
            fact p != 0;
            fact aligned(p, 8);
            fact p->value == value;
            fact tail.items == rest;
        },
    }
}

function length<T>(xs: List<T>) -> Integer
    decreases xs
{
    match xs {
        List::Nil => 0,
        List::Cons(value, rest) => length(rest) + 1,
    }
}

theorem length_nonnegative<T>(xs: List<T>) {
    ensures length(xs) >= 0 by {
        induct(xs) as ih {
            List::Nil => {
                unfold(length(List<T>::Nil));
                simp();
            }
            List::Cons(value, rest) => {
                apply(ih(rest));
                unfold(length(List<T>::Cons(value, rest)));
                arithmetic() using { length(rest) >= 0; };
            }
        }
    }
}

function first_or<T>(xs: List<T>, fallback: T) -> T {
    match xs {
        List::Nil => fallback,
        List::Cons(value, rest) => value,
    }
}

function is_cons<T>(xs: List<T>) -> bool {
    match xs {
        List::Nil => false,
        List::Cons(value, rest) => true,
    }
}

function rest<T>(xs: List<T>) -> List<T> {
    match xs {
        List::Nil => List<T>::Nil,
        List::Cons(value, tail) => tail,
    }
}

template<class T> void Stack<T>::push(T value) {
    owns *this;
    consumes before: nodes<T>(this->head);
    produces after: nodes<T>(this->head);
    requires length(before.items) < 1000000;
    requires to_integer(this->count) == length(before.items);
    ensures after.items == List::Cons(value, old(before.items));
    ensures to_integer(this->count) == length(after.items);
} by {
    execute();
    let after = fold(nodes<T>(this->head), { items: List::Cons(value, old(before.items)) }, { tail: before });
    unfold(length(List<T>::Cons(value, old(before.items))));
    apply(uint64_add_to_integer(old(this->count), 1u64));
    have to_integer(old(this->count) + 1u64) == length(List::Cons(value, old(before.items))) by arithmetic() using {
        to_integer(old(this->count) + 1u64) == to_integer(old(this->count)) + to_integer(1u64);
        to_integer(old(this->count)) == length(old(before.items));
        length(List::Cons(value, old(before.items))) == length(old(before.items)) + 1;
    };
    simp();
}

template<class T> bool Stack<T>::pop(T& out) {
    owns *this;
    owns out;
    consumes before: nodes<T>(this->head);
    produces after: nodes<T>(this->head);
    requires to_integer(this->count) == length(before.items);
    ensures result == is_cons(old(before.items));
    ensures out == first_or(old(before.items), old(out));
    ensures after.items == rest(old(before.items));
    ensures to_integer(this->count) == length(after.items);
} by {
    match before.items {
        List::Nil => {
            unfold(before);
            execute();
            let after = fold(nodes<T>(this->head), { items: List<T>::Nil });
            unfold(length(List<T>::Nil));
            unfold(is_cons(List<T>::Nil));
            unfold(first_or(List<T>::Nil, old(out)));
            unfold(rest(List<T>::Nil));
        },
        List::Cons(value, tail_items) => {
            let { tail: tail } = unfold(before);
            unfold(length(List::Cons(value, tail_items)));
            apply(length_nonnegative(tail_items));
            execute();
            unfold(is_cons(List::Cons(value, tail_items)));
            unfold(first_or(List::Cons(value, tail_items), old(out)));
            unfold(rest(List::Cons(value, tail_items)));
            match tail_items {
                List::Nil => {
                    unfold(tail);
                    let after = fold(nodes<T>(this->head), { items: List<T>::Nil });
                    unfold(length(List<T>::Nil));
                    have length(tail_items) == 0 by simp();
                    have to_integer(old(this->count)) == 1 by arithmetic() using {
                        to_integer(old(this->count)) == length(List::Cons(value, tail_items));
                        length(List::Cons(value, tail_items)) == length(tail_items) + 1;
                        length(tail_items) == 0;
                    };
                    simp();
                },
                List::Cons(next_value, next_items) => {
                    let { tail: next } = unfold(tail);
                    let after = fold(nodes<T>(this->head), { items: List::Cons(next_value, next_items) }, { tail: next });
                    have to_integer(old(this->count)) == length(tail_items) + 1 by arithmetic() using {
                        to_integer(old(this->count)) == length(List::Cons(value, tail_items));
                        length(List::Cons(value, tail_items)) == length(tail_items) + 1;
                    };
                    have to_integer(1u64) <= to_integer(old(this->count)) by arithmetic() using {
                        to_integer(old(this->count)) == length(tail_items) + 1;
                        length(tail_items) >= 0;
                    };
                    apply(uint64_subtract_to_integer(old(this->count), 1u64));
                    have to_integer(old(this->count) - 1u64) == length(tail_items) by arithmetic() using {
                        to_integer(old(this->count) - 1u64) == to_integer(old(this->count)) - to_integer(1u64);
                        to_integer(old(this->count)) == length(tail_items) + 1;
                    };
                    simp();
                },
            }
        },
    }
}

template<class T> unsigned long Stack<T>::size() const {
    views *this;
    ensures result == this->count;
} by { execute(); simp(); }

int round_trip(int x) {
    ensures result == x;
} by {
    execute_until(statement(2));
    let empty = fold(nodes<int>(stack.head), { items: List<int32>::Nil });
    unfold(length(List<int32>::Nil));
    have length(List<int32>::Nil) < 1000000 by arithmetic() using { length(List<int32>::Nil) == 0; };
    execute();
    unfold(length(List<int32>::Cons(x, List<int32>::Nil)));
    unfold(first_or(List<int32>::Cons(x, List<int32>::Nil), 0));
    simp();
}

unsigned long pushed_size(int x) {
    ensures to_integer(result) == 2;
} by {
    execute_until(statement(2));
    let empty = fold(nodes<int>(stack.head), { items: List<int32>::Nil });
    unfold(length(List<int32>::Nil));
    have length(List<int32>::Nil) < 1000000 by arithmetic() using { length(List<int32>::Nil) == 0; };
    execute_until(statement(3));
    unfold(length(List<int32>::Cons(x, List<int32>::Nil)));
    have length(List<int32>::Cons(x, List<int32>::Nil)) < 1000000 by arithmetic() using {
        length(List<int32>::Cons(x, List<int32>::Nil)) == length(List<int32>::Nil) + 1;
        length(List<int32>::Nil) == 0;
    };
    execute();
    unfold(length(List<int32>::Cons(x, List<int32>::Cons(x, List<int32>::Nil))));
    have length(List<int32>::Cons(x, List<int32>::Cons(x, List<int32>::Nil))) == 2 by arithmetic() using {
        length(List<int32>::Cons(x, List<int32>::Cons(x, List<int32>::Nil))) == length(List<int32>::Cons(x, List<int32>::Nil)) + 1;
        length(List<int32>::Cons(x, List<int32>::Nil)) == length(List<int32>::Nil) + 1;
        length(List<int32>::Nil) == 0;
    };
    simp();
}
```

```expect
pass
```
