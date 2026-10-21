# The generic C++ stack is a container for every type

`Stack<T>` derives from the class template `Container<T>`, whose generic
`class` block declares its object's state: a `List<T>` of values, top first,
and a size. The stack defines them once for every `T`, the list from the
`nodes<T>` resource it holds beside its memory, `resource state:
nodes<T>(this->head);`, and the size from its `count`. Its overrides `put`
and `take` call the stack's own `push` and `pop`, proved once as in
`cpp_generic_resource_checked_once.md`, and refine `Container<T>`'s
interface, whose clauses compare `Integer` lengths of the object's state.
`round_trip_virtual` puts a value through any `Container<int>&` and takes
it back, applying lemmas about the list it names in its proof, and
`through` lends it a `Stack<int>`, whose nodes go into the object with its
memory and come back holding the same list.

```cpp filename=stack.cpp function=round_trip_virtual;through profile=normal_only templates=Container<T>;Stack<T>
template<class T> struct Node {
    T value;
    Node* next;
};

template<class T> struct Container {
    virtual void put(T value) noexcept = 0;
    virtual bool take(T& out) noexcept = 0;
};

template<class T> class Stack : public Container<T> {
    Node<T>* head = nullptr;
    unsigned long count = 0;

public:
    ~Stack() noexcept {
        while (head != nullptr) {
            Node<T>* node = head;
            head = node->next;
            delete node;
        }
    }

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

    void put(T value) noexcept override { push(value); }

    bool take(T& out) noexcept override { return pop(out); }
};

int round_trip_virtual(Container<int>& container, int x) noexcept {
    container.put(x);
    int out = 0;
    container.take(out);
    return out;
}

int through(Stack<int>& stack, int x) noexcept {
    int got = round_trip_virtual(stack, x);
    return got;
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

template<class T> Stack<T>::~Stack() {
    owns *this;
    consumes list: nodes<T>(this->head);
} by {
    loop {
        owns *this;
        owns list: nodes<T>(this->head);
        decreases length(list.items);

        initialize by simp();
        preserve by {
            match list.items {
                List::Nil => { contradiction(list.items == List<T>::Nil); },
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
                    step();
                    close_invariants();
                },
            }
        }
    }
    unfold(list);
    simp();
}



theorem cons_is_cons<T>(v: T, xs: List<T>) {
    ensures is_cons(List::Cons(v, xs)) by {
        unfold(is_cons(List::Cons(v, xs)));
        simp();
    }
}

theorem first_or_cons<T>(v: T, xs: List<T>, fallback: T) {
    ensures first_or(List::Cons(v, xs), fallback) == v by {
        unfold(first_or(List::Cons(v, xs), fallback));
        simp();
    }
}

theorem rest_cons<T>(v: T, xs: List<T>) {
    ensures rest(List::Cons(v, xs)) == xs by {
        unfold(rest(List::Cons(v, xs)));
        simp();
    }
}

// Every container holds a list of values, top first, and its size.
template<class T> class Container<T> {
    function items(this) -> List<T>;
    function size(this) -> uint64;
}
template<class T> extern void Container<T>::put(T value) {
    requires length(items(this)) < 1000000;
    requires to_integer(size(this)) == length(items(this));
    ensures items(this) == List::Cons(value, old(items(this)));
    ensures to_integer(size(this)) == length(items(this));
}
template<class T> extern bool Container<T>::take(T& out) {
    owns out;
    requires to_integer(size(this)) == length(items(this));
    ensures result == is_cons(old(items(this)));
    ensures out == first_or(old(items(this)), old(out));
    ensures items(this) == rest(old(items(this)));
    ensures to_integer(size(this)) == length(items(this));
}

// The stack is a container for every `T`: its list is the nodes resource
// it holds beside its memory.
template<class T> class Stack<T> : Container<T> {
    resource state: nodes<T>(this->head);
    function items(this) -> List<T> { state.items }
    function size(this) -> uint64 { this->count }
}
template<class T> void Stack<T>::put(T value) {
} by { execute(); simp(); }
template<class T> bool Stack<T>::take(T& out) {
} by { execute(); simp(); }

// Through any container of `int`: what is put is what is taken, and the
// list is as it was.
int round_trip_virtual(Container<int>& container, int x) {
    requires length(items(container)) < 1000000;
    requires to_integer(size(container)) == length(items(container));
    ensures result == x;
    ensures items(container) == old(items(container));
} by {
    execute();
    apply(cons_is_cons(x, old(items(container))));
    apply(first_or_cons(x, old(items(container)), 0));
    apply(rest_cons(x, old(items(container))));
    simp();
}

// A stack lent as a container gets back its list.
int through(Stack<int>& stack, int x) {
    owns stack;
    consumes list: nodes<int>(stack.head);
    produces after: nodes<int>(stack.head);
    requires length(list.items) < 1000000;
    requires to_integer(stack.count) == length(list.items);
    ensures result == x;
    ensures after.items == old(list.items);
} by { execute(); simp(); }
```

```expect
pass
```
