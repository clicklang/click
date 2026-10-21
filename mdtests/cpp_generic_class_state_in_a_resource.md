# A C++ class template's object state may live in a resource it holds

`Container<T>` declares its object's state, its `items`, a `List<T>`.
`Stack<T>` keeps its items in nodes on the heap, which no field of the
stack holds: its `class` block names the resource that holds them beside its
own memory, `resource state: nodes<T>(this->head);`, and defines `items`
from it. `Stack<T>`'s overrides are verified once with `T` abstract, each
holding `*this` and `state`. A caller passing a `Stack<int>` as a
`Container<int>&` lends its memory and its nodes, packed into the object,
and gets back a `nodes<int>` instance holding the object's new items, which
its own `state` takes.

`Stack<T>`'s destructor deletes the remaining nodes and is verified once,
consuming them. `local_round_trip` builds a `Stack<int>` from its default
member initializers, folds its empty nodes as `state` before passing it as a
`Container<int>&`, and the destructor consumes the nodes the unpack gave
back at its return.

```cpp filename=containers.cpp function=caller;local_round_trip profile=normal_only templates=Container<T>;Stack<T>
template<class T> struct Node {
    T value;
    Node* next;
};
template<class T> struct Container {
    virtual void push(T value) noexcept = 0;
    virtual bool pop(T& out) noexcept = 0;
};
template<class T> class Stack : public Container<T> {
    Node<T>* head = nullptr;
public:
    ~Stack() noexcept {
        while (head != nullptr) {
            Node<T>* node = head;
            head = node->next;
            delete node;
        }
    }
    void push(T value) noexcept override {
        head = new Node<T>{value, head};
    }
    bool pop(T& out) noexcept override {
        if (head == nullptr) {
            return false;
        }
        Node<T>* node = head;
        out = node->value;
        head = node->next;
        delete node;
        return true;
    }
};
int round_trip(Container<int>& container, int x) noexcept {
    container.push(x);
    int out = 0;
    container.pop(out);
    return out;
}
int caller(Stack<int>& stack, int x) noexcept {
    return round_trip(stack, x);
}
int local_round_trip(int x) noexcept {
    Stack<int> stack;
    return round_trip(stack, x);
}
```

```click
verifying "containers.cpp";
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
template<class T> class Container<T> {
    function items(this) -> List<T>;
}
template<class T> extern void Container<T>::push(T value) {
    ensures items(this) == List::Cons(value, old(items(this)));
}
template<class T> extern bool Container<T>::pop(T& out) {
    owns out;
    ensures result == is_cons(old(items(this)));
    ensures out == first_or(old(items(this)), old(out));
    ensures items(this) == rest(old(items(this)));
}
template<class T> class Stack<T> : Container<T> {
    resource state: nodes<T>(this->head);
    function items(this) -> List<T> { state.items }
}
template<class T> void Stack<T>::push(T value) {
} by {
    match state.items {
        List::Nil => {
            unfold(state);
            execute();
            let tail = fold(nodes<T>(this->head->next), { items: List<T>::Nil });
            let state = fold(nodes<T>(this->head), { items: List::Cons(value, List<T>::Nil) }, { tail: tail });
        },
        List::Cons(top, below) => {
            let { tail: rest } = unfold(state);
            execute();
            let tail = fold(nodes<T>(this->head->next), { items: List::Cons(top, below) }, { tail: rest });
            let state = fold(nodes<T>(this->head), { items: List::Cons(value, List::Cons(top, below)) }, { tail: tail });
        },
    }
}
template<class T> bool Stack<T>::pop(T& out) {
} by {
    match state.items {
        List::Nil => {
            unfold(state);
            execute();
            let state = fold(nodes<T>(this->head), { items: List<T>::Nil });
            unfold(is_cons(List<T>::Nil));
            unfold(first_or(List<T>::Nil, old(out)));
            unfold(rest(List<T>::Nil));
        },
        List::Cons(value, tail_items) => {
            let { tail: tail } = unfold(state);
            execute();
            unfold(is_cons(List::Cons(value, tail_items)));
            unfold(first_or(List::Cons(value, tail_items), old(out)));
            unfold(rest(List::Cons(value, tail_items)));
            match tail_items {
                List::Nil => {
                    unfold(tail);
                    let state = fold(nodes<T>(this->head), { items: List<T>::Nil });
                    simp();
                },
                List::Cons(next_value, next_items) => {
                    let { tail: next } = unfold(tail);
                    let state = fold(nodes<T>(this->head), { items: List::Cons(next_value, next_items) }, { tail: next });
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
int round_trip(Container<int>& container, int x) {
    ensures result == first_or(List::Cons(x, old(items(container))), 0);
} by { execute(); simp(); }
int caller(Stack<int>& stack, int x) {
    owns stack;
    owns state: nodes<int>(stack.head);
    ensures result == x;
} by {
    execute();
    unfold(first_or(List<int>::Cons(x, old(state.items)), 0));
    simp();
}
int local_round_trip(int x) {
    ensures result == x;
} by {
    execute_until(statement(2));
    let state = fold(nodes<int>(stack.head), { items: List<int32>::Nil });
    execute();
    unfold(first_or(List<int32>::Cons(x, List<int32>::Nil), 0));
    simp();
}
```

```expect
pass
```
