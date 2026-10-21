# A C++ function's proof names its parameters' object state

A sidecar function's clauses read a parameter's object state, `items(container)`,
as the object's field, and so does its proof: `round_trip` applies lemmas
about `first_or` and `rest` at `old(items(container))`, the list the
container held at entry, so it states its result as `x` itself and that the
container's list is as it was. `caller` lends its stack and gets back its
own list. The program is `cpp_generic_class_state_in_a_resource.md`'s.

```cpp filename=containers.cpp function=caller profile=normal_only templates=Container<T>;Stack<T>
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
int round_trip(Container<int>& container, int x) {
    ensures result == x;
    ensures items(container) == old(items(container));
} by {
    execute();
    apply(first_or_cons(x, old(items(container)), 0));
    apply(rest_cons(x, old(items(container))));
    simp();
}
int caller(Stack<int>& stack, int x) {
    owns stack;
    owns state: nodes<int>(stack.head);
    ensures result == x;
    ensures state.items == old(state.items);
} by { execute(); simp(); }
```

```expect
pass
```
