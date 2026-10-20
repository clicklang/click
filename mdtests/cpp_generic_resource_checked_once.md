# A C++ class template's generic resource is checked once for every type

`Stack<T>` holds a linked list of `Node<T>`. The sidecar describes the list
once for every type with a resource of its own type parameter, `nodes<T>`,
whose field is a `List<T>` and whose nodes are `new` allocations of
`sizeof(Node<T>)`, the size each instance's `new` allocates. `Stack<T>::push`
and `size` are proved once with `T` abstract, against the generic spec
function `length<T>`. Each instance is written out at its type: the client
`pushed_size` folds `nodes<int>` and calls `Stack<int>::push`, whose contract
is the generic one at `int`.

```cpp filename=stack.cpp function=pushed_size profile=normal_only templates=Stack<T>
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

    unsigned long size() const noexcept { return count; }
};

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

template<class T> unsigned long Stack<T>::size() const {
    views *this;
    ensures result == this->count;
} by { execute(); simp(); }

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
