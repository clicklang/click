# C++ record pointers

A pointer to a simple record, `Node*`, is a parameter, a local, a field and a
result. `p->field` reads and writes the record it points to when `p` is a
parameter or local; `nullptr` and `==` test it. A specification writes the
type as the source does, `p: Node*`, and a resource over it describes a list
by its nodes.

```cpp filename=list.cpp function=relink profile=normal_only
struct Node {
    int value;
    Node* next;
};

int head(Node* node) noexcept {
    return node->value;
}

Node* rest(Node* node) noexcept {
    return node->next;
}

Node* link(Node* node, Node* next) noexcept {
    node->next = next;
    return node;
}

bool is_empty(Node* node) noexcept {
    return node == nullptr;
}

int first_or(Node* node, int fallback) noexcept {
    if (node == nullptr) {
        return fallback;
    }
    return node->value;
}

int relink(Node* first, Node* second) noexcept {
    Node* next = rest(first);
    is_empty(next);
    if (next == nullptr) {
        link(first, second);
    }
    int second_value = head(second);
    int fallback = first_or(next, second_value);
    return fallback;
}
```

```click
verifying "list.cpp";

resource list_at(p: Node*) {
    field items: List<int32>;
    match items {
        List::Nil => { fact p == 0; },
        List::Cons(value, rest) => {
            owns *p;
            owns tail: list_at(p->next);
            fact p != 0;
            fact p->value == value;
            fact tail.items == rest;
        },
    }
}

function head_or(xs: List<int32>, fallback: int32) -> int32 {
    match xs {
        List::Nil => fallback,
        List::Cons(value, rest) => value,
    }
}

int head(Node* node) {
    views *node;
    ensures result == node->value;
} by { execute(); simp(); }

Node* rest(Node* node) {
    views *node;
    ensures result == node->next;
} by { execute(); simp(); }

Node* link(Node* node, Node* next) {
    owns *node;
    ensures result == node;
    ensures node->next == next;
    ensures node->value == old(node->value);
} by { execute(); simp(); }

bool is_empty(Node* node) {
    ensures result implies node == 0;
    ensures node == 0 implies result;
} by { execute(); simp(); }

int first_or(Node* node, int fallback) {
    consumes nodes: list_at(node);
    produces after: list_at(node);
    ensures after.items == old(nodes.items);
    ensures result == head_or(old(nodes.items), fallback);
} by {
    match nodes.items {
        List::Nil => {
            unfold(nodes);
            execute();
            let after = fold(list_at(node), { items: List<int32>::Nil });
        },
        List::Cons(value, rest) => {
            let { tail: tail } = unfold(nodes);
            execute();
            let after = fold(list_at(node), { items: List::Cons(value, rest) }, { tail: tail });
        },
    }
}

int relink(Node* first, Node* second) {
    owns *first;
    requires first->next == 0;
    owns *second;
    ensures first->next == second;
    ensures result == second->value;
} by {
    let empty = fold(list_at(first->next), { items: List<int32>::Nil });
    execute();
    unfold(head_or(List<int32>::Nil, second->value));
    simp();
}
```

```expect
pass
```
