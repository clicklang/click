# A C++ record pointer's list resource refuses an overclaim

`first_or` reads the head of the list `node` points to. Its contract cannot
claim it always returns the fallback: on a nonempty list it returns the
node's value, which the list resource names.

```cpp filename=list.cpp function=first_or profile=normal_only
struct Node {
    int value;
    Node* next;
};

int first_or(Node* node, int fallback) noexcept {
    if (node == nullptr) {
        return fallback;
    }
    return node->value;
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

int first_or(Node* node, int fallback) {
    consumes nodes: list_at(node);
    produces after: list_at(node);
    ensures after.items == old(nodes.items);
    ensures result == fallback;
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
```

```expect
fail: `ensures result == fallback` failed for `first_or.ensures_1`
```
