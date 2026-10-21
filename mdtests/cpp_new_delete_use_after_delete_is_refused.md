# A C++ record cannot be read after its delete

After `drop` deletes the node, its memory is no longer allocated, and reading
`node->value` is undefined behavior.

```cpp filename=list.cpp function=round_trip profile=normal_only
struct Node {
    int value;
    Node* next;
};

Node* push(Node* head, int value) noexcept {
    Node* node = nullptr;
    node = new Node{value, head};
    return node;
}

void drop(Node* node) noexcept {
    delete node;
}

int round_trip(int value) noexcept {
    Node* node = push(nullptr, value);
    drop(node);
    int result = node->value;
    return result;
}
```

```click
verifying "list.cpp";

Node* push(Node* head, int value) {
    ensures result != 0;
    ensures aligned(result, 8);
    produces allocation(result, sizeof(Node));
    produces *result;
    ensures result->value == value;
    ensures result->next == head;
} by { execute(); simp(); }

void drop(Node* node) {
    requires node != 0;
    consumes allocation(node, sizeof(Node));
    consumes *node;
} by { execute(); simp(); }

int round_trip(int value) {
    ensures result == value;
} by { execute(); simp(); }
```

```expect
fail: invalid memory access
```
