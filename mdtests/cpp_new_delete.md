# C++ new and delete of a simple record

`new Node{v, n}` allocates one simple record with the global `operator new`
and initializes each field in declaration order. In a `noexcept` function a
failed allocation ends the program, so the result is never null; the caller
receives the allocation and the record's memory, as from a successful
`malloc`. `delete` ends the record and frees its allocation.

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
    int result = node->value;
    drop(node);
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
pass
```
