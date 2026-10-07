# A tagged null word clears back to null

`rb_set_parent_color(node, NULL, RB_BLACK)` forms the integer `1` from a
null pointer. Clearing the tag recovers the canonical null pointer, whether
the null came from the literal `0`, a parameter known to be null, or an
owned word loaded from memory and known to contain only tag bits.

```c filename=tagged_pointer_null_word.c
struct node {
    int32 value;
    unsigned long word;
};

struct node* literal_null_round_trip() {
    unsigned long word = (unsigned long)0 + 1;
    return (struct node*)(word & ~3);
}

struct node* known_null_round_trip(struct node* next) {
    unsigned long word = (unsigned long)next + 1;
    return (struct node*)(word & ~3);
}

struct node* loaded_tagged_null(struct node* node) {
    unsigned long pc = node->word;
    return (struct node*)(pc & ~3);
}

struct node* loaded_zero(struct node* node) {
    unsigned long pc = node->word;
    return (struct node*)pc;
}
```

```click
verifying "tagged_pointer_null_word.c";

struct node* literal_null_round_trip() {
    ensures result == 0;
} by {
    execute();
    simp();
}

struct node* known_null_round_trip(struct node* next) {
    requires next == 0;
    ensures result == 0;
} by {
    execute();
    simp();
}

struct node* loaded_tagged_null(struct node* node) {
    owns node->word;
    requires node->word == 1;
    ensures result == 0;
} by {
    execute();
    simp();
}

struct node* loaded_zero(struct node* node) {
    owns node->word;
    requires node->word == 0;
    ensures result == 0;
} by {
    execute();
    simp();
}
```

```expect
pass
```
