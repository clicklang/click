# Numeric copy equality does not preserve a modular representation

```c filename=packed.c
struct node { int32 value; };
unsigned long copy_word(unsigned long word) { return word; }
int32 read_packed(unsigned long word, struct node* p) {
    unsigned long copied = copy_word(word);
    return ((struct node*)(copied & ~1))->value;
}
```

```click
verifying "packed.c";

unsigned long copy_word(unsigned long word) {
    ensures result == old(word);
} by { execute(); simp(); }
int32 read_packed(unsigned long word, struct node* p) {
    requires p != 0;
    requires ((struct node*)(word & ~1)) == p;
    views p->value;
    ensures result == p->value;
} by { execute(); simp(); }
```

```expect
fail: access outside the subobject the pointer designates
```
