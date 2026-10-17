# A full cast postcondition preserves a packed pointer across a call

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
    ensures ((struct node*)(result & ~1)) == old((struct node*)(word & ~1));
} by { execute(); simp(); }
int32 read_packed(unsigned long word, struct node* p) {
    requires p != 0;
    requires ((struct node*)(word & ~1)) == p;
    views p->value;
    ensures result == p->value;
} by { execute(); simp(); }
```

```expect
pass
```
