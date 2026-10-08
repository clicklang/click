# A bare struct subscript reads the first word

Struct field subscripts use the element address. The existing bare subscript
syntax reads its first int32 word, including through a struct pointer field.

```c filename=struct_word.c
struct node { int value; struct node *left; struct node *right; };
int child_value(struct node *node) { return node->left->value; }
```

```click
verifying "struct_word.c";

int32 child_value(struct node* node) {
    views node->left;
    requires node->left != 0;
    views node->left->value;
    ensures result == node->left[0];
} by { execute(); simp(); }
```

```expect
pass
```
