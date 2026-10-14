# an authorized abstract token transfers a runtime quantity

This checks the quantity form of the resources page: `owns amount of
object_ref(object)` lends a runtime, proved-nonnegative number of units of an
`authorized abstract` token, and a caller holding a constant quantity can
supply it.

```c filename=authorized_abstract_token_quantity_borrow.c
struct object {
    int32 value;
};

void use_refs(struct object* object, int32 amount) {
}

void hold_two(struct object* object) {
    use_refs(object, 2);
}
```

```click
authorized abstract resource object_ref(object: struct object*);

verifying "authorized_abstract_token_quantity_borrow.c";

void use_refs(struct object* object, int32 amount) {
    requires 0 <= amount;
    owns amount of object_ref(object);
} by { execute(); simp(); }

void hold_two(struct object* object) {
    owns 2 of object_ref(object);
} by { execute(); simp(); }
```

```expect
pass
```
