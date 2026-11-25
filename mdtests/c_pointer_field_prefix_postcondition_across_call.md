# A modular C pointer-field prefix postcondition survives checked restoration

The prefix proof runs before return. It preserves each selected element across
the append and length-field writes using explicit separation facts, then joins
the two equalities. The caller receives the resulting quantified contract.

```c filename=vector.c
struct vector {
    int32 len;
    int32 cap;
    int32* data;
};

int32 vector_push(struct vector* owner, int32 value) {
    int32 index;
    int32* data;
    index = owner->len;
    data = owner->data;
    data[index] = value;
    owner->len = index + 1;
    return owner->len;
}

int32 caller(struct vector* owner, int32 value) { return vector_push(owner, value); }
```

```click
resource vector_storage(owner: struct vector*) {
    owns owner->len;
    owns owner->cap;
    owns owner->data;
    owns owner->data[0..owner->cap];
    fact 0 <= owner->len;
    fact owner->len <= owner->cap;
    fact owner->cap <= 1073741823;
    fact separate(memory(*owner), memory(owner->data[0..owner->cap]));
}

verifying "vector.c";
int32 vector_push(struct vector* owner, int32 value) {
    requires owner->len < owner->cap;
    owns vector_storage(owner);
    ensures to_integer(result) == to_integer(old(owner->len) + 1);
    ensures to_integer(owner->len) == to_integer(old(owner->len) + 1);
    ensures owner->data[old(owner->len)] == value;
    ensures owner->cap == old(owner->cap);
    ensures owner->data == old(owner->data);
    ensures forall (k: int32) {
        0 <= k and k < old(owner->len) implies
            owner->data[k] == old(owner->data[k])
    };
} by {
    unfold(vector_storage(owner));
    step();
    step();
    step();
    step();
    step();
    step();
    have forall (k: int32) { 0 <= k and k < old(owner->len) implies owner->data[k] == old(owner->data[k]) } by {
        intro() {
            intro() {
                have 0 <= k;
                have k < old(owner->len);
                // The append writes at the old length, beyond this prefix element.
                have old(owner->len) != k by {
                    if old(owner->len) == k {
                        have not (k < old(owner->len)) by {
                            rewrite(old(owner->len), k);
                            close();
                        }
                        contradiction(k < old(owner->len));
                    } else {
                        close();
                    }
                }
                have separate(memory(old(owner->data)[old(owner->len)]), memory(old(owner->data)[k])) by {
                    apply(click::separation::separate_elements(old(owner->data), old(owner->len), k));
                }
                have separate(statement(4).footprint, memory(old(owner->data)[k])) by {
                    close() using { separate(memory(old(owner->data)[old(owner->len)]), memory(old(owner->data)[k])); };
                }
                have at(statement(4).exit, owner->data[k]) == at(statement(4).entry, owner->data[k]) by {
                    preserve(memory(old(owner->data)[k]), statement(4));
                }
                // Restrict the struct/array separation to the length field and element.
                have k < old(owner->cap) by {
                    close() using { k < old(owner->len); old(owner->len) <= old(owner->cap); };
                }
                have contains(memory(*owner), memory(owner->len)) by { close(); }
                have contains(memory(old(owner->data)[0..old(owner->cap)]), memory(old(owner->data)[k])) by {
                    apply(click::separation::contains_element(old(owner->data), 0, old(owner->cap), k));
                }
                have separate(memory(owner->len), memory(old(owner->data)[k])) by {
                    apply(click::separation::separate_restrict(memory(*owner), memory(old(owner->data)[0..old(owner->cap)]), memory(owner->len), memory(old(owner->data)[k])));
                }
                have separate(statement(5).footprint, memory(old(owner->data)[k])) by {
                    close() using { separate(memory(owner->len), memory(old(owner->data)[k])); };
                }
                have at(statement(5).exit, owner->data[k]) == at(statement(5).entry, owner->data[k]) by {
                    preserve(memory(old(owner->data)[k]), statement(5));
                }
                close();
            }
        }
    }
    step();
    have owner->data == old(owner->data) by {
        close();
    }
    have owner->data[old(owner->len)] == value by {
        close();
    }
    fold(vector_storage(owner));
    close();
    close();
    close();
    close();
    close();
    close();
    close();
}

int32 caller(struct vector* owner, int32 value) {
    requires owner->len < owner->cap;
    owns vector_storage(owner);
    ensures forall (k: int32) { 0 <= k and k < old(owner->len) implies owner->data[k] == old(owner->data[k]) };
} by { step_until(function.exit); close(); close(); }
```

```expect
pass
```
