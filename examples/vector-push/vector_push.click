arithmetic "integer";

resource nonempty_vector(owner: struct vector*) {
    owns *owner;
    owns owner->data[0..owner->cap];
    fact 1 <= owner->len;
    fact owner->len <= owner->cap;
    fact separate(memory(*owner), memory(owner->data[0..owner->cap]));
}

verifying "vector_push.c";

int32 vector_push(struct vector* owner, int32 value) {
    requires 0 <= owner->len;
    requires owner->len < owner->cap;
    requires separate(memory(*owner), memory(owner->data[0..owner->cap]));
    consumes *owner;
    consumes owner->data[0..owner->cap];
    produces nonempty_vector(owner);
    ensures result == old(owner->len) + 1;
    ensures owner->len == old(owner->len) + 1;
    ensures owner->data[old(owner->len)] == value;
    ensures owner->cap == old(owner->cap);
    ensures owner->data == old(owner->data);
} by {
    execute();
    fold(nonempty_vector(owner));
    auto();
}
