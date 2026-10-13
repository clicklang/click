resource nonempty_vector(owner: struct vector*) {
    owns owner->len;
    owns owner->cap;
    owns owner->data;
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
    consumes owner->len;
    consumes owner->cap;
    consumes owner->data;
    consumes owner->data[0..owner->cap];
    produces nonempty_vector(owner);
    ensures result == old(owner->len) + 1;
    ensures owner->len == old(owner->len) + 1;
    ensures owner->data[old(owner->len)] == value;
    ensures owner->cap == old(owner->cap);
    ensures owner->data == old(owner->data);
} by {
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    fold(nonempty_vector(owner));
    assumption();
    assumption();
    assumption();
    assumption();
    assumption();
    assumption();
}
