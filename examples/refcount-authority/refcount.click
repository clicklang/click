resource reference(obj: struct object*) {}

resource control(obj: struct object*) {
    contains allocation(obj, sizeof(struct object));
    owns object(obj);
    owns authority(reference(obj));
    fact obj->refs == count(reference(obj));
}

verifying "../refcount/object_init.c";
verifying "../refcount/object_retain.c";
verifying "../refcount/object_release_nonfinal.c";
verifying "../refcount/object_release_final.c";

void object_init(struct object* obj) {
    consumes object(obj);
    produces object(obj);
    ensures obj->refs == 1;
} by {
    execute();
    simp();
}

void object_retain(struct object* obj) {
    owns control(obj);
    requires obj->refs < 2147483647;
    produces reference(obj);
} by {
    open(control(obj)) {
        step();
        fold(reference(obj));
    }
    execute();
    simp();
}

void object_release_nonfinal(struct object* obj) {
    owns control(obj);
    consumes reference(obj);
    requires obj->refs > 1;
} by {
    open(control(obj)) {
        unfold(reference(obj));
        step();
    }
    execute();
    simp();
}

void object_release_final(struct object* obj) {
    requires obj->refs == 1;
    consumes control(obj);
    consumes reference(obj);
} by {
    unfold(control(obj));
    unfold(reference(obj));
    unfold(authority(reference(obj)));
    execute();
    simp();
}
