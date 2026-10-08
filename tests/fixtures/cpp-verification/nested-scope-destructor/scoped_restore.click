verifying "scoped_restore.cpp";

void Restore_constructor(struct Restore* this, int32* slot) {
    owns this->p;
    owns this->saved;
    owns slot[0..1];
    ensures this->p == slot;
    ensures this->saved == old(slot[0]);
    ensures slot[0] == 7;
} by {
    execute();
    simp();
}

void Restore_destructor(struct Restore* this) {
    requires separate(memory(*this), memory(this->p[0..1]));
    owns this->p;
    owns this->saved;
    owns this->p[0..1];
    ensures this->p == old(this->p);
    ensures this->saved == old(this->saved);
    ensures this->p[0] == old(this->saved);
} by {
    execute();
    simp();
}

int32 scoped_restore(bool early, int32& value) {
    owns value;
    ensures early != 0 implies result == 7;
    ensures early == 0 implies result == old(value);
    ensures value == old(value);
} by {
    execute();
    simp();
}
