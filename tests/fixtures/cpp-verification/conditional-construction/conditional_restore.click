verifying "conditional_restore.cpp";

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
    requires this->saved == 41;
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

int32 conditional_restore(bool construct, bool early, int32& value) {
    owns value;
    requires value == 41;
    ensures construct != 0 implies (early != 0 implies result == 7);
    ensures construct != 0 implies (early == 0 implies result == 41);
    ensures construct == 0 implies result == 41;
    ensures value == 41;
} by {
    execute();
    simp();
}
