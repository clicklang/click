verifying "conditional_restore.cpp";

Restore::Restore(int32* slot) {
    owns this->p;
    owns this->saved;
    owns slot[0..1];
    ensures this->p == slot;
    ensures this->saved == old(slot[0]);
    ensures slot[0] == 7;
}

Restore::~Restore() {
    requires this->saved == 41;
    requires separate(memory(*this), memory(this->p[0..1]));
    owns this->p;
    owns this->saved;
    owns this->p[0..1];
    ensures this->p == old(this->p);
    ensures this->saved == old(this->saved);
    ensures this->p[0] == old(this->saved);
}

int32 conditional_restore(bool construct, bool early, int32& value) {
    owns value;
    requires value == 41;
    ensures construct == true implies (early == true implies result == 7);
    ensures construct == true implies (early == false implies result == 41);
    ensures construct == false implies result == 41;
    ensures value == 41;
}
