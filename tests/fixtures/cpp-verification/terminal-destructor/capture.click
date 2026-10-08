verifying "capture.cpp";

void RestoreState_constructor(struct RestoreState* this, int32* slot) {
    owns this->pointer;
    owns this->saved;
    owns slot[0..1];
    ensures this->pointer == slot;
    ensures this->saved == old(slot[0]);
    ensures slot[0] == 7;
} by {
    execute();
    simp();
}

void RestoreState_destructor(struct RestoreState* this) {
    requires separate(memory(*this), memory(this->pointer[0..1]));
    owns this->pointer;
    owns this->saved;
    owns this->pointer[0..1];
    ensures this->pointer == old(this->pointer);
    ensures this->saved == old(this->saved);
    ensures this->pointer[0] == old(this->saved);
} by {
    execute();
    simp();
}

int32 capture(int32& value) {
    owns value;
    ensures result == 7;
    ensures value == old(value);
} by {
    execute();
    simp();
}
