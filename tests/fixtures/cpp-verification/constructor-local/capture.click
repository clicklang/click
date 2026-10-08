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

int32 capture(int32& value) {
    owns value;
    ensures value == 7;
    ensures result == old(value);
} by {
    execute();
    simp();
}
