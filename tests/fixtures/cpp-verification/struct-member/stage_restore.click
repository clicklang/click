verifying "stage_restore.cpp";

int32 stage_restore(struct RestoreState& state, int32& value) {
    owns state.pointer;
    owns state.saved;
    owns value;
    ensures state.pointer == &value;
    ensures state.saved == old(value);
    ensures value == 7;
    ensures result == old(value);
} by {
    execute();
    simp();
}
