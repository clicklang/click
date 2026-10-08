verifying "stage_restore.cpp";

int32 stage_restore(int32& value) {
    owns value;
    ensures value == 7;
    ensures result == old(value);
} by {
    execute();
    simp();
}
