verifying "increment.cpp";

int32 increment(int32& value) {
    requires value < 2147483647;
    owns value;
    ensures value == old(value) + 1;
    ensures result == value;
} by {
    execute();
    simp();
}
