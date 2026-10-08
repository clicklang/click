verifying "relay_value.cpp";

int32 read_value(int32& value) {
    owns value;
    ensures value == old(value);
    ensures result == value;
} by {
    execute();
    simp();
}

int32 relay_value(int32& value) {
    requires value < 2147483647;
    owns value;
    ensures result == value + 1;
} by {
    execute();
    simp();
}
