verifying "call_set_seven.cpp";

int32 set_seven(int32& value) {
    owns value;
    ensures value == 7;
    ensures result == value;
} by {
    execute();
    simp();
}

int32 call_set_seven(int32& value) {
    owns value;
    ensures value == 7;
    ensures result == value;
} by {
    execute();
    simp();
}
