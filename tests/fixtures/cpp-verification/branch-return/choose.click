verifying "choose.cpp";

int32 choose(bool early, int32& value) {
    owns value;
    ensures result == (if early != 0 { 7 } else { 9 });
    ensures value == result;
} by {
    execute();
    simp();
}
