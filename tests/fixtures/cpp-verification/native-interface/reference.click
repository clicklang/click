verifying "interface.cpp";
int32& identity(int32& value) { ensures &result == &value; }
int32 probe() { ensures result == 7; }
