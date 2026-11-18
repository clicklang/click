verifying "advance.cpp";

void advance(bool empty, int32& cursor) {
    owns cursor;
    ensures empty implies cursor == old(cursor);
    ensures not empty implies cursor == 7;
}
