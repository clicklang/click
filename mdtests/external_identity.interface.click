int32 external_identity(int32 x) {
    requires x >= 0;
    ensures result == x;
}
