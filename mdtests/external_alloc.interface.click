uint8* external_alloc(int32 bytes) {
    requires 0 < bytes;
    ensures result != 0;
    produces allocation(result, bytes);
    produces result[0..bytes];
}
