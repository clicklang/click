int32 external_set(int32 p[]) {
    owns p[0..1];
    ensures p[0] == 0;
    ensures result == 0;
}
