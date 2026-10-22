int32 enters_either_way(int32 a, int32 b) {
    while (a > 0 || b > 0) {
        a = 0;
        b = 0;
    }
    return a + b;
}
