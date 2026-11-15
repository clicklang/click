verifying "interface.cpp";
int32 take(struct Pair value) { ensures result == value.used; }
int32 probe(struct Pair& source) {
    views source.unused;
    views source.used;
    ensures result == source.used;
}
