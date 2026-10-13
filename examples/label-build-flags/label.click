verifying "label_fit.c";
verifying "label_copy.c";

uint64 label_fit(uint64 length) {
    ensures result < 32;
    ensures result <= length;
} by {
    execute();
    have result <= length by auto;
    simp();
}

uint64 label_measure(const char* src) {
    requires cstr_readable(src);
    ensures result < 32;
} by {
    execute();
    simp();
}
