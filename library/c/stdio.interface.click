// C11 7.21.1 guarantees that standard output is open at program startup.
FILE *const stdout;

theorem stdout_non_null() {
    ensures stdout != 0;
}
