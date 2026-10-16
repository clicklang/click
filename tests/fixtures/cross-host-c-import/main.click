target "x86_64-unknown-linux-gnu";
verifying "main.c";

int answer() {
    ensures result == 42;
} by {
    execute();
    simp();
}
