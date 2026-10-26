target "x86_64-unknown-linux-gnu";
mode "kernel";
verifying "main.c";

int32 from_header() {
    ensures result == 15;
} by {
    execute();
    solve();
}

int32 answer() {
    ensures result == 15;
} by {
    execute();
    solve();
}
