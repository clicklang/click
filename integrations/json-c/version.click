verifying "json_c_version.c";

const char *json_c_version() {
    ensures readable: viewable(result[0..5]);
    ensures first: result[0] == '0';
    ensures dot: result[1] == '.';
    ensures minor_tens: result[2] == '1';
    ensures minor_ones: result[3] == '8';
    ensures terminator: result[4] == '\0';
}

int json_c_version_num() {
    ensures result == 4608;
}
