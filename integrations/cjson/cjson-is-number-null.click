verifying "cJSON.c";
int cJSON_IsNumber(const struct cJSON *item) {
    requires item == 0;
    ensures result == 0;
}
