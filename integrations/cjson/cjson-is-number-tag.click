verifying "cJSON.c";
int cJSON_IsNumber(const struct cJSON *item) {
    requires item != 0;
    views item->type;
    ensures result == (if (item->type & 255) == 8 { 1 } else { 0 });
}
