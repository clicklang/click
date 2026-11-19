verifying "arraylist.c";

void *array_list_get_idx(struct array_list *arr, uint64 i) {
    views arr->length;
    requires arr->length <= i;
    ensures result == 0;
}
