verifying "arraylist.c";

void *array_list_get_idx(struct array_list *arr, uint64 i) {
    views arr->length;
    requires i < arr->length;
    views arr->array;
    views arr->array[i];
    ensures result == arr->array[i];
}
