verifying "arraylist.c";

uint64 array_list_length(struct array_list *arr) {
    views arr[0..1];
    ensures result == arr->length;
}
