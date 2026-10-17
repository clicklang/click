verifying "case.c";
function node_type(p: struct node*) -> int32 { 1 }
struct node* get(struct node* p) {
    requires node_type(p) == 1;
    ensures result != 0 implies node_type(result) == 1;
} by { execute(); simp(); }
