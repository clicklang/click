verifying "case.c";
import "library.click";
int32 caller(struct node* p) {
    requires node_type(p) == 1;
    ensures result == 0 or result == 1;
} by {
    step(); step();
    if q != 0 {
        have node_type(q) == 1;
        execute(); simp();
    } else { execute(); simp(); }
}
